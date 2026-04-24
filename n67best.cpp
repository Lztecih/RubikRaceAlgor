// ============================================================
// Rubik's Race — END-TO-END SOLVER (Phase 1 + 2 + 3)
// ============================================================
// Reads puzzle, solves it from scratch, compresses, saves everything.
//
// COMPILE:
//   g++ -O3 -std=c++17 -pthread solver.cpp -o solver
//
// USAGE:
//   ./solver <puzzle.txt> <output_prefix> [hours]
//
// OUTPUTS (all with trailing S; submit whichever is shortest):
//   <prefix>_final.txt          -- best across all threads (submit this)
//   <prefix>_phase1.txt         -- after Phase 1 only (initial solution)
//   <prefix>_sweep_T{0-3}.txt   -- per-sweep-thread best
//   <prefix>_sa_T{0-3}.txt      -- per-SA-thread best
//
// DESIGN:
//   Phase 1: 2 threads running BFS-from-center beam search in parallel
//            (different BFS seed cells -> different orderings)
//   Phase 2: 4 threads running sweeping IDA* vacuum, different K bands
//   Phase 3: 4 threads running random-offset SA IDA*
//   Checkpoint thread saves best to disk every 5 min.
//   Ctrl-C / SIGTERM: flushes all files cleanly before exit.
// ============================================================

#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <queue>
#include <algorithm>
#include <cstring>
#include <cstdlib>
#include <cstdio>
#include <cstdint>
#include <climits>
#include <ctime>
#include <random>
#include <chrono>
#include <thread>
#include <mutex>
#include <atomic>
#include <csignal>
#include <unistd.h>
#include <memory>
#include <unordered_set>

using namespace std;
using namespace chrono;

// ============================================================
// GLOBALS
// ============================================================
static int N, M;
static const int MAXN = 70;       // supports N up to 67
static const int DR[4] = { 1, -1, 0, 0 };   // UDLR: where the blank moves
static const int DC[4] = { 0, 0, 1, -1 };
static const char DCH[4] = { 'U', 'D', 'L', 'R' };
static const int OPP[4] = { 1, 0, 3, 2 };
static int dirOf(char c){ return c=='U'?0:c=='D'?1:c=='L'?2:3; }

static int init_board[MAXN][MAXN];
static int tgt[MAXN][MAXN];
static int init_br, init_bc;

static auto t_start = steady_clock::now();
static double elapsed(){ return duration<double>(steady_clock::now() - t_start).count(); }
static string g_out_prefix;

// ============================================================
// INPUT
// ============================================================
static void readPuzzle(const char* path){
    ifstream f(path);
    if(!f){ cerr<<"cannot open "<<path<<"\n"; exit(1); }
    f >> N; M = N - 2;
    if (N < 5 || N > 67 || (N % 2) == 0){
        cerr << "Invalid N=" << N << " (must be odd, 5..67)\n"; exit(1);
    }
    for (int r=0; r<N; r++) for (int c=0; c<N; c++){
        f >> init_board[r][c];
        if (init_board[r][c] == -1){ init_br = r; init_bc = c; init_board[r][c] = 0; }
    }
    for (int r=0; r<M; r++) for (int c=0; c<M; c++) f >> tgt[r][c];
}

// ============================================================
// VALIDATION
// ============================================================
static bool validate(const string& S){
    static thread_local int b[MAXN][MAXN];
    for (int r=0; r<N; r++) for (int c=0; c<N; c++) b[r][c] = init_board[r][c];
    int br = init_br, bc = init_bc;
    for (char c : S){
        int d = dirOf(c);
        int nr = br + DR[d], nc = bc + DC[d];
        if (nr<0||nr>=N||nc<0||nc>=N) return false;
        swap(b[br][bc], b[nr][nc]);
        br = nr; bc = nc;
    }
    for (int r=0; r<M; r++) for (int c=0; c<M; c++)
        if (b[r+1][c+1] != tgt[r][c]) return false;
    return true;
}

// ============================================================
// INVERSE-PAIR ELIMINATION
// ============================================================
static string stripInversePairs(string S){
    bool changed = true;
    while (changed){
        changed = false;
        string out; out.reserve(S.size());
        for (char c : S){
            if (!out.empty()){
                int d1 = dirOf(out.back()), d2 = dirOf(c);
                if (d1 == OPP[d2]){ out.pop_back(); changed = true; continue; }
            }
            out.push_back(c);
        }
        S = std::move(out);
    }
    return S;
}

// ============================================================
// FILE SAVE (thread-safe)
// ============================================================
static mutex g_file_mutex;
static void saveSolutionFile(const string& path, const string& S, const string& note){
    lock_guard<mutex> lk(g_file_mutex);
    ofstream f(path);
    f << S << "S\n";
    f << "// length=" << S.size() << "  " << note << "\n";
}

// Print a solution to stdout with clear markers. User can copy-paste the
// string block mid-run without waiting for the full solver to finish.
static mutex g_stdout_mutex;
static void printSolutionToStdout(const string& S, const string& tag){
    lock_guard<mutex> lk(g_stdout_mutex);
    cout << "\n===== SOLUTION AFTER " << tag
         << " (length=" << S.size() << ") =====\n";
    cout << S << "S\n===== END " << tag << " =====\n" << flush;
}

// ============================================================
// LOG
// ============================================================
static mutex g_log_mutex;
static void logMsg(const string& s){
    lock_guard<mutex> lk(g_log_mutex);
    cerr << "[t=" << (int)elapsed() << "s] " << s << "\n";
}

// ============================================================
// PHASE 1: A* ROUTING + BEAM SEARCH
// ============================================================
// 4D state: (tile_r, tile_c, blank_r, blank_c). For N=67, |state| = 67^4 = 20.1M.
// Each A* context needs 4 int arrays of size FLAT_LIM = ~80MB each = 320MB per context.
// That's per Phase-1 thread, so keep P1_THREADS small (2).

static int FLAT_LIM;

struct AstarCtx {
    vector<int> g_cost;
    vector<int> parent_enc;
    vector<int> generation;
    vector<uint8_t> dir_in;
    int cur_gen = 0;
    void init(){
        g_cost.assign(FLAT_LIM, 0);
        parent_enc.assign(FLAT_LIM, 0);
        generation.assign(FLAT_LIM, 0);
        dir_in.assign(FLAT_LIM, 0);
    }
};

static inline int encState(int tr, int tc, int br, int bc){
    return ((tr * N + tc) * N + br) * N + bc;
}
static inline void decState(int e, int& tr, int& tc, int& br, int& bc){
    bc = e % N; e /= N;
    br = e % N; e /= N;
    tc = e % N; e /= N;
    tr = e;
}
static inline bool inBoard(int r, int c){ return r>=0 && r<N && c>=0 && c<N; }

struct BQ {
    vector<vector<int>> b;
    int minb = 0;
    void reset(int cap){
        if ((int)b.size() < cap) b.assign(cap, {});
        else for (auto& v : b) v.clear();
        minb = 0;
    }
    void push(int cost, int val){
        if (cost >= (int)b.size()) b.resize(cost + 8);
        b[cost].push_back(val);
    }
    bool empty(){
        while (minb < (int)b.size() && b[minb].empty()) minb++;
        return minb == (int)b.size();
    }
    int pop(){
        int v = b[minb].back(); b[minb].pop_back();
        return v;
    }
    int curCost(){ return minb; }
};

// Admissible heuristic: Manhattan(tile -> goal) + max(0, |blank -> tile| - 1)
static inline int hRouting(int tr, int tc, int gr, int gc, int br, int bc){
    int dt = abs(tr - gr) + abs(tc - gc);
    if (dt == 0) return 0;
    int db = abs(br - tr) + abs(bc - tc);
    return dt + max(0, db - 1);
}

// Returns empty string + returns true if already at goal, else fills out_path.
static bool astarRoute(
    AstarCtx& ctx, const short* state, const uint8_t* locked,
    int tr0, int tc0, int gr, int gc, int br0, int bc0,
    string& out_path, int expand_limit = 300000
){
    (void)state; // current board not needed for routing; locked[] captures obstacles
    out_path.clear();
    if (tr0 == gr && tc0 == gc) return true;
    ctx.cur_gen++;

    BQ q;
    q.reset(4 * (N + M));

    int s0 = encState(tr0, tc0, br0, bc0);
    ctx.g_cost[s0] = 0;
    ctx.generation[s0] = ctx.cur_gen;
    ctx.parent_enc[s0] = -1;
    ctx.dir_in[s0] = 255;
    q.push(hRouting(tr0, tc0, gr, gc, br0, bc0), s0);

    int expanded = 0;
    int goal_enc = -1;

    while (!q.empty() && expanded < expand_limit){
        int s = q.pop();
        int tr, tc, br, bc;
        decState(s, tr, tc, br, bc);

        if (tr == gr && tc == gc){ goal_enc = s; break; }
        expanded++;

        int g = ctx.g_cost[s];

        for (int d = 0; d < 4; d++){
            int nbr = br + DR[d];
            int nbc = bc + DC[d];
            if (!inBoard(nbr, nbc)) continue;
            if (locked[nbr * MAXN + nbc]) continue;

            int ntr = tr, ntc = tc;
            if (nbr == tr && nbc == tc){ ntr = br; ntc = bc; }

            int ns = encState(ntr, ntc, nbr, nbc);
            int ng = g + 1;
            if (ctx.generation[ns] != ctx.cur_gen || ng < ctx.g_cost[ns]){
                ctx.generation[ns] = ctx.cur_gen;
                ctx.g_cost[ns] = ng;
                ctx.parent_enc[ns] = s;
                ctx.dir_in[ns] = (uint8_t)d;
                int h = hRouting(ntr, ntc, gr, gc, nbr, nbc);
                q.push(ng + h, ns);
            }
        }
    }

    if (goal_enc < 0) return false;

    vector<char> rev;
    int cur = goal_enc;
    while (ctx.parent_enc[cur] != -1){
        rev.push_back(DCH[ctx.dir_in[cur]]);
        cur = ctx.parent_enc[cur];
    }
    out_path.assign(rev.rbegin(), rev.rend());
    return true;
}

static void applyPath(short* state, int& br, int& bc, const string& path){
    for (char c : path){
        int d = dirOf(c);
        int nr = br + DR[d], nc = bc + DC[d];
        swap(state[br*MAXN+bc], state[nr*MAXN+nc]);
        br = nr; bc = nc;
    }
}

// BFS ordering from a seed (i,j) inside the MxM target
static vector<pair<int,int>> buildSpiralOrder(int seed_r, int seed_c){
    vector<pair<int,int>> order;
    vector<vector<int>> vis(M, vector<int>(M, 0));
    queue<pair<int,int>> q;
    if (seed_r < 0) seed_r = 0;
    if (seed_r >= M) seed_r = M-1;
    if (seed_c < 0) seed_c = 0;
    if (seed_c >= M) seed_c = M-1;
    q.push({seed_r, seed_c});
    vis[seed_r][seed_c] = 1;
    while (!q.empty()){
        auto pr = q.front(); q.pop();
        int r = pr.first, c = pr.second;
        order.push_back({r, c});
        static const int ddr[] = {-1, 1, 0, 0};
        static const int ddc[] = {0, 0, -1, 1};
        for (int k = 0; k < 4; k++){
            int nr = r + ddr[k], nc = c + ddc[k];
            if (nr>=0 && nr<M && nc>=0 && nc<M && !vis[nr][nc]){
                vis[nr][nc] = 1; q.push({nr, nc});
            }
        }
    }
    return order;
}

// Outside-in pair-safe order: solve row0 (top row), then col0 (left column),
// then last row (bottom), then last column (right). Then recurse on the inner
// (M-2)x(M-2) sub-region with the same pattern.
//
// This avoids the catastrophic "long-thin-strip endgame" that row/col snake
// orders create. Instead of leaving one remaining row or column where each
// tile needs huge detours, this leaves a SQUARE at the end — which needs
// fewer detour moves per tile.
//
// Importantly: we do row0 BEFORE col0, so the corner (0,0) gets solved as part
// of row0 with the row0-pair technique implicit in A* routing. Similarly for
// (0, M-1), (M-1, 0), (M-1, M-1) — each is a corner at the end of its row/col.
static vector<pair<int,int>> buildOutsideInOrder(bool reverse_spiral = false){
    vector<pair<int,int>> order;
    int top = 0, bot = M - 1, left = 0, right = M - 1;
    while (top <= bot && left <= right){
        // Remaining region is a rectangle [top..bot] x [left..right].
        // If it's just one row or one column, emit it in order and stop.
        if (top == bot){
            for (int c = left; c <= right; c++) order.push_back({top, c});
            break;
        }
        if (left == right){
            for (int r = top; r <= bot; r++) order.push_back({r, left});
            break;
        }
        // Emit top row (left to right), stopping before right so col emission
        // handles (top, right).
        if (!reverse_spiral){
            for (int c = left; c < right; c++) order.push_back({top, c});
            // Emit right column (top to bottom), stopping before bot.
            for (int r = top; r < bot; r++) order.push_back({r, right});
            // Emit bottom row (right to left), stopping before left.
            for (int c = right; c > left; c--) order.push_back({bot, c});
            // Emit left column (bottom to top), stopping before top.
            for (int r = bot; r > top; r--) order.push_back({r, left});
        } else {
            // Mirror image: left column first, then bottom row, then right col, then top row.
            for (int r = top; r < bot; r++) order.push_back({r, left});
            for (int c = left; c < right; c++) order.push_back({bot, c});
            for (int r = bot; r > top; r--) order.push_back({r, right});
            for (int c = right; c > left; c--) order.push_back({top, c});
        }
        top++; bot--; left++; right--;
    }
    return order;
}

// Row-major snake order: (0,0), (0,1)...(0,M-1), (1,M-1)...(1,0), ...
// This is the safe order: outer-first, so the blank can always navigate the
// outer board ring + unsolved inner rectangle. No locked cells can trap the blank.
//
// row_first:     true = solve row-by-row, false = solve col-by-col
// reverse_rows:  flips which end each row/col starts from (TL vs TR zigzag phase)
// bottom_first:  true = start from last row/col and work backwards toward row/col 0
static vector<pair<int,int>> buildSnakeOrder(bool row_first, bool reverse_rows, bool bottom_first = false){
    vector<pair<int,int>> order;
    if (row_first){
        for (int rr = 0; rr < M; rr++){
            int r = bottom_first ? (M - 1 - rr) : rr;
            bool rev = (rr % 2) == (reverse_rows ? 0 : 1);
            if (rev) for (int c = M-1; c >= 0; c--) order.push_back({r, c});
            else     for (int c = 0; c < M; c++)    order.push_back({r, c});
        }
    } else {
        for (int cc = 0; cc < M; cc++){
            int c = bottom_first ? (M - 1 - cc) : cc;
            bool rev = (cc % 2) == (reverse_rows ? 0 : 1);
            if (rev) for (int r = M-1; r >= 0; r--) order.push_back({r, c});
            else     for (int r = 0; r < M; r++)    order.push_back({r, c});
        }
    }
    return order;
}

// Beam state
struct BState {
    vector<short> board;       // MAXN*MAXN
    vector<uint8_t> locked;    // MAXN*MAXN
    int br, bc;
    string moves;
    int step;
    long long score;
    BState() : board(MAXN*MAXN, 0), locked(MAXN*MAXN, 0), br(0), bc(0), step(0), score(0) {}
};

struct P1Args {
    int thread_id;
    string strategy_name;        // for logging: "row-snake", "col-snake", "spiral", etc.
    vector<pair<int,int>> order; // precomputed M*M cells in placement order
    int beam_width;
    double deadline;
    string result;               // full solution if validated
    string partial;              // best partial (moves accumulated) if stuck/timed-out
    int partial_step = 0;
    bool done = false;
};

static void runPhase1(P1Args* A){
    const auto& order = A->order;

    unique_ptr<AstarCtx> ctx(new AstarCtx());
    try {
        ctx->init();
    } catch (const std::bad_alloc&){
        logMsg("[P1 T" + to_string(A->thread_id) + "] OUT OF MEMORY allocating A* context (need ~"
               + to_string((long long)FLAT_LIM * 13 / (1024*1024)) + " MB)");
        A->done = true;
        return;
    }

    BState init;
    for (int r = 0; r < N; r++) for (int c = 0; c < N; c++)
        init.board[r * MAXN + c] = (short)init_board[r][c];
    init.br = init_br;
    init.bc = init_bc;
    init.step = 0;
    init.score = 0;

    vector<BState> beam;
    beam.push_back(std::move(init));
    int total = (int)order.size();

    for (int step = 0; step < total; step++){
        if (elapsed() > A->deadline){
            logMsg("[P1 T" + to_string(A->thread_id) + "] deadline at step "
                   + to_string(step) + "/" + to_string(total));
            break;
        }
        int ti = order[step].first, tj = order[step].second;
        int gr = ti + 1, gc = tj + 1;
        int color = tgt[ti][tj];

        // Figure out next step's goal cell (for lookahead scoring).
        // If this is the last step, no lookahead.
        int next_gr = -1, next_gc = -1;
        if (step + 1 < total){
            int nti = order[step + 1].first, ntj = order[step + 1].second;
            next_gr = nti + 1; next_gc = ntj + 1;
        }

        vector<BState> next_beam;
        next_beam.reserve(A->beam_width * 3);

        for (auto& st : beam){
            // already correct?
            if (st.board[gr * MAXN + gc] == color && !st.locked[gr * MAXN + gc]){
                BState ns = st;
                ns.locked[gr * MAXN + gc] = 1;
                ns.step = step + 1;
                // Score: moves_made is PRIMARY (multiplier >> max blank penalty),
                // blank penalty is a tiebreaker only. Max blank penalty ≈ 2N ≤ 134.
                // Use multiplier 1024 so ties-to-1-move-difference never swap order.
                long long blank_penalty = 0;
                if (next_gr >= 0){
                    blank_penalty = abs(ns.br - next_gr) + abs(ns.bc - next_gc);
                }
                ns.score = (long long)ns.moves.size() * 1024 + blank_penalty;
                next_beam.push_back(std::move(ns));
                continue;
            }

            struct Cand { int r, c, cost; };
            vector<Cand> cands;
            for (int r = 0; r < N; r++) for (int c = 0; c < N; c++){
                if (st.locked[r * MAXN + c]) continue;
                short id = st.board[r * MAXN + c];
                if (id <= 0) continue;
                if (id != color) continue;   // tiles ARE colored by id in input (see note below)
                int cost = abs(r - gr) + abs(c - gc);
                cands.push_back({r, c, cost});
            }
            if (cands.empty()) continue;
            sort(cands.begin(), cands.end(), [](const Cand& a, const Cand& b){ return a.cost < b.cost; });

            int tried = 0;
            int remaining = total - step;
            // Try more candidates: when many cells are locked, the nearest tile often
            // isn't routable and we need to fall back on further ones. Endgame needs
            // more options because each bad choice cascades 30-80 moves.
            int max_tries = (remaining > 400) ? 4 : (remaining > 100) ? 6 : 12;
            for (auto& cd : cands){
                if (tried >= max_tries) break;
                tried++;
                string path;
                // Scale A* budget with board size; N=67 needs ~1M expansions for tight routes
                int astar_budget = 100000 + N * N * 200;
                bool ok = astarRoute(*ctx, st.board.data(), st.locked.data(),
                                     cd.r, cd.c, gr, gc, st.br, st.bc, path, astar_budget);
                if (!ok) continue;
                BState ns = st;
                applyPath(ns.board.data(), ns.br, ns.bc, path);
                ns.moves += path;
                ns.locked[gr * MAXN + gc] = 1;
                ns.step = step + 1;
                // Score with blank-position tiebreaker (see above)
                long long blank_penalty = 0;
                if (next_gr >= 0){
                    blank_penalty = abs(ns.br - next_gr) + abs(ns.bc - next_gc);
                }
                ns.score = (long long)ns.moves.size() * 1024 + blank_penalty;
                next_beam.push_back(std::move(ns));
            }
        }

        if (next_beam.empty()){
            logMsg("[P1 T" + to_string(A->thread_id) + " " + A->strategy_name
                   + "] STUCK at step " + to_string(step) + "/" + to_string(total));
            // Save partial so Phase 2 can optionally start from here if all threads fail
            if (!beam.empty()){
                A->partial = beam[0].moves;
                A->partial_step = step;
            }
            A->done = true;
            return;
        }
        sort(next_beam.begin(), next_beam.end(),
             [](const BState& a, const BState& b){ return a.score < b.score; });
        // Adaptive beam width: modestly widen beam for the endgame where each
        // decision costs many moves. Scale from 1.0x at 75% done to 1.5x at 100%.
        // (Was 2x — too slow, doubling beam in endgame ate all the budget.)
        int effective_beam = A->beam_width;
        int remaining_after = total - step - 1;
        if (remaining_after < total / 4){
            double scale = 1.0 + 0.5 * (double)(total/4 - remaining_after) / (double)(total/4);
            effective_beam = (int)(A->beam_width * scale);
        }
        if ((int)next_beam.size() > effective_beam) next_beam.resize(effective_beam);
        beam = std::move(next_beam);

        if (step % 200 == 0 || step == total - 1){
            logMsg("[P1 T" + to_string(A->thread_id) + " " + A->strategy_name
                   + "] step " + to_string(step+1) + "/" + to_string(total)
                   + " best=" + to_string(beam[0].moves.size()));
        }
    }

    A->done = true;
    if (!beam.empty()){
        // Did we finish all steps?
        if (beam[0].step >= total){
            A->result = beam[0].moves;
        } else {
            A->partial = beam[0].moves;
            A->partial_step = beam[0].step;
        }
    }
    logMsg("[P1 T" + to_string(A->thread_id) + " " + A->strategy_name + "] done: "
           + (A->result.empty() ? ("partial " + to_string(A->partial.size()) + " moves at step "
                                   + to_string(A->partial_step) + "/" + to_string(total))
                                : ("full "    + to_string(A->result.size())  + " moves")));
}

// ============================================================
// PHASE 2/3: CHECKPOINTED HISTORY + IDA* VACUUM
// ============================================================
struct Hist {
    int K = 500;
    vector<vector<short>> cks;
    vector<int> blks;
    const string* S = nullptr;

    void build(const string& s){
        S = &s;
        int n = (int)s.size() / K + 1;
        cks.assign(n, {});
        blks.assign(n, 0);
        vector<short> b(N*N);
        for (int r=0; r<N; r++) for (int c=0; c<N; c++) b[r*N+c] = (short)init_board[r][c];
        int blank = init_br * N + init_bc;
        cks[0] = b; blks[0] = blank;
        int ck = 1;
        for (int i = 0; i < (int)s.size(); i++){
            int d = dirOf(s[i]);
            int r = blank / N, c = blank % N;
            int nr = r + DR[d], nc = c + DC[d];
            swap(b[r*N+c], b[nr*N+nc]);
            blank = nr*N+nc;
            if ((i+1) % K == 0 && ck < n){ cks[ck] = b; blks[ck] = blank; ck++; }
        }
    }
    void at(int i, short* out, int& out_blank) const {
        int ck = i / K; if (ck >= (int)cks.size()) ck = (int)cks.size()-1;
        memcpy(out, cks[ck].data(), N*N*sizeof(short));
        int blank = blks[ck];
        for (int j = ck * K; j < i; j++){
            int d = dirOf((*S)[j]);
            int r = blank/N, c = blank%N;
            int nr = r+DR[d], nc = c+DC[d];
            swap(out[r*N+c], out[nr*N+nc]);
            blank = nr*N+nc;
        }
        out_blank = blank;
    }
};

struct IDA {
    vector<int> tgt_r, tgt_c;
    vector<int> cur_r, cur_c;
    vector<short> board;
    int blank_r, blank_c;
    long long nodes = 0, cap = 0;
    double deadline = 0;
    string path;
};

static int computeH(IDA& I){
    int h = 0;
    int ids_max = N * N + 4;
    for (int id = 1; id < ids_max; id++){
        if (I.tgt_r[id] < 0) continue;
        h += abs(I.cur_r[id] - I.tgt_r[id]) + abs(I.cur_c[id] - I.tgt_c[id]);
    }
    return h;
}

static bool isGoal(IDA& I){
    int ids_max = N * N + 4;
    for (int id = 1; id < ids_max; id++){
        if (I.tgt_r[id] < 0) continue;
        if (I.cur_r[id] != I.tgt_r[id] || I.cur_c[id] != I.tgt_c[id]) return false;
    }
    return true;
}

static bool dfs(IDA& I, int last_dir, int g, int bound, int K){
    I.nodes++;
    if ((I.nodes & 0xFFFFF) == 0){
        if (elapsed() > I.deadline) return false;
        if (I.nodes >= I.cap) return false;
    }
    int h = computeH(I);
    if (g + h > bound) return false;
    if (h == 0) return isGoal(I);
    if (g >= K) return false;

    for (int d = 0; d < 4; d++){
        if (last_dir >= 0 && d == OPP[last_dir]) continue;
        int nr = I.blank_r + DR[d], nc = I.blank_c + DC[d];
        if (nr<0||nr>=N||nc<0||nc>=N) continue;

        int moved_id = I.board[nr*N+nc];
        swap(I.board[I.blank_r*N+I.blank_c], I.board[nr*N+nc]);
        if (moved_id > 0){
            I.cur_r[moved_id] = I.blank_r; I.cur_c[moved_id] = I.blank_c;
        }
        int pr = I.blank_r, pc = I.blank_c;
        I.blank_r = nr; I.blank_c = nc;
        I.path.push_back(DCH[d]);

        if (dfs(I, d, g+1, bound, K)) return true;

        I.path.pop_back();
        I.blank_r = pr; I.blank_c = pc;
        swap(I.board[I.blank_r*N+I.blank_c], I.board[nr*N+nc]);
        if (moved_id > 0){ I.cur_r[moved_id] = nr; I.cur_c[moved_id] = nc; }
    }
    return false;
}

static int tryWindow(IDA& I, const short* start_board, int start_blank,
                     const short* end_board, int K, long long node_cap, double deadline,
                     string& new_seq){
    int ids_max = N * N + 4;
    I.tgt_r.assign(ids_max, -1);
    I.tgt_c.assign(ids_max, -1);
    I.cur_r.assign(ids_max, -1);
    I.cur_c.assign(ids_max, -1);
    I.board.assign(N*N, 0);

    for (int r=0; r<N; r++) for (int c=0; c<N; c++){
        short v = start_board[r*N+c];
        I.board[r*N+c] = v;
        if (v > 0){ I.cur_r[v] = r; I.cur_c[v] = c; }
    }
    int changed = 0;
    for (int r=0; r<N; r++) for (int c=0; c<N; c++){
        short v = end_board[r*N+c];
        if (v <= 0) continue;
        if (I.cur_r[v] != r || I.cur_c[v] != c){
            I.tgt_r[v] = r; I.tgt_c[v] = c; changed++;
        }
    }
    if (changed == 0){ new_seq = ""; return K; }

    I.blank_r = start_blank / N;
    I.blank_c = start_blank % N;
    I.nodes = 0; I.cap = node_cap; I.deadline = deadline;
    I.path.clear();

    int h0 = computeH(I);
    if (h0 >= K) return 0;

    for (int bound = h0; bound < K; bound++){
        I.nodes = 0;
        I.path.clear();
        if (dfs(I, -1, 0, bound, K)){
            new_seq = I.path;
            return K - (int)new_seq.size();
        }
        if (elapsed() > I.deadline) return 0;
        if (I.nodes >= I.cap) return 0;
    }
    return 0;
}

// ============================================================
// SHARED STATE for Phase 2/3
// ============================================================
static mutex g_S_mutex;
static string g_best_S;
static atomic<long long> g_total_saved{0};

static const int MAX_POST_THREADS = 16;   // 8 sweep + 8 SA
static mutex g_thread_best_mutex[MAX_POST_THREADS];
static string g_thread_best[MAX_POST_THREADS];

static void updateThreadBest(int tid, const string& S){
    lock_guard<mutex> lk(g_thread_best_mutex[tid]);
    if (g_thread_best[tid].empty() || S.size() < g_thread_best[tid].size()){
        g_thread_best[tid] = S;
    }
}

struct SweepArgs {
    int thread_id;
    int kind;
    vector<int> window_sizes;
    long long node_cap_per_window;
    double deadline;
};

static void sweepThread(SweepArgs A){
    IDA I;
    int pass = 0;
    int zero_streak = 0;               // consecutive passes with 0 improvements
    const int STREAK_LIMIT = 20;       // give up if 20 passes in a row find nothing

    while (elapsed() < A.deadline){
        pass++;
        g_S_mutex.lock();
        string S = g_best_S;
        g_S_mutex.unlock();

        Hist H; H.build(S);
        int n_ws = (int)A.window_sizes.size();
        int K = A.window_sizes[pass % n_ws];
        if ((int)S.size() <= K){
            // This K-tier is pointless if S is shorter than K. Check if ANY of our
            // tier's windows fit — if none do, exit (e.g., final solution is very short).
            bool any_fits = false;
            for (int k2 : A.window_sizes) if ((int)S.size() > k2){ any_fits = true; break; }
            if (!any_fits){
                logMsg("[Sweep T" + to_string(A.thread_id)
                       + "] exiting: S=" + to_string(S.size())
                       + " shorter than all window sizes in tier");
                return;
            }
            continue;   // just this K is too big; next pass may pick a smaller one
        }

        long long saved_this_pass = 0;
        int improvements = 0;

        vector<short> bA(N*N), bB(N*N);
        int blA, blB;
        int sz = (int)S.size();
        for (int i = 0; i < sz - K; i++){
            if (elapsed() > A.deadline) break;
            if ((i % 2000) == 0 && i > 0){
                g_S_mutex.lock();
                if ((int)g_best_S.size() != sz){
                    g_S_mutex.unlock(); break;
                }
                g_S_mutex.unlock();
            }
            H.at(i, bA.data(), blA);
            H.at(i + K, bB.data(), blB);

            string repl;
            int saved = tryWindow(I, bA.data(), blA, bB.data(), K,
                                  A.node_cap_per_window, A.deadline, repl);
            if (saved > 0){
                g_S_mutex.lock();
                if ((int)g_best_S.size() >= i + K
                    && g_best_S.substr(0, i + K) == S.substr(0, i + K)){
                    string newS = g_best_S.substr(0, i) + repl + g_best_S.substr(i + K);
                    newS = stripInversePairs(newS);
                    g_best_S = newS;
                    g_total_saved += saved;
                    saved_this_pass += saved;
                    improvements++;
                    logMsg("[Sweep T" + to_string(A.thread_id) + " K=" + to_string(K) + "] +"
                           + to_string(saved) + " at " + to_string(i) + " | S=" + to_string(g_best_S.size()));
                    string snap = g_best_S;
                    g_S_mutex.unlock();
                    updateThreadBest(A.thread_id, snap);
                    saveSolutionFile(g_out_prefix + "_sweep_T" + to_string(A.thread_id) + ".txt",
                                     snap, "sweep K=" + to_string(K));
                    S = snap; H.build(S); sz = (int)S.size();
                    i = max(0, i - K/2);
                } else {
                    g_S_mutex.unlock();
                    break;
                }
            }
        }
        logMsg("[Sweep T" + to_string(A.thread_id) + "] pass " + to_string(pass)
               + " K=" + to_string(K) + ": " + to_string(improvements) + " impr saved "
               + to_string(saved_this_pass) + " | global S=" + to_string(g_best_S.size()));

        // Track consecutive passes with 0 improvements. If this thread's K-tier
        // has nothing left to find, it's just wasting CPU — exit and let the
        // main orchestrator (checkpointer + other phases) reclaim it.
        if (improvements == 0){
            zero_streak++;
            if (zero_streak >= STREAK_LIMIT){
                logMsg("[Sweep T" + to_string(A.thread_id) + "] exiting: "
                       + to_string(STREAK_LIMIT) + " passes with 0 improvements");
                return;
            }
        } else {
            zero_streak = 0;
        }
    }
}

static void randomSAThread(SweepArgs A){
    mt19937 rng((uint32_t)time(nullptr) ^ (uint32_t)(A.thread_id * 7919 + 12345));
    IDA I;

    int outer_zero_streak = 0;
    const int OUTER_ZERO_LIMIT = 50;   // stop if 50 outer loops find nothing

    while (elapsed() < A.deadline){
        g_S_mutex.lock();
        string S = g_best_S;
        g_S_mutex.unlock();

        Hist H; H.build(S);
        int sz = (int)S.size();
        if (sz < 20) break;

        // SA window set tuned per N (accessed via global N)
        static const int Ks_small[]  = { 8, 10, 12, 15, 20, 30, 40, 60, 80, 100, 150, 200 };      // N <= 35
        static const int Ks_medium[] = { 15, 20, 30, 50, 80, 120, 180, 250, 350 };                 // N 36..55
        static const int Ks_large[]  = { 20, 30, 50, 100, 150, 200, 300, 400, 500 };               // N >= 56
        const int* Ks;
        int n_Ks;
        if (N <= 35){ Ks = Ks_small;  n_Ks = sizeof(Ks_small)  / sizeof(int); }
        else if (N <= 55){ Ks = Ks_medium; n_Ks = sizeof(Ks_medium) / sizeof(int); }
        else{ Ks = Ks_large;  n_Ks = sizeof(Ks_large)  / sizeof(int); }
        int K = Ks[rng() % n_Ks];
        if (sz <= K) continue;

        vector<short> bA(N*N), bB(N*N);
        int blA, blB;

        int iters = 500;
        int improvements = 0;
        for (int it = 0; it < iters && elapsed() < A.deadline; it++){
            int i = rng() % (sz - K);
            H.at(i, bA.data(), blA);
            H.at(i + K, bB.data(), blB);
            string repl;
            int saved = tryWindow(I, bA.data(), blA, bB.data(), K,
                                  A.node_cap_per_window, A.deadline, repl);
            if (saved > 0){
                g_S_mutex.lock();
                if ((int)g_best_S.size() >= i + K
                    && g_best_S.substr(0, i + K) == S.substr(0, i + K)){
                    string newS = g_best_S.substr(0, i) + repl + g_best_S.substr(i + K);
                    newS = stripInversePairs(newS);
                    g_best_S = newS;
                    g_total_saved += saved;
                    improvements++;
                    logMsg("[SA T" + to_string(A.thread_id) + " K=" + to_string(K) + "] +"
                           + to_string(saved) + " at " + to_string(i) + " | S=" + to_string(g_best_S.size()));
                    string snap = g_best_S;
                    g_S_mutex.unlock();
                    updateThreadBest(A.thread_id, snap);
                    saveSolutionFile(g_out_prefix + "_sa_T" + to_string(A.thread_id - 8) + ".txt",
                                     snap, "SA K=" + to_string(K));
                    S = snap; H.build(S); sz = (int)S.size();
                } else {
                    g_S_mutex.unlock(); break;
                }
            }
        }
        logMsg("[SA T" + to_string(A.thread_id) + "] random K=" + to_string(K)
               + " iters=" + to_string(iters) + " impr=" + to_string(improvements));

        // If nothing found in this entire outer loop (500 random samples across the whole string
        // with this K), unlikely we'll find anything later. Track zero streaks.
        if (improvements == 0){
            outer_zero_streak++;
            if (outer_zero_streak >= OUTER_ZERO_LIMIT){
                logMsg("[SA T" + to_string(A.thread_id) + "] exiting: "
                       + to_string(OUTER_ZERO_LIMIT) + " outer loops with 0 improvements");
                return;
            }
        } else {
            outer_zero_streak = 0;
        }
    }
}

// ============================================================
// CHECKPOINT + SIGNAL
// ============================================================
static atomic<bool> g_stop{false};

static void checkpointLoop(double deadline){
    while (!g_stop.load() && elapsed() < deadline){
        for (int i = 0; i < 300 && !g_stop.load(); i++){ sleep(1); }
        g_S_mutex.lock();
        string snap = g_best_S;
        g_S_mutex.unlock();
        if (!snap.empty()){
            saveSolutionFile(g_out_prefix + "_final.txt", snap,
                             "[checkpoint t=" + to_string((int)elapsed()) + "s]");
            logMsg("[ckpt] saved S=" + to_string(snap.size()) + " to " + g_out_prefix + "_final.txt");
        }
    }
}

static void sigintHandler(int){
    g_stop.store(true);
    g_S_mutex.lock();
    string snap = g_best_S;
    g_S_mutex.unlock();
    if (!snap.empty()){
        saveSolutionFile(g_out_prefix + "_final.txt", snap, "[SIGINT]");
    }
    for (int i = 0; i < MAX_POST_THREADS; i++){
        lock_guard<mutex> lk(g_thread_best_mutex[i]);
        if (!g_thread_best[i].empty()){
            string name = (i < 8) ? ("_sweep_T" + to_string(i))
                                  : ("_sa_T" + to_string(i - 8));
            saveSolutionFile(g_out_prefix + name + ".txt",
                             g_thread_best[i], "[SIGINT]");
        }
    }
    cerr << "\n[SIGINT] Saved S=" << snap.size() << "\n";
    _exit(0);
}

// ============================================================
// MAIN
// ============================================================
int main(int argc, char** argv){
    if (argc < 3){
        cerr << "usage: " << argv[0] << " <puzzle.txt> <output_prefix> [hours]\n";
        cerr << "\nOutputs (all with trailing S):\n";
        cerr << "  <prefix>_final.txt          -- best across all threads (submit this)\n";
        cerr << "  <prefix>_phase1.txt         -- after Phase 1 only\n";
        cerr << "  <prefix>_sweep_T{0-7}.txt   -- per-sweep-thread best\n";
        cerr << "  <prefix>_sa_T{0-7}.txt      -- per-SA-thread best\n";
        cerr << "\nExample:  " << argv[0] << " n67_puzzle.txt result 23\n";
        return 1;
    }
    double hours = (argc >= 4) ? atof(argv[3]) : 23.0;
    g_out_prefix = argv[2];


    signal(SIGINT, sigintHandler);
    signal(SIGTERM, sigintHandler);

    readPuzzle(argv[1]);
    FLAT_LIM = N * N * N * N;
    cerr << "N=" << N << " M=" << M << "\n";
    cerr << "Output prefix: " << g_out_prefix << "\n";
    cerr << "Budget: " << hours << " hours\n";
    cerr << "FLAT_LIM = " << FLAT_LIM << " (A* ctx ~"
         << (long long)FLAT_LIM * 13 / (1024*1024) << " MB per thread)\n";

    // Check if already solved
    bool solved = true;
    for (int r = 0; r < M && solved; r++) for (int c = 0; c < M; c++)
        if (init_board[r+1][c+1] != tgt[r][c]){ solved = false; break; }
    if (solved){
        cerr << "Board is already solved.\n";
        g_best_S = "";
        saveSolutionFile(g_out_prefix + "_final.txt", g_best_S, "[already solved]");
        cout << "FINAL: 0 moves -> " << g_out_prefix << "_final.txt\n";
        return 0;
    }

    // Decide beam width & P1 threads based on N (memory-aware, tuned per-size).
    // p1_threads is capped at 2 due to concurrency issues with 4+ P1 threads.
    int beam_width;
    int p1_threads;
    if (N <= 15){
        beam_width = 6767; p1_threads = 2;
    } else if (N <= 25){
        beam_width = 6767; p1_threads = 2;
    } else if (N <= 35){
        beam_width = 6767; p1_threads = 2;
    } else if (N <= 55){
        beam_width = 67; p1_threads = 2;
    } else {
        beam_width = 67; p1_threads = 2;
    }

    double total = hours * 3600.0;
    // P1 budget: smaller N completes much faster, so allocate less to P1 and more
    // to compression phases. For N=33 the sequence is only ~38k so Phase 2 benefits
    // most from longer runtime. For N=67 we need most time on P1 just to get a valid
    // starting solution.
    double p1_frac;
    if (N <= 20)       p1_frac = 0.67;
    else if (N <= 35)  p1_frac = 0.67;
    else if (N <= 55)  p1_frac = 0.67;
    else               p1_frac = 0.67;  
    double p1_budget = total * p1_frac;
    double p2_budget = (total - p1_budget) * 0.60;
    double p3_budget = total - p1_budget - p2_budget;
    cerr << "Schedule: P1 " << (int)p1_budget << "s, P2 " << (int)p2_budget
         << "s, P3 " << (int)p3_budget << "s\n";
    cerr << "P1 threads=" << p1_threads << " beam_width=" << beam_width << "\n";

    // ---------------- PHASE 1 ----------------
    logMsg("===== PHASE 1 START =====");
    double p1_deadline = elapsed() + p1_budget;

    // Ordering strategies: row/col snake from all 4 corners. Row-snake is the
    // classic reliable sliding-puzzle approach — outer-first so blank can always
    // reach any unsolved cell through the remaining unsolved region.
    //
    // We use 8 strategies to explore more of the search space. P1 is limited to
    // 2 concurrent threads (4+ thread crash is a known unfixed bug — see session
    // notes), so we run MULTIPLE WAVES of 2 threads each, cycling through
    // strategies. Each wave's best is kept; final P1 output = best across all waves.
    struct Strat { string name; vector<pair<int,int>> order; };
    vector<Strat> strats;
    // Row/col snake from all 4 corners — classic reliable orderings (never STUCK).
    strats.push_back({ "row-snake-TL",  buildSnakeOrder(true,  false, false) });
    strats.push_back({ "col-snake-TL",  buildSnakeOrder(false, false, false) });
    strats.push_back({ "row-snake-TR",  buildSnakeOrder(true,  true,  false) });
    strats.push_back({ "col-snake-TR",  buildSnakeOrder(false, true,  false) });
    strats.push_back({ "row-snake-BL",  buildSnakeOrder(true,  false, true ) });
    strats.push_back({ "col-snake-BL",  buildSnakeOrder(false, false, true ) });
    strats.push_back({ "row-snake-BR",  buildSnakeOrder(true,  true,  true ) });
    strats.push_back({ "col-snake-BR",  buildSnakeOrder(false, true,  true ) });
    // Spiral orderings — outside-in. Can STUCK due to parity in final 3x3 inner
    // region. Kept as experimental — may succeed on some inputs.
    strats.push_back({ "spiral-CW",     buildOutsideInOrder(false) });
    strats.push_back({ "spiral-CCW",    buildOutsideInOrder(true ) });

    // Per-N: how many waves to attempt given the total P1 budget. Each wave
    // needs enough time to finish P1, so we cap waves based on N.
    // Small N finishes in seconds → many waves; large N needs most time for one wave.
    int max_waves;
    if (N <= 15)       max_waves = 8;
    else if (N <= 25)  max_waves = 4;
    else if (N <= 35)  max_waves = 8;   // N=33: 8 waves × 2 = all 16 slots, cycles through 8 snake strategies
    else if (N <= 55)  max_waves = 2;   // N=51: 2 waves × 2 threads = 4 strategies
    else               max_waves = 2;   // N=67: 2 waves so row+col snake both get a shot

    string best_p1;
    int valid_count = 0;
    int all_p1_threads_run = 0;
    vector<P1Args> all_p1_results;      // accumulate across waves for file output

    // Wave-scheduling strategy: the FIRST wave gets enough time to finish
    // (based on conservative per-N estimate), then remaining waves share the
    // leftover time. If any wave produced a full valid result early, subsequent
    // waves continue running (more strategies = more chances for a shorter
    // solution), but if no full result has been found yet we prioritize giving
    // the current wave its full needed time.
    double min_wave_time;
    if (N <= 11)       min_wave_time = 90;      // N=9: needs ~60-120s
    else if (N <= 15)  min_wave_time = 240;
    else if (N <= 25)  min_wave_time = 600;
    else if (N <= 35)  min_wave_time = 4500;    // N=33: ~75 min/wave × 8 waves = 10hr P1
    else if (N <= 55)  min_wave_time = 4800;    // N=51: ~80 min
    else               min_wave_time = 21600;   // N=67: ~6 hr per wave at beam=1000, 2 waves fit in 12hr P1

    for (int wave = 0; wave < max_waves; wave++){
        double remaining = p1_deadline - elapsed();
        if (remaining <= 0) break;

        // Determine wave deadline. We prefer min_wave_time but cap at remaining/waves_left
        // if we're running out of budget.
        int waves_left = max_waves - wave;
        double share = remaining / waves_left;
        double wave_budget = max(share, min_wave_time);
        // But never exceed remaining budget
        if (wave_budget > remaining) wave_budget = remaining;
        // And if the wave can't possibly finish in allotted time AND we already
        // have a valid full solution, skip the remaining waves to let P2/P3 run
        if (wave_budget < min_wave_time * 0.5 && !best_p1.empty()){
            logMsg("[P1 wave " + to_string(wave+1) + "] skipping: only "
                   + to_string((int)wave_budget) + "s left, need ~"
                   + to_string((int)min_wave_time) + "s");
            break;
        }
        double wave_deadline = elapsed() + wave_budget;

        logMsg("[P1 wave " + to_string(wave+1) + "/" + to_string(max_waves)
               + "] strategies=[" + strats[(2*wave) % strats.size()].name + ", "
               + strats[(2*wave+1) % strats.size()].name + "] budget="
               + to_string((int)wave_budget) + "s");

        vector<P1Args> wave_args(p1_threads);
        vector<thread> p1_ths;
        for (int i = 0; i < p1_threads; i++){
            int strat_idx = (2 * wave + i) % strats.size();
            wave_args[i].thread_id = all_p1_threads_run + i;
            wave_args[i].strategy_name = strats[strat_idx].name;
            wave_args[i].order = strats[strat_idx].order;
            wave_args[i].beam_width = beam_width;
            wave_args[i].deadline = wave_deadline;
            p1_ths.emplace_back(runPhase1, &wave_args[i]);
        }
        for (auto& t : p1_ths) t.join();
        all_p1_threads_run += p1_threads;

        // Absorb wave results, track best
        for (auto& a : wave_args){
            string fname = g_out_prefix + "_phase1_T" + to_string(a.thread_id) + ".txt";
            if (!a.result.empty()){
                string cleaned = stripInversePairs(a.result);
                if (validate(cleaned)){
                    valid_count++;
                    saveSolutionFile(fname, cleaned,
                                     "[P1 " + a.strategy_name + " FULL length=" + to_string(cleaned.size()) + "]");
                    logMsg("[P1 T" + to_string(a.thread_id) + " " + a.strategy_name + "] FULL valid: "
                           + to_string(cleaned.size()) + " moves");
                    if (best_p1.empty() || cleaned.size() < best_p1.size()){
                        best_p1 = cleaned;
                        logMsg("[P1 wave " + to_string(wave+1) + "] NEW BEST: "
                               + to_string(best_p1.size()) + " (via " + a.strategy_name + ")");
                    }
                } else {
                    saveSolutionFile(fname, a.result,
                                     "[P1 " + a.strategy_name + " INVALID length=" + to_string(a.result.size()) + "]");
                    logMsg("[P1 T" + to_string(a.thread_id) + " " + a.strategy_name + "] INVALID, saved as-is");
                }
            } else if (!a.partial.empty()){
                saveSolutionFile(fname, a.partial,
                                 "[P1 " + a.strategy_name + " PARTIAL step=" + to_string(a.partial_step)
                                 + "/" + to_string((int)a.order.size())
                                 + " length=" + to_string(a.partial.size()) + "]");
            }
            all_p1_results.push_back(std::move(a));
        }

        // After each wave: dump the CURRENT best to stdout (grep-friendly) AND
        // save to _final.txt so the user can pick up the latest at any time,
        // even mid-run. Especially important for N=67 where runs are long and
        // you may want to grab wave 1's result while wave 2 is still cooking.
        if (!best_p1.empty()){
            printSolutionToStdout(best_p1, "WAVE " + to_string(wave+1));
            saveSolutionFile(g_out_prefix + "_final.txt", best_p1,
                             "[after wave " + to_string(wave+1) + " length=" + to_string(best_p1.size()) + "]");
            saveSolutionFile(g_out_prefix + "_wave" + to_string(wave+1) + ".txt", best_p1,
                             "[wave " + to_string(wave+1) + " best length=" + to_string(best_p1.size()) + "]");
            logMsg("[P1 wave " + to_string(wave+1) + "] BEST SO FAR: "
                   + to_string(best_p1.size()) + " | saved to "
                   + g_out_prefix + "_final.txt AND _wave" + to_string(wave+1) + ".txt");
        }

        if (elapsed() >= p1_deadline) break;
    }


    if (best_p1.empty()){
        cerr << "\nFATAL: no Phase 1 thread produced a valid full solution.\n";
        cerr << "  Partial results (if any) saved to " << g_out_prefix << "_phase1_T*.txt\n";
        cerr << "  Common causes:\n";
        cerr << "    - Beam too narrow: current beam_width=" << beam_width << ". Try increasing.\n";
        cerr << "    - Unlucky initial board. Try row-snake and col-snake with more threads.\n";
        cerr << "    - A* expand limit too small for dense layouts.\n";
        return 2;
    }
    logMsg("===== PHASE 1 DONE: " + to_string(best_p1.size())
           + " moves (from " + to_string(valid_count) + "/" + to_string(all_p1_threads_run)
           + " thread-waves) =====");
    saveSolutionFile(g_out_prefix + "_phase1.txt", best_p1,
                     "[best P1 across " + to_string(valid_count) + " valid runs]");
    printSolutionToStdout(best_p1, "PHASE 1");

    g_best_S = best_p1;
    for (int i = 0; i < MAX_POST_THREADS; i++) g_thread_best[i] = g_best_S;
    saveSolutionFile(g_out_prefix + "_final.txt", g_best_S, "[initial after P1]");

    // ---------------- CHECKPOINT THREAD ----------------
    thread ckpt_th(checkpointLoop, total);

    // ---------------- PHASE 2: SWEEP ----------------
    logMsg("===== PHASE 2 START =====");
    double p2_end = elapsed() + p2_budget;
    {
        vector<thread> ths;
        vector<SweepArgs> args(8);
        // 8 sweep threads, each scanning a different K-range. Small K (4-14) is
        // where IDA* can actually exhaust the search space and find shortcuts;
        // medium K (20-50) catches longer redundancies but hits node caps sooner.
        if (N <= 35){
            // N=33: solutions ~38-48k. Heavy focus on very small K.
            args[0] = { 0, 0, {4, 5, 6},              500000000LL, p2_end };
            args[1] = { 1, 0, {7, 8, 9},              500000000LL, p2_end };
            args[2] = { 2, 0, {10, 11, 12},           500000000LL, p2_end };
            args[3] = { 3, 0, {13, 14, 15},           400000000LL, p2_end };
            args[4] = { 4, 0, {16, 18, 20},           300000000LL, p2_end };
            args[5] = { 5, 0, {22, 25, 28},           250000000LL, p2_end };
            args[6] = { 6, 0, {30, 35, 40},           200000000LL, p2_end };
            args[7] = { 7, 0, {45, 50, 60},           150000000LL, p2_end };
        } else if (N <= 55){
            // N=51: solutions ~120-150k.
            args[0] = { 0, 0, {4, 5, 6},              500000000LL, p2_end };
            args[1] = { 1, 0, {7, 8, 9},              500000000LL, p2_end };
            args[2] = { 2, 0, {10, 11, 12},           500000000LL, p2_end };
            args[3] = { 3, 0, {13, 14, 15},           400000000LL, p2_end };
            args[4] = { 4, 0, {16, 18, 20},           300000000LL, p2_end };
            args[5] = { 5, 0, {22, 25, 28},           250000000LL, p2_end };
            args[6] = { 6, 0, {30, 35, 40},           200000000LL, p2_end };
            args[7] = { 7, 0, {45, 50, 60},           150000000LL, p2_end };
        } else {
            // N=67: solutions ~350-400k. Same small-K focus.
            args[0] = { 0, 0, {4, 5, 6},              500000000LL, p2_end };
            args[1] = { 1, 0, {7, 8, 9},              500000000LL, p2_end };
            args[2] = { 2, 0, {10, 11, 12},           500000000LL, p2_end };
            args[3] = { 3, 0, {13, 14, 15},           400000000LL, p2_end };
            args[4] = { 4, 0, {16, 18, 20},           300000000LL, p2_end };
            args[5] = { 5, 0, {22, 25, 28},           250000000LL, p2_end };
            args[6] = { 6, 0, {30, 35, 40},           200000000LL, p2_end };
            args[7] = { 7, 0, {45, 50, 60},           150000000LL, p2_end };
        }
        for (int i = 0; i < 8; i++) ths.emplace_back(sweepThread, args[i]);
        for (auto& t : ths) t.join();
    }
    logMsg("===== PHASE 2 DONE: S=" + to_string(g_best_S.size()) + " =====");
    {
        lock_guard<mutex> lk(g_S_mutex);
        printSolutionToStdout(g_best_S, "PHASE 2");
    }

    // ---------------- PHASE 3: SA ----------------
    logMsg("===== PHASE 3 START =====");
    double p3_end = total;
    {
        vector<thread> ths;
        vector<SweepArgs> args(8);
        // 8 SA threads, each with different random seeds for distinct offset coverage
        for (int i = 0; i < 8; i++){
            args[i] = { 8 + i, 1, {}, 100000000LL, p3_end };
        }
        for (int i = 0; i < 8; i++) ths.emplace_back(randomSAThread, args[i]);
        for (auto& t : ths) t.join();
    }
    logMsg("===== PHASE 3 DONE =====");
    {
        lock_guard<mutex> lk(g_S_mutex);
        printSolutionToStdout(g_best_S, "PHASE 3");
    }

    g_stop.store(true);
    ckpt_th.join();

    g_best_S = stripInversePairs(g_best_S);
    if (!validate(g_best_S)){
        cerr << "WARNING: final does not validate! Reverting to phase 1.\n";
        g_best_S = best_p1;
    }

    // Save all finals
    saveSolutionFile(g_out_prefix + "_final.txt", g_best_S, "[FINAL]");
    for (int i = 0; i < MAX_POST_THREADS; i++){
        string name = (i < 4) ? ("_sweep_T" + to_string(i))
                              : ("_sa_T" + to_string(i - 4));
        lock_guard<mutex> lk(g_thread_best_mutex[i]);
        if (!g_thread_best[i].empty()){
            saveSolutionFile(g_out_prefix + name + ".txt",
                             g_thread_best[i], "[FINAL for this thread]");
        }
    }

    cout << "\n===== RESULT SUMMARY =====\n";
    cout << "FINAL (merged best):      " << g_best_S.size() << " moves  -> " << g_out_prefix << "_final.txt\n";
    cout << "Phase 1 only:             " << best_p1.size() << " moves  -> " << g_out_prefix << "_phase1.txt\n";
    for (int i = 0; i < 4; i++){
        lock_guard<mutex> lk(g_thread_best_mutex[i]);
        cout << "Sweep thread T" << i << " best:     "
             << (g_thread_best[i].empty() ? 0 : (int)g_thread_best[i].size())
             << " moves  -> " << g_out_prefix << "_sweep_T" << i << ".txt\n";
    }
    for (int i = 0; i < 4; i++){
        lock_guard<mutex> lk(g_thread_best_mutex[i + 4]);
        cout << "SA thread    T" << i << " best:     "
             << (g_thread_best[i+4].empty() ? 0 : (int)g_thread_best[i+4].size())
             << " moves  -> " << g_out_prefix << "_sa_T" << i << ".txt\n";
    }
    cout << "===========================\n";
    cerr << "Total wall time: " << (int)elapsed() << "s\n";
    return 0;
}