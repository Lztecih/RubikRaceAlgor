// ============================================================
// Rubik's Race — PHASE 1 ONLY SOLVER (No Time Limit)
// ============================================================
// Reads puzzle, solves with Phase 1 (beam search), saves best result.
//
// COMPILE:
//   g++ -O3 -std=c++17 -pthread solver.cpp -o solver
//
// USAGE:
//   ./solver <puzzle.txt> <output_prefix>
//
// OUTPUTS:
//   <prefix>_final.txt     -- best solution
//   <prefix>_phase1.txt    -- Phase 1 result
//   <prefix>_phase1_T*.txt -- per-thread results
// ============================================================

#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <queue>
#include <algorithm>
#include <cstring>
#include <cstdlib>
#include <cstdio>
#include <cstdint>
#include <climits>
#include <chrono>
#include <thread>
#include <mutex>
#include <atomic>
#include <csignal>
#include <unistd.h>

using namespace std;
using namespace chrono;

// ============================================================
// GLOBALS
// ============================================================
static int N, M;
static const int MAXN = 70;
static const int DR[4] = { 1, -1, 0, 0 };
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
// INPUT + VALIDATION
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
// FILE + LOG
// ============================================================
static mutex g_file_mutex;
static void saveSolutionFile(const string& path, const string& S, const string& note){
    lock_guard<mutex> lk(g_file_mutex);
    ofstream f(path);
    f << S << "S\n";
    f << "// length=" << S.size() << "  " << note << "\n";
}

static mutex g_stdout_mutex;
static void printSolutionToStdout(const string& S, const string& tag){
    lock_guard<mutex> lk(g_stdout_mutex);
    cout << "\n===== SOLUTION AFTER " << tag
         << " (length=" << S.size() << ") =====\n";
    cout << S << "S\n===== END " << tag << " =====\n" << flush;
}

static mutex g_log_mutex;
static void logMsg(const string& s){
    lock_guard<mutex> lk(g_log_mutex);
    cerr << "[t=" << (int)elapsed() << "s] " << s << "\n";
}

// ============================================================
// PHASE 1: A* + BEAM SEARCH
// ============================================================
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
};

static inline int hRouting(int tr, int tc, int gr, int gc, int br, int bc){
    int dt = abs(tr - gr) + abs(tc - gc);
    if (dt == 0) return 0;
    int db = abs(br - tr) + abs(bc - tc);
    return dt + max(0, db - 1);
}

static bool astarRoute(
    AstarCtx& ctx, const uint8_t* locked,
    int tr0, int tc0, int gr, int gc, int br0, int bc0,
    string& out_path, int expand_limit = 300000
){
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

static vector<pair<int,int>> buildOutsideInOrder(bool reverse_spiral = false){
    vector<pair<int,int>> order;
    int top = 0, bot = M - 1, left = 0, right = M - 1;
    while (top <= bot && left <= right){
        if (top == bot){
            for (int c = left; c <= right; c++) order.push_back({top, c});
            break;
        }
        if (left == right){
            for (int r = top; r <= bot; r++) order.push_back({r, left});
            break;
        }
        if (!reverse_spiral){
            for (int c = left; c < right; c++) order.push_back({top, c});
            for (int r = top; r < bot; r++) order.push_back({r, right});
            for (int c = right; c > left; c--) order.push_back({bot, c});
            for (int r = bot; r > top; r--) order.push_back({r, left});
        } else {
            for (int r = top; r < bot; r++) order.push_back({r, left});
            for (int c = left; c < right; c++) order.push_back({bot, c});
            for (int r = bot; r > top; r--) order.push_back({r, right});
            for (int c = right; c > left; c--) order.push_back({top, c});
        }
        top++; bot--; left++; right--;
    }
    return order;
}

struct BState {
    vector<short> board;
    vector<uint8_t> locked;
    int br, bc;
    string moves;
    int step;
    long long score;
    BState() : board(MAXN*MAXN, 0), locked(MAXN*MAXN, 0), br(0), bc(0), step(0), score(0) {}
};

struct P1Args {
    int thread_id;
    string strategy_name;
    vector<pair<int,int>> order;
    int beam_width;
    string result;
    string partial;
    int partial_step = 0;
};

static void runPhase1(P1Args* A){
    const auto& order = A->order;
    unique_ptr<AstarCtx> ctx(new AstarCtx());
    try { ctx->init(); }
    catch (const std::bad_alloc&){
        logMsg("[P1 T" + to_string(A->thread_id) + "] OUT OF MEMORY");
        return;
    }

    BState init;
    for (int r = 0; r < N; r++) for (int c = 0; c < N; c++)
        init.board[r * MAXN + c] = (short)init_board[r][c];
    init.br = init_br;
    init.bc = init_bc;

    vector<BState> beam{std::move(init)};
    int total = (int)order.size();

    for (int step = 0; step < total; step++){
        int ti = order[step].first, tj = order[step].second;
        int gr = ti + 1, gc = tj + 1;
        int color = tgt[ti][tj];

        int next_gr = -1, next_gc = -1;
        if (step + 1 < total){
            auto [nti, ntj] = order[step + 1];
            next_gr = nti + 1; next_gc = ntj + 1;
        }

        vector<BState> next_beam;
        next_beam.reserve(A->beam_width * 3);

        for (auto& st : beam){
            if (st.board[gr * MAXN + gc] == color && !st.locked[gr * MAXN + gc]){
                BState ns = st;
                ns.locked[gr * MAXN + gc] = 1;
                ns.step = step + 1;
                long long blank_penalty = (next_gr >= 0) ? abs(ns.br - next_gr) + abs(ns.bc - next_gc) : 0;
                ns.score = (long long)ns.moves.size() * 1024 + blank_penalty;
                next_beam.push_back(std::move(ns));
                continue;
            }

            struct Cand { int r, c, cost; };
            vector<Cand> cands;
            for (int r = 0; r < N; r++) for (int c = 0; c < N; c++){
                if (st.locked[r * MAXN + c]) continue;
                if (st.board[r * MAXN + c] == color){
                    cands.push_back({r, c, abs(r-gr) + abs(c-gc)});
                }
            }
            if (cands.empty()) continue;
            sort(cands.begin(), cands.end(), [](const Cand& a, const Cand& b){ return a.cost < b.cost; });

            int tried = 0;
            int remaining = total - step;
            int max_tries = (remaining > 400) ? 4 : (remaining > 100) ? 6 : 12;

            for (auto& cd : cands){
                if (tried >= max_tries) break;
                tried++;
                string path;
                int astar_budget = 100000 + N*N*200;
                bool ok = astarRoute(*ctx, st.locked.data(), cd.r, cd.c, gr, gc, st.br, st.bc, path, astar_budget);
                if (!ok) continue;

                BState ns = st;
                applyPath(ns.board.data(), ns.br, ns.bc, path);
                ns.moves += path;
                ns.locked[gr * MAXN + gc] = 1;
                ns.step = step + 1;
                long long blank_penalty = (next_gr >= 0) ? abs(ns.br - next_gr) + abs(ns.bc - next_gc) : 0;
                ns.score = (long long)ns.moves.size() * 1024 + blank_penalty;
                next_beam.push_back(std::move(ns));
            }
        }

        if (next_beam.empty()){
            logMsg("[P1 T" + to_string(A->thread_id) + "] STUCK at step " + to_string(step));
            if (!beam.empty()) A->partial = beam[0].moves;
            return;
        }

        sort(next_beam.begin(), next_beam.end(), [](const BState& a, const BState& b){ return a.score < b.score; });

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

    if (!beam.empty()){
        if (beam[0].step >= total) A->result = beam[0].moves;
        else A->partial = beam[0].moves;
    }
}

// ============================================================
// SIGNAL
// ============================================================
static atomic<bool> g_stop{false};

static void sigintHandler(int){
    g_stop.store(true);
    cerr << "\n[SIGINT] Exiting...\n";
    _exit(0);
}

// ============================================================
// MAIN
// ============================================================
int main(int argc, char** argv){
    if (argc < 3){
        cerr << "usage: " << argv[0] << " <puzzle.txt> <output_prefix>\n";
        return 1;
    }
    g_out_prefix = argv[2];

    signal(SIGINT, sigintHandler);
    signal(SIGTERM, sigintHandler);

    readPuzzle(argv[1]);
    FLAT_LIM = N * N * N * N;
    cerr << "N=" << N << " M=" << M << "  FLAT_LIM=" << FLAT_LIM << "\n";

    bool solved = true;
    for (int r = 0; r < M && solved; r++)
        for (int c = 0; c < M; c++)
            if (init_board[r+1][c+1] != tgt[r][c]){ solved = false; break; }

    if (solved){
        cerr << "Board is already solved.\n";
        saveSolutionFile(g_out_prefix + "_final.txt", "", "[already solved]");
        return 0;
    }

    // ============================================================
    // Config 
    // ============================================================
    int beam_width, p1_threads,max_waves;                 // =================
    
    p1_threads = 2;                                       // =================
                                                          // =================
    if (N <= 15){                                         // =================
        beam_width = 1000;                               // =================
    } else if (N <= 25){                                 // =================
        beam_width = 6767;                               // =================
    } else if (N <= 35){                                // =================
        beam_width = 6767;                               // =================
    } else if (N <= 55){                                // =================
        beam_width = 67;                                // =================
    } else {                                             // =================
        beam_width = 67;                                 // =================
    }                                                    // =================
                                                         // =================
                                                         // =================
    if (N <= 15)       max_waves = 8;                    // =================
    else if (N <= 25)  max_waves = 4;                    // =================
    else if (N <= 35)  max_waves = 8;                    // =================
    else if (N <= 55)  max_waves = 2;                    // =================
    else  max_waves = 2;                                 // =================
    // ============================================================

    logMsg("===== PHASE 1 START (No time limit) =====");
    logMsg("beam_width=" + to_string(beam_width) + "  max_waves=" + to_string(max_waves));

    struct Strat { string name; vector<pair<int,int>> order; };
    vector<Strat> strats = {
        {"row-snake-TL",  buildSnakeOrder(true,  false, false)},
        {"col-snake-TL",  buildSnakeOrder(false, false, false)},
        {"row-snake-TR",  buildSnakeOrder(true,  true,  false)},
        {"col-snake-TR",  buildSnakeOrder(false, true,  false)},
        {"row-snake-BL",  buildSnakeOrder(true,  false, true )},
        {"col-snake-BL",  buildSnakeOrder(false, false, true )},
        {"row-snake-BR",  buildSnakeOrder(true,  true,  true )},
        {"col-snake-BR",  buildSnakeOrder(false, true,  true )},
        {"spiral-CW",     buildOutsideInOrder(false)},
        {"spiral-CCW",    buildOutsideInOrder(true)}
    };

    string best_p1;

    for (int wave = 0; wave < max_waves; wave++){
        logMsg("[P1 wave " + to_string(wave+1) + "/" + to_string(max_waves) + "] starting");

        vector<P1Args> wave_args(p1_threads);
        vector<thread> p1_ths;

        for (int i = 0; i < p1_threads; i++){
            int idx = (2 * wave + i) % strats.size();
            wave_args[i].thread_id = wave * p1_threads + i;
            wave_args[i].strategy_name = strats[idx].name;
            wave_args[i].order = strats[idx].order;
            wave_args[i].beam_width = beam_width;
            p1_ths.emplace_back(runPhase1, &wave_args[i]);
        }
        for (auto& t : p1_ths) t.join();

        for (auto& a : wave_args){
            string fname = g_out_prefix + "_phase1_T" + to_string(a.thread_id) + ".txt";
            if (!a.result.empty()){
                string cleaned = stripInversePairs(a.result);
                if (validate(cleaned)){
                    saveSolutionFile(fname, cleaned, "[P1 FULL]");
                    if (best_p1.empty() || cleaned.size() < best_p1.size()){
                        best_p1 = std::move(cleaned);
                        logMsg("[P1] NEW BEST: " + to_string(best_p1.size()) + " moves");
                    }
                }
            } else if (!a.partial.empty()){
                saveSolutionFile(fname, a.partial, "[P1 PARTIAL]");
            }
        }

        if (!best_p1.empty()){
            printSolutionToStdout(best_p1, "WAVE " + to_string(wave+1));
            saveSolutionFile(g_out_prefix + "_final.txt", best_p1, "[after wave " + to_string(wave+1) + "]");
        }
    }

    if (best_p1.empty()){
        cerr << "No valid solution found.\n";
        return 2;
    }

    string final_sol = stripInversePairs(best_p1);
    saveSolutionFile(g_out_prefix + "_phase1.txt", final_sol, "[Phase 1 best]");
    saveSolutionFile(g_out_prefix + "_final.txt", final_sol, "[FINAL]");

    printSolutionToStdout(final_sol, "FINAL");
    logMsg("===== DONE: " + to_string(final_sol.size()) + " moves =====");

    return 0;
}