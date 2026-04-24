// ============================================================
// STANDALONE VACUUM — PARANOID VERSION
// ============================================================
// This version validates the ENTIRE current solution after every
// improvement, before writing to disk. If validation ever fails,
// the improvement is rolled back and the program exits with
// error — guaranteeing best_vacuum.txt is ALWAYS valid.
//
// Slower than vacuum_safe, but correctness is guaranteed.
// For a 143k solution, adds ~0.5s per improvement, but with
// ~500 improvements total that's only ~4 minutes overhead.
//
// Compile: g++ -O3 -std=c++17 vacuum_paranoid.cpp -o vacuum_paranoid
// Usage:   (cat puzzle.txt; cat solution.txt) | ./vacuum_paranoid
// ============================================================

#include <iostream>
#include <vector>
#include <string>
#include <cmath>
#include <algorithm>
#include <cstring>
#include <fstream>
#include <ctime>
#include <iomanip>

using namespace std;

int N, M, N2;

const int DR[] = {1, -1, 0, 0};
const int DC[] = {0, 0, 1, -1};
const char CH[] = {'U', 'D', 'L', 'R'};

int target_r[5000], target_c[5000];
int target_blank_r = -1, target_blank_c = -1;

static const int N2_MAX = 67 * 67;

static vector<short> g_hist;
static vector<int> g_br, g_bc;

long long opt_nodes = 0;
long long ida_node_cap = 0;
bool ida_timeout = false;

int g_best_len = -1;
int g_save_pass = 0;
int g_save_win = 0;

// globals for validation
static vector<short> g_init_board;
static int g_init_br, g_init_bc;
static vector<vector<int>> g_target_inner;
static vector<short> g_id_to_color;

// ============================================================
// FULL VALIDATION of a solution string
// ============================================================
// Returns true iff the solution plays without going out of bounds
// and the final inner (N-2)x(N-2) region matches the target colors.
// If fail_idx != nullptr, it's set to the index of the first
// problematic move (out-of-bounds) or -1 if the issue was in
// the final target check.
static bool validateSolution(const string& S, int* fail_idx = nullptr,
                              string* fail_reason = nullptr){
    vector<short> b = g_init_board;
    int br = g_init_br, bc = g_init_bc;
    for(int idx = 0; idx < (int)S.size(); ++idx){
        char c = S[idx];
        int d = (c=='U')?0:(c=='D')?1:(c=='L')?2:3;
        int nr = br + DR[d], nc = bc + DC[d];
        if(nr < 0 || nr >= N || nc < 0 || nc >= N){
            if(fail_idx) *fail_idx = idx;
            if(fail_reason) *fail_reason = "out-of-bounds at move " + to_string(idx);
            return false;
        }
        swap(b[br*N+bc], b[nr*N+nc]);
        br = nr; bc = nc;
    }
    for(int r = 0; r < M; ++r){
        for(int c = 0; c < M; ++c){
            int id = b[(r+1)*N + (c+1)];
            int color = (id == 0) ? -1 : g_id_to_color[id];
            if(color != g_target_inner[r][c]){
                if(fail_idx) *fail_idx = -1;
                if(fail_reason) *fail_reason = "inner cell (" + to_string(r) +
                    "," + to_string(c) + ") is " + to_string(color) +
                    " expected " + to_string(g_target_inner[r][c]);
                return false;
            }
        }
    }
    return true;
}

// ============================================================
// SAVE (only saves VALIDATED solutions)
// ============================================================
static bool saveProgressSafe(const string& S){
    // Validate
    int fi; string fr;
    if(!validateSolution(S, &fi, &fr)){
        cerr << "\n[FATAL] about-to-save solution is INVALID: " << fr << "\n";
        return false;
    }
    int len = (int)S.size();
    if(len == g_best_len) return true;
    g_best_len = len;

    ofstream f("best_vacuu13.txt");
    if(!f){ cerr << "[WARN] cannot write best_vacuum.txt\n"; return true; }
    f << S << "S\n";
    f << "// length=" << len << "  pass=" << g_save_pass
      << "  K=" << g_save_win << "  VALIDATED\n";

    cerr << "  [SAVED+VALIDATED] best_vacuum13.txt (pass=" << g_save_pass
         << " K=" << g_save_win << " len=" << len << ")\n";
    return true;
}

// ============================================================
// HEURISTIC (admissible, requires blank at target too)
// ============================================================
inline int calc_h(const short* b, int br, int bc){
    int h = 0;
    for(int i = 0; i < N2; ++i){
        int id = b[i];
        if(id == 0) continue;
        h += abs(i/N - target_r[id]) + abs(i%N - target_c[id]);
    }
    for(int r = 0; r < N; ++r){
        for(int c1 = 0; c1 < N-1; ++c1){
            int id1 = b[r*N+c1];
            if(id1 == 0 || target_r[id1] != r) continue;
            for(int c2 = c1+1; c2 < N; ++c2){
                int id2 = b[r*N+c2];
                if(id2 == 0 || target_r[id2] != r) continue;
                if(target_c[id1] > target_c[id2]) h += 2;
            }
        }
    }
    for(int c = 0; c < N; ++c){
        for(int r1 = 0; r1 < N-1; ++r1){
            int id1 = b[r1*N+c];
            if(id1 == 0 || target_c[id1] != c) continue;
            for(int r2 = r1+1; r2 < N; ++r2){
                int id2 = b[r2*N+c];
                if(id2 == 0 || target_c[id2] != c) continue;
                if(target_r[id1] > target_r[id2]) h += 2;
            }
        }
    }
    int blank_dist = abs(br - target_blank_r) + abs(bc - target_blank_c);
    return max(h, blank_dist);
}

static bool ida_dfs(short* b, int br, int bc, int g, int bound, int last_d, string& path){
    opt_nodes++;
    if(opt_nodes > ida_node_cap){ ida_timeout = true; return false; }
    int h = calc_h(b, br, bc);
    if(g + h > bound) return false;
    if(h == 0 && br == target_blank_r && bc == target_blank_c) return true;

    for(int d = 0; d < 4; ++d){
        if(last_d != -1 && d == (last_d ^ 1)) continue;
        int nr = br + DR[d], nc = bc + DC[d];
        if(nr < 0 || nr >= N || nc < 0 || nc >= N) continue;

        swap(b[br*N+bc], b[nr*N+nc]);
        path.push_back(CH[d]);
        if(ida_dfs(b, nr, nc, g+1, bound, d, path)) return true;
        path.pop_back();
        swap(b[br*N+bc], b[nr*N+nc]);
    }
    return false;
}

static void rebuildHistoryFrom(const string& S, int start, int end,
                                const short* b_start, int br_start, int bc_start){
    // Use a small temp copy since b_start might alias g_hist[start*N2]
    vector<short> tmp(N2);
    memcpy(tmp.data(), b_start, N2 * sizeof(short));
    memcpy(&g_hist[(long long)start * N2], tmp.data(), N2 * sizeof(short));
    g_br[start] = br_start;
    g_bc[start] = bc_start;

    for(int i = start; i < end; ++i){
        short* cur = &g_hist[(long long)i    * N2];
        short* nxt = &g_hist[(long long)(i+1) * N2];
        memcpy(nxt, cur, N2 * sizeof(short));
        int br = g_br[i], bc = g_bc[i];
        int d = (S[i]=='U')?0 : (S[i]=='D')?1 : (S[i]=='L')?2 : 3;
        int nr = br + DR[d], nc = bc + DC[d];
        swap(nxt[br*N+bc], nxt[nr*N+nc]);
        g_br[i+1] = nr;
        g_bc[i+1] = nc;
    }
}

static void printProgress(int pass, int K, int cur, int total, clock_t start, int len){
    if(total <= 0) return;
    double pct = (double)cur / total;
    double el = (double)(clock() - start) / CLOCKS_PER_SEC;
    double eta = (cur > 0) ? (el / cur) * (total - cur) : 0.0;
    cerr << "\r[Pass " << pass << " K=" << K << "] "
         << cur << "/" << total
         << " (" << (int)(pct*100) << "%) Len:" << len
         << " ETA:" << fixed << setprecision(0) << eta << "s    ";
    cerr.flush();
}

// ============================================================
// MAIN
// ============================================================
int main(){
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);

    cerr << "STANDALONE VACUUM (paranoid - full revalidation)\n\n";

    if(!(cin >> N)) return 0;
    M = N - 2;
    N2 = N * N;

    if(N < 5 || N > 67 || (N % 2) == 0){
        cerr << "Invalid N\n"; return 1;
    }

    g_init_board.assign(N2, 0);
    g_id_to_color.assign(N2 + 10, 0);
    int id_counter = 1;
    int blank_idx = -1;

    for(int i = 0; i < N2; ++i){
        int val; cin >> val;
        if(val == -1){
            g_init_board[i] = 0;
            blank_idx = i;
        } else {
            g_init_board[i] = (short)id_counter;
            g_id_to_color[id_counter] = (short)val;
            id_counter++;
        }
    }
    g_init_br = blank_idx / N;
    g_init_bc = blank_idx % N;

    g_target_inner.assign(M, vector<int>(M));
    for(int r = 0; r < M; ++r)
        for(int c = 0; c < M; ++c)
            cin >> g_target_inner[r][c];

    string S = "LDDLDRDLLURDRULDLULDRULLDRRURULLDRULLDRUUUUULDRDLULDDRURRULLDRUUUUURDLULLDRRDDLUUULURURDLURRRDDDDLDLURURULDLURULDRRDLLURDLDDRRRDDDDDLURULDLURULDLURULDDRDLDRURDDLLURRDRUUURDLULURRDLLULDRURDLDRDLULDDRDLLURURULURULDRUULUURDDLURRULLDRUULDRRRRRDDLURULDLURULDLURULDLURULLDRRRULDLURDDDRULDRDLLURRRURDLULDRDLULDRDLLURDDLURDLDDDRUULDRURDDLLURRDDLLURRRUULDRDDDRULLDRUULULDRDDLURDLLURUUUURDDLURDDLURRUURULLDRULLDRRRRUUUUURDLULDRDLULDRDLULDRRULDDLULDRUULDRUUULDDRUUULDDDRRUURDLLURULLDDDRRDLUURDDRDLLDRDLUUUUURRDLDDDLURRDDDLURDDDLDRRULLLURDDLURRDLURULULURDRRRRULLDRULLDRULLDRRRRUUURDLULDRULLDRULLDRULLDRULUUURUULDRDRDLLUURURDDDRDLLULDRUULDRRRULLUURRDLDDDLDLUURURDLDDRDDRDDDRULDLURULLUURURULUUULDRUUULLDRDRRDDLLDDRULDDDRRDLDLUURUURDDLULDDRUURDDDLURDDLLURRRDRULLDRULLDRDLLURDRUULUURDDRUULDRUULLDRURULLDRULUURDDLURRULLDRULUURDDLUURDLURRRDDDLURDDDDDLURULDLUURDLUURDLUURULDRDDRULLURUULDDRDDRDLLURDDDLDRDLUURDLUURDLURRDDDDLURDLLUUURDDLUURDLURUULDDDRDRDLURULUUUURUUUULDDRULDDRULDDRULDRDDLUURDDDLUUUUUUUUULLLLLLLLLLLDDDDDDDDDDDDRRRRRRRRRRRRUUUUULUUUUUUULLLLLLLLLLLDDDDDDDDDDDDRRRRRRRRRRRRUUUUULUUUUUUULLLLLLLLLLLDDDDDDDDDDDDRRRRRRRRRRRRUUUUULUUUUUUULLLLLLLLLLLDDDDDDDDDDDDRRRRRRRRRRRRUUUUULUUUUUUULLLLLLLLLLLDDDDDDDDDDDDRRRRRRRRRRRRUUUUULUUUUUUULLLLLLLLLLLDDDDDDDDDDDDRRRRRRRRRRRRUUUUULUUUUUUULLLLLLLLLLLDDDDDDDDDDDDRRRRRRRRRRRRUUUUULUUUUUUULDRURDDLULULLLLLLLLLLDDDDDDDDDDDDRRRRRRRRRRRRUUUUULUUUUUURDDDLUUURULDRDDDDDLUUUUURDDDDDLUURDDDLUUUUUURS";
    

    if(S.empty()){ cerr << "No solution\n"; return 1; }
    if(S.back() == 'S') S.pop_back();

    auto cleanInversePairs = [](string& s){
        bool changed = true;
        while(changed){
            changed = false;
            string tmp; tmp.reserve(s.size());
            for(char c : s){
                if(!tmp.empty()){
                    char l = tmp.back();
                    if((l=='U'&&c=='D')||(l=='D'&&c=='U')||
                       (l=='L'&&c=='R')||(l=='R'&&c=='L')){
                        tmp.pop_back(); changed = true; continue;
                    }
                }
                tmp.push_back(c);
            }
            s = std::move(tmp);
        }
    };
    cleanInversePairs(S);

    cerr << "Validating input (len=" << S.size() << ")... ";
    string fr;
    if(!validateSolution(S, nullptr, &fr)){
        cerr << "INVALID: " << fr << "\n"; return 1;
    }
    cerr << "OK\n";

    long long slots_needed = (long long)(S.size() + 1) * N2;
    cerr << "Allocating " << (slots_needed * sizeof(short) / (1024*1024)) << " MB of history\n";
    g_hist.assign(slots_needed, 0);
    g_br.assign(S.size() + 1, 0);
    g_bc.assign(S.size() + 1, 0);

    rebuildHistoryFrom(S, 0, (int)S.size(), g_init_board.data(), g_init_br, g_init_bc);

    g_save_pass = 0; g_save_win = 0;
    saveProgressSafe(S);

    struct Tier { int K; long long node_cap; };
    vector<Tier> tiers = {
        {200,  500000}
    };

    bool globally_improved = true;
    int pass = 1;

    while(globally_improved && pass <= 20){
        globally_improved = false;
        g_save_pass = pass;
        cerr << "\n=== PASS " << pass << " ===\n";

        for(auto& tier : tiers){
            int K = tier.K;
            ida_node_cap = tier.node_cap;
            if(K >= (int)S.size()) continue;
            g_save_win = K;

            int improvements = 0;
            long long saved_total = 0;
            int sz = (int)S.size();
            int total_i = sz - K;
            clock_t t_start = clock();

            int i = 0;
            while(i <= total_i && i >= 0){
                if((i & 255) == 0) printProgress(pass, K, i, total_i, t_start, sz);

                short* st_start  = &g_hist[(long long)i * N2];
                short* st_target = &g_hist[(long long)(i+K) * N2];

                for(int idx = 0; idx < N2; ++idx){ target_r[idx] = -1; target_c[idx] = -1; }
                for(int idx = 0; idx < N2; ++idx){
                    int id = st_target[idx];
                    if(id != 0){ target_r[id] = idx/N; target_c[id] = idx%N; }
                }
                target_blank_r = g_br[i + K];
                target_blank_c = g_bc[i + K];

                // No-op detection
                bool is_noop = (g_br[i] == target_blank_r && g_bc[i] == target_blank_c);
                if(is_noop){
                    for(int idx = 0; idx < N2 && is_noop; ++idx){
                        if(st_start[idx] != st_target[idx]) is_noop = false;
                    }
                }

                string proposed_shortcut;
                bool have_candidate = false;

                if(is_noop){
                    proposed_shortcut = "";
                    have_candidate = true;
                } else {
                    int h_init = calc_h(st_start, g_br[i], g_bc[i]);
                    if(h_init >= K){ i++; continue; }

                    static short board_copy[N2_MAX];
                    bool found = false;
                    for(int bound = h_init; bound < K; ++bound){
                        memcpy(board_copy, st_start, N2 * sizeof(short));
                        opt_nodes = 0; ida_timeout = false;
                        string path;
                        if(ida_dfs(board_copy, g_br[i], g_bc[i], 0, bound, -1, path)){
                            proposed_shortcut = path;
                            found = true;
                            break;
                        }
                        if(ida_timeout) break;
                    }
                    if(found && (int)proposed_shortcut.size() < K){
                        have_candidate = true;
                    }
                }

                if(!have_candidate){ i++; continue; }

                // Verify the proposed shortcut locally
                vector<short> verify_board(N2);
                memcpy(verify_board.data(), st_start, N2 * sizeof(short));
                int vb_r = g_br[i], vb_c = g_bc[i];
                bool verify_ok = true;
                for(char c : proposed_shortcut){
                    int d = (c=='U')?0:(c=='D')?1:(c=='L')?2:3;
                    int nr = vb_r + DR[d], nc = vb_c + DC[d];
                    if(nr<0||nr>=N||nc<0||nc>=N){ verify_ok = false; break; }
                    swap(verify_board[vb_r*N+vb_c], verify_board[nr*N+nc]);
                    vb_r = nr; vb_c = nc;
                }
                if(verify_ok){
                    if(vb_r != target_blank_r || vb_c != target_blank_c) verify_ok = false;
                }
                if(verify_ok){
                    for(int idx = 0; idx < N2; ++idx){
                        if(verify_board[idx] != st_target[idx]){ verify_ok = false; break; }
                    }
                }
                if(!verify_ok){
                    cerr << "\n[WARN] local verify failed at i=" << i
                         << " K=" << K << ", skipping\n";
                    i++; continue;
                }

                // Apply the change
                string S_backup = S;
                vector<int> br_backup = g_br;
                vector<int> bc_backup = g_bc;
                // Don't back up g_hist (too big); if rollback, rebuild from scratch

                S.replace(i, K, proposed_shortcut);
                int new_i_end = i + (int)proposed_shortcut.size();

                // Replay shortcut on a scratch board to get state at new_i_end
                vector<short> board_at_new_end(N2);
                memcpy(board_at_new_end.data(), st_start, N2 * sizeof(short));
                int br_cur = g_br[i], bc_cur = g_bc[i];
                for(char c : proposed_shortcut){
                    int d = (c=='U')?0:(c=='D')?1:(c=='L')?2:3;
                    int nr = br_cur + DR[d], nc = bc_cur + DC[d];
                    swap(board_at_new_end[br_cur*N+bc_cur], board_at_new_end[nr*N+nc]);
                    br_cur = nr; bc_cur = nc;
                }

                rebuildHistoryFrom(S, new_i_end, (int)S.size(),
                                    board_at_new_end.data(), br_cur, bc_cur);

                // FULL REVALIDATION
                int fi; string fr;
                if(!validateSolution(S, &fi, &fr)){
                    cerr << "\n[ROLLBACK] change at i=" << i << " K=" << K
                         << " produced invalid solution: " << fr << "\n";
                    // Roll back
                    S = S_backup;
                    g_br = br_backup;
                    g_bc = bc_backup;
                    // Rebuild entire history from scratch
                    rebuildHistoryFrom(S, 0, (int)S.size(),
                                        g_init_board.data(), g_init_br, g_init_bc);
                    i++;
                    continue;
                }

                int saved = K - (int)proposed_shortcut.size();
                if(proposed_shortcut.empty()) saved = K;  // no-op case
                sz = (int)S.size();
                total_i = sz - K;
                improvements++;
                saved_total += saved;
                if(!saveProgressSafe(S)){
                    cerr << "[FATAL] save validation failed\n";
                    return 1;
                }

                i = max(0, i - K/2);
            }

            cerr << "\r[Pass " << pass << " K=" << K << "] DONE impr="
                 << improvements << " saved=" << saved_total
                 << " len=" << sz << "        \n";
            if(improvements > 0) globally_improved = true;
        }
        cerr << "Pass " << pass << " complete. Length=" << S.size() << "\n";
        pass++;
    }

    cleanInversePairs(S);
    if(!saveProgressSafe(S)){
        cerr << "[FATAL] final save invalid\n"; return 1;
    }

    cerr << "\n======================================\n";
    cerr << " DONE. Final length: " << S.size() << " moves (VALIDATED)\n";
    cerr << " Output: best_vacuum.txt\n";
    cerr << "======================================\n";
    return 0;
}