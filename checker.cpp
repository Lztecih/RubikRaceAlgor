// ============================================================
// RUBIK'S RACE VALIDATOR
// ============================================================
// Validates a solution string for the Rubik's Race puzzle.
//
// Input format (via stdin):
//   Line 1:     N (odd, 5..67)
//   Next N lines:     board (N numbers each, -1 = blank)
//   Next N-2 lines:   target ((N-2) numbers each)
//   Last:             solution string (ends with 'S')
//
// Output:
//   - Move count (excluding final S)
//   - VALID or INVALID (with specific reason)
//   - Final board state if valid
//
// Usage:
//   g++ -O2 -std=c++17 validator.cpp -o validator
//   (cat puzzle.txt; cat solution.txt) | ./validator
// ============================================================

#include <iostream>
#include <vector>
#include <string>
#include <sstream>

using namespace std;

int main(){
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);

    int N;
    if(!(cin >> N)){
        cerr << "ERROR: could not read N\n";
        return 1;
    }

    if(N < 5 || N > 67 || (N % 2) == 0){
        cerr << "ERROR: N must be odd and in [5, 67], got " << N << "\n";
        return 1;
    }

    int M = N - 2;

    // Read NxN board
    vector<vector<int>> board(N, vector<int>(N, 0));
    int br = -1, bc = -1;   // blank row, blank col
    int blank_count = 0;

    for(int r = 0; r < N; ++r){
        for(int c = 0; c < N; ++c){
            if(!(cin >> board[r][c])){
                cerr << "ERROR: could not read board cell (" << r << "," << c << ")\n";
                return 1;
            }
            if(board[r][c] == -1){
                br = r; bc = c;
                blank_count++;
            }
        }
    }

    if(blank_count != 1){
        cerr << "ERROR: board must have exactly one blank (-1), found " << blank_count << "\n";
        return 1;
    }

    // Read (N-2)x(N-2) target
    vector<vector<int>> target(M, vector<int>(M, 0));
    for(int r = 0; r < M; ++r){
        for(int c = 0; c < M; ++c){
            if(!(cin >> target[r][c])){
                cerr << "ERROR: could not read target cell (" << r << "," << c << ")\n";
                return 1;
            }
        }
    }

    // Read solution string
    string solution;
    if(!(cin >> solution)){
        cerr << "ERROR: could not read solution string\n";
        return 1;
    }

    cerr << "==============================================\n";
    cerr << " RUBIK'S RACE VALIDATOR\n";
    cerr << "==============================================\n";
    cerr << "N = " << N << " (board " << N << "x" << N << ", target " << M << "x" << M << ")\n";
    cerr << "Solution string length = " << solution.size() << " characters\n";

    // Check solution ends with 'S'
    if(solution.empty() || solution.back() != 'S'){
        cerr << "\nINVALID: solution must end with 'S' (got '"
             << (solution.empty() ? ' ' : solution.back()) << "')\n";
        return 1;
    }

    // Move count is length minus the trailing S
    int move_count = (int)solution.size() - 1;
    cerr << "Move count (excluding S) = " << move_count << "\n";

    // Validate each character is U/D/L/R
    for(int i = 0; i < (int)solution.size() - 1; ++i){
        char c = solution[i];
        if(c != 'U' && c != 'D' && c != 'L' && c != 'R'){
            cerr << "\nINVALID: character '" << c << "' at position " << i
                 << " is not U/D/L/R/S\n";
            return 1;
        }
    }

    cerr << "\nSimulating moves...\n";

    // Direction tables:
    // U = tile below moves up, so blank moves DOWN  (br + 1)
    // D = tile above moves down, so blank moves UP  (br - 1)
    // L = tile right moves left, so blank moves RIGHT (bc + 1)
    // R = tile left moves right, so blank moves LEFT  (bc - 1)

    for(int i = 0; i < (int)solution.size() - 1; ++i){
        char c = solution[i];
        int nbr = br, nbc = bc;
        if     (c == 'U') nbr = br + 1;   // blank goes down
        else if(c == 'D') nbr = br - 1;   // blank goes up
        else if(c == 'L') nbc = bc + 1;   // blank goes right
        else if(c == 'R') nbc = bc - 1;   // blank goes left

        // Bounds check
        if(nbr < 0 || nbr >= N || nbc < 0 || nbc >= N){
            cerr << "\nINVALID: move " << (i + 1) << " ('" << c
                 << "') would move blank out of bounds\n"
                 << "  blank was at (" << br << "," << bc << ")\n"
                 << "  would move to (" << nbr << "," << nbc << ")\n";
            return 1;
        }

        // Execute swap
        board[br][bc] = board[nbr][nbc];
        board[nbr][nbc] = -1;
        br = nbr;
        bc = nbc;
    }

    cerr << "All " << move_count << " moves executed successfully.\n\n";

    // Verify inner (N-2)x(N-2) region matches target
    // Inner region is rows [1..N-2] and cols [1..N-2]
    bool match = true;
    int first_bad_r = -1, first_bad_c = -1;
    int bad_got = 0, bad_want = 0;

    for(int r = 0; r < M; ++r){
        for(int c = 0; c < M; ++c){
            int got  = board[r + 1][c + 1];
            int want = target[r][c];
            if(got != want){
                if(match){
                    first_bad_r = r;
                    first_bad_c = c;
                    bad_got = got;
                    bad_want = want;
                }
                match = false;
            }
        }
    }

    if(!match){
        cerr << "INVALID: inner " << M << "x" << M << " region does not match target\n"
             << "  First mismatch at target(" << first_bad_r << "," << first_bad_c << ")\n"
             << "    got  = " << bad_got << "\n"
             << "    want = " << bad_want << "\n\n";

        cerr << "Final board state:\n";
        for(int r = 0; r < N; ++r){
            for(int c = 0; c < N; ++c){
                cerr << (board[r][c] == -1 ? "  _" : "") ;
                if(board[r][c] != -1)
                    cerr << (board[r][c] < 10 ? "  " : " ") << board[r][c];
            }
            cerr << "\n";
        }
        cerr << "\nExpected inner region:\n";
        for(int r = 0; r < M; ++r){
            for(int c = 0; c < M; ++c){
                cerr << (target[r][c] < 10 ? "  " : " ") << target[r][c];
            }
            cerr << "\n";
        }
        return 1;
    }

    // SUCCESS
    cerr << "==============================================\n";
    cerr << " VALID  (move count = " << move_count << ")\n";
    cerr << "==============================================\n";
    cerr << "Final board:\n";
    for(int r = 0; r < N; ++r){
        for(int c = 0; c < N; ++c){
            if(board[r][c] == -1)      cerr << "  _";
            else if(board[r][c] < 10)  cerr << "  " << board[r][c];
            else                        cerr << " "  << board[r][c];
        }
        cerr << "\n";
    }

    // Print the canonical summary to stdout (machine-readable)
    cout << "VALID " << move_count << "\n";

    return 0;
}