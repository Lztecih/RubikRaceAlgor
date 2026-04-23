#include <iostream>
#include <string>
#include <vector>
#include <queue>
#include <set>
#include <cmath>
#include <algorithm>
using namespace std;

// track current state
struct State {
    string board;
    int empty_idx;
    string path;
    int cost; // path length + Heuristic score

    // Constructor
    State(string b, int e, string p, int c) : board(b), empty_idx(e), path(p), cost(c) {}

    // Priority queue needs to know how to sort (lowest cost first)
    bool operator>(const State& other) const {
        return cost > other.cost;
    }
};

// Target positions separated into two basic arrays for older C++ support
int target_indices[] = {6, 7, 8, 11, 12, 13, 16, 17, 18};
char target_chars[] = {'6', '5', '4', '3', '2', '1', '1', '3', '6'};

// Manhattan Distance
int get_heuristic(const string& b) {
    int h = 0;
    for (int i = 0; i < 9; ++i) {
        int target_idx = target_indices[i];
        char req_char = target_chars[i];
        
        if (b[target_idx] == req_char) continue; // Already in place
        
        int tr = target_idx / 5;
        int tc = target_idx % 5;
        
        int min_dist = 100;
        // Find the closest matching character on the board
        for (int j = 0; j < 25; ++j) {
            if (b[j] == req_char) {
                int r = j / 5;
                int c = j % 5;
                int dist = abs(r - tr) + abs(c - tc);
                if (dist < min_dist) min_dist = dist;
            }
        }
        h += min_dist; // Add distance to the total score
    }
    return h;
}

bool is_solved(const string& b) {
    for (int i = 0; i < 9; ++i) {
        if (b[target_indices[i]] != target_chars[i]) return false;
    }
    return true;
}

int main() {
    string start_board = "2135631462255603142134456";
    int start_empty_idx = 14;

    // Added a space between > > for older C++ compatibility
    vector<pair<int, char> > moves[25];
    for (int r = 0; r < 5; ++r) {
        for (int c = 0; c < 5; ++c) {
            int i = r * 5 + c;
            // Using make_pair instead of {} initializer
            if (r > 0) moves[i].push_back(make_pair(i - 5, 'D'));
            if (r < 4) moves[i].push_back(make_pair(i + 5, 'U'));
            if (c > 0) moves[i].push_back(make_pair(i - 1, 'R'));
            if (c < 4) moves[i].push_back(make_pair(i + 1, 'L'));
        }
    }

    // Space added between > > here as well
    priority_queue<State, vector<State>, greater<State> > pq;
    set<string> visited; // Using standard set instead of unordered_set

    int initial_h = get_heuristic(start_board);
    pq.push(State(start_board, start_empty_idx, "", initial_h));
    visited.insert(start_board);

    cout << "Running A* Smart Search... please wait." << endl;

    while (!pq.empty()) {
        State curr = pq.top();
        pq.pop();

        if (curr.path.length() > 30) continue; // Skip paths over 30

        if (is_solved(curr.board)) {
            cout << "\nSolved in " << curr.path.length() << " moves!" << endl;
            cout << "Sequence: " << curr.path << endl;
            return 0;
        }

        // Using a standard for-loop instead of the range-based 'auto' loop
        for (size_t m = 0; m < moves[curr.empty_idx].size(); ++m) {
            int next_idx = moves[curr.empty_idx][m].first;
            char dir = moves[curr.empty_idx][m].second;

            string new_board = curr.board;
            swap(new_board[curr.empty_idx], new_board[next_idx]);

            if (visited.find(new_board) == visited.end()) {
                visited.insert(new_board);
                
                int new_h = get_heuristic(new_board);
                int new_cost = curr.path.length() + 1 + new_h;
                
                pq.push(State(new_board, next_idx, curr.path + dir, new_cost));
            }
        }
    }

    cout << "No solution exists for this board state within 30 moves." << endl;
    return 0;
}