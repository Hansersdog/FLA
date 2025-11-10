#include <bits/stdc++.h>
using namespace std;

// 简单安全的 trim
static inline string trim(const string &s) {
    size_t a = 0, b = s.size();
    while (a < b && isspace((unsigned char)s[a])) ++a;
    while (b > a && isspace((unsigned char)s[b-1])) --b;
    return s.substr(a, b-a);
}

int main(int argc, char** argv) {
    if (argc != 3) return 1;
    string inpath = argv[1];
    string outpath = argv[2];

    ifstream fin(inpath);
    if (!fin.is_open()) return 2;

    vector<string> state_names;
    vector<string> symbols;
    string q0_name;
    unordered_set<string> final_set;
    struct Trans { string from; string sym; string to; };
    vector<Trans> trans_raw;

    string line;
    while (std::getline(fin, line)) {
        string s = trim(line);
        if (s.empty()) continue;
        if (s[0] == ';') continue;
        // handle header lines
        if (s.rfind("#Q", 0) == 0) {
            auto p = s.find('{');
            auto q = s.find('}');
            if (p!=string::npos && q!=string::npos && q>p) {
                string inside = s.substr(p+1, q-p-1);
                string cur;
                for (char c: inside) {
                    if (c==',') {
                        string t = trim(cur); if (!t.empty()) state_names.push_back(t);
                        cur.clear();
                    } else cur.push_back(c);
                }
                string t = trim(cur); if (!t.empty()) state_names.push_back(t);
            }
            continue;
        }
        if (s.rfind("#S", 0) == 0) {
            auto p = s.find('{');
            auto q = s.find('}');
            if (p!=string::npos && q!=string::npos && q>p) {
                string inside = s.substr(p+1, q-p-1);
                string cur;
                for (char c: inside) {
                    if (c==',') {
                        string t = trim(cur); if (!t.empty()) symbols.push_back(t);
                        cur.clear();
                    } else cur.push_back(c);
                }
                string t = trim(cur); if (!t.empty()) symbols.push_back(t);
            }
            continue;
        }
        if (s.rfind("#q0", 0) == 0) {
            auto eq = s.find('=');
            if (eq!=string::npos) {
                string right = trim(s.substr(eq+1));
                q0_name = right;
            }
            continue;
        }
        if (s.rfind("#F", 0) == 0) {
            auto p = s.find('{');
            auto q = s.find('}');
            if (p!=string::npos && q!=string::npos && q>p) {
                string inside = s.substr(p+1, q-p-1);
                string cur;
                for (char c: inside) {
                    if (c==',') {
                        string t = trim(cur); if (!t.empty()) final_set.insert(t);
                        cur.clear();
                    } else cur.push_back(c);
                }
                string t = trim(cur); if (!t.empty()) final_set.insert(t);
            }
            continue;
        }
        // otherwise transition line: <old> <sym> <new>
        {
            // split by spaces (one space between parts per spec, but be tolerant)
            stringstream ss(s);
            string a,b,c;
            if (ss >> a >> b >> c) {
                trans_raw.push_back({a,b,c});
            }
        }
    }
    fin.close();

    // build maps for states
    unordered_map<string,int> idx;
    for (size_t i=0;i<state_names.size();++i) idx[state_names[i]] = (int)i;
    // allow states appearing only in transitions
    for (auto &t: trans_raw) {
        if (!idx.count(t.from)) {
            idx[t.from] = (int)state_names.size();
            state_names.push_back(t.from);
        }
        if (!idx.count(t.to)) {
            idx[t.to] = (int)state_names.size();
            state_names.push_back(t.to);
        }
    }

    int n = (int)state_names.size();
    int m = (int)symbols.size();
    // map symbol to index
    unordered_map<string,int> symidx;
    for (int i=0;i<m;++i) symidx[symbols[i]] = i;

    // transitions table, initialize with -1 (missing)
    vector<vector<int>> trans(n, vector<int>(m, -1));
    for (auto &t: trans_raw) {
        auto it = symidx.find(t.sym);
        if (it == symidx.end()) continue; // ignore unknown symbol (shouldn't happen per spec)
        int si = idx[t.from];
        int sj = idx[t.to];
        trans[si][it->second] = sj;
    }

    // If transitions missing, create a sink state
    bool need_sink = false;
    for (int i=0;i<n;++i) for (int j=0;j<m;++j) if (trans[i][j]==-1) need_sink = true;
    if (need_sink) {
        int sink_id = n;
        state_names.push_back("sink");
        idx["sink"] = sink_id;
        trans.emplace_back(m, sink_id); // sink transitions to itself
        ++n;
        for (int i=0;i<n-1;++i) trans[i].resize(m, sink_id);
    }

    // remove unreachable states: BFS from q0
    if (!idx.count(q0_name)) return 3;
    int q0 = idx[q0_name];
    vector<char> vis(n,0);
    queue<int> q;
    vis[q0]=1; q.push(q0);
    while(!q.empty()) {
        int u=q.front(); q.pop();
        for (int a=0;a<m;++a) {
            int v = trans[u][a];
            if (v>=0 && !vis[v]) { vis[v]=1; q.push(v); }
        }
    }
    vector<int> remap(n, -1);
    vector<string> r_state_names;
    for (int i=0;i<n;++i) if (vis[i]) {
        remap[i] = (int)r_state_names.size();
        r_state_names.push_back(state_names[i]);
    }
    if (r_state_names.empty()) return 4;
    int rn = (int)r_state_names.size();
    vector<vector<int>> rtrans(rn, vector<int>(m));
    vector<char> rfinal(rn,0);
    for (int i=0;i<n;++i) if (vis[i]) {
        int ni = remap[i];
        for (int a=0;a<m;++a) rtrans[ni][a] = remap[trans[i][a]];
        if (final_set.count(state_names[i])) rfinal[ni]=1;
    }
    int rq0 = remap[q0];

    // minimization by iterative signature refinement
    vector<int> cls(rn, 0);
    for (int i=0;i<rn;++i) cls[i] = rfinal[i] ? 1 : 0;
    bool changed = true;
    vector<int> newcls(rn);
    unordered_map<string,int> sigmap;
    while (changed) {
        changed = false;
        sigmap.clear();
        int nextid = 0;
        for (int i=0;i<rn;++i) {
            // build signature: current cls + for each symbol the class of target
            string sig = to_string(cls[i]);
            sig.push_back('|');
            for (int a=0;a<m;++a) {
                sig += to_string(cls[rtrans[i][a]]);
                sig.push_back(',');
            }
            auto it = sigmap.find(sig);
            if (it==sigmap.end()) {
                sigmap[sig] = nextid;
                newcls[i] = nextid;
                ++nextid;
            } else newcls[i] = it->second;
            if (newcls[i] != cls[i]) changed = true;
        }
        cls.swap(newcls);
    }

    // build minimized states: group id -> list of original states
    int groups = 0;
    for (int v: cls) if (v+1 > groups) groups = v+1;
    vector<string> mstate(groups);
    // name states as m0,m1,... but try to keep original q0 name for initial state's group
    for (int g=0;g<groups;++g) mstate[g] = "m" + to_string(g);
    int mq0g = cls[rq0];
    // give mq0g the original q0 name to improve readability (optional, meets spec)
    mstate[mq0g] = r_state_names[rq0];

    vector<char> mgfinal(groups,0);
    for (int i=0;i<rn;++i) {
        if (rfinal[i]) mgfinal[cls[i]] = 1;
    }
    vector<vector<int>> mtrans(groups, vector<int>(m, -1));
    for (int i=0;i<rn;++i) {
        int g = cls[i];
        for (int a=0;a<m;++a) {
            mtrans[g][a] = cls[rtrans[i][a]];
        }
    }

    // produce output
    ofstream fout(outpath);
    if (!fout.is_open()) return 5;

    // #Q
    fout << "#Q = {";
    for (int i=0;i<groups;++i) {
        if (i) fout << ",";
        fout << mstate[i];
    }
    fout << "}\n";
    // #S
    fout << "#S = {";
    for (int i=0;i<m;++i) {
        if (i) fout << ",";
        fout << symbols[i];
    }
    fout << "}\n";
    // #q0
    fout << "#q0 = " << mstate[mq0g] << "\n";
    // #F
    fout << "#F = {";
    bool first=true;
    for (int i=0;i<groups;++i) if (mgfinal[i]) {
        if (!first) fout << ",";
        fout << mstate[i];
        first=false;
    }
    fout << "}\n\n";
    // transitions
    for (int i=0;i<groups;++i) {
        for (int a=0;a<m;++a) {
            fout << mstate[i] << " " << symbols[a] << " " << mstate[mtrans[i][a]] << "\n";
        }
    }
    fout.close();
    return 0;
}