// ============================================================
// 0016 · AC 自动机 (Aho-Corasick)
// ------------------------------------------------------------
// 六个部分:
//   A. Kmp          逐模式 KMP 对照实现 (含比较次数计数器)
//   B. AhoAuto      完整 goto 转移表 (单步 O(1)), 文本扫描 + fail 树
//                   逆序传播: 模式出现次数 = fail 子树内访问数之和
//   C. AhoClimb     无转移表版本: miss 时沿 fail 上爬, 均摊 O(n),
//                   稀疏孩子表, 内存 O(模式总长) 而非 O(节点*sigma)
//   D. AhoOnlineBit fail 树 Euler 序 + 树状数组: 流式文本的在线查询
//                   "到目前为止模式 p 出现了多少次", 单次 O(log n)
//   E. 基准         一次 AC vs 逐个 KMP / goto vs climb / BIT 在线 vs 离线
//   F. G1-G6 对拍   随机多模式四方对拍 / 转移一致性 / fail 树恒等式 /
//                   边界专项 / 在线查询 / 复杂度计数断言
// 关键恒等式: 设扫描文本后状态 u 被访问 visits[u] 次, 则模式 p 的出现次数
//             = Σ visits[u], u 取遍 fail 树中 patNode(p) 的子树
//             (状态 u 是"最长模式后缀", p 是它的后缀 <=> patNode(p)
//              在 fail 树上是 u 的祖先或自身)
// 编译:   g++ -O2 -std=c++17 -Wall -Wextra 0016_ac_automaton.cpp -o 0016
// 注意:   本期源码未在本机编译(环境无 C++ 编译器), 算法逻辑已通过
//         Python 逐行镜像对拍验证, 详见 0016_ac_automaton.md
// ============================================================
#include <bits/stdc++.h>
using namespace std;
using ll = long long;

static int g_fail = 0;

#define CHECK(cond, ...)                          \
    do {                                          \
        if (!(cond)) {                            \
            printf("    [FAIL] " __VA_ARGS__);    \
            printf("\n");                         \
            ++g_fail;                             \
        }                                         \
    } while (0)

struct Timer {
    chrono::steady_clock::time_point a;
    void go() { a = chrono::steady_clock::now(); }
    double ms() const {
        return (double)chrono::duration_cast<chrono::microseconds>(
                   chrono::steady_clock::now() - a).count() / 1000.0;
    }
};

static string randStr(mt19937& rng, int n, int sigma) {
    string s(n, 'a');
    for (int i = 0; i < n; ++i) s[i] = (char)('a' + (int)(rng() % (unsigned)sigma));
    return s;
}

// ============================================================
// A. 逐模式 KMP (对照 oracle, 带比较计数器)
//    比较口径: 每做一次字符判定计 1 次 (与 0014 一致)
// ============================================================
struct Kmp {
    int m = 0;
    vector<int> pi;
    string pat;
    mutable ll cmp = 0;

    void build(const string& p) {
        pat = p;
        m = (int)p.size();
        pi.assign(m, 0);
        for (int i = 1; i < m; ++i) {
            int j = pi[i - 1];
            while (j > 0 && p[i] != p[j]) { ++cmp; j = pi[j - 1]; }
            if (p[i] == p[j]) { ++cmp; pi[i] = j + 1; }
            else { ++cmp; pi[i] = 0; }
        }
    }

    ll countIn(const string& t) const {
        if (m == 0) return 0;
        ll occ = 0;
        int j = 0;
        for (int i = 0; i < (int)t.size(); ++i) {
            while (j > 0 && t[i] != pat[j]) { ++cmp; j = pi[j - 1]; }
            if (t[i] == pat[j]) { ++cmp; ++j; }
            else { ++cmp; }
            if (j == m) { ++occ; j = pi[m - 1]; }
        }
        return occ;
    }
};

// 暴力计数 (小规模三方对拍用)
static ll g_bruteCmp = 0;
static ll bruteCount(const string& t, const string& p) {
    ll occ = 0;
    for (int i = 0; i + (int)p.size() <= (int)t.size(); ++i) {
        bool ok = true;
        for (int j = 0; j < (int)p.size(); ++j) {
            ++g_bruteCmp;
            if (t[i + j] != p[j]) { ok = false; break; }
        }
        if (ok) ++occ;
    }
    return occ;
}

// fail 树逆序传播 (A/C/D 共用逻辑): total[u] = visits[u] + Σ total[子树]
static void propagate(const vector<int>& order, const vector<int>& fail,
                      vector<ll>& total) {
    for (int i = (int)order.size() - 1; i >= 0; --i) {
        int v = order[i];
        total[fail[v]] += total[v];
    }
}

// ============================================================
// B. AC 自动机 · 完整 goto 转移表版
//    go[u][c] = u 有字符 c 孩子 ? 孩子 : go[fail[u]][c]
//    扫描文本恰好 n 次转移, 单步 O(1); 代价是 O(节点*sigma) 内存
// ============================================================
struct AhoAuto {
    int sigma = 26;
    vector<array<int, 26>> go;
    vector<int> fail;
    vector<int> order;      // BFS 序 (不含根), fail 树逆序传播要用
    vector<int> patNode;    // 模式 id -> 终止节点
    vector<ll> visits, total;
    ll trans = 0;           // 扫描转移次数 (复杂度断言: == n)

    void build(const vector<string>& pats) {
        sigma = 26;
        go.assign(1, {});
        go[0].fill(-1);
        patNode.assign(pats.size(), 0);
        for (size_t i = 0; i < pats.size(); ++i) {
            int u = 0;
            for (char ch : pats[i]) {
                int c = ch - 'a';
                if (go[u][c] == -1) {
                    go[u][c] = (int)go.size();
                    go.push_back({});
                    go.back().fill(-1);
                }
                u = go[u][c];
            }
            patNode[i] = u;
        }
        int tot = (int)go.size();
        fail.assign(tot, 0);
        order.clear();
        order.reserve(tot);
        queue<int> q;
        for (int c = 0; c < sigma; ++c) {
            int v = go[0][c];
            if (v == -1) go[0][c] = 0;
            else { fail[v] = 0; q.push(v); }
        }
        while (!q.empty()) {
            int u = q.front(); q.pop();
            order.push_back(u);
            for (int c = 0; c < sigma; ++c) {
                int v = go[u][c];
                if (v == -1) go[u][c] = go[fail[u]][c];
                else { fail[v] = go[fail[u]][c]; q.push(v); }
            }
        }
    }

    vector<ll> countAll(const string& t) {
        int tot = (int)go.size();
        visits.assign(tot, 0);
        trans = 0;
        int u = 0;
        for (char ch : t) {
            u = go[u][ch - 'a'];
            ++trans;
            ++visits[u];
        }
        total = visits;
        propagate(order, fail, total);
        vector<ll> res(patNode.size());
        for (size_t i = 0; i < patNode.size(); ++i) res[i] = total[patNode[i]];
        return res;
    }

    void selfCheck() const {
        for (int u = 0; u < (int)go.size(); ++u) {
            for (int c = 0; c < sigma; ++c) {
                if (go[u][c] == -1) {
                    CHECK(false, "goto not complete: go[%d][%d]", u, c);
                    return;
                }
            }
        }
        // fail[v] 必须在 BFS 序中先于 v 出现 (深度严格递减)
        vector<int> pos(go.size(), -1);
        pos[0] = 0;
        for (int i = 0; i < (int)order.size(); ++i) pos[order[i]] = i + 1;
        for (int v : order)
            CHECK(pos[fail[v]] != -1 && pos[fail[v]] < pos[v],
                  "fail BFS order violated at node %d", v);
    }
};

// ============================================================
// C. AC 自动机 · 上爬版 (无转移表)
//    miss 时沿 fail 上爬直到找到转移或回到根, 均摊 O(n):
//    深度每步至多 +1, 上爬总次数 <= 文本长度
//    稀疏孩子表: 内存 O(模式总长), 与 goto 版 O(节点*sigma) 对比
// ============================================================
struct AhoClimb {
    vector<vector<pair<int, int>>> ch;   // ch[u] = [(c, child), ...] 无序小表
    vector<int> fail;
    vector<int> order;
    vector<int> patNode;
    vector<ll> visits, total;
    ll climbs = 0;   // 上爬总次数 (复杂度断言: <= n)

    int chOf(int u, int c) const {
        for (const auto& pr : ch[u])
            if (pr.first == c) return pr.second;
        return -1;
    }

    void build(const vector<string>& pats) {
        ch.assign(1, {});
        patNode.assign(pats.size(), 0);
        for (size_t i = 0; i < pats.size(); ++i) {
            int u = 0;
            for (char cch : pats[i]) {
                int c = cch - 'a';
                int v = chOf(u, c);
                if (v == -1) {
                    v = (int)ch.size();
                    ch.push_back({});
                    ch[u].push_back({c, v});
                }
                u = v;
            }
            patNode[i] = u;
        }
        int tot = (int)ch.size();
        fail.assign(tot, 0);
        order.clear();
        order.reserve(tot);
        queue<int> q;
        for (const auto& pr : ch[0]) { fail[pr.second] = 0; q.push(pr.second); }
        while (!q.empty()) {
            int u = q.front(); q.pop();
            order.push_back(u);
            for (const auto& pr : ch[u]) {
                int c = pr.first, v = pr.second;
                int w = fail[u];
                while (w != 0 && chOf(w, c) == -1) w = fail[w];
                int f = chOf(w, c);
                fail[v] = (f == -1 || f == v) ? 0 : f;
                q.push(v);
            }
        }
    }

    // 从状态 u 走字符 c: 上爬找转移, 都没有则停在根
    int stepFrom(int u, int c) {
        int v = chOf(u, c);
        while (v == -1 && u != 0) {
            u = fail[u];
            ++climbs;
            v = chOf(u, c);
        }
        return v == -1 ? 0 : v;
    }

    vector<ll> countAll(const string& t) {
        int tot = (int)ch.size();
        visits.assign(tot, 0);
        climbs = 0;
        int u = 0;
        for (char cch : t) {
            u = stepFrom(u, cch - 'a');
            ++visits[u];
        }
        total = visits;
        propagate(order, fail, total);
        vector<ll> res(patNode.size());
        for (size_t i = 0; i < patNode.size(); ++i) res[i] = total[patNode[i]];
        return res;
    }
};

// ============================================================
// D. fail 树 Euler 序 + 树状数组 (在线版本)
//    流式喂文本, 随时可查"到目前为止模式 p 出现了几次"
//    每次 feed 单字符 O(log n), 每次查询 O(log n)
//    查询 = fail 子树 [tin[t], tout[t]] 内的访问点数
// ============================================================
struct Fenwick {
    int n = 0;
    vector<ll> t;
    void init(int n_) { n = n_; t.assign(n + 1, 0); }
    void add(int i, ll d) {
        for (++i; i <= n; i += i & -i) t[i] += d;
    }
    ll pre(int i) const {
        ll s = 0;
        for (++i; i > 0; i -= i & -i) s += t[i];
        return s;
    }
    ll range(int l, int r) const { return l > r ? 0 : pre(r) - pre(l - 1); }
};

struct AhoOnlineBit {
    AhoAuto ac;                 // 复用 goto 转移表导航
    vector<int> tin, tout;      // fail 树先序区间
    Fenwick bit;
    int cur = 0;

    void build(const vector<string>& pats) {
        ac.build(pats);
        int tot = (int)ac.go.size();
        vector<vector<int>> kids(tot);
        for (int v = 1; v < tot; ++v) kids[ac.fail[v]].push_back(v);
        tin.assign(tot, 0);
        tout.assign(tot, 0);
        // 先序: 显式栈
        vector<int> stk;
        stk.push_back(0);
        int timer = 0;
        while (!stk.empty()) {
            int x = stk.back(); stk.pop_back();
            tin[x] = timer++;
            for (int w : kids[x]) stk.push_back(w);
        }
        // tout 自底向上传播: tout[f] = max(tout[f], tout[v])
        for (int x = 0; x < tot; ++x) tout[x] = tin[x];
        for (int i = (int)ac.order.size() - 1; i >= 0; --i) {
            int v = ac.order[i];
            tout[ac.fail[v]] = max(tout[ac.fail[v]], tout[v]);
        }
        bit.init(tot);
        cur = 0;
    }

    void feed(const string& s) {
        for (char c : s) {
            cur = ac.go[cur][c - 'a'];
            bit.add(tin[cur], 1);
        }
    }

    void reset() {
        bit.init(bit.n);
        cur = 0;
    }

    ll countPattern(int pid) const {
        int tnode = ac.patNode[pid];
        return bit.range(tin[tnode], tout[tnode]);
    }
};

// ============================================================
// F. 对拍组
// ============================================================

// G1 · 随机多模式四方对拍: AC(goto) / AC(climb) / 逐模式 KMP / 暴力
// 覆盖: 小字母表(易撞 fail 链)/ 重复模式 / 互相嵌套的模式 / 单字符模式
static void g1(int rounds) {
    printf("G1 随机多模式四方对拍 (%d 轮)\n", rounds);
    mt19937 rng(16001);
    ll totalOcc = 0;
    for (int r = 0; r < rounds; ++r) {
        int sigma = 2 + (int)(rng() % 3);           // 2/3/4, 刻意偏小
        int n = 1 + (int)(rng() % 150);
        string t = randStr(rng, n, sigma);
        int m = (int)(rng() % 9);                   // 0..8 个模式
        vector<string> pats;
        for (int i = 0; i < m; ++i) {
            if (i >= 2 && (rng() % 3) == 0) {
                pats.push_back(pats[(size_t)(rng() % (unsigned)i)]);  // 重复
            } else if (r % 2 == 0 && n >= 2) {
                // 偶数轮: 直接从文本采样子串, 保证非零命中
                int st = (int)(rng() % (unsigned)(n - 1));
                int en = min(n, st + 1 + (int)(rng() % 12));
                pats.push_back(t.substr((size_t)st, (size_t)(en - st)));
            } else {
                int L = 1 + (int)(rng() % 12);
                pats.push_back(randStr(rng, L, sigma));
            }
        }
        AhoAuto ac;
        ac.build(pats);
        AhoClimb cl;
        cl.build(pats);
        vector<Kmp> ks(pats.size());
        vector<ll> want(pats.size());
        for (size_t i = 0; i < pats.size(); ++i) {
            ks[i].build(pats[i]);
            want[i] = ks[i].countIn(t);
        }
        vector<ll> a = ac.countAll(t);
        vector<ll> b = cl.countAll(t);
        for (size_t i = 0; i < pats.size(); ++i) {
            ll c = bruteCount(t, pats[i]);
            CHECK(a[i] == want[i] && b[i] == want[i] && c == want[i],
                  "r=%d sigma=%d n=%d pat#%zu=%s got ac=%lld climb=%lld brute=%lld want=%lld",
                  r, sigma, n, i, pats[i].c_str(), a[i], b[i], c, want[i]);
            totalOcc += want[i];
        }
    }
    printf("    %d 轮累计出现次数 %lld\n", rounds, totalOcc);
}

// G2 · 转移一致性: go[u][c] 必须等于 climb 版从 u 走 c 的模拟结果
static void g2(int rounds) {
    printf("G2 goto 转移表 vs 上爬模拟一致性 (%d 组)\n", rounds);
    mt19937 rng(16002);
    for (int r = 0; r < rounds; ++r) {
        int sigma = 2 + (int)(rng() % 3);
        vector<string> pats;
        int m = 1 + (int)(rng() % 6);
        for (int i = 0; i < m; ++i) pats.push_back(randStr(rng, 1 + (int)(rng() % 8), sigma));
        AhoAuto ac;
        ac.build(pats);
        AhoClimb cl;
        cl.build(pats);
        if ((int)ac.go.size() > 400) continue;      // 控制穷举规模
        for (int u = 0; u < (int)ac.go.size(); ++u) {
            for (int c = 0; c < sigma; ++c) {
                int g = ac.go[u][c];
                cl.climbs = 0;
                int s = cl.stepFrom(u, c);
                CHECK(g == s, "r=%d sigma=%d node=%d c=%d goto=%d climb=%d",
                      r, sigma, u, c, g, s);
            }
        }
        // 随机文本上两个版本的状态序列必须逐位一致
        string t = randStr(rng, 1 + (int)(rng() % 200), sigma);
        vector<int> s1, s2;
        int u1 = 0, u2 = 0;
        for (char cch : t) {
            u1 = ac.go[u1][cch - 'a'];
            u2 = cl.stepFrom(u2, cch - 'a');
            s1.push_back(u1);
            s2.push_back(u2);
        }
        CHECK(s1 == s2, "r=%d state sequence mismatch (len %zu vs %zu)",
              r, s1.size(), s2.size());
    }
}

// G3 · fail 树恒等式: 传播得到的 total == 直接 DFS 子树求和
static void g3(int rounds) {
    printf("G3 fail 树恒等式: 传播 vs 直接子树求和 (%d 组)\n", rounds);
    mt19937 rng(16003);
    for (int r = 0; r < rounds; ++r) {
        int sigma = 2 + (int)(rng() % 25);
        vector<string> pats;
        int m = 1 + (int)(rng() % 15);
        for (int i = 0; i < m; ++i) pats.push_back(randStr(rng, 1 + (int)(rng() % 10), sigma));
        AhoAuto ac;
        ac.build(pats);
        string t = randStr(rng, 1 + (int)(rng() % 120), sigma);
        ac.countAll(t);
        int tot = (int)ac.go.size();
        // fail 树孩子表
        vector<vector<int>> kids(tot);
        for (int v = 1; v < tot; ++v) kids[ac.fail[v]].push_back(v);
        // 对每个节点直接求子树和 (迭代栈)
        for (int u = 0; u < tot; ++u) {
            ll sum = 0;
            vector<int> stk = {u};
            while (!stk.empty()) {
                int x = stk.back(); stk.pop_back();
                sum += ac.visits[x];
                for (int w : kids[x]) stk.push_back(w);
            }
            CHECK(sum == ac.total[u], "r=%d node=%d propagated=%lld direct=%lld",
                  r, u, ac.total[u], sum);
        }
    }
}

// G4 · 边界专项
static void g4() {
    printf("G4 边界专项\n");
    mt19937 rng(16004);
    {   // 空模式表
        AhoAuto ac;
        ac.build({});
        vector<ll> res = ac.countAll("abc");
        CHECK(res.empty(), "empty pattern set should return empty result");
    }
    {   // 模式比文本长
        AhoAuto ac;
        vector<string> pats = {"abcdef"};
        ac.build(pats);
        vector<ll> res = ac.countAll("abc");
        CHECK(res.size() == 1 && res[0] == 0, "pattern longer than text: got %lld", res[0]);
    }
    {   // 模式 == 文本
        AhoAuto ac;
        vector<string> pats = {"abc"};
        ac.build(pats);
        vector<ll> res = ac.countAll("abc");
        CHECK(res.size() == 1 && res[0] == 1, "pattern == text: got %lld", res[0]);
    }
    {   // 全 a 文本 + 嵌套模式: a^n 中 a^k 出现 n-k+1 次
        string t(50, 'a');
        AhoAuto ac;
        vector<string> pats = {"a", "aa", "aaaaa"};
        ac.build(pats);
        vector<ll> res = ac.countAll(t);
        CHECK(res[0] == 50 && res[1] == 49 && res[2] == 46,
              "nested a^k in a^50: got %lld %lld %lld, want 50 49 46",
              res[0], res[1], res[2]);
    }
    {   // 重复模式: 两份相同模式必须得到相同计数
        AhoAuto ac;
        vector<string> pats = {"ab", "ab", "b"};
        ac.build(pats);
        vector<ll> res = ac.countAll("ababab");
        CHECK(res[0] == 3 && res[1] == 3 && res[2] == 3,
              "duplicates in ababab: got %lld %lld %lld, want 3 3 3",
              res[0], res[1], res[2]);
    }
    {   // 单字符文本
        AhoAuto ac;
        vector<string> pats = {"a", "b"};
        ac.build(pats);
        vector<ll> res = ac.countAll("a");
        CHECK(res[0] == 1 && res[1] == 0, "single char text: got %lld %lld", res[0], res[1]);
    }
    {   // 互为后缀的模式 (ab / b / cab): 每次出现都要分别计数
        AhoAuto ac;
        vector<string> pats = {"cab", "ab", "b"};
        ac.build(pats);
        vector<ll> res = ac.countAll("xcabab");
        CHECK(res[0] == 1 && res[1] == 2 && res[2] == 2,
              "suffix family in xcabab: got %lld %lld %lld, want 1 2 2",
              res[0], res[1], res[2]);
    }
    (void)rng;
}

// G5 · 在线查询: 流式喂文本, 任意时刻查"到目前为止模式 p 的出现次数"
static void g5(int rounds) {
    printf("G5 在线 BIT 查询 (%d 组 x 30 检查点)\n", rounds);
    mt19937 rng(16005);
    for (int r = 0; r < rounds; ++r) {
        int sigma = 2 + (int)(rng() % 3);
        int n = 5 + (int)(rng() % 150);
        string t = randStr(rng, n, sigma);
        vector<string> pats;
        int m = 1 + (int)(rng() % 6);
        for (int i = 0; i < m; ++i) pats.push_back(randStr(rng, 1 + (int)(rng() % 10), sigma));
        AhoOnlineBit ob;
        ob.build(pats);
        vector<Kmp> ks(pats.size());
        for (size_t i = 0; i < pats.size(); ++i) ks[i].build(pats[i]);
        for (int cp = 0; cp < 30; ++cp) {
            int x = 1 + (int)(rng() % (unsigned)n);     // 前缀长度
            ob.reset();
            ob.feed(t.substr(0, (size_t)x));
            for (size_t i = 0; i < pats.size(); ++i) {
                ll got = ob.countPattern((int)i);
                ll want = ks[i].countIn(t.substr(0, (size_t)x));
                CHECK(got == want,
                      "r=%d sigma=%d prefix=%d pat#%zu=%s got=%lld want=%lld",
                      r, sigma, x, i, pats[i].c_str(), got, want);
            }
        }
    }
}

// G6 · 复杂度计数断言: goto 转移数恰为 n; climb 上爬数 <= n
static void g6() {
    printf("G6 复杂度计数 (n=30000, sigma=2, m=100)\n");
    mt19937 rng(16006);
    int n = 30000;
    string t = randStr(rng, n, 2);
    vector<string> pats;
    for (int i = 0; i < 100; ++i)
        pats.push_back(randStr(rng, 3 + (int)(rng() % 10), 2));
    AhoAuto ac;
    ac.build(pats);
    vector<ll> ra = ac.countAll(t);
    AhoClimb cl;
    cl.build(pats);
    vector<ll> rb = cl.countAll(t);
    CHECK(ra == rb, "goto vs climb counts differ on G6 data");
    CHECK(ac.trans == n, "goto transitions %lld != n %d", ac.trans, n);
    CHECK(cl.climbs <= n, "climb steps %lld exceed n %d", cl.climbs, n);
    ll kmpCmp = 0;
    for (int i = 0; i < (int)pats.size(); ++i) {
        Kmp k;
        k.build(pats[i]);
        k.countIn(t);
        kmpCmp += k.cmp;
    }
    printf("    goto 转移 %lld (== n), climb 上爬 %lld (<= n, %.2f/n)\n",
           ac.trans, cl.climbs, (double)cl.climbs / (double)n);
    printf("    逐模式 KMP 总比较 %lld (%.1f x n), AC 单趟 %lld 次转移\n",
           kmpCmp, (double)kmpCmp / (double)n, ac.trans);
    // 内存对比
    double memGo = (double)ac.go.size() * 26.0 * 4.0 / 1024.0;
    double memCl = 0;
    for (const auto& v : cl.ch) memCl += (double)(v.size() * 8 + 24);
    printf("    内存: goto 表 %.1f KB vs climb 稀疏表 %.1f KB (节点数 %d)\n",
           memGo, memCl / 1024.0, (int)ac.go.size());
}

// ============================================================
// E. 基准
// ============================================================
static void bench() {
    printf("E. 基准 (n=2e5, sigma=2, m=200 模式 len 8..12)\n");
    mt19937 rng(16016);
    int n = 200000;
    string t = randStr(rng, n, 2);
    vector<string> pats;
    for (int i = 0; i < 200; ++i)
        pats.push_back(randStr(rng, 8 + (int)(rng() % 5), 2));

    AhoAuto ac;
    ac.build(pats);
    Timer tm;
    tm.go();
    vector<ll> ra = ac.countAll(t);
    double tAuto = tm.ms();

    AhoClimb cl;
    cl.build(pats);
    tm.go();
    vector<ll> rb = cl.countAll(t);
    double tClimb = tm.ms();

    tm.go();
    ll sumKmp = 0;
    ll kmpCmp = 0;
    for (int i = 0; i < (int)pats.size(); ++i) {
        Kmp k;
        k.build(pats[i]);
        sumKmp += k.countIn(t);
        kmpCmp += k.cmp;
    }
    double tKmp = tm.ms();

    ll sumA = 0, sumB = 0;
    for (ll x : ra) sumA += x;
    for (ll x : rb) sumB += x;
    CHECK(sumA == sumKmp && sumB == sumKmp,
          "bench checksum mismatch: ac=%lld climb=%lld kmp=%lld", sumA, sumB, sumKmp);
    printf("    B1 单趟计数: goto %.1f ms | climb %.1f ms | 逐模式 KMP %.1f ms\n",
           tAuto, tClimb, tKmp);
    printf("       出现总次数 %lld, KMP 总比较 %lld, 加速比 %.1fx\n",
           sumA, kmpCmp, tKmp / (tAuto > 0 ? tAuto : 1e-9));

    // B2 在线 BIT: 全量 feed + 200 次查询 vs 离线 countAll
    AhoOnlineBit ob;
    ob.build(pats);
    tm.go();
    ob.feed(t);
    ll sumBit = 0;
    for (int i = 0; i < 200; ++i) sumBit += ob.countPattern(i);
    double tBit = tm.ms();
    ll sumOff = 0;
    for (ll x : ra) sumOff += x;
    // BIT 查询与离线结果一致 (计数总和口径)
    CHECK(sumBit == sumOff, "BIT query sum %lld != offline %lld", sumBit, sumOff);
    printf("    B2 在线 BIT: feed+200 查询 %.1f ms (离线 countAll %.1f ms, 答案一致)\n",
           tBit, tAuto);
}

int main() {
    printf("== 0016 AC 自动机 ==\n");
    g1(300);
    g2(60);
    g3(40);
    g4();
    g5(40);
    g6();
    bench();
    printf("== 结果: %s (fail=%d) ==\n", g_fail == 0 ? "ALL PASS" : "HAS FAIL", g_fail);
    return g_fail == 0 ? 0 : 1;
}
