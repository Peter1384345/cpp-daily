// 0004 · 并查集 DSU —— 路径压缩 / 按大小合并 / 带权并查集 / 可撤销并查集 / 线段树分治
//
// 编译：g++ -O2 -std=c++17 -Wall -Wextra -o dsu 0004_dsu.cpp
// 程序自带随机对拍（每个变体各自与暴力互拍）与性能基准，全部通过返回码为 0。
//
// 四个变体：
//   1. DSU          路径压缩 + 按大小合并，O(alpha(n)) 摊还，动态连通性主力
//   2. WeightedDSU  带权（差分）并查集，维护 val[x] - val[root]，可判矛盾
//   3. RollbackDSU  可撤销并查集，只按大小合并、不压缩，O(log n) 撤销
//   4. DynConn      线段树分治 + 可撤销并查集 —— 离线动态连通性 O((m log T) alpha)

#include <bits/stdc++.h>
using namespace std;
using ll = long long;

// ============================================================
// 1. 基础 DSU：路径压缩 + 按大小合并
// ============================================================
class DSU {
public:
    explicit DSU(int n = 0) { init(n); }

    void init(int n) {
        p_.resize(n);
        sz_.assign(n, 1);
        comp_ = n;
        for (int i = 0; i < n; ++i) p_[i] = i;
    }
    // 迭代版路径压缩（两趟，无递归开销）：
    //   第一趟找根，第二趟把整条链直接挂到根上
    int find(int x) {
        int r = x;
        while (p_[r] != r) r = p_[r];
        while (p_[x] != r) {
            const int nxt = p_[x];
            p_[x] = r;
            x = nxt;
        }
        return r;
    }
    bool unite(int a, int b) {
        a = find(a);
        b = find(b);
        if (a == b) return false;
        if (sz_[a] < sz_[b]) swap(a, b);   // 小树挂大树：保证树高 O(log n)
        p_[b] = a;
        sz_[a] += sz_[b];
        --comp_;
        return true;
    }
    bool same(int a, int b) { return find(a) == find(b); }
    int comp() const { return comp_; }
    int size(int x) { return sz_[find(x)]; }   // 非根的 sz_ 是陈旧值，必须走根

private:
    vector<int> p_, sz_;
    int comp_ = 0;
};

// 对照实现 A：只按大小合并，不做路径压缩 —— 考察"压缩"本身的收益
class DSUPlain {
public:
    explicit DSUPlain(int n = 0) : p_(n), sz_(n, 1) {
        for (int i = 0; i < n; ++i) p_[i] = i;
    }
    int find(int x) const {
        while (p_[x] != x) x = p_[x];
        return x;
    }
    bool unite(int a, int b) {
        a = find(a);
        b = find(b);
        if (a == b) return false;
        if (sz_[a] < sz_[b]) swap(a, b);
        p_[b] = a;
        sz_[a] += sz_[b];
        return true;
    }
    bool same(int a, int b) const { return find(a) == find(b); }

private:
    vector<int> p_, sz_;
};

// 对照实现 B：既无压缩也无启发式合并 —— 链式输入下退化成 O(n) 的单链表
class DSUNaive {
public:
    explicit DSUNaive(int n = 0) : p_(n) {
        for (int i = 0; i < n; ++i) p_[i] = i;
    }
    int find(int x) const {
        while (p_[x] != x) x = p_[x];
        return x;
    }
    void unite(int a, int b) { p_[find(b)] = find(a); }   // 直接把后者根挂到前者根下
    bool same(int a, int b) const { return find(a) == find(b); }

private:
    vector<int> p_;
};

// ============================================================
// 2. 带权 DSU（差分 DSU）
//    维护 d[x] = val[x] - val[parent[x]]；find 后 d[x] = val[x] - val[root]
//    典型应用：前缀和关系校验、食物链种类、Parity Game 奇偶约束
// ============================================================
class WeightedDSU {
public:
    explicit WeightedDSU(int n = 0) : p_(n), d_(n, 0), sz_(n, 1) {
        for (int i = 0; i < n; ++i) p_[i] = i;
    }
    // 递归深度被按大小合并限制在 O(log n)，无需担心爆栈
    int find(int x) {
        if (p_[x] == x) return x;
        const int r = find(p_[x]);
        d_[x] += d_[p_[x]];   // 父已挂到根，其 d_ 即 val[父]-val[根]；必须先加再改 p_
        p_[x] = r;
        return r;
    }
    // 断言 val[b] - val[a] == w。与已知信息矛盾返回 false（状态不变）
    bool relate(int a, int b, ll w) {
        const int ra = find(a), rb = find(b);
        if (ra == rb) return d_[b] - d_[a] == w;
        // 需 val[rb] - val[ra] = w - d_[b] + d_[a]
        const ll delta = w - d_[b] + d_[a];
        if (sz_[ra] < sz_[rb]) {        // 把 ra 挂到 rb 下：d_[ra] = val[ra]-val[rb] = -delta
            p_[ra] = rb;
            d_[ra] = -delta;
            sz_[rb] += sz_[ra];
        } else {                        // 把 rb 挂到 ra 下
            p_[rb] = ra;
            d_[rb] = delta;
            sz_[ra] += sz_[rb];
        }
        return true;
    }
    bool same(int a, int b) { return find(a) == find(b); }
    // 前提：a、b 已连通；返回 val[b] - val[a]
    ll diff(int a, int b) {
        find(a);
        find(b);                        // 两次 find 后 d_ 均已是"到根的距离"（顺序无关）
        return d_[b] - d_[a];
    }

private:
    vector<int> p_, sz_;
    vector<ll> d_;
};

// ============================================================
// 3. 可撤销 DSU：只按大小合并（树高 O(log n)），用栈记录被改动的字段
//    关键取舍：一旦路径压缩，"撤销"就必须还原整条被压扁的链 → 放弃压缩
// ============================================================
class RollbackDSU {
public:
    explicit RollbackDSU(int n = 0) : p_(n), sz_(n, 1) {
        for (int i = 0; i < n; ++i) p_[i] = i;
    }
    int find(int x) const {              // 无压缩，纯爬树
        while (p_[x] != x) x = p_[x];
        return x;
    }
    bool same(int a, int b) const { return find(a) == find(b); }
    int snapshot() const { return (int)hist_.size(); }

    void rollback(int snap) {
        while ((int)hist_.size() > snap) {
            const Rec e = hist_.back();
            hist_.pop_back();
            p_[e.b] = e.b;               // b 原本是根
            sz_[e.b] = e.szb;            // 恢复 b 的旧大小（b 成为子节点后大小不再变化）
            sz_[e.a] -= e.szb;           // a 仍是根（LIFO 保证），减回去即可
        }
    }
    bool unite(int a, int b) {
        a = find(a);
        b = find(b);
        if (a == b) return false;
        if (sz_[a] < sz_[b]) swap(a, b);
        hist_.push_back({a, b, sz_[b]});
        p_[b] = a;
        sz_[a] += sz_[b];
        return true;
    }

private:
    struct Rec { int a, b, szb; };
    vector<int> p_, sz_;
    vector<Rec> hist_;
};

// ============================================================
// 4. 线段树分治：离线动态连通性
//    每条边在 [l, r) 时间内存在 → 挂到线段树 O(log T) 个节点上；
//    DFS 时进入节点即并边、离开节点即撤销 → 每个时刻看到的恰好是"当时存活"的边集合
// ============================================================
class DynConn {
public:
    explicit DynConn(int T) : T_(max(1, T)), seg_(4 * (size_t)max(1, T)) {}

    void add(int l, int r, int u, int v) {   // 半开区间 [l, r)，要求 0 <= l < r <= T_
        addRec(1, 0, T_ - 1, l, r - 1, u, v);
    }
    // qs[t] = {(u, v, idx)}，答案写入 ans[idx]（1 = 连通）
    void solve(RollbackDSU& dsu, const vector<vector<array<int, 3>>>& qs, vector<char>& ans) {
        dfs(1, 0, T_ - 1, dsu, qs, ans);
    }

private:
    void addRec(int node, int nl, int nr, int ql, int qr, int u, int v) {
        if (qr < nl || nr < ql) return;
        if (ql <= nl && nr <= qr) { seg_[node].push_back({u, v}); return; }
        const int mid = (nl + nr) >> 1;
        addRec(node << 1, nl, mid, ql, qr, u, v);
        addRec(node << 1 | 1, mid + 1, nr, ql, qr, u, v);
    }
    void dfs(int node, int nl, int nr, RollbackDSU& dsu,
             const vector<vector<array<int, 3>>>& qs, vector<char>& ans) {
        const int snap = dsu.snapshot();
        for (const auto& e : seg_[node]) dsu.unite(e[0], e[1]);
        if (nl == nr) {
            for (const auto& q : qs[nl]) ans[q[2]] = dsu.same(q[0], q[1]) ? 1 : 0;
        } else {
            const int mid = (nl + nr) >> 1;
            dfs(node << 1, nl, mid, dsu, qs, ans);
            dfs(node << 1 | 1, mid + 1, nr, dsu, qs, ans);
        }
        dsu.rollback(snap);
    }
    int T_;
    vector<vector<array<int, 2>>> seg_;
};

// ============================================================
// 暴力基准：邻接表 + BFS 重建连通分量
// ============================================================
static vector<int> bruteComp(int n, const vector<pair<int, int>>& edges) {
    vector<vector<int>> adj(n);
    for (const auto& e : edges) {
        adj[e.first].push_back(e.second);
        adj[e.second].push_back(e.first);
    }
    vector<int> c(n, -1);
    int id = 0;
    for (int s = 0; s < n; ++s) {
        if (c[s] != -1) continue;
        vector<int> st{s};
        c[s] = id;
        while (!st.empty()) {
            const int u = st.back();
            st.pop_back();
            for (int v : adj[u])
                if (c[v] == -1) { c[v] = id; st.push_back(v); }
        }
        ++id;
    }
    return c;
}

static uint64_t rngState = 0x9E3779B97F4A7C15ull;
static uint64_t rnd() {
    rngState ^= rngState << 13;
    rngState ^= rngState >> 7;
    rngState ^= rngState << 17;
    return rngState;
}

int main() {
    const int kRounds = 300;
    ll checks = 0;

    // ---------- A. 基础 DSU 对拍：每次 union 后与 BFS 重建分量比对 ----------
    for (int round = 0; round < kRounds; ++round) {
        const int n = 1 + (int)(rnd() % 120);
        const int m = 1 + (int)(rnd() % 60);
        DSU dsu(n);
        vector<pair<int, int>> edges;
        for (int i = 0; i < m; ++i) {
            const int u = (int)(rnd() % n), v = (int)(rnd() % n);
            if (dsu.unite(u, v)) edges.push_back({u, v});
            const vector<int> c = bruteComp(n, edges);
            const int comps = *max_element(c.begin(), c.end()) + 1;
            if (comps != dsu.comp()) {
                fprintf(stderr, "FAIL[A] round=%d n=%d comp dsu=%d brute=%d\n",
                        round, n, dsu.comp(), comps);
                return 1;
            }
            for (int t = 0; t < 20; ++t) {
                const int a = (int)(rnd() % n), b = (int)(rnd() % n);
                if (dsu.same(a, b) != (c[a] == c[b])) {
                    fprintf(stderr, "FAIL[A] round=%d a=%d b=%d\n", round, a, b);
                    return 1;
                }
                ++checks;
            }
        }
    }
    printf("[对拍 A] 基础 DSU vs BFS 重建：%d 轮，%lld 次连通性判定一致  PASS\n",
           kRounds, checks);

    // ---------- B. 带权 DSU 对拍：真关系必须接受，矛盾必须识破 ----------
    checks = 0;
    ll rejected = 0;
    for (int round = 0; round < kRounds; ++round) {
        const int n = 1 + (int)(rnd() % 60);          // 前缀下标 0..n
        vector<ll> P(n + 1, 0);                       // 真实前缀和
        for (int i = 1; i <= n; ++i) P[i] = P[i - 1] + (ll)(rnd() % 2001) - 1000;
        WeightedDSU w(n + 1);
        for (int op = 0; op < 40; ++op) {
            const int u = (int)(rnd() % (n + 1)), v = (int)(rnd() % (n + 1));
            if (u == v) continue;
            const ll real = P[v] - P[u];
            // 只在已连通时造矛盾，否则假关系会被"合法"接收并污染状态
            const bool wantFalse = (rnd() & 1) && w.same(u, v);
            const ll claim = wantFalse ? real + (ll)(1 + rnd() % 50) : real;
            const bool accepted = w.relate(u, v, claim);
            if (wantFalse) {
                if (accepted) {
                    fprintf(stderr, "FAIL[B] round=%d 矛盾未被识破 u=%d v=%d claim=%lld real=%lld\n",
                            round, u, v, claim, real);
                    return 1;
                }
                ++rejected;
            } else {
                if (!accepted) {
                    fprintf(stderr, "FAIL[B] round=%d 真实关系被拒 u=%d v=%d w=%lld\n",
                            round, u, v, claim);
                    return 1;
                }
                if (w.diff(u, v) != real || w.diff(v, u) != -real) {
                    fprintf(stderr, "FAIL[B] round=%d 差分错误 u=%d v=%d\n", round, u, v);
                    return 1;
                }
                ++checks;
            }
        }
    }
    printf("[对拍 B] 带权 DSU vs 真实前缀和：%d 轮，%lld 次差分校验通过、%lld 次矛盾被识破  PASS\n",
           kRounds, checks, rejected);

    // ---------- C. 可撤销 DSU 对拍：union / snapshot / rollback 交错 ----------
    checks = 0;
    for (int round = 0; round < 200; ++round) {
        const int n = 1 + (int)(rnd() % 50);
        RollbackDSU r(n);
        vector<pair<int, int>> active;               // 当前生效的合并边
        vector<pair<int, int>> snaps;                // (dsu 快照, active.size())
        for (int step = 0; step < 120; ++step) {
            const int kind = (int)(rnd() % 3);
            if (kind == 0 && !snaps.empty()) {
                const int k = (int)(rnd() % snaps.size());
                r.rollback(snaps[k].first);
                active.resize(snaps[k].second);
                snaps.resize((size_t)k + 1);         // 更晚的快照已失效
            } else if (kind == 1) {
                snaps.push_back({r.snapshot(), (int)active.size()});
            } else {
                const int u = (int)(rnd() % n), v = (int)(rnd() % n);
                if (r.unite(u, v)) active.push_back({u, v});
            }
            const vector<int> c = bruteComp(n, active);
            for (int a = 0; a < n; ++a)
                for (int b = a + 1; b < n; ++b) {
                    if (r.same(a, b) != (c[a] == c[b])) {
                        fprintf(stderr, "FAIL[C] round=%d step=%d a=%d b=%d\n", round, step, a, b);
                        return 1;
                    }
                    ++checks;
                }
        }
    }
    printf("[对拍 C] 可撤销 DSU vs BFS 重建：200 轮，%lld 次判定一致  PASS\n", checks);

    // ---------- D. 线段树分治对拍：每个时刻的答案与暴力逐时刻重建一致 ----------
    checks = 0;
    for (int round = 0; round < 60; ++round) {
        const int T = 1 + (int)(rnd() % 24);
        const int n = 1 + (int)(rnd() % 20);
        const int m = (int)(rnd() % 40);
        struct E { int l, r, u, v; };
        vector<E> es;
        for (int i = 0; i < m; ++i) {
            const int l = (int)(rnd() % T);
            const int rr = l + 1 + (int)(rnd() % (T - l));
            es.push_back({l, rr, (int)(rnd() % n), (int)(rnd() % n)});
        }
        const int qn = 1 + (int)(rnd() % 30);
        vector<vector<array<int, 3>>> byTime(T);
        for (int i = 0; i < qn; ++i)
            byTime[rnd() % T].push_back({(int)(rnd() % n), (int)(rnd() % n), i});

        DynConn dc(T);
        for (const auto& e : es) dc.add(e.l, e.r, e.u, e.v);
        vector<char> ans(qn, 0);
        RollbackDSU dsu(n);
        dc.solve(dsu, byTime, ans);

        for (int t = 0; t < T; ++t) {
            vector<pair<int, int>> act;
            for (const auto& e : es)
                if (e.l <= t && t < e.r) act.push_back({e.u, e.v});
            const vector<int> c = bruteComp(n, act);
            for (const auto& q : byTime[t]) {
                const char expect = (c[q[0]] == c[q[1]]) ? 1 : 0;
                if (ans[q[2]] != expect) {
                    fprintf(stderr, "FAIL[D] round=%d t=%d u=%d v=%d\n", round, t, q[0], q[1]);
                    return 1;
                }
                ++checks;
            }
        }
    }
    printf("[对拍 D] 线段树分治 vs 逐时刻重建：60 轮，%lld 次查询一致  PASS\n\n", checks);

    // ================= 性能基准 =================
    auto ms = [](chrono::steady_clock::time_point s, chrono::steady_clock::time_point e) {
        return (ll)chrono::duration_cast<chrono::milliseconds>(e - s).count();
    };
    const int kUnions = 1 << 22, kFinds = 1 << 23;
    const int N = 1 << 22;

    printf("[基准 1] 随机并 + 大量查询：n=%d, union=%d, find=%d\n", N, kUnions, kFinds);
    {
        DSU a(N);
        auto t0 = chrono::steady_clock::now();
        for (int i = 0; i < kUnions; ++i)
            a.unite((int)(rnd() % N), (int)(rnd() % N));
        auto t1 = chrono::steady_clock::now();
        uint64_t cs = 0;
        for (int i = 0; i < kFinds; ++i) cs += (uint64_t)a.find((int)(rnd() % N));
        auto t2 = chrono::steady_clock::now();
        printf("  压缩+按大小 : union %lld ms | find %lld ms (%.1f ns/次) | 剩余分量 %d\n",
               ms(t0, t1), ms(t1, t2), ms(t1, t2) * 1e6 / kFinds, a.comp());
        rngState ^= 0x9E3779B9ull;   // 让两组操作序列同分布但不同值

        DSUPlain b(N);
        auto s0 = chrono::steady_clock::now();
        for (int i = 0; i < kUnions; ++i)
            b.unite((int)(rnd() % N), (int)(rnd() % N));
        auto s1 = chrono::steady_clock::now();
        uint64_t cs2 = 0;
        for (int i = 0; i < kFinds; ++i) cs2 += (uint64_t)b.find((int)(rnd() % N));
        auto s2 = chrono::steady_clock::now();
        printf("  仅按大小    : union %lld ms | find %lld ms (%.1f ns/次)\n",
               ms(s0, s1), ms(s1, s2), ms(s1, s2) * 1e6 / kFinds);
        printf("  校验和 %llu / %llu\n", (unsigned long long)cs, (unsigned long long)cs2);
    }

    printf("[基准 2] 链式合并 i--i+1（最坏输入），随机 find\n");
    {
        const int C = 1 << 16;
        DSU a(C);
        auto t0 = chrono::steady_clock::now();
        for (int i = 0; i + 1 < C; ++i) a.unite(i, i + 1);
        auto t1 = chrono::steady_clock::now();
        uint64_t cs = 0;
        for (int i = 0; i < (1 << 20); ++i) cs += (uint64_t)a.find((int)(rnd() % C));
        auto t2 = chrono::steady_clock::now();
        printf("  压缩+按大小 : union %lld ms | find(1M) %lld ms (%.1f ns/次)\n",
               ms(t0, t1), ms(t1, t2), ms(t1, t2) * 1e6 / (1 << 20));

        DSUPlain b(C);
        for (int i = 0; i + 1 < C; ++i) b.unite(i, i + 1);
        auto s1 = chrono::steady_clock::now();
        for (int i = 0; i < (1 << 20); ++i) cs += (uint64_t)b.find((int)(rnd() % C));
        auto s2 = chrono::steady_clock::now();
        printf("  仅按大小    :                     find(1M) %lld ms (%.1f ns/次)\n",
               ms(s1, s2), ms(s1, s2) * 1e6 / (1 << 20));

        const int KN = 512;                 // 朴素版单次 find 就是 O(n)，只跑极少次数
        DSUNaive c(C);
        auto u0 = chrono::steady_clock::now();
        for (int i = 0; i + 1 < C; ++i) c.unite(i, i + 1);
        auto u1 = chrono::steady_clock::now();
        for (int i = 0; i < KN; ++i) cs += (uint64_t)c.find((int)(rnd() % C));
        auto u2 = chrono::steady_clock::now();
        printf("  朴素(无优化): union %lld ms | find(%d) %lld ms (%.1f ns/次)\n",
               ms(u0, u1), KN, ms(u1, u2), ms(u1, u2) * 1e6 / KN);
        printf("  校验和 %llu（防止查询被优化删除）\n", (unsigned long long)cs);
    }

    printf("[基准 3] 带权 DSU：n=2M，relate 2M 次 + diff 4M 次\n");
    {
        const int M = 1 << 21;
        WeightedDSU w(M);
        auto t0 = chrono::steady_clock::now();
        for (int i = 0; i < M; ++i)
            w.relate((int)(rnd() % M), (int)(rnd() % M), (ll)(rnd() % 1000));
        auto t1 = chrono::steady_clock::now();
        ll cs = 0;
        for (int i = 0; i < (1 << 22); ++i) {
            const int u = (int)(rnd() % M), v = (int)(rnd() % M);
            cs += w.diff(u, v);
        }
        auto t2 = chrono::steady_clock::now();
        printf("  relate %lld ms (%.1f ns/次) | diff %lld ms (%.1f ns/次) | 校验和 %lld\n",
               ms(t0, t1), ms(t0, t1) * 1e6 / M, ms(t1, t2),
               ms(t1, t2) * 1e6 / (1 << 22), (long long)cs);
    }

    printf("[基准 4] 离线动态连通性：线段树分治 vs 逐时刻重建\n");
    {
        const int T = 1 << 11, M = 1 << 13, QN = 1 << 13, n = 1 << 12;
        struct E { int l, r, u, v; };
        vector<E> es;
        for (int i = 0; i < M; ++i) {
            const int l = (int)(rnd() % T);
            const int rr = l + 1 + (int)(rnd() % (T - l));
            es.push_back({l, rr, (int)(rnd() % n), (int)(rnd() % n)});
        }
        vector<vector<array<int, 3>>> byTime(T);
        for (int i = 0; i < QN; ++i)
            byTime[rnd() % T].push_back({(int)(rnd() % n), (int)(rnd() % n), i});

        DynConn dc(T);
        for (const auto& e : es) dc.add(e.l, e.r, e.u, e.v);
        vector<char> ans(QN, 0);
        RollbackDSU dsu(n);
        auto t0 = chrono::steady_clock::now();
        dc.solve(dsu, byTime, ans);
        auto t1 = chrono::steady_clock::now();

        ll csSeg = 0;
        for (char v : ans) csSeg += v;
        ll csBrute = 0;
        for (int t = 0; t < T; ++t) {
            DSU fresh(n);
            for (const auto& e : es)
                if (e.l <= t && t < e.r) fresh.unite(e.u, e.v);
            for (const auto& q : byTime[t]) csBrute += fresh.same(q[0], q[1]);
        }
        auto t2 = chrono::steady_clock::now();
        printf("  T=%d, 边=%d, 查询=%d, n=%d\n", T, M, QN, n);
        printf("  线段树分治   : %lld ms\n", ms(t0, t1));
        printf("  逐时刻重建   : %lld ms  (复杂度 O(T*m*alpha)，分治为 O(m log T * alpha))\n",
               ms(t1, t2));
        if (csSeg != csBrute) {
            fprintf(stderr, "FAIL[基准4] 大规模答案不一致 分治=%lld 重建=%lld\n",
                    (long long)csSeg, (long long)csBrute);
            return 1;
        }
        printf("  校验和 分治=%lld 重建=%lld，%d 次查询答案完全一致  PASS\n",
               (long long)csSeg, (long long)csBrute, QN);
    }

    puts("\n全部测试通过（返回码 0）");
    return 0;
}
