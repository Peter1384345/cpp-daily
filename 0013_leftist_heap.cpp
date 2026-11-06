// ============================================================
// 0013 · 左偏树 / 可并堆 (Leftist Tree & Mergeable Heap)
// ------------------------------------------------------------
// 六个部分:
//   A. LeftistHeap    左偏树: dist(最短 null 路径长)不变式,
//                     merge 沿右脊柱 O(log n), 数组池零指针
//   B. SkewHeap       斜堆: 不存 dist, 每次合并恒交换左右,
//                     均摊 O(log n) 的自调整对照实现
//   C. 不变式检查     堆序 + dist 性质 + 右脊柱长度上界 log2(n+1)
//   D. LazyLeftistHeap 可删除/可减键堆: 死标记惰性生效,
//                     stale > live 时 O(live) 收集重建
//   E. Dijkstra       懒减键左偏树 vs std::priority_queue 重复插入
//   F. 基准           m 个堆逐个合并(左偏 vs 斜堆) + 大图 Dijkstra
// 正确性: 对拍 multiset 暴力 / Bellman-Ford / 双 Dijkstra 交叉
// 编译:   g++ -O2 -std=c++17 -Wall -Wextra 0013_leftist_heap.cpp -o 0013
// 注意:   本期源码未在本机编译(环境无 C++ 编译器), 算法逻辑已通过
//         Python 逐行镜像对拍验证, 详见 0013_leftist_heap.md
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

// ============================================================
// A. 左偏树核心: 共享数组池 LT, 0 号为哨兵(dist = -1)
//    不变式: dist[lc] >= dist[rc], dist[x] = dist[rc] + 1
//    => 右脊柱长度 <= log2(n+1), merge 代价 O(log n)
// ============================================================
struct LtNode { ll key; int lc, rc, dist; };
static vector<LtNode> LT(1);          // LT[0] 哨兵
static long long g_merge_path = 0;    // merge 走过的节点数(基准用)

static void ltInit() {
    LT.clear();
    LT.push_back({0, 0, 0, -1});
    g_merge_path = 0;
}
static int ltNew(ll k) {
    LT.push_back({k, 0, 0, 0});
    return (int)LT.size() - 1;
}
static int ltMerge(int a, int b) {
    if (!a || !b) return a + b;
    ++g_merge_path;
    if (LT[b].key > LT[a].key) std::swap(a, b);   // 大者作根(大根堆)
    LT[a].rc = ltMerge(LT[a].rc, b);
    if (LT[LT[a].lc].dist < LT[LT[a].rc].dist)
        std::swap(LT[a].lc, LT[a].rc);            // 保持左偏
    LT[a].dist = LT[LT[a].rc].dist + 1;
    return a;
}

class LeftistHeap {
public:
    bool   empty() const { return root_ == 0; }
    size_t size()  const { return n_; }
    ll     top()   const { return LT[root_].key; }

    void push(ll k) { root_ = ltMerge(root_, ltNew(k)); ++n_; }

    void pop() {
        int r = root_;
        root_ = ltMerge(LT[r].lc, LT[r].rc);
        --n_;
    }

    void mergeWith(LeftistHeap& o) {
        root_ = ltMerge(root_, o.root_);
        n_ += o.n_;
        o.root_ = 0; o.n_ = 0;
    }

    int spine() const {                      // 右脊柱长度
        int s = 0;
        for (int x = root_; x; x = LT[x].rc) ++s;
        return s;
    }

private:
    int root_ = 0;
    size_t n_ = 0;

public:
    // 迭代先序检查(左偏树左脊柱可达 O(n), 递归会爆栈)
    void checkInvariants() const {
        vector<int> st;
        if (root_) st.push_back(root_);
        while (!st.empty()) {
            int x = st.back(); st.pop_back();
            ll k = LT[x].key;
            if (LT[x].lc) CHECK(LT[LT[x].lc].key <= k,
                "heap order broken: left child %lld > parent %lld",
                (long long)LT[LT[x].lc].key, (long long)k);
            if (LT[x].rc) CHECK(LT[LT[x].rc].key <= k,
                "heap order broken: right child %lld > parent %lld",
                (long long)LT[LT[x].rc].key, (long long)k);
            CHECK(LT[x].dist == LT[LT[x].rc].dist + 1,
                "dist formula broken at node (key=%lld)", (long long)k);
            CHECK(LT[LT[x].lc].dist >= LT[LT[x].rc].dist,
                "leftist property broken at node (key=%lld)", (long long)k);
            if (LT[x].lc) st.push_back(LT[x].lc);
            if (LT[x].rc) st.push_back(LT[x].rc);
        }
    }
};

// ============================================================
// B. 斜堆: 不存 dist, 合并后恒交换左右子树
//    单次最坏 O(n), 均摊 O(log n) —— 与左偏树对照常数
// ============================================================
struct SkNode { ll key; int lc, rc; };
static vector<SkNode> SK(1);          // SK[0] 哨兵

static void skInit() { SK.clear(); SK.push_back({0, 0, 0}); }
static int skNew(ll k) { SK.push_back({k, 0, 0}); return (int)SK.size() - 1; }
static int skMerge(int a, int b) {
    if (!a || !b) return a + b;
    ++g_merge_path;
    if (SK[b].key > SK[a].key) std::swap(a, b);
    SK[a].rc = skMerge(SK[a].rc, b);
    std::swap(SK[a].lc, SK[a].rc);    // 无条件交换 —— 斜堆的全部秘密
    return a;
}

class SkewHeap {
public:
    bool   empty() const { return root_ == 0; }
    size_t size()  const { return n_; }
    ll     top()   const { return SK[root_].key; }

    void push(ll k) { root_ = skMerge(root_, skNew(k)); ++n_; }

    void pop() {
        int r = root_;
        root_ = skMerge(SK[r].lc, SK[r].rc);
        --n_;
    }

    void mergeWith(SkewHeap& o) {
        root_ = skMerge(root_, o.root_);
        n_ += o.n_;
        o.root_ = 0; o.n_ = 0;
    }

private:
    int root_ = 0;
    size_t n_ = 0;

public:
    // 迭代先序检查(斜堆树高可达 O(n), 递归会爆栈)
    void checkOrder() const {
        vector<int> st;
        if (root_) st.push_back(root_);
        while (!st.empty()) {
            int x = st.back(); st.pop_back();
            if (SK[x].lc) CHECK(SK[SK[x].lc].key <= SK[x].key,
                "skew heap order broken: left %lld > parent %lld",
                (long long)SK[SK[x].lc].key, (long long)SK[x].key);
            if (SK[x].rc) CHECK(SK[SK[x].rc].key <= SK[x].key,
                "skew heap order broken: right %lld > parent %lld",
                (long long)SK[SK[x].rc].key, (long long)SK[x].key);
            if (SK[x].lc) st.push_back(SK[x].lc);
            if (SK[x].rc) st.push_back(SK[x].rc);
        }
    }
};

// ============================================================
// D. LazyLeftistHeap: 可删除/可减键堆
//    erase(id) 只打标记; pop 遇死顶点直接丢弃;
//    stale > live 时收集活顶点 O(live) 队列式两两合并重建
//    —— 减键 = erase(旧id) + push(新键, 新id)
// ============================================================
class LazyLeftistHeap {
public:
    LazyLeftistHeap() { t_.push_back({0, 0, 0, 0, -1}); }

    bool empty() const { return root_ == 0; }

    // 返回分配的 id (调用方用 id 追踪该元素)
    int push(ll key, int id) {
        int x = nn(key, id);
        root_ = mg(root_, x);
        ++live_;
        return id;
    }

    void erase(int id) {
        if (!dead_.insert(id).second) return;    // 重复 erase 只计一次
        ++stale_;
        if (stale_ > live_) rebuild();
    }

    // 弹出当前最大活元素; 空返回 false
    bool pop(ll& key, int& id) {
        while (root_ && dead_.count(t_[root_].id)) {
            int r = root_;
            root_ = mg(t_[r].lc, t_[r].rc);
            dead_.erase(t_[r].id);               // id 不复用, 出树即清
            --stale_;
            --live_;
        }
        if (!root_) return false;
        key = t_[root_].key;
        id  = t_[root_].id;
        root_ = mg(t_[root_].lc, t_[root_].rc);
        --live_;
        return true;
    }

    void checkInvariants() const {
        CHECK(stale_ <= live_, "stale(%lld) > live(%lld) beyond rebuild",
              stale_, live_);
        vector<int> st;
        if (root_) st.push_back(root_);
        while (!st.empty()) {
            int x = st.back(); st.pop_back();
            if (t_[x].lc) CHECK(t_[t_[x].lc].key <= t_[x].key, "lazy heap order broken");
            if (t_[x].rc) CHECK(t_[t_[x].rc].key <= t_[x].key, "lazy heap order broken");
            CHECK(t_[x].dist == t_[t_[x].rc].dist + 1, "lazy heap dist broken");
            if (t_[x].lc) st.push_back(t_[x].lc);
            if (t_[x].rc) st.push_back(t_[x].rc);
        }
    }

private:
    struct N { ll key; int id, lc, rc, dist; };
    vector<N> t_;
    int root_ = 0;
    long long live_ = 0;     // 树内节点数(含死)
    long long stale_ = 0;    // 树内死节点数
    unordered_set<int> dead_;

    int nn(ll key, int id) {
        t_.push_back({key, id, 0, 0, 0});
        return (int)t_.size() - 1;
    }
    int mg(int a, int b) {
        if (!a || !b) return a + b;
        if (t_[b].key > t_[a].key) std::swap(a, b);
        t_[a].rc = mg(t_[a].rc, b);
        if (t_[t_[a].lc].dist < t_[t_[a].rc].dist)
            std::swap(t_[a].lc, t_[a].rc);
        t_[a].dist = t_[t_[a].rc].dist + 1;
        return a;
    }
    // 迭代收集(左偏树整树高可达 O(n), 避免深递归)
    void collect(int root, vector<pair<ll, int>>& v) const {
        vector<int> st;
        if (root) st.push_back(root);
        while (!st.empty()) {
            int x = st.back(); st.pop_back();
            if (!dead_.count(t_[x].id)) v.push_back({t_[x].key, t_[x].id});
            if (t_[x].lc) st.push_back(t_[x].lc);
            if (t_[x].rc) st.push_back(t_[x].rc);
        }
    }

    void rebuild() {
        vector<pair<ll, int>> v;
        collect(root_, v);
        t_.clear();
        t_.push_back({0, 0, 0, 0, -1});
        root_ = 0;
        deque<int> q;
        for (auto& pr : v) q.push_back(nn(pr.first, pr.second));
        while (q.size() > 1) {                    // 队列式两两合并 O(live)
            int a = q.front(); q.pop_front();
            int b = q.front(); q.pop_front();
            q.push_back(mg(a, b));
        }
        root_ = q.empty() ? 0 : q.front();
        stale_ = 0;
        live_ = (long long)v.size();
    }
};

// ============================================================
// E. Dijkstra: 懒减键左偏树版 vs std::priority_queue 版
// ============================================================
static vector<ll> dijkstraLazy(int n, const vector<vector<pair<int, ll>>>& g, int s) {
    const ll INF = LLONG_MAX / 4;
    vector<ll> best(n, INF);
    vector<int> id(n, -1);
    vector<int> owner;                            // heap id -> node
    LazyLeftistHeap h;

    best[s] = 0;
    // 堆是大根堆, Dijkstra 需小根堆 -> 键取负 (距离非负, 无溢出风险)
    id[s] = h.push(0, (int)owner.size());
    owner.push_back(s);

    while (!h.empty()) {
        ll dneg; int x;
        if (!h.pop(dneg, x)) break;
        ll d = -dneg;
        int v = owner[x];
        if (d != best[v]) continue;               // 死/过期条目
        for (auto& e : g[v]) {
            ll nd = d + e.second;
            if (nd < best[e.first]) {
                best[e.first] = nd;
                if (id[e.first] >= 0) h.erase(id[e.first]);   // 减键
                id[e.first] = h.push(-nd, (int)owner.size()); // 存负键
                owner.push_back(e.first);
            }
        }
    }
    return best;
}

static vector<ll> dijkstraPQ(int n, const vector<vector<pair<int, ll>>>& g, int s) {
    const ll INF = LLONG_MAX / 4;
    vector<ll> best(n, INF);
    priority_queue<pair<ll, int>, vector<pair<ll, int>>, greater<>> pq;
    best[s] = 0;
    pq.push({0, s});
    while (!pq.empty()) {
        auto [d, v] = pq.top(); pq.pop();
        if (d != best[v]) continue;
        for (auto& e : g[v]) {
            ll nd = d + e.second;
            if (nd < best[e.first]) {
                best[e.first] = nd;
                pq.push({nd, e.first});           // 重复插入式减键
            }
        }
    }
    return best;
}

// Bellman-Ford 慢对照
static vector<ll> bellmanFord(int n, const vector<array<ll, 3>>& edges, int s) {
    const ll INF = LLONG_MAX / 4;
    vector<ll> best(n, INF);
    best[s] = 0;
    for (int it = 0; it < n - 1; ++it) {
        bool chg = false;
        for (auto& e : edges) {
            if (best[e[0]] + e[2] < best[e[1]]) {
                best[e[1]] = best[e[0]] + e[2];
                chg = true;
            }
        }
        if (!chg) break;
    }
    return best;
}

// ============================================================
// G1. 左偏树 / 斜堆 vs multiset 三方对拍
// ============================================================
static void group1_leftist_skew() {
    printf("G1 左偏树/斜堆 vs multiset 三方对拍\n");
    ltInit(); skInit();
    const int H = 3;
    vector<LeftistHeap> L(H);
    vector<SkewHeap> K(H);
    vector<multiset<ll>> B(H);
    mt19937 rng(1301);
    long long ops = 0;

    for (int step = 0; step < 6000; ++step) {
        int tp = (int)(rng() % 100);
        int i = (int)(rng() % H), j = (int)(rng() % H);
        if (tp < 45) {
            ll v = (ll)(rng() % 1000000);
            L[i].push(v); K[i].push(v); B[i].insert(v);
            ++ops;
        } else if (tp < 75) {
            if (!L[i].empty()) {
                L[i].pop(); K[i].pop();
                B[i].erase(prev(B[i].end()));
                ++ops;
            }
        } else if (tp < 90) {
            if (i != j) {
                L[i].mergeWith(L[j]);
                K[i].mergeWith(K[j]);
                B[i].insert(B[j].begin(), B[j].end());
                B[j].clear();
                ++ops;
            }
        }
        for (int h = 0; h < H; ++h) {
            ll want = B[h].empty() ? LLONG_MIN : *B[h].rbegin();
            if (L[h].empty()) {
                CHECK(B[h].empty(), "leftist empty but brute has %zu elems", B[h].size());
            } else {
                CHECK(L[h].top() == want && L[h].size() == B[h].size(),
                      "leftist top/size mismatch: got %lld/%zu want %lld/%zu",
                      (long long)L[h].top(), L[h].size(), (long long)want, B[h].size());
            }
            if (K[h].empty()) {
                CHECK(B[h].empty(), "skew empty but brute has %zu elems", B[h].size());
            } else {
                CHECK(K[h].top() == want && K[h].size() == B[h].size(),
                      "skew top/size mismatch: got %lld/%zu want %lld/%zu",
                      (long long)K[h].top(), K[h].size(), (long long)want, B[h].size());
            }
        }
    }
    for (int h = 0; h < H; ++h) { L[h].checkInvariants(); K[h].checkOrder(); }
    printf("  %lld 次操作 x3 堆三方一致, 不变式全部通过\n", ops);
}

// ============================================================
// G2. 右脊柱上界 + 全量弹出有序性
// ============================================================
static void group2_spine_bound() {
    printf("G2 右脊柱长度上界 log2(n+1) 与弹出有序性\n");
    ltInit();
    LeftistHeap L;
    mt19937 rng(1302);
    const int N = 30000;
    for (int i = 0; i < N; ++i) L.push((ll)(rng() % 10000000));
    L.checkInvariants();

    int sp = L.spine();
    int ub = (int)floor(log2((double)N + 1.0)) + 1;
    CHECK(sp <= ub, "spine %d > log2(n+1)+1 = %d", sp, ub);
    printf("  n=%d 右脊柱=%d (上界 %d), 理论均值 ~%.1f\n",
           N, sp, ub, log2((double)N + 1.0));

    ll prev = LLONG_MAX;
    int cnt = 0;
    while (!L.empty()) {
        ll v = L.top();
        CHECK(v <= prev, "pop not descending: %lld after %lld", v, prev);
        prev = v;
        L.pop();
        ++cnt;
    }
    CHECK(cnt == N, "popped %d != %d", cnt, N);

    // 升序插入退化: 左偏树仍保持 O(log n) 右脊柱(与二叉堆 push 一样稳)
    ltInit();
    LeftistHeap L2;
    for (int i = 1; i <= 100000; ++i) L2.push(i);   // 升序插入: 最坏插入序列
    L2.checkInvariants();
    int sp2 = L2.spine();
    int ub2 = (int)floor(log2(100001.0)) + 1;
    CHECK(sp2 <= ub2, "ascending-insert spine %d > %d", sp2, ub2);
    printf("  升序插入 1e5: 右脊柱=%d (上界 %d) —— 左偏树无退化链问题\n", sp2, ub2);
}

// ============================================================
// G3. LazyLeftistHeap vs multiset (erase / decrease-key 模式)
// ============================================================
static void group3_lazy_heap() {
    printf("G3 可删除堆 vs multiset 对拍\n");
    LazyLeftistHeap h;
    multiset<ll> live;                            // 活元素键集合
    vector<int> ids;                              // 活元素 id 列表
    unordered_map<int, int> pos;                  // id -> 在 ids 中的下标
    unordered_map<int, ll> keyOf;                 // id -> 键
    mt19937 rng(1303);
    int nextId = 0;
    long long nPush = 0, nErase = 0, nPop = 0;

    auto removeAt = [&](size_t idx) {
        int moved = ids.back();
        ids[idx] = moved;
        pos[moved] = (int)idx;
        ids.pop_back();
    };

    for (int step = 0; step < 30000; ++step) {
        int tp = (int)(rng() % 100);
        if (tp < 40 || ids.empty()) {             // push
            ll k = (ll)(rng() % 1000000);
            int id = nextId++;
            h.push(k, id);
            live.insert(k);
            pos[id] = (int)ids.size();
            ids.push_back(id);
            keyOf[id] = k;
            ++nPush;
        } else if (tp < 65) {                     // erase (减键的前半)
            size_t idx = (size_t)(rng() % ids.size());
            int id = ids[idx];
            h.erase(id);
            live.erase(live.find(keyOf[id]));
            removeAt(idx);
            keyOf.erase(id);
            ++nErase;
        } else {                                  // pop, 必须恰好是最大活键
            ll d; int x;
            bool ok = h.pop(d, x);
            if (live.empty()) {
                CHECK(!ok, "pop returned element but live set empty");
            } else {
                CHECK(ok, "pop failed but live set has %zu elems", live.size());
                if (ok) {
                    ll want = *live.rbegin();
                    CHECK(d == want, "pop got %lld want %lld", d, want);
                    live.erase(live.find(want));
                    size_t idx = (size_t)pos[x];
                    removeAt(idx);
                    keyOf.erase(x);
                    ++nPop;
                }
            }
        }
        if (step % 500 == 0) h.checkInvariants();  // 全树检查抽样, 每 500 步一次
    }
    h.checkInvariants();
    printf("  push %lld / erase %lld / pop %lld 全程与 multiset 一致\n",
           nPush, nErase, nPop);
}

// ============================================================
// G4. Dijkstra 三方交叉 (懒减键 vs 重复插入 vs Bellman-Ford)
// ============================================================
static void group4_dijkstra() {
    printf("G4 Dijkstra 三方交叉对拍\n");
    mt19937 rng(1304);
    const int CASES = 15;
    long long checked = 0;

    for (int cs = 0; cs < CASES; ++cs) {
        int n = 30 + (int)(rng() % 30);           // 30..59
        vector<array<ll, 3>> edges;
        vector<vector<pair<int, ll>>> g(n);
        auto addEdge = [&](int u, int v, ll w) {
            g[u].push_back({v, w});
            edges.push_back({(ll)u, (ll)v, w});
        };
        for (int v = 1; v < n; ++v) {             // 保证连通
            int u = (int)(rng() % v);
            addEdge(u, v, (ll)(rng() % 50) + 1);
        }
        int extra = (int)(rng() % 120);
        for (int i = 0; i < extra; ++i) {
            int u = (int)(rng() % n), v = (int)(rng() % n);
            if (u != v) addEdge(u, v, (ll)(rng() % 50) + 1);
        }
        int s = (int)(rng() % n);

        auto a = dijkstraLazy(n, g, s);
        auto b = dijkstraPQ(n, g, s);
        auto c = bellmanFord(n, edges, s);
        for (int v = 0; v < n; ++v) {
            CHECK(a[v] == b[v], "case %d node %d: lazy %lld vs pq %lld",
                  cs, v, (long long)a[v], (long long)b[v]);
            CHECK(a[v] == c[v], "case %d node %d: lazy %lld vs bf %lld",
                  cs, v, (long long)a[v], (long long)c[v]);
            ++checked;
        }
    }
    printf("  %d 张随机图 x 平均 %lld 节点, 三方距离全部一致\n",
           CASES, checked / CASES);
}

// ============================================================
// F. 基准 (数值待本机编译后确认)
// ============================================================
static void bench_merge_heaps() {
    printf("B1 多堆逐个合并: m 个各含 k 元素的堆依次并入 (n=m*k)\n");
    const int M = 1500, K = 120;
    const int N = M * K;
    mt19937 rng(51301);

    // 左偏树
    ltInit();
    {
        vector<LeftistHeap> hs(M);
        for (int i = 0; i < M; ++i)
            for (int j = 0; j < K; ++j) hs[i].push((ll)(rng() % 10000000));
        g_merge_path = 0;
        auto t0 = chrono::steady_clock::now();
        for (int i = 1; i < M; ++i) hs[0].mergeWith(hs[i]);
        auto t1 = chrono::steady_clock::now();
        double ms = chrono::duration<double, milli>(t1 - t0).count();
        double avg = (double)g_merge_path / (double)(M - 1);
        printf("  左偏树: 合并 %d 堆 (n=%d) 用时 %.1f ms, 平均每并走 %.1f 个节点 (log2 n=%.1f)\n",
               M, N, ms, avg, log2((double)N));
        CHECK(hs[0].size() == (size_t)N, "leftist merged size %zu != %d", hs[0].size(), N);
    }

    // 斜堆对照
    skInit();
    {
        vector<SkewHeap> hs(M);
        for (int i = 0; i < M; ++i)
            for (int j = 0; j < K; ++j) hs[i].push((ll)(rng() % 10000000));
        g_merge_path = 0;
        auto t0 = chrono::steady_clock::now();
        for (int i = 1; i < M; ++i) hs[0].mergeWith(hs[i]);
        auto t1 = chrono::steady_clock::now();
        double ms = chrono::duration<double, milli>(t1 - t0).count();
        double avg = (double)g_merge_path / (double)(M - 1);
        printf("  斜堆:   同负载用时 %.1f ms, 平均每并走 %.1f 个节点\n", ms, avg);
        CHECK(hs[0].size() == (size_t)N, "skew merged size %zu != %d", hs[0].size(), N);
    }

    // 基线: 元素逐个重推 std::priority_queue —— 无 merge 能力时的唯一选择
    {
        vector<vector<ll>> vals(M);
        for (int i = 0; i < M; ++i)
            for (int j = 0; j < K; ++j) vals[i].push_back((ll)(rng() % 10000000));
        auto t0 = chrono::steady_clock::now();
        priority_queue<ll> pq;
        for (int i = 0; i < M; ++i)
            for (ll v : vals[i]) pq.push(v);
        auto t1 = chrono::steady_clock::now();
        double ms = chrono::duration<double, milli>(t1 - t0).count();
        printf("  基线:   全部元素重推 priority_queue 用时 %.1f ms (O(n log n), 无法增量并堆)\n", ms);
        CHECK(pq.size() == (size_t)N, "pq size %zu != %d", pq.size(), N);
    }
}

static void bench_dijkstra() {
    printf("B2 大图 Dijkstra: 懒减键左偏树 vs priority_queue 重复插入 (n=5e4, m=2.5e5)\n");
    const int N = 50000, M = 250000;
    mt19937 rng(51302);
    vector<vector<pair<int, ll>>> g(N);
    vector<array<ll, 3>> edges;
    edges.reserve(M);
    for (int v = 1; v < N; ++v) {
        int u = (int)(rng() % v);
        ll w = (ll)(rng() % 1000) + 1;
        g[u].push_back({v, w});
        edges.push_back({(ll)u, (ll)v, w});
    }
    for (int i = 0; i < M - (N - 1); ++i) {
        int u = (int)(rng() % N), v = (int)(rng() % N);
        if (u == v) { --i; continue; }
        ll w = (ll)(rng() % 1000) + 1;
        g[u].push_back({v, w});
        edges.push_back({(ll)u, (ll)v, w});
    }

    auto t0 = chrono::steady_clock::now();
    auto a = dijkstraLazy(N, g, 0);
    auto t1 = chrono::steady_clock::now();
    auto b = dijkstraPQ(N, g, 0);
    auto t2 = chrono::steady_clock::now();
    double ms1 = chrono::duration<double, milli>(t1 - t0).count();
    double ms2 = chrono::duration<double, milli>(t2 - t1).count();
    ll sa = 0, sb = 0;
    for (int v = 0; v < N; ++v) { sa += a[v] % 1000003; sb += b[v] % 1000003; }
    CHECK(sa == sb, "checksum mismatch: %lld vs %lld", sa, sb);
    printf("  懒减键左偏树 %.1f ms | priority_queue %.1f ms | 校验和一致 (%lld)\n",
           ms1, ms2, sa);
}

int main() {
    printf("== 0013 左偏树 / 可并堆 ==\n\n");
    group1_leftist_skew();
    group2_spine_bound();
    group3_lazy_heap();
    group4_dijkstra();
    printf("\n");
    bench_merge_heaps();
    bench_dijkstra();

    printf("\n%s (g_fail=%d)\n", g_fail ? "存在失败项" : "全部通过", g_fail);
    return g_fail ? 1 : 0;
}
