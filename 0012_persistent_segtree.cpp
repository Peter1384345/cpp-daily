// 0012 · 可持久化线段树（主席树）+ 小波矩阵 Wavelet Matrix
// 编译：g++ -O2 -std=c++17 -Wall -Wextra 0012_persistent_segtree.cpp -o 0012
// 运行：./0012      返回码 0 = 全部验证通过（对拍 + 结构不变式），1 = 有失败
//
// 本程序包含五个部分：
//   Part 0  PersistArray    —— 可持久化数组（版本链，不涉及值域）
//   Part 1  PersistentKth   —— 主席树：静态区间第 k 小 / 区间内 <= x 的个数 / 区间内值域求和
//   Part 2  WaveletMatrix   —— 小波矩阵：同样的 kth 与 countLe，O(n log σ) 但常数与内存小得多
//   Part 3  MergeSortTree   —— 归并树：O(log V · log² n) 的"慢对照"
//   Part 4  Brute           —— 暴力 oracle：nth_element / 线性扫
// 验证组 G1–G5，最后是 n=200000 / q=100000 的基准。
#include <bits/stdc++.h>

using namespace std;
using ll = long long;
using u64 = unsigned long long;

// ---------------------------------------------------------------- 基础设施

struct Rng {
    u64 s;
    explicit Rng(u64 seed = 0x9E3779B97F4A7C15ULL) : s(seed) {}
    u64 next() {
        s += 0x9E3779B97F4A7C15ULL;
        u64 z = s;
        z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
        z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
        return z ^ (z >> 31);
    }
    // [lo, hi] 闭区间
    int nextInt(int lo, int hi) { return lo + (int)(next() % (u64)(hi - lo + 1)); }
};

static double nowMs() {
    using namespace std::chrono;
    return duration<double, milli>(steady_clock::now().time_since_epoch()).count();
}

static int g_checks = 0;
static int g_fail = 0;

static void failMsg(const char* what) { printf("    [FAIL] %s\n", what); }

#define CHECK(cond, what) do { ++g_checks; if (!(cond)) { ++g_fail; failMsg(what); } } while (0)

// ------------------------------------------------- Part 0 可持久化数组（版本链）
// 单点赋值 + 历史版本读取。每次 set 只复制 O(log n) 个节点，其余全部共享。
// 这是"可持久化"最朴素的样子：不涉及值域，只演示版本之间如何共享。
struct PersistArray {
    int n = 0;
    vector<int> lc, rc, leaf;  // leaf 只在叶子节点有意义
    vector<int> roots;         // roots[v] = 第 v 个版本的根

    void init(int n_) {
        n = n_;
        lc.clear(); rc.clear(); leaf.clear(); roots.clear();
        lc.reserve(4 * n + 8); rc.reserve(4 * n + 8); leaf.reserve(4 * n + 8);
        lc.push_back(0); rc.push_back(0); leaf.push_back(0);  // 0 号空节点（本结构与 0 分开用）
        roots.push_back(build(0, n - 1));
    }
    int slot(int L, int R, int V) {
        lc.push_back(L); rc.push_back(R); leaf.push_back(V);
        return (int)leaf.size() - 1;
    }
    int build(int l, int r) {
        if (l == r) return slot(0, 0, 0);
        int mid = (l + r) >> 1;
        int L = build(l, mid);
        int R = build(mid + 1, r);
        return slot(L, R, 0);
    }
    int setRec(int prev, int l, int r, int pos, int v) {
        if (l == r) return slot(0, 0, v);
        int mid = (l + r) >> 1;
        if (pos <= mid) {
            int nl = setRec(lc[prev], l, mid, pos, v);
            return slot(nl, rc[prev], 0);      // 右子树整棵共享
        }
        int nr = setRec(rc[prev], mid + 1, r, pos, v);
        return slot(lc[prev], nr, 0);
    }
    // 基于 version 产生新版本，返回新版本号
    int set(int version, int pos, int v) {
        roots.push_back(setRec(roots[version], 0, n - 1, pos, v));
        return (int)roots.size() - 1;
    }
    int get(int version, int pos) const {
        int u = roots[version], l = 0, r = n - 1;
        while (l < r) {
            int mid = (l + r) >> 1;
            if (pos <= mid) { u = lc[u]; r = mid; } else { u = rc[u]; l = mid + 1; }
        }
        return leaf[u];
    }
    int nodeCount() const { return (int)leaf.size() - 1; }
    int versionCount() const { return (int)roots.size(); }
};

// ------------------------------------------------- Part 1 主席树（可持久化权值线段树）
// roots[i] = a[1..i] 这 i 个数插入后的权值线段树；区间 [l, r] 的信息 = roots[r] - roots[l-1]。
// 因为每次插入只走一条链，所以两棵树的差就是"区间内各值出现次数"。
struct PersistentKth {
    vector<int> lc, rc, cnt;
    vector<ll> sum;
    vector<int> roots;
    vector<int> vals;   // 压缩后的值域，rank -> 原值
    int m = 0;

    void init(const vector<int>& a) {
        vals = a;
        sort(vals.begin(), vals.end());
        vals.erase(unique(vals.begin(), vals.end()), vals.end());
        m = (int)vals.size();
        int n = (int)a.size();

        // 节点数上界：每个元素新增 (ceil(log2 m) + 1) 个节点
        int bits = 1;
        while ((1 << bits) < m) ++bits;
        long long cap = (long long)n * (bits + 2) + 16;
        lc.clear(); rc.clear(); cnt.clear(); sum.clear();
        lc.reserve((size_t)cap); rc.reserve((size_t)cap);
        cnt.reserve((size_t)cap); sum.reserve((size_t)cap);

        // 0 号节点是空节点，其左右儿子指向自己 —— 递归到底自然不会越界
        lc.push_back(0); rc.push_back(0); cnt.push_back(0); sum.push_back(0);

        roots.assign(n + 1, 0);
        for (int i = 1; i <= n; ++i) {
            int pos = (int)(lower_bound(vals.begin(), vals.end(), a[i - 1]) - vals.begin());
            roots[i] = update(roots[i - 1], 0, m - 1, pos, a[i - 1]);
        }
    }
    int newNode(int L, int R, int C, ll S) {
        lc.push_back(L); rc.push_back(R); cnt.push_back(C); sum.push_back(S);
        return (int)cnt.size() - 1;
    }
    // 路径复制：返回新根，旧版本的节点一个都不改
    int update(int prev, int l, int r, int pos, ll v) {
        if (l == r) return newNode(0, 0, cnt[prev] + 1, sum[prev] + v);
        int mid = (l + r) >> 1;
        if (pos <= mid) {
            int nl = update(lc[prev], l, mid, pos, v);
            return newNode(nl, rc[prev], cnt[prev] + 1, sum[prev] + v);
        }
        int nr = update(rc[prev], mid + 1, r, pos, v);
        return newNode(lc[prev], nr, cnt[prev] + 1, sum[prev] + v);
    }
    // 区间 [l, r]（1-indexed）第 k 小，k 从 1 开始
    int kth(int l, int r, int k) const {
        int u = roots[l - 1], v = roots[r];
        int lo = 0, hi = m - 1;
        while (lo < hi) {
            int mid = (lo + hi) >> 1;
            int cl = cnt[lc[v]] - cnt[lc[u]];
            if (k <= cl) { u = lc[u]; v = lc[v]; hi = mid; }
            else { k -= cl; u = rc[u]; v = rc[v]; lo = mid + 1; }
        }
        return vals[lo];
    }
    // 区间 [l, r] 内 <= x 的个数
    int countLe(int l, int r, int x) const {
        int need = (int)(upper_bound(vals.begin(), vals.end(), x) - vals.begin());  // 秩 < need
        if (need <= 0) return 0;
        int u = roots[l - 1], v = roots[r];
        if (need >= m) return cnt[v] - cnt[u];
        int res = 0, lo = 0, hi = m - 1;
        while (lo < hi) {
            int mid = (lo + hi) >> 1;
            if (need - 1 <= mid) { u = lc[u]; v = lc[v]; hi = mid; }
            else {
                res += cnt[lc[v]] - cnt[lc[u]];
                u = rc[u]; v = rc[v]; lo = mid + 1;
            }
        }
        res += cnt[v] - cnt[u];   // lo == need-1 的叶子
        return res;
    }
    // 区间 [l, r] 内秩 < need 的值的和
    ll sumLtRank(int u, int v, int need) const {
        if (need <= 0) return 0;
        if (need >= m) return sum[v] - sum[u];
        ll res = 0;
        int lo = 0, hi = m - 1;
        while (lo < hi) {
            int mid = (lo + hi) >> 1;
            if (need - 1 <= mid) { u = lc[u]; v = lc[v]; hi = mid; }
            else {
                res += sum[lc[v]] - sum[lc[u]];
                u = rc[u]; v = rc[v]; lo = mid + 1;
            }
        }
        res += sum[v] - sum[u];
        return res;
    }
    // 区间 [l, r] 内值落在 [a, b] 的元素之和
    ll sumBetween(int l, int r, int a, int b) const {
        int x = (int)(lower_bound(vals.begin(), vals.end(), a) - vals.begin());
        int y = (int)(upper_bound(vals.begin(), vals.end(), b) - vals.begin());  // 秩 < y
        if (y <= x) return 0;
        // 参数顺序必须是 (小版本, 大版本)：sumLtRank 内部按 sum[v] - sum[u] 取差
        ll hi = sumLtRank(roots[l - 1], roots[r], y);
        ll lo = sumLtRank(roots[l - 1], roots[r], x);
        return hi - lo;
    }
    int totalCount() const { return cnt[roots.back()]; }
    int nodeCount() const { return (int)cnt.size() - 1; }
    ll bytes() const {
        return (ll)cnt.size() * (ll)(sizeof(int) * 3 + sizeof(ll));
    }
};

// ------------------------------------------------- Part 2 小波矩阵
// 把值压缩成秩后按二进制位从高到低稳定划分：左半区 0、右半区 1。
// 每一层只存"1 的前缀个数"，于是层内 rank 是 O(1) 的两次减法。
// 复杂度与主席树同为 O(log σ)，但内存是 K*(n+1) 个 int，且全部连续访问。
struct WaveletMatrix {
    int n = 0, K = 0, m = 0;
    vector<int> pref;     // pref[lvl*(n+1) + i] = 第 lvl 层前 i 个位置中 1 的个数
    vector<int> zeroCnt;  // 每层 0 的总数（右半区的起始偏移）
    vector<int> vals;     // 秩 -> 原值

    void init(const vector<int>& a) {
        vals = a;
        sort(vals.begin(), vals.end());
        vals.erase(unique(vals.begin(), vals.end()), vals.end());
        m = (int)vals.size();
        n = (int)a.size();
        K = 1;
        while ((1 << K) < m) ++K;

        pref.assign((size_t)K * (size_t)(n + 1), 0);
        zeroCnt.assign(K, 0);

        vector<int> cur((size_t)n), nxt((size_t)n);
        for (int i = 0; i < n; ++i)
            cur[(size_t)i] = (int)(lower_bound(vals.begin(), vals.end(), a[(size_t)i]) - vals.begin());

        for (int lvl = 0; lvl < K; ++lvl) {
            int d = K - 1 - lvl;
            size_t base = (size_t)lvl * (size_t)(n + 1);
            int zc = 0;
            for (int i = 0; i < n; ++i) if (((cur[(size_t)i] >> d) & 1) == 0) ++zc;
            zeroCnt[lvl] = zc;
            pref[base] = 0;
            int zo = 0, oo = 0;
            for (int i = 0; i < n; ++i) {
                int b = (cur[(size_t)i] >> d) & 1;
                pref[base + (size_t)i + 1] = pref[base + (size_t)i] + b;
                if (!b) nxt[(size_t)zo++] = cur[(size_t)i];
                else nxt[(size_t)(zc + oo++)] = cur[(size_t)i];
            }
            cur.swap(nxt);
        }
    }
    // 区间 [l, r]（1-indexed）第 k 小
    int kth(int l, int r, int k) const {
        int L = l - 1, R = r;   // 半开区间 [L, R)
        int val = 0;
        for (int lvl = 0; lvl < K; ++lvl) {
            size_t base = (size_t)lvl * (size_t)(n + 1);
            int oL = pref[base + (size_t)L], oR = pref[base + (size_t)R];
            int zL = L - oL, zR = R - oR;
            int zc = zR - zL;
            if (k <= zc) { L = zL; R = zR; val <<= 1; }
            else { k -= zc; L = zeroCnt[lvl] + oL; R = zeroCnt[lvl] + oR; val = (val << 1) | 1; }
        }
        return vals[(size_t)val];
    }
    // 区间内秩 < need 的个数
    int countLtRank(int l, int r, int need) const {
        int L = l - 1, R = r;
        if (need <= 0 || L >= R) return 0;
        int res = 0;
        for (int lvl = 0; lvl < K; ++lvl) {
            int d = K - 1 - lvl;
            size_t base = (size_t)lvl * (size_t)(n + 1);
            int oL = pref[base + (size_t)L], oR = pref[base + (size_t)R];
            int zL = L - oL, zR = R - oR;
            if ((need >> d) & 1) {
                res += zR - zL;                       // 这一位为 0 的全部更小
                L = zeroCnt[lvl] + oL;
                R = zeroCnt[lvl] + oR;
            } else {
                L = zL; R = zR;
            }
            if (L >= R) break;
        }
        return res;
    }
    int countLe(int l, int r, int x) const {
        int need = (int)(upper_bound(vals.begin(), vals.end(), x) - vals.begin());
        return countLtRank(l, r, need);
    }
    ll bytes() const { return (ll)pref.size() * (ll)sizeof(int) + (ll)vals.size() * (ll)sizeof(int); }
};

// ------------------------------------------------- Part 3 归并树（慢对照）
// 线段树每个节点存排好序的区间；countLe 走 O(log n) 个节点各一次二分 = O(log² n)。
// 第 k 小要在值域上二分 → 总共 O(log V · log² n)。思路直白，代价明显。
struct MergeSortTree {
    int n = 0;
    vector<vector<int>> t;
    vector<int> vals;

    void init(const vector<int>& a) {
        vals = a;
        sort(vals.begin(), vals.end());
        vals.erase(unique(vals.begin(), vals.end()), vals.end());
        n = (int)a.size();
        t.assign((size_t)(4 * max(n, 1)), vector<int>());
        if (n) build(1, 0, n - 1, a);
    }
    void build(int p, int l, int r, const vector<int>& a) {
        if (l == r) { t[(size_t)p].assign(1, a[(size_t)l]); return; }
        int mid = (l + r) >> 1;
        build(p << 1, l, mid, a);
        build((p << 1) | 1, mid + 1, r, a);
        const vector<int>& L = t[(size_t)(p << 1)];
        const vector<int>& R = t[(size_t)((p << 1) | 1)];
        t[(size_t)p].resize(L.size() + R.size());
        merge(L.begin(), L.end(), R.begin(), R.end(), t[(size_t)p].begin());
    }
    int countRec(int p, int l, int r, int ql, int qr, int x) const {
        if (qr < l || r < ql) return 0;
        if (ql <= l && r <= qr) {
            const vector<int>& v = t[(size_t)p];
            return (int)(upper_bound(v.begin(), v.end(), x) - v.begin());
        }
        int mid = (l + r) >> 1;
        return countRec(p << 1, l, mid, ql, qr, x) + countRec((p << 1) | 1, mid + 1, r, ql, qr, x);
    }
    int countLe(int l, int r, int x) const { return countRec(1, 0, n - 1, l - 1, r - 1, x); }
    int kth(int l, int r, int k) const {
        int lo = 0, hi = (int)vals.size() - 1;
        while (lo < hi) {
            int mid = (lo + hi) >> 1;
            if (countLe(l, r, vals[(size_t)mid]) >= k) hi = mid; else lo = mid + 1;
        }
        return vals[(size_t)lo];
    }
    ll bytes() const {
        ll s = 0;
        for (size_t i = 0; i < t.size(); ++i) s += (ll)t[i].capacity() * (ll)sizeof(int);
        return s + (ll)t.size() * (ll)sizeof(vector<int>) + (ll)vals.size() * (ll)sizeof(int);
    }
};

// ------------------------------------------------- Part 4 暴力 oracle
struct Brute {
    vector<int> a;
    void init(const vector<int>& v) { a = v; }
    int kth(int l, int r, int k) const {
        vector<int> t(a.begin() + (l - 1), a.begin() + r);
        nth_element(t.begin(), t.begin() + (k - 1), t.end());
        return t[(size_t)(k - 1)];
    }
    int countLe(int l, int r, int x) const {
        int c = 0;
        for (int i = l - 1; i < r; ++i) if (a[(size_t)i] <= x) ++c;
        return c;
    }
    ll sumBetween(int l, int r, int lo, int hi) const {
        ll s = 0;
        for (int i = l - 1; i < r; ++i) {
            int v = a[(size_t)i];
            if (v >= lo && v <= hi) s += v;
        }
        return s;
    }
};

// 小工具：随机 (l, r, k)
struct Query { int l, r, k; };

static vector<Query> makeQueries(int n, int q, Rng& rng) {
    vector<Query> out;
    out.reserve((size_t)q);
    for (int i = 0; i < q; ++i) {
        int l = rng.nextInt(1, n);
        int r = rng.nextInt(1, n);
        if (l > r) swap(l, r);
        int k = rng.nextInt(1, r - l + 1);
        out.push_back(Query{l, r, k});
    }
    return out;
}

// ------------------------------------------------- G1 随机对拍
static void group1() {
    printf("[G1] 随机对拍：n=60 / 1000 次 kth + 1000 次 countLe + 400 次值域求和（四方一致）\n");
    Rng rng(20261101ULL);
    int n = 60;
    vector<int> a((size_t)n);
    for (int i = 0; i < n; ++i) a[(size_t)i] = rng.nextInt(0, 200);

    PersistentKth ps; ps.init(a);
    WaveletMatrix wm; wm.init(a);
    MergeSortTree mst; mst.init(a);
    Brute br; br.init(a);

    vector<Query> qs = makeQueries(n, 1000, rng);
    for (size_t i = 0; i < qs.size(); ++i) {
        const Query& q = qs[i];
        int b = br.kth(q.l, q.r, q.k);
        int p = ps.kth(q.l, q.r, q.k);
        int w = wm.kth(q.l, q.r, q.k);
        int g = mst.kth(q.l, q.r, q.k);
        CHECK(p == b, "G1 主席树 kth 与暴力不符");
        CHECK(w == b, "G1 小波矩阵 kth 与暴力不符");
        CHECK(g == b, "G1 归并树 kth 与暴力不符");
        int x = rng.nextInt(-10, 220);
        int cb = br.countLe(q.l, q.r, x);
        CHECK(ps.countLe(q.l, q.r, x) == cb, "G1 主席树 countLe 与暴力不符");
        CHECK(wm.countLe(q.l, q.r, x) == cb, "G1 小波矩阵 countLe 与暴力不符");
        CHECK(mst.countLe(q.l, q.r, x) == cb, "G1 归并树 countLe 与暴力不符");
    }
    for (int i = 0; i < 400; ++i) {
        const Query& q = qs[(size_t)i];
        int lo = rng.nextInt(-20, 220);
        int hi = lo + rng.nextInt(0, 260);
        CHECK(ps.sumBetween(q.l, q.r, lo, hi) == br.sumBetween(q.l, q.r, lo, hi),
              "G1 主席树 sumBetween 与暴力不符");
    }
    printf("    检查点 %d，失败 %d\n", g_checks, g_fail);
}

// ------------------------------------------------- G2 边界
static void group2() {
    printf("[G2] 边界：n=1 / 全等 / 全负 / k=1 与 k=len / x 越界 / 单点区间\n");
    int before = g_fail;
    {
        vector<int> a(1, 42);
        PersistentKth ps; ps.init(a);
        WaveletMatrix wm; wm.init(a);
        MergeSortTree mst; mst.init(a);
        CHECK(ps.kth(1, 1, 1) == 42, "G2 n=1 主席树 kth");
        CHECK(wm.kth(1, 1, 1) == 42, "G2 n=1 小波矩阵 kth");
        CHECK(mst.kth(1, 1, 1) == 42, "G2 n=1 归并树 kth");
        CHECK(ps.countLe(1, 1, 41) == 0, "G2 n=1 countLe(小于)");
        CHECK(wm.countLe(1, 1, 41) == 0, "G2 n=1 小波 countLe(小于)");
        CHECK(ps.countLe(1, 1, 42) == 1, "G2 n=1 countLe(相等)");
        CHECK(wm.countLe(1, 1, 42) == 1, "G2 n=1 小波 countLe(相等)");
        CHECK(ps.countLe(1, 1, 1 << 30) == 1, "G2 n=1 countLe(大于最大值)");
        CHECK(wm.countLe(1, 1, 1 << 30) == 1, "G2 n=1 小波 countLe(大于最大值)");
        CHECK(ps.sumBetween(1, 1, 0, 100) == 42, "G2 n=1 值域求和");
        CHECK(ps.sumBetween(1, 1, 43, 100) == 0, "G2 n=1 值域求和(空交集)");
    }
    {
        int n = 50;
        vector<int> a((size_t)n, 7);   // 全等
        PersistentKth ps; ps.init(a);
        WaveletMatrix wm; wm.init(a);
        MergeSortTree mst; mst.init(a);
        const Query q{1, n, 1};
        CHECK(ps.kth(q.l, q.r, q.k) == 7, "G2 全等 主席树 k=1");
        CHECK(wm.kth(q.l, q.r, q.k) == 7, "G2 全等 小波 k=1");
        CHECK(mst.kth(q.l, q.r, q.k) == 7, "G2 全等 归并树 k=1");
        CHECK(ps.kth(1, n, n) == 7, "G2 全等 主席树 k=n");
        CHECK(wm.kth(1, n, n) == 7, "G2 全等 小波 k=n");
        CHECK(ps.countLe(1, n, 6) == 0, "G2 全等 countLe(小于)");
        CHECK(wm.countLe(1, n, 6) == 0, "G2 全等 小波 countLe(小于)");
        CHECK(ps.countLe(1, n, 7) == n, "G2 全等 countLe(等于)");
        CHECK(wm.countLe(1, n, 7) == n, "G2 全等 小波 countLe(等于)");
        CHECK(ps.sumBetween(1, n, 0, 100) == (ll)7 * n, "G2 全等 值域求和");
    }
    {
        Rng rng(777ULL);
        int n = 80;
        vector<int> a((size_t)n);
        for (int i = 0; i < n; ++i) a[(size_t)i] = -rng.nextInt(1, 1000);   // 全负
        PersistentKth ps; ps.init(a);
        WaveletMatrix wm; wm.init(a);
        Brute br; br.init(a);
        vector<Query> qs = makeQueries(n, 500, rng);
        for (size_t i = 0; i < qs.size(); ++i) {
            const Query& q = qs[i];
            int b = br.kth(q.l, q.r, q.k);
            CHECK(ps.kth(q.l, q.r, q.k) == b, "G2 全负 主席树 kth");
            CHECK(wm.kth(q.l, q.r, q.k) == b, "G2 全负 小波 kth");
            int x = -rng.nextInt(1, 1200);
            CHECK(ps.countLe(q.l, q.r, x) == br.countLe(q.l, q.r, x), "G2 全负 主席树 countLe");
            CHECK(wm.countLe(q.l, q.r, x) == br.countLe(q.l, q.r, x), "G2 全负 小波 countLe");
        }
    }
    printf("    检查点 %d，失败 %d（本组失败 %d）\n", g_checks, g_fail, g_fail - before);
}

// ------------------------------------------------- G3 结构不变式
static void group3() {
    printf("[G3] 结构不变式：cnt[roots[i]]==i、sum 与前缀和一致、节点数上界、版本隔离\n");
    int before = g_fail;
    Rng rng(31415ULL);
    int n = 300;
    vector<int> a((size_t)n);
    for (int i = 0; i < n; ++i) a[(size_t)i] = rng.nextInt(0, 5000);

    PersistentKth ps; ps.init(a);
    ll pref = 0;
    bool cntOk = true, sumOk = true;
    for (int i = 1; i <= n; ++i) {
        pref += a[(size_t)(i - 1)];
        if (ps.cnt[ps.roots[i]] != i) cntOk = false;
        // 整区间求和（值域全覆盖）
        if (ps.sumBetween(1, i, INT_MIN, INT_MAX) != pref) sumOk = false;
    }
    CHECK(cntOk, "G3 前缀版本 cnt 不等于前缀长度");
    CHECK(sumOk, "G3 前缀版本 sum 与朴素前缀和不一致");
    CHECK(ps.totalCount() == n, "G3 全量 cnt 应等于 n");

    int bits = 1;
    while ((1 << bits) < ps.m) ++bits;
    ll bound = (ll)n * (bits + 1) + 1;
    CHECK((ll)ps.nodeCount() <= bound, "G3 主席树节点数超过 n*(log2(m)+1)+1");
    printf("    主席树节点 %d（上界 %lld，实际/上界 %.3f）\n",
           ps.nodeCount(), bound, (double)ps.nodeCount() / (double)bound);

    // 小波矩阵：所有层长度守恒（每层 0 的个数 + 1 的个数 == n）
    WaveletMatrix wm; wm.init(a);
    bool wmOk = true;
    for (int lvl = 0; lvl < wm.K; ++lvl) {
        size_t base = (size_t)lvl * (size_t)(n + 1);
        int ones = wm.pref[base + (size_t)n];
        if (wm.zeroCnt[lvl] + ones != n) wmOk = false;
    }
    CHECK(wmOk, "G3 小波矩阵层内元素数不守恒");
    printf("    小波矩阵层数 K=%d，内存 %.2f MB；主席树内存 %.2f MB\n",
           wm.K, (double)wm.bytes() / 1048576.0, (double)ps.bytes() / 1048576.0);
    printf("    本组失败 %d\n", g_fail - before);
}

// ------------------------------------------------- G4 可持久化数组
static void group4() {
    printf("[G4] 可持久化数组：200 次版本更新后，历史版本逐点比对（不可变性）\n");
    int before = g_fail;
    Rng rng(2718ULL);
    int n = 20;
    PersistArray pa; pa.init(n);
    vector<vector<int>> snap;            // 暴力：每个版本一份副本
    snap.push_back(vector<int>((size_t)n, 0));

    for (int step = 0; step < 200; ++step) {
        int ver = rng.nextInt(0, (int)snap.size() - 1);   // 任意历史版本上派生
        int pos = rng.nextInt(0, n - 1);
        int v = rng.nextInt(-1000, 1000);
        vector<int> nv = snap[(size_t)ver];
        nv[(size_t)pos] = v;
        snap.push_back(nv);
        int got = pa.set(ver, pos, v);
        CHECK(got == (int)snap.size() - 1, "G4 版本号不连续");
    }
    CHECK(pa.versionCount() == (int)snap.size(), "G4 版本数不符");

    bool same = true;
    for (size_t v = 0; v < snap.size(); ++v)
        for (int p = 0; p < n; ++p)
            if (pa.get((int)v, p) != snap[v][(size_t)p]) same = false;
    CHECK(same, "G4 历史版本内容被后续更新污染");
    printf("    版本数 %d，节点 %d，每版本平均新增 %.2f 个节点\n",
           pa.versionCount(), pa.nodeCount(),
           (double)pa.nodeCount() / (double)pa.versionCount());
    printf("    本组失败 %d\n", g_fail - before);
}

// ------------------------------------------------- G5 版本共享的实测
// 权值树建在 [0, m-1] 上；m 不是 2 的幂时，左右两段的叶子深度会差 1，
// 所以"每次新增节点数"不是常数，而是 深度(pos)+1 ∈ {⌈log2 m⌉, ⌈log2 m⌉+1}。
static int rankDepth(int pos, int m) {
    int l = 0, r = m - 1, d = 0;
    while (l < r) {
        int mid = (l + r) >> 1;
        ++d;
        if (pos <= mid) r = mid; else l = mid + 1;
    }
    return d;
}

static void group5() {
    printf("[G5] 版本共享实证：总节点数 == 逐元素累加 (深度+1)\n");
    int before = g_fail;
    int n = 1000;
    vector<int> a((size_t)n);
    Rng rng(999ULL);
    for (int i = 0; i < n; ++i) a[(size_t)i] = rng.nextInt(0, 1000000000);

    PersistentKth ps; ps.init(a);
    int bits = 1;
    while ((1 << bits) < ps.m) ++bits;
    long long expect = 0;
    int dmin = 1 << 30, dmax = 0;
    for (int i = 0; i < n; ++i) {
        int pos = (int)(lower_bound(ps.vals.begin(), ps.vals.end(), a[(size_t)i]) - ps.vals.begin());
        int d = rankDepth(pos, ps.m);
        expect += d + 1;
        if (d < dmin) dmin = d;
        if (d > dmax) dmax = d;
    }
    long long total = ps.nodeCount();
    CHECK(total == expect, "G5 总节点数与独立推算不符");
    printf("    m=%d（非 2 的幂，位数 %d），叶子深度 %d..%d，故每次插入新增 %d..%d 个节点\n",
           ps.m, bits, dmin, dmax, dmin + 1, dmax + 1);
    printf("    总节点 %lld，独立推算 %lld（逐元素累加 深度+1），平均每版本 %.2f 个\n",
           total, expect, (double)total / (double)n);
    if (total > 0) {
        printf("    共享比例 1 - %.1f/%lld ≈ %.4f\n", (double)total / (double)n, total,
               1.0 - ((double)total / (double)n) / (double)total);
    } else {
        CHECK(false, "G5 节点总数为 0（权值树没有建起来）");
    }

    // 对照组：m 恰为 2 的幂时，每次插入严格新增 bits+1 个节点
    int n2 = 1024;
    vector<int> a2((size_t)n2);
    for (int i = 0; i < n2; ++i) a2[(size_t)i] = i;
    Rng r2(4242ULL);
    for (int i = n2 - 1; i > 0; --i) {
        int j = r2.nextInt(0, i);
        swap(a2[(size_t)i], a2[(size_t)j]);
    }
    PersistentKth ps2; ps2.init(a2);
    if (ps2.m == n2) {
        CHECK((long long)ps2.nodeCount() == (long long)n2 * 11, "G5 m=1024 时节点数应为 1024*11");
        printf("    对照组 m=1024：每次严格新增 11 个节点，总 %d = %d × 11\n",
               ps2.nodeCount(), n2);
    } else {
        printf("    对照组 m=%d（未凑成 1024，跳过严格等式检查）\n", ps2.m);
    }

    WaveletMatrix wm; wm.init(a);
    printf("    小波矩阵 %d 层 × %d = %d 个 int，主席树 %lld 节点 × 20B\n",
           wm.K, n + 1, wm.K * (n + 1), total);
    printf("    本组失败 %d\n", g_fail - before);
}

// ------------------------------------------------- 基准
static void benchmark() {
    printf("\n========== 基准（n=200000, q=100000）==========\n");
    const int n = 200000;
    const int q = 100000;
    Rng rng(0xABCDEF12345ULL);
    vector<int> a((size_t)n);
    for (int i = 0; i < n; ++i) a[(size_t)i] = rng.nextInt(0, 999999999);
    vector<Query> qs = makeQueries(n, q, rng);
    vector<int> xs((size_t)q);
    for (int i = 0; i < q; ++i) xs[(size_t)i] = rng.nextInt(0, 999999999);

    double t0 = nowMs();
    PersistentKth ps; ps.init(a);
    double t1 = nowMs();
    WaveletMatrix wm; wm.init(a);
    double t2 = nowMs();
    MergeSortTree mst; mst.init(a);
    double t3 = nowMs();

    printf("建树：主席树 %.1f ms（%d 节点，%.1f MB）\n", t1 - t0, ps.nodeCount(),
           (double)ps.bytes() / 1048576.0);
    printf("      小波矩阵 %.1f ms（K=%d，%.1f MB）\n", t2 - t1, wm.K,
           (double)wm.bytes() / 1048576.0);
    printf("      归并树 %.1f ms（%.1f MB）\n", t3 - t2, (double)mst.bytes() / 1048576.0);
    printf("      主席树/小波矩阵 内存比 %.2fx\n",
           (double)ps.bytes() / (double)wm.bytes());

    // --- kth 查询
    ll sp = 0, sw = 0;
    double a0 = nowMs();
    for (int i = 0; i < q; ++i) sp += ps.kth(qs[(size_t)i].l, qs[(size_t)i].r, qs[(size_t)i].k);
    double a1 = nowMs();
    for (int i = 0; i < q; ++i) sw += wm.kth(qs[(size_t)i].l, qs[(size_t)i].r, qs[(size_t)i].k);
    double a2 = nowMs();
    bool sameKth = (sp == sw);
    printf("kth   ：主席树 %.1f ms   小波矩阵 %.1f ms   校验和 %s\n", a1 - a0, a2 - a1,
           sameKth ? "一致" : "不一致");
    CHECK(sameKth, "基准 kth 两侧校验和不一致");

    // --- countLe 查询
    ll cp = 0, cw = 0;
    double b0 = nowMs();
    for (int i = 0; i < q; ++i) cp += ps.countLe(qs[(size_t)i].l, qs[(size_t)i].r, xs[(size_t)i]);
    double b1 = nowMs();
    for (int i = 0; i < q; ++i) cw += wm.countLe(qs[(size_t)i].l, qs[(size_t)i].r, xs[(size_t)i]);
    double b2 = nowMs();
    bool sameLe = (cp == cw);
    printf("countLe：主席树 %.1f ms  小波矩阵 %.1f ms   校验和 %s\n", b1 - b0, b2 - b1,
           sameLe ? "一致" : "不一致");
    CHECK(sameLe, "基准 countLe 两侧校验和不一致");

    // --- 归并树（只跑 2000 个，慢对照）
    const int q2 = 2000;
    ll sm = 0;
    double c0 = nowMs();
    for (int i = 0; i < q2; ++i) sm += mst.kth(qs[(size_t)i].l, qs[(size_t)i].r, qs[(size_t)i].k);
    double c1 = nowMs();
    ll ref = 0;
    for (int i = 0; i < q2; ++i) ref += ps.kth(qs[(size_t)i].l, qs[(size_t)i].r, qs[(size_t)i].k);
    bool sameMst = (sm == ref);
    printf("归并树 kth：%d 次 %.1f ms（每次 %.1f us）  校验和 %s\n", q2, c1 - c0,
           (c1 - c0) * 1000.0 / (double)q2, sameMst ? "一致" : "不一致");
    CHECK(sameMst, "基准归并树校验和不一致");

    double perP = (a1 - a0) * 1000.0 / (double)q;
    double perW = (a2 - a1) * 1000.0 / (double)q;
    printf("单次 kth：主席树 %.3f us，小波矩阵 %.3f us，比值 %.2fx\n", perP, perW, perP / perW);
    printf("总检查点 %d，失败 %d\n", g_checks, g_fail);
}

int main() {
    printf("========== 0012 可持久化线段树（主席树）/ 小波矩阵 ==========\n");
    double t0 = nowMs();
    group1();
    group2();
    group3();
    group4();
    group5();
    benchmark();
    double t1 = nowMs();
    printf("\n全部验证 %s（检查点 %d，失败 %d，耗时 %.1f ms）\n",
           g_fail == 0 ? "通过" : "失败", g_checks, g_fail, t1 - t0);
    return g_fail == 0 ? 0 : 1;
}
