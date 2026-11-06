// ============================================================
// 0011 · 树链剖分 (Heavy-Light Decomposition, HLD)
// ------------------------------------------------------------
// 四个部分:
//   A. SegTree  区间加 + 区间和 + 区间最值(懒标记), 作为"链序列"底层容器
//   B. HLD      重儿子划分 + dfn 序: 树上"路径" <-> O(log n) 段连续区间
//               路径加 / 路径和 / 路径最值 / 子树加 / 子树和 / 子树最值
//               LCA, ancestorAt(倍增上跳), 换根子树和(补集思想)
//               —— 建树全程迭代, 无递归, n=2e5 不爆栈; 邻接表用 CSR 连续存储
//   C. BinLift  倍增 LCA + 根前缀和: 静态路径和 O(log n) 的对照实现
//               与 HLD 对比"静态 vs 动态"的适用边界
//   D. Brute    逐点爬树的暴力参考: 路径 O(路径长), 子树 O(n·depth)
//
// 正确性:
//   G1 随机树 3000 次混合操作 vs 暴力 + dfn 子树连续性不变式
//   G2 四种树形(链/菊花/完全二叉树/随机) 各 1200 次路径操作
//   G3 静态路径和 三方对拍(HLD / 倍增 / 暴力)
//   G4 边界: n=1, n=2, 换根建树(root 非 0), u==v, 根为叶
//   G5 跳链次数实证: 链=0, 菊花=2, 二叉树/随机树 O(log n)
//   G6 换根子树和 vs 暴力(每个查询重跑一次 BFS 定根)
//
// 编译:   g++ -O2 -std=c++17 -Wall -Wextra 0011_hld.cpp -o 0011
// 注意:   本期源码未在本机编译(环境无 C++ 编译器); 逻辑经 Python 逐行镜像
//         (.verify_mirror_0011.py) 随机对拍验证, 详见 0011_hld.md
// ============================================================
#include <bits/stdc++.h>
using namespace std;

static int g_fail = 0;

#define CHECK(cond, ...)                       \
    do {                                       \
        if (!(cond)) {                         \
            printf("    [FAIL] " __VA_ARGS__); \
            printf("\n");                      \
            ++g_fail;                          \
        }                                      \
    } while (0)

// ============================================================
// 确定性伪随机(xorshift64): 每组用例开头重置种子,
// 使 C++ 与 Python 镜像产生完全相同的操作序列
// ============================================================
static uint64_t g_seed = 0x9E3779B97F4A7C15ULL;
static inline uint64_t xr64() {
    g_seed ^= g_seed << 13;
    g_seed ^= g_seed >> 7;
    g_seed ^= g_seed << 17;
    return g_seed;
}
static inline uint32_t xr32() { return (uint32_t)(xr64() >> 33); }
static void reseed(uint64_t s) { g_seed = s; }

static void report(const char* name, int base) {
    printf("  => %s: %s\n", name, g_fail == base ? "PASS" : "FAIL");
}

// ============================================================
// A. SegTree —— 区间加 / 区间和 / 区间最值 (懒标记)
//
// 与 0002 的设计一致, 但接口按 HLD 的需要收窄:
// 只有 rangeAdd / rangeSum / rangeMax 三个公开操作,
// 全部作用于 **dfn 下标**, 与树上节点通过 rnk[] 双向映射。
// ============================================================
class SegTree {
public:
    int n = 0;
    vector<long long> sum, mx, lz, base;

    void init(const vector<long long>& a) {
        n = (int)a.size();
        base = a;
        sum.assign(4 * n + 4, 0);
        mx.assign(4 * n + 4, 0);
        lz.assign(4 * n + 4, 0);
        if (n > 0) build(1, 0, n - 1);
    }

    void pull(int p) {
        sum[p] = sum[p << 1] + sum[p << 1 | 1];
        mx[p] = max(mx[p << 1], mx[p << 1 | 1]);
    }

    // 整段打标记: 和 += d*len, 最值 += d, 懒标记 += d
    void tag(int p, int l, int r, long long d) {
        sum[p] += d * (long long)(r - l + 1);
        mx[p] += d;
        lz[p] += d;
    }

    void build(int p, int l, int r) {
        lz[p] = 0;
        if (l == r) { sum[p] = mx[p] = base[l]; return; }
        int m = (l + r) >> 1;
        build(p << 1, l, m);
        build(p << 1 | 1, m + 1, r);
        pull(p);
    }

    void push(int p, int l, int r) {
        if (lz[p] != 0 && l < r) {
            int m = (l + r) >> 1;
            tag(p << 1, l, m, lz[p]);
            tag(p << 1 | 1, m + 1, r, lz[p]);
        }
        lz[p] = 0;
    }

    void add(int p, int l, int r, int ql, int qr, long long d) {
        if (ql <= l && r <= qr) { tag(p, l, r, d); return; }
        push(p, l, r);
        int m = (l + r) >> 1;
        if (ql <= m) add(p << 1, l, m, ql, qr, d);
        if (qr > m) add(p << 1 | 1, m + 1, r, ql, qr, d);
        pull(p);
    }

    long long qsumImpl(int p, int l, int r, int ql, int qr) {
        // 查询路径上的节点必须下推: 父节点的 lz 只代表"整段被加过",
        // 子节点的 sum/mx 尚未包含它, 不下推会读到陈旧值
        if (ql <= l && r <= qr) return sum[p];
        push(p, l, r);
        int m = (l + r) >> 1;
        long long res = 0;
        if (ql <= m) res += qsumImpl(p << 1, l, m, ql, qr);
        if (qr > m) res += qsumImpl(p << 1 | 1, m + 1, r, ql, qr);
        return res;
    }

    long long qmaxImpl(int p, int l, int r, int ql, int qr) {
        if (ql <= l && r <= qr) return mx[p];
        push(p, l, r);
        int m = (l + r) >> 1;
        long long res = LLONG_MIN;
        if (ql <= m) res = max(res, qmaxImpl(p << 1, l, m, ql, qr));
        if (qr > m) res = max(res, qmaxImpl(p << 1 | 1, m + 1, r, ql, qr));
        return res;
    }

    // ---- 公开接口(dfn 闭区间 [l, r]) ----
    void rangeAdd(int l, int r, long long d) {
        if (l > r || n == 0) return;
        add(1, 0, n - 1, l, r, d);
    }
    long long rangeSum(int l, int r) {
        if (l > r || n == 0) return 0;
        return qsumImpl(1, 0, n - 1, l, r);
    }
    long long rangeMax(int l, int r) {
        if (l > r || n == 0) return LLONG_MIN;
        return qmaxImpl(1, 0, n - 1, l, r);
    }
};

// ============================================================
// B. HLD —— 树链剖分
//
// 核心不变式(整个结构只依赖这三条):
//   (1) 每个节点 u 的子树在 dfn 序上恰为连续区间 [dfn[u], dfn[u]+sz[u]-1]
//   (2) 每条重链在 dfn 序上连续, 且链上深度越大 dfn 越大
//   (3) 从任意节点上跳到根, 经过的重链数 <= O(log n)  (轻边至少减半)
// 有 (1)(2) 之后, 树上路径操作 = 把路径切成 O(log n) 段区间操作;
// 有 (3) 这个切分可以"边跳边做", 不需要预先求出全部段。
// ============================================================
class HLD {
public:
    int n = 0, rt = 0;
    vector<int> par, dep, sz, heavy, top, dfn, rnk;
    vector<int> estart, eto;   // CSR 邻接表
    SegTree seg;
    long long jumpCnt = 0;     // 路径查询累计跳链次数(供 G5 实证)

    HLD(int n_, const vector<int>& eu, const vector<int>& ev, int root_,
        const vector<long long>& val) {
        n = n_;
        rt = root_;
        buildCsr(eu, ev);
        buildDfs(val);
        vector<long long> base(n);
        for (int i = 0; i < n; ++i) base[dfn[i]] = val[i];
        seg.init(base);
    }

    // ---- CSR 邻接表: 度计数 -> 前缀和 -> 填充 ----
    // 相比 vector<vector<int>> 少了 n 次小分配, 遍历时访存连续
    void buildCsr(const vector<int>& eu, const vector<int>& ev) {
        vector<int> deg(n, 0);
        for (size_t i = 0; i < eu.size(); ++i) { ++deg[eu[i]]; ++deg[ev[i]]; }
        estart.assign(n + 1, 0);
        for (int i = 0; i < n; ++i) estart[i + 1] = estart[i] + deg[i];
        eto.assign(estart[n], 0);
        vector<int> pos(estart.begin(), estart.end() - 1);
        for (size_t i = 0; i < eu.size(); ++i) {
            int a = eu[i], b = ev[i];
            eto[pos[a]++] = b;
            eto[pos[b]++] = a;
        }
    }

    void buildDfs(const vector<long long>&) {
        par.assign(n, -1);
        dep.assign(n, 0);
        sz.assign(n, 1);
        heavy.assign(n, -1);
        top.assign(n, -1);
        dfn.assign(n, -1);
        rnk.assign(n, -1);

        // ---- 第一次遍历(迭代 BFS 定序): 求 par / dep / 遍历序 ----
        // 用 order 数组当队列, 避免 std::queue 的额外分配
        vector<int> order;
        order.reserve(n);
        order.push_back(rt);
        par[rt] = -1;
        dep[rt] = 0;
        for (size_t i = 0; i < order.size(); ++i) {
            int u = order[i];
            for (int k = estart[u]; k < estart[u + 1]; ++k) {
                int w = eto[k];
                if (w == par[u]) continue;
                par[w] = u;
                dep[w] = dep[u] + 1;
                order.push_back(w);
            }
        }

        // ---- 逆序求 sz / 重儿子(子树大小最大的儿子) ----
        // 用 order.size() 而不是 n 作下界: 图不连通时也不会越界读
        for (int i = (int)order.size() - 1; i >= 0; --i) {
            int u = order[i];
            sz[u] = 1;
            int best = -1, bs = 0;
            for (int k = estart[u]; k < estart[u + 1]; ++k) {
                int w = eto[k];
                if (par[w] != u) continue;
                sz[u] += sz[w];
                if (sz[w] > bs) { bs = sz[w]; best = w; }
            }
            heavy[u] = best;
        }

        // ---- 第二次遍历: 沿重链连续编号, 轻儿子各自开新链 ----
        // 注意栈是 LIFO, 轻重儿子的相对顺序被反转, 但子树连续性不受影响
        vector<int> stk;
        stk.push_back(rt);
        int cur = 0;
        while (!stk.empty()) {
            int v = stk.back();
            stk.pop_back();
            for (int u = v; u != -1; u = heavy[u]) {
                top[u] = v;
                dfn[u] = cur;
                rnk[cur] = u;
                ++cur;
                for (int k = estart[u]; k < estart[u + 1]; ++k) {
                    int w = eto[k];
                    if (par[w] == u && w != heavy[u]) stk.push_back(w);
                }
            }
        }
        // 建树完整性: 每个节点恰好被编号一次
        int missing = 0;
        for (int i = 0; i < n; ++i) if (dfn[i] < 0) ++missing;
        if (missing) printf("    [WARN] %d 个节点未被编号(非连通图?)\n", missing);
    }

    // ---------------- 路径操作 ----------------
    void pathAdd(int u, int v, long long d) {
        while (top[u] != top[v]) {
            if (dep[top[u]] < dep[top[v]]) swap(u, v);
            seg.rangeAdd(dfn[top[u]], dfn[u], d);
            u = par[top[u]];
        }
        if (dep[u] > dep[v]) swap(u, v);
        seg.rangeAdd(dfn[u], dfn[v], d);
    }

    long long pathSum(int u, int v) {
        long long res = 0;
        while (top[u] != top[v]) {
            if (dep[top[u]] < dep[top[v]]) swap(u, v);
            res += seg.rangeSum(dfn[top[u]], dfn[u]);
            ++jumpCnt;
            u = par[top[u]];
        }
        if (dep[u] > dep[v]) swap(u, v);
        res += seg.rangeSum(dfn[u], dfn[v]);
        return res;
    }

    long long pathMax(int u, int v) {
        long long res = LLONG_MIN;
        while (top[u] != top[v]) {
            if (dep[top[u]] < dep[top[v]]) swap(u, v);
            res = max(res, seg.rangeMax(dfn[top[u]], dfn[u]));
            ++jumpCnt;
            u = par[top[u]];
        }
        if (dep[u] > dep[v]) swap(u, v);
        res = max(res, seg.rangeMax(dfn[u], dfn[v]));
        return res;
    }

    // ---------------- 子树操作 ----------------
    // 完全靠不变式(1): 子树 = 一段连续 dfn 区间
    void subtreeAdd(int u, long long d) { seg.rangeAdd(dfn[u], dfn[u] + sz[u] - 1, d); }
    long long subtreeSum(int u) { return seg.rangeSum(dfn[u], dfn[u] + sz[u] - 1); }
    long long subtreeMax(int u) { return seg.rangeMax(dfn[u], dfn[u] + sz[u] - 1); }

    // ---------------- LCA / 上跳 ----------------
    int lca(int u, int v) const {
        while (top[u] != top[v]) {
            if (dep[top[u]] < dep[top[v]]) swap(u, v);
            u = par[top[u]];
        }
        return dep[u] < dep[v] ? u : v;
    }

    // 求 x 的、深度恰为 targetDep 的祖先 (targetDep <= dep[x])
    // 同一条链内深度差 = dfn 差, 可直接定位; 否则整链跳上去
    int ancestorAt(int x, int targetDep) const {
        while (dep[top[x]] > targetDep) x = par[top[x]];
        return rnk[dfn[x] - (dep[x] - targetDep)];
    }

    bool isAncestor(int a, int b) const {
        return dfn[a] <= dfn[b] && dfn[b] < dfn[a] + sz[a];
    }

    // ---------------- 换根子树和 ----------------
    // 以 r 为根时, u 的子树有三种情形:
    //   1) u == r          -> 全树
    //   2) u 不是 r 的祖先 -> 与原树一致(区间 [dfn[u], dfn[u]+sz[u]-1])
    //   3) u 是 r 的真祖先 -> 全树 - (u 的"朝向 r 的那个儿子"的子树)
    // 情形 3 里那个儿子 = r 的深度为 dep[u]+1 的祖先, 用 ancestorAt 一次定位
    long long rerootSubtreeSum(int u, int r) {
        if (u == r) return seg.rangeSum(0, n - 1);
        if (!isAncestor(u, r)) return seg.rangeSum(dfn[u], dfn[u] + sz[u] - 1);
        int c = ancestorAt(r, dep[u] + 1);
        return seg.rangeSum(0, n - 1) - seg.rangeSum(dfn[c], dfn[c] + sz[c] - 1);
    }

    long long totalSum() { return seg.rangeSum(0, n - 1); }
    long long at(int u) { return seg.rangeSum(dfn[u], dfn[u]); }

    // ---------------- 不变式自检: dfn 子树连续性 ----------------
    bool subtreeContiguous() const {
        for (int u = 0; u < n; ++u) {
            for (int i = dfn[u]; i < dfn[u] + sz[u]; ++i) {
                int x = rnk[i];
                while (x != u && x != -1) x = par[x];
                if (x != u) return false;
            }
            if (dfn[u] + sz[u] > n) return false;
        }
        return true;
    }
};

// ============================================================
// C. BinLift —— 倍增 LCA + 根前缀和(静态路径和)
//
// 只能处理"只读"的树: 一旦有修改, 前缀和全部失效。
// 这正是 HLD 存在的理由: 同一个查询, 静态 O(log n) 但不可修改;
// HLD 牺牲一点常数, 换来 O(log^2 n) 且支持任意路径/子树修改。
// ============================================================
class BinLift {
public:
    int n = 0, LOG = 0;
    vector<int> dep, par;
    vector<vector<int>> up;
    vector<long long> pre, val;

    BinLift(int n_, const vector<int>& eu, const vector<int>& ev, int root,
            const vector<long long>& v) {
        n = n_;
        val = v;
        vector<vector<int>> adj(n);
        for (size_t i = 0; i < eu.size(); ++i) {
            adj[eu[i]].push_back(ev[i]);
            adj[ev[i]].push_back(eu[i]);
        }
        LOG = 1;
        while ((1 << LOG) <= n) ++LOG;
        up.assign(LOG, vector<int>(n, -1));
        dep.assign(n, 0);
        par.assign(n, -1);
        pre.assign(n, 0);
        vector<int> ord;
        ord.reserve(n);
        ord.push_back(root);
        pre[root] = val[root];
        for (size_t i = 0; i < ord.size(); ++i) {
            int u = ord[i];
            for (int w : adj[u]) {
                if (w == par[u]) continue;
                par[w] = u;
                dep[w] = dep[u] + 1;
                pre[w] = pre[u] + val[w];
                ord.push_back(w);
            }
        }
        up[0] = par;
        for (int k = 1; k < LOG; ++k)
            for (int i = 0; i < n; ++i) {
                int m = up[k - 1][i];
                up[k][i] = (m < 0 ? -1 : up[k - 1][m]);
            }
    }

    int lca(int u, int v) const {
        if (dep[u] < dep[v]) swap(u, v);
        int d = dep[u] - dep[v];
        for (int k = 0; k < LOG; ++k)
            if ((d >> k) & 1) u = up[k][u];
        if (u == v) return u;
        for (int k = LOG - 1; k >= 0; --k)
            if (up[k][u] != up[k][v]) { u = up[k][u]; v = up[k][v]; }
        return up[0][u];
    }

    long long pathSum(int u, int v) const {
        int l = lca(u, v);
        return pre[u] + pre[v] - 2 * pre[l] + val[l];
    }
};

// ============================================================
// D. Brute —— 逐点爬树的暴力参考
// 路径: 每次把深的一侧上移一格, O(路径长)
// 子树: 对每个节点判断"u 是否其祖先", O(n·depth)
// ============================================================
class Brute {
public:
    int n = 0;
    vector<int> par, dep;
    vector<long long> val;
    vector<vector<int>> adj;

    Brute(int n_, const vector<int>& eu, const vector<int>& ev, int root,
          const vector<long long>& v) {
        n = n_;
        val = v;
        adj.assign(n, {});
        for (size_t i = 0; i < eu.size(); ++i) {
            adj[eu[i]].push_back(ev[i]);
            adj[ev[i]].push_back(eu[i]);
        }
        par.assign(n, -1);
        dep.assign(n, 0);
        vector<int> ord;
        ord.push_back(root);
        for (size_t i = 0; i < ord.size(); ++i) {
            int u = ord[i];
            for (int w : adj[u]) {
                if (w == par[u]) continue;
                par[w] = u;
                dep[w] = dep[u] + 1;
                ord.push_back(w);
            }
        }
    }

    void pathAdd(int u, int v, long long d) {
        while (u != v) {
            if (dep[u] < dep[v]) swap(u, v);
            val[u] += d;
            u = par[u];
        }
        val[u] += d;
    }

    long long pathSum(int u, int v) const {
        long long res = 0;
        int a = u, b = v;
        while (a != b) {
            if (dep[a] < dep[b]) swap(a, b);
            res += val[a];
            a = par[a];
        }
        res += val[a];
        return res;
    }

    long long pathMax(int u, int v) const {
        long long res = LLONG_MIN;
        int a = u, b = v;
        while (a != b) {
            if (dep[a] < dep[b]) swap(a, b);
            res = max(res, val[a]);
            a = par[a];
        }
        return max(res, val[a]);
    }

    bool isAnc(int a, int b) const {  // a 是否为 b 的祖先(含自身)
        while (b != -1) {
            if (b == a) return true;
            b = par[b];
        }
        return false;
    }

    void subtreeAdd(int u, long long d) {
        for (int w = 0; w < n; ++w)
            if (isAnc(u, w)) val[w] += d;
    }
    long long subtreeSum(int u) const {
        long long s = 0;
        for (int w = 0; w < n; ++w)
            if (isAnc(u, w)) s += val[w];
        return s;
    }
    long long subtreeMax(int u) const {
        long long s = LLONG_MIN;
        for (int w = 0; w < n; ++w)
            if (isAnc(u, w)) s = max(s, val[w]);
        return s;
    }

    // 以 r 为根时 u 的子树和: 重跑一次 BFS 定根, 再逐点判祖先
    long long rerootSubtreeSum(int u, int r) const {
        vector<int> p2(n, -1);
        vector<int> ord;
        ord.push_back(r);
        for (size_t i = 0; i < ord.size(); ++i) {
            int x = ord[i];
            for (int w : adj[x]) {
                if (w == p2[x]) continue;
                p2[w] = x;
                ord.push_back(w);
            }
        }
        long long s = 0;
        for (int w = 0; w < n; ++w) {
            int x = w;
            while (x != -1 && x != u) x = p2[x];
            if (x == u) s += val[w];
        }
        return s;
    }
};

// ============================================================
// 树形构造器
//   shape 0 链 / 1 菊花 / 2 完全二叉树 / 3 随机递归树(par[i] < i)
// ============================================================
static void makeShape(int shape, int n, vector<int>& eu, vector<int>& ev) {
    eu.clear();
    ev.clear();
    if (shape == 0) {
        for (int i = 1; i < n; ++i) { eu.push_back(i - 1); ev.push_back(i); }
    } else if (shape == 1) {
        for (int i = 1; i < n; ++i) { eu.push_back(0); ev.push_back(i); }
    } else if (shape == 2) {
        for (int i = 1; i < n; ++i) { eu.push_back((i - 1) / 2); ev.push_back(i); }
    } else {
        for (int i = 1; i < n; ++i) { eu.push_back((int)(xr32() % (uint32_t)i)); ev.push_back(i); }
    }
}

// ============================================================
// G1 随机树混合操作 vs 暴力
// ============================================================
static void group1() {
    printf("[G1] 随机树 n=60, 3000 次混合操作(路径加/和/最值 + 子树加/和/最值)\n");
    int base = g_fail;
    reseed(0xBEEF0011ULL);
    const int n = 60;
    vector<int> eu, ev;
    makeShape(3, n, eu, ev);
    vector<long long> v(n);
    for (int i = 0; i < n; ++i) v[i] = (long long)(xr32() % 101) - 50;

    HLD h(n, eu, ev, 0, v);
    Brute b(n, eu, ev, 0, v);
    CHECK(h.subtreeContiguous(), "dfn 序子树连续性(建树后)");

    int mismatch = 0, printed = 0, opCnt[6] = {0, 0, 0, 0, 0, 0};
    for (int it = 0; it < 3000; ++it) {
        int u = (int)(xr32() % (uint32_t)n);
        int w = (int)(xr32() % (uint32_t)n);
        long long d = (long long)(xr32() % 21) - 10;
        int op = (int)(xr32() % 6);
        ++opCnt[op];
        if (op == 0) {
            h.pathAdd(u, w, d);
            b.pathAdd(u, w, d);
        } else if (op == 1) {
            long long x = h.pathSum(u, w), y = b.pathSum(u, w);
            if (x != y) {
                ++mismatch;
                if (printed++ < 3) printf("    pathSum(%d,%d) hld=%lld brute=%lld\n", u, w, x, y);
            }
        } else if (op == 2) {
            long long x = h.pathMax(u, w), y = b.pathMax(u, w);
            if (x != y) {
                ++mismatch;
                if (printed++ < 3) printf("    pathMax(%d,%d) hld=%lld brute=%lld\n", u, w, x, y);
            }
        } else if (op == 3) {
            h.subtreeAdd(u, d);
            b.subtreeAdd(u, d);
        } else if (op == 4) {
            long long x = h.subtreeSum(u), y = b.subtreeSum(u);
            if (x != y) {
                ++mismatch;
                if (printed++ < 3) printf("    subtreeSum(%d) hld=%lld brute=%lld\n", u, x, y);
            }
        } else {
            long long x = h.subtreeMax(u), y = b.subtreeMax(u);
            if (x != y) {
                ++mismatch;
                if (printed++ < 3) printf("    subtreeMax(%d) hld=%lld brute=%lld\n", u, x, y);
            }
        }
    }
    CHECK(mismatch == 0, "G1 混合操作 3000 次失配 %d 次", mismatch);

    // 终态逐点校验: 单点查询 == 暴力值
    int badPoint = 0;
    for (int i = 0; i < n; ++i)
        if (h.at(i) != b.val[i]) {
            if (badPoint++ < 3) printf("    at(%d) hld=%lld brute=%lld\n", i, h.at(i), b.val[i]);
        }
    CHECK(badPoint == 0, "G1 终态逐点失配 %d 个", badPoint);
    CHECK(h.subtreeContiguous(), "dfn 序子树连续性(3000 次修改后)");
    printf("    操作分布: 加=%d 路径和=%d 路径最值=%d 子树加=%d 子树和=%d 子树最值=%d\n",
           opCnt[0], opCnt[1], opCnt[2], opCnt[3], opCnt[4], opCnt[5]);
    report("G1", base);
}

// ============================================================
// G2 四种树形(链/菊花/完全二叉树/随机树)各 1200 次路径操作
// ============================================================
static void group2() {
    printf("[G2] 四种树形 n=200, 各 1200 次路径加/和/最值 vs 暴力\n");
    int base = g_fail;
    const char* names[4] = {"链", "菊花", "完全二叉树", "随机树"};
    for (int shape = 0; shape < 4; ++shape) {
        reseed(0xCAFE0000ULL + (uint64_t)shape * 7919ULL);
        const int n = 200;
        vector<int> eu, ev;
        makeShape(shape, n, eu, ev);
        vector<long long> v(n);
        for (int i = 0; i < n; ++i) v[i] = (long long)(xr32() % 41) - 20;

        HLD h(n, eu, ev, 0, v);
        Brute b(n, eu, ev, 0, v);
        int mismatch = 0;
        for (int it = 0; it < 1200; ++it) {
            int u = (int)(xr32() % (uint32_t)n);
            int w = (int)(xr32() % (uint32_t)n);
            long long d = (long long)(xr32() % 11) - 5;
            int op = (int)(xr32() % 4);
            if (op == 0) { h.pathAdd(u, w, d); b.pathAdd(u, w, d); }
            else if (op == 1) { if (h.pathSum(u, w) != b.pathSum(u, w)) ++mismatch; }
            else if (op == 2) { if (h.pathMax(u, w) != b.pathMax(u, w)) ++mismatch; }
            else { h.subtreeAdd(u, d); b.subtreeAdd(u, d); }  // 子树修改也要覆盖
        }
        CHECK(mismatch == 0, "G2 %s 失配 %d 次", names[shape], mismatch);
        CHECK(h.subtreeContiguous(), "G2 %s 子树连续性", names[shape]);
        // 子树和也必须一致(独立于路径操作的校验路径)
        int bad = 0;
        for (int u = 0; u < n; ++u)
            if (h.subtreeSum(u) != b.subtreeSum(u)) ++bad;
        CHECK(bad == 0, "G2 %s 全节点子树和失配 %d 个", names[shape], bad);
        printf("    %-12s 完成(失配 %d, 子树和错 %d)\n", names[shape], mismatch, bad);
    }
    report("G2", base);
}

// ============================================================
// G3 静态路径和: HLD / 倍增 / 暴力 三方对拍
// ============================================================
static void group3() {
    printf("[G3] 静态路径和 n=500, 2000 次查询三方对拍(HLD/倍增/暴力)\n");
    int base = g_fail;
    reseed(0xD00D0011ULL);
    const int n = 500;
    vector<int> eu, ev;
    makeShape(3, n, eu, ev);
    vector<long long> v(n);
    for (int i = 0; i < n; ++i) v[i] = (long long)(xr32() % 2001) - 1000;

    HLD h(n, eu, ev, 0, v);
    BinLift bl(n, eu, ev, 0, v);
    Brute b(n, eu, ev, 0, v);

    int mismatch = 0, printed = 0;
    for (int it = 0; it < 2000; ++it) {
        int u = (int)(xr32() % (uint32_t)n);
        int w = (int)(xr32() % (uint32_t)n);
        long long a = h.pathSum(u, w), c = bl.pathSum(u, w), d = b.pathSum(u, w);
        if (!(a == c && c == d)) {
            ++mismatch;
            if (printed++ < 3)
                printf("    pathSum(%d,%d): hld=%lld binlift=%lld brute=%lld\n", u, w, a, c, d);
        }
        if (h.lca(u, w) != bl.lca(u, w)) {
            ++mismatch;
            if (printed++ < 3) printf("    lca(%d,%d) 不一致\n", u, w);
        }
    }
    CHECK(mismatch == 0, "G3 三方失配 %d 次", mismatch);

    // ancestorAt 专项: 对每个节点验证每个深度都能定位到正确答案
    int badAnc = 0;
    for (int u = 0; u < n; ++u)
        for (int d = 0; d <= h.dep[u]; ++d) {
            int x = h.ancestorAt(u, d);
            if (h.dep[x] != d || !h.isAncestor(x, u)) {
                if (badAnc++ < 3) printf("    ancestorAt(%d,%d)=%d dep=%d\n", u, d, x, h.dep[x]);
            }
        }
    CHECK(badAnc == 0, "G3 ancestorAt 失配 %d 个", badAnc);
    report("G3", base);
}

// ============================================================
// G4 边界: n=1 / n=2 / 换根建树(root 非 0) / u==v / 根为叶
// ============================================================
static void group4() {
    printf("[G4] 边界专项\n");
    int base = g_fail;

    {  // n = 1: 无边的极端情况
        vector<int> eu, ev;
        vector<long long> v{7};
        HLD h(1, eu, ev, 0, v);
        CHECK(h.pathSum(0, 0) == 7, "n=1 pathSum 应 7, 实际 %lld", h.pathSum(0, 0));
        CHECK(h.pathMax(0, 0) == 7, "n=1 pathMax 应 7");
        CHECK(h.subtreeSum(0) == 7, "n=1 subtreeSum 应 7");
        CHECK(h.rerootSubtreeSum(0, 0) == 7, "n=1 换根应 7");
        h.pathAdd(0, 0, -3);
        CHECK(h.at(0) == 4, "n=1 加 -3 后应 4, 实际 %lld", h.at(0));
        CHECK(h.lca(0, 0) == 0, "n=1 lca 应 0");
    }
    {  // n = 2: 只有一条边
        vector<int> eu{0}, ev{1};
        vector<long long> v{5, -8};
        HLD h(2, eu, ev, 0, v);
        CHECK(h.pathSum(0, 1) == -3, "n=2 路径和应 -3, 实际 %lld", h.pathSum(0, 1));
        CHECK(h.pathMax(0, 1) == 5, "n=2 路径最值应 5");
        CHECK(h.subtreeSum(0) == -3 && h.subtreeSum(1) == -8, "n=2 子树和错");
        CHECK(h.rerootSubtreeSum(0, 1) == 5, "n=2 以 1 为根时 0 的子树应 5");
        CHECK(h.ancestorAt(1, 0) == 0, "n=2 ancestorAt(1,0) 应 0");
    }
    {  // 换根建树: root = n-1, 路径结论必须与 root=0 完全一致
        reseed(0x4E000011ULL);
        const int n = 37;
        vector<int> eu, ev;
        makeShape(3, n, eu, ev);
        vector<long long> v(n);
        for (int i = 0; i < n; ++i) v[i] = (long long)(xr32() % 31) - 15;

        HLD h0(n, eu, ev, 0, v);
        HLD h1(n, eu, ev, n - 1, v);
        Brute b0(n, eu, ev, 0, v);
        Brute b1(n, eu, ev, n - 1, v);
        int mismatch = 0;
        for (int it = 0; it < 400; ++it) {
            int u = (int)(xr32() % (uint32_t)n);
            int w = (int)(xr32() % (uint32_t)n);
            if (h0.pathSum(u, w) != b0.pathSum(u, w)) ++mismatch;
            if (h1.pathSum(u, w) != b1.pathSum(u, w)) ++mismatch;
            if (h1.pathSum(u, w) != h0.pathSum(u, w)) ++mismatch;  // 路径和与根无关
        }
        CHECK(mismatch == 0, "换根建树失配 %d 次", mismatch);
        CHECK(h1.subtreeContiguous(), "换根建树后子树连续性");
        // 根为叶: 根的子树 = 全树
        CHECK(h1.subtreeSum(n - 1) == b1.subtreeSum(n - 1), "根为叶时子树和错");
    }
    report("G4", base);
}

// ============================================================
// G5 跳链次数实证: 路径被切成的段数 = 跳链次数 + 1
// ============================================================
static void group5() {
    printf("[G5] 跳链次数实证 n=32768, 2000 次随机路径和\n");
    int base = g_fail;
    const int n = 1 << 15;
    const char* names[4] = {"链", "菊花", "完全二叉树", "随机树"};
    for (int shape = 0; shape < 4; ++shape) {
        reseed(0x51000000ULL + (uint64_t)shape * 131ULL);
        vector<int> eu, ev;
        makeShape(shape, n, eu, ev);
        vector<long long> v(n, 1);
        HLD h(n, eu, ev, 0, v);
        BinLift bl(n, eu, ev, 0, v);   // 只用来算"暴力路径长度"作对比

        reseed(0x77770000ULL + (uint64_t)shape);
        long long totalJumps = 0, maxJumps = 0, totalPathLen = 0;
        for (int it = 0; it < 2000; ++it) {
            int u = (int)(xr32() % (uint32_t)n);
            int w = (int)(xr32() % (uint32_t)n);
            long long before = h.jumpCnt;
            h.pathSum(u, w);
            long long j = h.jumpCnt - before;
            totalJumps += j;
            maxJumps = max(maxJumps, j);
            int l = bl.lca(u, w);
            totalPathLen += (long long)h.dep[u] + h.dep[w] - 2LL * h.dep[l] + 1;
        }
        double avgJ = (double)totalJumps / 2000.0;
        double avgLen = (double)totalPathLen / 2000.0;
        printf("    %-12s 平均段数 %5.2f (跳链 %5.2f, 最大 %4lld) | 平均路径长 %9.1f "
               "| 折叠率 %8.1fx\n",
               names[shape], avgJ + 1, avgJ, maxJumps, avgLen, avgLen / (avgJ + 1));
        // 上界: 任意节点到根最多 log2(n) 条轻边, 路径至多两倍(留 16 的余量)
        CHECK(maxJumps <= 2LL * 16 + 2, "%s 跳链次数 %lld 超过 2log2(n)+2", names[shape], maxJumps);
        if (shape == 0) CHECK(avgJ == 0.0, "链上跳链应为 0, 实际 %.2f", avgJ);
        if (shape == 1) CHECK(avgJ <= 2.0, "菊花上跳链应 <= 2, 实际 %.2f", avgJ);
        if (shape >= 2) CHECK(avgJ >= 1.0, "%s 平均跳链应 >= 1, 实际 %.2f", names[shape], avgJ);
    }
    printf("    读法: 折叠率 = 路径点数 / 段数, 只说明\"路径被压缩了多少\"。\n");
    printf("    真正的代价是 段数 x O(log n): 链上 1 段完胜, 平衡树上段数已接近路径长度,\n");
    printf("    HLD 的价值在\"深树 + 需要修改\", 不在\"浅树 + 只读\"(那种场景倍增前缀和更划算)。\n");
    report("G5", base);
}

// ============================================================
// G6 换根子树和 vs 暴力(每个查询重跑 BFS 定根)
// ============================================================
static void group6() {
    printf("[G6] 换根子树和 n=80, 200 次路径加后 300 次随机 (u, 根) 查询\n");
    int base = g_fail;
    reseed(0x600D0011ULL);
    const int n = 80;
    vector<int> eu, ev;
    makeShape(3, n, eu, ev);
    vector<long long> v(n);
    for (int i = 0; i < n; ++i) v[i] = (long long)(xr32() % 41) - 20;

    HLD h(n, eu, ev, 0, v);
    Brute b(n, eu, ev, 0, v);
    for (int it = 0; it < 200; ++it) {
        int u = (int)(xr32() % (uint32_t)n);
        int w = (int)(xr32() % (uint32_t)n);
        long long d = (long long)(xr32() % 11) - 5;
        h.pathAdd(u, w, d);
        b.pathAdd(u, w, d);
    }
    int mismatch = 0, printed = 0;
    for (int it = 0; it < 300; ++it) {
        int u = (int)(xr32() % (uint32_t)n);
        int r = (int)(xr32() % (uint32_t)n);
        long long x = h.rerootSubtreeSum(u, r), y = b.rerootSubtreeSum(u, r);
        if (x != y) {
            ++mismatch;
            if (printed++ < 3) printf("    rerootSubtreeSum(%d, root=%d): hld=%lld brute=%lld\n", u, r, x, y);
        }
    }
    CHECK(mismatch == 0, "G6 换根子树和失配 %d 次", mismatch);
    report("G6", base);
}

// ============================================================
// 基准: 建树 + 10 万次路径和
// ============================================================
static void benchOne(const char* name, int shape, int n, int q) {
    reseed(0xC0FFEE00ULL + (uint64_t)shape);
    vector<int> eu, ev;
    makeShape(shape, n, eu, ev);
    vector<long long> v(n, 1);

    auto t0 = chrono::steady_clock::now();
    HLD h(n, eu, ev, 0, v);
    auto t1 = chrono::steady_clock::now();

    reseed(0x5EED0000ULL + (uint64_t)shape);
    long long sum = 0;
    for (int i = 0; i < q; ++i) {
        int u = (int)(xr32() % (uint32_t)n);
        int w = (int)(xr32() % (uint32_t)n);
        sum += h.pathSum(u, w);
    }
    auto t2 = chrono::steady_clock::now();

    double buildMs = chrono::duration<double, milli>(t1 - t0).count();
    double queryMs = chrono::duration<double, milli>(t2 - t1).count();
    printf("    %-12s n=%d q=%d | 建树 %7.2f ms | 查询 %8.2f ms (%5.0f ns/op) | "
           "平均跳链 %5.2f | sum=%lld\n",
           name, n, q, buildMs, queryMs, queryMs * 1e6 / (double)q,
           (double)h.jumpCnt / (double)q, sum);
}

static void benchmark() {
    printf("[基准] n=200000, q=100000 路径和查询\n");
    benchOne("随机树", 3, 200000, 100000);
    benchOne("链", 0, 200000, 100000);
    benchOne("菊花", 1, 200000, 100000);
    benchOne("完全二叉树", 2, 200000, 100000);
}

int main() {
    printf("=== 0011 树链剖分 HLD ===\n");
    group1();
    group2();
    group3();
    group4();
    group5();
    group6();
    benchmark();
    printf("\n=== 汇总: %s (失败项 %d) ===\n", g_fail == 0 ? "全部通过" : "存在失败", g_fail);
    return g_fail == 0 ? 0 : 1;
}
