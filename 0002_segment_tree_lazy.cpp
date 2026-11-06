// =============================================================================
//  每日 C++ 数据结构 · 0002  ——  线段树 + 懒标记 (Lazy Propagation / Tag Permanence)
//  编译: g++ -O2 -std=c++17 -Wall -Wextra -o segtree 0002_segment_tree_lazy.cpp
//  运行: ./segtree
//
//  本程序包含三块内容:
//    [1] 核心实现: 区间加 / 区间赋值 / 区间和 —— pushdown 双标记版
//        对照实现: 标记永久化版 (免 pushdown, 区间加 + 区间和更快)
//    [2] 随机对拍: 与暴力做法逐项比对 (含整段覆盖后区间加的标记叠加顺序)
//    [3] 性能实测: pushdown 版 vs 标记永久化版 vs O(n) 暴力
// =============================================================================
#include <algorithm>
#include <chrono>
#include <cstdio>
#include <random>
#include <vector>

#ifdef _WIN32
#include <windows.h>   // 仅用于把控制台切到 UTF-8, 避免中文输出乱码
#endif

using i64 = long long;
using Clock = std::chrono::steady_clock;

static inline double ms_since(const Clock::time_point& t0) {
    return std::chrono::duration<double, std::milli>(Clock::now() - t0).count();
}

static volatile i64 g_sink = 0;   // 防止编译器把基准测试整段优化掉

// -----------------------------------------------------------------------------
// [1a] pushdown 版线段树: 区间加 + 区间赋值 + 区间和, 单次操作 O(log n)
//
//      每个节点挂两个懒标记:
//        cov/val : 「整段先覆盖为 val」 —— 优先级最高, 会吸收掉已有的 add
//        add     : 「整段再加 add」 —— 叠加在覆盖之上
//      下传顺序: 先下发覆盖, 再下发加; 标记相加时子节点同理先吸收再叠加。
//      这套 "applyCov 吞掉 add" 的合并规则是双标记不写错的关键。
// -----------------------------------------------------------------------------
class SegTreeLazy {
public:
    void init(int n) {
        n_ = n;
        const size_t s = static_cast<size_t>(4 * n);
        sum_.assign(s, 0);
        add_.assign(s, 0);
        val_.assign(s, 0);
        cov_.assign(s, false);
    }

    void build(const std::vector<i64>& a) {       // a 为 0-indexed
        init(static_cast<int>(a.size()));
        if (n_ > 0) build(1, 0, n_ - 1, a);
    }

    void rangeAdd(int l, int r, i64 d) {          // 闭区间 [l, r], 0-indexed
        if (l > r) return;
        rangeAdd(1, 0, n_ - 1, l, r, d);
    }

    void rangeAssign(int l, int r, i64 v) {
        if (l > r) return;
        rangeAssign(1, 0, n_ - 1, l, r, v);
    }

    i64 rangeSum(int l, int r) const {
        if (l > r) return 0;
        return query(1, 0, n_ - 1, l, r);
    }

private:
    // 覆盖标记: 覆盖会把该节点尚未下传的加标记一并吞掉
    void applyCov(int node, int len, i64 v) {
        sum_[node] = v * len;
        cov_[node] = true;
        val_[node] = v;
        add_[node] = 0;
    }

    // 加标记: 若节点已被覆盖, 加法直接并入覆盖值, 避免两个标记的顺序问题
    void applyAdd(int node, int len, i64 d) {
        sum_[node] += d * len;
        if (cov_[node]) val_[node] += d;
        else add_[node] += d;
    }

    // 下传: 先覆盖后加 (与 applyAdd 的吸收规则一致, 顺序不可颠倒)
    void push(int node, int lo, int hi) {
        const int mid = (lo + hi) >> 1;
        const int lenL = mid - lo + 1, lenR = hi - mid;
        if (cov_[node]) {
            applyCov(2 * node, lenL, val_[node]);
            applyCov(2 * node + 1, lenR, val_[node]);
            cov_[node] = false;
        }
        if (add_[node] != 0) {
            applyAdd(2 * node, lenL, add_[node]);
            applyAdd(2 * node + 1, lenR, add_[node]);
            add_[node] = 0;
        }
    }

    void pull(int node) { sum_[node] = sum_[2 * node] + sum_[2 * node + 1]; }

    void build(int node, int lo, int hi, const std::vector<i64>& a) {
        if (lo == hi) { sum_[node] = a[lo]; return; }
        const int mid = (lo + hi) >> 1;
        build(2 * node, lo, mid, a);
        build(2 * node + 1, mid + 1, hi, a);
        pull(node);
    }

    void rangeAdd(int node, int lo, int hi, int l, int r, i64 d) {
        if (l <= lo && hi <= r) { applyAdd(node, hi - lo + 1, d); return; }
        push(node, lo, hi);
        const int mid = (lo + hi) >> 1;
        if (l <= mid) rangeAdd(2 * node, lo, mid, l, r, d);
        if (r > mid) rangeAdd(2 * node + 1, mid + 1, hi, l, r, d);
        pull(node);
    }

    void rangeAssign(int node, int lo, int hi, int l, int r, i64 v) {
        if (l <= lo && hi <= r) { applyCov(node, hi - lo + 1, v); return; }
        push(node, lo, hi);
        const int mid = (lo + hi) >> 1;
        if (l <= mid) rangeAssign(2 * node, lo, mid, l, r, v);
        if (r > mid) rangeAssign(2 * node + 1, mid + 1, hi, l, r, v);
        pull(node);
    }

    i64 query(int node, int lo, int hi, int l, int r) const {
        if (l <= lo && hi <= r) return sum_[node];
        push(node, lo, hi);
        const int mid = (lo + hi) >> 1;
        i64 res = 0;
        if (l <= mid) res += query(2 * node, lo, mid, l, r);
        if (r > mid) res += query(2 * node + 1, mid + 1, hi, l, r);
        return res;
    }

    int n_ = 0;
    std::vector<i64> sum_, add_, val_;
    std::vector<bool> cov_;
};

// -----------------------------------------------------------------------------
// [1b] 标记永久化版线段树: 区间加 + 区间和, 免 pushdown
//
//      思想: 标记不再下传, 永久留在节点上。
//        - 修改: 途中经过的每个节点, sum 都按「与操作区间的交集长度」即时累加,
//          完全覆盖时额外把 d 存入 add[node] 永久保留。
//        - 查询: 完全覆盖直接返回 sum; 部分覆盖时, 祖先身上残留的 add 标记
//          按「查询区间与该节点区间的交集长度」折算进答案。
//      每次操作只走一条根到叶的路径, 无下传、无回溯 pull, 常数显著更小。
//      代价: 只适合「标记不冲突」的场景 (纯区间加); 覆盖+加混合时规则复杂,
//      通常退回 pushdown 版。
// -----------------------------------------------------------------------------
class SegTreePermanent {
public:
    void init(int n) {
        n_ = n;
        sum_.assign(static_cast<size_t>(4 * n), 0);
        add_.assign(static_cast<size_t>(4 * n), 0);
    }

    void build(const std::vector<i64>& a) {
        init(static_cast<int>(a.size()));
        if (n_ > 0) build(1, 0, n_ - 1, a);
    }

    void rangeAdd(int l, int r, i64 d) {
        if (l > r) return;
        rangeAdd(1, 0, n_ - 1, l, r, d);
    }

    i64 rangeSum(int l, int r) const {
        if (l > r) return 0;
        return query(1, 0, n_ - 1, l, r);
    }

private:
    void build(int node, int lo, int hi, const std::vector<i64>& a) {
        if (lo == hi) { sum_[node] = a[lo]; return; }
        const int mid = (lo + hi) >> 1;
        build(2 * node, lo, mid, a);
        build(2 * node + 1, mid + 1, hi, a);
        sum_[node] = sum_[2 * node] + sum_[2 * node + 1];
    }

    void rangeAdd(int node, int lo, int hi, int l, int r, i64 d) {
        sum_[node] += d * i64(std::min(hi, r) - std::max(lo, l) + 1);  // 途经即累加
        if (l <= lo && hi <= r) { add_[node] += d; return; }           // 永久留存
        const int mid = (lo + hi) >> 1;
        if (l <= mid) rangeAdd(2 * node, lo, mid, l, r, d);
        if (r > mid) rangeAdd(2 * node + 1, mid + 1, hi, l, r, d);
    }

    i64 query(int node, int lo, int hi, int l, int r) const {
        if (l <= lo && hi <= r) return sum_[node];
        // 祖先残留标记对查询区间的贡献: 交集长度 * add
        i64 res = add_[node] * i64(std::min(hi, r) - std::max(lo, l) + 1);
        const int mid = (lo + hi) >> 1;
        if (l <= mid) res += query(2 * node, lo, mid, l, r);
        if (r > mid) res += query(2 * node + 1, mid + 1, hi, l, r);
        return res;
    }

    int n_ = 0;
    std::vector<i64> sum_, add_;
};

// -----------------------------------------------------------------------------
// [2] 随机对拍
// -----------------------------------------------------------------------------
static bool stress_mix(std::mt19937& rng) {
    // 覆盖 / 加 / 求和 混合操作, 专打「覆盖后区间加」的标记叠加顺序
    for (int round = 0; round < 200; ++round) {
        const int n = static_cast<int>(rng() % 48) + 1;
        std::vector<i64> a(static_cast<size_t>(n), 0);
        SegTreeLazy seg;
        seg.build(a);
        for (int op = 0; op < 800; ++op) {
            int l = static_cast<int>(rng() % n);
            int r = static_cast<int>(rng() % n);
            if (l > r) std::swap(l, r);
            const unsigned t = rng() % 3;
            if (t == 0) {                                  // 区间加
                const i64 d = static_cast<i64>(rng() % 201) - 100;
                for (int i = l; i <= r; ++i) a[i] += d;
                seg.rangeAdd(l, r, d);
            } else if (t == 1) {                           // 区间赋值
                const i64 v = static_cast<i64>(rng() % 201) - 100;
                for (int i = l; i <= r; ++i) a[i] = v;
                seg.rangeAssign(l, r, v);
            } else {                                       // 区间求和
                i64 want = 0;
                for (int i = l; i <= r; ++i) want += a[i];
                if (seg.rangeSum(l, r) != want) {
                    std::printf("  [FAIL] mix: n=%d op=%d l=%d r=%d\n", n, op, l, r);
                    return false;
                }
            }
        }
    }
    return true;
}

static bool stress_permanent(std::mt19937& rng) {
    for (int round = 0; round < 200; ++round) {
        const int n = static_cast<int>(rng() % 48) + 1;
        std::vector<i64> a(static_cast<size_t>(n));
        for (auto& x : a) x = static_cast<i64>(rng() % 50) - 25;
        SegTreePermanent seg;
        seg.build(a);
        for (int op = 0; op < 800; ++op) {
            int l = static_cast<int>(rng() % n);
            int r = static_cast<int>(rng() % n);
            if (l > r) std::swap(l, r);
            if (rng() % 2 == 0) {
                const i64 d = static_cast<i64>(rng() % 199) - 99;
                for (int i = l; i <= r; ++i) a[i] += d;
                seg.rangeAdd(l, r, d);
            } else {
                i64 want = 0;
                for (int i = l; i <= r; ++i) want += a[i];
                if (seg.rangeSum(l, r) != want) {
                    std::printf("  [FAIL] permanent: n=%d op=%d l=%d r=%d\n", n, op, l, r);
                    return false;
                }
            }
        }
    }
    return true;
}

static bool stress_edges(std::mt19937& rng) {
    // 边界: n=1、单点操作、整段覆盖再整段加、重复覆盖
    {
        SegTreeLazy seg;
        seg.build({7});
        seg.rangeAdd(0, 0, 3);
        seg.rangeAssign(0, 0, 10);
        if (seg.rangeSum(0, 0) != 10) return false;
    }
    {
        SegTreePermanent seg;
        seg.build({7});
        seg.rangeAdd(0, 0, 3);
        if (seg.rangeSum(0, 0) != 10) return false;
        if (seg.rangeSum(0, 0) != 10) return false;   // 查询不能有副作用
    }
    for (int round = 0; round < 100; ++round) {
        const int n = static_cast<int>(rng() % 30) + 1;
        std::vector<i64> a(static_cast<size_t>(n), 0);
        SegTreeLazy seg;
        seg.build(a);
        for (int op = 0; op < 200; ++op) {
            if (rng() % 3 == 0) {
                const i64 v = static_cast<i64>(rng() % 100);
                for (auto& x : a) x = v;
                seg.rangeAssign(0, n - 1, v);         // 整段覆盖
            } else {
                const i64 d = static_cast<i64>(rng() % 100);
                for (auto& x : a) x += d;
                seg.rangeAdd(0, n - 1, d);            // 整段加 (覆盖后立即叠加)
            }
            const int i = static_cast<int>(rng() % n);
            if (seg.rangeSum(i, i) != a[i]) return false;
        }
        i64 want = 0;
        for (auto x : a) want += x;
        if (seg.rangeSum(0, n - 1) != want) return false;
    }
    return true;
}

// -----------------------------------------------------------------------------
// [3] 性能实测: pushdown 版 vs 标记永久化版 vs O(n) 暴力
// -----------------------------------------------------------------------------
static void bench() {
    const int n = 1 << 20;      // 元素个数: 1,048,576
    const int Q = 1 << 19;      // 每类操作次数: 524,288
    std::mt19937 rng(20261020u);

    std::vector<i64> a(static_cast<size_t>(n));
    for (auto& x : a) x = static_cast<i64>(rng() % 1000);

    SegTreeLazy lazy_t;
    SegTreePermanent perm_t;
    lazy_t.build(a);
    perm_t.build(a);

    // 预生成操作序列 (两版本用同一序列, 保证公平)
    std::vector<int> qs(static_cast<size_t>(Q)), qe(static_cast<size_t>(Q));
    std::vector<i64> qd(static_cast<size_t>(Q));
    for (int i = 0; i < Q; ++i) {
        int l = static_cast<int>(rng() % n);
        int r = static_cast<int>(rng() % n);
        if (l > r) std::swap(l, r);
        qs[i] = l; qe[i] = r;
        qd[i] = static_cast<i64>(rng() % 100) - 50;
    }

    // ---- 区间加 ----
    auto t0 = Clock::now();
    for (int i = 0; i < Q; ++i) lazy_t.rangeAdd(qs[i], qe[i], qd[i]);
    const double tAddLazy = ms_since(t0);

    t0 = Clock::now();
    for (int i = 0; i < Q; ++i) perm_t.rangeAdd(qs[i], qe[i], qd[i]);
    const double tAddPerm = ms_since(t0);

    // ---- 区间和 (只读, 检验两版结果一致) ----
    t0 = Clock::now();
    i64 sLazy = 0;
    for (int i = 0; i < Q; ++i) sLazy += lazy_t.rangeSum(qs[i], qe[i]);
    const double tSumLazy = ms_since(t0);

    t0 = Clock::now();
    i64 sPerm = 0;
    for (int i = 0; i < Q; ++i) sPerm += perm_t.rangeSum(qs[i], qe[i]);
    const double tSumPerm = ms_since(t0);

    // ---- O(n) 暴力对照: 元素与操作数都缩小到 1/16, 否则跑不完 ----
    const int nb = n >> 4, Qb = Q >> 4;
    std::vector<i64> ab(static_cast<size_t>(nb));
    for (auto& x : ab) x = static_cast<i64>(rng() % 1000);
    t0 = Clock::now();
    i64 sBrute = 0;
    for (int i = 0; i < Qb; ++i) {
        if (i % 2 == 0) {
            for (int j = qs[i]; j <= qe[i] && j < nb; ++j) ab[j] += qd[i];
        } else {
            for (int j = qs[i]; j <= qe[i] && j < nb; ++j) sBrute += ab[j];
        }
    }
    const double tBrute = ms_since(t0);
    g_sink += sLazy + sPerm + sBrute;

    std::printf("\n[3] 性能实测 (n = %d, 每类操作 %d 次, -O2, 单线程)\n", n, Q);
    std::printf("  %-30s %12s %12s %8s\n", "项目", "pushdown 版", "标记永久化", "加速比");
    std::printf("  %-28s %12.2f %12.2f %7.2fx\n", "区间加 (ms)", tAddLazy, tAddPerm,
                tAddLazy > 0 ? tAddPerm / tAddLazy : 0.0);
    std::printf("  %-28s %12.2f %12.2f %7.2fx\n", "区间和 (ms)", tSumLazy, tSumPerm,
                tSumLazy > 0 ? tSumPerm / tSumLazy : 0.0);
    std::printf("  (对照) O(n) 暴力: n/16 规模、1/16 次数已耗时 %.2f ms (同规模折算约慢 256 倍)\n",
                tBrute);
    std::printf("  校验: 两版本区间和结果%s\n", sLazy == sPerm ? "完全一致" : "不一致(!)");
}

int main() {
#ifdef _WIN32
    SetConsoleOutputCP(CP_UTF8);
#endif
    std::mt19937 rng(987654321u);
    std::printf("[2] 随机对拍 (暴力做法 vs 线段树)\n");
    const bool ok1 = stress_mix(rng);
    const bool ok2 = stress_permanent(rng);
    const bool ok3 = stress_edges(rng);
    std::printf("  覆盖/加/求和混合  : %s\n", ok1 ? "PASS" : "FAIL");
    std::printf("  标记永久化区间加  : %s\n", ok2 ? "PASS" : "FAIL");
    std::printf("  边界 (n=1/整段/单点): %s\n", ok3 ? "PASS" : "FAIL");

    // 小样例人工可验算: a = {1,2,3,4,5}
    std::vector<i64> demo{1, 2, 3, 4, 5};
    SegTreeLazy seg;
    seg.build(demo);
    seg.rangeAssign(1, 3, 10);        // -> {1,10,10,10,5}
    seg.rangeAdd(0, 4, 2);            // -> {3,12,12,12,7}
    std::printf("\n[示例] a = {1,2,3,4,5} -> assign(1..3)=10 -> add(0..4)=+2\n");
    std::printf("  sum(2..4) = %lld (期望 31)\n", seg.rangeSum(2, 4));
    std::printf("  sum(0..0) = %lld (期望 3)\n", seg.rangeSum(0, 0));

    SegTreePermanent perm;
    perm.build(demo);
    perm.rangeAdd(1, 3, 10);
    std::printf("  永久化版 sum(1..3) = %lld (期望 39)\n", perm.rangeSum(1, 3));

    bench();
    std::printf("\n所有测试%s\n", (ok1 && ok2 && ok3) ? "通过。" : "存在失败项。");
    return (ok1 && ok2 && ok3) ? 0 : 1;
}
