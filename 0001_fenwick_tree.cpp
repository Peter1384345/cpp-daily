// =============================================================================
//  每日 C++ 数据结构 · 0001  ——  树状数组 (Fenwick Tree / BIT)
//  编译: g++ -O2 -std=c++17 -Wall -Wextra -o fenwick 0001_fenwick_tree.cpp
//  运行: ./fenwick
//
//  本程序包含三块内容:
//    [1] 核心实现: 单点加 / 前缀和 / O(n) 建树 / 倍增二分求第 k 小
//    [2] 随机对拍: 与暴力做法逐项比对, 证明实现正确
//    [3] 性能实测: 与迭代式线段树对比常数因子 (n = Q = 2^20)
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
// [1] 树状数组: 单点修改 O(log n) / 前缀和 O(log n) / 空间 O(n)
//     内部 1-indexed, 第 i 个节点管辖长度为 lowbit(i) 的区间 (i-lowbit(i), i]
// -----------------------------------------------------------------------------
class Fenwick {
public:
    explicit Fenwick(int n = 0) { init(n); }

    void init(int n) {
        n_ = n;
        t_.assign(n + 1, 0);
        log_ = 0;
        while ((1 << (log_ + 1)) <= n) ++log_;   // log_ = floor(log2(n))
    }

    // O(n) 线性建树: 先把原值放进节点, 再由子节点向上累加到父节点。
    // 相比 n 次 add 的 O(n log n), 少了一次 log 的常数.
    void build(const std::vector<i64>& a) {      // a 为 0-indexed
        init(static_cast<int>(a.size()));
        for (int i = 1; i <= n_; ++i) t_[i] = a[i - 1];
        for (int i = 1; i <= n_; ++i) {
            const int j = i + (i & -i);
            if (j <= n_) t_[j] += t_[i];
        }
    }

    void add(int i, i64 d) {
        for (; i <= n_; i += i & -i) t_[i] += d;
    }

    i64 prefix(int i) const {                    // a[1] + ... + a[i]
        i64 s = 0;
        for (; i > 0; i -= i & -i) s += t_[i];
        return s;
    }

    i64 rangeSum(int l, int r) const {
        return (l > r) ? 0 : prefix(r) - prefix(l - 1);
    }

    // 最小的下标 idx, 使 prefix(idx) >= k。要求元素非负且 total() >= k。
    // 利用树的二进制结构做倍增, 单次 O(log n) 且无二分外的额外开销;
    // 这是 BIT 相对线段树的独门优势: 线段树上求 kth 需要 O(log^2 n) 或额外维护最大值。
    int kth(i64 k) const {
        int pos = 0;
        i64 cur = 0;
        for (int pw = 1 << log_; pw > 0; pw >>= 1) {
            const int nxt = pos + pw;
            if (nxt <= n_ && cur + t_[nxt] < k) {   // 严格小于: 取最后一个前缀和 < k 的位置
                pos = nxt;
                cur += t_[nxt];
            }
        }
        return pos + 1;
    }

    i64 total() const { return prefix(n_); }
    int size() const { return n_; }

private:
    int n_ = 0;
    int log_ = 0;
    std::vector<i64> t_;
};

// -----------------------------------------------------------------------------
// 双 BIT 维护「区间加 + 区间和」:
//   设差分 d[i] = a[i] - a[i-1], 则 a[i] = sum_{j<=i} d[j],
//   prefix(x) = sum_{i<=x} a[i] = (x+1) * sum(d[1..x]) - sum(i*d[i], i<=x)
//   维护 BIT1 = d[i], BIT2 = i*d[i] 即可。
// -----------------------------------------------------------------------------
class RangeFenwick {
public:
    explicit RangeFenwick(int n = 0) { init(n); }

    void init(int n) {
        n_ = n;
        b1_.init(n + 1);   // 多开一位吸收 r+1 的负标记, 省去边界判断
        b2_.init(n + 1);
    }

    void rangeAdd(int l, int r, i64 d) {
        if (l > r) return;
        b1_.add(l, d);              b1_.add(r + 1, -d);
        b2_.add(l, d * l);          b2_.add(r + 1, -d * (r + 1));   // 维护 j*d[j]
    }

    i64 prefix(int x) const {
        if (x <= 0) return 0;
        return (x + 1) * b1_.prefix(x) - b2_.prefix(x);
    }

    i64 rangeSum(int l, int r) const { return prefix(r) - prefix(l - 1); }

private:
    Fenwick b1_, b2_;
    int n_ = 0;
};

// -----------------------------------------------------------------------------
// 对照组: 迭代式线段树 (只做单点加 + 区间和, 已是最精简写法)
// -----------------------------------------------------------------------------
class IterSegTree {
public:
    void build(const std::vector<i64>& a) {
        n_ = 1;
        while (n_ < static_cast<int>(a.size())) n_ <<= 1;
        t_.assign(static_cast<size_t>(2 * n_), 0);
        std::copy(a.begin(), a.end(), t_.begin() + n_);
        for (int i = n_ - 1; i >= 1; --i) t_[i] = t_[2 * i] + t_[2 * i + 1];
    }

    void add(int i, i64 d) {                       // 0-indexed
        for (int p = i + n_; p >= 1; p >>= 1) t_[p] += d;
    }

    i64 query(int l, int r) const {                // [l, r) 半开区间
        i64 res = 0;
        for (int a = l + n_, b = r + n_; a < b; a >>= 1, b >>= 1) {
            if (a & 1) res += t_[a++];
            if (b & 1) res += t_[--b];
        }
        return res;
    }

private:
    int n_ = 1;
    std::vector<i64> t_;
};

// -----------------------------------------------------------------------------
// [2] 随机对拍
// -----------------------------------------------------------------------------
static bool stress_basic(std::mt19937& rng) {
    for (int round = 0; round < 200; ++round) {
        const int n = static_cast<int>(rng() % 64) + 1;
        std::vector<i64> a(n + 1, 0);              // 1-indexed 暴力数组
        Fenwick f;
        f.init(n);
        for (int op = 0; op < 3000; ++op) {
            if (rng() % 2 == 0) {
                const int i = static_cast<int>(rng() % n) + 1;
                const i64 d = static_cast<i64>(rng() % 201) - 100;
                a[i] += d;
                f.add(i, d);
            } else {
                int l = static_cast<int>(rng() % n) + 1;
                int r = static_cast<int>(rng() % n) + 1;
                if (l > r) std::swap(l, r);
                i64 want = 0;
                for (int i = l; i <= r; ++i) want += a[i];
                if (f.rangeSum(l, r) != want) {
                    std::printf("  [FAIL] basic: n=%d op=%d l=%d r=%d\n", n, op, l, r);
                    return false;
                }
                // 顺带校验 prefix 与 total
                i64 pref = 0;
                for (int i = 1; i <= r; ++i) pref += a[i];
                if (f.prefix(r) != pref) return false;
            }
        }
    }
    return true;
}

static bool stress_kth(std::mt19937& rng) {
    for (int round = 0; round < 200; ++round) {
        const int n = static_cast<int>(rng() % 50) + 1;
        std::vector<i64> a(n + 1, 0);
        for (int i = 1; i <= n; ++i) a[i] = static_cast<i64>(rng() % 10);   // 含 0, 考验边界
        Fenwick f;
        f.build(std::vector<i64>(a.begin() + 1, a.end()));
        const i64 tot = f.total();
        i64 chk = 0;
        for (int i = 1; i <= n; ++i) chk += a[i];
        if (tot != chk) return false;
        if (tot == 0) continue;
        for (int t = 0; t < 20; ++t) {
            const i64 k = static_cast<i64>(rng() % tot) + 1;
            i64 s = 0;
            int want = -1;
            for (int i = 1; i <= n; ++i) {
                s += a[i];
                if (s >= k) { want = i; break; }
            }
            if (f.kth(k) != want) {
                std::printf("  [FAIL] kth: n=%d k=%lld got=%d want=%d\n",
                            n, k, f.kth(k), want);
                return false;
            }
        }
    }
    return true;
}

static bool stress_range_fenwick(std::mt19937& rng) {
    for (int round = 0; round < 200; ++round) {
        const int n = static_cast<int>(rng() % 40) + 1;
        std::vector<i64> a(n + 1, 0);
        RangeFenwick rf(n);
        for (int op = 0; op < 500; ++op) {
            if (rng() % 2 == 0) {
                int l = static_cast<int>(rng() % n) + 1;
                int r = static_cast<int>(rng() % n) + 1;
                if (l > r) std::swap(l, r);
                const i64 d = static_cast<i64>(rng() % 199) - 99;
                for (int i = l; i <= r; ++i) a[i] += d;
                rf.rangeAdd(l, r, d);
            } else {
                int l = static_cast<int>(rng() % n) + 1;
                int r = static_cast<int>(rng() % n) + 1;
                if (l > r) std::swap(l, r);
                i64 want = 0;
                for (int i = l; i <= r; ++i) want += a[i];
                if (rf.rangeSum(l, r) != want) {
                    std::printf("  [FAIL] range-fenwick: n=%d l=%d r=%d\n", n, l, r);
                    return false;
                }
            }
        }
    }
    return true;
}

// -----------------------------------------------------------------------------
// [3] 性能实测
// -----------------------------------------------------------------------------
static void bench() {
    const int n = 1 << 20;      // 元素个数: 1,048,576
    const int Q = 1 << 20;      // 查询次数
    std::mt19937 rng(20261019u);

    std::vector<i64> a(static_cast<size_t>(n));
    for (auto& x : a) x = static_cast<i64>(rng() % 1000);

    // ---- 建树: O(n) 线性建树 vs n 次 add ----
    auto t0 = Clock::now();
    Fenwick fast;
    fast.build(a);
    const double tBuildFast = ms_since(t0);

    t0 = Clock::now();
    Fenwick slow;
    slow.init(n);
    for (int i = 1; i <= n; ++i) slow.add(i, a[static_cast<size_t>(i - 1)]);
    const double tBuildSlow = ms_since(t0);

    if (fast.total() != slow.total()) std::printf("  [FAIL] build mismatch\n");

    // ---- 线段树对照组 ----
    t0 = Clock::now();
    IterSegTree seg;
    seg.build(a);
    const double tBuildSeg = ms_since(t0);

    // ---- 查询: 1M 次随机前缀和 ----
    std::vector<int> qs(static_cast<size_t>(Q));
    for (auto& q : qs) q = static_cast<int>(rng() % static_cast<unsigned>(n)) + 1;

    t0 = Clock::now();
    i64 sBit = 0;
    for (int q : qs) sBit += fast.prefix(q);
    const double tQueryBit = ms_since(t0);

    t0 = Clock::now();
    i64 sSeg = 0;
    for (int q : qs) sSeg += seg.query(0, q);
    const double tQuerySeg = ms_since(t0);

    if (sBit != sSeg) std::printf("  [FAIL] query mismatch %lld vs %lld\n", sBit, sSeg);

    // ---- 更新: 1M 次随机单点加 ----
    int idx = 0;
    t0 = Clock::now();
    for (int t = 0; t < Q; ++t) fast.add((idx++ % n) + 1, 1);
    const double tUpdBit = ms_since(t0);

    idx = 0;
    t0 = Clock::now();
    for (int t = 0; t < Q; ++t) seg.add(idx++ % n, 1);
    const double tUpdSeg = ms_since(t0);

    // ---- kth: 20 万次 ----
    const int K = 200000;
    const i64 tot = fast.total();
    t0 = Clock::now();
    i64 acc = 0;
    for (int t = 0; t < K; ++t)
        acc += fast.kth(static_cast<i64>(rng() % static_cast<unsigned long long>(tot)) + 1);
    const double tKth = ms_since(t0);
    g_sink += acc + sBit;

    std::printf("\n[3] 性能实测 (n = %d, Q = %d, -O2, 单线程)\n", n, Q);
    std::printf("  %-28s %10s %10s %8s\n", "项目", "BIT", "线段树", "加速比");
    std::printf("  %-26s %10.2f %10.2f %7.2fx\n", "建树 (ms)", tBuildFast, tBuildSeg,
                tBuildSeg > 0 ? tBuildSeg / tBuildFast : 0.0);
    std::printf("  %-26s %10.2f %10.2f %7.2fx\n", "1M 次前缀和查询 (ms)", tQueryBit, tQuerySeg,
                tQueryBit > 0 ? tQuerySeg / tQueryBit : 0.0);
    std::printf("  %-26s %10.2f %10.2f %7.2fx\n", "1M 次单点加 (ms)", tUpdBit, tUpdSeg,
                tUpdBit > 0 ? tUpdSeg / tUpdBit : 0.0);
    std::printf("  %-26.26s %10.2f %10s %8s\n", "20 万次 kth (ms)", tKth, "O(log^2)", "-");
    std::printf("  (对照) n 次 add 建树 = %.2f ms, 线性建树 = %.2f ms, 加速 %.2fx\n",
                tBuildSlow, tBuildFast, tBuildFast > 0 ? tBuildSlow / tBuildFast : 0.0);
    std::printf("  校验: BIT 与线段树查询结果%s\n", sBit == sSeg ? "完全一致" : "不一致(!)");
}

int main() {
#ifdef _WIN32
    SetConsoleOutputCP(CP_UTF8);
#endif
    std::mt19937 rng(123456789u);
    std::printf("[2] 随机对拍 (暴力做法 vs 树状数组)\n");
    const bool ok1 = stress_basic(rng);
    const bool ok2 = stress_kth(rng);
    const bool ok3 = stress_range_fenwick(rng);
    std::printf("  单点加 + 区间和    : %s\n", ok1 ? "PASS" : "FAIL");
    std::printf("  倍增二分 kth       : %s\n", ok2 ? "PASS" : "FAIL");
    std::printf("  双 BIT 区间加求和  : %s\n", ok3 ? "PASS" : "FAIL");

    // 小样例人工可验算: a = {1,2,3,4,5}
    std::vector<i64> demo{1, 2, 3, 4, 5};
    Fenwick f;
    f.build(demo);
    std::printf("\n[示例] a = {1,2,3,4,5}\n");
    std::printf("  sum(2..4) = %lld (期望 9)\n", f.rangeSum(2, 4));
    std::printf("  第 8 小元素下标 = %d (期望 4)\n", f.kth(8));

    bench();
    std::printf("\n所有测试%s\n", (ok1 && ok2 && ok3) ? "通过。" : "存在失败项。");
    return (ok1 && ok2 && ok3) ? 0 : 1;
}
