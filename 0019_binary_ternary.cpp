// ============================================================
// 0019 · 二分答案与三分
//        整数二分四写法 · 二分答案建模(最大化最小/最小化最大) ·
//        实数二分精度 · 三分求单峰极值
// 考纲等级: [J]/[S]
//   [J] CSP-J 入门组：二分查找、二分答案（跳石头/切木头类）、判定函数单调性
//   [S] CSP-S / NOIP：实数二分、三分法、倍增找界、"最小化最大值"建模
// 编译: g++ -O2 -std=c++17 -Wall -Wextra -o bt 0019_binary_ternary.cpp
// 运行: ./bt    返回码 0 = 全部对拍通过；1 = 有检查点失败
//
// 结构:
//   A. Rng / check                      基础设施
//   B. lowerBoundClosed / HalfOpen /
//      MaxForm / Doubling               整数二分四写法 + 线性扫描 oracle
//   C. jumpRemoveCount / jumpStones     跳石头: 最大化最小间距 (NOIP2015)
//      bruteJump                        穷举移除子集 oracle
//      splitSegCount / minMaxSplit      数列分段: 最小化最大段和
//      dpMinMaxSplit                    O(n^2 M) DP oracle
//      woodPieces / woodCut             木材加工: 最大化切割长度
//   D. bisectSqrt / newtonSqrtIters     实数二分 vs 牛顿法
//      ropeCutReal                      实数版切绳（整数版 = woodCut）
//   E. ternaryReal / ternaryIntMin /
//      ternaryIntMax                    三分（实数 / 整数数组）
//   F. G1-G8 对拍   B1-B4 基准
//
// 本期主要断言来源（全部由不变式推导，而非"跑出来是这样"）:
//   (1) 二分每轮区间严格缩小 ⇒ 比较次数 ≤ ceil(log2(n+1))（lo=mid 形式同界）
//   (2) lo=mid 分支的 mid 必须上取整，否则区间 [x, x+1] 卡死
//   (3) 二分答案的定义式断言: check(ans) 可行 且 check(ans+1) 不可行
//   (4) 实数二分迭代数 = ceil(log2((hi-lo)/eps))；返回值误差 ≤ eps/2
//   (5) 三分每轮区间缩为 2/3 ⇒ 迭代数 ≤ log_{1.5}((hi-lo)/eps)
//   (6) 整数三分循环条件 hi-lo>2 ⇒ m1<m2 且每轮严格缩小（3 个候选交给末尾线性扫）
// ============================================================
#include <bits/stdc++.h>
#include <functional>

// ---------------------------- A. 基础设施 ----------------------------
struct Rng {
    unsigned long long s;
    explicit Rng(unsigned long long seed) : s(seed ? seed : 0x9E3779B97F4A7C15ULL) {}
    unsigned long long next() {
        s ^= s << 7;
        s ^= s >> 9;
        return s;
    }
    int nextInt(int n) { return (int)(next() % (unsigned long long)n); }
    long long nextLong(long long n) { return (long long)(next() % (unsigned long long)n); }
};

static double nowMs() {
    auto t = std::chrono::steady_clock::now().time_since_epoch();
    return (double)std::chrono::duration_cast<std::chrono::microseconds>(t).count() / 1000.0;
}

static long long g_checks = 0;
static long long g_fails = 0;

static void check(bool cond, const std::string& what) {
    ++g_checks;
    if (!cond) {
        ++g_fails;
        if (g_fails <= 40) printf("  [FAIL] %s\n", what.c_str());
    }
}

static double dAbs(double v) { return v < 0 ? -v : v; }

static long long ceilLog2(long long x) {   // x >= 1
    long long r = 0;
    while ((1LL << r) < x) ++r;
    return r;
}

// ---------------------------- B. 整数二分四写法 ----------------------------
// 升序数组 a[0..n-1]，求第一个 >= x 的下标（不存在返回 n）。
// 四种写法必须与 std::lower_bound、线性扫描完全一致。

// 写法 1: 闭区间 [lo, hi] + ans 记录（最不易错的入门写法）
static int lowerBoundClosed(const std::vector<long long>& a, long long x, long long& cmp) {
    int n = (int)a.size();
    int lo = 0, hi = n - 1, ans = n;
    while (lo <= hi) {
        int mid = lo + (hi - lo) / 2;
        ++cmp;
        if (a[(size_t)mid] >= x) { ans = mid; hi = mid - 1; }
        else lo = mid + 1;
    }
    return ans;
}

// 写法 2: 半开区间 [lo, hi)（hi=mid 分支，下取整即可）
static int lowerBoundHalfOpen(const std::vector<long long>& a, long long x, long long& cmp) {
    int n = (int)a.size();
    int lo = 0, hi = n;
    while (lo < hi) {
        int mid = lo + (hi - lo) / 2;
        ++cmp;
        if (a[(size_t)mid] < x) lo = mid + 1;
        else hi = mid;
    }
    return lo;
}

// 写法 3: 闭区间 lo=mid 形式（答案域 [0, n]，lo=mid 分支 mid 必须上取整）
// 语义: 最后一个 < x 的位置 + 1 == lower_bound
static int lowerBoundMaxForm(const std::vector<long long>& a, long long x, long long& cmp) {
    int n = (int)a.size();
    int lo = 0, hi = n;
    while (lo < hi) {
        int mid = lo + (hi - lo + 1) / 2;    // 上取整! 否则 lo==mid 时死循环
        ++cmp;
        if (a[(size_t)(mid - 1)] < x) lo = mid;
        else hi = mid - 1;
    }
    return lo;
}

// 写法 4: 倍增找界 + 区间内二分（上界未知/无限域场景的标准做法）
static int lowerBoundDoubling(const std::vector<long long>& a, long long x, long long& cmp) {
    int n = (int)a.size();
    int pos = 0, step = 1;
    while (pos + step <= n) {
        ++cmp;
        if (a[(size_t)(pos + step - 1)] < x) { pos += step; step *= 2; }
        else break;
    }
    int hi = pos + step < n ? pos + step : n;
    int lo = pos;
    while (lo < hi) {
        int mid = lo + (hi - lo) / 2;
        ++cmp;
        if (a[(size_t)mid] < x) lo = mid + 1;
        else hi = mid;
    }
    return lo;
}

static int lowerBoundScan(const std::vector<long long>& a, long long x) {
    int n = (int)a.size();
    for (int i = 0; i < n; ++i)
        if (a[(size_t)i] >= x) return i;
    return n;
}

// ---------------------------- C. 二分答案三建模 ----------------------------
// ---- C1. 跳石头 (NOIP 2015 提高组): 最大化最小间距 ----
// p[0]=0(起点) < p[1..k](可移石头) < p[k+1]=L(终点, 不可移)。
// removeCount(mid) = 把所有相邻间距(含到终点)变得 >= mid 所需移走的最少石头数。
// 贪心: 从左到右扫，间距 < mid 就移走当前块（last 不更新）。
// 终点不可移但仍在循环里"计数"——若终点间距不足，把该次移除换成
// 它前一个保留块，合并后间距只增不减，计数不变（见讲义坑#2）。
static long long jumpRemoveCount(const std::vector<long long>& p, long long mid, long long& work) {
    long long cnt = 0, last = 0;
    int n = (int)p.size();
    for (int i = 1; i < n; ++i) {        // 含终点
        ++work;
        if (p[(size_t)i] - last < mid) ++cnt;   // 移走 p[i]，last 不动
        else last = p[(size_t)i];
    }
    return cnt;
}

// 答案 = 最大的 mid 使 removeCount(mid) <= M；答案域 [0, L]
static long long jumpStones(const std::vector<long long>& p, long long M,
                            long long& calls, long long& work) {
    long long lo = 0, hi = p[(size_t)p.size() - 1];
    while (lo < hi) {
        long long mid = lo + (hi - lo + 1) / 2;   // 上取整: lo=mid 分支必须
        ++calls;
        if (jumpRemoveCount(p, mid, work) <= M) lo = mid;
        else hi = mid - 1;
    }
    return lo;
}

// oracle: 穷举全部移除子集（popcount <= M），取最小间距的最大值
static long long bruteJump(const std::vector<long long>& p, long long M) {
    int k = (int)p.size() - 2;           // 可移石头数
    long long best = 0;
    int total = 1 << k;
    for (int mask = 0; mask < total; ++mask) {
        int removed = 0;
        for (int i = 0; i < k; ++i)
            if ((mask >> i) & 1) ++removed;
        if (removed > M) continue;
        long long last = 0, mn = -1;
        for (int i = 1; i <= k + 1; ++i) {
            if (i <= k && ((mask >> (i - 1)) & 1)) continue;   // 该石头被移走
            long long gap = p[(size_t)i] - last;
            if (mn < 0 || gap < mn) mn = gap;
            last = p[(size_t)i];
        }
        if (mn > best) best = mn;
    }
    return best;
}

// ---- C2. 数列分段 Section II (洛谷 P1182): 最小化最大段和 ----
// 把 n 个正数按顺序分成不超过 M 段，最小化"最大段和"。
// segCount(mid) = 每段和都 <= mid 时贪心所需的最少段数（要求 mid >= max(a)）。
static long long splitSegCount(const std::vector<long long>& a, long long mid, long long& work) {
    long long segs = 1, sum = 0;
    int n = (int)a.size();
    for (int i = 0; i < n; ++i) {
        ++work;
        if (sum + a[(size_t)i] <= mid) sum += a[(size_t)i];
        else { ++segs; sum = a[(size_t)i]; }
    }
    return segs;
}

// 答案 = 最小的 mid 使 segCount(mid) <= M；答案域 [max(a), sum(a)]
// 坑: 下界若取 0，mid < max(a) 时贪心段数失真（讲义坑#4）
static long long minMaxSplit(const std::vector<long long>& a, long long M,
                             long long& calls, long long& work) {
    long long lo = 0, hi = 0;
    int n = (int)a.size();
    for (int i = 0; i < n; ++i) {
        hi += a[(size_t)i];
        if (a[(size_t)i] > lo) lo = a[(size_t)i];
    }
    while (lo < hi) {
        long long mid = lo + (hi - lo) / 2;       // hi=mid 分支: 下取整
        ++calls;
        if (splitSegCount(a, mid, work) <= M) hi = mid;
        else lo = mid + 1;
    }
    return lo;
}

// oracle: dp[j][i] = 前 i 个数分 j 段的最小最大段和，O(n^2 M)
static long long dpMinMaxSplit(const std::vector<long long>& a, long long M) {
    int n = (int)a.size();
    const long long INF = (1LL << 60);
    std::vector<long long> pre((size_t)n + 1, 0);
    for (int i = 1; i <= n; ++i) pre[(size_t)i] = pre[(size_t)(i - 1)] + a[(size_t)(i - 1)];
    std::vector<std::vector<long long>> dp((size_t)M + 1, std::vector<long long>((size_t)n + 1, INF));
    dp[0][0] = 0;
    for (long long j = 1; j <= M; ++j)
        for (int i = 1; i <= n; ++i)
            for (int t = 0; t < i; ++t) {
                if (dp[(size_t)(j - 1)][(size_t)t] >= INF) continue;
                long long seg = pre[(size_t)i] - pre[(size_t)t];
                long long v = dp[(size_t)(j - 1)][(size_t)t] > seg ? dp[(size_t)(j - 1)][(size_t)t] : seg;
                if (v < dp[(size_t)j][(size_t)i]) dp[(size_t)j][(size_t)i] = v;
            }
    long long best = INF;
    for (long long j = 1; j <= M; ++j)
        if (dp[(size_t)j][(size_t)n] < best) best = dp[(size_t)j][(size_t)n];
    return best;
}

// ---------------------------- C3. 木材加工 (洛谷 P2440): 最大化切割长度 ----
static long long g_work_dummy = 0;

// n 段原木长 L[i]，每段切成长 k 的小段得 floor(L[i]/k) 段，总段数需 >= K。
// pieces(k) 关于 k 单调不增；答案 = 最大的可行 k（全不可行则为 0）。
static long long woodPieces(const std::vector<long long>& L, long long k, long long& work) {
    long long s = 0;
    int n = (int)L.size();
    for (int i = 0; i < n; ++i) { ++work; s += L[(size_t)i] / k; }
    return s;
}

static long long woodCut(const std::vector<long long>& L, long long K,
                         long long& calls, long long& work) {
    long long lo = 0, hi = 0;
    int n = (int)L.size();
    for (int i = 0; i < n; ++i)
        if (L[(size_t)i] > hi) hi = L[(size_t)i];
    while (lo < hi) {
        long long mid = lo + (hi - lo + 1) / 2;   // 上取整（lo=mid 分支），mid >= 1 恒成立
        ++calls;
        if (woodPieces(L, mid, work) >= K) lo = mid;
        else hi = mid - 1;
    }
    return lo;
}

static long long woodCutScan(const std::vector<long long>& L, long long K) {
    long long hi = 0;
    int n = (int)L.size();
    for (int i = 0; i < n; ++i)
        if (L[(size_t)i] > hi) hi = L[(size_t)i];
    for (long long k = hi; k >= 1; --k)
        if (woodPieces(L, k, g_work_dummy) >= K) return k;
    return 0;
}

// ---------------------------- D. 实数二分 ----------------------------
static long long g_lastItersBound = 0;

// sqrt 的实数二分: cond(v) = v*v >= x，域 [0, max(1,x)]
// 坑: hi 若取 x，当 x<1 时 sqrt(x)>x，答案根本不在域内（讲义坑#6）
static double bisectSqrt(double x, double eps, long long& iters) {
    double lo = 0.0, hi = x > 1.0 ? x : 1.0;
    double lo0 = lo, hi0 = hi;
    iters = 0;
    while (hi - lo > eps) {
        double mid = lo + (hi - lo) / 2;
        ++iters;
        if (mid * mid >= x) hi = mid;
        else lo = mid;
    }
    g_lastItersBound = ceilLog2((long long)((hi0 - lo0) / eps)) + 2;
    return (lo + hi) / 2;
}

static long long newtonSqrtIters(double x, double eps) {
    double v = x > 1.0 ? x : 1.0;
    long long it = 0;
    while (dAbs(v * v - x) > eps * (x > 1.0 ? x : 1.0) && it < 200) {
        v = (v + x / v) / 2.0;
        ++it;
    }
    return it;
}

// 实数版切绳: n 条绳长 l[i]，剪成 K 段（每段长 t，floor(l[i]/t) 段），最大化 t。
// 精确答案必是某个 l[i]/j（可行性只在 li/j 处变化），可作 oracle。
static double ropeCutReal(const std::vector<double>& l, long long K, double eps, long long& iters) {
    double lo = 0.0, hi = 0.0;
    int n = (int)l.size();
    for (int i = 0; i < n; ++i)
        if (l[(size_t)i] > hi) hi = l[(size_t)i];
    hi += 1.0;    // 坑: hi 必须留余量——单绳 K=1 时答案恰为 maxL，hi=maxL 只能从下方逼近
    iters = 0;
    while (hi - lo > eps) {
        double mid = lo + (hi - lo) / 2;
        ++iters;
        long long pieces = 0;
        for (int i = 0; i < n; ++i) pieces += (long long)std::floor(l[(size_t)i] / mid);
        if (pieces >= K) lo = mid;
        else hi = mid;
    }
    return (lo + hi) / 2;
}

// ---------------------------- E. 三分 ----------------------------
// 实数三分求单峰极值。isMin=true 时 f(m1)<=f(m2) ⇒ 极值在 [lo, m2]。
// 每轮区间缩为 2/3，迭代数 <= log_{1.5}((hi-lo)/eps)。
static double ternaryReal(const std::function<double(double)>& f, double lo, double hi,
                          double eps, bool isMin, long long& evals) {
    while (hi - lo > eps) {
        double m1 = lo + (hi - lo) / 3.0;
        double m2 = hi - (hi - lo) / 3.0;
        double v1 = f(m1), v2 = f(m2);
        evals += 2;
        if (isMin ? v1 <= v2 : v1 >= v2) hi = m2;
        else lo = m1;
    }
    return (lo + hi) / 2;
}

// 整数三分求谷底（严格单峰数组，先严格递减后严格递增）
// 循环条件 hi-lo>2 保证 m1<m2 且每轮严格缩小；剩余 <=3 个候选交给末尾线性扫
static int ternaryIntMin(const std::vector<long long>& a, long long& evals) {
    int lo = 0, hi = (int)a.size() - 1;
    while (hi - lo > 2) {
        int m1 = lo + (hi - lo) / 3;
        int m2 = hi - (hi - lo) / 3;
        ++evals;
        if (a[(size_t)m1] <= a[(size_t)m2]) hi = m2;
        else lo = m1;
    }
    int best = lo;
    for (int i = lo + 1; i <= hi; ++i)
        if (a[(size_t)i] < a[(size_t)best]) best = i;
    return best;
}

static int ternaryIntMax(const std::vector<long long>& a, long long& evals) {
    int lo = 0, hi = (int)a.size() - 1;
    while (hi - lo > 2) {
        int m1 = lo + (hi - lo) / 3;
        int m2 = hi - (hi - lo) / 3;
        ++evals;
        if (a[(size_t)m1] >= a[(size_t)m2]) hi = m2;
        else lo = m1;
    }
    int best = lo;
    for (int i = lo + 1; i <= hi; ++i)
        if (a[(size_t)i] > a[(size_t)best]) best = i;
    return best;
}

// 严格"谷型"数组: a[i] = 2*(i-t)^2 + |i-t|，t 为谷底（先严格减后严格增）
static std::vector<long long> makeValley(Rng& rng, int n) {
    int t = rng.nextInt(n);
    std::vector<long long> a((size_t)n);
    for (int i = 0; i < n; ++i) {
        long long d = i - t;
        if (d < 0) d = -d;
        a[(size_t)i] = 2 * d * d + d;
    }
    return a;
}

static std::vector<long long> makePeak(Rng& rng, int n) {
    int t = rng.nextInt(n);
    std::vector<long long> a((size_t)n);
    for (int i = 0; i < n; ++i) {
        long long d = i - t;
        if (d < 0) d = -d;
        a[(size_t)i] = -(2 * d * d + d);
    }
    return a;
}

// ---------------------------- F1. G 组对拍 ----------------------------
static void g1_integer_bound() {
    Rng rng(20190019);
    // 小数组穷举: n=1..8, 值域 [0,20], 查询 x=0..25 全覆盖
    for (int trial = 0; trial < 300; ++trial) {
        int n = 1 + rng.nextInt(8);
        std::vector<long long> a((size_t)n);
        for (int i = 0; i < n; ++i) a[(size_t)i] = rng.nextInt(21);
        std::sort(a.begin(), a.end());
        for (long long x = 0; x <= 25; ++x) {
            long long c1 = 0, c2 = 0, c3 = 0;
            int r0 = lowerBoundScan(a, x);
            int r1 = lowerBoundClosed(a, x, c1);
            int r2 = lowerBoundHalfOpen(a, x, c2);
            int r3 = lowerBoundMaxForm(a, x, c3);
            int rStd = (int)(std::lower_bound(a.begin(), a.end(), x) - a.begin());
            check(r1 == r0 && r2 == r0 && r3 == r0 && rStd == r0,
                  "G1 lower_bound 四写法不一致 n=" + std::to_string(n) + " x=" + std::to_string(x));
            long long bound = ceilLog2(n + 1) + 2;
            check(c1 <= bound && c2 <= bound && c3 <= bound,
                  "G1 比较次数超界 n=" + std::to_string(n));
        }
    }
    // 大数组随机查询
    for (int trial = 0; trial < 20; ++trial) {
        int n = 2000;
        std::vector<long long> a((size_t)n);
        for (int i = 0; i < n; ++i) a[(size_t)i] = rng.nextLong(1000000);
        std::sort(a.begin(), a.end());
        for (int q = 0; q < 100; ++q) {
            long long x = rng.nextLong(1000010) - 5;
            long long c1 = 0, c2 = 0, c3 = 0;
            int r0 = lowerBoundScan(a, x);
            int r1 = lowerBoundClosed(a, x, c1);
            int r2 = lowerBoundHalfOpen(a, x, c2);
            int r3 = lowerBoundMaxForm(a, x, c3);
            check(r1 == r0 && r2 == r0 && r3 == r0, "G1 大数组四写法不一致");
        }
    }
    printf("  G1 整数二分四写法 vs 扫描/std::lower_bound + 比较次数上界: OK\n");
}

static void g2_doubling() {
    Rng rng(20190020);
    for (int trial = 0; trial < 40; ++trial) {
        int n = 1 + rng.nextInt(2000);
        std::vector<long long> a((size_t)n);
        for (int i = 0; i < n; ++i) a[(size_t)i] = rng.nextLong(1000000);
        std::sort(a.begin(), a.end());
        for (int q = 0; q < 30; ++q) {
            long long x = rng.nextLong(1000010) - 5;
            long long c = 0;
            int r = lowerBoundDoubling(a, x, c);
            int r0 = lowerBoundScan(a, x);
            check(r == r0, "G2 倍增找界结果不一致");
            // 复杂度断言: 倍增 <= log2(n) + 区间二分 <= log2(n) => 2*log2 + 常数
            long long bound = 2 * ceilLog2(n + 1) + 8;
            check(c <= bound,
                  "G2 倍增比较次数超界 c=" + std::to_string(c) +
                  " bound=" + std::to_string(bound));
        }
    }
    printf("  G2 倍增找界 vs 扫描 + cmp<=2log2(n)+8: OK\n");
}

static void g3_jump_stones() {
    Rng rng(20190021);
    // 固定构造: 终点间距不足时"计数等价"的关键用例
    {
        std::vector<long long> p = {0, 5, 6};
        long long calls = 0, work = 0;
        long long ans = jumpStones(p, 1, calls, work);
        check(ans == bruteJump(p, 1), "G3 固定用例 p=[0,5,6] 失败");
    }
    for (int trial = 0; trial < 150; ++trial) {
        int k = rng.nextInt(11);                        // 可移石头 0..10
        long long L = 5 + rng.nextLong(60);
        long long M = rng.nextInt(5);
        std::vector<long long> p;
        p.push_back(0);
        for (int i = 0; i < k; ++i) {
            long long v = 1 + rng.nextLong(L - 1);
            p.push_back(v);
        }
        p.push_back(L);
        std::sort(p.begin(), p.end());
        p.erase(std::unique(p.begin(), p.end()), p.end());
        p[(size_t)0] = 0;
        p[(size_t)p.size() - 1] = L;                    // 保证起点 0 / 终点 L 恰好各一个
        long long calls = 0, work = 0;
        long long ans = jumpStones(p, M, calls, work);
        long long br = bruteJump(p, M);
        check(ans == br,
              "G3 跳石头 vs 穷举不一致 ans=" + std::to_string(ans) +
              " brute=" + std::to_string(br));
        check(calls <= ceilLog2(L + 1) + 4, "G3 check 调用次数超界");
    }
    // 大案例 + 定义式断言: check(ans) 可行 且 check(ans+1) 不可行
    {
        Rng rng2(20190022);
        long long L = 1000000000LL;
        std::vector<long long> p;
        p.push_back(0);
        for (int i = 0; i < 5000; ++i) p.push_back(1 + rng2.nextLong(L - 1));
        std::sort(p.begin(), p.end());
        p.erase(std::unique(p.begin(), p.end()), p.end());
        p[(size_t)0] = 0;
        p[(size_t)p.size() - 1] = L;
        long long M = 100;
        long long calls = 0, work = 0;
        long long ans = jumpStones(p, M, calls, work);
        long long w1 = 0, w2 = 0;
        check(jumpRemoveCount(p, ans, w1) <= M, "G3 定义式断言 check(ans) 应可行");
        check(jumpRemoveCount(p, ans + 1, w2) > M, "G3 定义式断言 check(ans+1) 应不可行");
        check(calls <= 40, "G3 大案例 check 调用次数超界");
        printf("  G3 大案例: k=%d M=%lld ans=%lld check调用=%lld work=%lld\n",
               (int)p.size() - 2, M, ans, calls, work);
    }
    printf("  G3 跳石头 vs 穷举 150 组 + 定义式断言: OK\n");
}

static void g4_min_max_split() {
    Rng rng(20190023);
    // 固定构造: 下界必须取 max(a) 的关键用例
    {
        std::vector<long long> a = {10, 1, 1, 1};
        long long calls = 0, work = 0;
        check(minMaxSplit(a, 3, calls, work) == 10, "G4 固定用例 [10,1,1,1] M=3 应为 10");
    }
    for (int trial = 0; trial < 100; ++trial) {
        int n = 1 + rng.nextInt(12);
        long long M = 1 + rng.nextLong(n);
        std::vector<long long> a((size_t)n);
        for (int i = 0; i < n; ++i) a[(size_t)i] = 1 + rng.nextLong(50);
        long long calls = 0, work = 0;
        long long ans = minMaxSplit(a, M, calls, work);
        long long dp = dpMinMaxSplit(a, M);
        check(ans == dp,
              "G4 数列分段 vs DP 不一致 ans=" + std::to_string(ans) +
              " dp=" + std::to_string(dp));
        check(calls <= ceilLog2(12LL * 50 + 1) + 4, "G4 check 调用次数超界");
    }
    // 大案例 + 定义式断言
    {
        Rng rng2(20190024);
        int n = 100000;
        std::vector<long long> a((size_t)n);
        for (int i = 0; i < n; ++i) a[(size_t)i] = 1 + rng2.nextLong(1000);
        long long M = 50;
        long long calls = 0, work = 0;
        long long ans = minMaxSplit(a, M, calls, work);
        long long w1 = 0, w2 = 0;
        long long mx = 0;
        for (int i = 0; i < n; ++i) if (a[(size_t)i] > mx) mx = a[(size_t)i];
        check(splitSegCount(a, ans, w1) <= M, "G4 定义式断言 check(ans) 应可行");
        if (ans - 1 >= mx)
            check(splitSegCount(a, ans - 1, w2) > M, "G4 定义式断言 check(ans-1) 应不可行");
        check(calls <= 40, "G4 大案例 check 调用次数超界");
        printf("  G4 大案例: n=%d M=%lld ans=%lld check调用=%lld\n", n, M, ans, calls);
    }
    printf("  G4 数列分段 vs DP 100 组 + 定义式断言: OK\n");
}

static void g5_wood_cut() {
    Rng rng(20190025);
    // 固定用例: 全不可行 => 答案 0
    {
        std::vector<long long> L = {3};
        long long calls = 0, work = 0;
        check(woodCut(L, 5, calls, work) == 0, "G5 固定用例 [3] K=5 应为 0");
    }
    for (int trial = 0; trial < 100; ++trial) {
        int n = 1 + rng.nextInt(8);
        long long K = 1 + rng.nextLong(40);
        std::vector<long long> L((size_t)n);
        for (int i = 0; i < n; ++i) L[(size_t)i] = 1 + rng.nextLong(60);
        long long calls = 0, work = 0;
        long long ans = woodCut(L, K, calls, work);
        long long scan = woodCutScan(L, K);
        check(ans == scan,
              "G5 木材加工 vs 线性扫描不一致 ans=" + std::to_string(ans) +
              " scan=" + std::to_string(scan));
        check(calls <= ceilLog2(61) + 4, "G5 check 调用次数超界");
    }
    printf("  G5 木材加工 vs 线性扫描 100 组（含答案 0）: OK\n");
}

static double g_exactRopeAnswer(const std::vector<double>& l, long long K) {
    // 精确 oracle: 答案必是某个 l[i]/j；用 long double 求 floor，容差防浮点抖动
    double best = 0.0;
    int n = (int)l.size();
    for (int i = 0; i < n; ++i)
        for (long long j = 1; j <= K; ++j) {
            double t = l[(size_t)i] / (double)j;
            long long pieces = 0;
            for (int q = 0; q < n; ++q)
                pieces += (long long)std::floor(l[(size_t)q] / t + 1e-9);
            if (pieces >= K && t > best) best = t;
        }
    return best;
}

static void g6_real_bisect() {
    const double xs[6] = {0.25, 0.5, 0.81, 2.0, 9.0, 12345.678};
    for (int i = 0; i < 6; ++i) {
        double x = xs[i];
        long long iters = 0;
        double r = bisectSqrt(x, 1e-9, iters);
        double ref = std::sqrt(x);
        check(dAbs(r - ref) <= 1e-7,
              "G6 sqrt 二分误差过大 x=" + std::to_string(x));
        check(iters <= g_lastItersBound,
              "G6 sqrt 二分迭代数超界 iters=" + std::to_string(iters));
    }
    // 实数切绳 vs 精确 oracle
    {
        std::vector<double> l = {3.5, 4.7, 2.9, 8.1, 6.6};
        long long K = 7;
        long long iters = 0;
        double ans = ropeCutReal(l, K, 1e-9, iters);
        double exact = g_exactRopeAnswer(l, K);
        check(dAbs(ans - exact) <= 1e-6,
              "G6 切绳 vs 精确 oracle 不一致");
        check(iters <= 60, "G6 切绳迭代数超界");
    }
    // 单绳 K=1: 答案恰为绳长（hi 余量用例）
    {
        std::vector<double> l = {5.0};
        long long iters = 0;
        double ans = ropeCutReal(l, 1, 1e-9, iters);
        check(dAbs(ans - 5.0) <= 1e-6, "G6 单绳 K=1 应得绳长本身");
    }
    long long itB = 0, itN = 0;
    bisectSqrt(2.0, 1e-12, itB);
    itN = newtonSqrtIters(2.0, 1e-12);
    printf("  G6 sqrt(2) eps=1e-12: 二分 %lld 轮 vs 牛顿 %lld 轮: OK\n", itB, itN);
}

static void g7_int_ternary() {
    Rng rng(20190026);
    for (int trial = 0; trial < 200; ++trial) {
        int n = 1 + rng.nextInt(50);
        std::vector<long long> v = makeValley(rng, n);
        long long ev = 0;
        int got = ternaryIntMin(v, ev);
        int want = 0;
        for (int i = 1; i < n; ++i)
            if (v[(size_t)i] < v[(size_t)want]) want = i;
        check(got == want,
              "G7 整数三分谷底不一致 n=" + std::to_string(n) +
              " got=" + std::to_string(got) + " want=" + std::to_string(want));
        check(ev <= 3 * ceilLog2(n + 2) + 6, "G7 三分迭代数超界");
        std::vector<long long> pk = makePeak(rng, n);
        ev = 0;
        got = ternaryIntMax(pk, ev);
        want = 0;
        for (int i = 1; i < n; ++i)
            if (pk[(size_t)i] > pk[(size_t)want]) want = i;
        check(got == want, "G7 整数三分峰顶不一致");
    }
    // 边界: n=1,2,3
    for (int n = 1; n <= 3; ++n) {
        std::vector<long long> v = makeValley(rng, n);
        long long ev = 0;
        int got = ternaryIntMin(v, ev);
        int want = 0;
        for (int i = 1; i < n; ++i)
            if (v[(size_t)i] < v[(size_t)want]) want = i;
        check(got == want, "G7 边界 n<=3 失败");
    }
    printf("  G7 整数三分 vs 线性扫描 200 组 + n<=3 边界: OK\n");
}

static void g8_real_ternary() {
    long long ev = 0;
    double r = ternaryReal([](double x) { return (x - 3.7) * (x - 3.7) + 1.0; },
                           0.0, 9.0, 1e-9, true, ev);
    check(dAbs(r - 3.7) <= 1e-6, "G8 f1 极小点应为 3.7");
    ev = 0;
    r = ternaryReal([](double x) { return -(x + 1.3) * (x + 1.3) + 5.0; },
                    -6.0, 4.0, 1e-9, false, ev);
    check(dAbs(r + 1.3) <= 1e-6, "G8 f2 极大点应为 -1.3");
    // 非对称严格单峰: f'(x) = (x-2)(2 + 0.3(x-2))，另一驻点 -4.67 在域外
    ev = 0;
    r = ternaryReal([](double x) {
        double d = x - 2.0;
        return d * d * (1.0 + 0.1 * d);
    }, -2.0, 6.0, 1e-9, true, ev);
    check(dAbs(r - 2.0) <= 1e-6, "G8 非对称单峰极小点应为 2");
    // 迭代数上界: log_{1.5}((hi-lo)/eps)，每次迭代 2 次求值
    long long ev2 = 0;
    ternaryReal([](double x) { return (x - 3.7) * (x - 3.7); },
                0.0, 1e9, 1e-9, true, ev2);
    double need = log(1e9 / 1e-9) / log(1.5);
    check(ev2 <= 2 * (long long)need + 8, "G8 三分求值次数超界");
    printf("  G8 实数三分解析解对照 + 求值次数上界(1e9/1e-9 -> %lld 次): OK\n", ev2);
}

// ---------------------------- F2. B 组基准 ----------------------------
static void b1_sorted_array() {
    Rng rng(20190027);
    int n = 200000;
    std::vector<long long> a((size_t)n);
    for (int i = 0; i < n; ++i) a[(size_t)i] = rng.nextLong(400000);
    std::sort(a.begin(), a.end());
    int Q = 20000;
    double t0 = nowMs();
    long long cmpSum = 0;
    long long acc = 0;
    for (int q = 0; q < Q; ++q) {
        long long x = rng.nextLong(400010) - 5;
        long long c = 0;
        acc += lowerBoundClosed(a, x, c);
        cmpSum += c;
    }
    double tBin = nowMs() - t0;
    t0 = nowMs();
    long long scanSum = 0;
    for (int q = 0; q < Q; ++q) {
        long long x = (long long)(q * 7919 % 400010) - 5;
        scanSum += lowerBoundScan(a, x);
    }
    double tScan = nowMs() - t0;
    double avgCmp = (double)cmpSum / Q;
    check(avgCmp <= 2 * (double)ceilLog2(n + 1) + 4, "B1 平均比较次数超界");
    printf("  B1 n=%d Q=%d: 二分平均比较 %.2f 次 / %.2f ms；线性扫描合计 %.2f ms\n",
           n, Q, avgCmp, tBin, tScan);
}

static void b2_jump_big() {
    Rng rng(20190028);
    long long L = 1000000000LL;
    std::vector<long long> p;
    p.push_back(0);
    for (int i = 0; i < 50000; ++i) p.push_back(1 + rng.nextLong(L - 1));
    std::sort(p.begin(), p.end());
    p.erase(std::unique(p.begin(), p.end()), p.end());
    p[(size_t)0] = 0;
    p[(size_t)p.size() - 1] = L;
    long long calls = 0, work = 0;
    double t0 = nowMs();
    long long ans = jumpStones(p, 500, calls, work);
    double ms = nowMs() - t0;
    check(calls <= 40, "B2 check 调用次数超界");
    printf("  B2 跳石头 n=%d L=1e9: ans=%lld, check 调用 %lld 次, 总工作量 %lld, %.2f ms\n",
           (int)p.size() - 2, ans, calls, work, ms);
}

static void b3_real_eps() {
    printf("  B3 sqrt(2) 二分迭代数随 eps:");
    long long prev = -1;
    for (double eps = 1e-3; eps >= 1e-12 + 1e-13; eps /= 10.0) {
        long long it = 0;
        bisectSqrt(2.0, eps, it);
        printf(" %.0e:%lld", eps, it);
        check(prev < 0 || it >= prev, "B3 迭代数应随 eps 减小而不减");
        prev = it;
    }
    printf("\n");
    long long itB = 0, itN = newtonSqrtIters(2.0, 1e-12);
    bisectSqrt(2.0, 1e-12, itB);
    check(itN < itB, "B3 牛顿法迭代数应少于二分");
    printf("  B3 eps=1e-12: 二分 %lld 轮 vs 牛顿 %lld 轮\n", itB, itN);
}

static void b4_ternary_big() {
    long long ev = 0;
    double t0 = nowMs();
    double r = ternaryReal([](double x) { return (x - 3.7) * (x - 3.7); },
                           0.0, 1e9, 1e-9, true, ev);
    double ms = nowMs() - t0;
    check(dAbs(r - 3.7) <= 1e-6, "B4 大区间三分结果错误");
    double need = log(1e9 / 1e-9) / log(1.5);
    check(ev <= 2 * (long long)need + 8, "B4 求值次数超界");
    printf("  B4 三分域长 1e9 eps=1e-9: 极值点 %.7f, 求值 %lld 次 (理论上界 %.0f), %.2f ms\n",
           r, ev, 2 * need, ms);
}

// ---------------------------- main ----------------------------
int main() {
    printf("=== 0019 二分答案与三分 · 对拍与基准 ===\n");

    g1_integer_bound();
    g2_doubling();
    g3_jump_stones();
    g4_min_max_split();
    g5_wood_cut();
    g6_real_bisect();
    g7_int_ternary();
    g8_real_ternary();

    b1_sorted_array();
    b2_jump_big();
    b3_real_eps();
    b4_ternary_big();

    printf("--- 检查点 %lld，失败 %lld ---\n", g_checks, g_fails);
    if (g_fails == 0) {
        printf("RESULT: ALL PASS\n");
        return 0;
    }
    printf("RESULT: FAILED\n");
    return 1;
}
