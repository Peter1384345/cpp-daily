// ============================================================
// 0010 · 分块 / 莫队算法 (Sqrt Decomposition / Mo's Algorithm)
// ------------------------------------------------------------
// 三个核心结构 + 一组实证:
//   A. SqrtBlocks   分块: 区间加 + 区间求和 + 单点赋值
//                   "块内聚合 + 块级 lazy + 散块暴力" 三件套
//                   —— 与 0002 线段树同题不同构: O(sqrt n) vs O(log n)
//   B. MoDistinct   莫队: 静态区间 distinct 数
//                   离线排序使指针总移动量均摊 O((n+q)·sqrt(n)),
//                   含奇偶块排序(偶块 r 升序 / 奇块 r 降序)常数优化
//   C. MoWithUpdate 带修莫队: 加"时间维"的 (l, r, t) 三维莫队
//                   块长取 n^(2/3), 总代价 O(n^(5/3))
//   D. 基准         ① 块大小 B 扫描: 实测 O(B + n/B) 拐点在 sqrt(n) 附近
//                   ② 莫队: 普通排序 vs 奇偶排序的指针移动量对比
//                   ③ 带修莫队: n^(5/3) 规模实测
// 正确性: G1 分块 vs 暴力逐操作(加/赋值/和 + bsum 不变式自检);
//         G2 莫队(普通/奇偶) vs 每查询暴力, 三种值域分布;
//         G3 带修莫队 vs 暴力重放时间线; G4 边界专项(含时间倒流);
//         G5 确定性操作序列下的 touch 计数拐点断言
// 编译:   g++ -O2 -std=c++17 -Wall -Wextra 0010_sqrt_mo.cpp -o 0010
// 注意:   本期源码未在本机编译(环境无 C++ 编译器); 算法逻辑经 Python 逐行镜像
//         (.verify_mirror_0010.py) 随机对拍验证, 详见 0010_sqrt_mo.md
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

static int isqrtI(long long x) {
    if (x <= 0) return 0;
    long long r = (long long)sqrt((double)x);
    while (r > 0 && r * r > x) --r;
    while ((r + 1) * (r + 1) <= x) ++r;
    return (int)r;
}

static void report(const char* name, int base) {
    printf("  => %s: %s\n", name, g_fail == base ? "PASS" : "FAIL");
}

// ============================================================
// A. SqrtBlocks —— 分块: 区间加 / 区间和 / 单点赋值
//
// 真实值 a[i] = v[i] + blazy[i / B];
// bsum[b] = 块 b 内 v[] 的原始和(不含 blazy) —— 永远与 v 同步维护。
//   整块加: 只动 blazy[b], O(1);  查询时补 blazy[b] * 块长
//   散块:   逐元素动 v 与 bsum, O(B)
// touch 计数器统计"元素级工作量", 用于实证 O(B + n/B) 的拐点。
// ============================================================
class SqrtBlocks {
public:
    int n = 0, B = 1, nb = 0;
    long long touch = 0;
    vector<long long> v, bsum, blazy;

    explicit SqrtBlocks(const vector<long long>& a, int forceB = 0) {
        n = (int)a.size();
        B = forceB > 0 ? forceB : max(1, isqrtI(max(n, 1)));
        if (B > max(n, 1)) B = max(n, 1);
        nb = (n + B - 1) / B;
        v = a;
        bsum.assign(nb, 0);
        blazy.assign(nb, 0);
        for (int i = 0; i < n; ++i) bsum[i / B] += v[i];
    }

    int blockLen(int b) const { return min((b + 1) * B, n) - b * B; }
    long long at(int i) const { return v[i] + blazy[i / B]; }

    void rangeAdd(int l, int r, long long d) {
        int bl = l / B, br = r / B;
        if (bl == br) {
            for (int i = l; i <= r; ++i) { v[i] += d; bsum[bl] += d; }
            touch += r - l + 1;
            return;
        }
        for (int i = l; i < (bl + 1) * B; ++i) { v[i] += d; bsum[bl] += d; }
        touch += (bl + 1) * B - l;
        for (int b = bl + 1; b < br; ++b) blazy[b] += d;
        touch += br - bl - 1;
        for (int i = br * B; i <= r; ++i) { v[i] += d; bsum[br] += d; }
        touch += r - br * B + 1;
    }

    long long rangeSum(int l, int r) {
        int bl = l / B, br = r / B;
        long long s = 0;
        if (bl == br) {
            for (int i = l; i <= r; ++i) s += v[i] + blazy[bl];
            touch += r - l + 1;
            return s;
        }
        for (int i = l; i < (bl + 1) * B; ++i) s += v[i] + blazy[bl];
        touch += (bl + 1) * B - l;
        for (int b = bl + 1; b < br; ++b) {
            s += bsum[b] + blazy[b] * (long long)blockLen(b);
            ++touch;  // 整块是 O(1) 工作, 只计 1
        }
        for (int i = br * B; i <= r; ++i) s += v[i] + blazy[br];
        touch += r - br * B + 1;
        return s;
    }

    void pointSet(int i, long long nv) {
        long long d = nv - at(i);
        if (d != 0) rangeAdd(i, i, d);
    }

    // 不变式自检: bsum 与 v 严格同步
    bool selfCheck() const {
        if ((int)bsum.size() != nb || (int)blazy.size() != nb) return false;
        for (int b = 0; b < nb; ++b) {
            long long s = 0;
            for (int i = b * B; i < min((b + 1) * B, n); ++i) s += v[i];
            if (s != bsum[b]) return false;
        }
        return true;
    }
};

// ============================================================
// B. MoDistinct —— 莫队: 静态区间 distinct 数
//
// 离线算法: 把 q 个查询按 (l 所在块, r) 排序,
// 维护双指针 [curL, curR] 与 cnt[] 直方图, 每步 add/del O(1)。
// 块长取 n / sqrt(q) 时总移动量 O(n·sqrt(q)) —— 均摊分析:
//   l 指针: 每块内最多 B 次 + 跨块 O(n), 共 O(q·B + n)
//   r 指针: 每块内单调扫 O(n), 共 n·(n/B) 块 → O(n^2/B)
//   平衡 B = n/sqrt(q) → O(n·sqrt(q) + q) ≈ O((n+q)·sqrt(n))
// 奇偶优化: 偶数块 r 升序、奇数块 r 降序, 消除跨块时的折返。
// ============================================================
struct MoQuery { int l, r, id; };

class MoDistinct {
public:
    // parity=false 普通排序; parity=true 奇偶块排序
    // moves 输出指针总移动次数(可空); 返回按 id 索引的答案
    static vector<long long> solve(const vector<int>& a, vector<MoQuery> qs,
                                   bool parity, unsigned long long* moves) {
        int n = (int)a.size();
        int q = (int)qs.size();
        vector<long long> ans(q, 0);
        if (q == 0) return ans;
        if (moves) *moves = 0;
        // distinct 只关心相等关系 → 值域压缩
        vector<int> vals(a);
        sort(vals.begin(), vals.end());
        vals.erase(unique(vals.begin(), vals.end()), vals.end());
        vector<int> c(n);
        for (int i = 0; i < n; ++i)
            c[i] = (int)(lower_bound(vals.begin(), vals.end(), a[i]) - vals.begin());
        int m = (int)vals.size();
        int B = n;
        if (q > 1) B = max(1, (int)((double)n / sqrt((double)q) + 0.5));
        if (B > n) B = n;
        sort(qs.begin(), qs.end(), [B, parity](const MoQuery& x, const MoQuery& y) {
            int bx = x.l / B, by = y.l / B;
            if (bx != by) return bx < by;
            if (parity && (bx & 1)) return x.r > y.r;  // 奇块降序
            return x.r < y.r;
        });
        vector<int> cnt(m, 0);
        long long cur = 0;
        int curL = 0, curR = -1;
        unsigned long long mv = 0;
        auto add = [&](int i) { if (cnt[c[i]]++ == 0) ++cur; };
        auto del = [&](int i) { if (--cnt[c[i]] == 0) --cur; };
        for (const MoQuery& Q : qs) {
            // 顺序固定: 先扩后缩 —— 保证过程中区间非空(答案不经过空档)
            while (curL > Q.l) { add(--curL); ++mv; }
            while (curR < Q.r) { add(++curR); ++mv; }
            while (curL < Q.l) { del(curL++); ++mv; }
            while (curR > Q.r) { del(curR--); ++mv; }
            ans[Q.id] = cur;
        }
        if (moves) *moves = mv;
        return ans;
    }
};

// ============================================================
// C. MoWithUpdate —— 带修莫队: (l, r, t) 三维
//
// 每个查询多一维 t = "查询时已生效的修改数"。
// 排序键 (l/B, r/B, t), 块长取 n^(2/3):
//   l 移动 O(q·B)  r 移动 O((n/B)·(n/B)·B) = O(n^2/B)
//   t 移动 O((n/B)^2 · 修改总数)…… 经典结论: B = n^(2/3) 时
//   三项平衡于 O(n^(5/3))。
// 时间指针 curT 只能向前 apply / 向后 revert, revert = apply 的逆。
// ============================================================
struct MoUQuery { int l, r, t, id; };
struct MoUUpdate { int pos, nv, ov; };

class MoWithUpdate {
public:
    static vector<long long> solve(const vector<int>& a0, vector<MoUQuery> qs,
                                   const vector<pair<int, int>>& rawUps,
                                   unsigned long long* moves) {
        int n = (int)a0.size();
        int q = (int)qs.size();
        vector<long long> ans(q, 0);
        if (q == 0) return ans;
        if (moves) *moves = 0;
        // 时间线: 第 i 次修改把 a[pos] 从 ov 改成 nv
        vector<int> arr(a0);
        vector<MoUUpdate> ups(rawUps.size());
        for (size_t i = 0; i < rawUps.size(); ++i) {
            int pos = rawUps[i].first, nv = rawUps[i].second;
            ups[i] = {pos, nv, arr[pos]};
            arr[pos] = nv;
        }
        // 值域压缩必须覆盖 初始值 ∪ 所有修改后的值
        vector<int> vals(a0);
        for (const MoUUpdate& u : ups) vals.push_back(u.nv);
        sort(vals.begin(), vals.end());
        vals.erase(unique(vals.begin(), vals.end()), vals.end());
        auto cid = [&](int x) {
            return (int)(lower_bound(vals.begin(), vals.end(), x) - vals.begin());
        };
        vector<int> c(n);
        for (int i = 0; i < n; ++i) c[i] = cid(a0[i]);
        // B = n^(2/3) (向下取整, 至少 1)
        int B = max(1, (int)pow((double)max(n, 1), 2.0 / 3.0));
        if (B > n) B = n;
        sort(qs.begin(), qs.end(), [B](const MoUQuery& x, const MoUQuery& y) {
            int bx = x.l / B, by = y.l / B;
            if (bx != by) return bx < by;
            int rx = x.r / B, ry = y.r / B;
            if (rx != ry) return rx < ry;
            return x.t < y.t;
        });
        int m = (int)vals.size();
        vector<int> cnt(m, 0);
        long long cur = 0;
        int curL = 0, curR = -1, curT = 0;
        unsigned long long mv = 0;
        auto addIdx = [&](int i) { if (cnt[c[i]]++ == 0) ++cur; };
        auto delIdx = [&](int i) { if (--cnt[c[i]] == 0) --cur; };
        auto applyUp = [&](const MoUUpdate& u) {
            if (curL <= u.pos && u.pos <= curR) {
                if (--cnt[c[u.pos]] == 0) --cur;
                if (cnt[cid(u.nv)]++ == 0) ++cur;
            }
            c[u.pos] = cid(u.nv);
        };
        auto revertUp = [&](const MoUUpdate& u) {
            if (curL <= u.pos && u.pos <= curR) {
                if (--cnt[c[u.pos]] == 0) --cur;
                if (cnt[cid(u.ov)]++ == 0) ++cur;
            }
            c[u.pos] = cid(u.ov);
        };
        for (const MoUQuery& Q : qs) {
            while (curL > Q.l) { addIdx(--curL); ++mv; }
            while (curR < Q.r) { addIdx(++curR); ++mv; }
            while (curL < Q.l) { delIdx(curL++); ++mv; }
            while (curR > Q.r) { delIdx(curR--); ++mv; }
            while (curT < Q.t) { applyUp(ups[curT++]); ++mv; }
            while (curT > Q.t) { revertUp(ups[--curT]); ++mv; }
            ans[Q.id] = cur;
        }
        if (moves) *moves = mv;
        return ans;
    }
};

// ============================================================
// G1. 分块 vs 暴力逐操作
// ============================================================
static void G1() {
    int base = g_fail;
    printf("G1 分块(区间加/区间和/单点赋值) vs 暴力逐操作\n");
    reseed(0xAAAA0001ULL);
    int n = 300, ops = 5000;
    vector<long long> a(n), brute(n);
    for (int i = 0; i < n; ++i) {
        a[i] = (long long)(xr32() % 2001) - 1000;
        brute[i] = a[i];
    }
    SqrtBlocks sb(a);
    for (int op = 0; op < ops; ++op) {
        int t = (int)(xr32() % 3);
        int l = (int)(xr32() % (uint32_t)n), r = (int)(xr32() % (uint32_t)n);
        if (l > r) swap(l, r);
        if (t == 0) {  // 区间加
            long long d = (long long)(xr32() % 2001) - 1000;
            sb.rangeAdd(l, r, d);
            for (int i = l; i <= r; ++i) brute[i] += d;
        } else if (t == 1) {  // 单点赋值
            long long nv = (long long)(xr32() % 200001) - 100000;
            sb.pointSet(l, nv);
            brute[l] = nv;
        } else {  // 区间和
            long long got = sb.rangeSum(l, r), want = 0;
            for (int i = l; i <= r; ++i) want += brute[i];
            if (got != want) {
                ++g_fail;
                printf("    [FAIL] op=%d sum[%d,%d] got=%lld want=%lld\n", op, l, r, got, want);
            }
        }
    }
    for (int i = 0; i < n; ++i) {
        if (sb.at(i) != brute[i]) {
            ++g_fail;
            printf("    [FAIL] 终态 at(%d) got=%lld want=%lld\n", i, sb.at(i), brute[i]);
            break;
        }
    }
    if (!sb.selfCheck()) {
        ++g_fail;
        printf("    [FAIL] selfCheck: bsum 不变式破坏\n");
    }
    printf("  n=%d ops=%d, 自动块长 B=%d\n", n, ops, sb.B);
    report("G1", base);
}

// ============================================================
// G2. 莫队(普通/奇偶) vs 每查询暴力 —— 三种值域分布
// ============================================================
static void G2() {
    int base = g_fail;
    printf("G2 莫队(区间 distinct) vs 逐查询暴力\n");
    reseed(0xAAAA0002ULL);
    struct Case { const char* name; int n, q, vmax; };
    const Case cases[] = {
        {"小值域高重复", 200, 300, 8},
        {"大值域近唯一", 300, 300, 100000},
        {"全同值      ", 150, 200, 1},
    };
    for (const Case& cs : cases) {
        vector<int> a(cs.n);
        for (int i = 0; i < cs.n; ++i) a[i] = (int)(xr32() % (uint32_t)cs.vmax);
        vector<MoQuery> qs(cs.q);
        for (int i = 0; i < cs.q; ++i) {
            int l = (int)(xr32() % (uint32_t)cs.n), r = (int)(xr32() % (uint32_t)cs.n);
            if (l > r) swap(l, r);
            qs[i] = {l, r, i};
        }
        unsigned long long mvP = 0, mvE = 0;
        vector<long long> plain = MoDistinct::solve(a, qs, false, &mvP);
        vector<long long> even = MoDistinct::solve(a, qs, true, &mvE);
        for (int i = 0; i < cs.q; ++i) {
            vector<int> seg(a.begin() + qs[i].l, a.begin() + qs[i].r + 1);
            sort(seg.begin(), seg.end());
            int want = (int)(unique(seg.begin(), seg.end()) - seg.begin());
            if (plain[i] != want) {
                ++g_fail;
                printf("    [FAIL] %s q#%d [%d,%d] got=%lld want=%d\n",
                       cs.name, i, qs[i].l, qs[i].r, plain[i], want);
            }
        }
        if (plain != even) {
            ++g_fail;
            printf("    [FAIL] %s 奇偶排序与普通排序答案不一致\n", cs.name);
        }
        printf("  %-10s n=%3d q=%3d: 指针移动 普通=%llu 奇偶=%llu\n", cs.name, cs.n, cs.q, mvP, mvE);
    }
    report("G2", base);
}

// ============================================================
// G3. 带修莫队 vs 暴力重放时间线
// ============================================================
static void G3() {
    int base = g_fail;
    printf("G3 带修莫队 vs 暴力重放\n");
    reseed(0xAAAA0003ULL);
    int n = 150, q = 250, ups = 250, vmax = 40;
    vector<int> a(n);
    for (int i = 0; i < n; ++i) a[i] = (int)(xr32() % (uint32_t)vmax);
    vector<pair<int, int>> ru(ups);
    for (int i = 0; i < ups; ++i)
        ru[i] = {(int)(xr32() % (uint32_t)n), (int)(xr32() % (uint32_t)vmax)};
    vector<MoUQuery> qs(q);
    for (int i = 0; i < q; ++i) {
        int l = (int)(xr32() % (uint32_t)n), r = (int)(xr32() % (uint32_t)n);
        if (l > r) swap(l, r);
        qs[i] = {l, r, (int)(xr32() % (uint32_t)(ups + 1)), i};
    }
    unsigned long long mv = 0;
    vector<long long> got = MoWithUpdate::solve(a, qs, ru, &mv);
    for (int i = 0; i < q; ++i) {
        vector<int> arr(a);  // 暴力: 从初始数组重放前 t 次修改
        for (int k = 0; k < qs[i].t; ++k) arr[ru[k].first] = ru[k].second;
        bool seen[64] = {false};
        int want = 0;
        for (int j = qs[i].l; j <= qs[i].r; ++j)
            if (!seen[arr[j]]) { seen[arr[j]] = true; ++want; }
        if (got[i] != want) {
            ++g_fail;
            printf("    [FAIL] q#%d [%d,%d] t=%d got=%lld want=%d\n",
                   i, qs[i].l, qs[i].r, qs[i].t, got[i], want);
        }
    }
    printf("  n=%d q=%d ups=%d: 指针+时间移动 %llu 次\n", n, q, ups, mv);
    report("G3", base);
}

// ============================================================
// G4. 边界专项
// ============================================================
static void G4() {
    int base = g_fail;
    printf("G4 边界专项\n");
    reseed(0xAAAA0004ULL);
    {  // (a) n=1 分块
        SqrtBlocks sb(vector<long long>{42}, 1);
        sb.rangeAdd(0, 0, 8);
        CHECK(sb.rangeSum(0, 0) == 50 && sb.at(0) == 50, "n=1 区间加/和失败\n");
        CHECK(sb.selfCheck(), "n=1 bsum 不变式破坏\n");
        sb.pointSet(0, -7);
        CHECK(sb.rangeSum(0, 0) == -7, "n=1 单点赋值失败\n");
    }
    {  // (b) 带修莫队: 时间前进 (t=0,1,0 排序后即 0,0,1)
        vector<int> a{1, 2, 3, 4};
        vector<pair<int, int>> ru{{0, 2}};
        vector<MoUQuery> qs{{0, 3, 0, 0}, {0, 3, 1, 1}, {0, 3, 0, 2}};
        vector<long long> ans = MoWithUpdate::solve(a, qs, ru, nullptr);
        CHECK(ans[0] == 4 && ans[1] == 3 && ans[2] == 4,
              "时间前进: got %lld %lld %lld\n", ans[0], ans[1], ans[2]);
    }
    {  // (c) 带修莫队: 时间倒流 (后一个查询 r 块更大但 t 更小)
        vector<int> a{1, 2, 3, 4};
        vector<pair<int, int>> ru{{1, 9}, {0, 8}, {1, 2}};
        vector<MoUQuery> qs{{0, 1, 3, 0}, {2, 3, 0, 1}};
        vector<long long> ans = MoWithUpdate::solve(a, qs, ru, nullptr);
        CHECK(ans[0] == 2 && ans[1] == 2, "时间倒流: got %lld %lld\n", ans[0], ans[1]);
    }
    {  // (d) 全同值: distinct 恒为 1
        vector<int> a(64, 5);
        vector<MoQuery> qs{{0, 63, 0}, {10, 40, 1}, {31, 31, 2}};
        vector<long long> ans = MoDistinct::solve(a, qs, true, nullptr);
        CHECK(ans[0] == 1 && ans[1] == 1 && ans[2] == 1, "全同值 distinct 应全为 1\n");
    }
    {  // (e) l == r
        vector<int> a{3, 1, 3, 3};
        vector<MoQuery> qs{{1, 1, 0}, {3, 3, 1}};
        vector<long long> ans = MoDistinct::solve(a, qs, false, nullptr);
        CHECK(ans[0] == 1 && ans[1] == 1, "l==r 应为 1\n");
    }
    {  // (f) n 恰为块长整数倍: 无残块, 全块覆盖
        vector<long long> a(64);
        for (int i = 0; i < 64; ++i) a[i] = i;
        SqrtBlocks sb(a, 8);  // nb=8, 无残块
        sb.rangeAdd(0, 63, 100);
        CHECK(sb.rangeSum(0, 63) == 100LL * 64 + 2016, "整块覆盖失败: %lld\n", sb.rangeSum(0, 63));
        CHECK(sb.selfCheck(), "bsum 不变式破坏(整块场景)\n");
    }
    report("G4", base);
}

// ============================================================
// G5. 实证: 块大小扫描的 touch 拐点 + 莫队奇偶一致性
// ============================================================
static void G5() {
    int base = g_fail;
    printf("G5 块大小扫描 touch 拐点 + 莫队奇偶一致性\n");
    reseed(0xAAAA0005ULL);
    int n = 4000, ops = 2000;
    vector<long long> a(n);
    for (int i = 0; i < n; ++i) a[i] = (long long)(xr32() % 2001) - 1000;
    vector<int> sl(ops), sr(ops);
    vector<long long> sd(ops);
    for (int k = 0; k < ops; ++k) {
        int l = (int)(xr32() % (uint32_t)n), r = (int)(xr32() % (uint32_t)n);
        if (l > r) swap(l, r);
        sl[k] = l;
        sr[k] = r;
        sd[k] = (long long)(xr32() % 101) - 50;
    }
    const int nB = 5;
    int Bs[nB] = {4, 16, 63, 256, 1024};
    long long tc[nB];
    for (int t = 0; t < nB; ++t) {
        SqrtBlocks sb(a, Bs[t]);
        for (int k = 0; k < ops; ++k) {
            if ((k & 1) == 0) sb.rangeAdd(sl[k], sr[k], sd[k]);
            else sb.rangeSum(sl[k], sr[k]);
        }
        tc[t] = sb.touch;
    }
    printf("  n=%d ops=%d  touch(B):", n, ops);
    for (int t = 0; t < nB; ++t) printf("  B=%4d:%lld", Bs[t], tc[t]);
    printf("\n");
    // 理论: 每操作 O(B + n/B), 拐点在 B=sqrt(n)≈63
    CHECK(tc[2] < tc[0], "touch(B=63)=%lld 应 < touch(B=4)=%lld\n", tc[2], tc[0]);
    CHECK(tc[2] < tc[1], "touch(B=63)=%lld 应 < touch(B=16)=%lld\n", tc[2], tc[1]);
    CHECK(tc[2] < tc[3], "touch(B=63)=%lld 应 < touch(B=256)=%lld\n", tc[2], tc[3]);
    CHECK(tc[2] < tc[4], "touch(B=63)=%lld 应 < touch(B=1024)=%lld\n", tc[2], tc[4]);
    {  // 莫队奇偶排序: 答案必须一致; 移动量是启发式, 只打印不硬断言
        int n2 = 800, q2 = 800;
        vector<int> b(n2);
        for (int i = 0; i < n2; ++i) b[i] = (int)(xr32() % 50);
        vector<MoQuery> qs(q2);
        for (int i = 0; i < q2; ++i) {
            int l = (int)(xr32() % (uint32_t)n2), r = (int)(xr32() % (uint32_t)n2);
            if (l > r) swap(l, r);
            qs[i] = {l, r, i};
        }
        unsigned long long mvP = 0, mvE = 0;
        vector<long long> ap = MoDistinct::solve(b, qs, false, &mvP);
        vector<long long> ae = MoDistinct::solve(b, qs, true, &mvE);
        CHECK(ap == ae, "奇偶排序与普通排序答案不一致\n");
        printf("  莫队 n=%d q=%d: 普通=%llu 奇偶=%llu (省 %.1f%%)\n",
               n2, q2, mvP, mvE, mvP ? 100.0 * (double)(mvP - mvE) / (double)mvP : 0.0);
    }
    report("G5", base);
}

// ============================================================
// 基准①: 分块块大小扫描 (真实计时)
// ============================================================
static void benchBlockSweep() {
    printf("---- 基准①: 分块块大小扫描 n=1e5 ops=1e5 ----\n");
    reseed(0xAAAA0101ULL);
    int n = 100000, ops = 100000;
    vector<long long> a(n);
    for (int i = 0; i < n; ++i) a[i] = (long long)(xr32() % 2001) - 1000;
    vector<int> sl(ops), sr(ops);
    vector<long long> sd(ops);
    for (int k = 0; k < ops; ++k) {
        int l = (int)(xr32() % (uint32_t)n), r = (int)(xr32() % (uint32_t)n);
        if (l > r) swap(l, r);
        sl[k] = l;
        sr[k] = r;
        sd[k] = (long long)(xr32() % 101) - 50;
    }
    int Bs[] = {32, 64, 128, 256, 316, 512, 1024, 2048, 4096};
    printf("  %6s %10s %14s\n", "B", "time(ms)", "touch");
    for (int B : Bs) {
        SqrtBlocks sb(a, B);
        auto t0 = chrono::steady_clock::now();
        long long sink = 0;
        for (int k = 0; k < ops; ++k) {
            if (k & 1) sink ^= sb.rangeSum(sl[k], sr[k]);
            else sb.rangeAdd(sl[k], sr[k], sd[k]);
        }
        auto t1 = chrono::steady_clock::now();
        double ms = chrono::duration<double, milli>(t1 - t0).count();
        printf("  %6d %10.1f %14lld   (sink=%lld)\n", B, ms, sb.touch, sink & 3);
    }
}

// ============================================================
// 基准②: 莫队 普通排序 vs 奇偶排序
// ============================================================
static void benchMo() {
    printf("---- 基准②: 莫队 n=1e5 q=1e5 ----\n");
    reseed(0xAAAA0102ULL);
    int n = 100000, q = 100000;
    vector<int> a(n);
    for (int i = 0; i < n; ++i) a[i] = (int)(xr32() % 1000000000);
    vector<MoQuery> qs(q);
    for (int i = 0; i < q; ++i) {
        int l = (int)(xr32() % (uint32_t)n), r = (int)(xr32() % (uint32_t)n);
        if (l > r) swap(l, r);
        qs[i] = {l, r, i};
    }
    unsigned long long mvP = 0, mvE = 0;
    auto t0 = chrono::steady_clock::now();
    vector<long long> ap = MoDistinct::solve(a, qs, false, &mvP);
    auto t1 = chrono::steady_clock::now();
    vector<long long> ae = MoDistinct::solve(a, qs, true, &mvE);
    auto t2 = chrono::steady_clock::now();
    CHECK(ap == ae, "基准中两种排序答案不一致\n");
    double msP = chrono::duration<double, milli>(t1 - t0).count();
    double msE = chrono::duration<double, milli>(t2 - t1).count();
    printf("  普通排序: %6.0f ms, 指针移动 %llu\n", msP, mvP);
    printf("  奇偶排序: %6.0f ms, 指针移动 %llu (省 %.1f%%)\n", msE, mvE,
           mvP ? 100.0 * (double)(mvP - mvE) / (double)mvP : 0.0);
}

// ============================================================
// 基准③: 带修莫队 O(n^(5/3)) 规模实测
// ============================================================
static void benchMoUpdate() {
    printf("---- 基准③: 带修莫队 n=5e4 q=4e4 修改=4e4 ----\n");
    reseed(0xAAAA0103ULL);
    int n = 50000, q = 40000, ups = 40000;
    vector<int> a(n);
    for (int i = 0; i < n; ++i) a[i] = (int)(xr32() % 1000000000);
    vector<pair<int, int>> ru(ups);
    for (int i = 0; i < ups; ++i)
        ru[i] = {(int)(xr32() % (uint32_t)n), (int)(xr32() % 1000000000)};
    vector<MoUQuery> qs(q);
    for (int i = 0; i < q; ++i) {
        int l = (int)(xr32() % (uint32_t)n), r = (int)(xr32() % (uint32_t)n);
        if (l > r) swap(l, r);
        qs[i] = {l, r, (int)(xr32() % (uint32_t)(ups + 1)), i};
    }
    unsigned long long mv = 0;
    auto t0 = chrono::steady_clock::now();
    vector<long long> ans = MoWithUpdate::solve(a, qs, ru, &mv);
    auto t1 = chrono::steady_clock::now();
    double ms = chrono::duration<double, milli>(t1 - t0).count();
    printf("  %6.0f ms, 指针+时间移动 %llu\n", ms, mv);
    printf("  抽样: ans[0]=%lld ans[q/2]=%lld\n", ans[0], ans[q / 2]);
}

int main() {
    printf("==== 0010 分块 / 莫队算法 ====\n");
    G1();
    G2();
    G3();
    G4();
    G5();
    benchBlockSweep();
    benchMo();
    benchMoUpdate();
    printf("==== 总结: %s (fail=%d) ====\n", g_fail ? "存在失败项" : "全部通过", g_fail);
    return g_fail ? 1 : 0;
}
