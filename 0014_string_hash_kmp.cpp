// ============================================================
// 0014 · 字符串哈希 + KMP + Z 函数
// ------------------------------------------------------------
// 六个部分:
//   A. Hash2      双模多项式哈希 (1e9+7 / 1e9+9), O(1) 子串相等判定
//   B. Hash64     mod 2^64 自然溢出哈希, 单次乘加, 基必须为奇数
//   C. KMP        前缀函数 pi / 全匹配 / 26 字母自动机 O(m*σ) 流式匹配
//   D. Z 函数     单趟 O(n), 顺带给出 LCP(i, 0) 全表
//   E. 周期       最小周期 = n - pi[n-1]; 严格周期还须整除 n
//   F. 基准       最坏文本 a^n vs a^(m-1)b 四方对比 + 子串 LCP 批量查询
// 正确性: KMP / 自动机 / Z / 暴力 / 双模哈希 五方对拍
//         + 单模碰撞率实测 + 偶数基灾难性碰撞演示
// 编译:   g++ -O2 -std=c++17 -Wall -Wextra 0014_string_hash_kmp.cpp -o 0014
// 注意:   本期源码未在本机编译(环境无 C++ 编译器), 算法逻辑已通过
//         Python 逐行镜像对拍验证, 详见 0014_string_hash_kmp.md
// ============================================================
#include <bits/stdc++.h>
using namespace std;
using ll = long long;
using ull = unsigned long long;
using u32 = unsigned int;

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
        return chrono::duration<double, milli>(chrono::steady_clock::now() - a).count();
    }
};

static string randStr(mt19937& rng, int n, int sigma) {
    string s(n, 'a');
    for (int i = 0; i < n; ++i) s[i] = (char)('a' + (int)(rng() % (unsigned)sigma));
    return s;
}

// ============================================================
// A. 双模多项式哈希
//    把串看成 base 进制数: H(s) = Σ s[i] * base^(n-1-i) mod p
//    子串哈希: H(l..r) = H[0..r] - H[0..l-1] * base^(r-l+1)
//    两个 1e9 级素数并联 => 单次误判概率 ~ 1e-18
// ============================================================
static const u32 M1 = 1000000007u;
static const u32 M2 = 1000000009u;

struct Hash2 {
    int n = 0;
    u32 b1 = 131, b2 = 137;
    vector<u32> p1, p2, h1, h2;   // p*: base 的幂, h*: 前缀哈希

    void build(const string& s, u32 base1 = 131, u32 base2 = 137) {
        n = (int)s.size();
        b1 = base1;
        b2 = base2;
        p1.assign(n + 1, 1);
        p2.assign(n + 1, 1);
        h1.assign(n + 1, 0);
        h2.assign(n + 1, 0);
        for (int i = 0; i < n; ++i) {
            u32 c = (u32)(s[i] - 'a' + 1);
            p1[i + 1] = (u32)((ull)p1[i] * b1 % M1);
            p2[i + 1] = (u32)((ull)p2[i] * b2 % M2);
            h1[i + 1] = (u32)(((ull)h1[i] * b1 + c) % M1);
            h2[i + 1] = (u32)(((ull)h2[i] * b2 + c) % M2);
        }
    }

    // 闭区间 [l, r] 的哈希; 先加 M*M 避免无符号下溢
    u32 sub1(int l, int r) const {
        return (u32)((h1[r + 1] + (ull)M1 * M1 - (ull)h1[l] * p1[r - l + 1] % M1) % M1);
    }
    u32 sub2(int l, int r) const {
        return (u32)((h2[r + 1] + (ull)M2 * M2 - (ull)h2[l] * p2[r - l + 1] % M2) % M2);
    }

    bool eq(int l1, int r1, int l2, int r2) const {
        if (r1 - l1 != r2 - l2) return false;
        return sub1(l1, r1) == sub1(l2, r2) && sub2(l1, r1) == sub2(l2, r2);
    }

    // 最长公共前缀: 二分长度 + O(1) 判定 => O(log n)
    int lcp(int i, int j) const {
        int hi = min(n - i, n - j), lo = 0;
        while (lo < hi) {
            int mid = (lo + hi + 1) >> 1;                 // mid >= 1, 不会出现空区间
            if (eq(i, i + mid - 1, j, j + mid - 1)) lo = mid;
            else hi = mid - 1;
        }
        return lo;
    }
};

// ============================================================
// B. mod 2^64 溢出哈希: 无取模, 一条 imul+add
//    基必须是奇数(与 2^64 互素), 否则高阶位被 2 的幂吃掉
// ============================================================
struct Hash64 {
    int n = 0;
    ull b = 131;
    vector<ull> p, h;

    void build(const string& s, ull base = 131) {
        n = (int)s.size();
        b = base;
        p.assign(n + 1, 1);
        h.assign(n + 1, 0);
        for (int i = 0; i < n; ++i) {
            ull c = (ull)(s[i] - 'a' + 1);
            p[i + 1] = p[i] * b;                          // 自然溢出
            h[i + 1] = h[i] * b + c;
        }
    }
    ull sub(int l, int r) const { return h[r + 1] - h[l] * p[r - l + 1]; }
    bool eq(int l1, int r1, int l2, int r2) const {
        if (r1 - l1 != r2 - l2) return false;
        return sub(l1, r1) == sub(l2, r2);
    }
};

static u32 polyMod(const string& s, u32 base, u32 mod) {
    u32 h = 0;
    for (char ch : s) h = (u32)(((ull)h * base + (u32)(ch - 'a' + 1)) % mod);
    return h;
}
static ull poly64(const string& s, ull base) {
    ull h = 0;
    for (char ch : s) h = h * base + (ull)(ch - 'a' + 1);
    return h;
}

// ============================================================
// C. KMP: 前缀函数 pi[i] = 既是 s[0..i] 真前缀又是真后缀的最长长度
//    匹配时失配就沿 pi 链跳, 文本指针永不回退 => O(n + m)
// ============================================================
struct KMP {
    string pat;
    int m = 0;
    vector<int> pi;
    vector<array<int, 26>> go;      // 自动机: go[state][c], state ∈ [0, m]

    void build(const string& p) {
        pat = p;
        m = (int)p.size();
        pi.assign(m, 0);
        for (int i = 1; i < m; ++i) {
            int j = pi[i - 1];
            while (j > 0 && pat[i] != pat[j]) j = pi[j - 1];
            if (pat[i] == pat[j]) ++j;
            pi[i] = j;
        }
        go.clear();
    }

    // 全匹配; cmps 统计字符相等性判定次数(与暴力公平对比)
    vector<int> matchAll(const string& t, ll* cmps = nullptr) const {
        vector<int> res;
        ll c = 0;
        int j = 0, n = (int)t.size();
        for (int i = 0; i < n; ++i) {
            while (j > 0 && pat[j] != t[i]) { ++c; j = pi[j - 1]; }
            if (j > 0) { ++c; ++j; }                      // 出循环即 pat[j]==t[i]
            else { ++c; if (pat[0] == t[i]) ++j; }
            if (j == m) { res.push_back(i - m + 1); j = pi[m - 1]; }
        }
        if (cmps) *cmps = c;
        return res;
    }

    // 单个字符转移(不建表, 沿 pi 回退): 均摊 O(1), 单次最坏 O(m)
    int nextState(int st, char c) const {
        int j = st;
        while (j > 0 && (j == m || pat[j] != c)) j = pi[j - 1];
        if (j < m && pat[j] == c) ++j;
        return j;
    }

    // 预建自动机: O(m*σ) 时间空间, 之后每字符严格 O(1)
    void buildAuto() {
        go.assign(m + 1, array<int, 26>());
        for (int st = 0; st <= m; ++st) {
            for (int c = 0; c < 26; ++c) {
                if (st < m && c == pat[st] - 'a') go[st][c] = st + 1;
                else if (st == 0) go[st][c] = 0;
                else go[st][c] = go[pi[st - 1]][c];       // pi[st-1] < st, 已算好
            }
        }
    }

    // 流式计数: 到 m 就是一次命中, 且 go[m][*] 已定义, 无需显式复位
    int matchCountAuto(const string& t) const {
        int st = 0, cnt = 0;
        for (char c : t) {
            st = go[st][c - 'a'];
            if (st == m) ++cnt;
        }
        return cnt;
    }

    // 最小周期: n - pi[n-1]; 整除 n 时才是 s = t^(n/p) 的循环节
    int minPeriod() const {
        if (m == 0) return 0;
        return m - pi[m - 1];
    }
};

// ============================================================
// D. Z 函数: z[i] = LCP(s, s[i..]); [l, r) 维护最右匹配段
// ============================================================
static vector<int> zFunc(const string& s, ll* cmps = nullptr) {
    int n = (int)s.size();
    vector<int> z(n, 0);
    if (n == 0) return z;
    z[0] = n;
    ll c = 0;
    int l = 0, r = 0;                                     // 当前盒子 [l, r)
    for (int i = 1; i < n; ++i) {
        if (i < r) z[i] = min(r - i, z[i - l]);           // 盒内直接复用
        // 计数器与暴力同口径: 每次字符相等性判定都计一次(含最后那次失配)
        while (i + z[i] < n) { ++c; if (s[z[i]] != s[i + z[i]]) break; ++z[i]; }
        if (i + z[i] > r) { l = i; r = i + z[i]; }
    }
    if (cmps) *cmps = c;
    return z;
}

static vector<int> zBrute(const string& s) {
    int n = (int)s.size();
    vector<int> z(n, 0);
    for (int i = 0; i < n; ++i) {
        int k = 0;
        while (i + k < n && s[k] == s[i + k]) ++k;
        z[i] = k;
    }
    return z;
}

// ============================================================
// 暴力对照实现
// ============================================================
static vector<int> bruteMatch(const string& t, const string& p, ll* cmps = nullptr) {
    vector<int> res;
    ll c = 0;
    int n = (int)t.size(), m = (int)p.size();
    for (int i = 0; i + m <= n; ++i) {
        bool ok = true;
        for (int j = 0; j < m; ++j) {
            ++c;
            if (t[i + j] != p[j]) { ok = false; break; }
        }
        if (ok) res.push_back(i);
    }
    if (cmps) *cmps = c;
    return res;
}

static int bruteLcp(const string& s, int i, int j) {
    int n = (int)s.size(), k = 0;
    while (i + k < n && j + k < n && s[i + k] == s[j + k]) ++k;
    return k;
}

// 最小周期定义: 最小的 p >= 1 使 s[i]==s[i+p] 对所有 i < n-p 成立; 否则 p=n
static int bruteMinPeriod(const string& s) {
    int n = (int)s.size();
    for (int p = 1; p <= n; ++p) {
        bool ok = true;
        for (int i = 0; i + p < n; ++i)
            if (s[i] != s[i + p]) { ok = false; break; }
        if (ok) return p;
    }
    return n;
}

static bool sameVec(const vector<int>& a, const vector<int>& b) { return a == b; }

// ============================================================
// G1. KMP / 自动机 / Z / 暴力 / 双模哈希 五方对拍
// ============================================================
static void group1_match() {
    printf("G1 五方匹配对拍 (sigma=2/4/26)\n");
    mt19937 rng(1401);
    ll cases = 0, hits = 0;

    for (int sigma : {2, 4, 26}) {
        for (int cs = 0; cs < 600; ++cs) {
            int n = 1 + (int)(rng() % 120);
            int m = 1 + (int)(rng() % 12);
            string t = randStr(rng, n, sigma);
            string p;
            if (cs & 1) {                                  // 模式取自文本 => 保证有命中
                int st = (int)(rng() % (unsigned)n);
                int len = min(m, n - st);
                p = t.substr(st, len);
            } else {
                p = randStr(rng, m, sigma);
            }
            ++cases;
            int mm = (int)p.size();

            KMP k;
            k.build(p);
            auto a = k.matchAll(t);
            auto b = bruteMatch(t, p);

            // 自动机流式: 计数须与 KMP 命中数一致
            k.buildAuto();
            int cnt = k.matchCountAuto(t);

            // Z 函数: s = p + '{' + t, z[i] >= mm 即命中起点 i-mm-1
            string s = p;
            s.push_back('{');
            s += t;
            auto z = zFunc(s);
            vector<int> d;
            for (int i = mm + 1; i < (int)s.size(); ++i)
                if (z[i] >= mm) d.push_back(i - mm - 1);

            // 双模哈希逐位置判定: 文本子串哈希 vs 模式串整体哈希
            Hash2 ht, hp;
            ht.build(t);
            hp.build(p);
            u32 q1 = hp.sub1(0, mm - 1), q2 = hp.sub2(0, mm - 1);
            vector<int> e;
            for (int i = 0; i + mm <= (int)t.size(); ++i)
                if (ht.sub1(i, i + mm - 1) == q1 && ht.sub2(i, i + mm - 1) == q2)
                    e.push_back(i);

            CHECK(sameVec(a, b), "KMP vs 暴力 失配 (sigma=%d n=%d m=%d)", sigma, n, mm);
            CHECK(sameVec(a, d), "KMP vs Z 失配 (sigma=%d n=%d m=%d)", sigma, n, mm);
            CHECK(sameVec(a, e), "KMP vs 哈希 失配 (sigma=%d n=%d m=%d)", sigma, n, mm);
            CHECK(cnt == (int)a.size(), "自动机计数 %d != KMP %zu", cnt, a.size());
            hits += (ll)a.size();
        }
    }
    printf("  %lld 组 (sigma=2/4/26 各 600), 累计命中 %lld 处, 五方完全一致\n", cases, hits);
}

// ============================================================
// G2. 自动机表 == pi 回退转移 —— 逐状态逐字符穷举
// ============================================================
static void group2_automaton() {
    printf("G2 自动机表 vs pi 回退转移 (逐状态 x 26 字符穷举)\n");
    mt19937 rng(1402);
    ll cmp = 0;
    for (int cs = 0; cs < 120; ++cs) {
        int m = 1 + (int)(rng() % 60);
        int sigma = 2 + (int)(rng() % 3);
        string p = randStr(rng, m, sigma);
        KMP k;
        k.build(p);
        k.buildAuto();
        for (int st = 0; st <= m; ++st)
            for (int c = 0; c < 26; ++c) {
                int want = k.nextState(st, (char)('a' + c));
                ++cmp;
                CHECK(k.go[st][c] == want, "m=%d st=%d c=%c: auto=%d pi=%d",
                      m, st, (char)('a' + c), k.go[st][c], want);
            }
    }
    printf("  %lld 个 (状态,字符) 格全部一致, 自动机表大小 O(m*sigma)\n", cmp);
}

// ============================================================
// G3. Z 函数 vs O(n^2) 暴力
// ============================================================
static void group3_z() {
    printf("G3 Z 函数 vs 暴力 O(n^2)\n");
    mt19937 rng(1403);
    ll n2 = 0;
    for (int cs = 0; cs < 400; ++cs) {
        int n = 1 + (int)(rng() % 200);
        int sigma = 1 + (int)(rng() % 3);
        string s = randStr(rng, n, sigma);
        auto a = zFunc(s);
        auto b = zBrute(s);
        if (!sameVec(a, b)) {
            CHECK(false, "Z 失配 cs=%d n=%d sigma=%d", cs, n, sigma);
        }
        CHECK(a[0] == n, "z[0]=%d 应为 n=%d", a[0], n);
        n2 += n;
    }
    // 极端 1: 全同字符, z 呈递减台阶
    string same(1000, 'a');
    auto zs = zFunc(same);
    for (int i = 1; i < 1000; ++i)
        CHECK(zs[i] == 1000 - i, "a^1000 z[%d]=%d 应为 %d", i, zs[i], 1000 - i);
    // 极端 2: 周期 2 的串 "abab..." —— 偶数位 z 恰好等于剩余长度, 奇数位恒 0
    string alt(1000, 'a');
    for (int i = 0; i < 1000; ++i) alt[i] = (i & 1) ? 'b' : 'a';
    auto za = zFunc(alt);
    for (int i = 1; i < 1000; ++i) {
        int want = (i & 1) ? 0 : (1000 - i);
        CHECK(za[i] == want, "abab.. z[%d]=%d 应为 %d", i, za[i], want);
    }
    printf("  400 组随机串 (总长 %lld) + a^1000 台阶 + abab.. 奇偶台阶 全一致\n", n2);
}

// ============================================================
// G4. 周期: n - pi[n-1] 与暴力最小周期等价; 整除才是循环节
// ============================================================
static void group4_period() {
    printf("G4 最小周期 = n - pi[n-1] 与暴力定义对拍\n");
    mt19937 rng(1404);
    ll tot = 0;
    for (int cs = 0; cs < 600; ++cs) {
        int n = 1 + (int)(rng() % 80);
        int sigma = 1 + (int)(rng() % 3);
        string s = randStr(rng, n, sigma);
        KMP k;
        k.build(s);
        int p = k.minPeriod(), q = bruteMinPeriod(s);
        CHECK(p == q, "n=%d: pi 周期 %d != 暴力周期 %d (s=%s)", n, p, q, s.c_str());
        ++tot;
    }

    // t^k: 本原串 t 重复 k 次 => 最小周期恰为 |t| 且整除 n
    int ok = 0;
    for (int cs = 0; cs < 400 && ok < 100; ++cs) {
        int L = 1 + (int)(rng() % 6);
        string base = randStr(rng, L, 3);
        if (bruteMinPeriod(base) != L) continue;           // 非本原串跳过
        ++ok;
        int k = 1 + (int)(rng() % 6);
        string s;
        for (int i = 0; i < k; ++i) s += base;
        KMP ks;
        ks.build(s);
        int n = (int)s.size();
        CHECK(ks.minPeriod() == L, "t^k 最小周期 %d != |t| = %d", ks.minPeriod(), L);
        CHECK(n % ks.minPeriod() == 0, "n=%d 未被周期 %d 整除", n, ks.minPeriod());

        // border 链: pi 链上每一环都必须真的是 border
        vector<int> chain;
        for (int b = ks.pi[n - 1]; b > 0; b = ks.pi[b - 1]) chain.push_back(b);
        for (int b : chain)
            CHECK(s.compare(0, b, s, n - b, b) == 0,
                  "border %d 校验失败 (n=%d)", b, n);

        // 削掉最后一个字符: 周期还在, 但 n 不再被整除 => 不是 t^k 形式
        if (k >= 2 && n > 1) {
            string s2 = s.substr(0, n - 1);
            KMP k2;
            k2.build(s2);
            int p2 = k2.minPeriod(), n2 = (int)s2.size();
            CHECK(p2 == bruteMinPeriod(s2), "截断串最小周期不符 p2=%d", p2);
            // L=1 时任何长度都被 1 整除, 该断言只在 L>=2 时有信息量
            if (p2 < n2 && L > 1)
                CHECK(n2 % p2 != 0, "截断后仍整除? n2=%d p2=%d", n2, p2);
        }
    }
    printf("  600 组随机串周期一致; %d 组 t^k 边界与 border 链通过\n", ok);
}

// ============================================================
// G5. 哈希 LCP vs 逐字符比较 (Hash2 与 Hash64 交叉)
// ============================================================
static void group5_lcp() {
    printf("G5 哈希 LCP (二分) vs 逐字符, 双哈希交叉\n");
    mt19937 rng(1405);
    ll q = 0;
    for (int cs = 0; cs < 40; ++cs) {
        int n = 1 + (int)(rng() % 400);
        int sigma = 1 + (int)(rng() % 3);
        string s = randStr(rng, n, sigma);
        Hash2 h2;
        h2.build(s);
        Hash64 h64;
        h64.build(s, 131);
        for (int t = 0; t < 60; ++t) {
            int i = (int)(rng() % (unsigned)n), j = (int)(rng() % (unsigned)n);
            int a = bruteLcp(s, i, j), b = h2.lcp(i, j);
            CHECK(a == b, "Hash2 lcp(%d,%d)=%d != %d (n=%d)", i, j, b, a, n);
            // Hash64 逐长度一致性: 前缀相同 <=> 哈希相同
            bool eq64 = (b == 0) ? true : h64.eq(i, i + b - 1, j, j + b - 1);
            CHECK(eq64, "Hash64 在 lcp=%d 处不等 (i=%d j=%d)", b, i, j);
            ++q;
        }
        // 全串自比: lcp(i,i) = n - i
        for (int i = 0; i < n; i += max(1, n / 7))
            CHECK(h2.lcp(i, i) == n - i, "自比 lcp(%d,%d) 应为 %d", i, i, n - i);
    }
    printf("  %lld 次随机 LCP 查询, Hash2(二分) = 逐字符, Hash64 同结论\n", q);
}

// ============================================================
// G6. 单模 vs 双模: 生日攻击实测碰撞
// ============================================================
static void group6_collision() {
    printf("G6 单模 vs 双模 碰撞实测 (随机串, 生日攻击)\n");
    const int N = 150000, L = 20;
    mt19937 rng(1406);
    vector<string> v(N);
    for (int i = 0; i < N; ++i) v[i] = randStr(rng, L, 26);

    unordered_map<u32, int> seen1;
    seen1.reserve((size_t)N * 2);
    ll col1 = 0;
    int i1 = -1, j1 = -1;
    for (int i = 0; i < N; ++i) {
        u32 a = polyMod(v[i], 131, M1);
        auto it = seen1.find(a);
        if (it == seen1.end()) seen1.emplace(a, i);
        else { ++col1; if (i1 < 0) { i1 = it->second; j1 = i; } }
    }

    unordered_map<ull, int> seen2;
    seen2.reserve((size_t)N * 2);
    ll col2 = 0;
    for (int i = 0; i < N; ++i) {
        u32 a = polyMod(v[i], 131, M1);
        u32 b = polyMod(v[i], 137, M2);
        ull key = ((ull)a << 32) | (ull)b;
        auto it = seen2.find(key);
        if (it == seen2.end()) seen2.emplace(key, i);
        else ++col2;
    }

    double pairs = (double)N * (double)(N - 1) / 2.0;
    printf("  %d 条长 %d 随机串, 候选对数 %.3g\n", N, L, pairs);
    printf("  单模 1e9+7 : %lld 对碰撞 (理论期望 %.1f)\n", col1, pairs / 1e9);
    printf("  双模       : %lld 对碰撞 (理论期望 %.4f)\n", col2, pairs / 1e18);
    if (i1 >= 0) {
        printf("  首对冲突: \"%s\" / \"%s\"\n", v[i1].c_str(), v[j1].c_str());
        CHECK(v[i1] != v[j1], "自碰撞误报");
        CHECK(polyMod(v[i1], 131, M1) == polyMod(v[j1], 131, M1), "冲突对哈希不等");
        CHECK(polyMod(v[i1], 137, M2) != polyMod(v[j1], 137, M2), "双模本应区分该对");
    }
    CHECK(col2 == 0, "双模出现 %lld 对碰撞(概率 ~1e-9, 也可能真的中了)", col2);
}

// ============================================================
// G7. 偶数基灾难: base = 256 = 2^8, 只保留末 8 个字符
// ============================================================
static void group7_even_base() {
    printf("G7 偶数基灾难: base=256 vs base=131 (16 字符, 末 8 位相同)\n");
    mt19937 rng(1407);
    int tests = 0, bad256 = 0, bad131 = 0;
    for (int cs = 0; cs < 3000; ++cs) {
        string a(16, 'a'), b(16, 'a');
        for (int j = 0; j < 16; ++j) {
            char c = (char)('a' + (int)(rng() % 26));
            if (j < 8) {
                a[j] = c;
                b[j] = (char)('a' + (int)(rng() % 26));
            } else {
                a[j] = c;
                b[j] = c;                                   // 末 8 位强行相同
            }
        }
        if (a == b) continue;
        ++tests;
        if (poly64(a, 256) == poly64(b, 256)) ++bad256;
        if (poly64(a, 131) == poly64(b, 131)) ++bad131;
    }
    printf("  %d 对串: base=256 碰撞 %d 对 (%.1f%%), base=131 碰撞 %d 对\n",
           tests, bad256, 100.0 * (double)bad256 / (double)tests, bad131);
    CHECK(bad256 == tests, "base=256 应 100%% 碰撞, 实际 %d/%d", bad256, tests);
    CHECK(bad131 == 0, "base=131 碰撞 %d 对", bad131);
    // 同一条链: base = 2^64 时哈希恒等于末 1 个字符
    printf("  base=2^64 等价于只看最后 1 个字符; 基必须 > 值域且与 2^64 互素(奇数)\n");
}

// ============================================================
// F1. 最坏文本: t = a^n, p = a^(m-1) b  (暴力 O(nm), KMP O(n))
// ============================================================
static void bench_worst_text() {
    const int N = 300000, M = 64;
    string t(N, 'a');
    string p(M - 1, 'a');
    p.push_back('b');
    printf("B1 最坏文本 t=a^%d, p=a^%d+b (暴力理论 %.2g 次比较)\n",
           N, M - 1, (double)N * M);

    Timer tm;
    double ms;
    ll c1 = 0, c2 = 0, c3 = 0;

    tm.go();
    auto r1 = bruteMatch(t, p, &c1);
    ms = tm.ms();
    printf("  暴力       : %8.2f ms | %10lld 次比较 | %zu 命中\n", ms, c1, r1.size());

    KMP k;
    k.build(p);
    k.buildAuto();
    tm.go();
    auto r2 = k.matchAll(t, &c2);
    ms = tm.ms();
    printf("  KMP        : %8.2f ms | %10lld 次比较 | %zu 命中\n", ms, c2, r2.size());

    string cat = p;
    cat.push_back('{');
    cat += t;
    tm.go();
    auto z = zFunc(cat, &c3);
    ms = tm.ms();
    int zc = 0;
    for (int i = M + 1; i < (int)cat.size(); ++i)
        if (z[i] >= M) ++zc;
    printf("  Z 函数     : %8.2f ms | %10lld 次比较 | %d 命中\n", ms, c3, zc);

    tm.go();
    int cnt = 0;
    for (size_t pos = 0; (pos = t.find(p, pos)) != string::npos; ++pos) ++cnt;
    ms = tm.ms();
    printf("  string::find: %7.2f ms | (库内 memcmp, 无比较计数) | %d 命中\n", ms, cnt);

    CHECK(r1.size() == r2.size(), "暴力 %zu 与 KMP %zu 命中数不一致", r1.size(), r2.size());
    CHECK((int)r1.size() == zc && zc == cnt, "Z/find 命中数 %d/%d != %zu", zc, cnt, r1.size());
    // 复杂度断言与正确性断言分离: 数值全对也可能是 O(nm) 的退化实现
    CHECK(c2 <= 4LL * N, "KMP 比较次数 %lld 超出线性上界 4n=%lld", c2, 4LL * N);
    CHECK(c3 <= 4LL * N, "Z 比较次数 %lld 超出线性上界 4n=%lld", c3, 4LL * N);
    printf("  比较次数比 暴力/KMP = %.1f 倍 (渐近 O(nm)/O(n), KMP 常数≈2)\n",
           (double)c1 / (double)c2);
}

// ============================================================
// F2. 子串 LCP 批量查询: 哈希+二分 vs 逐字符, 两种文本形态
// ============================================================
static void bench_lcp_queries() {
    printf("B2 子串 LCP 批量查询: 哈希二分 vs 逐字符\n");

    // 形态 A: 随机文本, LCP 期望极短 => 逐字符反而更快
    {
        const int N = 300000, Q = 50000;
        mt19937 rng(51401);
        string s(N, 'a');
        for (int i = 0; i < N; ++i) s[i] = (char)('a' + (int)(rng() % 26));
        Hash2 h;
        h.build(s);
        // 查询对**先生成再统一使用** —— 两轮各取一次 RNG 会让两侧序列错位
        vector<pair<int, int>> qs(Q);
        for (int q = 0; q < Q; ++q) {
            qs[q].first = (int)(rng() % (unsigned)N);
            qs[q].second = (int)(rng() % (unsigned)N);
        }
        Timer tm;
        tm.go();
        ll sum1 = 0;
        for (int q = 0; q < Q; ++q) sum1 += bruteLcp(s, qs[q].first, qs[q].second);
        double ms1 = tm.ms();
        tm.go();
        ll sum2 = 0;
        for (int q = 0; q < Q; ++q) sum2 += h.lcp(qs[q].first, qs[q].second);
        double ms2 = tm.ms();
        CHECK(sum1 == sum2, "随机文本 LCP 和 %lld != %lld", sum1, sum2);
        printf("  随机文本 n=%d Q=%d: 逐字符 %7.1f ms (总 LCP %lld) | 哈希二分 %7.1f ms\n",
               N, Q, ms1, sum1, ms2);
    }

    // 形态 B: 周期文本, LCP 长达 O(n) => 哈希完胜
    {
        const int N = 60000, Q = 2000;
        mt19937 rng(51402);
        string s(N, 'a');
        for (int i = 0; i < N; ++i) s[i] = (char)('a' + i % 7);
        Hash2 h;
        h.build(s);
        vector<pair<int, int>> qs(Q);
        for (int q = 0; q < Q; ++q) {
            qs[q].first = (int)(rng() % (unsigned)N);
            qs[q].second = (int)(rng() % (unsigned)N);
        }
        Timer tm;
        tm.go();
        ll sum1 = 0;
        for (int q = 0; q < Q; ++q) sum1 += bruteLcp(s, qs[q].first, qs[q].second);
        double ms1 = tm.ms();
        tm.go();
        ll sum2 = 0;
        for (int q = 0; q < Q; ++q) sum2 += h.lcp(qs[q].first, qs[q].second);
        double ms2 = tm.ms();
        CHECK(sum1 == sum2, "周期文本 LCP 和 %lld != %lld", sum1, sum2);
        double avg = (double)sum1 / (double)Q;
        printf("  周期文本 n=%d Q=%d (平均 LCP %.0f): 逐字符 %7.1f ms | 哈希二分 %7.1f ms\n",
               N, Q, avg, ms1, ms2);
    }
    printf("  结论: 逐字符 O(LCP), 哈希 O(log n); LCP 短时逐字符常数更低, LCP 长时哈希数量级领先\n");
}

int main() {
    printf("== 0014 字符串哈希 + KMP + Z 函数 ==\n\n");
    group1_match();
    group2_automaton();
    group3_z();
    group4_period();
    group5_lcp();
    group6_collision();
    group7_even_base();
    printf("\n");
    bench_worst_text();
    bench_lcp_queries();

    printf("\n%s (g_fail=%d)\n", g_fail ? "存在失败项" : "全部通过", g_fail);
    return g_fail ? 1 : 0;
}
