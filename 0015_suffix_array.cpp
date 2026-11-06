// ===========================================================================
// 0015 · 后缀数组（Suffix Array）
//
//   A  倍增 + 计数排序                  O(n log n)
//   B  SA-IS（诱导排序，线性）            O(n)
//   C  Kasai height/LCP + 稀疏表 RMQ     O(n) 建 / O(1) 查询
//   D  双模哈希 LCP（独立 oracle，仅校验用）
//   E  三个应用：不同子串计数 / 最长重复子串 / 两串最长公共子串
//   F  校验与基准：穷举对拍 + 随机多方对拍 + 复杂度计数（而不只是"答案对"）
//
// 编译：g++ -O2 -std=c++17 -Wall -Wextra 0015_suffix_array.cpp -o sa15
// 说明：本机（作者环境）无 C++ 编译器，正确性由 .verify_mirror_0015.py 的
//       Python 逐行镜像验证；源码本身未经本机编译，语法层面的风险见讲义第 8 节。
// ===========================================================================

#include <bits/stdc++.h>
using namespace std;

using ll = long long;
using ull = unsigned long long;

// ============================ 0. 基础设施 ============================

struct Timer {
    chrono::steady_clock::time_point t0 = chrono::steady_clock::now();
    void reset() { t0 = chrono::steady_clock::now(); }
    double ms() const {
        auto d = chrono::steady_clock::now() - t0;
        // 用 duration_cast 到微秒再换算，避免 duration<double, milli> 里的时间单位名
        // 需要 chrono:: 限定（写 `duration<double, milli>` 在部分实现下找不到 milli）
        double us = (double)chrono::duration_cast<chrono::microseconds>(d).count();
        return us / 1000.0;
    }
};

struct Rng {
    ull s;
    explicit Rng(ull seed = 0x9E3779B97F4A7C15ULL) : s(seed) {}
    ull next() {
        ull z = (s += 0x9E3779B97F4A7C15ULL);
        z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
        z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
        return z ^ (z >> 31);
    }
    int nextInt(int lo, int hi) { return lo + (int)(next() % (ull)(hi - lo + 1)); }
};

static int g_fail = 0;

static void failLine(const string& msg) {
    ++g_fail;
    cout << "    [FAIL] " << msg << "\n";
}

static string vecHead(const vector<int>& v, int k) {
    string s = "[";
    for (int i = 0; i < (int)v.size() && i < k; i++) {
        if (i) s += ",";
        s += to_string(v[i]);
    }
    if ((int)v.size() > k) s += ",...";
    s += "]";
    return s;
}

// ============================ 1. 暴力参照 ============================

// 逐字符比较的后缀排序：字典序的教科书定义，O(n^2 log n)，只用于小 n。
// 前缀关系（a 走到 n）说明 a 是 b 的真前缀，a 更小 —— 对应 `return a > b`。
static vector<int> saBrute(const vector<int>& s) {
    int n = (int)s.size();
    vector<int> sa(n);
    iota(sa.begin(), sa.end(), 0);
    sort(sa.begin(), sa.end(), [&](int a, int b) {
        while (a < n && b < n) {
            if (s[a] != s[b]) return s[a] < s[b];
            ++a;
            ++b;
        }
        return a > b;
    });
    return sa;
}

static int lcpBrute(const vector<int>& s, int i, int j) {
    int n = (int)s.size(), h = 0;
    while (i + h < n && j + h < n && s[i + h] == s[j + h]) ++h;
    return h;
}

// ============================ 2. A · 倍增法 ============================

struct SAInfo {
    vector<int> sa;
    vector<int> rk;
};

// 核心：把"按前 2k 个字符排序"变成"按 (rank[i], rank[i+k]) 排序"。
// 因为 sa 已按 rank 有序，先把 i 按第二关键字排到 tmp（i+k>=n 的排最前），
// 再对第一关键字做一次稳定计数排序 —— 两趟 O(n)，故每轮 O(n)。
static SAInfo buildSaDoubling(const vector<int>& s, int sigma, int* roundsOut = nullptr) {
    int n = (int)s.size();
    SAInfo res;
    res.sa.assign(n, 0);
    res.rk.assign(n, 0);
    if (n == 0) {
        if (roundsOut) *roundsOut = 0;
        return res;
    }
    int cap = max(sigma, n) + 1;
    vector<int> cnt(cap, 0), tmp(n), nr(n);

    for (int i = 0; i < n; i++) cnt[s[i]]++;
    for (int i = 1; i < sigma; i++) cnt[i] += cnt[i - 1];
    for (int i = n - 1; i >= 0; i--) res.sa[--cnt[s[i]]] = i;

    res.rk[res.sa[0]] = 0;
    int classes = 1;
    for (int i = 1; i < n; i++) {
        if (s[res.sa[i]] != s[res.sa[i - 1]]) ++classes;
        res.rk[res.sa[i]] = classes - 1;
    }

    int rounds = 0;
    for (int k = 1; k < n && classes < n; k <<= 1) {
        ++rounds;
        int p = 0;
        for (int i = n - k; i < n; i++) tmp[p++] = i;
        for (int i = 0; i < n; i++) {
            if (res.sa[i] >= k) tmp[p++] = res.sa[i] - k;
        }
        fill(cnt.begin(), cnt.begin() + classes, 0);
        for (int i = 0; i < n; i++) cnt[res.rk[tmp[i]]]++;
        for (int i = 1; i < classes; i++) cnt[i] += cnt[i - 1];
        for (int i = n - 1; i >= 0; i--) res.sa[--cnt[res.rk[tmp[i]]]] = tmp[i];

        nr[res.sa[0]] = 0;
        int nc = 1;
        for (int i = 1; i < n; i++) {
            int a = res.sa[i - 1], b = res.sa[i];
            int a2 = (a + k < n) ? res.rk[a + k] : -1;
            int b2 = (b + k < n) ? res.rk[b + k] : -1;
            if (res.rk[a] != res.rk[b] || a2 != b2) ++nc;
            nr[b] = nc - 1;
        }
        res.rk.swap(nr);
        classes = nc;
    }
    if (roundsOut) *roundsOut = rounds;
    return res;
}

// ============================ 3. B · SA-IS ============================

// 全局工作量累加器：递归各层 n 之和。线性算法的证据就是 work/n 有界。
static long long g_saisWork = 0;
static long long g_saisCalls = 0;

// 前提：s.back() 是唯一最小字符（哨兵 0），且所有值在 [0, upper]。
// 类型：L 型 s[i] > s[i+1]（或相等且 i+1 为 L），S 型反之；末尾哨兵按 L 处理。
static void saIsCore(const vector<int>& s, int upper, vector<int>& sa) {
    int n = (int)s.size();
    g_saisWork += n;
    ++g_saisCalls;

    if (n == 1) {
        sa.assign(1, 0);
        return;
    }
    if (n == 2) {
        sa.assign(2, 0);
        if (s[0] < s[1]) { sa[0] = 0; sa[1] = 1; }
        else { sa[0] = 1; sa[1] = 0; }
        return;
    }
    if (n < 10) {  // 小规模直接排，避免递归开销（O(n^2 log n) 但 n<10）
        sa.resize(n);
        iota(sa.begin(), sa.end(), 0);
        sort(sa.begin(), sa.end(), [&](int a, int b) {
            while (a < n && b < n) {
                if (s[a] != s[b]) return s[a] < s[b];
                ++a;
                ++b;
            }
            return a > b;
        });
        return;
    }

    vector<char> isS(n, 0);  // isS[n-1] = 0：哨兵视为 L 型
    for (int i = n - 2; i >= 0; i--) {
        if (s[i] == s[i + 1]) isS[i] = isS[i + 1];
        else isS[i] = (s[i] < s[i + 1]) ? 1 : 0;
    }

    // sumL[c] = 桶 c 的起点；sumS[c] = 桶 c 中 L 段之后（S 段起点）
    vector<int> sumL(upper + 2, 0), sumS(upper + 2, 0);
    for (int i = 0; i < n; i++) {
        if (!isS[i]) sumS[s[i]]++;
        else sumL[s[i] + 1]++;
    }
    for (int i = 0; i <= upper; i++) {
        sumS[i] += sumL[i];
        if (i < upper) sumL[i + 1] += sumS[i];
    }

    auto induce = [&](const vector<int>& lms) {
        sa.assign(n, -1);
        vector<int> buf(upper + 2, 0);
        // (1) 先把 LMS 后缀塞到各自桶的 S 段起点（顺序任意，仅作种子）
        copy(sumS.begin(), sumS.end(), buf.begin());
        for (int d : lms) {
            if (d == n) continue;
            sa[buf[s[d]]++] = d;
        }
        // (2) L 型诱导：桶头开始，从左往右
        copy(sumL.begin(), sumL.end(), buf.begin());
        sa[buf[s[n - 1]]++] = n - 1;
        for (int i = 0; i < n; i++) {
            int v = sa[i];
            if (v >= 1 && !isS[v - 1]) sa[buf[s[v - 1]]++] = v - 1;
        }
        // (3) S 型诱导：桶尾开始，从右往左
        copy(sumL.begin(), sumL.end(), buf.begin());
        for (int i = n - 1; i >= 0; i--) {
            int v = sa[i];
            if (v >= 1 && isS[v - 1]) sa[--buf[s[v - 1] + 1]] = v - 1;
        }
    };

    vector<int> lmsMap(n + 1, -1);
    int m = 0;
    for (int i = 1; i < n; i++) {
        if (!isS[i - 1] && isS[i]) lmsMap[i] = m++;
    }
    vector<int> lms;
    lms.reserve(m);
    for (int i = 1; i < n; i++) {
        if (!isS[i - 1] && isS[i]) lms.push_back(i);
    }

    induce(lms);

    if (m > 0) {
        vector<int> sortedLms;
        sortedLms.reserve(m);
        for (int v : sa) {
            if (v >= 0 && lmsMap[v] != -1) sortedLms.push_back(v);
        }
        vector<int> recS(m, 0);
        int recUpper = 0;
        recS[lmsMap[sortedLms[0]]] = 0;
        for (int i = 1; i < m; i++) {
            int l = sortedLms[i - 1], r = sortedLms[i];
            int endL = (lmsMap[l] + 1 < m) ? lms[lmsMap[l] + 1] : n;
            int endR = (lmsMap[r] + 1 < m) ? lms[lmsMap[r] + 1] : n;
            bool same = true;
            if (endL - l != endR - r) {
                same = false;
            } else {
                while (l < endL) {
                    if (s[l] != s[r]) break;
                    ++l;
                    ++r;
                }
                if (l == n || s[l] != s[r]) same = false;
            }
            if (!same) ++recUpper;
            recS[lmsMap[sortedLms[i]]] = recUpper;
        }
        vector<int> recSa;
        saIsCore(recS, recUpper, recSa);
        for (int i = 0; i < m; i++) sortedLms[i] = lms[recSa[i]];
        induce(sortedLms);
    }
}

// 包装：追加哨兵 0、全体 +1，保证"末尾唯一最小"这一前提成立。
// SA(s + $) 的第一项恒为哨兵位置 n，去掉它即得 SA(s)。
static vector<int> buildSaIs(const vector<int>& s, int sigma) {
    int n = (int)s.size();
    if (n == 0) return {};
    vector<int> t(n + 1, 0);
    for (int i = 0; i < n; i++) t[i] = s[i] + 1;
    t[n] = 0;
    vector<int> sa;
    saIsCore(t, sigma, sa);  // t 的最大值为 sigma
    return vector<int>(sa.begin() + 1, sa.end());
}

// ============================ 4. C · Kasai LCP ============================

// lcp[i] = LCP(sa[i-1], sa[i])，lcp[0] = 0。
// 关键性质：LCP(i, j) >= LCP(i-1, j-1) - 1，故 h 只需从上一次的 h-1 继续，
// 总比较次数摊还 O(n)。
static vector<int> buildLcp(const vector<int>& s, const vector<int>& sa,
                            const vector<int>& rk, long long* cmpOut = nullptr) {
    int n = (int)s.size();
    vector<int> lcp(n, 0);
    long long cmp = 0;
    int h = 0;
    for (int i = 0; i < n; i++) {
        int r = rk[i];
        if (r == 0) {
            h = 0;
            continue;
        }
        int j = sa[r - 1];
        while (i + h < n && j + h < n) {
            ++cmp;
            if (s[i + h] != s[j + h]) break;
            ++h;
        }
        lcp[r] = h;
        if (h) --h;
    }
    if (cmpOut) *cmpOut = cmp;
    return lcp;
}

struct LcpOracle {
    int n = 0;
    vector<int> sa, rk, lcp, lg;
    vector<vector<int>> st;

    void build(const vector<int>& s, const vector<int>& saIn) {
        n = (int)s.size();
        sa = saIn;
        rk.assign(n, 0);
        for (int i = 0; i < n; i++) rk[sa[i]] = i;
        lcp = buildLcp(s, sa, rk, nullptr);

        lg.assign(n + 2, 0);
        for (int i = 2; i <= n + 1; i++) lg[i] = lg[i >> 1] + 1;
        int K = (n > 1) ? lg[n] + 1 : 1;
        st.assign(K, vector<int>(n, 0));
        st[0] = lcp;
        for (int k = 1; k < K; k++) {
            int half = 1 << (k - 1);
            for (int i = 0; i + (1 << k) <= n; i++) {
                st[k][i] = min(st[k - 1][i], st[k - 1][i + half]);
            }
        }
    }

    // O(1)：任意两个后缀的 LCP = 名次区间上 lcp 的最小值
    int lcpOf(int i, int j) const {
        if (i == j) return n - i;
        int a = rk[i], b = rk[j];
        if (a > b) swap(a, b);
        int lo = a + 1, hi = b;
        int len = hi - lo + 1;
        int k = lg[len];
        return min(st[k][lo], st[k][hi - (1 << k) + 1]);
    }
};

// ============================ 5. D · 哈希 LCP（oracle） ============================

struct HashLcp {
    static constexpr int MOD1 = 1000000007;
    static constexpr int MOD2 = 1000000009;
    static constexpr int BASE1 = 131;
    static constexpr int BASE2 = 137;

    int n = 0;
    vector<int> p1, p2, h1, h2;

    void build(const vector<int>& s) {
        n = (int)s.size();
        p1.assign(n + 1, 1);
        p2.assign(n + 1, 1);
        h1.assign(n + 1, 0);
        h2.assign(n + 1, 0);
        for (int i = 0; i < n; i++) {
            ll c = s[i] + 1;
            p1[i + 1] = (int)((ll)p1[i] * BASE1 % MOD1);
            p2[i + 1] = (int)((ll)p2[i] * BASE2 % MOD2);
            h1[i + 1] = (int)(((ll)h1[i] * BASE1 + c) % MOD1);
            h2[i + 1] = (int)(((ll)h2[i] * BASE2 + c) % MOD2);
        }
    }

    bool eq(int i, int j, int len) const {
        int a1 = (int)((h1[i + len] - (ll)h1[i] * p1[len] % MOD1 + MOD1) % MOD1);
        int b1 = (int)((h1[j + len] - (ll)h1[j] * p1[len] % MOD1 + MOD1) % MOD1);
        if (a1 != b1) return false;
        int a2 = (int)((h2[i + len] - (ll)h2[i] * p2[len] % MOD2 + MOD2) % MOD2);
        int b2 = (int)((h2[j + len] - (ll)h2[j] * p2[len] % MOD2 + MOD2) % MOD2);
        return a2 == b2;
    }

    int lcp(int i, int j) const {
        int hi = min(n - i, n - j), lo = 0;
        while (lo < hi) {
            int mid = (lo + hi + 1) >> 1;
            if (eq(i, j, mid)) lo = mid;
            else hi = mid - 1;
        }
        return lo;
    }
};

// ============================ 6. 校验工具 ============================

static bool checkPermAndRank(const vector<int>& sa, int n) {
    vector<char> seen(n, 0);
    for (int v : sa) {
        if (v < 0 || v >= n || seen[v]) return false;
        seen[v] = 1;
    }
    return true;
}

// 只靠 lcp 就能 O(n) 验证"严格字典序递增"。
// 注意前缀关系的方向：sa[i-1]=a 必须 < sa[i]=b。
//   b 的 LCP 已到末尾 → b 是 a 的真前缀 → b < a，顺序错；
//   a 的 LCP 已到末尾 → a 是 b 的真前缀 → 顺序对。
static bool checkSortedByLcp(const vector<int>& s, const vector<int>& sa, const vector<int>& lcp) {
    int n = (int)s.size();
    for (int i = 1; i < n; i++) {
        int a = sa[i - 1], b = sa[i], h = lcp[i];
        if (b + h == n) return false;
        if (a + h == n) continue;
        if (!(s[a + h] < s[b + h])) return false;
    }
    return true;
}

// ============================ 7. 应用 ============================

static ll countDistinctSubstrings(const vector<int>& lcp) {
    int n = (int)lcp.size();
    ll total = (ll)n * (n + 1) / 2;
    for (int i = 1; i < n; i++) total -= lcp[i];
    return total;
}

struct RepInfo {
    int len = 0;
    int pos = -1;
};

static RepInfo longestRepeat(const vector<int>& sa, const vector<int>& lcp) {
    RepInfo best;
    for (int i = 1; i < (int)lcp.size(); i++) {
        if (lcp[i] > best.len) {
            best.len = lcp[i];
            best.pos = sa[i];
        }
    }
    return best;
}

static ll distinctBrute(const vector<int>& s) {
    set<vector<int>> st;
    int n = (int)s.size();
    for (int i = 0; i < n; i++) {
        vector<int> cur;
        for (int j = i; j < n; j++) {
            cur.push_back(s[j]);
            st.insert(cur);
        }
    }
    return (ll)st.size();
}

static int longestRepeatBrute(const vector<int>& s) {
    int n = (int)s.size(), best = 0;
    for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
            int h = 0;
            while (j + h < n && s[i + h] == s[j + h]) ++h;
            best = max(best, h);
        }
    }
    return best;
}

struct LcsInfo {
    int len = 0;
    int posA = -1;
    int posB = -1;
};

// 两串拼成 a + {唯一分隔符} + b，公共子串必然是两个"跨半区"后缀的 LCP 的最大值。
static LcsInfo longestCommonSubstring(const vector<int>& a, const vector<int>& b) {
    int na = (int)a.size(), nb = (int)b.size();
    LcsInfo best;
    if (na == 0 || nb == 0) return best;
    vector<int> comb;
    comb.reserve(na + nb + 1);
    for (int x : a) comb.push_back(x + 1);
    comb.push_back(0);
    for (int x : b) comb.push_back(x + 1);
    int maxVal = 0;
    for (int x : comb) maxVal = max(maxVal, x);
    // comb 的值域是 [0, maxVal]，按契约要传"上界（不含）"= maxVal + 1
    vector<int> sa = buildSaIs(comb, maxVal + 1);
    LcpOracle orc;
    orc.build(comb, sa);
    for (int i = 1; i < (int)comb.size(); i++) {
        int p = sa[i - 1], q = sa[i];
        if (p == na || q == na) continue;  // 含分隔符的相邻对不算
        bool pa = (p < na), qa = (q < na);
        if (pa == qa) continue;
        int h = orc.lcp[i];
        if (h > best.len) {
            best.len = h;
            best.posA = pa ? p : q;
            best.posB = pa ? (q - na - 1) : (p - na - 1);
        }
    }
    return best;
}

static LcsInfo lcsBrute(const vector<int>& a, const vector<int>& b) {
    int na = (int)a.size(), nb = (int)b.size();
    vector<vector<int>> dp(na + 1, vector<int>(nb + 1, 0));
    LcsInfo best;
    for (int i = 1; i <= na; i++) {
        for (int j = 1; j <= nb; j++) {
            if (a[i - 1] == b[j - 1]) dp[i][j] = dp[i - 1][j - 1] + 1;
            if (dp[i][j] > best.len) {
                best.len = dp[i][j];
                best.posA = i - dp[i][j];
                best.posB = j - dp[i][j];
            }
        }
    }
    return best;
}

// ============================ 8. 字符串生成 ============================

// kind: 0 随机 1 全同 2 周期 p 3 交替 4 Fibonacci 字
// 值域严格为 [0, sigma-1]，与 buildSaDoubling / buildSaIs 的契约一致
static vector<int> genString(int kind, int n, int sigma, Rng& rng) {
    vector<int> s(n, 0);
    if (kind == 0) {
        for (int i = 0; i < n; i++) s[i] = rng.nextInt(0, max(0, sigma - 1));
    } else if (kind == 1) {
        for (int i = 0; i < n; i++) s[i] = 0;
    } else if (kind == 2) {
        int p = max(1, sigma);
        for (int i = 0; i < n; i++) s[i] = i % p;
    } else if (kind == 3) {
        for (int i = 0; i < n; i++) s[i] = i % 2;
    } else {
        string a = "0", b = "01";
        while ((int)b.size() < n) {
            string c = b + a;
            a = b;
            b = c;
        }
        for (int i = 0; i < n; i++) s[i] = b[i] - '0';
    }
    return s;
}

static const char* kindName(int kind) {
    switch (kind) {
        case 0: return "random";
        case 1: return "all-equal";
        case 2: return "period-p";
        case 3: return "abab";
        default: return "fibonacci";
    }
}

// ============================ 9. 校验组 ============================

// G1 穷举全部长度 <= 10 的二进制串：三方 SA 一致 + 每种 LCP 查询一致
static void group1() {
    cout << "G1 穷举二进制串 (长度 1..10, 共 2046 个)\n";
    long long cnt = 0, pairCnt = 0;
    for (int len = 1; len <= 10; len++) {
        for (int mask = 0; mask < (1 << len); mask++) {
            vector<int> s(len);
            for (int i = 0; i < len; i++) s[i] = (mask >> i) & 1;
            vector<int> a = saBrute(s);
            SAInfo d = buildSaDoubling(s, 2);
            vector<int> b = buildSaIs(s, 2);
            if (d.sa != a) {
                failLine("doubling != brute len=" + to_string(len) + " s=" + vecHead(s, 12));
                return;
            }
            if (b != a) {
                failLine("sais != brute len=" + to_string(len) + " s=" + vecHead(s, 12));
                return;
            }
            if (!checkPermAndRank(d.sa, len)) {
                failLine("sa 不是排列 len=" + to_string(len));
                return;
            }
            LcpOracle orc;
            orc.build(s, b);
            if (!checkSortedByLcp(s, b, orc.lcp)) {
                failLine("lcp 校验未通过 len=" + to_string(len));
                return;
            }
            for (int i = 0; i < len; i++) {
                for (int j = 0; j < len; j++) {
                    int want = lcpBrute(s, i, j);
                    int got = orc.lcpOf(i, j);
                    if (want != got) {
                        failLine("lcp 失配 i=" + to_string(i) + " j=" + to_string(j) +
                                 " want=" + to_string(want) + " got=" + to_string(got));
                        return;
                    }
                    ++pairCnt;
                }
            }
            ++cnt;
        }
    }
    cout << "    串 " << cnt << " 个, LCP 查询 " << pairCnt << " 次, 全部一致\n";
}

// G2 随机串：三种 SA 实现 + 哈希 LCP + 暴力应用
static void group2() {
    cout << "G2 随机串多方对拍\n";
    Rng rng(20261103);
    int sigmas[5] = {1, 2, 3, 4, 26};
    int lens[6] = {1, 2, 3, 7, 40, 300};
    long long cases = 0, lcpChecks = 0, appCases = 0;
    for (int si = 0; si < 5; si++) {
        int sigma = sigmas[si];
        for (int li = 0; li < 6; li++) {
            int n = lens[li];
            for (int rep = 0; rep < 12; rep++) {
                vector<int> s = genString(0, n, sigma, rng);
                vector<int> want = saBrute(s);
                SAInfo d = buildSaDoubling(s, sigma);
                vector<int> b = buildSaIs(s, sigma);
                if (d.sa != want) { failLine("G2 doubling != brute n=" + to_string(n)); return; }
                if (b != want) { failLine("G2 sais != brute n=" + to_string(n)); return; }
                LcpOracle orc;
                orc.build(s, b);
                if (!checkSortedByLcp(s, b, orc.lcp)) { failLine("G2 顺序校验失败"); return; }
                HashLcp hh;
                hh.build(s);
                for (int q = 0; q < 15; q++) {
                    int i = rng.nextInt(0, n - 1), j = rng.nextInt(0, n - 1);
                    int got = orc.lcpOf(i, j);
                    int want2 = hh.lcp(i, j);
                    if (got != want2) {
                        failLine("G2 lcp(sa)=" + to_string(got) + " != lcp(hash)=" + to_string(want2) +
                                 " n=" + to_string(n) + " i=" + to_string(i) + " j=" + to_string(j));
                        return;
                    }
                    ++lcpChecks;
                }
                if (n <= 60) {
                    ll d1 = countDistinctSubstrings(orc.lcp);
                    ll d2 = distinctBrute(s);
                    if (d1 != d2) {
                        failLine("G2 不同子串 " + to_string(d1) + " != " + to_string(d2));
                        return;
                    }
                    int r1 = longestRepeat(b, orc.lcp).len;
                    int r2 = longestRepeatBrute(s);
                    if (r1 != r2) {
                        failLine("G2 最长重复 " + to_string(r1) + " != " + to_string(r2));
                        return;
                    }
                    ++appCases;
                }
                ++cases;
            }
        }
    }
    cout << "    串 " << cases << " 个, LCP 查询 " << lcpChecks
         << " 次, 应用比对 " << appCases << " 组\n";
}

// G3 极端形状：全同 / 周期 / 交替 / Fibonacci —— 倍增法的轮数与后缀序都最刁钻
static void group3() {
    cout << "G3 极端形状串 (全同/周期/交替/Fibonacci)\n";
    Rng rng(777);
    int sizes[5] = {1, 2, 3, 17, 500};
    int roundsTotal = 0, roundCases = 0;
    for (int kind = 1; kind <= 4; kind++) {
        for (int si = 0; si < 5; si++) {
            int n = sizes[si];
            vector<int> s = genString(kind, n, 2, rng);
            int rounds = 0;
            SAInfo d = buildSaDoubling(s, 2, &rounds);
            vector<int> b = buildSaIs(s, 2);
            if (d.sa != b) {
                failLine(string("G3 ") + kindName(kind) + " n=" + to_string(n) + " doubling != sais");
                return;
            }
            if (n <= 500) {
                vector<int> want = saBrute(s);
                if (b != want) {
                    failLine(string("G3 ") + kindName(kind) + " n=" + to_string(n) + " != brute");
                    return;
                }
            }
            if (n >= 17) {
                roundsTotal += rounds;
                ++roundCases;
            }
        }
    }
    cout << "    20 组全部一致; 倍增轮数均值 " << (roundCases ? (double)roundsTotal / roundCases : 0.0)
         << " (n>=17 的 " << roundCases << " 组)\n";
}

// G4 应用：两串最长公共子串，SA 版本 vs O(na*nb) DP
static void group4() {
    cout << "G4 两串最长公共子串 (SA vs DP)\n";
    Rng rng(424242);
    int cases = 0, totalLen = 0;
    for (int rep = 0; rep < 200; rep++) {
        int na = rng.nextInt(1, 40), nb = rng.nextInt(1, 40);
        int sigma = rng.nextInt(1, 3);
        vector<int> a = genString(0, na, sigma, rng);
        vector<int> b = genString(0, nb, sigma, rng);
        LcsInfo x = longestCommonSubstring(a, b);
        LcsInfo y = lcsBrute(a, b);
        if (x.len != y.len) {
            failLine("G4 长度 " + to_string(x.len) + " != " + to_string(y.len) +
                     " na=" + to_string(na) + " nb=" + to_string(nb));
            return;
        }
        // 位置也必须自洽：抽出来的两段确实相等且等长
        if (x.len > 0) {
            if (x.posA < 0 || x.posB < 0 || x.posA + x.len > na || x.posB + x.len > nb) {
                failLine("G4 位置越界");
                return;
            }
            for (int t = 0; t < x.len; t++) {
                if (a[x.posA + t] != b[x.posB + t]) {
                    failLine("G4 抽出的两段不相等");
                    return;
                }
            }
        }
        totalLen += x.len;
        ++cases;
    }
    cout << "    " << cases << " 组一致, 答案长度合计 " << totalLen << "\n";
}

// G5 性能：n = 2e5 四种形状，倍增 vs SA-IS；另在 n = 2e4 上加朴素 std::sort 对照
static void benchOne(int kind, int n, bool withNaive, Rng& rng) {
    vector<int> s = genString(kind, n, (kind == 0 ? 26 : (kind == 2 ? 3 : 2)), rng);
    int rounds = 0;
    Timer t;

    t.reset();
    SAInfo d = buildSaDoubling(s, 26, &rounds);
    double td = t.ms();

    t.reset();
    long long workBefore = 0;
    long long calls = 0;
    g_saisWork = 0;
    g_saisCalls = 0;
    vector<int> b = buildSaIs(s, 26);
    workBefore = g_saisWork;
    calls = g_saisCalls;
    double ts = t.ms();

    double tn = -1.0;
    bool naiveOk = true;
    if (withNaive) {
        t.reset();
        vector<int> naive = saBrute(s);
        tn = t.ms();
        naiveOk = (naive == b);
    }
    if (d.sa != b) failLine("G5 大 n 下 doubling != sais, kind=" + to_string(kind));
    if (!naiveOk) failLine("G5 朴素排序与 SA-IS 不一致");

    LcpOracle orc;
    orc.build(s, b);
    if (!checkSortedByLcp(s, b, orc.lcp)) failLine("G5 大 n 下顺序校验失败");

    double ratio = (double)workBefore / n;
    cout << "    " << left << setw(11) << kindName(kind) << right << " n=" << setw(7) << n
         << "  倍增 " << setw(8) << fixed << setprecision(2) << td << " ms"
         << "  SA-IS " << setw(8) << ts << " ms"
         << "  轮数 " << setw(2) << rounds
         << "  SA-IS 工作量/n " << setw(5) << setprecision(2) << ratio
         << "  递归层数 " << calls;
    if (withNaive) cout << "  朴素 " << setw(9) << tn << " ms";
    cout << "\n";
}

static void group5() {
    cout << "G5 基准 (n=2e5; 朴素对照另在 n=2e4 随机串)\n";
    Rng rng(99991);
    for (int kind = 0; kind <= 3; kind++) benchOne(kind, 200000, false, rng);
    // 只在随机串上跑朴素排序：全同串的逐字符比较是 O(n)，朴素会是 O(n^2 log n)
    benchOne(0, 20000, true, rng);
}

// G6 复杂度断言：只对拍数值永远发现不了 O(n^2) 退化，必须显式计数
static void group6() {
    cout << "G6 复杂度计数\n";
    Rng rng(2026);
    int n = 100000;
    for (int kind = 0; kind <= 3; kind++) {
        int sg = (kind == 0) ? 26 : 2;
        vector<int> s = genString(kind, n, sg, rng);
        vector<int> sa = buildSaIs(s, sg);
        vector<int> rk(n, 0);
        for (int i = 0; i < n; i++) rk[sa[i]] = i;
        long long cmp = 0;
        vector<int> lcp = buildLcp(s, sa, rk, &cmp);
        if (!checkSortedByLcp(s, sa, lcp)) {
            failLine(string("G6 顺序校验失败 ") + kindName(kind));
            return;
        }
        // Kasai 的摊还上界：h 总增量 <= n，加上每个 i 至多一次失配 => <= 2n
        if (cmp > 2LL * n + 5) {
            failLine(string("G6 Kasai 比较次数超上界 ") + kindName(kind) + " cmp=" + to_string(cmp));
            return;
        }
        long long hsum = 0;
        for (int i = 1; i < n; i++) hsum += lcp[i];
        cout << "    " << left << setw(11) << kindName(kind) << right
             << " Kasai 比较 " << setw(7) << cmp << " (" << setw(5) << fixed << setprecision(3)
             << (double)cmp / n << "n)"
             << "  Σlcp/n " << setw(6) << setprecision(2) << (double)hsum / n << "\n";
    }

    // 倍增法轮数上界：每轮 k 翻倍，k < n，故轮数 <= ceil(log2 n)
    for (int m = 1000; m <= 32000; m *= 2) {
        vector<int> s = genString(1, m, 1, rng);  // 全同串：轮数最多
        int rounds = 0;
        buildSaDoubling(s, 1, &rounds);
        int expect = 0;
        while ((1 << expect) < m) ++expect;
        if (rounds > expect) {
            failLine("G6 倍增轮数 " + to_string(rounds) + " > ceil(log2 n)=" + to_string(expect));
            return;
        }
        if (m == 32000) {
            cout << "    全同串 n=" << m << " 轮数 " << rounds
                 << " = ceil(log2 n) " << expect << "\n";
        }
    }
    cout << "    复杂度断言全部通过\n";
}

// ============================ 10. 主程序 ============================

int main() {
    ios::sync_with_stdio(false);
    cout << "===== 0015 后缀数组 SA: 倍增 / SA-IS / Kasai / 应用 =====\n";
    group1();
    group2();
    group3();
    group4();
    group5();
    group6();
    cout << "===== " << (g_fail == 0 ? "ALL PASS" : "FAILED " + to_string(g_fail))
         << " =====\n";
    cout << "注：本程序未在作者本机编译（无 C++ 工具链），数值随机器不同；\n"
         << "    算法正确性由 .verify_mirror_0015.py 的 Python 镜像验证。\n";
    return g_fail == 0 ? 0 : 1;
}
