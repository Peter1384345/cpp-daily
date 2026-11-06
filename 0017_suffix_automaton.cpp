// ============================================================
// 0017 · 后缀自动机 (Suffix Automaton, SAM)
// 考纲等级: [N]  （NOI 大纲“字符串”条目；CSP-S/NOIP 多以哈希/SA 替代）
// 编译: g++ -O2 -std=c++17 -Wall -Wextra -o sam 0017_suffix_automaton.cpp
// 运行: ./sam    返回码 0 = 全部对拍通过；1 = 有检查点失败
//
// 结构:
//   A. SAM       26 字母稠密转移（主实现，含 endpos 计数 / 不同子串 / LCS / 第 k 子串）
//   B. SAMMap    任意字母表稀疏转移（std::map），用于大字符集与交叉对拍
//   C. Brute     独立 oracle：子串集合、逐位置匹配、O(nm) LCS
//   D. G1-G6     对拍 + 结构不变式（状态/转移上界、endpos 等价类）
//   E. B1-B3     基准：建机规模、模式查询（SAM vs 暴力）、LCS（SAM vs 二分+双哈希）
//
// 核心恒等式（本程序的主要断言来源）:
//   (1) 不同子串数 = Σ_v (len[v] - len[link[v]])，v 取遍非根状态
//   (2) Σ_v occ[v] * (len[v] - len[link[v]]) = n(n+1)/2   （所有子串的出现次数总和）
//   (3) 状态 v 的 endpos 集合大小 = occ[v]，且同类串 endpos 完全相同
//   (4) 状态数 ≤ 2n-1，转移数 ≤ 3n-4（n ≥ 3）
// ============================================================
#include <bits/stdc++.h>

// ---------------------------- 工具 ----------------------------
struct Rng {
    unsigned long long s;
    explicit Rng(unsigned long long seed) : s(seed ? seed : 0x9E3779B97F4A7C15ULL) {}
    unsigned long long next() {
        s ^= s << 7;
        s ^= s >> 9;
        return s;
    }
    int nextInt(int n) { return (int)(next() % (unsigned long long)n); }
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
        if (g_fails <= 30) printf("  [FAIL] %s\n", what.c_str());
    }
}

static std::string randomString(Rng& rng, int n, int sigma) {
    std::string s((size_t)n, 'a');
    for (int i = 0; i < n; ++i) s[(size_t)i] = (char)('a' + rng.nextInt(sigma));
    return s;
}

// ============================ A. SAM ============================
// 每个状态代表一个 endpos 等价类：类内所有子串的出现结束位置集合相同。
// len[v]   = 该类中最长串的长度
// link[v]  = 该类“最长串的最长后缀”所属状态（len[link[v]] < len[v]）
// cnt[v]   = 建机时该状态被“前缀终点”命中的次数（克隆置 0），传播后即 |endpos|
class SAM {
public:
    struct State {
        std::array<int, 26> next;
        int len;
        int link;
        int cnt;
        int firstpos;
        bool clone;
        State() : len(0), link(-1), cnt(0), firstpos(-1), clone(false) { next.fill(-1); }
    };

    std::vector<State> st;
    std::vector<int> occ;      // countOcc() 之后的 |endpos|
    int last;
    long long transCount;      // 累计建立的转移条数（含克隆重定向）
    long long cloneCount;

    SAM() { reset(); }

    void reset() {
        st.clear();
        st.push_back(State());
        last = 0;
        transCount = 0;
        cloneCount = 0;
        occ.clear();
    }

    int size() const { return (int)st.size(); }

    // 增量构造：每读入一个字符，最多新增 2 个状态
    int extend(int c) {
        int cur = size();
        st.push_back(State());
        st[cur].len = st[last].len + 1;
        st[cur].cnt = 1;                       // 新前缀终点，贡献 1 个结束位置
        st[cur].firstpos = st[cur].len - 1;

        int p = last;
        while (p != -1 && st[p].next[c] == -1) {
            st[p].next[c] = cur;
            ++transCount;
            p = st[p].link;
        }
        if (p == -1) {
            st[cur].link = 0;
        } else {
            int q = st[p].next[c];
            if (st[p].len + 1 == st[q].len) {
                st[cur].link = q;
            } else {
                // 克隆：把 q 的 endpos 拆成“长度 ≤ len[p]+1”与“更长”两部分
                int clone = size();
                st.push_back(st[q]);
                st[clone].len = st[p].len + 1;
                st[clone].cnt = 0;             // 克隆不是前缀终点
                st[clone].clone = true;
                ++cloneCount;
                while (p != -1 && st[p].next[c] == q) {
                    st[p].next[c] = clone;
                    ++transCount;
                    p = st[p].link;
                }
                st[q].link = clone;
                st[cur].link = clone;
            }
        }
        last = cur;
        return cur;
    }

    void build(const std::string& s) {
        reset();
        st.reserve(2 * s.size() + 2);
        for (char ch : s) extend(ch - 'a');
    }

    // 按 len 计数排序（len ≤ n，O(状态数 + n)）；返回 len 升序的状态序列
    std::vector<int> orderByLen() const {
        int maxLen = 0;
        for (const State& s : st) maxLen = std::max(maxLen, s.len);
        std::vector<int> bucket((size_t)maxLen + 1, 0);
        std::vector<int> order(st.size(), 0);
        for (const State& s : st) ++bucket[(size_t)s.len];
        for (int i = 1; i <= maxLen; ++i) bucket[(size_t)i] += bucket[(size_t)i - 1];
        for (int v = size() - 1; v >= 0; --v) {
            order[(size_t)--bucket[(size_t)st[(size_t)v].len]] = v;
        }
        return order;
    }

    // link 树自底向上合并：|endpos| 由子状态累加得到（必须逆 len 序）
    void countOcc() {
        occ.assign(st.size(), 0);
        for (size_t i = 0; i < st.size(); ++i) occ[i] = st[i].cnt;
        std::vector<int> order = orderByLen();
        for (int i = (int)order.size() - 1; i >= 1; --i) {
            int v = order[(size_t)i];
            if (v == 0) continue;
            occ[(size_t)st[(size_t)v].link] += occ[(size_t)v];
        }
    }

    long long distinctCount() const {
        long long r = 0;
        for (int v = 1; v < size(); ++v) {
            r += (long long)st[(size_t)v].len - st[(size_t)st[(size_t)v].link].len;
        }
        return r;
    }

    // 模式出现次数：沿转移走到状态，答案即该状态的 |endpos|
    int occurrences(const std::string& p) const {
        int v = 0;
        for (char ch : p) {
            int c = ch - 'a';
            if (c < 0 || c >= 26) return 0;
            v = st[(size_t)v].next[(size_t)c];
            if (v == -1) return 0;
        }
        return occ[(size_t)v];
    }

    // O(|t|) 最长公共子串：失配时沿 link 收缩，l 始终等于当前匹配长度
    int longestCommonSubstring(const std::string& t) const {
        int v = 0;
        int l = 0;
        int best = 0;
        for (char ch : t) {
            int c = ch - 'a';
            if (c < 0 || c >= 26) { v = 0; l = 0; continue; }
            while (v != 0 && st[(size_t)v].next[(size_t)c] == -1) {
                v = st[(size_t)v].link;
                l = st[(size_t)v].len;
            }
            if (st[(size_t)v].next[(size_t)c] != -1) {
                v = st[(size_t)v].next[(size_t)c];
                ++l;
            } else {
                v = 0;
                l = 0;
            }
            best = std::max(best, l);
        }
        return best;
    }

    // g[v] = 从 v 出发能走出的“非空”不同字符串个数（DAG 上路径计数）
    std::vector<long long> pathCounts() const {
        std::vector<long long> g(st.size(), 0);
        std::vector<int> order = orderByLen();
        for (int i = (int)order.size() - 1; i >= 0; --i) {
            int v = order[(size_t)i];
            long long sum = 0;
            for (int c = 0; c < 26; ++c) {
                int u = st[(size_t)v].next[(size_t)c];
                if (u != -1) sum += 1 + g[(size_t)u];
            }
            g[(size_t)v] = sum;
        }
        return g;
    }

    // 字典序第 k 个不同子串（1-indexed）；每条转移贡献“1 个字符本身 + 其后续”
    bool kthDistinct(long long k, std::string& out) const {
        out.clear();
        if (k <= 0) return false;
        std::vector<long long> g = pathCounts();
        if (k > g[0]) return false;
        int v = 0;
        while (true) {
            bool moved = false;
            for (int c = 0; c < 26 && !moved; ++c) {
                int u = st[(size_t)v].next[(size_t)c];
                if (u == -1) continue;
                long long block = 1 + g[(size_t)u];
                if (k > block) {
                    k -= block;
                    continue;
                }
                out.push_back((char)('a' + c));
                if (k == 1) return true;
                --k;
                v = u;
                moved = true;
            }
            if (!moved) return false;
        }
    }

    // 计重第 k 个子串（P3975 的“本质不同/计重”两问中的计重版）
    // 走到状态 u 的串出现 occ[u] 次，故该分支权重 = occ[u] + h[u]
    bool kthWithRepeat(long long k, std::string& out) const {
        out.clear();
        if (k <= 0 || occ.size() != st.size()) return false;
        std::vector<long long> h(st.size(), 0);
        std::vector<int> order = orderByLen();
        for (int i = (int)order.size() - 1; i >= 0; --i) {
            int v = order[(size_t)i];
            long long sum = 0;
            for (int c = 0; c < 26; ++c) {
                int u = st[(size_t)v].next[(size_t)c];
                if (u != -1) sum += (long long)occ[(size_t)u] + h[(size_t)u];
            }
            h[(size_t)v] = sum;
        }
        if (k > h[0]) return false;
        int v = 0;
        while (true) {
            bool moved = false;
            for (int c = 0; c < 26 && !moved; ++c) {
                int u = st[(size_t)v].next[(size_t)c];
                if (u == -1) continue;
                long long w = (long long)occ[(size_t)u] + h[(size_t)u];
                if (k > w) {
                    k -= w;
                    continue;
                }
                out.push_back((char)('a' + c));
                if (k <= occ[(size_t)u]) return true;
                k -= occ[(size_t)u];
                v = u;
                moved = true;
            }
            if (!moved) return false;
        }
    }
};

// ========================== B. SAMMap ==========================
// 同一算法，转移用 std::map 存储：O(σ) 的稠密数组在 σ 很大时不可接受
class SAMMap {
public:
    struct State {
        std::map<int, int> next;
        int len;
        int link;
        int cnt;
        int firstpos;
        State() : len(0), link(-1), cnt(0), firstpos(-1) {}
    };

    std::vector<State> st;
    int last;
    long long transCount;

    SAMMap() { reset(); }

    void reset() {
        st.clear();
        st.push_back(State());
        last = 0;
        transCount = 0;
    }

    int size() const { return (int)st.size(); }

    int extend(int c) {
        int cur = size();
        st.push_back(State());
        st[cur].len = st[last].len + 1;
        st[cur].cnt = 1;
        st[cur].firstpos = st[cur].len - 1;

        int p = last;
        while (p != -1 && st[(size_t)p].next.find(c) == st[(size_t)p].next.end()) {
            st[(size_t)p].next[c] = cur;
            ++transCount;
            p = st[(size_t)p].link;
        }
        if (p == -1) {
            st[cur].link = 0;
        } else {
            int q = st[(size_t)p].next[c];
            if (st[(size_t)p].len + 1 == st[(size_t)q].len) {
                st[cur].link = q;
            } else {
                int clone = size();
                st.push_back(State());
                st[clone].next = st[(size_t)q].next;
                st[clone].len = st[(size_t)p].len + 1;
                st[clone].link = st[(size_t)q].link;
                st[clone].cnt = 0;
                st[clone].firstpos = st[(size_t)q].firstpos;
                while (p != -1) {
                    std::map<int, int>::iterator it = st[(size_t)p].next.find(c);
                    if (it == st[(size_t)p].next.end() || it->second != q) break;
                    it->second = clone;
                    ++transCount;
                    p = st[(size_t)p].link;
                }
                st[(size_t)q].link = clone;
                st[cur].link = clone;
            }
        }
        last = cur;
        return cur;
    }

    void build(const std::string& s) {
        reset();
        for (char ch : s) extend((int)(unsigned char)ch);
    }

    std::vector<int> orderByLen() const {
        int maxLen = 0;
        for (const State& s : st) maxLen = std::max(maxLen, s.len);
        std::vector<int> bucket((size_t)maxLen + 1, 0);
        std::vector<int> order(st.size(), 0);
        for (const State& s : st) ++bucket[(size_t)s.len];
        for (int i = 1; i <= maxLen; ++i) bucket[(size_t)i] += bucket[(size_t)i - 1];
        for (int v = size() - 1; v >= 0; --v) {
            order[(size_t)--bucket[(size_t)st[(size_t)v].len]] = v;
        }
        return order;
    }

    std::vector<int> occOf() const {
        std::vector<int> occ(st.size(), 0);
        for (size_t i = 0; i < st.size(); ++i) occ[i] = st[i].cnt;
        std::vector<int> order = orderByLen();
        for (int i = (int)order.size() - 1; i >= 1; --i) {
            int v = order[(size_t)i];
            if (v == 0) continue;
            occ[(size_t)st[(size_t)v].link] += occ[(size_t)v];
        }
        return occ;
    }

    long long distinctCount() const {
        long long r = 0;
        for (int v = 1; v < size(); ++v) {
            r += (long long)st[(size_t)v].len - st[(size_t)st[(size_t)v].link].len;
        }
        return r;
    }

    int occurrences(const std::string& p, const std::vector<int>& occ) const {
        int v = 0;
        for (char ch : p) {
            int c = (int)(unsigned char)ch;
            std::map<int, int>::const_iterator it = st[(size_t)v].next.find(c);
            if (it == st[(size_t)v].next.end()) return 0;
            v = it->second;
        }
        return occ[(size_t)v];
    }
};

// =========================== C. Brute ===========================
static std::set<std::string> bruteDistinctSet(const std::string& s) {
    std::set<std::string> st;
    const int n = (int)s.size();
    for (int i = 0; i < n; ++i) {
        std::string cur;
        for (int j = i; j < n; ++j) {
            cur.push_back(s[(size_t)j]);
            st.insert(cur);
        }
    }
    return st;
}

static int bruteOcc(const std::string& text, const std::string& pat) {
    if (pat.empty()) return 0;
    const int n = (int)text.size();
    const int m = (int)pat.size();
    int cnt = 0;
    for (int i = 0; i + m <= n; ++i) {
        bool ok = true;
        for (int j = 0; j < m; ++j) {
            if (text[(size_t)(i + j)] != pat[(size_t)j]) { ok = false; break; }
        }
        if (ok) ++cnt;
    }
    return cnt;
}

static std::vector<int> bruteEnds(const std::string& text, const std::string& pat) {
    std::vector<int> ends;
    const int n = (int)text.size();
    const int m = (int)pat.size();
    for (int i = 0; i + m <= n; ++i) {
        bool ok = true;
        for (int j = 0; j < m; ++j) {
            if (text[(size_t)(i + j)] != pat[(size_t)j]) { ok = false; break; }
        }
        if (ok) ends.push_back(i + m - 1);
    }
    return ends;
}

// distinctOnly=true: 字典序不同子串；false: 全部子串（含重复）排序，供计重 kth 对拍
static std::vector<std::string> bruteSorted(const std::string& s, bool distinctOnly) {
    std::vector<std::string> v;
    const int n = (int)s.size();
    if (distinctOnly) {
        std::set<std::string> st = bruteDistinctSet(s);
        v.assign(st.begin(), st.end());
    } else {
        for (int i = 0; i < n; ++i) {
            std::string cur;
            for (int j = i; j < n; ++j) {
                cur.push_back(s[(size_t)j]);
                v.push_back(cur);
            }
        }
        std::sort(v.begin(), v.end());
    }
    return v;
}

// 最长公共“子串”（连续）：失配处必须归零，不能取 max —— 这是
// 与“最长公共子序列”最容易混淆的一处（本期镜像首轮即踩中）。
static int bruteLcs(const std::string& a, const std::string& b) {
    const int n = (int)a.size();
    const int m = (int)b.size();
    std::vector<int> prev((size_t)m + 1, 0), cur((size_t)m + 1, 0);
    int best = 0;
    for (int i = 1; i <= n; ++i) {
        std::fill(cur.begin(), cur.end(), 0);
        for (int j = 1; j <= m; ++j) {
            if (a[(size_t)(i - 1)] == b[(size_t)(j - 1)]) {
                cur[(size_t)j] = prev[(size_t)(j - 1)] + 1;
                best = std::max(best, cur[(size_t)j]);
            } else {
                cur[(size_t)j] = 0;
            }
        }
        prev.swap(cur);
    }
    return best;
}

// ====================== D. 对拍与不变式 ======================
// G1: 小串全量对拍（不同子串数 + 每个子串出现次数 + 计数恒等式）
static void testG1() {
    printf("[G1] 小串全量对拍: 不同子串 / 每个子串 occ / Σ occ×(len-link.len)\n");
    Rng rng(1001ULL);
    long long subs = 0;
    long long clonesSeen = 0;
    int rounds = 200;
    for (int round = 0; round < rounds; ++round) {
        int sigma = 2 + round % 3;
        int n = 1 + rng.nextInt(36);
        std::string s = randomString(rng, n, sigma);
        SAM sam;
        sam.build(s);
        sam.countOcc();

        std::set<std::string> bs = bruteDistinctSet(s);
        clonesSeen += sam.cloneCount;
        check(sam.distinctCount() == (long long)bs.size(), "G1 不同子串数");
        check((long long)sam.size() <= 2LL * n, "G1 状态数 ≤ 2n");
        check(sam.transCount <= 3LL * n, "G1 转移数 ≤ 3n");
        check(sam.occ[(size_t)0] == n, "G1 根 occ 累加为 n");

        long long ident = 0;
        for (int v = 1; v < sam.size(); ++v) {
            ident += (long long)sam.occ[(size_t)v] *
                     (sam.st[(size_t)v].len - sam.st[(size_t)sam.st[(size_t)v].link].len);
        }
        check(ident == (long long)n * (n + 1) / 2, "G1 Σ occ×(len-link.len) = n(n+1)/2");

        for (std::set<std::string>::const_iterator it = bs.begin(); it != bs.end(); ++it) {
            ++subs;
            int got = sam.occurrences(*it);
            int want = bruteOcc(s, *it);
            if (got != want) {
                check(false, "G1 子串 occ 失配: " + *it);
                break;
            }
        }
    }
    printf("      %d 组小串, %lld 个子串出现次数逐一对拍, 覆盖 %lld 个克隆状态\n",
           rounds, subs, clonesSeen);
}

// G2: 第 k 个不同子串 / 计重第 k 子串（vs 排序枚举）+ 路径计数恒等式
static void testG2() {
    printf("[G2] 第 k 子串（本质不同 / 计重）vs 排序枚举\n");
    Rng rng(2002ULL);
    long long kchecks = 0;
    for (int round = 0; round < 100; ++round) {
        int sigma = 2 + round % 2;
        int n = 1 + rng.nextInt(12);
        std::string s = randomString(rng, n, sigma);
        SAM sam;
        sam.build(s);
        sam.countOcc();

        std::vector<std::string> distinct = bruteSorted(s, true);
        std::vector<std::string> multi = bruteSorted(s, false);

        std::vector<long long> g = sam.pathCounts();
        check(g[0] == (long long)distinct.size(), "G2 路径数 = 不同子串数");

        for (size_t k = 1; k <= distinct.size(); ++k) {
            std::string out;
            check(sam.kthDistinct((long long)k, out), "G2 kthDistinct 应返回 true");
            check(out == distinct[k - 1], "G2 kthDistinct 串失配");
            ++kchecks;
        }
        std::string tmp;
        check(!sam.kthDistinct((long long)distinct.size() + 1, tmp), "G2 kthDistinct 越界应 false");
        check(!sam.kthDistinct(0, tmp), "G2 kthDistinct k=0 应 false");

        for (size_t k = 1; k <= multi.size(); ++k) {
            std::string out;
            check(sam.kthWithRepeat((long long)k, out), "G2 kthRepeat 应返回 true");
            check(out == multi[k - 1], "G2 kthRepeat 串失配");
            ++kchecks;
        }
        check(!sam.kthWithRepeat((long long)multi.size() + 1, tmp), "G2 kthRepeat 越界应 false");
    }
    printf("      %lld 次第 k 串查询全部吻合\n", kchecks);
}

// G3: 最长公共子串 vs O(nm) DP
static void testG3() {
    printf("[G3] 最长公共子串 vs O(nm) DP\n");
    Rng rng(3003ULL);
    int rounds = 200;
    for (int round = 0; round < rounds; ++round) {
        int sigma = 2 + round % 2;
        int n = 1 + rng.nextInt(40);
        int m = 1 + rng.nextInt(40);
        std::string a = randomString(rng, n, sigma);
        std::string b = randomString(rng, m, sigma);
        SAM sam;
        sam.build(a);
        int got = sam.longestCommonSubstring(b);
        int want = bruteLcs(a, b);
        if (got != want) {
            check(false, "G3 LCS 失配 a=" + a + " b=" + b + " got=" +
                         std::to_string(got) + " want=" + std::to_string(want));
            break;
        }
    }
    check(true, "G3 全部随机对");
    {
        SAM sam;
        sam.build("abc");
        check(sam.longestCommonSubstring("") == 0, "G3 空 t 的 LCS = 0");
        sam.build("");
        check(sam.longestCommonSubstring("abc") == 0, "G3 空 s 的 LCS = 0");
    }
    printf("      %d 组随机串 + 空串边界\n", rounds);
}

// G4: 边界与退化串
static void testG4() {
    printf("[G4] 边界: n=1 / 全同 / 全异 / 周期串 / 不存在模式 / 空串\n");
    {
        SAM sam;
        sam.build("a");
        sam.countOcc();
        check(sam.size() == 2, "G4 n=1 状态数 = 2");
        check(sam.distinctCount() == 1, "G4 n=1 不同子串 = 1");
        check(sam.occurrences("a") == 1, "G4 n=1 occ(a) = 1");
        check(sam.longestCommonSubstring("a") == 1, "G4 LCS(a,a) = 1");
        check(sam.longestCommonSubstring("b") == 0, "G4 LCS(a,b) = 0");
    }
    {
        std::string s(50, 'a');
        SAM sam;
        sam.build(s);
        sam.countOcc();
        check(sam.distinctCount() == 50, "G4 a^50 不同子串 = 50");
        check(sam.occurrences("a") == 50, "G4 occ(a) = 50");
        check(sam.occurrences("aa") == 49, "G4 occ(aa) = 49");
        check(sam.occurrences(std::string(51, 'a')) == 0, "G4 超长模式 occ = 0");
        std::string out;
        check(sam.kthDistinct(50, out) && out == s, "G4 第 50 个不同子串 = a^50");
        // 计重总数 = 50*51/2 = 1275，最后一个才是 a^50
        check(sam.kthWithRepeat(1275, out) && out == s, "G4 计重第 1275 个 = a^50");
        check(!sam.kthWithRepeat(1276, out), "G4 计重越界 = false");
    }
    {
        std::string s;
        for (int i = 0; i < 26; ++i) s.push_back((char)('a' + i));
        SAM sam;
        sam.build(s);
        sam.countOcc();
        check(sam.distinctCount() == 26LL * 27 / 2, "G4 26 个互异字符 不同子串 = 351");
        check(sam.longestCommonSubstring("zyxwvutsrqponmlkjihgfedcba") == 1, "G4 逆序 LCS = 1");
    }
    {
        SAM sam;
        sam.build("abababab");
        sam.countOcc();
        check(sam.distinctCount() == (long long)bruteDistinctSet("abababab").size(),
              "G4 abababab 不同子串");
        check(sam.occurrences("zzz") == 0, "G4 不存在模式 occ = 0");
        check(sam.occurrences("abababab") == 1, "G4 模式=整串 occ = 1");
        check(sam.occurrences("abab") == 3, "G4 occ(abab) = 3");
    }
    {
        SAM sam;
        sam.build("");
        sam.countOcc();
        check(sam.size() == 1, "G4 空串只有根");
        check(sam.distinctCount() == 0, "G4 空串不同子串 = 0");
        check(sam.longestCommonSubstring("abc") == 0, "G4 空串 LCS = 0");
    }
    printf("      6 组边界场景完成\n");
}

// G5: 大字母表（σ=100）稀疏转移版 vs 暴力集合
static void testG5() {
    printf("[G5] 大字母表 σ=100: SAMMap vs 暴力集合\n");
    Rng rng(5005ULL);
    long long subs = 0;
    for (int round = 0; round < 50; ++round) {
        int n = 1 + rng.nextInt(120);
        std::string s;
        s.resize((size_t)n);
        for (int i = 0; i < n; ++i) s[(size_t)i] = (char)rng.nextInt(100);
        SAMMap sam;
        sam.build(s);
        std::vector<int> occ = sam.occOf();
        std::set<std::string> bs = bruteDistinctSet(s);
        check(sam.distinctCount() == (long long)bs.size(), "G5 大字母表不同子串数");
        check((long long)sam.size() <= 2LL * n, "G5 状态数 ≤ 2n");
        const int probe = 40;
        for (int t = 0; t < probe && !bs.empty(); ++t) {
            std::set<std::string>::const_iterator it = bs.begin();
            std::advance(it, (size_t)rng.nextInt((int)bs.size()));
            int got = sam.occurrences(*it, occ);
            int want = bruteOcc(s, *it);
            if (got != want) {
                check(false, "G5 大字母表 occ 失配");
                break;
            }
            ++subs;
        }
    }
    printf("      50 组 σ=100 串, %lld 次 occ 抽样对拍\n", subs);
}

// G6: 结构不变式 —— len 单调、转移长度、endpos 等价类
static void testG6() {
    printf("[G6] 结构不变式: len[link]<len / 转移长度 / endpos 等价类\n");
    Rng rng(6006ULL);
    int states = 0;
    for (int round = 0; round < 30; ++round) {
        int n = 1 + rng.nextInt(120);
        std::string s = randomString(rng, n, 3);
        SAM sam;
        sam.build(s);
        sam.countOcc();
        states += sam.size();

        for (int v = 1; v < sam.size(); ++v) {
            int lk = sam.st[(size_t)v].link;
            if (lk < 0 || sam.st[(size_t)lk].len >= sam.st[(size_t)v].len) {
                check(false, "G6 link 长度单调性");
                break;
            }
            if (sam.occ[(size_t)v] <= 0) {
                check(false, "G6 occ 必须为正");
                break;
            }
            int L = sam.st[(size_t)v].len;
            int fp = sam.st[(size_t)v].firstpos;
            if (fp < L - 1) {
                check(false, "G6 firstpos 与 len 矛盾");
                break;
            }
            std::string longest = s.substr((size_t)(fp - L + 1), (size_t)L);
            std::vector<int> ends = bruteEnds(s, longest);
            if ((int)ends.size() != sam.occ[(size_t)v]) {
                check(false, "G6 |endpos| = occ");
                break;
            }
            // 同类中最短串（长度 len[link]+1）是 longest 的后缀，endpos 必须一致
            int shortLen = sam.st[(size_t)lk].len + 1;
            std::string shortest = longest.substr((size_t)(L - shortLen), (size_t)shortLen);
            if (bruteEnds(s, shortest) != ends) {
                check(false, "G6 同类串 endpos 相同");
                break;
            }
        }
        // 每条转移 v -c-> u 满足 len[u] >= len[v]+1
        for (int v = 0; v < sam.size(); ++v) {
            for (int c = 0; c < 26; ++c) {
                int u = sam.st[(size_t)v].next[(size_t)c];
                if (u >= 0 && sam.st[(size_t)u].len < sam.st[(size_t)v].len + 1) {
                    check(false, "G6 转移长度单调");
                    v = sam.size();
                    break;
                }
            }
        }
    }
    printf("      30 组串, 累计 %d 个状态的不变式检查\n", states);
}

// =========================== E. 基准 ===========================
// DoubleHash: 双模滚动哈希，仅用于 B3 的“另一条复杂度路线”对照
struct DoubleHash {
    static constexpr long long M1 = 1000000007LL;
    static constexpr long long M2 = 1000000009LL;
    static constexpr long long BASE = 911382323LL;

    int n = 0;
    std::vector<long long> h1, h2, p1, p2;

    void init(const std::string& s) {
        n = (int)s.size();
        h1.assign((size_t)n + 1, 0);
        h2.assign((size_t)n + 1, 0);
        p1.assign((size_t)n + 1, 1);
        p2.assign((size_t)n + 1, 1);
        for (int i = 0; i < n; ++i) {
            long long v = (long long)(unsigned char)s[(size_t)i] + 1;
            p1[(size_t)i + 1] = p1[(size_t)i] * BASE % M1;
            p2[(size_t)i + 1] = p2[(size_t)i] * BASE % M2;
            h1[(size_t)i + 1] = (h1[(size_t)i] * BASE + v) % M1;
            h2[(size_t)i + 1] = (h2[(size_t)i] * BASE + v) % M2;
        }
    }

    unsigned long long key(int l, int len) const {
        long long a = (h1[(size_t)(l + len)] - h1[(size_t)l] * p1[(size_t)len] % M1 + M1) % M1;
        long long b = (h2[(size_t)(l + len)] - h2[(size_t)l] * p2[(size_t)len] % M2 + M2) % M2;
        return ((unsigned long long)a << 32) | (unsigned long long)b;
    }
};

static int hashLcs(const std::string& a, const std::string& b) {
    DoubleHash ha, hb;
    ha.init(a);
    hb.init(b);
    int lo = 0;
    int hi = std::min((int)a.size(), (int)b.size());
    std::unordered_set<unsigned long long> seen;
    while (lo < hi) {
        int mid = (lo + hi + 1) / 2;
        seen.clear();
        seen.reserve((size_t)((int)a.size() - mid + 1) * 2 + 8);
        for (int i = 0; i + mid <= (int)a.size(); ++i) seen.insert(ha.key(i, mid));
        bool ok = false;
        for (int i = 0; i + mid <= (int)b.size() && !ok; ++i) {
            if (seen.count(hb.key(i, mid))) ok = true;
        }
        if (ok) lo = mid;
        else hi = mid - 1;
    }
    return lo;
}

static void benchB1() {
    const int n = 200000;
    Rng rng(7007ULL);
    std::string s = randomString(rng, n, 4);
    double t0 = nowMs();
    SAM sam;
    sam.build(s);
    sam.countOcc();
    double t1 = nowMs();
    long long distinct = sam.distinctCount();
    long long ident = 0;
    for (int v = 1; v < sam.size(); ++v) {
        ident += (long long)sam.occ[(size_t)v] *
                 (sam.st[(size_t)v].len - sam.st[(size_t)sam.st[(size_t)v].link].len);
    }
    double memKB = (double)sam.size() * (double)sizeof(SAM::State) / 1024.0;
    printf("[B1] n=%d σ=4 建机+计数 %.2f ms | 状态 %d (2n=%d) 转移 %lld 克隆 %lld | "
           "不同子串 %lld | 稠密表内存 %.1f KB\n",
           n, t1 - t0, sam.size(), 2 * n, sam.transCount, sam.cloneCount,
           distinct, memKB);
    check((long long)sam.size() <= 2LL * n, "B1 状态数上界");
    check(sam.transCount <= 3LL * n, "B1 转移数上界");
    check(ident == (long long)n * (n + 1) / 2, "B1 计数恒等式");
    check(sam.occurrences(s.substr(0, 20)) == bruteOcc(s, s.substr(0, 20)), "B1 前缀 occ 抽检");
}

static void benchB2() {
    const int n = 50000;
    const int q = 300;
    const int plen = 12;
    Rng rng(8008ULL);
    std::string text = randomString(rng, n, 2);
    std::vector<std::string> pats;
    pats.reserve((size_t)q);
    for (int i = 0; i < q; ++i) {
        if (i % 2 == 0) {
            int pos = rng.nextInt(n - plen + 1);
            pats.push_back(text.substr((size_t)pos, (size_t)plen));
        } else {
            pats.push_back(randomString(rng, plen, 2));
        }
    }

    SAM sam;
    double t0 = nowMs();
    sam.build(text);
    sam.countOcc();
    long long sumSam = 0;
    for (int i = 0; i < q; ++i) sumSam += sam.occurrences(pats[(size_t)i]);
    double t1 = nowMs();

    long long sumBrute = 0;
    for (int i = 0; i < q; ++i) sumBrute += bruteOcc(text, pats[(size_t)i]);
    double t2 = nowMs();

    printf("[B2] 模式查询 n=%d q=%d |p|=%d | SAM %.2f ms (建机+%d 查询) 合计驻留 %lld | "
           "逐模式暴力 %.2f ms 合计 %lld | 加速 %.1fx\n",
           n, q, plen, t1 - t0, q, sumSam, t2 - t1, sumBrute, (t2 - t1) / (t1 - t0));
    check(sumSam == sumBrute, "B2 两种查询方式校验和相等");
}

static void benchB3() {
    const int n = 100000;
    Rng rng(9009ULL);
    std::string a = randomString(rng, n, 2);
    std::string b = randomString(rng, n, 2);

    SAM sam;
    double t0 = nowMs();
    sam.build(a);
    int lcsSam = sam.longestCommonSubstring(b);
    double t1 = nowMs();

    int lcsHash = hashLcs(a, b);
    double t2 = nowMs();

    printf("[B3] LCS n=m=%d σ=2 | SAM O(n+m) %.2f ms -> %d | 二分+双哈希 "
           "O((n+m)log n) %.2f ms -> %d | 加速 %.1fx\n",
           n, t1 - t0, lcsSam, t2 - t1, lcsHash, (t2 - t1) / (t1 - t0));
    check(lcsSam == lcsHash, "B3 SAM LCS = 双哈希 LCS");
}

int main() {
    printf("=== 0017 后缀自动机 SAM 验证（考纲 [N]）===\n");
    double t0 = nowMs();

    testG1();
    testG2();
    testG3();
    testG4();
    testG5();
    testG6();
    benchB1();
    benchB2();
    benchB3();

    double t1 = nowMs();
    printf("--- 检查点 %lld, 失败 %lld, 总耗时 %.1f ms ---\n", g_checks, g_fails, t1 - t0);
    if (g_fails == 0) {
        printf("RESULT: ALL PASS\n");
        return 0;
    }
    printf("RESULT: FAILED\n");
    return 1;
}
