// 0003 · 稀疏表 Sparse Table —— O(n log n) 预处理、O(1) 区间最值查询
// 变体：分块 ST —— O(n) 级空间、准 O(1) 查询（同块内线性扫描，块间查表）
//
// 编译：g++ -O2 -std=c++17 -Wall -Wextra -o st 0003_sparse_table.cpp
// 程序自带随机对拍（三个实现互拍）与性能/空间基准，全部通过返回码为 0。

#include <bits/stdc++.h>
using namespace std;
using ll = long long;

// ---------------- 经典稀疏表：O(n log n) 空间，O(1) 查询 ----------------
class SparseTable {
public:
    explicit SparseTable(const vector<int>& a) : n_((int)a.size()) {
        lg_.assign(n_ + 1, 0);                 // lg 表必须开到 n+1，查询时 len 最大为 n
        for (int i = 2; i <= n_; ++i) lg_[i] = lg_[i >> 1] + 1;
        LOG_ = lg_[n_] + 1;                    // 层数：覆盖长度 2^(LOG-1) >= n
        st_.assign(LOG_, vector<int>(n_));
        st_[0] = a;
        for (int k = 1; k < LOG_; ++k) {
            const int half = 1 << (k - 1), len = 1 << k;
            for (int i = 0; i + len <= n_; ++i)
                st_[k][i] = min(st_[k - 1][i], st_[k - 1][i + half]);
        }
    }
    // 闭区间 [l, r]，要求 0 <= l <= r < n_；两个可重叠的 2^k 段拼出任意区间
    int query(int l, int r) const {
        const int k = lg_[r - l + 1];
        return min(st_[k][l], st_[k][r - (1 << k) + 1]);  // 注意右端点是 r-2^k+1
    }
    size_t memoryBytes() const {
        size_t s = lg_.size() * sizeof(int);
        for (const auto& v : st_) s += v.size() * sizeof(int);
        return s;
    }
private:
    int n_, LOG_;
    vector<int> lg_;
    vector<vector<int>> st_;
};

// ---------------- 分块 ST：3n 级空间，准 O(1) 查询 ----------------
// 思路：块内前缀 min (pre) + 块内后缀 min (suf) + 块最小值再建一层 ST。
//   - l,r 在同一块      ：块内线性扫，O(B)，B 取 32~64 常数极小
//   - l,r 跨相邻两块    ：min(suf[l], pre[r])，真 O(1)
//   - l,r 隔中间整块    ：min(suf[l], 块间 ST 查询, pre[r])，O(1)
class BlockST {
public:
    explicit BlockST(const vector<int>& a, int B)
        : n_((int)a.size()), B_(max(1, B)), a_(a) {
        m_ = (n_ + B_ - 1) / B_;               // 块数
        pre_.assign(n_, 0);
        suf_.assign(n_, 0);
        bmin_.assign(m_, INT_MAX);
        for (int i = 0; i < n_; ++i) {
            pre_[i] = (i % B_ == 0) ? a[i] : min(pre_[i - 1], a[i]);
            bmin_[i / B_] = min(bmin_[i / B_], a[i]);
        }
        for (int i = n_ - 1; i >= 0; --i)      // 块尾（含末尾残块的实际尾）重置起点
            suf_[i] = ((i + 1) % B_ == 0 || i == n_ - 1) ? a[i] : min(suf_[i + 1], a[i]);
        lg2_.assign(m_ + 1, 0);
        for (int i = 2; i <= m_; ++i) lg2_[i] = lg2_[i >> 1] + 1;
        LOGm_ = lg2_[m_] + 1;
        bst_.assign(LOGm_, vector<int>(m_));
        bst_[0] = bmin_;
        for (int k = 1; k < LOGm_; ++k) {
            const int half = 1 << (k - 1), len = 1 << k;
            for (int i = 0; i + len <= m_; ++i)
                bst_[k][i] = min(bst_[k - 1][i], bst_[k - 1][i + half]);
        }
    }
    int query(int l, int r) const {
        const int bl = l / B_, br = r / B_;
        if (bl == br) {                        // 同块：B 很小，直接扫
            int res = a_[l];
            for (int i = l + 1; i <= r; ++i) res = min(res, a_[i]);
            return res;
        }
        int res = min(suf_[l], pre_[r]);       // 两侧残块
        if (br - bl >= 2) {                    // 中间整块 [bl+1, br-1]
            const int len = br - bl - 1, k = lg2_[len];
            res = min(res, min(bst_[k][bl + 1], bst_[k][br - (1 << k)]));
        }
        return res;
    }
    size_t memoryBytes() const {
        size_t s = (a_.size() + pre_.size() + suf_.size() + bmin_.size() + lg2_.size()) * sizeof(int);
        for (const auto& v : bst_) s += v.size() * sizeof(int);
        return s;
    }
private:
    int n_, B_, m_, LOGm_;
    vector<int> a_, pre_, suf_, bmin_, lg2_;
    vector<vector<int>> bst_;
};

// ---------------- 朴素暴力：对拍基准 ----------------
static int bruteMin(const vector<int>& a, int l, int r) {
    int res = a[l];
    for (int i = l + 1; i <= r; ++i) res = min(res, a[i]);
    return res;
}

static uint64_t rngState = 0x9E3779B97F4A7C15ull;
static uint64_t rnd() {
    rngState ^= rngState << 13; rngState ^= rngState >> 7; rngState ^= rngState << 17;
    return rngState;
}

int main() {
    // ---------- 1. 随机对拍：暴力 vs ST vs 分块 ST ----------
    const int kRounds = 600;
    ll checks = 0;
    for (int round = 0; round < kRounds; ++round) {
        int n = 1 + (int)(rnd() % 300);
        vector<int> a(n);
        for (auto& x : a) x = (int)(rnd() % 41) - 20;   // 小值域，保证大量重复值
        SparseTable st(a);
        BlockST bst(a, 8 + (int)(rnd() % 57));          // 块大小随机，覆盖 1/2 残块等边界

        // 每轮固定做一次全区间查询，保证覆盖 [0, n-1] 边界
        if (st.query(0, n - 1) != bruteMin(a, 0, n - 1) ||
            bst.query(0, n - 1) != bruteMin(a, 0, n - 1)) {
            fprintf(stderr, "FAIL full-range at n=%d\n", n);
            return 1;
        }
        const int kQ = 200;
        for (int q = 0; q < kQ; ++q) {
            int l = (int)(rnd() % n), r = (int)(rnd() % n);
            if (l > r) swap(l, r);
            int b0 = bruteMin(a, l, r), b1 = st.query(l, r), b2 = bst.query(l, r);
            if (b1 != b0 || b2 != b0) {
                fprintf(stderr, "FAIL round=%d n=%d l=%d r=%d brute=%d st=%d bst=%d\n",
                        round, n, l, r, b0, b1, b2);
                return 1;
            }
            ++checks;
        }
    }
    // n=1 极端样例
    {
        vector<int> one{-7};
        SparseTable st(one);
        BlockST bst(one, 4);
        if (st.query(0, 0) != -7 || bst.query(0, 0) != -7) { fputs("FAIL n=1\n", stderr); return 1; }
    }
    printf("[对拍] %d 轮 x 201 次查询，共 %lld 次，三实现全部一致  PASS\n", kRounds, checks + 2);

    // ---------- 2. 性能与空间基准：ST vs 分块 ST ----------
    const int N = 1 << 18;                 // 262144
    const int QN = 1 << 21;                // 2097152 次查询
    vector<int> a(N);
    for (auto& x : a) x = (int)(rnd() % 2000000001) - 1000000000;

    auto t0 = chrono::steady_clock::now();
    SparseTable st(a);
    auto t1 = chrono::steady_clock::now();
    BlockST bst(a, 64);
    auto t2 = chrono::steady_clock::now();

    uint64_t cs1 = 0, cs2 = 0;
    auto q0 = chrono::steady_clock::now();
    for (int q = 0; q < QN; ++q) {
        int l = (int)(rnd() % N), r = (int)(rnd() % N);
        if (l > r) swap(l, r);
        cs1 += (uint64_t)st.query(l, r);
    }
    auto q1 = chrono::steady_clock::now();
    rngState ^= 0xDEADBEEFCAFEF00Dull;     // 两组查询用不同序列但同分布
    for (int q = 0; q < QN; ++q) {
        int l = (int)(rnd() % N), r = (int)(rnd() % N);
        if (l > r) swap(l, r);
        cs2 += (uint64_t)bst.query(l, r);
    }
    auto q2 = chrono::steady_clock::now();

    auto ms = [](chrono::steady_clock::time_point s, chrono::steady_clock::time_point e) {
        return chrono::duration_cast<chrono::milliseconds>(e - s).count();
    };
    printf("[基准] n=%d, 查询数=%d\n", N, QN);
    printf("  稀疏表 ST   : 构建 %lld ms | 查询 %lld ms (%.1f ns/次) | 空间 %.1f MB\n",
           (ll)ms(t0, t1), (ll)ms(q0, q1),
           ms(q0, q1) * 1e6 / QN, st.memoryBytes() / 1048576.0);
    printf("  分块 ST B=64: 构建 %lld ms | 查询 %lld ms (%.1f ns/次) | 空间 %.1f MB\n",
           (ll)ms(t1, t2), (ll)ms(q1, q2),
           ms(q1, q2) * 1e6 / QN, bst.memoryBytes() / 1048576.0);
    printf("  校验和 st=%llu bst=%llu（用于防止查询被编译器优化删除）\n",
           (unsigned long long)cs1, (unsigned long long)cs2);
    return 0;
}
