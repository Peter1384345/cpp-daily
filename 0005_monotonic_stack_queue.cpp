// ============================================================
// 0005 · 单调栈 / 单调队列 (Monotonic Stack & Queue)
// ------------------------------------------------------------
// 三个经典应用:
//   A. 滑动窗口最大值 / 最小值        单调队列 O(n)
//   B. 柱状图中最大矩形               单调栈   O(n)
//   C. 长度不超过 K 的最大子段和      前缀和 + 单调队列 O(n)
// 正确性: 每个应用均与暴力 O(nk) 随机对拍
// 性能:   std::deque 版 vs 手写环形数组版 基准对比
// 编译:   g++ -O2 -std=c++17 -Wall -Wextra 0005_monotonic_stack_queue.cpp -o 0005
// 注意: 本期源码未在本机编译(环境无 C++ 编译器), 算法逻辑已通过
//       Python 逐行镜像对拍验证, 详见 0005_monotonic_stack_queue.md
// ============================================================
#include <bits/stdc++.h>
using namespace std;
using ll = long long;

// ---------- 手写环形数组单调队列(维护最大值, 队列内下标对应值严格递减) ----------
struct MaxQueueRing {
    const vector<ll>& a;
    vector<int> q;          // 环形缓冲区, 存下标
    int head = 0, tail = 0; // 有效区间 [head, tail), 环形意义下
    int cap;
    explicit MaxQueueRing(const vector<ll>& arr) : a(arr), cap((int)arr.size() + 2) {
        q.assign(cap, 0);
    }
    bool empty() const { return head == tail; }
    void push(int i) { // 新下标 i 入队, 弹出所有值 <= a[i] 的队尾
        while (!empty() && a[q[(tail + cap - 1) % cap]] <= a[i])
            tail = (tail + cap - 1) % cap;
        q[tail] = i;
        tail = (tail + 1) % cap;
    }
    void popBefore(int l) { // 弹出所有下标 < l 的队首
        while (!empty() && q[head] < l) head = (head + 1) % cap;
    }
    ll best() const { return a[q[head]]; }
};

// ---------- std::deque 版(对照: 写法简洁, 但节点分散、常数较大) ----------
struct MaxQueueStl {
    const vector<ll>& a;
    deque<int> q;
    explicit MaxQueueStl(const vector<ll>& arr) : a(arr) {}
    void push(int i) {
        while (!q.empty() && a[q.back()] <= a[i]) q.pop_back();
        q.push_back(i);
    }
    void popBefore(int l) {
        while (!q.empty() && q.front() < l) q.pop_front();
    }
    ll best() const { return a[q.front()]; }
};

// ---------- 手写环形数组单调队列(维护最小值) ----------
struct MinQueueRing {
    const vector<ll>& a;
    vector<int> q;
    int head = 0, tail = 0, cap;
    explicit MinQueueRing(const vector<ll>& arr) : a(arr), cap((int)arr.size() + 2) {
        q.assign(cap, 0);
    }
    bool empty() const { return head == tail; }
    void push(int i) { // 弹出所有值 >= a[i] 的队尾, 队列内值严格递增
        while (!empty() && a[q[(tail + cap - 1) % cap]] >= a[i])
            tail = (tail + cap - 1) % cap;
        q[tail] = i;
        tail = (tail + 1) % cap;
    }
    void popBefore(int l) {
        while (!empty() && q[head] < l) head = (head + 1) % cap;
    }
    ll best() const { return a[q[head]]; }
};

// ---------- A. 滑动窗口最大值: 队列实现泛型复用 ----------
template <class Q>
vector<ll> slidingWindowMax(const vector<ll>& a, int k) {
    int n = (int)a.size();
    vector<ll> res;
    if (n == 0 || k <= 0) return res;
    res.reserve(max(0, n - k + 1));
    Q q(a);
    for (int i = 0; i < n; ++i) {
        q.push(i);
        if (i >= k) q.popBefore(i - k + 1); // 窗口左端 = i-k+1
        if (i >= k - 1) res.push_back(q.best());
    }
    return res;
}

vector<ll> slidingWindowMaxBrute(const vector<ll>& a, int k) {
    vector<ll> res;
    int n = (int)a.size();
    for (int i = k - 1; i < n; ++i) {
        ll m = a[i];
        for (int j = i - k + 1; j <= i; ++j) m = max(m, a[j]);
        res.push_back(m);
    }
    return res;
}

// ---------- A2. 滑动窗口最小值 ----------
vector<ll> slidingWindowMin(const vector<ll>& a, int k) {
    int n = (int)a.size();
    vector<ll> res;
    if (n == 0 || k <= 0) return res;
    res.reserve(max(0, n - k + 1));
    MinQueueRing q(a);
    for (int i = 0; i < n; ++i) {
        q.push(i);
        if (i >= k) q.popBefore(i - k + 1);
        if (i >= k - 1) res.push_back(q.best());
    }
    return res;
}

vector<ll> slidingWindowMinBrute(const vector<ll>& a, int k) {
    vector<ll> res;
    int n = (int)a.size();
    for (int i = k - 1; i < n; ++i) {
        ll m = a[i];
        for (int j = i - k + 1; j <= i; ++j) m = min(m, a[j]);
        res.push_back(m);
    }
    return res;
}

// ---------- B. 柱状图中最大矩形: 单调栈 O(n) ----------
ll largestRectangle(const vector<ll>& h) {
    int n = (int)h.size();
    vector<int> st; // 存下标, 对应高度严格递增
    st.reserve(n + 1);
    ll best = 0;
    for (int i = 0; i <= n; ++i) {
        ll cur = (i == n) ? -1 : h[i]; // 末尾哨兵 -1, 强制清空栈
        while (!st.empty() && h[st.back()] > cur) {
            ll height = h[st.back()];
            st.pop_back();
            int left = st.empty() ? -1 : st.back(); // 左侧第一个更矮的位置
            best = max(best, height * (ll)(i - left - 1));
        }
        st.push_back(i);
    }
    return best;
}

ll largestRectangleBrute(const vector<ll>& h) {
    int n = (int)h.size();
    ll best = 0;
    for (int i = 0; i < n; ++i) { // 以 h[i] 为高的最大扩展宽度
        int l = i, r = i;
        while (l > 0 && h[l - 1] >= h[i]) --l;
        while (r + 1 < n && h[r + 1] >= h[i]) ++r;
        best = max(best, h[i] * (ll)(r - l + 1));
    }
    return best;
}

// ---------- C. 长度 <= K 的最大子段和: 前缀和 + 单调队列 O(n) ----------
ll maxSubarrayLenK(const vector<ll>& a, int k) {
    int n = (int)a.size();
    vector<ll> s(n + 1, 0);
    for (int i = 0; i < n; ++i) s[i + 1] = s[i] + a[i];
    MinQueueRing mq(s);     // 队列存前缀和下标 j, 维护 s[j] 最小
    ll best = LLONG_MIN;
    for (int i = 1; i <= n; ++i) {
        mq.push(i - 1);     // 新候选左端点 j = i-1
        mq.popBefore(i - k); // 保留 j >= i-k, 保证子段长 <= k
        best = max(best, s[i] - mq.best());
    }
    return best;
}

ll maxSubarrayLenKBrute(const vector<ll>& a, int k) {
    int n = (int)a.size();
    vector<ll> s(n + 1, 0);
    for (int i = 0; i < n; ++i) s[i + 1] = s[i] + a[i];
    ll best = LLONG_MIN;
    for (int i = 1; i <= n; ++i)
        for (int j = max(0, i - k); j < i; ++j)
            best = max(best, s[i] - s[j]);
    return best;
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    mt19937 rng(20261025);
    bool ok = true;
    auto check = [&](bool cond, const string& name) {
        cout << (cond ? "[PASS] " : "[FAIL] ") << name << "\n";
        if (!cond) ok = false;
    };

    // ---- A. 滑动窗口最大值: 暴力 vs 环形数组队列 vs std::deque ----
    {
        bool all = true;
        for (int t = 0; t < 500 && all; ++t) {
            int n = 1 + (int)(rng() % 60);
            int k = 1 + (int)(rng() % n);
            vector<ll> a(n);
            for (auto& x : a) x = (ll)(rng() % 201) - 100;
            auto brute = slidingWindowMaxBrute(a, k);
            auto r1 = slidingWindowMax<MaxQueueRing>(a, k);
            auto r2 = slidingWindowMax<MaxQueueStl>(a, k);
            if (r1 != brute || r2 != brute) all = false;
        }
        check(all, "A  滑动窗口最大值  暴力 vs 环形数组 vs std::deque (500 轮)");
    }

    // ---- A2. 滑动窗口最小值 ----
    {
        bool all = true;
        for (int t = 0; t < 500 && all; ++t) {
            int n = 1 + (int)(rng() % 60);
            int k = 1 + (int)(rng() % n);
            vector<ll> a(n);
            for (auto& x : a) x = (ll)(rng() % 201) - 100;
            if (slidingWindowMin(a, k) != slidingWindowMinBrute(a, k)) all = false;
        }
        // 边界专项: n=1, k=1, k=n, 全相等
        vector<ll> one = {7};
        if (slidingWindowMin(one, 1) != vector<ll>{7}) all = false;
        vector<ll> eq(10, 5);
        if (slidingWindowMin(eq, 10) != vector<ll>(1, 5)) all = false;
        check(all, "A2 滑动窗口最小值  暴力 vs 环形数组 (500 轮 + 边界)");
    }

    // ---- B. 柱状图中最大矩形 ----
    {
        bool all = true;
        for (int t = 0; t < 400 && all; ++t) {
            int n = 1 + (int)(rng() % 80);
            vector<ll> h(n);
            for (auto& x : h) x = (ll)(rng() % 31); // 含 0 高度
            if (largestRectangle(h) != largestRectangleBrute(h)) all = false;
        }
        // 边界: 全相等 / 严格递增 / 严格递减
        if (largestRectangle(vector<ll>(7, 4)) != 28) all = false;
        if (largestRectangle(vector<ll>{1, 2, 3, 4, 5}) != 9) all = false;
        if (largestRectangle(vector<ll>{5, 4, 3, 2, 1}) != 9) all = false;
        check(all, "B  柱状图最大矩形  暴力 vs 单调栈 (400 轮 + 边界)");
    }

    // ---- C. 长度 <= K 的最大子段和 ----
    {
        bool all = true;
        for (int t = 0; t < 400 && all; ++t) {
            int n = 1 + (int)(rng() % 60);
            int k = 1 + (int)(rng() % n);
            vector<ll> a(n);
            for (auto& x : a) x = (ll)(rng() % 101) - 50;
            if (maxSubarrayLenK(a, k) != maxSubarrayLenKBrute(a, k)) all = false;
        }
        // 边界: k=1 (即最大单元素), k=n (经典最大子段和)
        vector<ll> a1 = {-3, -1, -2};
        if (maxSubarrayLenK(a1, 1) != -1) all = false;
        if (maxSubarrayLenK(a1, 3) != -1) all = false;
        check(all, "C  长度<=K 最大子段和  暴力 vs 前缀和+单调队列 (400 轮 + 边界)");
    }

    // ---- 基准: n=2e6, k=5000 滑动窗口最大值, 环形数组 vs std::deque ----
    {
        const int N = 2000000, K = 5000;
        mt19937_64 rng64(12345);
        vector<ll> big(N);
        for (auto& x : big) x = (ll)(rng64() % 1000000007LL);

        auto t0 = chrono::steady_clock::now();
        auto r1 = slidingWindowMax<MaxQueueRing>(big, K);
        auto t1 = chrono::steady_clock::now();
        auto r2 = slidingWindowMax<MaxQueueStl>(big, K);
        auto t2 = chrono::steady_clock::now();
        double ms1 = chrono::duration<double, milli>(t1 - t0).count();
        double ms2 = chrono::duration<double, milli>(t2 - t1).count();

        check(r1 == r2, "基准  两种实现结果一致 (n=2e6, k=5000)");
        ll cs = 0;
        for (ll v : r1) cs = (cs * 131 + v) % 1000000007LL;
        cout << "  环形数组队列: " << ms1 << " ms | std::deque: " << ms2
             << " ms | 校验和: " << cs << "\n";
    }

    cout << (ok ? "ALL TESTS PASSED" : "SOME TESTS FAILED") << "\n";
    return ok ? 0 : 1;
}
