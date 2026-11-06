// ============================================================
// 0006 · 二叉堆 / 优先队列 (Binary Heap & Priority Queue)
// ------------------------------------------------------------
// 五个部分:
//   A. DHeap<D>  手写 d 叉堆: hole 下沉(每层 1 次写)、Floyd O(n) 建堆
//   B. 建堆对比   Floyd O(n) vs 逐个 push O(n log n) —— 对拍 + 基准
//   C. heapSort   原地堆排序(复用 hole 下沉, 零额外内存)
//   D. LazyDeleteHeap  可删除堆: 惰性删除 + 失效比例超阈值 O(n) 重建
//   E. DualHeap   对顶堆动态中位数(大根堆存小半 + 小根堆存大半)
// 正确性: 每一部分均与暴力/multiset/std::sort 随机对拍
// 性能:   建堆两种方式、D=2 vs D=4、堆排序 vs std::sort
// 编译:   g++ -O2 -std=c++17 -Wall -Wextra 0006_binary_heap.cpp -o 0006
// 注意:   本期源码未在本机编译(环境无 C++ 编译器), 算法逻辑已通过
//         Python 逐行镜像对拍验证, 详见 0006_binary_heap.md
// ============================================================
#include <bits/stdc++.h>
using namespace std;
using ll = long long;

static int g_fail = 0;

#define CHECK(cond, ...)                          \
    do {                                          \
        if (!(cond)) {                            \
            printf("    [FAIL] " __VA_ARGS__);    \
            printf("\n");                         \
            ++g_fail;                             \
        }                                         \
    } while (0)

// ============================================================
// A. d 叉堆(手写)  D=2 即二叉堆
//    不变式: cmp_(h_[i], h_[child]) == false  →  默认 less 得到大根堆
//    全部用 0-index: 子节点 D*i+1 .. D*i+D, 父节点 (i-1)/D
// ============================================================
template <class T, int D = 2, class Cmp = std::less<T>>
class DHeap {
public:
    explicit DHeap(Cmp c = Cmp()) : cmp_(c) {}

    bool   empty() const { return h_.empty(); }
    size_t size()  const { return h_.size(); }
    const T& top() const { return h_[0]; }
    Cmp  cmp()     const { return cmp_; }

    void reserve(size_t n) { h_.reserve(n); }

    // 入堆: 上浮, hole 法(先挖坑再一次性落位, 每层只写 1 次而非 3 次)
    void push(const T& v) {
        h_.push_back(v);
        int i = (int)h_.size() - 1;
        while (i > 0) {
            int p = (i - 1) / D;
            if (!cmp_(h_[p], v)) break;   // 父节点已不劣于 v, 停
            h_[i] = h_[p];
            i = p;
        }
        h_[i] = v;
    }

    // 出堆: 堆顶被"最后一个元素"或"无穷差"顶替后下沉
    void pop() {
        int n = (int)h_.size();
        if (n <= 1) { h_.clear(); return; }
        T v = h_.back();
        h_.pop_back();
        siftDownHole(0, v, (int)h_.size());
    }

    // Floyd 建堆: 从最后一个非叶节点逆序下沉, 总代价 O(n)
    void build(vector<T>&& arr) {
        h_ = std::move(arr);
        int n = (int)h_.size();
        if (n < 2) return;                       // 空堆 / 单元素已合法
        for (int i = (n - 2) / D; i >= 0; --i)   // 最后一个非叶节点
            siftDownHole(i, h_[i], n);
    }

    // 取出内部数组(堆序被破坏), 供可删除堆 O(n) 重建使用
    vector<T> release() {
        vector<T> r;
        r.swap(h_);
        return r;
    }

    // 仅供测试: 校验堆序不变式
    bool check() const {
        int n = (int)h_.size();
        for (int i = 0; i < n; ++i)
            for (int k = 1; k <= D; ++k) {
                int c = i * D + k;
                if (c >= n) break;
                if (cmp_(h_[i], h_[c])) return false;
            }
        return true;
    }

    vector<T> items() const { return h_; }        // 仅供测试

private:
    vector<T> h_;
    Cmp cmp_;

    // 把 v 放到 i 位置后向下修复; 调用前后 h_[i] 的内容视为"可覆盖的坑"
    void siftDownHole(int i, T v, int n) {
        while (true) {
            int first = i * D + 1;
            if (first >= n) break;
            int best  = first;
            int last  = std::min(first + D, n);
            for (int c = first + 1; c < last; ++c)
                if (cmp_(h_[best], h_[c])) best = c;   // 选最"优"的孩子
            if (!cmp_(v, h_[best])) break;             // v 已不劣于它, 停
            h_[i] = h_[best];
            i = best;
        }
        h_[i] = v;
    }
};

// ============================================================
// C. 原地堆排序(大根堆, 升序结果) —— 零额外内存
// ============================================================
static void siftDownRange(vector<ll>& a, int i, int n) {
    ll v = a[i];
    while (true) {
        int c = 2 * i + 1;
        if (c >= n) break;
        if (c + 1 < n && a[c + 1] > a[c]) ++c;
        if (a[c] <= v) break;
        a[i] = a[c];
        i = c;
    }
    a[i] = v;
}

static void heapSort(vector<ll>& a) {
    int n = (int)a.size();
    for (int i = n / 2 - 1; i >= 0; --i) siftDownRange(a, i, n);   // O(n) 建堆
    for (int end = n - 1; end > 0; --end) {                        // 逐个取最大值
        std::swap(a[0], a[end]);
        siftDownRange(a, 0, end);
    }
}

// ============================================================
// D. 可删除堆: 惰性删除
//    erase(v) 只登记"待删一次", 不立即在堆内查找
//    getMax() 前清掉堆顶的待删项; 待删数超过一半则 O(n) 重建
// ============================================================
class LazyDeleteHeap {
public:
    void insert(ll v) {
        h_.push(v);
        ++live_[v];
        ++liveCount_;
    }

    // 删除一个值为 v 的元素; 不存在返回 false
    bool erase(ll v) {
        auto it = live_.find(v);
        if (it == live_.end()) return false;
        if (--(it->second) == 0) live_.erase(it);
        ++pending_[v];
        ++stale_;
        --liveCount_;
        return true;
    }

    bool   empty() const { return liveCount_ == 0; }
    size_t size()  const { return (size_t)liveCount_; }

    ll getMax() {
        cleanTop();
        return h_.top();
    }

    // 仅测试: 堆内残留(含待删)元素个数
    size_t rawSize() const { return h_.size(); }

private:
    DHeap<ll, 2> h_;
    unordered_map<ll, int> live_, pending_;
    int liveCount_ = 0;
    int stale_     = 0;   // 堆内待删元素总数

    void cleanTop() {
        while (!h_.empty()) {
            ll t = h_.top();
            auto it = pending_.find(t);
            if (it == pending_.end()) break;
            if (--(it->second) == 0) pending_.erase(it);
            h_.pop();
            --stale_;
        }
        if (stale_ > 64 && stale_ * 2 > (int)h_.size()) rebuild();
    }

    // O(n): 过滤掉待删元素后整体重建, 同时回收内存
    void rebuild() {
        vector<ll> all = h_.release();
        vector<ll> keep;
        keep.reserve(all.size());
        for (ll v : all) {
            auto it = pending_.find(v);
            if (it != pending_.end() && it->second > 0) {
                if (--(it->second) == 0) pending_.erase(it);
            } else {
                keep.push_back(v);
            }
        }
        pending_.clear();
        stale_ = 0;
        h_.build(std::move(keep));
    }
};

// ============================================================
// E. 对顶堆动态中位数
//    lo_: 较小的一半, 大根堆   hi_: 较大的一半, 小根堆
//    不变式: lo_.size() == hi_.size() 或 lo_.size() == hi_.size()+1
// ============================================================
class DualHeap {
public:
    void add(ll v) {
        if (lo_.empty() || v <= lo_.top()) lo_.push(v);
        else                               hi_.push(v);
        while ((int)lo_.size() > (int)hi_.size() + 1) { hi_.push(lo_.top()); lo_.pop(); }
        while ((int)lo_.size() < (int)hi_.size())     { lo_.push(hi_.top()); hi_.pop(); }
    }

    // 返回 2×中位数, 整数精确(避免浮点比较误差)
    ll median2x() const {
        if (lo_.size() > hi_.size()) return 2 * lo_.top();
        return lo_.top() + hi_.top();
    }

private:
    priority_queue<ll> lo_;
    priority_queue<ll, vector<ll>, greater<ll>> hi_;
};

// ============================================================
// 计时
// ============================================================
template <class F>
static double benchMs(F f) {
    auto t0 = chrono::steady_clock::now();
    f();
    auto t1 = chrono::steady_clock::now();
    return chrono::duration<double, milli>(t1 - t0).count();
}

// ============================================================
// 测试 A: 堆 vs multiset 暴力(含堆序校验)
// ============================================================
template <int D>
static void testHeapVsMultiset(int rounds, uint64_t seed, const char* name) {
    mt19937_64 rng(seed);
    DHeap<ll, D> hp;
    multiset<ll> ref;
    int before = g_fail;

    for (int step = 0; step < rounds; ++step) {
        int op = (int)(rng() % 100);
        if (op < 60 || ref.empty()) {
            ll v = (ll)(rng() % 2001) - 1000;
            hp.push(v);
            ref.insert(v);
        } else {
            CHECK(hp.top() == *ref.rbegin(), "top mismatch step=%d", step);
            hp.pop();
            ref.erase(prev(ref.end()));
        }
        if (!ref.empty()) {
            CHECK(hp.top() == *ref.rbegin(), "top mismatch step=%d", step);
            CHECK(hp.size() == ref.size(), "size mismatch step=%d", step);
        } else {
            CHECK(hp.empty(), "should be empty step=%d", step);
        }
        if (step % 53 == 0 && !hp.empty()) CHECK(hp.check(), "heap order broken step=%d", step);
    }
    printf("  [%s] 堆 vs multiset: %s (%d 次操作, 终态 size=%zu)\n",
           name, g_fail == before ? "PASS" : "FAIL", rounds, hp.size());
}

// 小根堆(自定义比较器) —— 验证模板泛化
static void testMinHeap(int rounds, uint64_t seed) {
    mt19937_64 rng(seed);
    DHeap<ll, 2, std::greater<ll>> hp;
    multiset<ll> ref;
    int before = g_fail;

    for (int step = 0; step < rounds; ++step) {
        int op = (int)(rng() % 100);
        if (op < 60 || ref.empty()) {
            ll v = (ll)(rng() % 2001) - 1000;
            hp.push(v);
            ref.insert(v);
        } else {
            CHECK(hp.top() == *ref.begin(), "min-top mismatch step=%d", step);
            hp.pop();
            ref.erase(ref.begin());
        }
        if (!ref.empty()) CHECK(hp.top() == *ref.begin(), "min-top mismatch step=%d", step);
        if (step % 53 == 0 && !hp.empty()) CHECK(hp.check(), "min-heap order broken step=%d", step);
    }
    printf("  [D=2 min] 小根堆 vs multiset: %s (%d 次操作)\n",
           g_fail == before ? "PASS" : "FAIL", rounds);
}

// ============================================================
// 测试 B: Floyd O(n) 建堆 == 逐个 push 建堆, 且 pop 序列降序
// ============================================================
static void testBuild(int trials, uint64_t seed) {
    mt19937_64 rng(seed);
    int before = g_fail;

    for (int t = 0; t < trials; ++t) {
        int n = (int)(rng() % 200);
        vector<ll> a(n);
        for (auto& x : a) x = (ll)(rng() % 1001) - 500;

        DHeap<ll, 2> hf;
        vector<ll> c = a;
        hf.build(std::move(c));                 // Floyd

        DHeap<ll, 2> hp;
        for (ll x : a) hp.push(x);              // 逐个插入

        CHECK(hf.size() == hp.size(), "build size mismatch n=%d", n);
        if (n > 0) CHECK(hf.top() == hp.top(), "build top mismatch n=%d", n);
        CHECK(hf.check(), "Floyd heap order broken n=%d", n);
        CHECK(hp.check(), "push heap order broken n=%d", n);

        vector<ll> x1 = hf.items(), x2 = hp.items();
        sort(x1.begin(), x1.end());
        sort(x2.begin(), x2.end());
        CHECK(x1 == x2, "build multiset mismatch n=%d", n);

        // 连续 pop 必须得到非递增序列, 且元素多重集合一致
        ll last = LLONG_MAX;
        for (int i = 0; i < n; ++i) {
            CHECK(hf.top() <= last, "pop order broken n=%d i=%d", n, i);
            last = hf.top();
            hf.pop();
            if (!hf.empty()) CHECK(hf.check(), "heap order broken after pop n=%d", n);
        }
        CHECK(hf.empty(), "not empty after n pops n=%d", n);
    }
    printf("  [build] Floyd vs 逐个push (含 pop 降序): %s (%d 组)\n",
           g_fail == before ? "PASS" : "FAIL", trials);
}

// ============================================================
// 测试 C: heapSort vs std::sort, 覆盖升序/降序/全等/极值/空/单元素
// ============================================================
static void testHeapSort(int trials, uint64_t seed) {
    mt19937_64 rng(seed);
    int before = g_fail;

    auto oneCase = [&](vector<ll> a, const char* tag, int t) {
        vector<ll> b = a;
        heapSort(a);
        sort(b.begin(), b.end());
        CHECK(a == b, "heapSort mismatch tag=%s trial=%d n=%zu", tag, t, a.size());
    };

    oneCase({}, "empty", -1);
    oneCase({42}, "single", -1);
    oneCase({3, 3, 3, 3, 3}, "all-equal", -1);
    oneCase({-5, -1, -100, 0, 7, -100}, "negatives", -1);

    for (int t = 0; t < trials; ++t) {
        int n = (int)(rng() % 120);
        vector<ll> a(n);
        for (auto& x : a) x = (ll)(rng() % 41) - 20;   // 小值域, 大量重复
        oneCase(a, "random-dup", t);

        sort(a.begin(), a.end());
        oneCase(a, "ascending", t);
        reverse(a.begin(), a.end());
        oneCase(a, "descending", t);
    }
    printf("  [heapSort] vs std::sort: %s (%d 组 + 4 边界)\n",
           g_fail == before ? "PASS" : "FAIL", trials * 3);
}

// ============================================================
// 测试 D: 可删除堆 vs multiset
// ============================================================
static void testLazyDelete(int rounds, uint64_t seed) {
    mt19937_64 rng(seed);
    LazyDeleteHeap hp;
    multiset<ll> ref;
    int before = g_fail;

    for (int step = 0; step < rounds; ++step) {
        int op = (int)(rng() % 100);
        if (op < 55 || ref.empty()) {
            ll v = (ll)(rng() % 201) - 100;      // 小值域 → 大量重复键
            hp.insert(v);
            ref.insert(v);
        } else if (op < 85) {
            ll v = (ll)(rng() % 201) - 100;
            auto it = ref.find(v);
            bool ok = hp.erase(v);
            CHECK(ok == (it != ref.end()), "erase return mismatch step=%d", step);
            if (it != ref.end()) ref.erase(it);
        } else {
            if (!ref.empty()) {
                CHECK(hp.getMax() == *ref.rbegin(), "getMax mismatch step=%d", step);
            }
        }
        CHECK(hp.size() == ref.size(), "size mismatch step=%d", step);
        if (!ref.empty()) {
            CHECK(hp.getMax() == *ref.rbegin(), "getMax mismatch step=%d", step);
        } else {
            CHECK(hp.empty(), "should be empty step=%d", step);
        }
        // 惰性删除的内存上界: 待删数 > 有效数才重建 → 残留 <= 2×有效 + 64
        if (step % 101 == 0)
            CHECK(hp.rawSize() <= 2 * hp.size() + 130,
                  "raw heap bloated step=%d raw=%zu live=%zu", step, hp.rawSize(), hp.size());
    }
    printf("  [lazy-delete] 可删除堆 vs multiset: %s (%d 次操作, 终态 size=%zu)\n",
           g_fail == before ? "PASS" : "FAIL", rounds, hp.size());
}

// ============================================================
// 测试 E: 对顶堆中位数 vs 排序暴力
// ============================================================
static void testMedian(int rounds, uint64_t seed) {
    mt19937_64 rng(seed);
    DualHeap dh;
    vector<ll> ref;
    int before = g_fail;

    for (int i = 0; i < rounds; ++i) {
        ll v = (ll)(rng() % 401) - 200;
        dh.add(v);
        ref.push_back(v);
        if (i % 7 == 0 || i < 4) {
            sort(ref.begin(), ref.end());
            int n = (int)ref.size();
            ll want = (n % 2) ? 2 * ref[n / 2] : ref[n / 2 - 1] + ref[n / 2];
            CHECK(dh.median2x() == want, "median mismatch i=%d n=%d", i, n);
        }
    }
    printf("  [dual-heap] 动态中位数 vs 排序: %s (%d 次插入)\n",
           g_fail == before ? "PASS" : "FAIL", rounds);
}

// ============================================================
// 基准测试
// ============================================================
static void benchAll() {
    const int N = 1 << 21;   // 2,097,152
    vector<ll> data(N);
    mt19937_64 rng(20261025ULL);
    for (auto& x : data) x = (ll)(rng() % (1ULL << 40));

    printf("\n--- 基准 (N = %d, 随机 40 位整数) ---\n", N);
    volatile ll sink = 0;

    // 1) 建堆: Floyd O(n) vs 逐个 push O(n log n)
    DHeap<ll, 2> hFloyd, hPush;
    double tFloyd = benchMs([&] { vector<ll> c = data; hFloyd.build(std::move(c)); });
    double tPush  = benchMs([&] { for (ll x : data) hPush.push(x); });
    printf("  建堆  Floyd O(n)          : %8.2f ms   top=%lld\n", tFloyd, hFloyd.top());
    printf("  建堆  逐个 push O(nlg n)  : %8.2f ms   top=%lld   加速 %.2fx\n",
           tPush, hPush.top(), tPush / tFloyd);
    CHECK(hFloyd.top() == hPush.top(), "bench build top mismatch");

    // 2) D=2 vs D=4: 建堆 + N 次混合 push/pop
    auto mixed = [&](auto& hp) {
        vector<ll> c = data;
        hp.build(std::move(c));
        for (int i = 0; i < N; ++i) {
            hp.push(data[(size_t)i] + 1);
            sink = sink + hp.top();
            hp.pop();
        }
    };
    DHeap<ll, 2> h2; DHeap<ll, 4> h4;
    double t2 = benchMs([&] { mixed(h2); });
    double t4 = benchMs([&] { mixed(h4); });
    printf("  混合 push/pop  D=2        : %8.2f ms\n", t2);
    printf("  混合 push/pop  D=4        : %8.2f ms   (D=4 相对 %.2fx)\n", t4, t2 / t4);
    CHECK(h2.size() == h4.size(), "bench D2/D4 size mismatch");
    CHECK(h2.check() && h4.check(), "bench D2/D4 heap order broken");

    // 3) 堆排序 vs std::sort
    vector<ll> s1 = data, s2 = data;
    double th = benchMs([&] { heapSort(s1); });
    double ts = benchMs([&] { std::sort(s2.begin(), s2.end()); });
    printf("  堆排序 heapSort           : %8.2f ms\n", th);
    printf("  std::sort (introsort)     : %8.2f ms   (std::sort 快 %.2fx)\n", ts, th / ts);
    CHECK(s1 == s2, "heapsort result != std::sort");
    sink = sink + s1[0];
    (void)sink;
}

// ============================================================
int main() {
    printf("=== 0006 二叉堆 / 优先队列 ===\n");
    testHeapVsMultiset<2>(200000, 1001, "D=2");
    testHeapVsMultiset<4>(200000, 1002, "D=4");
    testMinHeap(100000, 1003);
    testBuild(400, 1004);
    testHeapSort(120, 1005);
    testLazyDelete(300000, 1006);
    testMedian(6000, 1007);
    benchAll();

    printf("\n=== 结果: %s (失败断言 %d 条) ===\n", g_fail == 0 ? "ALL PASS" : "FAILED", g_fail);
    return g_fail == 0 ? 0 : 1;
}
