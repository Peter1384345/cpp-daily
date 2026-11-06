// ============================================================
// 0009 · Splay(伸展树) / 文艺平衡树
// ------------------------------------------------------------
// 三个实现 + 一组实证:
//   A. SplayTree<true>   双旋 splay 集合: zig / zig-zig / zig-zag,
//                        splay(x, goal) 可把 x 提到任意目标节点之下(不只根)
//   B. SplayTree<false>  单旋对照: 只用 zig 一路上提 —— 正确, 但均摊界从
//                        O(log n) 退化为 O(n); 同一个模板只差一个 bool
//   C. SplaySeq          文艺平衡树: 双哨兵 + 隐式键 + rev/add 双 lazy + 区间 sum/min
//   D. 实证              顺序插入 1..M 后的树高; 反复访问最小值时的累计旋转次数
// 正确性: G1/G2 与有序向量逐操作对拍, G3 与 vector 对拍区间操作,
//         G4 边界专项, G5 单旋/双旋退化对照(带不变式断言)
// 性能:   N=2e5 集合三方(splay / zig-only / std::set); 序列 3e5 建树 + 4 类区间操作
// 编译:   g++ -O2 -std=c++17 -Wall -Wextra 0009_splay.cpp -o 0009
// 注意:   本期源码未在本机编译(环境无 C++ 编译器); 算法逻辑经 Python 逐行镜像
//         (.verify_mirror_0009.py) 随机对拍验证, 详见 0009_splay.md
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
// 确定性伪随机(xorshift64): 固定种子, 结果可复现
// ============================================================
static uint64_t g_seed = 0x9E3779B97F4A7C15ULL;
static inline uint64_t xr64() {
    g_seed ^= g_seed << 13;
    g_seed ^= g_seed >> 7;
    g_seed ^= g_seed << 17;
    return g_seed;
}
// 注意: 这里没有 xr32() —— Splay 不需要随机优先级, 它的平衡来自"访问即提根"
// (对照 0008 的 Treap: 那边的 pri 字段是期望 O(log n) 的唯一来源)

// ============================================================
// A/B. SplayTree<DoubleRot> — 伸展树(集合语义)
//
// 与 Treap/红黑树最本质的差别: 它**没有平衡条件**。
// 唯一规则是"访问谁, 就把谁转到根"。平衡性是这个动作的副产品,
// 且只在均摊意义上成立 —— 单次操作可以是 O(n)。
//
// splay(x, goal) 是本类的唯一原语: 把 x 旋转到 goal 的孩子位置
// (goal == 0 表示转到根)。三种情形的区分就是全部:
//   zig     : 父就是目标      → 旋一次
//   zig-zig : x 与父同向      → 先旋父, 再旋 x(必须这个顺序)
//   zig-zag : x 与父异向      → 先旋 x, 再旋 x
// 单旋版(DoubleRot=false)把前两种都退化成 zig, 正确性不变, 均摊界崩塌。
// ============================================================
template <bool DoubleRot>
class SplayTree {
public:
    static constexpr int NOKEY = INT_MIN;

    explicit SplayTree(size_t reserve_n = 1024) {
        t.reserve(reserve_n + 1);
        t.push_back(Node{});  // 0 号为 NIL: sz = 0
    }

    int size() const { return t[root_].sz; }
    int root() const { return root_; }
    unsigned long long spins() const { return spins_; }

    // true = 新插入; false = 键已存在(已提到根, 属自适应的一部分)
    bool insert(int key) {
        if (!root_) {
            root_ = alloc(key);
            return true;
        }
        int x = root_;
        while (true) {
            if (key == t[x].key) {
                splay(x, 0);
                return false;
            }
            bool goLeft = (key < t[x].key);
            int nx = goLeft ? t[x].l : t[x].r;
            if (!nx) {
                int nd = alloc(key);  // 先取完 x 的信息再 alloc, 防 vector 重分配后引用悬空
                t[nd].fa = x;
                if (goLeft) t[x].l = nd; else t[x].r = nd;
                // x 的 sz 不必在此修正: splay 的第一次 rot 会 pull(y = x)
                splay(nd, 0);
                return true;
            }
            x = nx;
        }
    }

    // 删除: 先提到根, 再用"左子树最大值"接右子树
    bool erase(int key) {
        if (!root_) return false;
        int x = root_;
        while (x && t[x].key != key) x = (key < t[x].key) ? t[x].l : t[x].r;
        if (!x) return false;
        splay(x, 0);
        int L = t[x].l, R = t[x].r;
        if (!L) {  // 无左子树: 右子树直接上位
            root_ = R;
            if (R) t[R].fa = 0;
        } else {
            t[L].fa = 0;  // 断开, 让 splay(m, 0) 能停在 L 处
            int m = L;
            while (t[m].r) m = t[m].r;
            splay(m, 0);  // m 成为根, 且 m 必无右孩子(L 中最大)
            t[m].r = R;
            if (R) t[R].fa = m;
            pull(m);
        }
        t[x] = Node{};
        free_.push_back(x);
        return true;
    }

    // 找到就提到根 —— splay 的核心用法: 让"刚访问过的"变便宜
    bool access(int key) {
        int x = root_;
        while (x && t[x].key != key) x = (key < t[x].key) ? t[x].l : t[x].r;
        if (!x) return false;
        splay(x, 0);
        return true;
    }

    bool contains(int key) const {
        int x = root_;
        while (x) {
            if (key < t[x].key) x = t[x].l;
            else if (key > t[x].key) x = t[x].r;
            else return true;
        }
        return false;
    }

    // 严格小于 key 的个数 = key 的 0-based 排名(纯下行, 不提根)
    int count_lt(int key) const {
        int x = root_, res = 0;
        while (x) {
            if (t[x].key < key) { res += t[t[x].l].sz + 1; x = t[x].r; }
            else x = t[x].l;
        }
        return res;
    }

    int count_le(int key) const {
        int x = root_, res = 0;
        while (x) {
            if (t[x].key <= key) { res += t[t[x].l].sz + 1; x = t[x].r; }
            else x = t[x].l;
        }
        return res;
    }

    int kth(int k) const {  // 0-based, 越界返回 NOKEY
        if (k < 0 || k >= t[root_].sz) return NOKEY;
        int x = root_;
        while (x) {
            int ls = t[t[x].l].sz;
            if (k < ls) x = t[x].l;
            else if (k == ls) return t[x].key;
            else { k -= ls + 1; x = t[x].r; }
        }
        return NOKEY;
    }

    bool prev_lt(int key, int &out) const {
        int c = count_lt(key);
        if (c == 0) return false;
        out = kth(c - 1);
        return true;
    }
    bool next_gt(int key, int &out) const {
        int c = count_le(key);
        if (c >= t[root_].sz) return false;
        out = kth(c);
        return true;
    }

    vector<int> to_vector() const {
        vector<int> out;
        out.reserve((size_t)t[root_].sz);
        vector<int> st;
        int cur = root_;
        while (cur || !st.empty()) {
            while (cur) { st.push_back(cur); cur = t[cur].l; }
            cur = st.back();
            st.pop_back();
            out.push_back(t[cur].key);
            cur = t[cur].r;
        }
        return out;
    }

    // 迭代求树高: splay 树的瞬时高度可达 O(n), 递归会爆栈
    int height() const {
        if (!root_) return 0;
        int best = 0;
        vector<pair<int, int>> st;
        st.push_back({root_, 1});
        while (!st.empty()) {
            int x = st.back().first, d = st.back().second;
            st.pop_back();
            if (d > best) best = d;
            if (t[x].l) st.push_back({t[x].l, d + 1});
            if (t[x].r) st.push_back({t[x].r, d + 1});
        }
        return best;
    }

    // 结构自检(迭代): 中序严格递增 + 父子指针互指 + sz 自洽
    bool check() const {
        vector<int> st;
        int cur = root_, cnt = 0, prevKey = 0;
        bool has = false;
        while (cur || !st.empty()) {
            while (cur) { st.push_back(cur); cur = t[cur].l; }
            cur = st.back();
            st.pop_back();
            if (has && !(prevKey < t[cur].key)) return false;
            prevKey = t[cur].key;
            has = true;
            if (t[cur].fa) {
                if (t[t[cur].fa].l != cur && t[t[cur].fa].r != cur) return false;
            }
            if (t[cur].sz != t[t[cur].l].sz + t[t[cur].r].sz + 1) return false;
            ++cnt;
            cur = t[cur].r;
        }
        return cnt == t[root_].sz;
    }

private:
    struct Node {
        int l = 0, r = 0, fa = 0, key = 0, sz = 0;
    };
    vector<Node> t;
    vector<int> free_;
    int root_ = 0;
    unsigned long long spins_ = 0;  // 旋转计数, 仅用于诊断

    int alloc(int key) {
        int id;
        if (!free_.empty()) {
            id = free_.back();
            free_.pop_back();
            t[(size_t)id] = Node{0, 0, 0, key, 1};
        } else {
            id = (int)t.size();
            t.push_back(Node{0, 0, 0, key, 1});
        }
        return id;
    }

    bool is_right(int x) const { return t[t[x].fa].r == x; }  // fa==0 时 t[0].r==0 != x

    void pull(int x) {
        if (x) t[x].sz = t[t[x].l].sz + t[t[x].r].sz + 1;
    }

    // 单旋: x 上升一层。不 push/pull 之外做任何事 —— SplayTree 没有 lazy
    void rot(int x) {
        ++spins_;
        int y = t[x].fa, z = t[y].fa;
        if (t[y].l == x) {
            t[y].l = t[x].r;
            if (t[x].r) t[t[x].r].fa = y;
            t[x].r = y;
        } else {
            t[y].r = t[x].l;
            if (t[x].l) t[t[x].l].fa = y;
            t[x].l = y;
        }
        t[y].fa = x;
        t[x].fa = z;
        if (z) {
            if (t[z].l == y) t[z].l = x;
            else t[z].r = x;
        }
        pull(y);
        pull(x);
    }

    void splay(int x, int goal = 0) {
        while (t[x].fa != goal) {
            int y = t[x].fa, z = t[y].fa;
            if (z != goal) {
                // 双旋: 同向先旋父(zig-zig), 异向先旋 x(zig-zag)
                if (DoubleRot && is_right(x) == is_right(y)) rot(y);
                else rot(x);
            }
            rot(x);
        }
        if (!goal) root_ = x;
    }
};

using SplaySet = SplayTree<true>;
using ZigOnlySet = SplayTree<false>;

// ============================================================
// C. SplaySeq — 文艺平衡树(隐式键序列)
//
// 树的位置即下标, 中序遍历就是序列。为了让"区间"总能写成
// "某节点的左子树", 首尾各放一个哨兵:
//
//   树中位置  1        2 .. n+1        n+2
//   内容     -INF      a[1..n]         +INF
//   用户下标           1 .. n
//
// 于是区间 [l, r] == splay(kth(l)) 后 splay(kth(r+2), 根) 得到的
// "根的右孩子的左子树"。两次 splay 就把任意区间"夹"成一个子树,
// 这是 splay 做区间问题的全部秘密。
//
// 双 lazy 的纪律(见讲义第五节): pull(x) 之前必须保证 t[x].add == 0,
// 否则 pull 会把 apply_add 加到 x.sum 上的 d*sz 覆盖掉。
// 本实现靠 "splay 前把 x 到根的整条路径 push 一遍" 来保证这一点。
// ============================================================
class SplaySeq {
public:
    static constexpr long long INFV = (long long)1e15;
    static constexpr long long BIGV = LLONG_MAX / 2;

    explicit SplaySeq(size_t reserve_n = 1024) {
        t.reserve(reserve_n + 3);
        build(vector<int>());
    }

    explicit SplaySeq(const vector<int> &a) {
        t.reserve(a.size() + 3);
        build(a);
    }

    int size() const { return n_; }
    int heightHint() const { return heightOf(root_); }

    // O(n) 建树: 取中点递归, 直接得到平衡树。
    // 逐个 insert 是 O(n log n) 且带 n 次旋转常数, 建树阶段不必付这个代价。
    void build(const vector<int> &a) {
        t.clear();
        free_.clear();
        path_.clear();
        n_ = (int)a.size();
        neg_ = pos_ = 0;
        t.push_back(Node{0, 0, 0, 0, 0, BIGV, 0, 0, false});  // NIL: mn = +BIG
        root_ = buildRec(1, n_ + 2, 0, a);
    }

    bool at(int pos, long long &out) {  // pos ∈ [1, n]
        if (pos < 1 || pos > n_) return false;
        int x = kth(pos + 1);
        if (!x) return false;
        out = t[x].val;
        return true;
    }

    // 在第 pos 个元素之前插入(pos ∈ [1, n+1])
    bool insertAt(int pos, long long v) {
        if (pos < 1 || pos > n_ + 1) return false;
        int a = kth(pos);
        splay(a, 0);
        int b = kth(pos + 1);
        splay(b, a);
        int nd = alloc(v);
        t[b].l = nd;
        t[nd].fa = b;
        pull(b);
        pull(a);
        ++n_;
        return true;
    }

    bool eraseAt(int pos) {  // pos ∈ [1, n]
        if (pos < 1 || pos > n_) return false;
        int a = kth(pos);
        splay(a, 0);
        int b = kth(pos + 2);
        splay(b, a);
        int m = t[b].l;
        if (!m) return false;  // 不可达
        t[b].l = 0;
        t[m].fa = 0;
        pull(b);
        pull(a);
        t[m] = Node{};
        free_.push_back(m);
        --n_;
        return true;
    }

    // 区间翻转: 只打标记, O(1)。rev 不改变 sum/min/sz, 所以**不需要** pull 祖先
    bool rangeRev(int l, int r) {
        if (l < 1 || r > n_ || l > r) return false;
        int m = extract(l, r);
        applyRev(m);
        return true;
    }

    // 区间加: 必须 pull 回去(祖先的 sum/min 变了), 与 rev 形成不对称
    bool rangeAdd(int l, int r, long long d) {
        if (l < 1 || r > n_ || l > r) return false;
        int a = kth(l);
        splay(a, 0);
        int b = kth(r + 2);
        splay(b, a);
        int m = t[b].l;
        applyAdd(m, d);
        pull(b);
        pull(a);
        return true;
    }

    bool rangeSum(int l, int r, long long &out) {
        if (l < 1 || r > n_ || l > r) return false;
        int m = extract(l, r);
        out = t[m].sum;
        return true;
    }

    bool rangeMin(int l, int r, long long &out) {
        if (l < 1 || r > n_ || l > r) return false;
        int m = extract(l, r);
        out = t[m].mn;
        return true;
    }

    vector<long long> toVector() {
        vector<long long> out;
        out.reserve((size_t)n_);
        vector<pair<int, int>> st;  // (节点, 0=待展开左子树)
        if (root_) st.push_back({root_, 0});
        while (!st.empty()) {
            int x = st.back().first, state = st.back().second;
            st.pop_back();
            push(x);  // 展开前必须落实 rev, 否则左右顺序是反的
            if (state == 0) {
                st.push_back({x, 1});
                if (t[x].l) st.push_back({t[x].l, 0});
            } else {
                if (x != neg_ && x != pos_) out.push_back(t[x].val);  // 跳过哨兵
                if (t[x].r) st.push_back({t[x].r, 0});
            }
        }
        return out;
    }

    // 自检: 父子互指 + sz 自洽 + sum/mn 与 add 的自洽关系
    //   sum(x) == sum(l)+sum(r)+val(x) + add(x)*(sz(x)-1)
    //   mn(x)  == min(val(x), mn(l)+add(x), mn(r)+add(x))
    // 这两式由 applyAdd 的定义直接推出, 不必先 flatten(flatten 会真正翻转序列)
    bool check() const {
        int cnt = 0;
        return walk(root_, 0, cnt) && cnt == n_ + 2;
    }

private:
    struct Node {
        int l = 0, r = 0, fa = 0;
        long long val = 0, sum = 0, mn = 0, add = 0;
        int sz = 0;
        bool rev = false;
    };
    vector<Node> t;
    vector<int> free_;
    vector<int> path_;
    int root_ = 0;
    int n_ = 0;
    int neg_ = 0, pos_ = 0;  // 两个哨兵的节点下标

    int heightOf(int x) const {
        if (!x) return 0;
        return 1 + max(heightOf(t[x].l), heightOf(t[x].r));
    }

    int alloc(long long v) {
        int id;
        if (!free_.empty()) {
            id = free_.back();
            free_.pop_back();
            t[(size_t)id] = Node{0, 0, 0, v, v, v, 0, 1, false};
        } else {
            id = (int)t.size();
            t.push_back(Node{0, 0, 0, v, v, v, 0, 1, false});
        }
        return id;
    }

    int buildRec(int lo, int hi, int fa, const vector<int> &a) {
        if (lo > hi) return 0;
        int mid = lo + ((hi - lo) >> 1);
        long long v;
        if (mid == 1) v = -INFV;
        else if (mid == n_ + 2) v = INFV;
        else v = (long long)a[(size_t)(mid - 2)];
        int x = (int)t.size();
        t.push_back(Node{0, 0, fa, v, v, v, 0, 1, false});  // add = 0, 可直接 pull
        // 哨兵必须按"节点身份"记住, 不能靠下标或位置判断 —— 下标是分配顺序, 与中序位置无关
        if (mid == 1) neg_ = x;
        else if (mid == n_ + 2) pos_ = x;
        int l = buildRec(lo, mid - 1, x, a);
        int r = buildRec(mid + 1, hi, x, a);
        t[x].l = l;
        t[x].r = r;
        pull(x);
        return x;
    }

    // 前提: t[x].add == 0(否则 applyAdd 加到 sum 上的 d*sz 会被覆盖)
    void pull(int x) {
        if (!x) return;
        t[x].sz = t[t[x].l].sz + t[t[x].r].sz + 1;
        t[x].sum = t[t[x].l].sum + t[t[x].r].sum + t[x].val;
        t[x].mn = min(t[x].val, min(t[t[x].l].mn, t[t[x].r].mn));
    }

    void applyRev(int x) {
        if (!x) return;
        swap(t[x].l, t[x].r);
        t[x].rev ^= 1;
    }

    void applyAdd(int x, long long d) {
        if (!x || d == 0) return;
        t[x].val += d;
        t[x].sum += d * (long long)t[x].sz;
        t[x].mn += d;
        t[x].add += d;
    }

    void push(int x) {
        if (!x) return;
        if (t[x].rev) {
            applyRev(t[x].l);
            applyRev(t[x].r);
            t[x].rev = false;
        }
        if (t[x].add) {
            long long d = t[x].add;
            applyAdd(t[x].l, d);
            applyAdd(t[x].r, d);
            t[x].add = 0;
        }
    }

    bool isRight(int x) const { return t[t[x].fa].r == x; }

    void rot(int x) {
        int y = t[x].fa, z = t[y].fa;
        if (t[y].l == x) {
            t[y].l = t[x].r;
            if (t[x].r) t[t[x].r].fa = y;
            t[x].r = y;
        } else {
            t[y].r = t[x].l;
            if (t[x].l) t[t[x].l].fa = y;
            t[x].l = y;
        }
        t[y].fa = x;
        t[x].fa = z;
        if (z) {
            if (t[z].l == y) t[z].l = x;
            else t[z].r = x;
        }
        pull(y);  // y、x 都在刚 push 过的路径上, add 必为 0
        pull(x);
    }

    // 关键: 先把 x→根 整条路径自顶向下 push, 再旋转。
    // 否则旋转中的 pull 会作用在带 add 标记的节点上, 聚合量被静默破坏。
    void splay(int x, int goal = 0) {
        path_.clear();
        for (int y = x; y; y = t[y].fa) path_.push_back(y);
        for (int i = (int)path_.size() - 1; i >= 0; --i) push(path_[(size_t)i]);
        while (t[x].fa != goal) {
            int y = t[x].fa, z = t[y].fa;
            if (z != goal) {
                if (isRight(x) == isRight(y)) rot(y);
                else rot(x);
            }
            rot(x);
        }
        if (!goal) root_ = x;
    }

    int kth(int k) {  // 1-based 树中位置, 返回节点下标
        int x = root_;
        while (x) {
            push(x);  // 下行必须先落实标记, 否则 ls 是翻转前的值
            int ls = t[t[x].l].sz;
            if (k <= ls) x = t[x].l;
            else if (k == ls + 1) return x;
            else { k -= ls + 1; x = t[x].r; }
        }
        return 0;
    }

    // 区间 [l, r](1-based) 对应的子树根
    int extract(int l, int r) {
        int a = kth(l);       // 位置 l: 元素 l-1(或 -INF 哨兵)
        splay(a, 0);
        int b = kth(r + 2);   // 位置 r+2: 元素 r+1(或 +INF 哨兵)
        splay(b, a);
        return t[b].l;        // 位置 [l+1, r+1] == 元素 [l, r]
    }

    bool walk(int x, int fa, int &cnt) const {
        if (!x) return true;
        if (t[x].fa != fa) return false;
        if (t[x].sz != t[t[x].l].sz + t[t[x].r].sz + 1) return false;
        long long base = t[t[x].l].sum + t[t[x].r].sum + t[x].val;
        if (t[x].sum != base + t[x].add * (long long)(t[x].sz - 1)) return false;
        long long m = min(t[x].val, min(t[t[x].l].mn + t[x].add, t[t[x].r].mn + t[x].add));
        if (t[x].mn != m) return false;
        ++cnt;
        return walk(t[x].l, x, cnt) && walk(t[x].r, x, cnt);
    }
};

// ============================================================
// 验证工具: 有序向量作为 oracle(dedup 集合语义)
// ============================================================
struct SortedOracle {
    vector<int> v;

    bool insert(int key) {
        auto it = lower_bound(v.begin(), v.end(), key);
        if (it != v.end() && *it == key) return false;
        v.insert(it, key);
        return true;
    }
    bool erase(int key) {
        auto it = lower_bound(v.begin(), v.end(), key);
        if (it == v.end() || *it != key) return false;
        v.erase(it);
        return true;
    }
    bool contains(int key) const {
        auto it = lower_bound(v.begin(), v.end(), key);
        return it != v.end() && *it == key;
    }
    int count_lt(int key) const { return (int)(lower_bound(v.begin(), v.end(), key) - v.begin()); }
    int count_le(int key) const { return (int)(upper_bound(v.begin(), v.end(), key) - v.begin()); }
    bool prev_lt(int key, int &out) const {
        auto it = lower_bound(v.begin(), v.end(), key);
        if (it == v.begin()) return false;
        out = *(--it);
        return true;
    }
    bool next_gt(int key, int &out) const {
        auto it = upper_bound(v.begin(), v.end(), key);
        if (it == v.end()) return false;
        out = *it;
        return true;
    }
    static constexpr int NOKEY = INT_MIN;
    int kth(int k) const {
        if (k < 0 || k >= (int)v.size()) return NOKEY;
        return v[(size_t)k];
    }
};

// 接口清单(与 0008 的教训对应): 任何集合实现都必须实现下面 8 个方法,
// 否则模板实例化失败 —— 没有编译器时, 这类错误只能靠镜像先跑出来。
template <class SetT>
static void run_set_ops(SetT &s, SortedOracle &o, int ops, uint32_t keymod, const char *name) {
    int mismatch = 0;
    for (int i = 0; i < ops; ++i) {
        uint64_t r = xr64();
        int op = (int)(r % 100);
        int key = (int)((r >> 8) % keymod);
        if (op < 40) {
            bool a = s.insert(key), b = o.insert(key);
            if (a != b) { ++mismatch; CHECK(false, "%s insert(%d) ret %d vs %d", name, key, (int)a, (int)b); }
        } else if (op < 58) {
            bool a = s.erase(key), b = o.erase(key);
            if (a != b) { ++mismatch; CHECK(false, "%s erase(%d) ret %d vs %d", name, key, (int)a, (int)b); }
        } else if (op < 70) {
            bool a = s.contains(key), b = o.contains(key);
            if (a != b) { ++mismatch; CHECK(false, "%s contains(%d) %d vs %d", name, key, (int)a, (int)b); }
        } else if (op < 82) {
            int a = s.count_lt(key), b = o.count_lt(key);
            if (a != b) { ++mismatch; CHECK(false, "%s count_lt(%d) %d vs %d", name, key, a, b); }
        } else if (op < 90) {
            int k = (int)((r >> 20) % (uint32_t)(o.v.size() + 2));  // 刻意越界
            int a = s.kth(k), b = o.kth(k);
            if (a != b) { ++mismatch; CHECK(false, "%s kth(%d) %d vs %d", name, k, a, b); }
        } else if (op < 95) {
            int pa = 0, pb = 0;
            bool fa = s.prev_lt(key, pa), fb = o.prev_lt(key, pb);
            if (fa != fb || (fa && pa != pb)) { ++mismatch; CHECK(false, "%s prev_lt(%d) %d/%d vs %d/%d", name, key, (int)fa, pa, (int)fb, pb); }
        } else {
            int na = 0, nb = 0;
            bool ga = s.next_gt(key, na), gb = o.next_gt(key, nb);
            if (ga != gb || (ga && na != nb)) { ++mismatch; CHECK(false, "%s next_gt(%d) %d/%d vs %d/%d", name, key, (int)ga, na, (int)gb, nb); }
        }
        if (mismatch > 3) { printf("    [STOP] %s 连续失配, 终止该组\n", name); break; }
    }
    vector<int> got = s.to_vector();
    if (got != o.v) {
        ++g_fail;
        printf("    [FAIL] %s 中序与 oracle 不一致: got %zu, want %zu\n", name, got.size(), o.v.size());
        size_t lim = min(got.size(), o.v.size());
        for (size_t i = 0; i < lim; ++i)
            if (got[i] != o.v[i]) { printf("    first diff @%zu: %d vs %d\n", i, got[i], o.v[i]); break; }
    }
    if (s.size() != (int)o.v.size()) {
        ++g_fail;
        printf("    [FAIL] %s size %d vs %zu\n", name, s.size(), o.v.size());
    }
}

// ============================================================
// 基准辅助
// 两个被测实现的查询序列必须完全一致, 才能比较校验和:
// 第 k 小的下标由 i 的确定性哈希给出, 不消耗全局随机流
// ============================================================
static inline int kth_index(int i, int N) {
    return (int)((uint32_t)i * 2654435761u % (uint32_t)N);
}

template <class SetT>
static unsigned long long query_stage(SetT &s, const vector<int> &keys, int N) {
    unsigned long long cs = 0;
    if constexpr (is_same_v<SetT, std::set<int>>) {
        for (int i = 0; i < N; ++i) cs += (unsigned long long)s.count(keys[(size_t)i]);
    } else {
        for (int i = 0; i < N; ++i) {
            cs += (unsigned long long)s.count_lt(keys[(size_t)i]);
            cs += (unsigned long long)(s.kth(kth_index(i, N)) + 1);
        }
    }
    return cs;
}

template <class SetT>
static void bench_struct(SetT &s, const vector<int> &keys, int N, double &t_ins, double &t_q,
                         double &t_era, unsigned long long &cs) {
    auto t0 = chrono::steady_clock::now();
    for (int i = 0; i < N; ++i) s.insert(keys[(size_t)i]);
    auto t1 = chrono::steady_clock::now();
    cs = query_stage(s, keys, N);
    auto t2 = chrono::steady_clock::now();
    for (int i = 0; i < N; i += 2) s.erase(keys[(size_t)i]);
    auto t3 = chrono::steady_clock::now();
    t_ins = chrono::duration<double>(t1 - t0).count();
    t_q = chrono::duration<double>(t2 - t1).count();
    t_era = chrono::duration<double>(t3 - t2).count();
}

int main() {
    printf("=== 0009 Splay / 文艺平衡树 ===\n");

    // ---------- G1: 双旋 splay vs oracle ----------
    {
        printf("[G1] SplaySet(双旋) 随机对拍\n");
        SplaySet s(40000);
        SortedOracle o;
        run_set_ops(s, o, 40000, 200, "splay");
        if (!s.check()) { ++g_fail; printf("    [FAIL] splay check() 不变式违例\n"); }
        printf("    size=%d height=%d spins=%llu\n", s.size(), s.height(), s.spins());
    }

    // ---------- G2: 单旋 splay vs oracle(正确性必须同样成立) ----------
    {
        printf("[G2] ZigOnlySet(单旋) 随机对拍\n");
        ZigOnlySet s(40000);
        SortedOracle o;
        run_set_ops(s, o, 20000, 200, "zig");
        if (!s.check()) { ++g_fail; printf("    [FAIL] zig check() 不变式违例\n"); }
        printf("    size=%d height=%d spins=%llu\n", s.size(), s.height(), s.spins());
    }

    // ---------- G3: SplaySeq vs 向量 oracle ----------
    {
        printf("[G3] SplaySeq 区间操作对拍(insert/erase/rev/add/sum/min/at)\n");
        SplaySeq q(4096);
        vector<long long> v;
        int bad = 0;
        // 从空序列开始, 用 insertAt 逐条建立, 顺带覆盖 n=0/1 的边界
        for (int step = 0; step < 6000; ++step) {
            uint64_t r = xr64();
            int op = (int)(r % 100);
            int n = (int)v.size();
            long long out = 0;
            if (op < 22 || n == 0) {
                int pos = (int)((r >> 8) % (uint64_t)(n + 1)) + 1;  // 1..n+1
                long long val = (long long)((r >> 20) % 1000);
                bool ok = q.insertAt(pos, val);
                if (!ok) { ++bad; CHECK(false, "insertAt(%d) 失败", pos); }
                v.insert(v.begin() + (pos - 1), val);
            } else if (op < 38) {
                int pos = (int)((r >> 8) % (uint64_t)n) + 1;
                bool ok = q.eraseAt(pos);
                if (!ok) { ++bad; CHECK(false, "eraseAt(%d) 失败", pos); }
                v.erase(v.begin() + (pos - 1));
            } else if (op < 55) {
                int l = (int)((r >> 8) % (uint64_t)n) + 1;
                int rr = l + (int)((r >> 20) % (uint64_t)(n - l + 1));
                bool ok = q.rangeRev(l, rr);
                if (!ok) { ++bad; CHECK(false, "rangeRev(%d,%d) 失败", l, rr); }
                reverse(v.begin() + (l - 1), v.begin() + rr);
            } else if (op < 70) {
                int l = (int)((r >> 8) % (uint64_t)n) + 1;
                int rr = l + (int)((r >> 20) % (uint64_t)(n - l + 1));
                long long d = (long long)((r >> 40) % 61) - 30;
                bool ok = q.rangeAdd(l, rr, d);
                if (!ok) { ++bad; CHECK(false, "rangeAdd(%d,%d,%lld) 失败", l, rr, d); }
                for (int i = l; i <= rr; ++i) v[(size_t)(i - 1)] += d;
            } else if (op < 84) {
                int l = (int)((r >> 8) % (uint64_t)n) + 1;
                int rr = l + (int)((r >> 20) % (uint64_t)(n - l + 1));
                long long a = 0;
                if (!q.rangeSum(l, rr, a)) { ++bad; CHECK(false, "rangeSum(%d,%d) 失败", l, rr); }
                long long b = 0;
                for (int i = l; i <= rr; ++i) b += v[(size_t)(i - 1)];
                if (a != b) { ++bad; CHECK(false, "rangeSum(%d,%d) %lld vs %lld", l, rr, a, b); }
            } else if (op < 94) {
                int l = (int)((r >> 8) % (uint64_t)n) + 1;
                int rr = l + (int)((r >> 20) % (uint64_t)(n - l + 1));
                long long a = 0;
                if (!q.rangeMin(l, rr, a)) { ++bad; CHECK(false, "rangeMin(%d,%d) 失败", l, rr); }
                long long b = LLONG_MAX;
                for (int i = l; i <= rr; ++i) b = min(b, v[(size_t)(i - 1)]);
                if (a != b) { ++bad; CHECK(false, "rangeMin(%d,%d) %lld vs %lld", l, rr, a, b); }
            } else {
                int pos = (int)((r >> 8) % (uint64_t)n) + 1;
                long long a = 0;
                if (!q.at(pos, a)) { ++bad; CHECK(false, "at(%d) 失败", pos); }
                if (a != v[(size_t)(pos - 1)]) { ++bad; CHECK(false, "at(%d) %lld vs %lld", pos, a, v[(size_t)(pos - 1)]); }
            }
            if (bad > 3) break;
        }
        vector<long long> got = q.toVector();
        if (got != v) {
            ++g_fail;
            printf("    [FAIL] seq 末态不一致: got %zu, want %zu\n", got.size(), v.size());
            size_t lim = min(got.size(), v.size());
            for (size_t i = 0; i < lim; ++i)
                if (got[i] != v[i]) { printf("    first diff @%zu: %lld vs %lld\n", i, got[i], v[i]); break; }
        } else {
            printf("    seq 末态 %d 元素逐位一致\n", (int)v.size());
        }
        if (!q.check()) { ++g_fail; printf("    [FAIL] seq check() 不变式违例\n"); }
    }

    // ---------- G4: 边界专项 ----------
    {
        printf("[G4] 边界专项\n");
        SplaySet s;
        CHECK(s.size() == 0, "空集 size=%d", s.size());
        CHECK(!s.erase(1), "空集 erase 应返回 false");
        CHECK(!s.contains(1), "空集 contains 应返回 false");
        CHECK(s.kth(0) == SplaySet::NOKEY, "空集 kth(0) 应返回哨兵");
        CHECK(s.height() == 0, "空集 height=%d", s.height());
        int tmp = 0;
        CHECK(!s.prev_lt(0, tmp), "空集 prev_lt 应返回 false");
        CHECK(!s.next_gt(0, tmp), "空集 next_gt 应返回 false");

        s.insert(5);
        s.insert(INT_MIN);
        s.insert(INT_MAX);
        CHECK(s.size() == 3, "插 3 个后 size=%d", s.size());
        CHECK(s.kth(0) == INT_MIN && s.kth(2) == INT_MAX, "kth 端点错: %d %d", s.kth(0), s.kth(2));
        CHECK(s.count_lt(INT_MIN) == 0, "count_lt(INT_MIN)=%d", s.count_lt(INT_MIN));
        CHECK(s.count_le(INT_MAX) == 3, "count_le(INT_MAX)=%d", s.count_le(INT_MAX));
        CHECK(!s.insert(5), "重复插入应返回 false");
        CHECK(s.size() == 3, "重复插入后 size=%d", s.size());
        CHECK(!s.prev_lt(INT_MIN, tmp), "INT_MIN 无前驱");
        CHECK(!s.next_gt(INT_MAX, tmp), "INT_MAX 无后继");
        CHECK(s.erase(INT_MAX) && s.size() == 2, "删除最大值后 size=%d", s.size());
        CHECK(s.erase(INT_MIN) && s.erase(5), "清空失败");
        CHECK(s.size() == 0 && s.root() == 0, "清空后 size=%d root=%d", s.size(), s.root());
        CHECK(s.insert(7) && s.size() == 1, "清空后重插失败");
        CHECK(s.to_vector() == vector<int>({7}), "重插后内容错");

        // 序列: 空表 / 单元素 / 全段翻转偶数次 / 越界
        SplaySeq q;
        CHECK(q.size() == 0, "空序列 size=%d", q.size());
        long long out = 0;
        CHECK(!q.at(1, out), "空序列 at 应失败");
        CHECK(!q.rangeSum(1, 0, out), "空序列区间和应失败");
        CHECK(!q.rangeRev(1, 1), "空序列翻转应失败");
        CHECK(!q.eraseAt(1), "空序列 eraseAt 应失败");
        CHECK(q.insertAt(1, 42) && q.size() == 1, "空序列插入首元素失败");
        CHECK(q.at(1, out) && out == 42, "单元素 at=%lld", out);
        CHECK(q.rangeRev(1, 1), "单元素翻转应成功");
        CHECK(q.at(1, out) && out == 42, "单元素翻转后 at=%lld", out);
        CHECK(!q.insertAt(3, 1), "越界 insertAt 应失败");
        CHECK(!q.rangeMin(1, 2, out), "越界 rangeMin 应失败");

        q.build({3, 1, 4, 1, 5, 9, 2, 6});
        CHECK(q.size() == 8, "build 后 size=%d", q.size());
        CHECK(q.rangeSum(1, 8, out) && out == 31, "总和=%lld, 期望 31", out);
        CHECK(q.rangeMin(1, 8, out) && out == 1, "最小值=%lld, 期望 1", out);
        CHECK(q.rangeRev(1, 8), "整段翻转失败");
        vector<long long> want = {6, 2, 9, 5, 1, 4, 1, 3};
        CHECK(q.toVector() == want, "整段翻转后序列错");
        for (int i = 0; i < 1001; ++i) q.rangeRev(1, 8);  // 奇数次: 又翻回去
        want = {3, 1, 4, 1, 5, 9, 2, 6};
        CHECK(q.toVector() == want, "翻转 1002 次(偶数)后应还原");
        CHECK(q.rangeAdd(1, 8, 10), "整段加失败");
        CHECK(q.rangeSum(1, 8, out) && out == 111, "加 10 后总和=%lld, 期望 111", out);
        CHECK(q.rangeMin(1, 8, out) && out == 11, "加 10 后最小值=%lld, 期望 11", out);
        CHECK(q.rangeRev(1, 4) && q.rangeAdd(2, 6, -100), "重叠 rev+add 失败");
        // 重叠操作后与暴力核对
        vector<long long> bf = {3 + 10, 1 + 10, 4 + 10, 1 + 10, 5 + 10, 9 + 10, 2 + 10, 6 + 10};
        reverse(bf.begin(), bf.begin() + 4);
        for (int i = 2; i <= 6; ++i) bf[(size_t)(i - 1)] -= 100;
        CHECK(q.toVector() == bf, "rev+add 交叠后与暴力不一致");
        CHECK(q.check(), "seq check() 不变式违例");
    }

    if (g_fail == 0) printf("correctness: ALL PASS\n");

    // ---------- G5: 单旋 vs 双旋 —— 均摊界为什么必须双旋 ----------
    {
        printf("[G5] 单旋 vs 双旋退化实证\n");
        const int M = 2000;

        // (1) 顺序插入 1..M: 两者都是纯链 —— splay 的平衡不是"插入即平衡"
        SplaySet A;
        ZigOnlySet B;
        for (int i = 1; i <= M; ++i) { A.insert(i); B.insert(i); }
        printf("    (1) 顺序插入 1..%d: 树高 双旋=%d 单旋=%d\n", M, A.height(), B.height());
        CHECK(A.height() == M && B.height() == M, "顺序插入应得到纯链: %d / %d", A.height(), B.height());

        // (2) 对最深处做一次访问: 双旋把访问路径"折半"(zig-zig 一次降两层), 单旋只把目标挪到根
        A.access(1);
        B.access(1);
        printf("    (2) 访问最小值一次后: 树高 双旋=%d 单旋=%d (预期 ~M/2 / M)\n", A.height(), B.height());
        CHECK(A.height() <= M / 2 + 4 && A.height() >= M / 4, "双旋后树高未折半: %d", A.height());
        CHECK(B.height() >= M - 2, "单旋后树高应几乎不变: %d", B.height());

        // (3) 顺序访问 1..M: 双旋 O(n)(顺序访问定理), 单旋 Θ(n^2)
        SplaySet A2;
        ZigOnlySet B2;
        for (int i = 1; i <= M; ++i) { A2.insert(i); B2.insert(i); }
        unsigned long long d0 = A2.spins(), e0 = B2.spins();
        for (int i = 1; i <= M; ++i) { A2.access(i); B2.access(i); }
        unsigned long long dA = A2.spins() - d0, dB = B2.spins() - e0;
        printf("    (3) 顺序访问 1..%d: 双旋旋转=%llu (%.2f/M) 单旋旋转=%llu (%.2f/M^2)\n", M, dA,
               (double)dA / (double)M, dB, (double)dB / ((double)M * (double)M));
        CHECK(dA <= (unsigned long long)(6 * M), "双旋顺序访问应为线性: %llu", dA);
        CHECK(dB >= (unsigned long long)M * (unsigned long long)M / 4, "单旋顺序访问应为平方级: %llu", dB);
        CHECK(dB >= 20 * dA, "双旋/单旋差距不足: %llu vs %llu", dA, dB);
    }

    // ---------- 基准 1: 集合 N=2e5 三方 ----------
    {
        const int N = 200000;
        printf("\nbenchmark set N=%d (seconds)\n", N);
        vector<int> keys((size_t)N);
        for (int i = 0; i < N; ++i) keys[(size_t)i] = i * 2;
        for (int i = N - 1; i > 0; --i) {  // 洗牌, 避免顺序插入的退化/优势混淆结论
            int j = (int)(xr64() % (uint64_t)(i + 1));
            swap(keys[(size_t)i], keys[(size_t)j]);
        }

        struct Bench { const char *name; double t_ins, t_q, t_era; unsigned long long cs; };
        Bench res[3];

        SplaySet s1((size_t)N);
        bench_struct(s1, keys, N, res[0].t_ins, res[0].t_q, res[0].t_era, res[0].cs);
        res[0].name = "splay";
        printf("    splay: size=%d height=%d spins=%llu\n", s1.size(), s1.height(), s1.spins());

        ZigOnlySet s2((size_t)N);
        bench_struct(s2, keys, N, res[1].t_ins, res[1].t_q, res[1].t_era, res[1].cs);
        res[1].name = "zig-only";
        printf("    zig: size=%d height=%d spins=%llu\n", s2.size(), s2.height(), s2.spins());

        std::set<int> s3;
        bench_struct(s3, keys, N, res[2].t_ins, res[2].t_q, res[2].t_era, res[2].cs);
        res[2].name = "std::set";
        printf("    set: size=%zu\n", s3.size());

        printf("%-10s %10s %10s %10s\n", "struct", "insert", "query", "erase");
        for (int i = 0; i < 3; ++i)
            printf("%-10s %10.3f %10.3f %10.3f\n", res[i].name, res[i].t_ins, res[i].t_q, res[i].t_era);
        CHECK(res[0].cs == res[1].cs, "splay/zig 查询校验和不一致: %llu vs %llu", res[0].cs, res[1].cs);
        printf("checksum(splay)=%llu checksum(zig)=%llu checksum(set)=%llu\n",
               res[0].cs, res[1].cs, res[2].cs);
    }

    // ---------- 基准 2: 序列 M=3e5 ----------
    {
        const int M = 300000;
        printf("\nbenchmark seq M=%d\n", M);
        vector<int> init((size_t)M);
        for (int i = 0; i < M; ++i) init[(size_t)i] = (int)(xr64() % 1000);
        SplaySeq q((size_t)M);
        auto t0 = chrono::steady_clock::now();
        q.build(init);
        auto t1 = chrono::steady_clock::now();
        long long cs = 0, out = 0;
        for (int i = 0; i < 50000; ++i) {
            int l = (int)(xr64() % (uint64_t)M) + 1;
            int rr = l + (int)(xr64() % (uint64_t)(M - l + 1));
            if (q.rangeSum(l, rr, out)) cs += out;
        }
        auto t2 = chrono::steady_clock::now();
        for (int i = 0; i < 50000; ++i) {
            int l = (int)(xr64() % (uint64_t)M) + 1;
            int rr = l + (int)(xr64() % (uint64_t)(M - l + 1));
            q.rangeAdd(l, rr, (long long)(i % 7) - 3);
        }
        auto t3 = chrono::steady_clock::now();
        for (int i = 0; i < 50000; ++i) {  // 小段翻转: O(log n) 定位 + O(1) 打标记
            int l = (int)(xr64() % (uint64_t)M) + 1;
            int len = (int)(xr64() % 100) + 1;
            if (l + len - 1 <= M) q.rangeRev(l, l + len - 1);
        }
        auto t4 = chrono::steady_clock::now();
        for (int i = 0; i < 50000; ++i) {
            int l = (int)(xr64() % (uint64_t)M) + 1;
            int rr = l + (int)(xr64() % (uint64_t)(M - l + 1));
            if (q.rangeMin(l, rr, out)) cs += out;
        }
        auto t5 = chrono::steady_clock::now();
        printf("%-18s %10s\n", "phase", "seconds");
        printf("%-18s %10.3f\n", "build(3e5, O(n))", chrono::duration<double>(t1 - t0).count());
        printf("%-18s %10.3f\n", "sum(5e4)", chrono::duration<double>(t2 - t1).count());
        printf("%-18s %10.3f\n", "add(5e4)", chrono::duration<double>(t3 - t2).count());
        printf("%-18s %10.3f\n", "rev(5e4)", chrono::duration<double>(t4 - t3).count());
        printf("%-18s %10.3f\n", "min(5e4)", chrono::duration<double>(t5 - t4).count());
        printf("checksum=%lld size=%d height=%d\n", cs, q.size(), q.heightHint());
        CHECK(q.size() == M, "序列长度被破坏: %d", q.size());
        CHECK(q.check(), "序列结构不变式被破坏(sz/sum/mn/add 自洽)");
    }

    if (g_fail == 0)
        printf("RESULT: ALL PASS\n");
    else
        printf("RESULT: %d FAIL\n", g_fail);
    return g_fail == 0 ? 0 : 1;
}
