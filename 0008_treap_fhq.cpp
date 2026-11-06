// ============================================================
// 0008 · Treap / FHQ-Treap(无旋转分裂合并 + 区间翻转 + 可持久化)
// ------------------------------------------------------------
// 四个实现, 层层递进:
//   A. FHQSet        无旋转 Treap: 按值分裂(split_lt/split_le) + 合并(数组池 + 空闲链表复用)
//   B. RotTreap      经典旋转 Treap: 插入旋转上浮 / 删除旋转下沉(对照实现, 不支持区间)
//   C. FHQSeq        隐式键 Treap: 按排名分裂, 支持区间翻转 lazy 标记 + 区间和
//   D. PersistentFHQ 可持久化 Treap: split/merge 路径复制, 保留任意历史版本做第 k 小查询
// 正确性: G1-G4 与有序向量(dedup 集合语义)逐条对拍 + 结构不变式自检 + G5 边界专项
// 性能:   N=4e5 建树 / 查排名 / 查第 k 小 / 删除, 三方横向对比; 序列版 3e5 建 + 区间操作
// 编译:   g++ -O2 -std=c++17 -Wall -Wextra 0008_treap_fhq.cpp -o 0008
// 注意:   本期源码未在本机编译(环境无 C++ 编译器), 算法逻辑已通过 Python 逐行镜像
//         (.verify_mirror_0008.py) 随机对拍验证, 详见 0008_treap_fhq.md
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
// 确定性伪随机(xorshift64): 固定种子, 同一份代码多次运行结果可复现
// Treap 的优先级必须随机 —— 这是它期望 O(log n) 的唯一来源
// ============================================================
static uint64_t g_seed = 0x9E3779B97F4A7C15ULL;
static inline uint64_t xr64() {
    g_seed ^= g_seed << 13;
    g_seed ^= g_seed >> 7;
    g_seed ^= g_seed << 17;
    return g_seed;
}
static inline uint32_t xr32() { return (uint32_t)(xr64() >> 11); }

// ============================================================
// A. FHQSet — 无旋转 Treap(集合语义)
//
// 核心只有两个操作:
//   split(x, key) -> (a, b)  : 按值把树切成两棵, 不改变任何节点的父子关系之外的结构
//   merge(a, b)              : 前提 max(a) < min(b), 按优先级选根递归
// 插入 = split 拆开 + 新建节点 + 两次 merge;  删除 = 两次 split 摘出来 + merge 残部
//
// 数组池 + 空闲链表: 删除的节点不还给系统, 而是回收到 free_, 供后续插入复用
//   → 混合负载(反复插删)下内存不增长; 也是 0007 哈希表之后第二个"池化"实现
// ============================================================
class FHQSet {
public:
    static constexpr int NOKEY = INT_MIN;  // kth 越界哨兵(约定调用方先用 size() 判断)

    explicit FHQSet(size_t reserve_n = 1024) {
        t.reserve(reserve_n + 1);
        t.push_back(Node{});  // 0 号位是 NIL: sz=0, pull 因此无需判空
    }

    int size() const { return t[root_].sz; }
    int root() const { return root_; }

    // true = 新插入; false = 键已存在(集合语义不重复计数)
    bool insert(int key) {
        int a, b, c, d;
        split_lt(root_, key, a, b);  // a: < key      b: >= key
        split_le(b, key, c, d);      // c: == key     d: > key
        if (c) {                     // 已存在: 原样并回, 不新建
            root_ = merge(a, merge(c, d));
            return false;
        }
        int nd = alloc(key);
        root_ = merge(a, merge(nd, d));
        return true;
    }

    bool erase(int key) {
        int a, b, c, d;
        split_lt(root_, key, a, b);
        split_le(b, key, c, d);
        if (!c) {  // 键不存在: b 仍是合法 Treap, 直接并回
            root_ = merge(a, b);
            return false;
        }
        recycle(c);  // 整棵只含 key 的单点树(集合语义) → 回收
        root_ = merge(a, d);
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

    // 严格小于 key 的个数 = key 的 0-based 排名
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

    // 0-based 第 k 小(k ∈ [0, size)), 越界返回 NOKEY
    int kth(int k) const {
        if (k < 0 || k >= t[root_].sz) return NOKEY;
        int x = root_;
        while (x) {
            int ls = t[t[x].l].sz;
            if (k < ls) x = t[x].l;
            else if (k == ls) return t[x].key;
            else { k -= ls + 1; x = t[x].r; }
        }
        return NOKEY;  // 不可达
    }

    bool prev_lt(int key, int &out) const {  // 严格小于 key 的最大键
        int c = count_lt(key);
        if (c == 0) return false;
        out = kth(c - 1);
        return true;
    }
    bool next_gt(int key, int &out) const {  // 严格大于 key 的最小键
        int c = count_le(key);
        if (c >= t[root_].sz) return false;
        out = kth(c);
        return true;
    }

    // 中序遍历 → 直接检验 BST 有序性
    vector<int> to_vector() const {
        vector<int> out;
        out.reserve((size_t)t[root_].sz);
        stack<int> st;
        int cur = root_;
        while (cur || !st.empty()) {
            while (cur) { st.push(cur); cur = t[cur].l; }
            cur = st.top(); st.pop();
            out.push_back(t[cur].key);
            cur = t[cur].r;
        }
        return out;
    }

    // 结构不变式自检: sz 一致 + 大根堆序(父 pri >= 子 pri) + 键域
    bool check() const {
        int cnt = 0;
        bool ok = walk(root_, nullptr, nullptr, cnt);
        return ok && cnt == t[root_].sz;
    }

protected:
    struct Node {
        int l = 0, r = 0, key = 0;
        uint32_t pri = 0;
        int sz = 0;
    };
    vector<Node> t;
    vector<int> free_;
    int root_ = 0;

    int alloc(int key) {
        int id;
        if (!free_.empty()) {
            id = free_.back();
            free_.pop_back();
            t[(size_t)id] = Node{0, 0, key, xr32(), 1};
        } else {
            id = (int)t.size();
            t.push_back(Node{0, 0, key, xr32(), 1});
        }
        return id;
    }

    // 迭代后序回收整棵子树(避免深递归), 节点清零后进空闲链表
    void recycle(int x) {
        if (!x) return;
        vector<int> st;
        st.push_back(x);
        while (!st.empty()) {
            int u = st.back();
            st.pop_back();
            int l = t[u].l, r = t[u].r;
            t[u] = Node{};
            free_.push_back(u);
            if (l) st.push_back(l);
            if (r) st.push_back(r);
        }
    }

    static void pull(vector<Node> &t, int x) {
        if (x) t[x].sz = t[t[x].l].sz + t[t[x].r].sz + 1;
    }
    void pull_(int x) { pull(t, x); }

    // a: keys < key; b: keys >= key
    void split_lt(int x, int key, int &a, int &b) {
        if (!x) { a = b = 0; return; }
        if (t[x].key < key) { a = x; split_lt(t[x].r, key, t[x].r, b); }
        else { b = x; split_lt(t[x].l, key, a, t[x].l); }
        pull_(x);
    }

    // a: keys <= key; b: keys > key
    void split_le(int x, int key, int &a, int &b) {
        if (!x) { a = b = 0; return; }
        if (t[x].key <= key) { a = x; split_le(t[x].r, key, t[x].r, b); }
        else { b = x; split_le(t[x].l, key, a, t[x].l); }
        pull_(x);
    }

    int merge(int a, int b) {
        if (!a || !b) return a | b;
        if (t[a].pri > t[b].pri) { t[a].r = merge(t[a].r, b); pull_(a); return a; }
        t[b].l = merge(a, t[b].l); pull_(b); return b;
    }

    bool walk(int x, const int *lo, const int *hi, int &cnt) const {
        if (!x) return true;
        if (lo && t[x].key <= *lo) return false;
        if (hi && t[x].key >= *hi) return false;
        if (t[x].sz != t[t[x].l].sz + t[t[x].r].sz + 1) return false;
        if (t[x].l && t[t[x].l].pri > t[x].pri) return false;
        if (t[x].r && t[t[x].r].pri > t[x].pri) return false;
        ++cnt;
        int lo2 = t[x].key, hi2 = t[x].key;
        return walk(t[x].l, lo, &hi2, cnt) && walk(t[x].r, &lo2, hi, cnt);
    }
};

// ============================================================
// B. RotTreap — 经典旋转 Treap(对照实现)
//   插入: 递归插入后若子节点 pri 更大则单旋上浮
//   删除: 找到节点后把 pri 更大的孩子旋上来, 目标下沉一层, 继续删; 叶子直接摘除
//   与 FHQ 的差别: 无 split/merge 抽象, 天然不支持区间/可持久化(修改是原地破坏性的)
//   这里同样维护 sz, 以支持 rank / kth, 保证与 FHQSet 可比
// ============================================================
class RotTreap {
public:
    static constexpr int NOKEY = INT_MIN;

    explicit RotTreap(size_t reserve_n = 1024) {
        t.reserve(reserve_n + 1);
        t.push_back(Node{});
    }

    int size() const { return t[root_].sz; }

    bool insert(int key) {
        bool added = false;
        root_ = ins(root_, key, added);
        return added;
    }

    bool erase(int key) {
        bool rem = false;
        root_ = era(root_, key, rem);
        return rem;
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

    int count_lt(int key) const {
        int x = root_, res = 0;
        while (x) {
            if (t[x].key < key) { res += t[t[x].l].sz + 1; x = t[x].r; }
            else x = t[x].l;
        }
        return res;
    }

    int kth(int k) const {
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

    int count_le(int key) const {
        int x = root_, res = 0;
        while (x) {
            if (t[x].key <= key) { res += t[t[x].l].sz + 1; x = t[x].r; }
            else x = t[x].l;
        }
        return res;
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
        stack<int> st;
        int cur = root_;
        while (cur || !st.empty()) {
            while (cur) { st.push(cur); cur = t[cur].l; }
            cur = st.top(); st.pop();
            out.push_back(t[cur].key);
            cur = t[cur].r;
        }
        return out;
    }

    int height() const { return h(root_); }

private:
    struct Node {
        int l = 0, r = 0, key = 0;
        uint32_t pri = 0;
        int sz = 0;
    };
    vector<Node> t;
    vector<int> free_;
    int root_ = 0;

    int alloc(int key) {
        int id;
        if (!free_.empty()) {
            id = free_.back();
            free_.pop_back();
            t[(size_t)id] = Node{0, 0, key, xr32(), 1};
        } else {
            id = (int)t.size();
            t.push_back(Node{0, 0, key, xr32(), 1});
        }
        return id;
    }

    void pull_(int x) { if (x) t[x].sz = t[t[x].l].sz + t[t[x].r].sz + 1; }

    int rot_right(int y) {  // y 的左孩子 x 上位
        int x = t[y].l;
        t[y].l = t[x].r;
        t[x].r = y;
        pull_(y);
        pull_(x);
        return x;
    }

    int rot_left(int x) {  // x 的右孩子 y 上位
        int y = t[x].r;
        t[x].r = t[y].l;
        t[y].l = x;
        pull_(x);
        pull_(y);
        return y;
    }

    int ins(int x, int key, bool &added) {
        if (!x) { added = true; return alloc(key); }
        if (key == t[x].key) { added = false; return x; }
        if (key < t[x].key) {
            t[x].l = ins(t[x].l, key, added);
            if (t[x].l && t[t[x].l].pri > t[x].pri) x = rot_right(x);
        } else {
            t[x].r = ins(t[x].r, key, added);
            if (t[x].r && t[t[x].r].pri > t[x].pri) x = rot_left(x);
        }
        pull_(x);
        return x;
    }

    int era(int x, int key, bool &rem) {
        if (!x) return 0;
        if (key < t[x].key) { t[x].l = era(t[x].l, key, rem); pull_(x); return x; }
        if (key > t[x].key) { t[x].r = era(t[x].r, key, rem); pull_(x); return x; }
        rem = true;
        if (!t[x].l || !t[x].r) {  // 至多一个孩子: 直接摘除
            int y = t[x].l ? t[x].l : t[x].r;
            t[x] = Node{};
            free_.push_back(x);
            return y;
        }
        // 两个孩子都在: pri 大的孩子旋上来, 目标下沉一层, 递归继续删同一 key
        if (t[t[x].l].pri > t[t[x].r].pri) {
            int y = rot_right(x);
            t[y].r = era(t[y].r, key, rem);
            pull_(y);
            return y;
        }
        int y = rot_left(x);
        t[y].l = era(t[y].l, key, rem);
        pull_(y);
        return y;
    }

    int h(int x) const {  // 实测树高(仅用于诊断, 递归深度 ≤ 树高 + 1)
        if (!x) return 0;
        return 1 + max(h(t[x].l), h(t[x].r));
    }
};

// ============================================================
// C. FHQSeq — 隐式键 Treap(序列 = 中序遍历顺序)
//   把"按值分裂"换成"按排名分裂": 左子树规模就是下标偏移, 与键值无关
//   → 支持 O(log n) 的任意位置插入/删除/区间翻转/区间和
//   区间翻转: 把区间 split 出来, 在根上打 rev 标记(交换左右孩子的动作推迟到真正访问时)
// ============================================================
class FHQSeq {
public:
    explicit FHQSeq(size_t reserve_n = 1024) {
        t.reserve(reserve_n + 1);
        t.push_back(Node{});  // NIL: sz=0, sum=0
    }

    int size() const { return t[root_].sz; }

    void push_back(int v) { root_ = merge(root_, alloc(v)); }

    // 在第 pos 个元素之前插入(pos ∈ [0, size])
    bool insert_at(int pos, int v) {
        if (pos < 0 || pos > t[root_].sz) return false;
        int a, b;
        split_sz(root_, pos, a, b);
        root_ = merge(merge(a, alloc(v)), b);
        return true;
    }

    bool erase_at(int pos) {
        if (pos < 0 || pos >= t[root_].sz) return false;
        int a, b, c;
        split_sz(root_, pos, a, b);       // a: [0, pos)
        split_sz(b, 1, b, c);             // b: [pos, pos+1)  c: [pos+1, ...)
        root_ = merge(a, c);              // b 单点树丢弃(不回收: 保持 lazy 简单)
        return true;
    }

    // 闭区间 [l, r] 翻转
    bool reverse_range(int l, int r) {
        if (l < 0 || r >= t[root_].sz || l > r) return false;
        int a, b, c;
        split_sz(root_, l, a, b);
        split_sz(b, r - l + 1, b, c);
        if (b) t[b].rev ^= 1;  // 只交换标记, O(1)
        root_ = merge(a, merge(b, c));
        return true;
    }

    long long range_sum(int l, int r) {
        if (l < 0 || r >= t[root_].sz || l > r) return 0;
        int a, b, c;
        split_sz(root_, l, a, b);
        split_sz(b, r - l + 1, b, c);
        long long s = t[b].sum;
        root_ = merge(a, merge(b, c));
        return s;
    }

    int at(int pos) const {
        if (pos < 0 || pos >= t[root_].sz) return INT_MIN;
        int x = root_;
        FHQSeq *self = const_cast<FHQSeq *>(this);
        while (x) {
            self->push(x);
            int ls = t[t[x].l].sz;
            if (pos < ls) x = t[x].l;
            else if (pos == ls) return t[x].val;
            else { pos -= ls + 1; x = t[x].r; }
        }
        return INT_MIN;
    }

    vector<int> to_vector() const {
        vector<int> out;
        out.reserve((size_t)t[root_].sz);
        FHQSeq *self = const_cast<FHQSeq *>(this);
        stack<pair<int, int>> st;  // (节点, 状态): 0=待展开左子树
        if (root_) st.push({root_, 0});
        while (!st.empty()) {
            int x = st.top().first, state = st.top().second;
            st.pop();
            self->push(x);  // 展开前必须落实 rev, 否则左右顺序是反的
            if (state == 0) {
                st.push({x, 1});
                if (t[x].l) st.push({t[x].l, 0});
            } else {
                out.push_back(t[x].val);
                if (t[x].r) st.push({t[x].r, 0});
            }
        }
        return out;
    }

    bool check() const {
        int cnt = 0;
        bool ok = walk(root_, cnt);
        return ok && cnt == t[root_].sz;
    }

private:
    struct Node {
        int l = 0, r = 0, val = 0;
        uint32_t pri = 0;
        int sz = 0;
        long long sum = 0;
        bool rev = false;
    };
    vector<Node> t;
    int root_ = 0;

    int alloc(int v) {
        int id = (int)t.size();
        t.push_back(Node{0, 0, v, xr32(), 1, (long long)v, false});
        return id;
    }

    static void pull(vector<Node> &t, int x) {
        if (!x) return;
        t[x].sz = t[t[x].l].sz + t[t[x].r].sz + 1;
        t[x].sum = t[t[x].l].sum + t[t[x].r].sum + (long long)t[x].val;
    }
    void pull_(int x) { pull(t, x); }

    // 落实翻转: 交换孩子 + 把标记下推。注意 sum 与 sz 对翻转不敏感(不需要改)
    void push(int x) {
        if (!x || !t[x].rev) return;
        swap(t[x].l, t[x].r);
        if (t[x].l) t[t[x].l].rev ^= 1;
        if (t[x].r) t[t[x].r].rev ^= 1;
        t[x].rev = false;
    }

    // a: 前 k 个元素; b: 其余
    void split_sz(int x, int k, int &a, int &b) {
        if (!x) { a = b = 0; return; }
        push(x);
        int ls = t[t[x].l].sz;
        if (k <= ls) { b = x; split_sz(t[x].l, k, a, t[x].l); }
        else { a = x; split_sz(t[x].r, k - ls - 1, t[x].r, b); }
        pull_(x);
    }

    int merge(int a, int b) {
        if (!a || !b) return a | b;
        if (t[a].pri > t[b].pri) {
            push(a);
            t[a].r = merge(t[a].r, b);
            pull_(a);
            return a;
        }
        push(b);
        t[b].l = merge(a, t[b].l);
        pull_(b);
        return b;
    }

    bool walk(int x, int &cnt) const {
        if (!x) return true;
        if (t[x].sz != t[t[x].l].sz + t[t[x].r].sz + 1) return false;
        if (t[x].sum != t[t[x].l].sum + t[t[x].r].sum + (long long)t[x].val) return false;
        if (t[x].l && t[t[x].l].pri > t[x].pri) return false;
        if (t[x].r && t[t[x].r].pri > t[x].pri) return false;
        ++cnt;
        return walk(t[x].l, cnt) && walk(t[x].r, cnt);
    }
};

// ============================================================
// D. PersistentFHQ — 可持久化 Treap(路径复制)
//   split/merge 不修改原节点, 而是"复制一份改指针": 一次操作只新增 O(log n) 个节点
//   → 任意历史版本根永久可用; 空间 O((n + q) log n)
//   典型应用: "每次插入一个数, 查询某历史版本第 k 小"(在线可持久化集合)
// ============================================================
class PersistentFHQ {
public:
    static constexpr int NOKEY = INT_MIN;

    explicit PersistentFHQ(size_t reserve_n = 1024) {
        t.reserve(reserve_n + 1);
        t.push_back(Node{});
    }

    int size(int root) const { return t[root].sz; }

    bool contains(int root, int key) const {
        while (root) {
            if (key < t[root].key) root = t[root].l;
            else if (key > t[root].key) root = t[root].r;
            else return true;
        }
        return false;
    }

    // 返回新版本根; 键已存在时原样返回(不产生新版本)
    int insert(int root, int key) {
        if (contains(root, key)) return root;
        int a, b;
        split_lt(root, key, a, b);
        int nd = mk(0, 0, key, xr32(), 1);
        return merge(merge(a, nd), b);
    }

    int count_lt(int root, int key) const {
        int res = 0;
        while (root) {
            if (t[root].key < key) { res += t[t[root].l].sz + 1; root = t[root].r; }
            else root = t[root].l;
        }
        return res;
    }

    int kth(int root, int k) const {
        if (k < 0 || k >= t[root].sz) return NOKEY;
        while (root) {
            int ls = t[t[root].l].sz;
            if (k < ls) root = t[root].l;
            else if (k == ls) return t[root].key;
            else { k -= ls + 1; root = t[root].r; }
        }
        return NOKEY;
    }

    size_t node_count() const { return t.size() - 1; }

private:
    struct Node {
        int l = 0, r = 0, key = 0;
        uint32_t pri = 0;
        int sz = 0;
    };
    vector<Node> t;  // 只增不改: 已发布的版本永远指向旧节点

    int mk(int l, int r, int key, uint32_t pri, int sz) {
        t.push_back(Node{l, r, key, pri, sz});
        return (int)t.size() - 1;
    }

    // a: keys < key, b: keys >= key —— 沿路径复制
    void split_lt(int x, int key, int &a, int &b) {
        if (!x) { a = b = 0; return; }
        if (t[x].key < key) {
            int na = 0, nb = 0;
            split_lt(t[x].r, key, na, nb);
            a = mk(t[x].l, na, t[x].key, t[x].pri, t[t[x].l].sz + t[na].sz + 1);
            b = nb;
        } else {
            int na = 0, nb = 0;
            split_lt(t[x].l, key, na, nb);
            b = mk(na, t[x].r, t[x].key, t[x].pri, t[na].sz + t[t[x].r].sz + 1);
            a = na;
        }
    }

    int merge(int a, int b) {
        if (!a || !b) return a | b;
        if (t[a].pri > t[b].pri) {
            int nr = merge(t[a].r, b);
            return mk(t[a].l, nr, t[a].key, t[a].pri, t[t[a].l].sz + t[nr].sz + 1);
        }
        int nl = merge(a, t[b].l);
        return mk(nl, t[b].r, t[b].key, t[b].pri, t[nl].sz + t[t[b].r].sz + 1);
    }
};

// ============================================================
// 验证工具: 有序向量作为 oracle(dedup 集合语义)
// ============================================================
struct SortedOracle {
    vector<int> v;  // 恒有序且无重复

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
    int count_lt(int key) const {
        return (int)(lower_bound(v.begin(), v.end(), key) - v.begin());
    }
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

// 对一个集合实现跑一段随机操作, 与 oracle 逐条比对
template <class SetT>
static void run_set_ops(SetT &s, SortedOracle &o, int ops, uint32_t keymod,
                        const char *name) {
    int mismatch = 0;
    for (int i = 0; i < ops; ++i) {
        uint64_t r = xr64();
        int op = (int)(r % 100);
        int key = (int)((r >> 8) % keymod);
        if (op < 40) {
            bool a = s.insert(key), b = o.insert(key);
            if (a != b) { ++mismatch; CHECK(false, "%s insert(%d) ret %d vs %d", name, key, (int)a, (int)b); }
        } else if (op < 60) {
            bool a = s.erase(key), b = o.erase(key);
            if (a != b) { ++mismatch; CHECK(false, "%s erase(%d) ret %d vs %d", name, key, (int)a, (int)b); }
        } else if (op < 70) {
            bool a = s.contains(key), b = o.contains(key);
            if (a != b) { ++mismatch; CHECK(false, "%s contains(%d) %d vs %d", name, key, (int)a, (int)b); }
        } else if (op < 85) {
            int a = s.count_lt(key), b = o.count_lt(key);
            if (a != b) { ++mismatch; CHECK(false, "%s count_lt(%d) %d vs %d", name, key, a, b); }
        } else if (op < 95) {
            // k 取到 size+1, 刻意覆盖越界分支
            int k = (int)((r >> 20) % (uint32_t)(o.v.size() + 2));
            int a = s.kth(k), b = o.kth(k);
            if (a != b) { ++mismatch; CHECK(false, "%s kth(%d) %d vs %d", name, k, a, b); }
        } else {
            int pa = 0, pb = 0;
            bool fa = s.prev_lt(key, pa), fb = o.prev_lt(key, pb);
            if (fa != fb || (fa && pa != pb)) { ++mismatch; CHECK(false, "%s prev_lt(%d) %d/%d vs %d/%d", name, key, (int)fa, pa, (int)fb, pb); }
            int na = 0, nb = 0;
            bool ga = s.next_gt(key, na), gb = o.next_gt(key, nb);
            if (ga != gb || (ga && na != nb)) { ++mismatch; CHECK(false, "%s next_gt(%d) %d/%d vs %d/%d", name, key, (int)ga, na, (int)gb, nb); }
        }
        if (mismatch > 3) { printf("    [STOP] %s 连续失配, 终止该组\n", name); break; }
    }
    // 全量核对: 有序序列必须逐元素相同
    vector<int> got = s.to_vector();
    if (got != o.v) {
        ++g_fail;
        printf("    [FAIL] %s inorder mismatch: got %zu, want %zu\n", name, got.size(), o.v.size());
    }
    if (s.size() != (int)o.v.size()) {
        ++g_fail;
        printf("    [FAIL] %s size %d vs %zu\n", name, s.size(), o.v.size());
    }
}

// ============================================================
// 基准辅助
// 查询序列必须对两个 Treap 完全一致才能比较校验和:
// 第 k 小的下标由 i 的线性同余式确定, 不消耗全局随机数
// (若在循环里调 xr64(), 两次运行拿到的 k 不同, 校验和必然不等 → 假报警)
// ============================================================
static inline int kth_index(int i, int N) {
    return (int)((uint32_t)i * 2654435761u % (uint32_t)N);
}

template <class SetT>
static unsigned long long query_stage(SetT &s, const vector<int> &keys, int N) {
    unsigned long long cs = 0;
    if constexpr (is_same_v<SetT, std::set<int>>) {
        // std::set 无 rank/kth, 只比查找命中; 校验和与 Treap 不可比
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
static void bench_struct(SetT &s, const vector<int> &keys, int N, double &t_ins,
                         double &t_q, double &t_era, unsigned long long &cs) {
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
    printf("=== 0008 Treap / FHQ-Treap ===\n");

    // ---------- G1: FHQSet vs oracle ----------
    {
        printf("[G1] FHQSet 随机对拍\n");
        FHQSet s(20000);
        SortedOracle o;
        run_set_ops(s, o, 40000, 200, "fhq");
        if (!s.check()) { ++g_fail; printf("    [FAIL] fhq check() 不变式违例\n"); }
        printf("    size=%d\n", s.size());
    }

    // ---------- G2: RotTreap vs oracle ----------
    {
        printf("[G2] RotTreap 随机对拍\n");
        RotTreap s(20000);
        SortedOracle o;
        run_set_ops(s, o, 40000, 200, "rot");
        printf("    size=%d height=%d\n", s.size(), s.height());
    }

    // ---------- G3: FHQSeq vs 向量 oracle ----------
    {
        printf("[G3] FHQSeq 区间操作对拍(push/insert/erase/reverse/sum)\n");
        FHQSeq q(20000);
        vector<int> v;
        int bad = 0;
        for (int i = 0; i < 8000; ++i) {
            uint64_t r = xr64();
            int op = (int)(r % 100);
            int n = (int)v.size();
            if (op < 40 || n == 0) {
                int val = (int)((r >> 8) % 1000);
                q.push_back(val);
                v.push_back(val);
            } else if (op < 55) {
                int pos = (int)((r >> 8) % (uint32_t)(n + 1));
                int val = (int)((r >> 20) % 1000);
                bool a = q.insert_at(pos, val);
                v.insert(v.begin() + pos, val);
                if (!a) { ++bad; CHECK(false, "insert_at(%d) 失败", pos); }
            } else if (op < 65) {
                int pos = (int)((r >> 8) % (uint32_t)n);
                bool a = q.erase_at(pos);
                v.erase(v.begin() + pos);
                if (!a) { ++bad; CHECK(false, "erase_at(%d) 失败", pos); }
            } else if (op < 80) {
                int l = (int)((r >> 8) % (uint32_t)n);
                int r2 = l + (int)((r >> 20) % (uint32_t)(n - l));
                bool ok = q.reverse_range(l, r2);
                reverse(v.begin() + l, v.begin() + r2 + 1);
                if (!ok) { ++bad; CHECK(false, "reverse_range(%d,%d) 失败", l, r2); }
            } else if (op < 92) {
                int l = (int)((r >> 8) % (uint32_t)n);
                int r2 = l + (int)((r >> 20) % (uint32_t)(n - l));
                long long a = q.range_sum(l, r2);
                long long b = 0;
                for (int t2 = l; t2 <= r2; ++t2) b += v[(size_t)t2];
                if (a != b) { ++bad; CHECK(false, "range_sum(%d,%d) %lld vs %lld", l, r2, a, b); }
            } else {
                int pos = (int)((r >> 8) % (uint32_t)n);
                int a = q.at(pos);
                if (a != v[(size_t)pos]) { ++bad; CHECK(false, "at(%d) %d vs %d", pos, a, v[(size_t)pos]); }
            }
            if (bad > 3) break;
        }
        vector<int> got = q.to_vector();
        if (got != v) {
            ++g_fail;
            printf("    [FAIL] seq mismatch: got %zu want %zu\n", got.size(), v.size());
            size_t lim = min(got.size(), v.size());
            for (size_t i = 0; i < lim; ++i)
                if (got[i] != v[i]) { printf("    first diff @%zu: %d vs %d\n", i, got[i], v[i]); break; }
        } else {
            printf("    seq size=%d OK\n", (int)v.size());
        }
        if (!q.check()) { ++g_fail; printf("    [FAIL] seq check() 不变式违例\n"); }
    }

    // ---------- G4: 可持久化 —— 历史版本必须永不被破坏 ----------
    {
        printf("[G4] PersistentFHQ 版本对拍\n");
        PersistentFHQ p(200000);
        vector<int> roots;
        vector<vector<int>> snapshot;  // snapshot[i] = 第 i 版的有序内容
        roots.push_back(0);
        snapshot.push_back({});
        SortedOracle cur;
        int cur_root = 0;
        for (int i = 0; i < 400; ++i) {
            int key = (int)(xr64() % 500);
            int nr = p.insert(cur_root, key);
            if (nr != cur_root) {  // 只有真正插入才产生新版本
                cur.insert(key);
                cur_root = nr;
                roots.push_back(nr);
                snapshot.push_back(cur.v);
            }
        }
        int bad = 0;
        for (size_t ver = 0; ver < roots.size(); ++ver) {
            const vector<int> &want = snapshot[ver];
            if (p.size(roots[ver]) != (int)want.size()) {
                ++bad;
                CHECK(false, "版本%zu size %d vs %zu", ver, p.size(roots[ver]), want.size());
                continue;
            }
            for (int k = 0; k < (int)want.size(); ++k) {
                int got = p.kth(roots[ver], k);
                if (got != want[(size_t)k]) { ++bad; CHECK(false, "版本%zu kth(%d) %d vs %d", ver, k, got, want[(size_t)k]); break; }
            }
            // 越界必须返回哨兵
            if (p.kth(roots[ver], (int)want.size()) != PersistentFHQ::NOKEY) {
                ++bad;
                CHECK(false, "版本%zu kth 越界未返回哨兵", ver);
            }
        }
        // 版本数 × 每次 O(log n) 新增节点 ≈ 上界检查
        printf("    版本数=%zu 总节点=%zu (理论上界 %zu)\n", roots.size(), p.node_count(),
               (size_t)(roots.size() * 40));
        printf("    对拍失配=%d\n", bad);
    }

    // ---------- G5: 边界专项 ----------
    {
        printf("[G5] 边界专项\n");
        FHQSet s;
        CHECK(s.kth(0) == FHQSet::NOKEY, "空集 kth(0) 应返回哨兵, 实际 %d", s.kth(0));
        int tmp = 0;
        CHECK(!s.prev_lt(0, tmp), "空集 prev_lt 应返回 false");
        CHECK(!s.next_gt(0, tmp), "空集 next_gt 应返回 false");
        CHECK(!s.erase(12345), "空集 erase 应返回 false");
        CHECK(!s.contains(0), "空集 contains 应返回 false");

        s.insert(INT_MIN);
        s.insert(INT_MAX);
        s.insert(0);
        CHECK(s.size() == 3, "插 3 个后 size=%d", s.size());
        CHECK(s.kth(0) == INT_MIN && s.kth(2) == INT_MAX, "kth 端点错: %d %d", s.kth(0), s.kth(2));
        CHECK(s.prev_lt(INT_MIN, tmp) == false, "INT_MIN 无前驱");
        CHECK(s.next_gt(INT_MAX, tmp) == false, "INT_MAX 无后继");
        CHECK(s.count_lt(INT_MIN) == 0, "count_lt(INT_MIN)=%d", s.count_lt(INT_MIN));
        CHECK(s.count_le(INT_MAX) == 3, "count_le(INT_MAX)=%d", s.count_le(INT_MAX));
        CHECK(!s.insert(0), "重复插入应返回 false");
        CHECK(s.size() == 3, "重复插入后 size=%d", s.size());

        FHQSeq q;
        CHECK(q.range_sum(0, 0) == 0, "空序列区间和为 0");
        q.push_back(7);
        CHECK(q.at(0) == 7, "单元素 at(0)=%d", q.at(0));
        CHECK(q.reverse_range(0, 0), "单元素翻转应成功");
        CHECK(q.at(0) == 7, "单元素翻转后值不变");
        CHECK(!q.erase_at(1), "越界 erase_at 应失败");
        CHECK(!q.insert_at(2, 1), "越界 insert_at 应失败");
        CHECK(q.insert_at(1, 9), "尾部 insert_at 应成功");
        CHECK(q.to_vector() == vector<int>({7, 9}), "序列应为 7,9");
        // 整段翻转 + 反复翻转必须还原(验证 lazy 标记成对抵消)
        for (int i = 0; i < 1000; ++i) q.reverse_range(0, 1);
        CHECK(q.to_vector() == vector<int>({7, 9}), "偶数次整段翻转应还原");

        PersistentFHQ p;
        int r0 = 0;
        CHECK(p.kth(r0, 0) == PersistentFHQ::NOKEY, "空版本 kth 应返回哨兵");
        int r1 = p.insert(r0, 42);
        CHECK(p.size(r0) == 0, "旧版本不应被修改: size=%d", p.size(r0));
        CHECK(p.size(r1) == 1 && p.kth(r1, 0) == 42, "新版本内容错");
        CHECK(p.insert(r1, 42) == r1, "重复插入应返回同一根");
    }

    if (g_fail == 0) printf("correctness: ALL PASS\n");

    // ---------- 基准: N=4e5 ----------
    {
        const int N = 400000;
        printf("\nbenchmark N=%d (seconds)\n", N);
        vector<int> keys((size_t)N);
        for (int i = 0; i < N; ++i) keys[(size_t)i] = i * 2;  // 偶数键, 间隔 2
        // Fisher-Yates 洗牌: 插入顺序随机, 避免顺序插值造成的退化
        for (int i = N - 1; i > 0; --i) {
            int j = (int)(xr64() % (uint64_t)(i + 1));
            swap(keys[(size_t)i], keys[(size_t)j]);
        }

        struct Bench { const char *name; double t_ins, t_q, t_era; unsigned long long cs; };
        Bench res[3];

        FHQSet s1((size_t)N);
        bench_struct(s1, keys, N, res[0].t_ins, res[0].t_q, res[0].t_era, res[0].cs);
        res[0].name = "fhq";
        printf("    fhq: size=%d\n", s1.size());

        RotTreap s2((size_t)N);
        bench_struct(s2, keys, N, res[1].t_ins, res[1].t_q, res[1].t_era, res[1].cs);
        res[1].name = "rot";
        printf("    rot: size=%d height=%d\n", s2.size(), s2.height());

        std::set<int> s3;
        bench_struct(s3, keys, N, res[2].t_ins, res[2].t_q, res[2].t_era, res[2].cs);
        res[2].name = "std::set";
        printf("    set: size=%zu\n", s3.size());

        printf("%-12s %10s %10s %10s\n", "struct", "insert", "query", "erase");
        for (int i = 0; i < 3; ++i)
            printf("%-12s %10.3f %10.3f %10.3f\n", res[i].name, res[i].t_ins, res[i].t_q, res[i].t_era);
        // fhq 与 rot 的查询序列完全相同(同 keys / 同 kth_index), 校验和必须一致
        CHECK(res[0].cs == res[1].cs, "fhq/rot 查询校验和不一致: %llu vs %llu", res[0].cs, res[1].cs);
        printf("checksum(fhq)=%llu checksum(rot)=%llu checksum(set)=%llu\n",
               res[0].cs, res[1].cs, res[2].cs);
    }

    // ---------- 基准: 隐式键序列 ----------
    {
        const int M = 300000;
        printf("\nbenchmark seq M=%d\n", M);
        FHQSeq q((size_t)M);
        auto t0 = chrono::steady_clock::now();
        for (int i = 0; i < M; ++i) q.push_back((int)(xr64() % 1000));
        auto t1 = chrono::steady_clock::now();
        long long cs = 0;
        for (int i = 0; i < 100000; ++i) {
            int l = (int)(xr64() % (uint64_t)M);
            int r = l + (int)(xr64() % (uint64_t)(M - l));
            cs += q.range_sum(l, r);
        }
        auto t2 = chrono::steady_clock::now();
        for (int i = 0; i < 50000; ++i) {  // 小段翻转: O(log n) 定位 + O(1) 打标记
            int l = (int)(xr64() % (uint64_t)M);
            int len = (int)(xr64() % 100);
            if (l + len < M) q.reverse_range(l, l + len);
        }
        auto t3 = chrono::steady_clock::now();
        printf("%-16s %10s\n", "phase", "seconds");
        printf("%-16s %10.3f\n", "build(3e5)", chrono::duration<double>(t1 - t0).count());
        printf("%-16s %10.3f\n", "sum(1e5)", chrono::duration<double>(t2 - t1).count());
        printf("%-16s %10.3f\n", "rev(5e4)", chrono::duration<double>(t3 - t2).count());
        printf("checksum=%lld size=%d\n", cs, q.size());
        CHECK(q.check(), "序列结构不变式被破坏(size/sum/heap)");
    }

    if (g_fail == 0)
        printf("RESULT: ALL PASS\n");
    else
        printf("RESULT: %d FAIL\n", g_fail);
    return g_fail == 0 ? 0 : 1;
}
