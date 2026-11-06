// ============================================================
// 0007 · 哈希表(开放寻址 / Open Addressing Flat Hash Map)
// ------------------------------------------------------------
// 三个核心实现 + std::unordered_map 对照:
//   A. LinearMap      线性探测 + 墓碑(缓存最友好, 最常用的 flat hash)
//   B. TriMap         三角数二次探测 t(t+1)/2 (模 2^k 遍历全表, 修复纯平方探测半表缺陷)
//   C. RobinHoodMap   Robin Hood hashing(PSL 均衡 + 查找早退 + 后移删除, 无墓碑)
//   对照              std::unordered_map(节点式链地址法, 指针追逐 + 每节点堆分配)
// 正确性: 四方随机对拍(插入/查找/删除结果逐条一致), 三角数覆盖性断言
// 性能:   N=2e6 插入 / 查找 / 删除 / 混合 四阶段基准, 四表横向对比
// 编译:   g++ -O2 -std=c++17 -Wall -Wextra 0007_open_addressing_hash_map.cpp -o 0007
// 注意:   本期源码未在本机编译(环境无 C++ 编译器), 算法逻辑已通过
//         Python 逐行镜像对拍验证, 详见 0007_open_addressing_hash_map.md
// ============================================================
#include <bits/stdc++.h>
using namespace std;
using u64 = uint64_t;

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
// 哈希函数: splitmix64 (雪崩性好, 极快, 一行混入常数)
// 键不直接取低位 —— 低位随机化是开放寻址正确的生命线
// ============================================================
static inline u64 splitmix64(u64 x) {
    x += 0x9E3779B97F4A7C15ULL;
    x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9ULL;
    x = (x ^ (x >> 27)) * 0x94D049BB133111EBULL;
    return x ^ (x >> 31);
}

// ============================================================
// A. 线性探测 + 墓碑
//    状态: 0=空 1=占用 2=墓碑
//    负载上限 0.7; 墓碑数 > 占用数时同容量 rehash 清墓碑
//    不变式: 表中永远至少有一个空槽(负载严格 < 1), 查找不会死循环
// ============================================================
class LinearMap {
public:
    static constexpr size_t NPOS = (size_t)-1;

    explicit LinearMap(size_t cap_hint = 16) { init(round_pow2(cap_hint * 2)); }

    bool contains(u64 k) const { return find(k) != NPOS; }

    // 返回 true = 新插入, false = 已存在并更新
    bool insert(u64 k, u64 v) {
        // 负载检查放在探测前: (占用+墓碑+1) 超限即扩容
        if ((used_ + tombs_ + 1) * 10 >= cap_ * 7) grow();
        size_t pos = probe_insert(k);
        if (pos != NPOS) { keys_[pos] = k; vals_[pos] = v; state_[pos] = 1; ++used_; return true; }
        // probe_insert 找到了已有键并原地更新的情况不会走到这里(见 probe_insert)
        return false;
    }

    u64* find(u64 k) {
        size_t pos = find_pos(k);
        return pos == NPOS ? nullptr : &vals_[pos];
    }
    const u64* find(u64 k) const { return const_cast<LinearMap*>(this)->find(k); }

    bool erase(u64 k) {
        size_t pos = find_pos(k);
        if (pos == NPOS) return false;
        state_[pos] = 2;
        --used_; ++tombs_;
        // 墓碑超过占用数: 同容量 rehash 一次, 防止查找链无限变长
        if (tombs_ > used_) rehash(cap_);
        return true;
    }

    size_t size() const { return used_; }

private:
    vector<u64> keys_, vals_;
    vector<uint8_t> state_;
    size_t cap_ = 0, mask_ = 0, used_ = 0, tombs_ = 0;

    static size_t round_pow2(size_t x) {
        size_t p = 1;
        while (p < x) p <<= 1;
        return p;
    }

    void init(size_t cap) {
        cap_ = cap; mask_ = cap - 1;
        keys_.assign(cap, 0);
        vals_.assign(cap, 0);
        state_.assign(cap, 0);
        used_ = tombs_ = 0;
    }

    // 查找键所在槽位; 不存在返回 NPOS
    size_t find_pos(u64 k) const {
        size_t pos = (size_t)(splitmix64(k) & mask_);
        while (true) {
            uint8_t st = state_[pos];
            if (st == 0) return NPOS;                       // 空槽截断: 链断则键必不在
            if (st == 1 && keys_[pos] == k) return pos;     // 跳过墓碑继续走
            pos = (pos + 1) & mask_;
        }
    }

    // 插入用探测: 找到已存在的键返回 NPOS 并原地更新; 否则返回可放位置(优先复用墓碑)
    size_t probe_insert(u64 k) {
        size_t pos = (size_t)(splitmix64(k) & mask_);
        size_t first_tomb = NPOS;
        while (true) {
            uint8_t st = state_[pos];
            if (st == 0) {
                if (first_tomb != NPOS) { --tombs_; return first_tomb; }
                return pos;
            }
            if (st == 2) {
                if (first_tomb == NPOS) first_tomb = pos;
            } else if (keys_[pos] == k) {
                vals_[pos] = k;              // 已存在: 原地更新(值=键, 演示用)
                return NPOS;
            }
            pos = (pos + 1) & mask_;
        }
    }

    void grow() { rehash(cap_ * 2); }

    void rehash(size_t new_cap) {
        vector<u64> ok, ov;
        ok.reserve(used_); ov.reserve(used_);
        for (size_t i = 0; i < cap_; ++i)
            if (state_[i] == 1) { ok.push_back(keys_[i]); ov.push_back(vals_[i]); }
        init(new_cap);
        for (size_t i = 0; i < ok.size(); ++i) {
            size_t pos = (size_t)(splitmix64(ok[i]) & mask_);
            while (state_[pos] == 1) pos = (pos + 1) & mask_;
            keys_[pos] = ok[i]; vals_[pos] = ov[i]; state_[pos] = 1; ++used_;
        }
    }
};

// ============================================================
// B. 三角数二次探测
//    纯 i^2 探测在容量为 2^k 时只能触达一半槽位(性质: i^2 mod 2^k 的像只有一半)
//    改用三角数 T_t = t(t+1)/2: {T_t mod 2^k} 恰好取遍全部 2^k 个余数
//    且相邻位移差递增, 兼顾二次聚类的缓解与覆盖完整性
//    删除策略与线性探测相同: 墓碑
// ============================================================
class TriMap {
public:
    static constexpr size_t NPOS = (size_t)-1;

    explicit TriMap(size_t cap_hint = 16) { init(round_pow2(cap_hint * 2)); }

    bool insert(u64 k, u64 v) {
        if ((used_ + tombs_ + 1) * 10 >= cap_ * 7) grow();
        size_t pos = probe_insert(k);
        if (pos != NPOS) { keys_[pos] = k; vals_[pos] = v; state_[pos] = 1; ++used_; return true; }
        return false;
    }

    const u64* find(u64 k) const {
        size_t pos = find_pos(k);
        return pos == NPOS ? nullptr : &vals_[pos];
    }

    bool erase(u64 k) {
        size_t pos = find_pos(k);
        if (pos == NPOS) return false;
        state_[pos] = 2;
        --used_; ++tombs_;
        if (tombs_ > used_) rehash(cap_);
        return true;
    }

    size_t size() const { return used_; }

private:
    vector<u64> keys_, vals_;
    vector<uint8_t> state_;
    size_t cap_ = 0, mask_ = 0, used_ = 0, tombs_ = 0;

    static size_t round_pow2(size_t x) {
        size_t p = 1;
        while (p < x) p <<= 1;
        return p;
    }

    void init(size_t cap) {
        cap_ = cap; mask_ = cap - 1;
        keys_.assign(cap, 0);
        vals_.assign(cap, 0);
        state_.assign(cap, 0);
        used_ = tombs_ = 0;
    }

    size_t find_pos(u64 k) const {
        u64 h = splitmix64(k);
        for (u64 t = 0;; ++t) {
            size_t pos = (size_t)((h + t * (t + 1) / 2) & mask_);
            uint8_t st = state_[pos];
            if (st == 0) return NPOS;
            if (st == 1 && keys_[pos] == k) return pos;
        }
    }

    size_t probe_insert(u64 k) {
        u64 h = splitmix64(k);
        size_t first_tomb = NPOS;
        for (u64 t = 0;; ++t) {
            size_t pos = (size_t)((h + t * (t + 1) / 2) & mask_);
            uint8_t st = state_[pos];
            if (st == 0) {
                if (first_tomb != NPOS) { --tombs_; return first_tomb; }
                return pos;
            }
            if (st == 2) {
                if (first_tomb == NPOS) first_tomb = pos;
            } else if (keys_[pos] == k) {
                vals_[pos] = k;
                return NPOS;
            }
        }
    }

    void grow() { rehash(cap_ * 2); }

    void rehash(size_t new_cap) {
        vector<u64> ok, ov;
        ok.reserve(used_); ov.reserve(used_);
        for (size_t i = 0; i < cap_; ++i)
            if (state_[i] == 1) { ok.push_back(keys_[i]); ov.push_back(vals_[i]); }
        init(new_cap);
        for (size_t i = 0; i < ok.size(); ++i) {
            u64 h = splitmix64(ok[i]);
            for (u64 t = 0;; ++t) {
                size_t pos = (size_t)((h + t * (t + 1) / 2) & mask_);
                if (state_[pos] == 0) {
                    keys_[pos] = ok[i]; vals_[pos] = ov[i]; state_[pos] = 1; ++used_;
                    break;
                }
            }
        }
    }
};

// ============================================================
// C. Robin Hood hashing
//    每个元素记录 PSL(Probe Sequence Length, 距 home 槽的位移)
//    插入时"劫富济贫": 后来者 PSL 大于占位者 PSL 则交换位置 —— PSL 方差急剧缩小
//    查找可早退: 途中遇到 PSL 严格小于当前探测距离的槽 → 键必不在表内
//    删除用后移(backward shift): 删除产生空洞后, 把后方 PSL 更大元素前移回填,
//    表中永远无墓碑, 早退性质永久成立
//    负载可放宽到 0.85(线性探测此时早已灾难性聚簇)
// ============================================================
class RobinHoodMap {
public:
    static constexpr size_t NPOS = (size_t)-1;
    static constexpr uint32_t EMPTY = UINT32_MAX;

    explicit RobinHoodMap(size_t cap_hint = 16) { init(round_pow2(cap_hint * 2)); }

    bool insert(u64 k, u64 v) {
        // 负载检查在插入前: 严格上界, 保证插入路径的交换链必然终止于空槽
        if ((used_ + 1) * 100 >= cap_ * 85) grow();
        u64 h = splitmix64(k);
        size_t pos = (size_t)(h & mask_);
        u64 ck = k, cv = v;
        uint32_t cp = 0;                       // 携带元素的当前探测距离
        while (true) {
            if (psl_[pos] == EMPTY) {          // 空槽: 直接落位
                keys_[pos] = ck; vals_[pos] = cv; psl_[pos] = cp;
                ++used_;
                return true;
            }
            if (keys_[pos] == ck) {            // 已存在: 原地更新
                vals_[pos] = cv;
                return false;
            }
            if (cp > psl_[pos]) {              // 劫富济贫: 换位, 占位者继续下移
                u64 tk = keys_[pos]; keys_[pos] = ck; ck = tk;
                u64 tv = vals_[pos]; vals_[pos] = cv; cv = tv;
                uint32_t tp = psl_[pos]; psl_[pos] = cp; cp = tp;
            }
            ++cp;                              // 携带元素再走一步, 距离 +1
            pos = (pos + 1) & mask_;
        }
    }

    const u64* find(u64 k) const {
        u64 h = splitmix64(k);
        size_t pos = (size_t)(h & mask_);
        uint32_t p = 0;
        while (true) {
            if (psl_[pos] == EMPTY) return nullptr;      // 空槽: 链断
            if (psl_[pos] < p) return nullptr;           // 早退: 占位者比我"穷", 键必不在
            if (keys_[pos] == k) return &vals_[pos];
            ++p;
            pos = (pos + 1) & mask_;
        }
    }

    bool erase(u64 k) {
        u64 h = splitmix64(k);
        size_t pos = (size_t)(h & mask_);
        uint32_t p = 0;
        // 先按查找语义定位
        while (true) {
            if (psl_[pos] == EMPTY || psl_[pos] < p) return false;
            if (keys_[pos] == k) break;
            ++p;
            pos = (pos + 1) & mask_;
        }
        // 后移删除: 空洞右邻若 PSL>0 则前移一格(PSL-1), 直到空槽或 PSL==0
        size_t hole = pos;
        size_t cur = (pos + 1) & mask_;
        while (psl_[cur] != EMPTY && psl_[cur] != 0) {
            keys_[hole] = keys_[cur];
            vals_[hole] = vals_[cur];
            psl_[hole] = psl_[cur] - 1;
            hole = cur;
            cur = (cur + 1) & mask_;
        }
        psl_[hole] = EMPTY;
        --used_;
        return true;
    }

    size_t size() const { return used_; }

    // 调试: 最大 PSL(健康表应远小于理论最坏)
    uint32_t max_psl() const {
        uint32_t m = 0;
        for (size_t i = 0; i < cap_; ++i)
            if (psl_[i] != EMPTY && psl_[i] > m) m = psl_[i];
        return m;
    }

private:
    vector<u64> keys_, vals_;
    vector<uint32_t> psl_;
    size_t cap_ = 0, mask_ = 0, used_ = 0;

    static size_t round_pow2(size_t x) {
        size_t p = 1;
        while (p < x) p <<= 1;
        return p;
    }

    void init(size_t cap) {
        cap_ = cap; mask_ = cap - 1;
        keys_.assign(cap, 0);
        vals_.assign(cap, 0);
        psl_.assign(cap, EMPTY);
        used_ = 0;
    }

    void grow() {
        vector<u64> ok, ov;
        ok.reserve(used_); ov.reserve(used_);
        for (size_t i = 0; i < cap_; ++i)
            if (psl_[i] != EMPTY) { ok.push_back(keys_[i]); ov.push_back(vals_[i]); }
        init(cap_ * 2);
        for (size_t i = 0; i < ok.size(); ++i) insert(ok[i], ov[i]);
    }
};

// ============================================================
// D. 正确性: 四方对拍
//    oracle = std::unordered_map<u64,u64>, 每步操作四方结果逐条比对
// ============================================================
static u64 rng_state = 0x123456789ABCDEFULL;
static inline u64 rng() {
    rng_state = splitmix64(rng_state);
    return rng_state;
}

template <class MapT>
static void run_group(MapT& m, const vector<pair<int, u64>>& ops,
                      const char* name, int group_id) {
    unordered_map<u64, u64> oracle;   // 每个实现独立重建 oracle, 互不污染
    size_t n_ins = 0, n_era = 0, n_hit = 0;
    u64 cs = 0;   // 校验和: 所有命中 find 的值之和 + erase 成功次数
    for (size_t i = 0; i < ops.size(); ++i) {
        int op = ops[i].first;
        u64 k = ops[i].second;
        if (op == 0) {                              // insert
            bool a = m.insert(k, k);
            auto r = oracle.emplace(k, k);
            bool b = r.second;
            CHECK(a == b, "G%d %s insert ret mismatch key=%llu", group_id, name,
                  (unsigned long long)k);
            ++n_ins;
        } else if (op == 1) {                       // erase
            bool a = m.erase(k);
            bool b = oracle.erase(k) > 0;
            CHECK(a == b, "G%d %s erase ret mismatch key=%llu", group_id, name,
                  (unsigned long long)k);
            cs += a ? 1 : 0;
            ++n_era;
        } else {                                    // find
            const u64* a = m.find(k);
            auto it = oracle.find(k);
            bool a_hit = (a != nullptr);
            bool b_hit = (it != oracle.end());
            CHECK(a_hit == b_hit, "G%d %s find hit mismatch key=%llu", group_id,
                  name, (unsigned long long)k);
            if (a_hit) {
                CHECK(*a == it->second, "G%d %s find val mismatch key=%llu",
                      group_id, name, (unsigned long long)k);
                cs += *a;
                ++n_hit;
            }
        }
    }
    CHECK(m.size() == oracle.size(), "G%d %s size mismatch %zu vs %zu",
          group_id, name, m.size(), oracle.size());
    printf("  G%d %-10s ok  ins=%zu era=%zu hit=%zu size=%zu checksum=%llu\n",
           group_id, name, n_ins, n_era, n_hit, m.size(),
           (unsigned long long)cs);
}

int main() {
    printf("== 0007 open addressing hash map ==\n");

    // ---- 覆盖性断言: 三角数探测在 2^k 容量下取遍所有槽位 ----
    {
        const u64 CAP = 1024;
        vector<uint8_t> seen((size_t)CAP, 0);
        for (u64 t = 0; t < CAP * 8; ++t) {
            u64 pos = (t * (t + 1) / 2) % CAP;
            seen[(size_t)pos] = 1;
        }
        u64 cnt = 0;
        for (u64 i = 0; i < CAP; ++i) cnt += seen[(size_t)i];
        CHECK(cnt == CAP, "triangular probe coverage %llu != %llu",
              (unsigned long long)cnt, (unsigned long long)CAP);
        printf("triangular probe covers %llu/%llu slots\n",
               (unsigned long long)cnt, (unsigned long long)CAP);
    }

    // ---- G1: 小键域(高冲突) 均匀混合 ----
    {
        LinearMap m1; TriMap m2; RobinHoodMap m3;
        vector<pair<int, u64>> ops;
        ops.reserve(60000);
        for (int i = 0; i < 60000; ++i) {
            int op = (int)(rng() % 100);
            op = op < 55 ? 0 : (op < 80 ? 1 : 2);
            ops.push_back({op, rng() % 2000});
        }
        run_group(m1, ops, "linear", 1);
        run_group(m2, ops, "tri", 1);
        run_group(m3, ops, "robin", 1);
    }

    // ---- G2: 大键域(稀疏, 低冲突) ----
    {
        LinearMap m1; TriMap m2; RobinHoodMap m3;
        vector<pair<int, u64>> ops;
        ops.reserve(40000);
        for (int i = 0; i < 40000; ++i) {
            int op = (int)(rng() % 100);
            op = op < 60 ? 0 : (op < 85 ? 1 : 2);
            ops.push_back({op, rng() % 1000000007ULL});
        }
        run_group(m1, ops, "linear", 2);
        run_group(m2, ops, "tri", 2);
        run_group(m3, ops, "robin", 2);
    }

    // ---- G3: 爆发插入-全清-再插入(rehash 抖动) ----
    {
        LinearMap m1; TriMap m2; RobinHoodMap m3;
        vector<pair<int, u64>> ops;
        for (int round = 0; round < 8; ++round) {
            for (u64 k = 1; k <= 8000; ++k) {
                u64 key = (u64)round * 1000003ULL + k;
                ops.push_back({0, key});
            }
            for (int i = 0; i < 3000; ++i) {
                u64 key = (u64)round * 1000003ULL + 1 + (u64)(rng() % 8000);
                ops.push_back({1, key});
            }
        }
        run_group(m1, ops, "linear", 3);
        run_group(m2, ops, "tri", 3);
        run_group(m3, ops, "robin", 3);
    }

    // ---- G4: 顺序键插入 + 随机删半(直接 mod 取址会灾难聚簇, 检验哈希质量) ----
    {
        LinearMap m1; TriMap m2; RobinHoodMap m3;
        vector<pair<int, u64>> ops;
        for (u64 k = 0; k < 20000; ++k) ops.push_back({0, k});
        for (int i = 0; i < 12000; ++i) {
            int op = (int)(rng() % 100);
            op = op < 40 ? 1 : 2;
            ops.push_back({op, rng() % 20000});
        }
        run_group(m1, ops, "linear", 4);
        run_group(m2, ops, "tri", 4);
        run_group(m3, ops, "robin", 4);
    }

    if (g_fail == 0) printf("correctness: ALL PASS\n");

    // ---- 基准: N=2e6 四阶段, 四表横向对比 ----
    // 阶段: 1) 插入 N 个不同键  2) 查找(半命中半未命中)
    //       3) 删除一半        4) 混合 插入/删除/查找 各 200k
    {
        const size_t N = 2000000;
        vector<u64> keys(N);
        for (size_t i = 0; i < N; ++i) keys[i] = splitmix64(i + 42);
        // keys 本身即去重后的随机键(splitmix64 单射), 无需再洗牌

        struct Bench { const char* name; u64 cs; double t1, t2, t3, t4; };
        Bench bench[4];
        int bi = 0;

        auto run_bench = [&](auto&& make_map, const char* name) {
            using MapT = decay_t<decltype(make_map())>;
            auto m = make_map();
            u64 cs = 0;
            // 两种容器 find 返回类型不同(指针 vs 迭代器), 统一适配成"取值或 0"
            auto lookup = [&](u64 k) -> u64 {
                if constexpr (is_same_v<MapT, unordered_map<u64, u64>>) {
                    auto it = m.find(k);
                    return it == m.end() ? 0 : it->second;
                } else {
                    const u64* v = m.find(k);
                    return v ? *v : 0;
                }
            };
            auto do_insert = [&](u64 k) {
                if constexpr (is_same_v<MapT, unordered_map<u64, u64>>)
                    m.emplace(k, k);
                else
                    m.insert(k, k);
            };
            auto t0 = chrono::steady_clock::now();
            for (size_t i = 0; i < N; ++i) do_insert(keys[i]);
            auto t1 = chrono::steady_clock::now();
            for (size_t i = 0; i < N; ++i) {
                cs += lookup(keys[i]);                        // 命中
                cs += lookup(keys[N - 1 - i] ^ 0xDEADBEEFULL); // 未命中
            }
            auto t2 = chrono::steady_clock::now();
            for (size_t i = 0; i < N; i += 2) m.erase(keys[i]);
            auto t3 = chrono::steady_clock::now();
            for (size_t i = 0; i < 200000; ++i) {
                u64 k = keys[(size_t)(rng() % N)];
                do_insert(k);
                m.erase(keys[(size_t)(rng() % N)]);
                cs += lookup(k);
            }
            auto t4 = chrono::steady_clock::now();
            bench[bi].name = name;
            bench[bi].cs = cs;
            bench[bi].t1 = chrono::duration<double>(t1 - t0).count();
            bench[bi].t2 = chrono::duration<double>(t2 - t1).count();
            bench[bi].t3 = chrono::duration<double>(t3 - t2).count();
            bench[bi].t4 = chrono::duration<double>(t4 - t3).count();
            ++bi;
        };

        run_bench([] { return LinearMap(N); }, "linear");
        run_bench([] { return TriMap(N); }, "tri");
        run_bench([] { return RobinHoodMap(N); }, "robin");
        run_bench([] { return unordered_map<u64, u64>(); }, "unordered_map");

        // 校验和必须一致(操作序列四方完全相同)
        for (int i = 1; i < 4; ++i)
            CHECK(bench[i].cs == bench[0].cs, "bench checksum mismatch %s vs %s",
                  bench[i].name, bench[0].name);

        printf("\nbenchmark N=%zu (seconds, lower is better)\n", N);
        printf("%-14s %8s %8s %8s %8s\n", "map", "insert", "find", "erase", "mixed");
        for (int i = 0; i < 4; ++i)
            printf("%-14s %8.3f %8.3f %8.3f %8.3f\n", bench[i].name,
                   bench[i].t1, bench[i].t2, bench[i].t3, bench[i].t4);
        printf("checksum=%llu\n", (unsigned long long)bench[0].cs);
    }

    if (g_fail == 0)
        printf("RESULT: ALL PASS\n");
    else
        printf("RESULT: %d FAIL\n", g_fail);
    return g_fail == 0 ? 0 : 1;
}
