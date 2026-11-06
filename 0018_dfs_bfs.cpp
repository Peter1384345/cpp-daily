// ============================================================
// 0018 · DFS / BFS 全解
//        连通块 · 双端队列 BFS(0-1 边权) · 双向 BFS · 迭代加深 · 剪枝三件套
// 考纲等级: [J]/[S]
//   [J] CSP-J 入门组：图的遍历、连通块、网格 BFS/DFS、回溯、简单剪枝
//   [S] CSP-S / NOIP：0-1 BFS（双端队列）、双向 BFS、迭代加深、最优性剪枝与记忆化
// 编译: g++ -O2 -std=c++17 -Wall -Wextra -o search 0018_dfs_bfs.cpp
// 运行: ./search    返回码 0 = 全部对拍通过；1 = 有检查点失败
//
// 结构:
//   A. Grid / BfsStat      网格与统计（dist / 入队次数 / 出队次数）
//   B. bfsMarkPush         入队即标记（标准 BFS，每点入队恰一次）
//      bfsMarkPop          出队才标记（常见错误写法，dist 仍正确但入队膨胀）
//   C. compBfs/compDfs/compDsu   连通块三方实现（BFS / 显式栈 DFS / 并查集）
//   D. zeroOneGrid         双端队列 BFS：进入墙格代价 1，否则 0（最少破墙数）
//      dijkstraGrid        优先队列 Dijkstra（对照）
//      bellmanGrid         逐轮松弛（独立 oracle，杜绝"两实现共享同一建模错误"）
//   E. bidirGrid           双向 BFS（按层扩展，取两侧层深之和的下界终止）
//   F. LockGraph           隐式状态图（转盘锁，mod^k 状态），单向 vs 双向规模对比
//   G. iddfs               迭代加深 DFS（对拍 BFS 最短步数，统计重复展开量）
//   H. 剪枝三件套           0/1 背包：朴素 / 最优性上界 / 记忆化 / 上界+记忆化
//   I. queensNaive/queensBit   N 皇后：可行性剪枝 + 位运算
//   J. G1-G9 对拍   B1-B5 基准
//
// 本期主要断言来源（全部由不变式推导，而非"跑出来是这样"）:
//   (1) BFS 入队即标记 ⇒ 入队次数 == 出队次数 == 可达格数
//   (2) 无向无权图上 |dist[u]-dist[v]| ≤ 1 对每条边成立
//   (3) 0-1 BFS 的 dist 必须同时满足 dist[s]=0 与全部边的三角不等式
//   (4) 连通块数 == 并查集合并后的根数；三实现的划分必须逐格一致（规范化编号后比较）
//   (5) 迭代加深给出的最小深度 == BFS 距离（完备性 + 最优性）
//   (6) 记忆化的 key 必须包含"决策位置 + 剩余容量"，缺一维即错
//   (7) 最优性剪枝用的上界必须是"合法上界"，否则会剪掉最优解
// ============================================================
#include <bits/stdc++.h>

// ---------------------------- 基础设施 ----------------------------
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
        if (g_fails <= 40) printf("  [FAIL] %s\n", what.c_str());
    }
}

static const int INF = 1000000000;
static const int DX[4] = {-1, 1, 0, 0};
static const int DY[4] = {0, 0, -1, 1};

// ============================ A. 网格 ============================
struct Grid {
    int n, m;
    std::vector<unsigned char> wall;   // 1 = 墙 / 障碍

    Grid() : n(0), m(0) {}
    Grid(int n_, int m_) : n(n_), m(m_), wall((size_t)n_ * (size_t)m_, 0) {}

    int id(int x, int y) const { return x * m + y; }
    bool inside(int x, int y) const { return x >= 0 && x < n && y >= 0 && y < m; }
    bool open(int x, int y) const { return inside(x, y) && wall[(size_t)(x * m + y)] == 0; }
    int cells() const { return n * m; }
};

static Grid makeRandomGrid(Rng& rng, int n, int m, int wallPct) {
    Grid g(n, m);
    for (int i = 0; i < n * m; ++i) g.wall[(size_t)i] = (rng.nextInt(100) < wallPct) ? 1 : 0;
    g.wall[(size_t)g.id(0, 0)] = 0;                 // 保证起终点可站
    g.wall[(size_t)g.id(n - 1, m - 1)] = 0;
    return g;
}

struct BfsStat {
    std::vector<int> dist;
    long long enq;    // 入队次数
    long long pops;   // 出队（含被判为陈旧而跳过）次数
    long long done;   // 真正处理过的结点数
    BfsStat() : enq(0), pops(0), done(0) {}
};

// ==================== B. 两种 BFS 标记时机 ====================
// 标准写法：入队前判 dist，入队时立刻写 dist。
// 不变式：每个可达格恰好入队一次 ⇒ enq == done == 可达格数。
static BfsStat bfsMarkPush(const Grid& g, int sx, int sy) {
    BfsStat r;
    r.dist.assign((size_t)g.cells(), -1);
    if (!g.open(sx, sy)) return r;
    std::vector<int> q;
    q.reserve((size_t)g.cells());
    int s = g.id(sx, sy);
    r.dist[(size_t)s] = 0;
    q.push_back(s);
    ++r.enq;
    for (size_t h = 0; h < q.size(); ++h) {
        int u = q[h];
        ++r.pops;
        ++r.done;
        int x = u / g.m, y = u % g.m;
        int du = r.dist[(size_t)u];
        for (int d = 0; d < 4; ++d) {
            int nx = x + DX[d], ny = y + DY[d];
            if (!g.open(nx, ny)) continue;
            int v = g.id(nx, ny);
            if (r.dist[(size_t)v] != -1) continue;
            r.dist[(size_t)v] = du + 1;
            q.push_back(v);
            ++r.enq;
        }
    }
    return r;
}

// 常见错误写法：出队才标记已访问。因为入队时无法用 done 判断（此时必为 false），
// 只能"无条件入队"，于是同一格会被多个父结点重复推入，靠出队时的 done 丢弃陈旧副本。
// 距离结果依然正确（同层父结点的 du 相同，写入值一致），但入队次数显著膨胀 ——
// 数值对拍抓不到，只能靠 enq/done 的计数断言（本期 G3）。
static BfsStat bfsMarkPop(const Grid& g, int sx, int sy) {
    BfsStat r;
    r.dist.assign((size_t)g.cells(), -1);
    if (!g.open(sx, sy)) return r;
    std::vector<char> done((size_t)g.cells(), 0);
    std::vector<int> q;
    q.reserve((size_t)g.cells() * 4);
    int s = g.id(sx, sy);
    r.dist[(size_t)s] = 0;
    q.push_back(s);
    ++r.enq;
    for (size_t h = 0; h < q.size(); ++h) {
        int u = q[h];
        ++r.pops;
        if (done[(size_t)u]) continue;      // 陈旧副本：已按更早（同层）的路径处理过
        done[(size_t)u] = 1;
        ++r.done;
        int x = u / g.m, y = u % g.m;
        int du = r.dist[(size_t)u];
        for (int d = 0; d < 4; ++d) {
            int nx = x + DX[d], ny = y + DY[d];
            if (!g.open(nx, ny)) continue;
            int v = g.id(nx, ny);
            if (done[(size_t)v]) continue;
            r.dist[(size_t)v] = du + 1;
            q.push_back(v);
            ++r.enq;
        }
    }
    return r;
}

// ==================== C. 连通块三方实现 ====================
static int compBfs(const Grid& g, std::vector<int>& lab) {
    const int N = g.cells();
    lab.assign((size_t)N, -1);
    std::vector<int> q;
    int cnt = 0;
    for (int s = 0; s < N; ++s) {
        if (g.wall[(size_t)s] || lab[(size_t)s] != -1) continue;
        q.clear();
        q.push_back(s);
        lab[(size_t)s] = cnt;
        for (size_t h = 0; h < q.size(); ++h) {
            int u = q[h];
            int x = u / g.m, y = u % g.m;
            for (int d = 0; d < 4; ++d) {
                int nx = x + DX[d], ny = y + DY[d];
                if (!g.inside(nx, ny)) continue;
                int v = g.id(nx, ny);
                if (g.wall[(size_t)v] || lab[(size_t)v] != -1) continue;
                lab[(size_t)v] = cnt;
                q.push_back(v);
            }
        }
        ++cnt;
    }
    return cnt;
}

// 显式栈 DFS：n×m 可达 4e6，递归版在链状迷宫里必爆栈（0013 教训的同类问题）
static int compDfs(const Grid& g, std::vector<int>& lab, long long& pushes) {
    const int N = g.cells();
    lab.assign((size_t)N, -1);
    std::vector<int> stk;
    int cnt = 0;
    pushes = 0;
    for (int s = 0; s < N; ++s) {
        if (g.wall[(size_t)s] || lab[(size_t)s] != -1) continue;
        stk.clear();
        stk.push_back(s);
        lab[(size_t)s] = cnt;
        ++pushes;
        while (!stk.empty()) {
            int u = stk.back();
            stk.pop_back();
            int x = u / g.m, y = u % g.m;
            for (int d = 0; d < 4; ++d) {
                int nx = x + DX[d], ny = y + DY[d];
                if (!g.inside(nx, ny)) continue;
                int v = g.id(nx, ny);
                if (g.wall[(size_t)v] || lab[(size_t)v] != -1) continue;
                lab[(size_t)v] = cnt;
                stk.push_back(v);
                ++pushes;
            }
        }
        ++cnt;
    }
    return cnt;
}

struct Dsu {
    std::vector<int> p, sz;
    void init(int n) {
        p.resize((size_t)n);
        sz.assign((size_t)n, 1);
        for (int i = 0; i < n; ++i) p[(size_t)i] = i;
    }
    int find(int x) {
        while (p[(size_t)x] != x) {
            p[(size_t)x] = p[(size_t)p[(size_t)x]];   // 路径减半
            x = p[(size_t)x];
        }
        return x;
    }
    bool unite(int a, int b) {
        a = find(a);
        b = find(b);
        if (a == b) return false;
        if (sz[(size_t)a] < sz[(size_t)b]) std::swap(a, b);
        p[(size_t)b] = a;
        sz[(size_t)a] += sz[(size_t)b];
        return true;
    }
};

static int compDsu(const Grid& g, std::vector<int>& lab) {
    const int N = g.cells();
    const int m = g.m;
    Dsu d;
    d.init(N);
    for (int x = 0; x < g.n; ++x) {
        for (int y = 0; y < m; ++y) {
            int u = x * m + y;
            if (g.wall[(size_t)u]) continue;
            if (x + 1 < g.n && !g.wall[(size_t)((x + 1) * m + y)]) d.unite(u, (x + 1) * m + y);
            if (y + 1 < m && !g.wall[(size_t)(x * m + y + 1)]) d.unite(u, x * m + y + 1);
        }
    }
    lab.assign((size_t)N, -1);
    std::vector<int> mp((size_t)N, -1);
    int cnt = 0;
    for (int i = 0; i < N; ++i) {
        if (g.wall[(size_t)i]) continue;
        int rt = d.find(i);
        if (mp[(size_t)rt] < 0) mp[(size_t)rt] = cnt++;
        lab[(size_t)i] = mp[(size_t)rt];
    }
    return cnt;
}

// 把划分编号规范化（按扫描序重编号），使不同实现的编号可直接逐格比较
static std::vector<int> canonicalLabels(const std::vector<int>& lab, int cnt) {
    std::vector<int> mp((size_t)cnt, -1), out(lab.size(), -1);
    int nxt = 0;
    for (size_t i = 0; i < lab.size(); ++i) {
        if (lab[i] < 0) continue;
        if (mp[(size_t)lab[i]] < 0) mp[(size_t)lab[i]] = nxt++;
        out[i] = mp[(size_t)lab[i]];
    }
    return out;
}

// ============ D. 0-1 BFS（双端队列）与两种独立 oracle ============
// 语义：进入墙格代价 1（需要破墙），进入空格代价 0。求最少破墙数。
// 关键：代价 0 的松弛放队首，代价 1 的放队尾 —— 队列因此始终保持"距离单调"。
static std::vector<int> zeroOneGrid(const Grid& g, int sx, int sy, long long& relax) {
    const int N = g.cells();
    std::vector<int> dist((size_t)N, INF);
    relax = 0;
    if (!g.inside(sx, sy)) return dist;
    std::deque<int> dq;
    int s = g.id(sx, sy);
    dist[(size_t)s] = 0;
    dq.push_back(s);
    while (!dq.empty()) {
        int u = dq.front();
        dq.pop_front();
        int du = dist[(size_t)u];
        int x = u / g.m, y = u % g.m;
        for (int d = 0; d < 4; ++d) {
            int nx = x + DX[d], ny = y + DY[d];
            if (!g.inside(nx, ny)) continue;
            int v = g.id(nx, ny);
            int w = g.wall[(size_t)v] ? 1 : 0;
            if (du + w < dist[(size_t)v]) {
                dist[(size_t)v] = du + w;
                ++relax;
                if (w == 0) dq.push_front(v);
                else dq.push_back(v);
            }
        }
    }
    return dist;
}

// 错误示范：0/1 权图上用普通 FIFO 队列 + "出队即定稿"。
// FIFO 不保证出队顺序按距离单调（0 权边会把小距离结点压到队尾），
// 一旦某点被提前定稿，后续更短路径无法回写 → 距离偏大。
static std::vector<int> zeroOneFifo(const Grid& g, int sx, int sy) {
    const int N = g.cells();
    std::vector<int> dist((size_t)N, INF);
    if (!g.inside(sx, sy)) return dist;
    std::vector<char> done((size_t)N, 0);
    std::vector<int> q;
    int s = g.id(sx, sy);
    dist[(size_t)s] = 0;
    q.push_back(s);
    for (size_t h = 0; h < q.size(); ++h) {
        int u = q[h];
        if (done[(size_t)u]) continue;
        done[(size_t)u] = 1;
        int du = dist[(size_t)u];
        int x = u / g.m, y = u % g.m;
        for (int d = 0; d < 4; ++d) {
            int nx = x + DX[d], ny = y + DY[d];
            if (!g.inside(nx, ny)) continue;
            int v = g.id(nx, ny);
            if (done[(size_t)v]) continue;
            int w = g.wall[(size_t)v] ? 1 : 0;
            if (du + w < dist[(size_t)v]) {
                dist[(size_t)v] = du + w;
                q.push_back(v);
            }
        }
    }
    return dist;
}

static std::vector<int> dijkstraGrid(const Grid& g, int sx, int sy, long long& pops) {
    const int N = g.cells();
    std::vector<int> dist((size_t)N, INF);
    pops = 0;
    if (!g.inside(sx, sy)) return dist;
    typedef std::pair<int, int> PII;
    std::priority_queue<PII, std::vector<PII>, std::greater<PII> > pq;
    int s = g.id(sx, sy);
    dist[(size_t)s] = 0;
    pq.push(PII(0, s));
    while (!pq.empty()) {
        PII top = pq.top();
        pq.pop();
        int du = top.first, u = top.second;
        if (du != dist[(size_t)u]) continue;      // 陈旧条目
        ++pops;
        int x = u / g.m, y = u % g.m;
        for (int d = 0; d < 4; ++d) {
            int nx = x + DX[d], ny = y + DY[d];
            if (!g.inside(nx, ny)) continue;
            int v = g.id(nx, ny);
            int w = g.wall[(size_t)v] ? 1 : 0;
            if (du + w < dist[(size_t)v]) {
                dist[(size_t)v] = du + w;
                pq.push(PII(du + w, v));
            }
        }
    }
    return dist;
}

// 独立 oracle：逐轮全边松弛，直至无更新。O(VE)，只用于小图。
// wallCost = false → 单位权（每步 1，用于对拍普通 BFS）；
// wallCost = true  → 进入墙格代价 1、否则 0（用于对拍 0-1 BFS）。
// 注意：两者不能合并成"墙格才付 1、否则 0"，否则单位权情形会退化成全 0 权。
static std::vector<int> bellmanGrid(const Grid& g, int sx, int sy, bool wallCost) {
    const int N = g.cells();
    std::vector<int> dist((size_t)N, INF);
    if (!g.inside(sx, sy)) return dist;
    dist[(size_t)g.id(sx, sy)] = 0;
    for (int round = 0; round < N; ++round) {
        bool changed = false;
        for (int x = 0; x < g.n; ++x) {
            for (int y = 0; y < g.m; ++y) {
                int u = g.id(x, y);
                if (dist[(size_t)u] == INF) continue;
                for (int d = 0; d < 4; ++d) {
                    int nx = x + DX[d], ny = y + DY[d];
                    if (!g.inside(nx, ny)) continue;
                    int v = g.id(nx, ny);
                    if (!wallCost && g.wall[(size_t)v]) continue;   // 单位权：墙不可通行
                    int w = wallCost ? (g.wall[(size_t)v] ? 1 : 0) : 1;
                    if (dist[(size_t)u] + w < dist[(size_t)v]) {
                        dist[(size_t)v] = dist[(size_t)u] + w;
                        changed = true;
                    }
                }
            }
        }
        if (!changed) break;
    }
    return dist;
}

// ==================== E. 网格双向 BFS ====================
// 每次扩展"较小前沿"的整整一层；da/db 记录两侧层深。
// 终止：两侧层深之和已不可能改进 best（任一未发现路径长度 ≥ depA+depB+1）。
static int bidirGrid(const Grid& g, int sx, int sy, int tx, int ty, long long& expanded) {
    expanded = 0;
    if (!g.open(sx, sy) || !g.open(tx, ty)) return -1;
    if (sx == tx && sy == ty) return 0;
    const int N = g.cells();
    std::vector<int> da((size_t)N, -1), db((size_t)N, -1);
    std::vector<int> fa, fb, nxt;
    int s = g.id(sx, sy), t = g.id(tx, ty);
    fa.push_back(s);
    da[(size_t)s] = 0;
    fb.push_back(t);
    db[(size_t)t] = 0;
    int depA = 0, depB = 0;
    int best = INF;
    while (!fa.empty() && !fb.empty() && depA + depB + 1 < best) {
        bool fromA = fa.size() <= fb.size();
        nxt.clear();
        if (fromA) {
            for (size_t i = 0; i < fa.size(); ++i) {
                int u = fa[i];
                ++expanded;
                int x = u / g.m, y = u % g.m;
                for (int d = 0; d < 4; ++d) {
                    int nx = x + DX[d], ny = y + DY[d];
                    if (!g.open(nx, ny)) continue;
                    int v = g.id(nx, ny);
                    if (da[(size_t)v] != -1) continue;
                    da[(size_t)v] = depA + 1;
                    nxt.push_back(v);
                    if (db[(size_t)v] != -1) best = std::min(best, da[(size_t)v] + db[(size_t)v]);
                }
            }
            fa.swap(nxt);
            ++depA;
        } else {
            for (size_t i = 0; i < fb.size(); ++i) {
                int u = fb[i];
                ++expanded;
                int x = u / g.m, y = u % g.m;
                for (int d = 0; d < 4; ++d) {
                    int nx = x + DX[d], ny = y + DY[d];
                    if (!g.open(nx, ny)) continue;
                    int v = g.id(nx, ny);
                    if (db[(size_t)v] != -1) continue;
                    db[(size_t)v] = depB + 1;
                    nxt.push_back(v);
                    if (da[(size_t)v] != -1) best = std::min(best, db[(size_t)v] + da[(size_t)v]);
                }
            }
            fb.swap(nxt);
            ++depB;
        }
    }
    return best == INF ? -1 : best;
}

// ==================== F. 隐式状态图（转盘锁） ====================
// 状态 = digits 位、每位 mod 进制的数；一次操作把某一位 +1 或 -1（循环）。
// 这是"状态空间 BFS"的最小可运行模型：分支因子 2*digits，直径 digits*mod/2。
struct LockGraph {
    int digits, mod, total;
    std::vector<unsigned char> blocked;
    std::vector<int> pw;

    LockGraph(int d, int m) : digits(d), mod(m), total(1) {
        pw.assign((size_t)digits, 1);
        for (int i = 1; i < digits; ++i) pw[(size_t)i] = pw[(size_t)i - 1] * mod;
        for (int i = 0; i < digits; ++i) total *= mod;
        blocked.assign((size_t)total, 0);
    }

    int stateCount() const { return total; }

    int neighborCount(int s, int* out) const {
        int cnt = 0;
        for (int p = 0; p < digits; ++p) {
            int base = (s / pw[(size_t)p]) % mod;
            for (int step = 0; step < 2; ++step) {
                int delta = (step == 0) ? 1 : -1;
                int nb = (base + delta + mod) % mod;
                int t = s + (nb - base) * pw[(size_t)p];
                if (!blocked[(size_t)t]) out[cnt++] = t;
            }
        }
        return cnt;
    }
};

static std::vector<int> lockBfs(const LockGraph& g, int s, long long& expanded) {
    std::vector<int> dist((size_t)g.stateCount(), -1);
    std::vector<int> q;
    q.reserve((size_t)g.stateCount());
    expanded = 0;
    if (g.blocked[(size_t)s]) return dist;
    dist[(size_t)s] = 0;
    q.push_back(s);
    int buf[64];
    for (size_t h = 0; h < q.size(); ++h) {
        int u = q[h];
        ++expanded;
        int c = g.neighborCount(u, buf);
        for (int k = 0; k < c; ++k) {
            int v = buf[k];
            if (dist[(size_t)v] != -1) continue;
            dist[(size_t)v] = dist[(size_t)u] + 1;
            q.push_back(v);
        }
    }
    return dist;
}

static int lockBidir(const LockGraph& g, int s, int t, long long& expanded) {
    expanded = 0;
    if (s == t) return 0;
    if (g.blocked[(size_t)s] || g.blocked[(size_t)t]) return -1;
    const int N = g.stateCount();
    std::vector<int> da((size_t)N, -1), db((size_t)N, -1);
    std::vector<int> fa, fb, nxt;
    fa.push_back(s);
    da[(size_t)s] = 0;
    fb.push_back(t);
    db[(size_t)t] = 0;
    int depA = 0, depB = 0, best = INF;
    int buf[64];
    while (!fa.empty() && !fb.empty() && depA + depB + 1 < best) {
        bool fromA = fa.size() <= fb.size();
        nxt.clear();
        const std::vector<int>& cur = fromA ? fa : fb;
        std::vector<int>& ownDist = fromA ? da : db;
        std::vector<int>& otherDist = fromA ? db : da;
        int myDep = fromA ? depA : depB;
        for (size_t i = 0; i < cur.size(); ++i) {
            int u = cur[i];
            ++expanded;
            int c = g.neighborCount(u, buf);
            for (int k = 0; k < c; ++k) {
                int v = buf[k];
                if (ownDist[(size_t)v] != -1) continue;
                ownDist[(size_t)v] = myDep + 1;
                nxt.push_back(v);
                if (otherDist[(size_t)v] != -1)
                    best = std::min(best, ownDist[(size_t)v] + otherDist[(size_t)v]);
            }
        }
        if (fromA) {
            fa.swap(nxt);
            ++depA;
        } else {
            fb.swap(nxt);
            ++depB;
        }
    }
    return best == INF ? -1 : best;
}

// ==================== G. 迭代加深 DFS ====================
// 空间 O(depth)，时间 O(b^depth)。对"深度未知但答案很浅"的问题，
// 牺牲重复展开换取空间与"第一条解即最优"的性质。
static bool iddfsRec(const Grid& g, int x, int y, int tx, int ty, int depth,
                     std::vector<char>& onPath, long long& nodes) {
    ++nodes;
    if (x == tx && y == ty) return true;
    if (depth == 0) return false;
    for (int d = 0; d < 4; ++d) {
        int nx = x + DX[d], ny = y + DY[d];
        if (!g.open(nx, ny)) continue;
        int v = g.id(nx, ny);
        if (onPath[(size_t)v]) continue;          // 路径内剪枝：不走回头路
        onPath[(size_t)v] = 1;
        if (iddfsRec(g, nx, ny, tx, ty, depth - 1, onPath, nodes)) return true;
        onPath[(size_t)v] = 0;                    // 回溯：恢复现场
    }
    return false;
}

static int iddfs(const Grid& g, int sx, int sy, int tx, int ty, int maxDepth, long long& nodes) {
    nodes = 0;
    if (!g.open(sx, sy) || !g.open(tx, ty)) return -1;
    std::vector<char> onPath((size_t)g.cells(), 0);
    onPath[(size_t)g.id(sx, sy)] = 1;
    for (int lim = 0; lim <= maxDepth; ++lim) {
        if (iddfsRec(g, sx, sy, tx, ty, lim, onPath, nodes)) return lim;
    }
    return -1;
}

// ==================== H. 剪枝三件套（0/1 背包） ====================
struct Item {
    int w, v;
};

struct KnapStat {
    long long nodes;
    KnapStat() : nodes(0) {}
};

// 分数背包上界（整数版，避免浮点误差）：整件取走，最后一件按比例取整。
// 因为允许"切分物品"，任何 0/1 方案的价值都不可能超过它 —— 这是合法上界。
static long long fracBound(const std::vector<Item>& it, int i, int cap) {
    long long val = 0;
    int rem = cap;
    for (int k = i; k < (int)it.size() && rem > 0; ++k) {
        if (it[k].w <= rem) {
            val += it[k].v;
            rem -= it[k].w;
        } else {
            val += (long long)it[k].v * (long long)rem / (long long)it[k].w;
            rem = 0;
        }
    }
    return val;
}

static long long knapDp(const std::vector<Item>& it, int cap) {
    std::vector<long long> dp((size_t)cap + 1, 0);
    for (size_t k = 0; k < it.size(); ++k) {
        for (int c = cap; c >= it[k].w; --c) {
            long long cand = dp[(size_t)(c - it[k].w)] + it[k].v;
            if (cand > dp[(size_t)c]) dp[(size_t)c] = cand;
        }
    }
    return dp[(size_t)cap];
}

// H1 朴素 DFS：无任何剪枝，2^n 个叶子的完整搜索树
static long long knapPlain(const std::vector<Item>& it, int i, int cap, KnapStat& st) {
    ++st.nodes;
    if (i == (int)it.size() || cap == 0) return 0;
    long long best = knapPlain(it, i + 1, cap, st);
    if (it[(size_t)i].w <= cap) {
        long long t = it[(size_t)i].v + knapPlain(it, i + 1, cap - it[(size_t)i].w, st);
        if (t > best) best = t;
    }
    return best;
}

// H2 可行性 + 最优性剪枝：当前价值 + 上界 ≤ 已知最优 ⇒ 整棵子树不可能更好
static void knapBound(const std::vector<Item>& it, int i, int cap, long long cur,
                      long long& best, KnapStat& st) {
    ++st.nodes;
    if (cur > best) best = cur;                       // 前缀本身即一个可行解
    if (i == (int)it.size() || cap == 0) return;
    if (cur + fracBound(it, i, cap) <= best) return;  // 最优性剪枝（合法上界）
    if (it[(size_t)i].w <= cap)
        knapBound(it, i + 1, cap - it[(size_t)i].w, cur + it[(size_t)i].v, best, st);
    knapBound(it, i + 1, cap, cur, best, st);
}

// H3 记忆化：key = (决策位置 i, 剩余容量 cap) —— 两维缺一不可
static long long knapMemo(const std::vector<Item>& it, int i, int cap,
                          std::vector<long long>& memo, int W, KnapStat& st) {
    ++st.nodes;
    if (i == (int)it.size() || cap == 0) return 0;
    long long& slot = memo[(size_t)i * (size_t)(W + 1) + (size_t)cap];
    if (slot >= 0) return slot;
    long long best = knapMemo(it, i + 1, cap, memo, W, st);
    if (it[(size_t)i].w <= cap) {
        long long t = it[(size_t)i].v + knapMemo(it, i + 1, cap - it[(size_t)i].w, memo, W, st);
        if (t > best) best = t;
    }
    slot = best;
    return best;
}

// H4 上界 + 记忆化：与 H3 的差别是"上界只与本子问题已得最优比较"（局部剪枝），
// 因此记忆值仍是精确最优。若把全局 best 参与剪枝再写入 memo，memo 里存的就是
// "被外部最优解压扁过的上界"，跨上下文复用即出错（见讲义坑 #6）。
static long long knapBoundMemo(const std::vector<Item>& it, int i, int cap,
                               std::vector<long long>& memo, int W, KnapStat& st) {
    ++st.nodes;
    if (i == (int)it.size() || cap == 0) return 0;
    long long& slot = memo[(size_t)i * (size_t)(W + 1) + (size_t)cap];
    if (slot >= 0) return slot;
    long long best = 0;
    if (it[(size_t)i].w <= cap)
        best = it[(size_t)i].v + knapBoundMemo(it, i + 1, cap - it[(size_t)i].w, memo, W, st);
    if (fracBound(it, i + 1, cap) > best)
        best = std::max(best, knapBoundMemo(it, i + 1, cap, memo, W, st));
    slot = best;
    return best;
}

// ==================== I. N 皇后 ====================
// 两种度量必须分开记：
//   nodes  = 搜索树结点数（= 递归调用次数），两种写法完全相同
//   probes = 候选枚举总量（朴素每结点 n 次；位运算只枚举可用位）
// 位运算省的是"每结点的工作量"，不是"搜索树规模"——本期 G9 的实测结论。
struct QueenStat {
    long long nodes;
    long long probes;
    QueenStat() : nodes(0), probes(0) {}
};

static bool queensOk(const std::vector<int>& pos, int row, int col) {
    for (int r = 0; r < row; ++r) {
        int c = pos[(size_t)r];
        if (c == col || std::abs(c - col) == row - r) return false;
    }
    return true;
}

static long long queensNaive(int n, int row, std::vector<int>& pos, QueenStat& st) {
    ++st.nodes;
    st.probes += n;                       // 逐列试，不管列是否被占
    if (row == n) return 1;
    long long cnt = 0;
    for (int c = 0; c < n; ++c) {
        if (!queensOk(pos, row, c)) continue;          // 可行性剪枝
        pos[(size_t)row] = c;
        cnt += queensNaive(n, row + 1, pos, st);
    }
    return cnt;
}

// 位运算版：三个掩码同时表达"列 / 主对角 / 副对角"占用，一次 & 拿到全部可行列
static long long queensBit(int n, int row, int cols, int d1, int d2, QueenStat& st) {
    ++st.nodes;
    if (row == n) return 1;
    long long cnt = 0;
    int mask = (1 << n) - 1;
    int avail = mask & ~(cols | d1 | d2);
    st.probes += __builtin_popcount((unsigned)avail);
    while (avail) {
        int bit = avail & (-avail);
        avail -= bit;
        cnt += queensBit(n, row + 1, cols | bit, (d1 | bit) << 1, (d2 | bit) >> 1, st);
    }
    return cnt;
}

static long long queensByBit(int n, QueenStat& st) {
    if (n <= 0) return 0;
    if (n > 20) return -1;            // 位宽保护
    return queensBit(n, 0, 0, 0, 0, st);
}

static long long queensByNaive(int n, QueenStat& st) {
    std::vector<int> pos((size_t)std::max(n, 1), 0);
    return queensNaive(n, 0, pos, st);
}

// ============================ J. 对拍 ============================
// 不同实现对"不可达"的约定不同（BFS 用 -1，最短路类用 INF），
// 比较前必须统一口径 —— 否则测试会因为表示差异而假失败（本期首轮即踩到）。
static std::vector<int> normInf(const std::vector<int>& d) {
    std::vector<int> out(d);
    for (size_t i = 0; i < out.size(); ++i)
        if (out[i] == INF) out[i] = -1;
    return out;
}

// G1 连通块三方一致（BFS / 显式栈 DFS / 并查集），且划分逐格相同
static void testG1() {
    printf("[G1] 连通块三方对拍\n");
    Rng rng(18001ULL);
    int shapes[6][3] = {{1, 1, 0}, {3, 4, 20}, {5, 5, 35}, {8, 3, 45}, {12, 9, 25}, {20, 20, 40}};
    for (int t = 0; t < 6; ++t) {
        for (int rep = 0; rep < 6; ++rep) {
            Grid g = makeRandomGrid(rng, shapes[t][0], shapes[t][1], shapes[t][2]);
            std::vector<int> l1, l2, l3;
            int c1 = compBfs(g, l1);
            long long pushes = 0;
            int c2 = compDfs(g, l2, pushes);
            int c3 = compDsu(g, l3);
            check(c1 == c2 && c2 == c3, "G1 连通块数三方相等");
            std::vector<int> k1 = canonicalLabels(l1, c1);
            std::vector<int> k2 = canonicalLabels(l2, c2);
            std::vector<int> k3 = canonicalLabels(l3, c3);
            check(k1 == k2, "G1 BFS 与 DFS 划分逐格一致");
            check(k1 == k3, "G1 BFS 与 DSU 划分逐格一致");
            long long freeCells = 0;
            for (int i = 0; i < g.cells(); ++i) if (!g.wall[(size_t)i]) ++freeCells;
            long long sumSizes = 0;
            std::vector<long long> sz((size_t)c1, 0);
            for (int i = 0; i < g.cells(); ++i)
                if (k1[(size_t)i] >= 0) ++sz[(size_t)k1[(size_t)i]];
            for (int i = 0; i < c1; ++i) sumSizes += sz[(size_t)i];
            check(sumSizes == freeCells, "G1 各块尺寸之和 == 空格数");
            check(pushes == freeCells, "G1 显式栈 DFS 每格恰好入栈一次");
        }
    }
    printf("     6 种形状 × 6 组随机网格，划分与计数全部一致\n");
}

// G2 BFS 距离对拍：入队标记 / 出队标记 / 逐轮松弛（三方）
static void testG2() {
    printf("[G2] 网格 BFS 距离三方对拍\n");
    Rng rng(18002ULL);
    int totalCells = 0;
    for (int t = 0; t < 40; ++t) {
        int n = 1 + rng.nextInt(9);
        int m = 1 + rng.nextInt(9);
        int pct = rng.nextInt(50);
        Grid g = makeRandomGrid(rng, n, m, pct);
        BfsStat a = bfsMarkPush(g, 0, 0);
        BfsStat b = bfsMarkPop(g, 0, 0);
        std::vector<int> c = bellmanGrid(g, 0, 0, false);
        check(a.dist == b.dist, "G2 入队标记 == 出队标记");
        check(a.dist == normInf(c), "G2 BFS == 逐轮松弛");
        check(a.enq == a.done, "G2 入队次数 == 处理结点数（每点仅入队一次）");
        check(b.enq >= b.done, "G2 出队标记的入队次数 ≥ 处理数");
        // 边约束：无向无权图上相邻两格距离差不超过 1
        long long badEdges = 0;
        for (int x = 0; x < g.n; ++x) {
            for (int y = 0; y < g.m; ++y) {
                int u = g.id(x, y);
                if (a.dist[(size_t)u] < 0) continue;
                for (int d = 0; d < 4; ++d) {
                    int nx = x + DX[d], ny = y + DY[d];
                    if (!g.open(nx, ny)) continue;
                    int v = g.id(nx, ny);
                    if (a.dist[(size_t)v] < 0) continue;
                    if (std::abs(a.dist[(size_t)u] - a.dist[(size_t)v]) > 1) ++badEdges;
                }
                ++totalCells;
            }
        }
        check(badEdges == 0, "G2 相邻格距离差 ≤ 1");
    }
    printf("     40 组随机网格，覆盖 %d 个可达格，边约束逐条校验\n", totalCells);
}

// G3 标记时机的工作量差异：数值全对，只有计数能区分
static void testG3() {
    printf("[G3] BFS 标记时机的工作量差异 + 0/1 权图上的定稿错误\n");
    Rng rng(18003ULL);
    Grid g = makeRandomGrid(rng, 40, 40, 20);
    BfsStat a = bfsMarkPush(g, 0, 0);
    BfsStat b = bfsMarkPop(g, 0, 0);
    check(a.dist == b.dist, "G3 两种标记方式距离完全一致");
    check(a.enq == a.done, "G3 入队标记：enq == done");
    check(b.enq > b.done, "G3 出队标记：enq > done（存在重复入队）");
    printf("     40x40 墙率 20%%：入队标记 enq=%lld，出队标记 enq=%lld（%.2fx），可达 %lld 格\n",
           a.enq, b.enq, (double)b.enq / (double)(a.enq ? a.enq : 1), a.done);

    // 同一张图改成 0/1 权：普通队列 + 出队定稿会得到偏大的距离
    int bad = 0, cases = 0;
    for (int t = 0; t < 30; ++t) {
        int n = 3 + rng.nextInt(8);
        int m = 3 + rng.nextInt(8);
        Grid h = makeRandomGrid(rng, n, m, 30 + rng.nextInt(30));
        long long relax = 0;
        std::vector<int> good = zeroOneGrid(h, 0, 0, relax);
        std::vector<int> fifo = zeroOneFifo(h, 0, 0);
        ++cases;
        bool diff = false;
        for (int i = 0; i < h.cells(); ++i) {
            if (good[(size_t)i] != fifo[(size_t)i]) {
                diff = true;
                break;
            }
        }
        if (diff) ++bad;
    }
    printf("     0/1 权图 %d 组中，普通队列+出队定稿有 %d 组距离偏大\n", cases, bad);
    check(bad > 0, "G3 普通队列上的出队定稿会产生错解（反例存在）");
}

// G4 0-1 BFS：双端队列 / Dijkstra / 逐轮松弛 三方一致 + 三角不等式
static void testG4() {
    printf("[G4] 0-1 BFS（最少破墙数）三方对拍\n");
    Rng rng(18004ULL);
    long long totalRelax = 0;
    for (int t = 0; t < 30; ++t) {
        int n = 2 + rng.nextInt(8);
        int m = 2 + rng.nextInt(8);
        Grid g = makeRandomGrid(rng, n, m, 20 + rng.nextInt(40));
        long long relax = 0, pops = 0;
        std::vector<int> d1 = zeroOneGrid(g, 0, 0, relax);
        std::vector<int> d2 = dijkstraGrid(g, 0, 0, pops);
        std::vector<int> d3 = bellmanGrid(g, 0, 0, true);
        check(d1 == d2, "G4 0-1 BFS == Dijkstra");
        check(d1 == d3, "G4 0-1 BFS == 逐轮松弛");
        check(d1[(size_t)g.id(0, 0)] == 0, "G4 源点距离为 0");
        totalRelax += relax;
        long long badEdges = 0;
        for (int x = 0; x < g.n; ++x) {
            for (int y = 0; y < g.m; ++y) {
                int u = g.id(x, y);
                if (d1[(size_t)u] == INF) continue;
                for (int d = 0; d < 4; ++d) {
                    int nx = x + DX[d], ny = y + DY[d];
                    if (!g.inside(nx, ny)) continue;
                    int v = g.id(nx, ny);
                    int w = g.wall[(size_t)v] ? 1 : 0;
                    // 反向边代价 = 进入 u 的代价
                    int wr = g.wall[(size_t)u] ? 1 : 0;
                    if (d1[(size_t)v] != INF) {
                        if (d1[(size_t)v] > d1[(size_t)u] + w) ++badEdges;
                        if (d1[(size_t)u] > d1[(size_t)v] + wr) ++badEdges;
                    }
                }
            }
        }
        check(badEdges == 0, "G4 全部边满足三角不等式");
    }
    printf("     30 组随机网格，累计松弛 %lld 次，三角不等式逐边校验\n", totalRelax);
}

// G5 双向 BFS 与单向 BFS 距离一致
static void testG5() {
    printf("[G5] 双向 BFS 对拍\n");
    Rng rng(18005ULL);
    long long expB = 0, expU = 0;
    int cases = 0;
    for (int t = 0; t < 40; ++t) {
        int n = 3 + rng.nextInt(12);
        int m = 3 + rng.nextInt(12);
        Grid g = makeRandomGrid(rng, n, m, 10 + rng.nextInt(30));
        BfsStat u = bfsMarkPush(g, 0, 0);
        long long e = 0;
        int bd = bidirGrid(g, 0, 0, n - 1, m - 1, e);
        int ud = u.dist[(size_t)g.id(n - 1, m - 1)];
        check(bd == ud, "G5 双向 BFS 距离 == 单向 BFS 距离");
        if (ud > 0) {
            expB += e;
            expU += u.done;
            ++cases;
        }
    }
    printf("     %d 组可达样本：双向展开 %lld 结点，单向展开 %lld 结点，比值 %.3f\n",
           cases, expB, expU, (double)expB / (double)(expU ? expU : 1));
}

// G6 隐式状态图：单向 vs 双向（正确性 + 规模）
static void testG6() {
    printf("[G6] 隐式状态图（转盘锁）单向 vs 双向\n");
    Rng rng(18006ULL);
    // 6.1 无障碍：此时距离有闭式解 —— 每位独立，距离 = Σ 环形差
    {
        LockGraph pure(4, 6);
        long long ex = 0;
        std::vector<int> d = lockBfs(pure, 0, ex);
        int far = 0;
        for (int i = 0; i < pure.stateCount(); ++i)
            if (d[(size_t)i] > far) far = d[(size_t)i];
        check(far == pure.digits * (pure.mod / 2), "G6 无障碍时最大距离 == digits*mod/2");
        // 最远状态 = 每位都转 mod/2 步；注意不是"全 5"（全 5 只需每位 1 步）
        int mid = (pure.mod / 2) * ((pure.stateCount() - 1) / (pure.mod - 1));
        check(d[(size_t)mid] == pure.digits * (pure.mod / 2), "G6 每位转 mod/2 步的距离 == 12");
        long long eb = 0;
        int bd = lockBidir(pure, 0, mid, eb);
        check(bd == pure.digits * (pure.mod / 2), "G6 无障碍时双向距离同样为 12");
    }
    // 6.2 随机障碍：双向 vs 单向（每个用例以 a 为源单独跑单向，才是同源 oracle）
    LockGraph g(4, 6);
    for (int i = 0; i < g.stateCount(); ++i)
        g.blocked[(size_t)i] = (rng.nextInt(100) < 8) ? 1 : 0;
    g.blocked[0] = 0;
    g.blocked[(size_t)(g.stateCount() - 1)] = 0;
    long long expU = 0;
    std::vector<int> d0 = lockBfs(g, 0, expU);
    check(d0[(size_t)(g.stateCount() - 1)] != -1, "G6 起终点连通（用例前提）");
    long long expB = 0, expUPair = 0;
    int pairs = 0;
    for (int t = 0; t < 60; ++t) {
        int a = rng.nextInt(g.stateCount());
        int b = rng.nextInt(g.stateCount());
        if (a == b) continue;
        if (g.blocked[(size_t)a] || g.blocked[(size_t)b]) continue;
        long long ea = 0;
        std::vector<int> da = lockBfs(g, a, ea);      // 同源单向 oracle
        long long eb = 0;
        int bd = lockBidir(g, a, b, eb);
        check(bd == da[(size_t)b], "G6 双向距离 == 同源单向距离");
        expB += eb;
        expUPair += ea;
        ++pairs;
    }
    printf("     状态数 %d（6^4），样本 %d 组：双向累计展开 %lld，同源单向累计展开 %lld（%.2fx）\n",
           g.stateCount(), pairs, expB, expUPair,
           (double)expUPair / (double)(expB ? expB : 1));
}

// G7 迭代加深：深度 == BFS 距离；重复展开量随深度指数增长
static void testG7() {
    printf("[G7] 迭代加深 DFS 对拍 BFS\n");
    Rng rng(18007ULL);
    for (int t = 0; t < 8; ++t) {
        Grid g = makeRandomGrid(rng, 6, 6, 15);
        BfsStat u = bfsMarkPush(g, 0, 0);
        int ud = u.dist[(size_t)g.id(5, 5)];
        long long nodes = 0;
        int dd = iddfs(g, 0, 0, 5, 5, 16, nodes);
        if (ud < 0) {
            check(dd == -1, "G7 不可达时迭代加深也返回 -1");
        } else {
            check(dd == ud, "G7 迭代加深深度 == BFS 距离");
        }
    }
    // 开网格上观察重复展开：同一目标，深度 d 与 d+1 的结点数
    Grid open(7, 7);
    BfsStat u = bfsMarkPush(open, 0, 0);
    int d = u.dist[(size_t)open.id(6, 6)];
    long long n1 = 0, n2 = 0;
    iddfs(open, 0, 0, 6, 5, 16, n1);          // 距离 11
    iddfs(open, 0, 0, 6, 6, 16, n2);          // 距离 12
    check(d == 12, "G7 7x7 对角距离为 12");
    check(n2 > n1, "G7 深度 +1 使展开结点数增加");
    check(n2 > (long long)open.cells() * 100, "G7 迭代加深展开量远超网格格数");
    printf("     7x7 开网格到 (6,6)：BFS 访问 %lld 格，迭代加深展开 %lld 结点（%.0fx）\n",
           u.done, n2, (double)n2 / (double)u.done);
}

// G8 背包四实现对拍 DP + 剪枝效果
static void testG8() {
    printf("[G8] 0/1 背包：朴素 / 上界 / 记忆化 / 上界+记忆化\n");
    Rng rng(18008ULL);
    long long sumPlain = 0, sumBound = 0, sumMemo = 0, sumBM = 0;
    bool strict = false;
    for (int t = 0; t < 60; ++t) {
        int n = 4 + rng.nextInt(9);
        int W = 10 + rng.nextInt(40);
        std::vector<Item> it((size_t)n);
        for (int i = 0; i < n; ++i) {
            it[(size_t)i].w = 1 + rng.nextInt(12);
            it[(size_t)i].v = it[(size_t)i].w * (1 + rng.nextInt(5));
        }
        std::sort(it.begin(), it.end(), [](const Item& a, const Item& b) {
            return (double)a.v / (double)a.w > (double)b.v / (double)b.w;
        });
        long long dp = knapDp(it, W);
        KnapStat s1, s2, s3, s4;
        long long r1 = knapPlain(it, 0, W, s1);
        long long r2 = 0;
        knapBound(it, 0, W, 0, r2, s2);
        std::vector<long long> memo((size_t)n * (size_t)(W + 1), -1);
        long long r3 = knapMemo(it, 0, W, memo, W, s3);
        std::vector<long long> memo2((size_t)n * (size_t)(W + 1), -1);
        long long r4 = knapBoundMemo(it, 0, W, memo2, W, s4);
        check(r1 == dp, "G8 朴素 DFS == DP");
        check(r2 == dp, "G8 上界剪枝 == DP");
        check(r3 == dp, "G8 记忆化 == DP");
        check(r4 == dp, "G8 上界+记忆化 == DP");
        check(s2.nodes <= s1.nodes, "G8 上界剪枝结点数 ≤ 朴素");
        check(s3.nodes <= s1.nodes, "G8 记忆化结点数 ≤ 朴素");
        check(s4.nodes <= s1.nodes, "G8 上界+记忆化结点数 ≤ 朴素");
        sumPlain += s1.nodes;
        sumBound += s2.nodes;
        sumMemo += s3.nodes;
        sumBM += s4.nodes;
        if (s2.nodes < s1.nodes || s3.nodes < s1.nodes) strict = true;
    }
    check(strict, "G8 至少一组出现严格剪枝效果");
    printf("     60 组：朴素 %lld 结点 / 上界 %lld (%.1f%%) / 记忆化 %lld (%.1f%%) / 合并 %lld (%.1f%%)\n",
           sumPlain, sumBound, 100.0 * (double)sumBound / (double)sumPlain,
           sumMemo, 100.0 * (double)sumMemo / (double)sumPlain,
           sumBM, 100.0 * (double)sumBM / (double)sumPlain);
}

// G9 N 皇后：与已知答案表比对 + 位运算的"结点数不变、工作量下降"
static void testG9() {
    printf("[G9] N 皇后：已知答案表 + 两种剪枝的结点/枚举量\n");
    const long long known[13] = {0, 1, 0, 0, 2, 10, 4, 40, 92, 352, 724, 2680, 14200};
    for (int n = 1; n <= 11; ++n) {
        QueenStat sb, sn;
        long long cb = queensByBit(n, sb);
        check(cb == known[n], "G9 位运算版与已知答案表一致");
        if (n <= 9) {
            long long cn = queensByNaive(n, sn);
            check(cn == known[n], "G9 朴素回溯与已知答案表一致");
            check(sb.nodes == sn.nodes, "G9 两种写法的搜索树结点数相同");
            check(sb.probes < sn.probes, "G9 位运算枚举量更小");
        }
    }
    QueenStat sb, sn;
    long long c8b = queensByBit(8, sb);
    long long c8n = queensByNaive(8, sn);
    check(c8b == 92 && c8n == 92, "G9 n=8 答案为 92");
    printf("     n=8：结点数 %lld/%lld（相同），候选枚举 %lld vs %lld（%.1fx 差距）\n",
           sb.nodes, sn.nodes, sb.probes, sn.probes,
           (double)sn.probes / (double)(sb.probes ? sb.probes : 1));
}

// ============================ 基准 ============================
static void benchB1() {
    const int n = 1200;
    Grid g(n, n);
    BfsStat a = bfsMarkPush(g, 0, 0);
    BfsStat b = bfsMarkPop(g, 0, 0);
    double t0 = nowMs();
    BfsStat a2 = bfsMarkPush(g, 0, 0);
    double t1 = nowMs();
    BfsStat b2 = bfsMarkPop(g, 0, 0);
    double t2 = nowMs();
    printf("[B1] 1200x1200 开网格 BFS | 入队标记 %.2f ms enq=%lld | 出队标记 %.2f ms enq=%lld (%.2fx) | 距离一致 %s\n",
           t1 - t0, a2.enq, t2 - t1, b2.enq,
           (double)b2.enq / (double)a2.enq, (a.dist == b.dist) ? "是" : "否");
    check(a2.dist == b2.dist, "B1 两种标记方式距离一致");
    check(a2.enq == (long long)n * n, "B1 开网格上每格恰好入队一次");
    check(b2.enq > a2.enq, "B1 出队标记产生重复入队");
}

static void benchB2() {
    const int n = 800;
    Rng rng(18102ULL);
    Grid g = makeRandomGrid(rng, n, n, 25);
    long long relax = 0, pops = 0;
    double t0 = nowMs();
    std::vector<int> d1 = zeroOneGrid(g, 0, 0, relax);
    double t1 = nowMs();
    std::vector<int> d2 = dijkstraGrid(g, 0, 0, pops);
    double t2 = nowMs();
    long long s1 = 0, s2 = 0;
    for (int i = 0; i < g.cells(); ++i) {
        if (d1[(size_t)i] < INF) s1 += d1[(size_t)i];
        if (d2[(size_t)i] < INF) s2 += d2[(size_t)i];
    }
    printf("[B2] 800x800 墙率25%% 最少破墙 | 0-1BFS %.2f ms 松弛 %lld | Dijkstra %.2f ms 出堆 %lld | 加速 %.2fx | 校验和 %lld/%lld\n",
           t1 - t0, relax, t2 - t1, pops, (t2 - t1) / (t1 - t0), s1, s2);
    check(s1 == s2, "B2 两种算法校验和相等");
}

static void benchB3() {
    const int digits = 7, mod = 6;
    Rng rng(18103ULL);
    LockGraph g(digits, mod);                 // 6^7 = 279936
    for (int i = 0; i < g.stateCount(); ++i)
        g.blocked[(size_t)i] = (rng.nextInt(100) < 5) ? 1 : 0;
    g.blocked[0] = 0;
    g.blocked[(size_t)(g.stateCount() - 1)] = 0;

    long long expU = 0;
    double t0 = nowMs();
    std::vector<int> d0 = lockBfs(g, 0, expU);
    double t1 = nowMs();

    // (a) 最远点：两侧搜索半径之和 ≈ 直径，球体已饱和 → 收益趋近于 1
    int far = (mod / 2) * ((g.stateCount() - 1) / (mod - 1));
    if (g.blocked[(size_t)far]) far = g.stateCount() - 1;
    long long expFar = 0;
    int dFar = lockBidir(g, 0, far, expFar);
    double t2 = nowMs();
    check(dFar == d0[(size_t)far], "B3 最远点：双向 == 单向");

    // (b) 随机点对：典型距离远小于直径，这才是双向 BFS 的收益区间
    long long sumU = 0, sumB = 0;
    int cnt = 0;
    for (int t = 0; t < 40; ++t) {
        int a = rng.nextInt(g.stateCount());
        int b = rng.nextInt(g.stateCount());
        if (a == b || g.blocked[(size_t)a] || g.blocked[(size_t)b]) continue;
        long long ea = 0, eb = 0;
        std::vector<int> da = lockBfs(g, a, ea);
        int bd = lockBidir(g, a, b, eb);
        check(bd == da[(size_t)b], "B3 随机点对：双向 == 单向");
        sumU += ea;
        sumB += eb;
        ++cnt;
    }
    printf("[B3] 转盘锁 6^%d=%d 状态 | 单源单向 %.2f ms 展开 %lld | 双向 %.2f ms\n",
           digits, g.stateCount(), t1 - t0, expU, t2 - t1);
    printf("     最远点 dist=%d：双向展开 %lld（占单向 %.1f%%）\n",
           dFar, expFar, 100.0 * (double)expFar / (double)(expU ? expU : 1));
    if (cnt > 0) {
        printf("     %d 组随机点对：单向均 %.0f，双向均 %.0f，比值 %.2f\n",
               cnt, (double)sumU / (double)cnt, (double)sumB / (double)cnt,
               (double)sumU / (double)(sumB ? sumB : 1));
    }
    check(cnt > 0, "B3 随机点对样本非空");
}

static void benchB4() {
    const int n = 40, W = 2000;
    Rng rng(18104ULL);
    std::vector<Item> it((size_t)n);
    for (int i = 0; i < n; ++i) {
        it[(size_t)i].w = 20 + rng.nextInt(160);
        it[(size_t)i].v = it[(size_t)i].w * (1 + rng.nextInt(4));
    }
    std::sort(it.begin(), it.end(), [](const Item& a, const Item& b) {
        return (double)a.v / (double)a.w > (double)b.v / (double)b.w;
    });
    long long dp = knapDp(it, W);

    KnapStat s2, s3, s4;
    long long r2 = 0;
    double t0 = nowMs();
    knapBound(it, 0, W, 0, r2, s2);
    double t1 = nowMs();
    std::vector<long long> m1((size_t)n * (size_t)(W + 1), -1);
    long long r3 = knapMemo(it, 0, W, m1, W, s3);
    double t2 = nowMs();
    std::vector<long long> m2((size_t)n * (size_t)(W + 1), -1);
    long long r4 = knapBoundMemo(it, 0, W, m2, W, s4);
    double t3 = nowMs();
    printf("[B4] n=%d W=%d | 上界 %.2f ms 结点 %lld | 记忆化 %.2f ms 结点 %lld | 合并 %.2f ms 结点 %lld | 答案 %lld/%lld/%lld/%lld\n",
           n, W, t1 - t0, s2.nodes, t2 - t1, s3.nodes, t3 - t2, s4.nodes, r2, r3, r4, dp);
    check(r2 == dp && r3 == dp && r4 == dp, "B4 三实现答案 == DP");
    check(s2.nodes < (1LL << 40), "B4 上界剪枝未退化为全搜索");

    // n=20 时朴素搜索可跑：给出"剪枝把指数压成多少"的直接读数
    const int n2 = 20;
    std::vector<Item> it2((size_t)n2);
    for (int i = 0; i < n2; ++i) {
        it2[(size_t)i].w = 20 + rng.nextInt(160);
        it2[(size_t)i].v = it2[(size_t)i].w * (1 + rng.nextInt(4));
    }
    std::sort(it2.begin(), it2.end(), [](const Item& a, const Item& b) {
        return (double)a.v / (double)a.w > (double)b.v / (double)b.w;
    });
    KnapStat s1, sb;
    long long q1 = knapPlain(it2, 0, W, s1);
    long long q2 = 0;
    knapBound(it2, 0, W, 0, q2, sb);
    printf("[B4b] n=%d W=%d | 朴素 %lld 结点 | 上界 %lld 结点 (%.3f%%) | 答案 %lld/%lld\n",
           n2, W, s1.nodes, sb.nodes, 100.0 * (double)sb.nodes / (double)s1.nodes, q1, q2);
    check(q1 == q2, "B4b 朴素 == 上界剪枝");
}

static void benchB5() {
    QueenStat sb;
    double t0 = nowMs();
    long long c12 = queensByBit(12, sb);
    double t1 = nowMs();
    QueenStat s8, s9;
    double t2 = nowMs();
    long long c8 = queensByNaive(8, s8);
    double t3 = nowMs();
    long long c9 = queensByNaive(9, s9);
    double t4 = nowMs();
    printf("[B5] N 皇后 | 位运算 n=12 %.1f ms 结点 %lld 枚举 %lld 方案 %lld | "
           "朴素 n=8 %.1f ms 枚举 %lld | 朴素 n=9 %.1f ms 枚举 %lld (%.2fx)\n",
           t1 - t0, sb.nodes, sb.probes, c12, t3 - t2, s8.probes, t4 - t3, s9.probes,
           (double)s9.probes / (double)(s8.probes ? s8.probes : 1));
    check(c12 == 14200, "B5 n=12 方案数 14200");
    check(c8 == 92, "B5 n=8 方案数 92");
    check(c9 == 352, "B5 n=9 方案数 352");
}

int main() {
    printf("=== 0018 DFS / BFS 全解（考纲 [J]/[S]）===\n");
    double t0 = nowMs();

    testG1();
    testG2();
    testG3();
    testG4();
    testG5();
    testG6();
    testG7();
    testG8();
    testG9();

    benchB1();
    benchB2();
    benchB3();
    benchB4();
    benchB5();

    double t1 = nowMs();
    printf("--- 检查点 %lld, 失败 %lld, 总耗时 %.1f ms ---\n", g_checks, g_fails, t1 - t0);
    if (g_fails == 0) {
        printf("RESULT: ALL PASS\n");
        return 0;
    }
    printf("RESULT: FAILED\n");
    return 1;
}
