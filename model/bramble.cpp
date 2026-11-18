// Bramble: a cycle-costed model of an FPGA SAT solver for the AgentSAT ECP5 target.
//
// It solves for real (CDCL + a concurrent local-search engine) while charging every step the clock cycles the
// planned hardware would spend on it, so architecture choices can be compared on the competition instances before
// any RTL exists. The cost model's constants are estimates; they will be checked against the RTL in Verilator.
//
// Hardware the model stands for:
//   * P clause partitions, each its own BRAM bank holding clause bodies and watch lists. When a literal becomes
//     false, every partition scans its own watch list for it at the same time; the step costs the slowest one.
//     A clause is placed in the partition whose watch lists for its two watched literals are shortest.
//   * A binary-implication unit beside them (binary clauses never touch the clause banks).
//   * Elastic partitioning: watch-list heads cost 2*nvars words per partition, so an instance with many variables
//     runs on fewer partitions instead of being rejected.
//   * VMTF decisions (O(1) list moves, no heap) in focused mode; optional EVSIDS heap in stable mode, charged per
//     heap level.
//   * A probSAT local-search engine running concurrently (critical variable kept as an XOR of true variables).
//     Phases flow both ways: CDCL can rephase from the walker's best assignment, the walker restarts from CDCL's.
//   * Tiered clause-database reduction by LBD (bucketed, no sort), forced early when the bank is full.
//
// Usage: bramble FILE.cnf [--P=8] [--mhz=50] [--limit=300] [--check] [--no-sls] [--stable=vsids|vmtf|off] ...
#include <algorithm>
#include <cassert>
#include <cinttypes>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

using u32 = uint32_t;
using u64 = uint64_t;
using i64 = int64_t;

// ------------------------------------------------------------------------------------------------ configuration
struct Config {
    int P = 8;                    // clause partitions (banks)
    int head_words = 65536;       // total watch-list head words across partitions (elastic partitioning)
    double mhz = 50.0;
    double limit_s = 300.0;
    bool check = false;           // RUP-check every learned clause (slow; debug)
    bool sls = true;              // concurrent local-search engine
    int stable = 1;               // 0 off (focused only), 1 VMTF in stable mode too, 2 EVSIDS heap in stable mode
    int pipe = 3;                 // cycles of pipeline latency per propagated literal
    int ports = 2;                // value reads per cycle per partition (dual-port BRAM)
    u64 seed = 1;
    long arena_words = 1 << 20;   // clause-bank capacity in literal slots (all partitions together), when bram=0
    int bram = 0;                 // entry BRAM budget in DP16KD blocks (0: unlimited); the ECP5-85F has 208, the SoC uses 25
    bool verbose = false;
    bool gauss = true;            // XOR recovery + Gauss-Jordan before search
    double vivify = 0.15;         // share of cycles for vivifying learned clauses (0: off)
    int gauss_width = 8;          // longest clause considered part of an XOR
    int gauss_word = 36;          // bits per row-XOR cycle (one DP16KD port at 36 bits)
};

static inline u32 lit_of(int dimacs) { return dimacs > 0 ? 2u * (dimacs - 1) : 2u * (-dimacs - 1) + 1; }
static inline int dimacs_of(u32 l) { return (l & 1) ? -(int)(l / 2 + 1) : (int)(l / 2 + 1); }
static inline u32 var_of(u32 l) { return l >> 1; }

struct Rng {  // xorshift64*: what an LFSR-ish hardware RNG would give
    u64 s;
    explicit Rng(u64 seed) : s(seed * 0x9E3779B97F4A7C15ull + 1) {}
    u64 next() { s ^= s >> 12; s ^= s << 25; s ^= s >> 27; return s * 2685821657736338717ull; }
    u32 below(u32 n) { return (u32)(next() % n); }
    double unit() { return (next() >> 11) * (1.0 / 9007199254740992.0); }
};

// ------------------------------------------------------------------------------------------------ formula
struct Formula {
    int nvars = 0;
    std::vector<std::vector<u32>> clauses;   // original clauses, literals in our encoding
    bool empty_clause = false;
};

static bool read_dimacs(const char* path, Formula& f) {
    FILE* fp = fopen(path, "r");
    if (!fp) return false;
    std::vector<u32> cur;
    int c;
    while ((c = fgetc(fp)) != EOF) {
        if (c == 'c' || c == 'p' || c == '%') {
            if (c == 'p') {
                int nv = 0, nc = 0;
                if (fscanf(fp, " cnf %d %d", &nv, &nc) == 2) f.nvars = nv;
            }
            while (c != '\n' && c != EOF) c = fgetc(fp);
            continue;
        }
        if (c == '-' || (c >= '0' && c <= '9')) {
            ungetc(c, fp);
            int x;
            if (fscanf(fp, "%d", &x) != 1) break;
            if (x == 0) {
                // drop duplicate literals; keep tautologies out (they are always satisfied)
                std::sort(cur.begin(), cur.end());
                cur.erase(std::unique(cur.begin(), cur.end()), cur.end());
                bool taut = false;
                for (size_t i = 1; i < cur.size(); i++) if ((cur[i] ^ 1) == cur[i - 1]) taut = true;
                if (cur.empty()) f.empty_clause = true;
                if (!taut) f.clauses.push_back(cur);
                cur.clear();
            } else {
                if (abs(x) > f.nvars) f.nvars = abs(x);
                cur.push_back(lit_of(x));
            }
        }
    }
    fclose(fp);
    return true;
}

// ------------------------------------------------------------------------------------------------ XOR + Gauss
// Recover XOR constraints (a variable set whose clauses cover every assignment of one parity) and run Gauss-Jordan
// elimination over GF(2) before search. An inconsistent row proves UNSAT; rows reduced to one or two variables give
// units and equivalences for the CDCL core. Hardware: rows are bit vectors in BRAM borrowed from the (not yet used)
// clause banks; one row-XOR costs one cycle per `gauss_word` bits.
struct GaussResult { bool unsat = false; int xors = 0; int units = 0; int equivs = 0; u64 cycles = 0; u64 cols = 0;
                     std::vector<std::vector<u32>> derived; };

static GaussResult gauss(const Formula& f, int max_width, int word_bits) {
    GaussResult R;
    // group clauses of width <= max_width by their variable set
    struct Key { std::vector<u32> vs; bool operator<(const Key& o) const { return vs < o.vs; } };
    std::vector<std::pair<std::vector<u32>, u32>> items;   // (sorted vars, negation mask over that order)
    for (auto& c : f.clauses) {
        if (c.empty() || (int)c.size() > max_width) continue;
        std::vector<u32> vs; vs.reserve(c.size());
        for (u32 l : c) vs.push_back(var_of(l));
        std::vector<u32> sv = vs; std::sort(sv.begin(), sv.end());
        if (std::adjacent_find(sv.begin(), sv.end()) != sv.end()) continue;
        u32 mask = 0;
        for (u32 l : c) mask |= (l & 1) << (std::lower_bound(sv.begin(), sv.end(), var_of(l)) - sv.begin());
        items.push_back({sv, mask});
        R.cycles += 2 * c.size();   // hashing the variable set
    }
    std::sort(items.begin(), items.end());
    R.cycles += items.size() * 2;
    // short clauses, for "a missing XOR clause is fine if a shorter clause subsumes it"
    std::vector<std::vector<u32>> shorts;
    for (auto& c : f.clauses) if ((int)c.size() < max_width) { auto t = c; std::sort(t.begin(), t.end()); shorts.push_back(t); }
    std::sort(shorts.begin(), shorts.end());
    auto subsumed = [&](const std::vector<u32>& vars, u32 mask) {
        int k = (int)vars.size();
        for (u32 sub = 1; sub < (1u << k) - 1; sub++) {   // proper, non-empty subsets of the clause
            std::vector<u32> t;
            for (int b = 0; b < k; b++) if (sub >> b & 1) t.push_back(2 * vars[b] + (mask >> b & 1));
            std::sort(t.begin(), t.end());
            if (std::binary_search(shorts.begin(), shorts.end(), t)) return true;
        }
        return false;
    };
    struct Row { std::vector<u64> bits; int rhs; };
    std::vector<u32> cols;                       // variables that occur in some XOR
    std::vector<std::pair<std::vector<u32>, int>> xs;
    for (size_t i = 0; i < items.size();) {
        size_t j = i;
        while (j < items.size() && items[j].first == items[i].first) j++;
        int k = (int)items[i].first.size();
        u32 need = 1u << (k - 1);
        for (int par = 0; par < 2; par++) {
            std::vector<u32> masks;
            for (size_t t = i; t < j; t++) if (__builtin_popcount(items[t].second) % 2 == par) masks.push_back(items[t].second);
            std::sort(masks.begin(), masks.end()); masks.erase(std::unique(masks.begin(), masks.end()), masks.end());
            if (masks.size() * 2 < need) continue;   // not plausibly an XOR
            bool all = masks.size() == need;
            if (!all) {   // every missing clause must be subsumed by a shorter one
                all = true;
                for (u32 m = 0; m < (1u << k) && all; m++) {
                    if (__builtin_popcount(m) % 2 != par || std::binary_search(masks.begin(), masks.end(), m)) continue;
                    R.cycles += 1u << k;
                    if (!subsumed(items[i].first, m)) all = false;
                }
            }
            if (all) xs.push_back({items[i].first, par ^ 1});
        }
        i = j;
    }
    R.xors = (int)xs.size();
    if (xs.empty()) return R;
    for (auto& x : xs) for (u32 v : x.first) cols.push_back(v);
    std::sort(cols.begin(), cols.end()); cols.erase(std::unique(cols.begin(), cols.end()), cols.end());
    size_t W = (cols.size() + 63) / 64;
    R.cols = cols.size();
    u64 hw_words = (cols.size() + word_bits - 1) / word_bits;   // hardware words per row
    std::vector<Row> rows;
    for (auto& x : xs) {
        Row r{std::vector<u64>(W, 0), x.second};
        for (u32 v : x.first) { size_t c = std::lower_bound(cols.begin(), cols.end(), v) - cols.begin(); r.bits[c / 64] ^= 1ull << (c % 64); }
        rows.push_back(std::move(r));
        R.cycles += hw_words;
    }
    // Gauss-Jordan
    size_t prow = 0;
    std::vector<int> pivot_of_row;
    for (size_t c = 0; c < cols.size() && prow < rows.size(); c++) {
        size_t sel = prow;
        while (sel < rows.size() && !(rows[sel].bits[c / 64] >> (c % 64) & 1)) sel++;
        R.cycles += (sel - prow) + 1;
        if (sel == rows.size()) continue;
        std::swap(rows[sel], rows[prow]);
        for (size_t r = 0; r < rows.size(); r++) {
            if (r != prow && (rows[r].bits[c / 64] >> (c % 64) & 1)) {
                for (size_t w = 0; w < W; w++) rows[r].bits[w] ^= rows[prow].bits[w];
                rows[r].rhs ^= rows[prow].rhs;
                R.cycles += hw_words;
            }
            R.cycles += 1;   // bit test
        }
        prow++;
    }
    for (auto& r : rows) {
        std::vector<u32> vs;
        for (size_t w = 0; w < W; w++) for (u64 b = r.bits[w]; b; b &= b - 1) vs.push_back(cols[w * 64 + __builtin_ctzll(b)]);
        R.cycles += hw_words;
        if (vs.empty()) { if (r.rhs) { R.unsat = true; return R; } continue; }
        if (vs.size() == 1) { R.derived.push_back({2 * vs[0] + (r.rhs ? 0u : 1u)}); R.units++; }
        else if (vs.size() == 2) {   // x ^ y = rhs: two binary clauses
            u32 x = 2 * vs[0], y = 2 * vs[1];
            if (r.rhs) { R.derived.push_back({x, y}); R.derived.push_back({x ^ 1, y ^ 1}); }
            else { R.derived.push_back({x, y ^ 1}); R.derived.push_back({x ^ 1, y}); }
            R.equivs++;
        }
    }
    return R;
}

// ------------------------------------------------------------------------------------------------ RUP checker
// Independent of the solver's data structures: recomputes unit propagation from scratch over every clause it was
// given. Used only with --check.
struct Checker {
    int n;
    std::vector<std::vector<u32>> cls;
    std::vector<std::vector<int>> occ;   // literal -> clause indices
    explicit Checker(const Formula& f) : n(f.nvars), occ(2 * f.nvars) {
        for (auto& c : f.clauses) add(c);
    }
    void add(const std::vector<u32>& c) {
        int id = (int)cls.size();
        cls.push_back(c);
        for (u32 l : c) occ[l].push_back(id);
    }
    // true if assuming the negation of c propagates to a conflict
    bool rup(const std::vector<u32>& c) const {
        std::vector<int8_t> val(2 * n, 0);
        std::vector<u32> q;
        auto set = [&](u32 l) -> bool {   // false on conflict
            if (val[l] == 1) return true;
            if (val[l] == -1) return false;
            val[l] = 1; val[l ^ 1] = -1; q.push_back(l);
            return true;
        };
        for (u32 l : c) if (!set(l ^ 1)) return true;
        // seed with every unit clause and every clause already unit/empty under the assumptions
        for (size_t i = 0; i < cls.size(); i++) {
            int unk = 0; u32 last = 0; bool sat = false;
            for (u32 l : cls[i]) { if (val[l] == 1) { sat = true; break; } if (val[l] == 0) { unk++; last = l; } }
            if (sat) continue;
            if (unk == 0) return true;
            if (unk == 1 && !set(last)) return true;
        }
        for (size_t h = 0; h < q.size(); h++) {
            u32 f = q[h] ^ 1;   // became false
            for (int id : occ[f]) {
                int unk = 0; u32 last = 0; bool sat = false;
                for (u32 l : cls[id]) { if (val[l] == 1) { sat = true; break; } if (val[l] == 0) { unk++; last = l; } }
                if (sat) continue;
                if (unk == 0) return true;
                if (unk == 1 && !set(last)) return true;
            }
        }
        return false;
    }
};

// ------------------------------------------------------------------------------------------------ local search
// probSAT with the polynomial break function, over the original clauses only. Break counts are kept incrementally;
// a clause's critical variable (its only true literal's variable) is the XOR of its true variables while numTrue==1.
struct Walker {
    const Formula& F;
    int n;
    Rng rng;
    std::vector<int8_t> a;           // assignment per var
    std::vector<u32> ntrue, critx;   // per clause
    std::vector<u32> brk;            // per var
    std::vector<u32> unsat, upos;    // unsat clause list + position
    std::vector<std::vector<u32>> occ;  // literal -> clauses
    std::vector<int8_t> best;
    u32 best_unsat = ~0u;
    u64 flips = 0, cycles = 0, restart_at = 0;
    double cb;
    std::vector<double> ptab;
    bool solved = false;

    Walker(const Formula& f, u64 seed) : F(f), n(f.nvars), rng(seed), a(n, 0), ntrue(f.clauses.size()),
        critx(f.clauses.size()), brk(n), upos(f.clauses.size(), ~0u), occ(2 * f.nvars), best(n, 0) {
        int maxw = 0;
        for (size_t i = 0; i < f.clauses.size(); i++) {
            for (u32 l : f.clauses[i]) occ[l].push_back((u32)i);
            maxw = std::max(maxw, (int)f.clauses[i].size());
        }
        cb = maxw <= 3 ? 2.06 : maxw <= 4 ? 3.0 : maxw <= 5 ? 3.7 : 5.1;   // probSAT's tuned values
        ptab.resize(64);
        for (int b = 0; b < 64; b++) ptab[b] = pow(1.0 + b, -cb);   // a small ROM in hardware
    }
    void init(const std::vector<int8_t>* phases) {
        for (int v = 0; v < n; v++) a[v] = phases ? ((*phases)[v] >= 0 ? 1 : 0) : (rng.next() & 1);
        std::fill(brk.begin(), brk.end(), 0);
        unsat.clear();
        for (size_t i = 0; i < F.clauses.size(); i++) {
            u32 t = 0, x = 0;
            for (u32 l : F.clauses[i]) if (truth(l)) { t++; x ^= var_of(l); }
            ntrue[i] = t; critx[i] = x;
            if (t == 1) brk[x]++;
            upos[i] = ~0u;
            if (t == 0) { upos[i] = (u32)unsat.size(); unsat.push_back((u32)i); }
        }
        cycles += F.clauses.size() + n;   // initialization sweep
        best_unsat = ~0u;
        note_best();
    }
    bool truth(u32 l) const { return (a[var_of(l)] == 1) == !(l & 1); }
    void note_best() {
        if (unsat.size() < best_unsat) { best_unsat = (u32)unsat.size(); best = a; }
        if (unsat.empty()) solved = true;
    }
    void flip(u32 v) {
        u32 tl = a[v] ? 2 * v : 2 * v + 1;   // literal of v that is true now and becomes false
        u32 fl = tl ^ 1;
        a[v] ^= 1;
        u64 work = 0;
        for (u32 c : occ[tl]) {   // these lose a true literal
            work++;
            u32 t = --ntrue[c];
            critx[c] ^= v;
            if (t == 0) { brk[v]--; upos[c] = (u32)unsat.size(); unsat.push_back(c); work += 2; }
            else if (t == 1) brk[critx[c]]++;
        }
        for (u32 c : occ[fl]) {   // these gain one
            work++;
            u32 t = ++ntrue[c];
            if (t == 1) {
                u32 p = upos[c], last = unsat.back();
                unsat[p] = last; upos[last] = p; unsat.pop_back(); upos[c] = ~0u;
                brk[v]++; work += 2;
            } else if (t == 2) brk[critx[c]]--;
            critx[c] ^= v;
        }
        cycles += 2 + (work + 1) / 2;   // two occurrence lists per cycle (dual port)
        flips++;
    }
    // run for about `budget` cycles; returns true when a model was found
    bool run(u64 budget, const std::vector<int8_t>& cdcl_phases) {
        u64 stop = cycles + budget;
        while (cycles < stop && !solved) {
            if (flips >= restart_at) {
                init(flips == 0 ? nullptr : &cdcl_phases);
                restart_at = flips + 100000 + 20ull * F.clauses.size();
                if (solved) break;
            }
            u32 c = unsat[rng.below((u32)unsat.size())];
            const auto& cl = F.clauses[c];
            double sum = 0, w[512];
            size_t k = std::min<size_t>(cl.size(), 512);
            for (size_t i = 0; i < k; i++) { w[i] = ptab[std::min<u32>(brk[var_of(cl[i])], 63)]; sum += w[i]; }
            cycles += 2 + (k + 1) / 2;
            double r = rng.unit() * sum;
            size_t pick = 0;
            for (; pick + 1 < k; pick++) { r -= w[pick]; if (r <= 0) break; }
            flip(var_of(cl[pick]));
            note_best();
        }
        return solved;
    }
};

// ------------------------------------------------------------------------------------------------ CDCL core
enum : u32 { REASON_NONE = ~0u, BIN_FLAG = 0x80000000u };

struct Watch { u32 cref; u32 blocker; };

struct Stats {
    u64 conflicts = 0, decisions = 0, propagations = 0, restarts = 0, reduces = 0, learned = 0, deleted = 0;
    u64 cyc_bcp = 0, cyc_analyze = 0, cyc_decide = 0, cyc_backtrack = 0, cyc_reduce = 0, cyc_other = 0;
    u64 rephases = 0, walk_rephases = 0, forced_reduces = 0, checked = 0;
    u64 viv_tried = 0, viv_shrunk = 0, viv_lits_removed = 0, viv_units = 0, cyc_vivify = 0, walker_flips = 0;
};

struct Solver {
    Config cfg;
    const Formula& F;
    int n;
    Rng rng;
    Stats st;
    int P_active;

    // clause arena: [size][meta][lits...]; meta = lbd | learned<<16 | deleted<<17 | used<<18 | part<<20
    std::vector<u32> arena;
    std::vector<u32> learned_refs;
    long arena_live = 0;   // literal slots in use (clauses not deleted)
    long arena_peak = 0, clauses_live = 0, clauses_peak = 0;   // for the BRAM estimate
    // with a BRAM budget: bits of clause-bank memory in use and available (bodies, headers, watches, learned binaries)
    double live_bits = 0, cap_bits = 1e300;
    int lbits = 16, abits = 18;
    bool memout = false;
    double clause_bits(u32 k) const { return (k + 2.0) * lbits + 2.0 * (abits + lbits); }

    std::vector<int8_t> val;          // per literal
    std::vector<int> level;
    std::vector<u32> reason;
    std::vector<u32> trail;
    std::vector<size_t> trail_lim;
    size_t qhead = 0;

    std::vector<std::vector<std::vector<Watch>>> wl;   // [partition][literal]
    std::vector<std::vector<u32>> bins;                // [literal] -> implied literals when it becomes false
    std::vector<u32> part_load;                        // watches per partition (for statistics)

    // decisions
    std::vector<u32> prev_, next_;
    std::vector<u64> stamp;
    u32 vmtf_first = ~0u, vmtf_last = ~0u, vmtf_search = ~0u;
    u64 stamp_ctr = 0;
    std::vector<double> act;
    double act_inc = 1.0;
    std::vector<u32> heap, hpos;

    // phases
    std::vector<int8_t> saved, target, bestp;
    size_t target_max = 0, best_max = 0;

    // modes, restarts
    bool stable = false;
    u64 mode_switch_at = 1000, mode_len = 1000;
    double ema_fast = 0, ema_slow = 0;
    u64 last_restart_conf = 0;
    u64 luby_i = 0, luby_next = 0;
    u64 reduce_at = 2000, reduce_inc = 300, reduce_k = 0;
    u64 rephase_at = 1000, rephase_k = 0;

    // analysis scratch
    std::vector<uint8_t> seen;
    std::vector<u32> learnt, to_clear, analyzed, stack_;
    std::vector<u64> level_stamp;
    u64 lstamp = 0;

    Checker* chk = nullptr;
    u32 ignore_cr = REASON_NONE;          // the clause being vivified takes no part in propagation
    bool probing = false;                 // vivification: do not save its assignments as phases
    bool walker_dropped = false;          // the instance needed the walker's memory
    std::vector<u32> occ_count;           // literal occurrences in the original clauses (a static table)
    u64 viv_mark = 0;                     // cycles at the end of the last vivification round
    Walker* walker = nullptr;
    u64 cycles = 0, cycle_limit;
    u64 walker_synced = 0;

    Solver(const Config& c, const Formula& f) : cfg(c), F(f), n(f.nvars), rng(c.seed), val(2 * f.nvars, 0),
        level(f.nvars, 0), reason(f.nvars, REASON_NONE), bins(2 * f.nvars), prev_(f.nvars), next_(f.nvars),
        stamp(f.nvars), act(f.nvars, 0), hpos(f.nvars, ~0u), saved(f.nvars, 1), target(f.nvars, 0),
        bestp(f.nvars, 0), seen(f.nvars, 0), level_stamp(f.nvars + 2, 0) {
        // elastic partitioning: heads cost 2n words per active partition
        P_active = std::max(1, std::min(cfg.P, cfg.head_words / std::max(1, 2 * n)));
        wl.assign(P_active, std::vector<std::vector<Watch>>(2 * n));
        part_load.assign(P_active, 0);
        for (int v = 0; v < n; v++) {   // VMTF queue in variable order
            prev_[v] = v ? v - 1 : ~0u; next_[v] = v + 1 < n ? v + 1 : ~0u; stamp[v] = ++stamp_ctr;
        }
        if (n) { vmtf_first = 0; vmtf_last = n - 1; vmtf_search = n - 1; }
        cycle_limit = (u64)(cfg.limit_s * cfg.mhz * 1e6);
    }

    // ---- helpers
    static int clog2_(u64 x) { int b = 0; while ((1ull << b) < x) b++; return std::max(b, 1); }
    double fixed_blocks(bool with_walker) const {
        auto blocks = [](double bits) { return bits <= 0 ? 0.0 : std::ceil(bits / 18432.0); };
        double nn = std::max(1, n);
        int vb = clog2_(n);
        double b = blocks(2 * nn) * (P_active + 1) + blocks(nn * clog2_(n + 1)) + blocks(nn * (abits + 1)) + blocks(nn * lbits)
                 + blocks(2 * nn) * 3 + blocks(nn * vb) * 2 + blocks(nn * 32) + blocks(2 * nn);
        b += P_active * blocks(2 * nn * abits);                  // watch-list heads per bank
        u64 nbin = 0; for (auto& l : bins) nbin += l.size();
        b += blocks((double)nbin * lbits) + blocks(2 * nn * 16);  // original binaries + their heads
        if (with_walker) {
            u64 lits = 0; for (auto& c : F.clauses) lits += c.size();
            double mc = std::max<double>(1, F.clauses.size());
            int cb = clog2_((u64)mc);
            b += blocks(mc * 4) + blocks(mc * vb) + blocks(mc * cb) * 2 + blocks(nn * 8) + blocks(2 * nn)
               + blocks((double)lits * cb) + blocks(2 * nn * clog2_(lits + 2));
        }
        return b;
    }
    u32* lits(u32 cr) { return &arena[cr + 2]; }
    u32 csize(u32 cr) const { return arena[cr]; }
    u32& meta(u32 cr) { return arena[cr + 1]; }
    int lbd_of(u32 cr) { return meta(cr) & 0xFFFF; }
    bool is_learned(u32 cr) { return meta(cr) >> 16 & 1; }
    bool is_deleted(u32 cr) { return meta(cr) >> 17 & 1; }
    int part_of(u32 cr) { return meta(cr) >> 20; }
    int dlevel() const { return (int)trail_lim.size(); }
    int8_t value(u32 l) const { return val[l]; }

    void assign(u32 l, u32 why) {
        u32 v = var_of(l);
        val[l] = 1; val[l ^ 1] = -1;
        level[v] = dlevel();
        reason[v] = why;
        trail.push_back(l);
        st.propagations++;
    }

    // place a clause's two watches in the partition with the least load on those two lists
    int pick_partition(u32 w0, u32 w1) {
        int bestp_ = 0; size_t bl = ~(size_t)0;
        for (int p = 0; p < P_active; p++) {
            size_t l = wl[p][w0].size() + wl[p][w1].size();
            if (l < bl) { bl = l; bestp_ = p; }
        }
        return bestp_;
    }

    u32 add_clause_arena(const std::vector<u32>& c, bool learned, int lbd) {
        u32 cr = (u32)arena.size();
        int p = pick_partition(c[0], c[1]);
        arena.push_back((u32)c.size());
        arena.push_back((u32)std::min(lbd, 0xFFFF) | (learned ? 1u << 16 : 0) | ((u32)p << 20));
        for (u32 l : c) arena.push_back(l);
        wl[p][c[0]].push_back({cr, c[1]});
        wl[p][c[1]].push_back({cr, c[0]});
        part_load[p] += 2;
        arena_live += c.size(); clauses_live++; live_bits += clause_bits((u32)c.size());
        arena_peak = std::max(arena_peak, arena_live); clauses_peak = std::max(clauses_peak, clauses_live);
        if (learned) learned_refs.push_back(cr);
        return cr;
    }

    // ---- propagation: returns conflict as (cref) or BIN_FLAG|... encoded in confl / confl_bin
    u32 confl = REASON_NONE; u32 confl_bin[2];
    bool propagate() {
        while (qhead < trail.size()) {
            u32 L = trail[qhead++];
            u32 f = L ^ 1;   // became false
            u64 work_bin = 0, work_max = 0;
            // binary implications
            for (u32 b : bins[f]) {
                work_bin++;
                if (val[b] == 1) continue;
                if (val[b] == -1) {
                    confl = BIN_FLAG; confl_bin[0] = b; confl_bin[1] = f;
                    cycles += (work_bin + 1) / 2 + cfg.pipe; st.cyc_bcp += (work_bin + 1) / 2 + cfg.pipe;
                    return false;
                }
                assign(b, BIN_FLAG | f);
            }
            // partitions in parallel on the same literal
            bool conflict = false;
            for (int p = 0; p < P_active && !conflict; p++) {
                auto& ws = wl[p][f];
                u64 work = 0;
                size_t i = 0, j = 0;
                for (; i < ws.size(); i++) {
                    Watch w = ws[i];
                    work++;   // read watch + blocker value
                    if (val[w.blocker] == 1 || w.cref == ignore_cr) { ws[j++] = w; continue; }
                    if (is_deleted(w.cref)) continue;   // dropped lazily
                    u32 cr = w.cref;
                    u32* c = lits(cr);
                    u32 sz = csize(cr);
                    if (c[0] == f) std::swap(c[0], c[1]);
                    work++;   // read header + first two literals
                    u32 first = c[0];
                    if (first != w.blocker && val[first] == 1) { ws[j++] = {cr, first}; continue; }
                    u32 k = 2; bool found = false;
                    for (; k < sz; k++) if (val[c[k]] != -1) { found = true; break; }
                    work += ((found ? k - 1 : sz - 2) + cfg.ports - 1) / cfg.ports;
                    if (found) {
                        std::swap(c[1], c[k]);
                        wl[p][c[1]].push_back({cr, first});
                        work++;   // watch write
                        continue;
                    }
                    ws[j++] = {cr, first};
                    if (val[first] == -1) {
                        confl = cr; conflict = true; i++;
                        for (; i < ws.size(); i++) ws[j++] = ws[i];
                        break;
                    }
                    assign(first, cr);
                }
                ws.resize(j);
                work_max = std::max(work_max, work);
            }
            u64 step = std::max(work_max, (work_bin + 1) / 2) + cfg.pipe;
            cycles += step; st.cyc_bcp += step;
            if (conflict) return false;
        }
        return true;
    }

    // ---- debug: after a conflict-free propagation no clause may be false or unit (--check)
    void audit() {
        auto chk = [&](const u32* c, u32 sz, const char* what, u32 id) {
            int unk = 0; bool sat = false;
            for (u32 k = 0; k < sz; k++) { if (val[c[k]] == 1) sat = true; else if (val[c[k]] == 0) unk++; }
            if (!sat && unk <= 1) {
                fprintf(stderr, "AUDIT: %s clause %u is %s at level %d:", what, id, unk ? "unit" : "false", dlevel());
                for (u32 k = 0; k < sz; k++) fprintf(stderr, " %d@%d%s", (c[k] & 1) ? -(int)(c[k] / 2 + 1) : (int)(c[k] / 2 + 1),
                    val[c[k]] ? level[var_of(c[k])] : -1, val[c[k]] == 1 ? "T" : val[c[k]] == -1 ? "F" : "?");
                fprintf(stderr, "\n");
                exit(5);
            }
        };
        for (u32 cr = 0; cr < arena.size(); cr += 2 + arena[cr]) if (!is_deleted(cr)) chk(lits(cr), csize(cr), "long", cr);
        for (u32 l = 0; l < 2 * (u32)n; l++) for (u32 b : bins[l]) { u32 c[2] = {l, b}; chk(c, 2, "binary", l); }
    }

    // ---- decisions: VMTF
    void vmtf_bump(u32 v) {
        if (next_[v] == ~0u) { stamp[v] = ++stamp_ctr; return; }   // already last
        // unlink
        if (prev_[v] != ~0u) next_[prev_[v]] = next_[v]; else vmtf_first = next_[v];
        prev_[next_[v]] = prev_[v];
        if (vmtf_search == v) vmtf_search = prev_[v] != ~0u ? prev_[v] : next_[v];
        // append
        prev_[v] = vmtf_last; next_[v] = ~0u; next_[vmtf_last] = v; vmtf_last = v;
        stamp[v] = ++stamp_ctr;
        if (val[2 * v] == 0) vmtf_search = v;
    }
    // ---- decisions: EVSIDS heap (stable mode option)
    bool hless(u32 a, u32 b) const { return act[a] > act[b]; }
    void hup(u32 i) {
        u32 v = heap[i];
        while (i) { u32 p = (i - 1) / 2; if (!hless(v, heap[p])) break; heap[i] = heap[p]; hpos[heap[i]] = i; i = p; cycles++; }
        heap[i] = v; hpos[v] = i;
    }
    void hdown(u32 i) {
        u32 v = heap[i], sz = (u32)heap.size();
        for (;;) {
            u32 c = 2 * i + 1; if (c >= sz) break;
            if (c + 1 < sz && hless(heap[c + 1], heap[c])) c++;
            if (!hless(heap[c], v)) break;
            heap[i] = heap[c]; hpos[heap[i]] = i; i = c; cycles++;
        }
        heap[i] = v; hpos[v] = i;
    }
    void hinsert(u32 v) { if (hpos[v] != ~0u) return; hpos[v] = (u32)heap.size(); heap.push_back(v); hup(hpos[v]); }
    u32 hpop() {
        u32 v = heap[0]; u32 last = heap.back(); heap.pop_back(); hpos[v] = ~0u;
        if (!heap.empty()) { heap[0] = last; hpos[last] = 0; hdown(0); }
        return v;
    }
    void vsids_bump(u32 v) {
        act[v] += act_inc;
        if (act[v] > 1e100) { for (auto& x : act) x *= 1e-100; act_inc *= 1e-100; cycles += n; }
        if (hpos[v] != ~0u) hup(hpos[v]);
    }
    bool use_heap() const { return stable && cfg.stable == 2; }

    u32 decide() {   // returns literal or ~0u when all assigned
        if (use_heap()) {
            while (!heap.empty()) {
                u32 v = hpop(); cycles += 1; st.cyc_decide += 1;
                if (val[2 * v] == 0) return pick_phase(v);
            }
            return ~0u;
        }
        u32 v = vmtf_search;
        u64 w = 0;
        while (v != ~0u && val[2 * v] != 0) { v = prev_[v]; w++; }
        cycles += w + 1; st.cyc_decide += w + 1;
        if (v == ~0u) return ~0u;
        vmtf_search = v;
        return pick_phase(v);
    }
    u32 pick_phase(u32 v) {
        int8_t ph = (stable && target[v]) ? target[v] : saved[v];
        return ph >= 0 ? 2 * v : 2 * v + 1;
    }

    void backtrack(int lvl) {
        if (dlevel() <= lvl) return;
        size_t to = trail_lim[lvl];
        u64 w = 0;
        for (size_t i = trail.size(); i-- > to;) {
            u32 l = trail[i], v = var_of(l);
            if (!probing) saved[v] = (l & 1) ? -1 : 1;
            val[l] = 0; val[l ^ 1] = 0; reason[v] = REASON_NONE;
            if (stamp[v] > stamp[vmtf_search == ~0u ? v : vmtf_search] || vmtf_search == ~0u) vmtf_search = v;
            if (cfg.stable == 2) hinsert(v);
            w++;
        }
        trail.resize(to); trail_lim.resize(lvl);
        qhead = std::min(qhead, to);
        cycles += w; st.cyc_backtrack += w;
    }

    // ---- conflict analysis (1UIP + recursive minimization)
    template <class F_> void for_reason(u32 v, F_ fn) {
        u32 r = reason[v];
        if (r & BIN_FLAG) { fn(r & ~BIN_FLAG); return; }
        u32* c = lits(r); u32 sz = csize(r);
        for (u32 k = 1; k < sz; k++) fn(c[k]);
    }
    u32 reason_size(u32 v) { u32 r = reason[v]; return (r & BIN_FLAG) ? 2 : csize(r); }

    bool redundant(u32 l, u32 abstract) {   // is ~l implied by the other learnt literals?
        stack_.clear(); stack_.push_back(l);
        size_t top = to_clear.size();
        u64 work = 0;
        while (!stack_.empty()) {
            u32 x = stack_.back(); stack_.pop_back();
            u32 v = var_of(x);
            bool ok = true;
            for_reason(v, [&](u32 q) {
                if (!ok) return;
                work++;
                u32 qv = var_of(q);
                if (seen[qv] || level[qv] == 0) return;
                if (reason[qv] != REASON_NONE && (abstract >> (level[qv] & 31) & 1)) {
                    seen[qv] = 2; stack_.push_back(q); to_clear.push_back(qv);
                } else ok = false;
            });
            if (!ok) {
                for (size_t i = top; i < to_clear.size(); i++) seen[to_clear[i]] = 0;
                to_clear.resize(top);
                cycles += work; st.cyc_analyze += work;
                return false;
            }
        }
        cycles += work; st.cyc_analyze += work;
        return true;
    }

    int analyze(u32 cf, int& out_lbd) {
        learnt.clear(); learnt.push_back(0); analyzed.clear();
        int pathc = 0; u32 p = ~0u;
        size_t idx = trail.size();
        u64 work = 0;
        auto visit = [&](u32 q) {
            u32 v = var_of(q);
            work++;
            if (seen[v] || level[v] == 0) return;
            seen[v] = 1; analyzed.push_back(v);
            if (level[v] >= dlevel()) pathc++; else learnt.push_back(q);
        };
        // conflict clause
        if (cf == BIN_FLAG) { visit(confl_bin[0]); visit(confl_bin[1]); }
        else { u32* c = lits(cf); for (u32 k = 0; k < csize(cf); k++) visit(c[k]); mark_used(cf); }
        for (;;) {
            while (!seen[var_of(trail[--idx])]) work++;
            p = trail[idx];
            u32 pv = var_of(p);
            seen[pv] = 0; pathc--;
            if (pathc == 0) break;
            u32 r = reason[pv];
            if (!(r & BIN_FLAG)) mark_used(r);
            for_reason(pv, visit);
            work += (reason_size(pv) + 1) / 2;
        }
        learnt[0] = p ^ 1;
        // minimization
        u32 abstract = 0;
        for (size_t i = 1; i < learnt.size(); i++) abstract |= 1u << (level[var_of(learnt[i])] & 31);
        to_clear.clear();
        size_t j = 1;
        for (size_t i = 1; i < learnt.size(); i++) {
            u32 v = var_of(learnt[i]);
            if (reason[v] == REASON_NONE || !redundant(learnt[i], abstract)) learnt[j++] = learnt[i];
        }
        learnt.resize(j);
        for (u32 v : to_clear) seen[v] = 0;
        for (size_t i = 0; i < learnt.size(); i++) seen[var_of(learnt[i])] = 0;
        for (u32 v : analyzed) seen[v] = 0;
        // backjump level: second highest, put it at position 1
        int bt = 0;
        if (learnt.size() > 1) {
            size_t mi = 1;
            for (size_t i = 2; i < learnt.size(); i++) if (level[var_of(learnt[i])] > level[var_of(learnt[mi])]) mi = i;
            std::swap(learnt[1], learnt[mi]);
            bt = level[var_of(learnt[1])];
        }
        // LBD
        lstamp++;
        int lbd = 0;
        for (u32 l : learnt) { int lv = level[var_of(l)]; if (level_stamp[lv] != lstamp) { level_stamp[lv] = lstamp; lbd++; } }
        out_lbd = lbd;
        // bump
        for (u32 v : analyzed) { if (stable && cfg.stable == 2) vsids_bump(v); else vmtf_bump(v); }
        if (stable && cfg.stable == 2) act_inc *= 1.0 / 0.95;
        work += analyzed.size() * 4 + learnt.size();
        cycles += work; st.cyc_analyze += work;
        return bt;
    }
    void mark_used(u32 cr) { if (is_learned(cr)) meta(cr) |= 1u << 18; }

    // ---- clause database reduction
    void reduce(int level) {   // 0 scheduled, 1 forced, 2 also used tier 2, 3 every learned clause but reasons
        bool forced = level > 0;
        st.reduces++; if (forced) st.forced_reduces++;
        // protect reasons
        auto locked = [&](u32 cr) {
            u32 l0 = lits(cr)[0], v = var_of(l0);
            return val[l0] == 1 && reason[v] == cr;
        };
        std::vector<u32> cand;
        u64 work = 0;
        for (u32 cr : learned_refs) {
            work += 2;
            if (is_deleted(cr)) continue;
            int lbd = lbd_of(cr);
            bool used = meta(cr) >> 18 & 1;
            meta(cr) &= ~(1u << 18);
            if (locked(cr)) continue;
            if (lbd <= 2 && level < 3) continue;          // tier 1: keep
            if (lbd <= 6 && used && level < 2) continue;  // tier 2: keep while used
            cand.push_back(cr);
        }
        // bucket by LBD (counting sort), delete the worse half
        std::stable_sort(cand.begin(), cand.end(), [&](u32 a, u32 b) { return lbd_of(a) > lbd_of(b); });
        size_t kill = level >= 2 ? cand.size() : forced ? cand.size() * 3 / 4 : cand.size() / 2;
        for (size_t i = 0; i < kill; i++) {
            meta(cand[i]) |= 1u << 17; arena_live -= csize(cand[i]); clauses_live--; st.deleted++;
            live_bits -= clause_bits(csize(cand[i]));
        }
        // rebuild watch lists without deleted clauses (all partitions in parallel)
        u64 maxw = 0;
        for (int p = 0; p < P_active; p++) {
            u64 w = 0;
            for (auto& ws : wl[p]) {
                size_t j = 0;
                for (auto& x : ws) { w++; if (!is_deleted(x.cref)) ws[j++] = x; }
                ws.resize(j);
            }
            maxw = std::max(maxw, w);
        }
        std::vector<u32> keep;
        for (u32 cr : learned_refs) if (!is_deleted(cr)) keep.push_back(cr);
        learned_refs.swap(keep);
        work += maxw + 2 * n;   // the head sweep is per literal
        cycles += work; st.cyc_reduce += work;
    }

    // ---- vivification: shorten learned clauses with the propagation engine (root level, budgeted)
    bool vivify_round() {   // false if the formula was found UNSAT
        backtrack(0);
        if (!propagate()) return false;
        u64 budget = (u64)(cfg.vivify * (cycles - viv_mark)), start = cycles;
        std::vector<u32> cand;
        for (u32 cr : learned_refs) {
            if (is_deleted(cr) || (meta(cr) >> 19 & 1) || lbd_of(cr) > 6) continue;
            cand.push_back(cr);
        }
        std::stable_sort(cand.begin(), cand.end(), [&](u32 a, u32 b) { return lbd_of(a) < lbd_of(b); });
        std::vector<u32> lits_, keep;
        for (u32 cr : cand) {
            if (cycles - start > budget) break;
            if (is_deleted(cr)) continue;
            u32 l0 = lits(cr)[0];
            if (val[l0] == 1 && reason[var_of(l0)] == cr) continue;   // a root-level reason: leave it
            meta(cr) |= 1u << 19;
            st.viv_tried++;
            u32 sz = csize(cr);
            lits_.assign(lits(cr), lits(cr) + sz);
            bool sat_root = false;
            keep.clear();
            for (u32 l : lits_) { if (val[l] == 1) sat_root = true; else if (val[l] == 0) keep.push_back(l); }
            if (sat_root) { delete_clause(cr); continue; }
            // most frequent literals first (they propagate most)
            std::sort(keep.begin(), keep.end(), [&](u32 a, u32 b) { return occ_count[a] > occ_count[b]; });
            cycles += keep.size() * keep.size() / 2 + 2;   // small insertion sort in the controller
            if (keep.empty()) return false;   // every literal false at the root: UNSAT
            ignore_cr = cr; probing = true;
            std::vector<u32> out;
            bool done = false;
            for (u32 l : keep) {
                if (val[l] == 1) { out.push_back(l); done = true; break; }   // implied by the others: stop here
                if (val[l] == -1) continue;                                   // implied false: drop it
                out.push_back(l);
                trail_lim.push_back(trail.size());
                assign(l ^ 1, REASON_NONE);
                if (!propagate()) { done = true; break; }                     // the others already conflict
            }
            (void)done;
            ignore_cr = REASON_NONE;
            backtrack(0);
            probing = false;
            if (out.size() >= sz) continue;
            st.viv_shrunk++; st.viv_lits_removed += sz - out.size();
            int lbd = std::min<int>(lbd_of(cr), (int)out.size());
            delete_clause(cr);
            learnt = out;
            if (chk) {
                if (!chk->rup(learnt)) { fprintf(stderr, "CHECK FAILED: vivified clause is not RUP\n"); exit(3); }
                chk->add(learnt); st.checked++;
            }
            if (out.size() == 1) {
                st.viv_units++;
                assign(out[0], REASON_NONE);
                if (!propagate()) return false;
            } else if (out.size() == 2) {
                bins[out[0]].push_back(out[1]); bins[out[1]].push_back(out[0]);
                live_bits += 2.0 * lbits; cycles += 3;
            } else {
                u32 ncr = add_clause_arena(out, true, lbd);
                meta(ncr) |= 1u << 19;
                cycles += (out.size() + 1) / 2 + 2;
            }
        }
        st.cyc_vivify += cycles - start;
        viv_mark = cycles;
        return true;
    }
    void delete_clause(u32 cr) {   // lazily: watch lists drop it at the next reduction
        if (is_deleted(cr)) return;
        meta(cr) |= 1u << 17; arena_live -= csize(cr); clauses_live--; st.deleted++;
        live_bits -= clause_bits(csize(cr));
    }

    // ---- learning
    bool learn(int bt, int lbd) {
        if (chk) {
            if (!chk->rup(learnt)) {
                fprintf(stderr, "CHECK FAILED: learned clause %" PRIu64 " is not RUP\n", st.learned);
                exit(3);
            }
            chk->add(learnt);
            st.checked++;
        }
        st.learned++;
        backtrack(bt);
        if (learnt.size() == 1) { assign(learnt[0], REASON_NONE); return true; }
        if (learnt.size() == 2) {
            bins[learnt[0]].push_back(learnt[1]);
            bins[learnt[1]].push_back(learnt[0]);
            live_bits += 2.0 * lbits;
            assign(learnt[0], BIN_FLAG | learnt[1]);
            cycles += 3;
            return true;
        }
        u32 cr = add_clause_arena(learnt, true, lbd);
        u64 w = (learnt.size() + 1) / 2 + 2;
        cycles += w; st.cyc_other += w;
        assign(learnt[0], cr);
        return true;
    }

    // ---- restarts, modes, rephasing
    static u64 luby(u64 x) {   // MiniSat's formulation, x = 0, 1, 2, ...: 1 1 2 1 1 2 4 ...
        u64 size = 1, seq = 0;
        while (size < x + 1) { seq++; size = 2 * size + 1; }
        while (size - 1 != x) { size = (size - 1) >> 1; seq--; x = x % size; }
        return 1ull << seq;
    }
    bool want_restart() {
        if (stable) return st.conflicts >= luby_next;
        if (st.conflicts - last_restart_conf < 2) return false;
        return ema_fast > 1.1 * ema_slow;
    }
    void do_restart() {
        st.restarts++;
        backtrack(0);
        last_restart_conf = st.conflicts;
        if (stable) { luby_next = st.conflicts + 1024 * luby(++luby_i); }
    }
    void switch_mode() {
        stable = !stable;
        mode_len = mode_len * 2;
        mode_switch_at = st.conflicts + mode_len;
        if (stable) {
            luby_i = 0; luby_next = st.conflicts + 1024;
            if (cfg.stable == 2) { heap.clear(); std::fill(hpos.begin(), hpos.end(), ~0u); for (int v = 0; v < n; v++) if (val[2 * v] == 0) hinsert(v); }
        }
        backtrack(0);
    }
    void update_targets() {
        // consistent prefix = everything assigned below the conflict level
        size_t lim = trail_lim.empty() ? trail.size() : trail_lim.back();
        if (lim > target_max) {
            target_max = lim;
            for (size_t i = 0; i < lim; i++) { u32 l = trail[i]; target[var_of(l)] = (l & 1) ? -1 : 1; }
            cycles += lim / 4;
        }
        if (lim > best_max) {
            best_max = lim;
            for (size_t i = 0; i < lim; i++) { u32 l = trail[i]; bestp[var_of(l)] = (l & 1) ? -1 : 1; }
            cycles += lim / 4;
        }
    }
    void rephase() {
        st.rephases++;
        int kind = rephase_k++ % 6;   // B W O B W I
        if ((kind == 1 || kind == 4) && walker) {
            for (int v = 0; v < n; v++) saved[v] = walker->best[v] ? 1 : -1;
            st.walk_rephases++;
        } else if (kind == 0 || kind == 3 || ((kind == 1 || kind == 4) && !walker)) {
            for (int v = 0; v < n; v++) if (bestp[v]) saved[v] = bestp[v];
        } else if (kind == 2) {
            std::fill(saved.begin(), saved.end(), 1);
        } else {
            std::fill(saved.begin(), saved.end(), -1);
        }
        std::fill(target.begin(), target.end(), 0); target_max = 0; best_max = 0;
        cycles += n; st.cyc_other += n;
        rephase_at = st.conflicts + 1000 * (rephase_k + 1);
    }

    // ---- top level
    int solve() {   // 10 SAT, 20 UNSAT, 0 unknown (limit)
        if (F.empty_clause) return 20;
        if (cfg.check) chk = new Checker(F);
        if (cfg.gauss) {
            gr = gauss(F, cfg.gauss_width, cfg.gauss_word);
            cycles += gr.cycles;
            if (gr.unsat) { by_gauss = true; return 20; }
            for (auto& c : gr.derived) {
                extra.push_back(c);
                if (chk) chk->add(c);   // XOR-implied, not RUP: given to the checker as an axiom
            }
        }
        // load: units at level 0, binaries to the binary unit, the rest to partitions
        std::vector<const std::vector<u32>*> all;
        for (auto& c : F.clauses) all.push_back(&c);
        for (auto& c : extra) all.push_back(&c);
        for (auto* cp : all) {
            auto& c = *cp;
            cycles += c.size() + 1;   // streaming load, one word per cycle
            if (c.size() == 1) {
                if (val[c[0]] == -1) return 20;
                if (val[c[0]] == 0) assign(c[0], REASON_NONE);
            } else if (c.size() == 2) {
                bins[c[0]].push_back(c[1]); bins[c[1]].push_back(c[0]);   // (a|b): a false -> b
            } else add_clause_arena(c, false, 0);
        }
        occ_count.assign(2 * n, 0);
        for (auto& c : F.clauses) for (u32 l : c) occ_count[l]++;
        if (cfg.bram > 0) {
            // fixed structures first (per-variable state, list heads, binary unit heads, walker); the rest is bank space
            lbits = clog2_(n) + 1;
            double fixed = fixed_blocks(cfg.sls);
            cap_bits = (cfg.bram - fixed) * 18432.0 * 0.97;   // a little lost to per-bank rounding
            if (cfg.sls && live_bits > 0.8 * cap_bits) {      // tight: the walker's memory goes to the banks
                walker_dropped = true;
                cap_bits = (cfg.bram - fixed_blocks(false)) * 18432.0 * 0.97;
            }
            if (live_bits > cap_bits) return -1;          // the original clauses do not fit: rejected
        } else if (arena_live > cfg.arena_words) return -1;
        Walker w(F, cfg.seed * 7 + 3);
        if (cfg.sls && !walker_dropped) walker = &w;
        for (;;) {
            if (cycles >= cycle_limit) return 0;
            if (walker && cycles - walker_synced > 20000) {   // the walker runs alongside: give it the same cycles
                std::vector<int8_t> ph(n);
                for (int v = 0; v < n; v++) ph[v] = saved[v];
                if (walker->run(cycles - walker_synced, ph)) {
                    model.assign(walker->a.begin(), walker->a.end());
                    from_walker = true;
                    return 10;
                }
                walker_synced = cycles;
                st.walker_flips = walker->flips;
            }
            if (!propagate()) {
                st.conflicts++;
                if (dlevel() == 0) return 20;
                if (stable) update_targets();
                int lbd = 0;
                int bt = analyze(confl, lbd);
                // exponential moving averages with warm-up (shift-and-add in hardware)
                ema_fast += (lbd - ema_fast) * std::max(1.0 / 32, 1.0 / st.conflicts);
                ema_slow += (lbd - ema_slow) * std::max(1e-5, 1.0 / st.conflicts);
                learn(bt, lbd);
                for (int lvl = 1; lvl <= 3 && (cfg.bram > 0 ? live_bits > 0.9 * cap_bits
                                                         : arena_live > cfg.arena_words * 9 / 10); lvl++) reduce(lvl);
                if (live_bits > cap_bits) { memout = true; return 0; }   // only reasons and originals left
                if (st.conflicts >= reduce_at) {
                    reduce(0); reduce_k++; reduce_at = st.conflicts + 2000 + reduce_inc * reduce_k;
                    if (cfg.vivify > 0 && !vivify_round()) return 20;
                    continue;
                }
                if (cfg.stable && st.conflicts >= mode_switch_at) switch_mode();
                else if (st.conflicts >= rephase_at) { backtrack(0); rephase(); }
                else if (want_restart()) do_restart();
                continue;
            }
            if (cfg.check) audit();
            u32 d = decide();
            if (d == ~0u) {
                model.resize(n);
                for (int v = 0; v < n; v++) model[v] = val[2 * v] == 1;
                return 10;
            }
            st.decisions++;
            trail_lim.push_back(trail.size());
            assign(d, REASON_NONE);
        }
    }
    std::vector<int8_t> model;
    bool from_walker = false;
    GaussResult gr;
    bool by_gauss = false;
    std::vector<std::vector<u32>> extra;   // derived by Gauss
};

// ------------------------------------------------------------------------------------------------ BRAM estimate
// DP16KD blocks (18 Kbit) the design needs for this instance at its peak. Each structure is its own memory, so
// each is rounded up to whole blocks; banked structures are rounded per bank.
static int clog2(u64 x) { int b = 0; while ((1ull << b) < x) b++; return std::max(b, 1); }
struct Bram { double per_var = 0, banks = 0, binaries = 0, walker = 0, gauss = 0; int total = 0; };
static Bram bram_estimate(const Solver& s, const Formula& f) {
    const double BLK = 18432.0;
    auto blocks = [&](double bits) { return bits <= 0 ? 0.0 : std::ceil(bits / BLK); };
    u64 n = std::max(1, f.nvars), m = std::max<u64>(1, s.clauses_peak);
    int vb = clog2(n), lb = vb + 1, cb = clog2(m) + 1, ab = clog2(std::max<long>(2, s.arena_peak + 2 * s.clauses_peak));
    int P = s.P_active;
    Bram b;
    // per-variable state: value copies (one per bank, dual-port), level, reason, trail, 3 phases, VMTF links+stamp, seen
    b.per_var = blocks(2.0 * n) * (P + 1) + blocks((double)n * clog2(n + 1)) + blocks((double)n * (ab + 1))
              + blocks((double)n * lb) + blocks(2.0 * n) * 3 + blocks((double)n * vb) * 2 + blocks(n * 32.0) + blocks(2.0 * n);
    // per bank: clause bodies + headers, watch entries (clause ref + blocker), list heads
    double body = (double)(s.arena_peak + 2 * s.clauses_peak) / P * lb, watches = 2.0 * s.clauses_peak / P * (ab + lb);
    b.banks = P * (blocks(body) + blocks(watches) + blocks(2.0 * n * ab));
    // binary implication lists
    u64 nbin = 0; for (auto& l : s.bins) nbin += l.size();
    b.binaries = blocks((double)nbin * lb) + blocks(2.0 * n * clog2(nbin + 2));
    if (s.walker) {
        u64 lits = 0; for (auto& c : f.clauses) lits += c.size();
        u64 mc = std::max<u64>(1, f.clauses.size());
        b.walker = blocks(mc * 4.0) + blocks((double)mc * vb) + blocks((double)mc * clog2(mc)) * 2 + blocks(n * 8.0)
                 + blocks(2.0 * n) + blocks((double)lits * clog2(mc)) + blocks(2.0 * n * clog2(lits + 2));
    }
    if (s.gr.xors) b.gauss = blocks((double)s.gr.xors * s.gr.cols);   // borrowed from the banks before search
    b.total = (int)(b.per_var + b.banks + b.binaries + b.walker);
    if (b.gauss > b.banks) b.total += (int)(b.gauss - b.banks);    // only what the banks cannot lend
    return b;
}

static bool check_model(const Formula& f, const std::vector<int8_t>& m) {
    for (auto& c : f.clauses) {
        bool ok = false;
        for (u32 l : c) if ((m[var_of(l)] == 1) == !(l & 1)) { ok = true; break; }
        if (!ok) return false;
    }
    return true;
}

int main(int argc, char** argv) {
    if (argc < 2) { fprintf(stderr, "usage: bramble FILE.cnf [options]\n"); return 2; }
    Config cfg;
    for (int i = 2; i < argc; i++) {
        const char* a = argv[i];
        auto opt = [&](const char* name) -> const char* {
            size_t k = strlen(name);
            return strncmp(a, name, k) == 0 && a[k] == '=' ? a + k + 1 : nullptr;
        };
        if (const char* v = opt("--P")) cfg.P = atoi(v);
        else if (const char* v = opt("--heads")) cfg.head_words = atoi(v);
        else if (const char* v = opt("--mhz")) cfg.mhz = atof(v);
        else if (const char* v = opt("--limit")) cfg.limit_s = atof(v);
        else if (const char* v = opt("--seed")) cfg.seed = strtoull(v, nullptr, 10);
        else if (const char* v = opt("--arena")) cfg.arena_words = atol(v);
        else if (const char* v = opt("--bram")) cfg.bram = atoi(v);
        else if (const char* v = opt("--stable")) cfg.stable = !strcmp(v, "off") ? 0 : !strcmp(v, "vsids") ? 2 : 1;
        else if (!strcmp(a, "--check")) cfg.check = true;
        else if (!strcmp(a, "--no-sls")) cfg.sls = false;
        else if (!strcmp(a, "--no-gauss")) cfg.gauss = false;
        else if (const char* v = opt("--vivify")) cfg.vivify = atof(v);
        else if (!strcmp(a, "-v")) cfg.verbose = true;
        else { fprintf(stderr, "unknown option %s\n", a); return 2; }
    }
    Formula f;
    if (!read_dimacs(argv[1], f)) { fprintf(stderr, "cannot read %s\n", argv[1]); return 2; }
    Solver s(cfg, f);
    int r = s.solve();
    const char* res = r == 10 ? "SAT" : r == 20 ? "UNSAT" : r == -1 ? "REJECTED" : s.memout ? "MEMOUT" : "UNKNOWN";
    bool ok = true;
    if (r == 10) ok = check_model(f, s.model);
    double secs = s.cycles / (cfg.mhz * 1e6);
    printf("result %s%s time_s %.4f cycles %" PRIu64 " conflicts %" PRIu64 " decisions %" PRIu64
           " props %" PRIu64 " P %d sls %s%s\n",
           res, ok ? "" : "_INVALID", secs, s.cycles, s.st.conflicts, s.st.decisions, s.st.propagations,
           s.P_active, cfg.sls ? (s.walker_dropped ? "dropped" : "on") : "off", s.from_walker ? " by_walker" : s.by_gauss ? " by_gauss" : "");
    Bram br = bram_estimate(s, f);
    fprintf(stderr, "bram: %d blocks (per-var %.0f, banks %.0f, binaries %.0f, walker %.0f, gauss %.0f borrowed)\n",
            br.total, br.per_var, br.banks, br.binaries, br.walker, br.gauss);
    if (cfg.gauss && s.gr.xors)
        fprintf(stderr, "gauss: %d xors, %d units, %d equivalences, %" PRIu64 " cycles%s\n", s.gr.xors, s.gr.units,
                s.gr.equivs, s.gr.cycles, s.gr.unsat ? ", inconsistent" : "");
    if (cfg.verbose) {
        auto& t = s.st;
        printf("cycles: bcp %" PRIu64 " analyze %" PRIu64 " decide %" PRIu64 " backtrack %" PRIu64 " reduce %" PRIu64
               " other %" PRIu64 "\n", t.cyc_bcp, t.cyc_analyze, t.cyc_decide, t.cyc_backtrack, t.cyc_reduce, t.cyc_other);
        printf("restarts %" PRIu64 " reduces %" PRIu64 " (forced %" PRIu64 ") learned %" PRIu64 " deleted %" PRIu64
               " rephases %" PRIu64 " (walk %" PRIu64 ") checked %" PRIu64 " walker_flips %" PRIu64 "\n",
               t.restarts, t.reduces, t.forced_reduces, t.learned, t.deleted, t.rephases, t.walk_rephases, t.checked,
               t.walker_flips);
        printf("vivify: tried %" PRIu64 " shrunk %" PRIu64 " literals removed %" PRIu64 " units %" PRIu64 " cycles %" PRIu64 "\n",
               t.viv_tried, t.viv_shrunk, t.viv_lits_removed, t.viv_units, t.cyc_vivify);
    }
    return ok ? (r == 10 ? 10 : r == 20 ? 20 : 0) : 4;
}
