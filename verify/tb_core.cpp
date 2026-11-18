// Drive the CDCL core directly: stream the clauses, start, and RUP-check every learned clause the hardware emits on
// its debug port as it emits it. Input file: "nvars nclauses nlits" then the stream words.
// Prints: RESULT <0|1|2|rejected> CYCLES n CONFLICTS n LEARNED n CHECKED n, then MODEL for SAT.
// Exit code 3: a learned clause failed the RUP check. 4: the SAT model is wrong.
#include "Vcore.h"
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

static Vcore* d;
static uint64_t cyc = 0;

static void tick() { d->clk = 0; d->eval(); d->clk = 1; d->eval(); cyc++; }

// ---- RUP checker (the model's, over DIMACS literals)
struct Checker {
    int n;
    std::vector<std::vector<int>> cls;
    std::vector<std::vector<int>> occ;   // index (2*(v-1) + neg) -> clause ids
    explicit Checker(int nv) : n(nv), occ(2 * nv + 2) {}
    static int ix(int l) { return l > 0 ? 2 * (l - 1) : 2 * (-l - 1) + 1; }
    void add(const std::vector<int>& c0) {   // duplicate literals merged; a tautology is always satisfied: dropped
        std::vector<int> c;
        for (int l : c0) {
            bool dup = false;
            for (int x : c) { if (x == l) dup = true; if (x == -l) return; }
            if (!dup) c.push_back(l);
        }
        int id = (int)cls.size(); cls.push_back(c);
        for (int l : c) occ[ix(l)].push_back(id);
    }
    bool rup(const std::vector<int>& c) const {
        std::vector<int8_t> val(n + 1, 0);
        std::vector<int> q;
        auto lv = [&](int l) { int v = val[abs(l)]; return l > 0 ? v : -v; };
        auto set = [&](int l) { if (lv(l) == 1) return true; if (lv(l) == -1) return false; val[abs(l)] = l > 0 ? 1 : -1; q.push_back(l); return true; };
        for (int l : c) if (!set(-l)) return true;
        auto check = [&](int id) {   // 0 ok, 1 conflict
            int unk = 0, last = 0;
            for (int l : cls[id]) { int x = lv(l); if (x == 1) return 0; if (x == 0) { unk++; last = l; } }
            if (unk == 0) return 1;
            if (unk == 1 && !set(last)) return 1;
            return 0;
        };
        for (size_t i = 0; i < cls.size(); i++) if (check((int)i)) return true;
        for (size_t h = 0; h < q.size(); h++) for (int id : occ[ix(-q[h])]) if (check(id)) return true;
        return false;
    }
};

int main(int argc, char** argv) {
    FILE* f = fopen(argv[1], "r");
    long long max_cycles = argc > 2 ? atoll(argv[2]) : 2000000000LL;
    bool check = argc > 3 && atoi(argv[3]);
    int nv, nc, nl;
    if (fscanf(f, "%d %d %d", &nv, &nc, &nl) != 3) return 1;
    std::vector<int> words; int x;
    while (fscanf(f, "%d", &x) == 1) words.push_back(x);
    std::vector<std::vector<int>> clauses; { std::vector<int> c; for (int w : words) { if (w) c.push_back(w); else { clauses.push_back(c); c.clear(); } } }
    Checker chk(nv);
    if (check) for (auto& c : clauses) chk.add(c);

    d = new Vcore;
    d->rst = 1; tick(); tick(); d->rst = 0;
    d->nvars = nv;
    while (!d->load_ready) tick();
    for (int w : words) {
        while (!d->load_ready) tick();
        d->load_data = (uint32_t)w; d->load_valid = 1; tick(); d->load_valid = 0;
    }
    d->start = 1; tick(); d->start = 0;
    uint64_t t0 = cyc, learned = 0, checked = 0;
    std::vector<int> cur;
    while (!d->done && !d->rejected) {
        tick();
        if (d->dbg_learn_valid) { int l = d->dbg_learn_lit; cur.push_back((l & 1) ? -((l >> 1) + 1) : (l >> 1) + 1); }
        if (d->dbg_learn_end) {
            learned++;
            if (check) {
                if (!chk.rup(cur)) {
                    printf("CHECK FAILED: learned clause %llu is not RUP:", (unsigned long long)learned);
                    for (int l : cur) printf(" %d", l);
                    printf("\n"); return 3;
                }
                chk.add(cur); checked++;
            }
            cur.clear();
        }
        if ((long long)(cyc - t0) > max_cycles) break;
    }
    if (d->rejected) { printf("RESULT rejected CYCLES %llu\n", (unsigned long long)(cyc - t0)); return 0; }
    if (!d->done) { printf("RESULT timeout CYCLES %llu CONFLICTS %u LEARNED %llu CHECKED %llu\n", (unsigned long long)(cyc - t0), d->conflicts, (unsigned long long)learned, (unsigned long long)checked); return 0; }
    int res = d->result;
    printf("RESULT %d CYCLES %llu CONFLICTS %u DECISIONS %u LEARNED %llu CHECKED %llu INFO 0x%x\n", res,
           (unsigned long long)(cyc - t0), d->conflicts, d->decisions, (unsigned long long)learned, (unsigned long long)checked, d->info);
    if (res == 1) {
        std::vector<int> model(nv + 1, 0);
        for (int v = 0; v < nv; v++) { d->model_addr = v; tick(); tick(); model[v + 1] = d->model_val ? 1 : -1; }
        for (auto& c : clauses) {
            bool ok = false;
            for (int l : c) if ((l > 0) == (model[abs(l)] == 1)) { ok = true; break; }
            if (!ok) { printf("MODEL INVALID\n"); return 4; }
        }
        printf("MODEL OK\n");
    }
    return 0;
}
