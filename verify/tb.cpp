// Drive the entry over Wishbone the way the runner does: abort, sizes, clause stream, start, poll, model.
// Input file: "nvars nclauses nlits" then the stream words. Prints status, result, info, cycles and the model.
#include "Ventry.h"
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

static Ventry* d;
static uint64_t cyc = 0;

static void tick() {
    d->clk = 0; d->eval();
    d->clk = 1; d->eval();
    cyc++;
}

static uint32_t wb(int adr, bool we, uint32_t data = 0) {
    d->wb_adr = adr; d->wb_we = we; d->wb_dat_w = data; d->wb_sel = 0xF; d->wb_cyc = 1; d->wb_stb = 1;
    for (long i = 0;; i++) {
        tick();
        if (d->wb_ack) break;
        if (i > 50000000) { fprintf(stderr, "no ack at adr %d\n", adr); exit(2); }
    }
    uint32_t v = d->wb_dat_r;
    tick();                       // the master holds the request through the edge that ends the ack cycle
    d->wb_cyc = 0; d->wb_stb = 0;
    tick();
    return v;
}

int main(int argc, char** argv) {
    FILE* f = fopen(argv[1], "r");
    long long max_cycles = argc > 2 ? atoll(argv[2]) : 2000000000LL;
    int nv, nc, nl;
    if (fscanf(f, "%d %d %d", &nv, &nc, &nl) != 3) return 1;
    std::vector<int32_t> words;
    int x;
    while (fscanf(f, "%d", &x) == 1) words.push_back(x);
    d = new Ventry;
    d->rst = 1; tick(); tick(); d->rst = 0;
    wb(0, true, 2);                                   // ABORT
    for (int i = 0; i < 100000 && wb(1, false) != 0; i++) {}
    wb(3, true, nv); wb(4, true, nc); wb(5, true, nl);
    for (int32_t w : words) wb(6, true, (uint32_t)w);
    wb(0, true, 1);                                   // START
    uint64_t t0 = cyc;
    uint32_t st = 0;
    while (true) {
        st = wb(1, false);
        if (st & 6) break;
        for (int i = 0; i < 1000; i++) tick();
        if ((long long)(cyc - t0) > max_cycles) { printf("TIMEOUT cycles %llu\n", (unsigned long long)(cyc - t0)); return 0; }
    }
    uint32_t res = wb(2, false), info = wb(15, false);
    printf("STATUS %u RESULT %u INFO %u CYCLES %llu\n", st, res, info, (unsigned long long)(cyc - t0));
    if (res == 1) {
        printf("MODEL");
        for (int i = 0; i < nv; i++) printf(" %d", (int32_t)wb(256, false));
        printf("\n");
    }
    return 0;
}
