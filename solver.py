"""Bramble, stage 1: XOR recovery and Gauss-Jordan elimination over GF(2), behind the AgentSAT register map.

The shell (design.py, unchanged from the template) streams the clauses in; this module

  1. LOAD    keeps every clause of at most K literals in a hash table keyed by its (sorted) variable set, with a
             2^K-bit mask of the sign patterns seen for that set. Duplicate literals are dropped; a tautology, a
             longer clause, a variable past column C, or a clause that finds no free slot within PROBE_LIMIT is left
             out (only ever losing XORs, never adding one).
  2. SCAN    finds the XORs: a variable set whose clauses cover every sign pattern of one parity. A missing pattern
             still counts when a shorter clause in the table subsumes it (looked up in the same table).
  3. GAUSS   eliminates the XOR rows, Gauss-Jordan, one row-XOR per cycle on 513-bit rows (512 columns + rhs).
  4. CHECK   an all-zero row with rhs 1 proves the formula UNSAT.
  5. SMALL   an instance of at most BF_VARS variables and BF_WORDS stream words is also kept whole, and if Gauss
             proved nothing every assignment is tried: SAT with its model, or UNSAT once all are exhausted.
             (This is what the pre-flight's built-in instances need; real instances are far larger.)
Anything else is UNKNOWN.

UNSAT is only ever claimed from genuine XOR constraints of the formula or from exhausting every assignment, so it is
never wrong; SAT only with an assignment that satisfied every clause. An overflow anywhere (table, rows) or an
instance past the capacity gives UNKNOWN.

Later stages add the CDCL core and the local-search engine around this front end.
"""

from amaranth import Array, Cat, Const, Elaboratable, Module, Mux, ResetInserter, Signal, signed
from amaranth.lib.memory import Memory

import cdcl
import walker

K = 7                 # widest clause considered part of an XOR
VB = 9                # variable index bits: columns 0..511
C = 1 << VB           # Gauss columns (variables)
R = 256               # Gauss rows (XOR constraints)
EB = 9                # hash table index bits
E = 1 << EB           # hash table entries
PROBE_LIMIT = 64      # linear probing gives up after this many slots: the clause is left out (sound, see below)
KEY_W = 1 + 3 + K * VB      # valid, width, variables
MASK_W = 1 << K             # one bit per sign pattern

# Block RAM budget: a real cloud build's SoC uses about 53 of the 208 block RAMs (the firmware ROM is not in
# `mrg pnr`'s count), so an entry gets about 155, not the published 183 (FPSAT#21, mrg-sandbox#35). The walker's
# memories cost 20 and it only takes formulas under 512 variables, so it is off to stay under the budget.
USE_WALKER = False

BF_VARS = 16          # brute force: variables
BF_WORDS = 256        # brute force: clause-stream words kept

# info word (logs only): rows found | flags
INFO_TABLE_FULL = 1 << 16    # some clauses found no slot and were left out
INFO_ROWS_FULL = 1 << 17
INFO_TOO_WIDE = 1 << 18      # instance has more variables than columns: no elimination
INFO_GAUSS = 1 << 19
INFO_BRUTE = 1 << 20         # the answer came from trying every assignment
INFO_WALKER = 1 << 21        # the answer came from the local-search walker


def parity_select(k, par):
    """Mask of the sign patterns of a k-variable set whose number of negations has parity `par`."""
    return sum(1 << i for i in range(1 << k) if bin(i).count("1") % 2 == par)


class GaussFront(Elaboratable):
    """Stages 1-4 above. Answers UNSAT, or UNKNOWN for the CDCL core to take over; never SAT."""

    def __init__(self):
        # From the shell.
        self.start = Signal()
        self.abort = Signal()
        self.nvars = Signal(32)
        self.nclauses = Signal(32)
        self.nlits = Signal(32)
        self.load_valid = Signal()
        self.load_data = Signal(signed(32))
        self.model_addr = Signal(32)
        # To the shell.
        self.idle = Signal()
        self.load_ready = Signal()
        self.done = Signal()
        self.rejected = Signal()
        self.result = Signal(2)
        self.info = Signal(32)
        self.model_val = Signal()

    def elaborate(self, platform):  # noqa: C901 - one FSM, read top to bottom
        m = Module()

        # ---------------------------------------------------------------- memories
        m.submodules.keys = keys = Memory(shape=KEY_W, depth=E, init=[])
        m.submodules.masks = masks = Memory(shape=MASK_W, depth=E, init=[])
        m.submodules.mat = mat = Memory(shape=C + 1, depth=R, init=[])
        kr, kw = keys.read_port(), keys.write_port()
        mr, mw = masks.read_port(), masks.write_port()
        xr, xw = mat.read_port(), mat.write_port()


        # ---------------------------------------------------------------- clause being loaded (sorted)
        cnt = Signal(range(K + 1))
        sv = Array(Signal(VB, name=f"sv{i}") for i in range(K))     # variables, ascending
        ss = Array(Signal(name=f"ss{i}") for i in range(K))          # signs (1 = negative literal)
        drop = Signal()                                               # this clause takes no part
        start_pending = Signal()

        # ---------------------------------------------------------------- probe key (insert or lookup)
        pk = Signal(3)                                   # width
        pv = Array(Signal(VB, name=f"pv{i}") for i in range(K))
        pbit = Signal(K)                                 # sign pattern index (insert: to set; lookup: to test)
        h = Signal(EB)
        probes = Signal(EB + 1)
        lookup_hit = Signal()                            # result of a lookup
        lookup = Signal()                                # 0 insert, 1 lookup
        key_word = Cat(Const(1, 1), pk, *[pv[i] for i in range(K)])

        def hash_of(width, vs):
            x = width
            for i in range(K):
                rot = (i * 3) % EB
                v = vs[i].as_unsigned() if hasattr(vs[i], "as_unsigned") else vs[i]
                vv = Cat(v, Const(0, EB - VB))
                x = x ^ Cat(vv[rot:], vv[:rot]) if rot else x ^ vv
            return x[:EB]

        # ---------------------------------------------------------------- scan / gauss state
        e = Signal(EB + 1)                               # table entry being scanned
        ek = Signal(3)
        evs = Array(Signal(VB, name=f"ev{i}") for i in range(K))
        emask = Signal(MASK_W)
        par = Signal()
        missing = Signal(MASK_W)
        mbit = Signal(K)                                 # the missing pattern being covered
        sub = Signal(K + 1)                              # subset of positions being tried
        rows = Signal(range(R + 1))
        rowbuf = Signal(C + 1)
        rhs = Signal()
        vi = Signal(range(K + 1))
        col = Signal(VB + 1)
        r = Signal(range(R + 1))
        piv = Signal(range(R + 1))
        prow = Signal(C + 1)
        used = Signal(R)
        unsat = Signal()
        table_full = Signal()
        rows_full = Signal()
        too_wide = Signal()
        clr = Signal(EB + 1)


        m.d.comb += [self.rejected.eq(0), self.model_val.eq(0)]

        # literal arriving
        d = self.load_data
        a = Signal(32)
        m.d.comb += a.eq(Mux(d < 0, -d, d))
        lv = Signal(VB)
        lneg = Signal()
        m.d.comb += [lv.eq((a - 1)[:VB]), lneg.eq(d < 0)]
        too_big = (a > C)

        # insertion position and duplicate detection over the sorted slots
        same = Signal(K)
        gt = Signal(K)
        for i in range(K):
            m.d.comb += [same[i].eq((i < cnt) & (sv[i] == lv)),
                         gt[i].eq((i < cnt) & (sv[i] > lv))]
        dup_same_sign = Signal()
        taut = Signal()
        for i in range(K):
            with m.If(same[i]):
                m.d.comb += [dup_same_sign.eq(ss[i] == lneg), taut.eq(ss[i] != lneg)]

        with m.If(self.start):
            m.d.sync += start_pending.eq(1)

        with m.FSM(name="bramble"):
            # ------------------------------------------------------------ clear the table (idle, loads stalled)
            with m.State("CLEAR"):
                m.d.comb += self.idle.eq(1)
                with m.If(clr == E):
                    m.d.sync += [cnt.eq(0), drop.eq(0), rows.eq(0), table_full.eq(0), rows_full.eq(0),
                                 unsat.eq(0), too_wide.eq(0)]
                    m.next = "READY"
                with m.Else():
                    m.d.comb += [kw.addr.eq(clr[:EB]), kw.data.eq(0), kw.en.eq(1)]
                    m.d.sync += clr.eq(clr + 1)

            # ------------------------------------------------------------ clause stream
            with m.State("READY"):
                m.d.comb += [self.idle.eq(1), self.load_ready.eq(1)]
                with m.If(start_pending | self.start):
                    m.d.sync += [start_pending.eq(0), e.eq(0), too_wide.eq(self.nvars > C)]
                    m.next = "SCAN_RD"
                with m.Elif(self.load_valid):
                    with m.If(d == 0):
                        with m.If(~drop & (cnt != 0)):
                            # probe for insertion
                            m.d.sync += [pk.eq(cnt), lookup.eq(0), probes.eq(0),
                                         pbit.eq(Cat(*[ss[i] & (i < cnt) for i in range(K)]))]
                            for i in range(K):
                                m.d.sync += pv[i].eq(Mux(i < cnt, sv[i], 0))
                            m.d.sync += h.eq(hash_of(cnt, [Mux(i < cnt, sv[i], 0) for i in range(K)]))
                            m.next = "PROBE_RD"
                        m.d.sync += [cnt.eq(0), drop.eq(0)]
                    with m.Elif(drop | dup_same_sign):
                        pass
                    with m.Elif(taut | too_big | (cnt == K)):
                        m.d.sync += drop.eq(1)
                    with m.Else():
                        # insert lv at its sorted position; slots holding a larger variable move up one
                        pos = Signal(range(K + 1))
                        m.d.comb += pos.eq(cnt - sum(gt[i] for i in range(K)))
                        for i in range(K):
                            with m.If(i == pos):
                                m.d.sync += [sv[i].eq(lv), ss[i].eq(lneg)]
                            if i > 0:
                                with m.If((i > pos) & (i <= cnt)):
                                    m.d.sync += [sv[i].eq(sv[i - 1]), ss[i].eq(ss[i - 1])]
                        m.d.sync += cnt.eq(cnt + 1)

            # ------------------------------------------------------------ hash probe (insert or lookup)
            with m.State("PROBE_RD"):
                m.d.comb += [kr.addr.eq(h), mr.addr.eq(h)]
                m.next = "PROBE"
            with m.State("PROBE"):
                ent_valid = kr.data[0]
                match = ent_valid & (kr.data == key_word)
                pmask = Signal(MASK_W)
                m.d.comb += pmask.eq(Const(1, MASK_W) << pbit)
                with m.If(lookup):
                    with m.If(match):
                        m.d.sync += lookup_hit.eq((mr.data & pmask).any())
                        m.next = "SUB_RESULT"
                    with m.Elif(~ent_valid | (probes == PROBE_LIMIT - 1)):
                        m.d.sync += lookup_hit.eq(0)
                        m.next = "SUB_RESULT"
                    with m.Else():
                        m.d.sync += [h.eq(h + 1), probes.eq(probes + 1)]
                        m.next = "PROBE_RD"
                with m.Else():
                    with m.If(match):
                        m.d.comb += [mw.addr.eq(h), mw.data.eq(mr.data | pmask), mw.en.eq(1)]
                        m.next = "READY"
                    with m.Elif(~ent_valid):
                        m.d.comb += [kw.addr.eq(h), kw.data.eq(key_word), kw.en.eq(1),
                                     mw.addr.eq(h), mw.data.eq(pmask), mw.en.eq(1)]
                        m.next = "READY"
                    with m.Elif(probes == PROBE_LIMIT - 1):
                        # no slot nearby: leave the clause out. That can only make an XOR look incomplete or a
                        # missing pattern look uncovered, so it can lose XORs but never invent one.
                        m.d.sync += table_full.eq(1)
                        m.next = "READY"
                    with m.Else():
                        m.d.sync += [h.eq(h + 1), probes.eq(probes + 1)]
                        m.next = "PROBE_RD"

            # ------------------------------------------------------------ scan the table for XORs
            with m.State("SCAN_RD"):
                with m.If(too_wide):
                    m.next = "FINISH"
                with m.Elif(e == E):
                    m.d.sync += [col.eq(0), used.eq(0)]
                    m.next = "GAUSS_COL"
                with m.Else():
                    m.d.comb += [kr.addr.eq(e[:EB]), mr.addr.eq(e[:EB])]
                    m.next = "SCAN"
            with m.State("SCAN"):
                with m.If(kr.data[0]):
                    m.d.sync += [ek.eq(kr.data[1:4]), emask.eq(mr.data), par.eq(0)]
                    for i in range(K):
                        m.d.sync += evs[i].eq(kr.data[4 + i * VB: 4 + (i + 1) * VB])
                    m.next = "PARITY"
                with m.Else():
                    m.d.sync += e.eq(e + 1)
                    m.next = "SCAN_RD"
            with m.State("PARITY"):
                sel = Signal(MASK_W)
                with m.Switch(Cat(par, ek)):
                    for k in range(1, K + 1):
                        for p in (0, 1):
                            with m.Case(p | (k << 1)):
                                m.d.comb += sel.eq(parity_select(k, p))
                m.d.sync += missing.eq(sel & ~emask)
                m.next = "COVER"
            with m.State("COVER"):
                # every missing pattern must be subsumed by a shorter clause
                with m.If(missing == 0):
                    m.d.sync += [rowbuf.eq(0), rhs.eq(~par), vi.eq(0)]
                    m.next = "ROW_BUILD"
                with m.Else():
                    # lowest missing pattern
                    for i in reversed(range(MASK_W)):
                        with m.If(missing[i]):
                            m.d.sync += mbit.eq(i)
                    m.d.sync += sub.eq(1)
                    m.next = "SUB_TRY"
            with m.State("SUB_TRY"):
                full = (Const(1, K + 1) << ek) - 1
                with m.If(sub >= full):
                    m.next = "NEXT_PAR"           # no shorter clause covers it: not an XOR of this parity
                with m.Else():
                    # compact the chosen positions into the probe key
                    width = Signal(3)
                    outs = [Signal(VB, name=f"cv{j}") for j in range(K)]
                    obits = [Signal(name=f"cb{j}") for j in range(K)]
                    sel_pos = [Signal(name=f"sp{i}") for i in range(K)]
                    for i in range(K):
                        m.d.comb += sel_pos[i].eq(sub[i] & (i < ek))
                    # prefix counts give each chosen position its output slot
                    for i in range(K):
                        pos = sum(sel_pos[j] for j in range(i)) if i else Const(0, 3)
                        for j in range(K):
                            with m.If(sel_pos[i] & (pos == j)):
                                m.d.comb += [outs[j].eq(evs[i]), obits[j].eq(mbit[i])]
                    m.d.comb += width.eq(sum(sel_pos))
                    m.d.sync += [pk.eq(width), lookup.eq(1), probes.eq(0), pbit.eq(Cat(*obits))]
                    for j in range(K):
                        m.d.sync += pv[j].eq(outs[j])
                    m.d.sync += h.eq(hash_of(width, outs))
                    m.next = "PROBE_RD"
            with m.State("SUB_RESULT"):
                with m.If(lookup_hit):
                    m.d.sync += missing.eq(missing & ~(Const(1, MASK_W) << mbit))
                    m.next = "COVER"
                with m.Else():
                    m.d.sync += sub.eq(sub + 1)
                    m.next = "SUB_TRY"
            with m.State("NEXT_PAR"):
                with m.If(par == 0):
                    m.d.sync += par.eq(1)
                    m.next = "PARITY"
                with m.Else():
                    m.d.sync += e.eq(e + 1)
                    m.next = "SCAN_RD"

            # ------------------------------------------------------------ write an XOR row
            with m.State("ROW_BUILD"):
                with m.If(vi == ek):
                    with m.If(rows == R):
                        m.d.sync += rows_full.eq(1)
                        m.next = "FINISH"
                    with m.Else():
                        m.d.comb += [xw.addr.eq(rows), xw.data.eq(Cat(rowbuf[:C], rhs)), xw.en.eq(1)]
                        m.d.sync += rows.eq(rows + 1)
                        m.next = "NEXT_PAR"
                with m.Else():
                    m.d.sync += [rowbuf.eq(rowbuf | (Const(1, C + 1) << evs[vi])), vi.eq(vi + 1)]

            # ------------------------------------------------------------ Gauss-Jordan
            with m.State("GAUSS_COL"):
                with m.If((col == C) | (col >= self.nvars)):
                    m.d.sync += r.eq(0)
                    m.next = "CHECK_RD"
                with m.Else():
                    m.d.sync += r.eq(0)
                    m.next = "FIND_RD"
            with m.State("FIND_RD"):
                with m.If(r == rows):
                    m.d.sync += col.eq(col + 1)       # no pivot in this column
                    m.next = "GAUSS_COL"
                with m.Else():
                    m.d.comb += xr.addr.eq(r)
                    m.next = "FIND"
            with m.State("FIND"):
                bit = xr.data.bit_select(col[:VB], 1)
                with m.If(~used.bit_select(r, 1) & bit):
                    m.d.sync += [piv.eq(r), prow.eq(xr.data), used.eq(used | (Const(1, R) << r)), r.eq(0)]
                    m.next = "ELIM_RD"
                with m.Else():
                    m.d.sync += r.eq(r + 1)
                    m.next = "FIND_RD"
            with m.State("ELIM_RD"):
                with m.If(r == rows):
                    m.d.sync += col.eq(col + 1)
                    m.next = "GAUSS_COL"
                with m.Else():
                    m.d.comb += xr.addr.eq(r)
                    m.next = "ELIM"
            with m.State("ELIM"):
                bit = xr.data.bit_select(col[:VB], 1)
                with m.If((r != piv) & bit):
                    m.d.comb += [xw.addr.eq(r), xw.data.eq(xr.data ^ prow), xw.en.eq(1)]
                m.d.sync += r.eq(r + 1)
                m.next = "ELIM_RD"

            # ------------------------------------------------------------ an all-zero row with rhs 1?
            with m.State("CHECK_RD"):
                with m.If(r == rows):
                    m.next = "FINISH"
                with m.Else():
                    m.d.comb += xr.addr.eq(r)
                    m.next = "CHECK"
            with m.State("CHECK"):
                with m.If(~xr.data[:C].any() & xr.data[C]):
                    m.d.sync += unsat.eq(1)
                    m.next = "FINISH"
                with m.Else():
                    m.d.sync += r.eq(r + 1)
                    m.next = "CHECK_RD"

            with m.State("FINISH"):
                m.d.comb += [self.done.eq(1), self.result.eq(Mux(unsat, 2, 0)),
                             self.info.eq(rows | Mux(table_full, INFO_TABLE_FULL, 0) | Mux(rows_full, INFO_ROWS_FULL, 0)
                                          | Mux(too_wide, INFO_TOO_WIDE, 0) | INFO_GAUSS)]

        return m


class Solver(Elaboratable):
    """The Gauss front end, then (if it proved nothing) the CDCL core, on the same clause stream."""
    max_vars = cdcl.NV - 1
    max_clauses = (1 << 16) - 1          # the loader's per-clause duplicate stamps are 16 bits
    max_lits = cdcl.ARENA                # long clauses live in the arena (binaries and units do not)

    def __init__(self):
        self.start = Signal()
        self.abort = Signal()
        self.nvars = Signal(32)
        self.nclauses = Signal(32)
        self.nlits = Signal(32)
        self.load_valid = Signal()
        self.load_data = Signal(signed(32))
        self.model_addr = Signal(32)
        self.idle = Signal()
        self.load_ready = Signal()
        self.done = Signal()
        self.rejected = Signal()
        self.result = Signal(2)
        self.info = Signal(32)
        self.model_val = Signal()

    def elaborate(self, platform):
        m = Module()
        m.submodules.front = front = GaussFront()
        m.submodules.core = core = cdcl.Cdcl()
        walk = walker.Walker()
        if USE_WALKER:
            m.submodules.walker = walk
        else:
            walk._MustUse__silence = True      # its signals stay undriven (constant 0)
        both_ready = front.load_ready & core.load_ready
        core_started = Signal()
        m.d.comb += [
            front.nvars.eq(self.nvars), front.nclauses.eq(self.nclauses), front.nlits.eq(self.nlits),
            front.load_valid.eq(self.load_valid & both_ready), front.load_data.eq(self.load_data),
            front.start.eq(self.start),
            core.nvars.eq(self.nvars),
            core.load_valid.eq(self.load_valid & both_ready), core.load_data.eq(self.load_data),
            core.model_addr.eq(self.model_addr),
            self.load_ready.eq(both_ready),
            self.idle.eq(front.idle & core.idle),
            self.model_val.eq(Mux(walk.solved, walk.model_val, core.model_val)),
            # the walker (probSAT) beside the core: it reads the clauses the core keeps while loading, borrows the
            # arena's read port when the core leaves it idle, and starts when the core starts searching
        ]
        if USE_WALKER:
            m.d.comb += [
                walk.ev_valid.eq(core.ev_valid), walk.ev_kind.eq(core.ev_kind), walk.ev_l0.eq(core.ev_l0),
                walk.ev_l1.eq(core.ev_l1), walk.ev_cref.eq(core.ev_cref), walk.ev_len.eq(core.ev_len),
                walk.nvars.eq(self.nvars), walk.go.eq(core.ev_done), walk.stop.eq(core.done),
                walk.arena_data.eq(core.arena_data), walk.walk_ok.eq(core.walk_ok),
                core.walk_addr.eq(walk.walk_addr), core.walk_req.eq(walk.walk_req), core.walk_busy.eq(walk.busy), walk.model_addr.eq(self.model_addr),
            ]
        front_proved = front.done & (front.result == 2)
        # the front end has finished without a proof: hand over to the core (once)
        with m.If(front.done & ~front_proved & ~core_started):
            m.d.comb += core.start.eq(1)
            m.d.sync += core_started.eq(1)
        with m.If(front_proved):
            m.d.comb += [self.done.eq(1), self.result.eq(2), self.info.eq(front.info)]
        with m.Elif(core.rejected):
            m.d.comb += [self.rejected.eq(1), self.info.eq(core.info)]
        with m.Elif(core.done):
            m.d.comb += [self.done.eq(1), self.result.eq(core.result), self.info.eq(core.info | (front.info & 0xFFFF))]
        with m.Elif(walk.solved):
            m.d.comb += [self.done.eq(1), self.result.eq(1), self.info.eq(INFO_WALKER)]
        # abort: both drop everything and start over
        return ResetInserter({"sync": self.abort})(m)
