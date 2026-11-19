"""Bramble's local-search engine (probSAT), running beside the CDCL core.

The walker's formula is the instance's clauses as the core kept them while loading (it reports each unit, binary and
long clause); long clauses are read from the core's arena, where the original clauses sit at the front and never move,
on cycles the core leaves the arena's read port idle.

Setup (after the clause stream):
  count     occurrences per literal (the long clauses read from the arena)
  prefix    counts -> end offsets
  fill      occ[--end[lit]] = clause, so `off` ends as start offsets (CSR, no extra memory)
  init      an assignment; per clause the number of true literals and the XOR of their variables (its critical
            variable while exactly one is true); break counts; the list of unsatisfied clauses
Then, until the list is empty or the solver stops:
  pick an unsatisfied clause at random; weight its literals by a probability ROM indexed by break count (probSAT's
  polynomial break function); flip one at random in proportion; update counts through the flipped variable's two
  occurrence lists. The best assignment so far is kept; the walk restarts from a fresh assignment every
  100,000 + 20 * clauses flips (the model's schedule).

Soundness: SAT is claimed only when no clause is unsatisfied by the walker's own exactly kept counts, and the model is
the walker's assignment. Anything the walker cannot hold (too many clauses or occurrences, a clause wider than MAXK)
turns it off; the core goes on alone.
"""

from amaranth import Array, Cat, Const, Elaboratable, Module, Mux, Signal
from amaranth.lib.memory import Memory

from cdcl import AAW, LB, NV as NVMAX, VB

CB = 11                 # clause index bits: WC clauses
WC = 1 << CB
OB = 12                 # occurrence index bits: WO occurrences (also the walker's literal store)
WO = 1 << OB
WVB = 9                 # the walker takes formulas of fewer than WV variables (its per-variable memories)
WV = 1 << WVB
MAXK = 64               # widest clause the walker takes
TB = 7                  # true-literal count bits (up to MAXK)
BRB = 14                # break count bits (at most WO)
NONE_POS = (1 << (CB + 1)) - 1


def ptab(cb):
    """probSAT's weights (1 + break)^-cb as 16-bit fractions, for breaks 0..63."""
    return [max(1, round(65535 * (1.0 + b) ** -cb)) for b in range(64)]


def mem(m, name, width, depth):
    mm = Memory(shape=width, depth=depth, init=[])
    m.submodules[name] = mm
    return mm.read_port(), mm.write_port()


class Walker(Elaboratable):
    def __init__(self):
        # from the core
        self.ev_valid = Signal()
        self.ev_kind = Signal(2)
        self.ev_l0 = Signal(LB)
        self.ev_l1 = Signal(LB)
        self.ev_cref = Signal(AAW)
        self.ev_len = Signal(12)
        self.nvars = Signal(32)
        self.go = Signal()                  # the core has begun solving
        self.stop = Signal()                # the solver has answered
        self.arena_data = Signal(LB)
        self.walk_ok = Signal()
        # to the core
        self.busy = Signal()                # copying the clauses: the core waits before it starts searching
        self.walk_addr = Signal(AAW)
        self.walk_req = Signal()
        # answer
        self.solved = Signal()
        self.disabled = Signal()
        self.model_addr = Signal(32)
        self.model_val = Signal()
        self.flips = Signal(32)
        self.seed = Signal(32, init=0x2545F491)

    def elaborate(self, platform):  # noqa: C901
        m = Module()
        ci_r, ci_w = mem(m, "cinfo", 2 + 2 * LB, WC)        # kind | l0 l1  or  kind | cref len
        cd_r, cd_w = mem(m, "cdyn", TB + VB, WC)            # true count | XOR of the true variables
        up_r, up_w = mem(m, "upos", CB + 1, WC)             # position in the unsat list
        un_r, un_w = mem(m, "unsat", CB, WC)
        of_r, of_w = mem(m, "off", OB + 1, 2 * WV)          # count / end / start offset per literal
        oc_r, oc_w = mem(m, "occ", CB, WO)
        av_r, av_w = mem(m, "assign", 1, WV)
        bs_r, bs_w = mem(m, "best", 1, WV)
        br_r, br_w = mem(m, "brk", BRB, WV)
        lt_r, lt_w = mem(m, "lits", LB, WO)                 # the walker's own copy of every clause, back to back
        pk_r, pk_w = mem(m, "pick", VB + 16, MAXK)          # (variable, weight) of the clause being picked from

        def var(l): return l[1:LB]

        n = Signal(VB + 1)
        nc = Signal(CB + 1)                 # clauses
        total = Signal(OB + 2)              # occurrences
        maxw = Signal(12)
        off_bad = Signal()
        nuns = Signal(CB + 1)
        best_uns = Signal(CB + 2)
        restart_at = Signal(32)
        c = Signal(CB + 1)
        k = Signal(12)
        klen = Signal(12)
        kind = Signal(2)
        l0 = Signal(LB)
        l1 = Signal(LB)
        cref = Signal(AAW)
        lit = Signal(LB)
        x = Signal(VB)
        tl = Signal(LB)
        o = Signal(OB + 2)
        oe = Signal(OB + 2)
        t = Signal(TB)
        cx = Signal(VB)
        tsum = Signal(TB)
        xsum = Signal(VB)
        wsum = Signal(23)
        rr = Signal(23)
        cc = Signal(CB)
        p = Signal(CB + 1)
        last = Signal(CB)
        phase = Signal(2)                   # mode of the clause-literal walk (count / fill / init / pick)
        rng = Signal(32)
        wl = Signal(VB + 16)
        cbsel = Signal(2)
        bv = Signal(BRB)
        a_old = Signal()
        lp = Signal(OB + 1)                 # literals stored
        lcount = Signal(OB + 5)             # literals the core announced
        cstart = Signal(OB + 1)
        i = Signal(VB + 2)

        # probability ROMs, one per probSAT exponent; the exponent follows the widest clause
        roms = [ptab(cbv) for cbv in (2.06, 3.0, 3.7, 5.1)]
        weight = Signal(16)
        bidx = Signal(6)
        with m.Switch(Cat(bidx, cbsel)):
            for s_, tab in enumerate(roms):
                for b_, v_ in enumerate(tab):
                    with m.Case(b_ | (s_ << 6)):
                        m.d.comb += weight.eq(v_)

        # xorshift32, one step a cycle: x ^= x << 13; x ^= x >> 17; x ^= x << 5 (each step cut to 32 bits)
        xa, xb, xc = Signal(32), Signal(32), Signal(32)
        m.d.comb += [xa.eq(rng ^ (rng << 13)), xb.eq(xa ^ (xa >> 17)), xc.eq(xb ^ (xb << 5))]
        m.d.sync += rng.eq(Mux(rng == 0, self.seed, xc))

        m.d.comb += [self.model_val.eq(av_r.data), self.walk_req.eq(0)]

        def lit_true(av, l): return av ^ l[0]          # assignment bit, literal: true when value != sign

        with m.FSM(name="walker"):
            # ------------------------------------------------------------ record the clauses as the core keeps them
            with m.State("LOAD"):
                with m.If(self.ev_valid):
                    with m.If(nc == WC):
                        m.d.sync += off_bad.eq(1)
                    with m.Else():
                        pay = Mux(self.ev_kind == 2, Cat(self.ev_cref, self.ev_len[:9]), Cat(self.ev_l0, self.ev_l1))
                        m.d.comb += [ci_w.addr.eq(nc), ci_w.data.eq(Cat(self.ev_kind, pay)), ci_w.en.eq(1)]
                        m.d.sync += nc.eq(nc + 1)
                        m.d.sync += lcount.eq(lcount + Mux(self.ev_kind == 2, self.ev_len, self.ev_kind + 1))
                        with m.If(lcount + Mux(self.ev_kind == 2, self.ev_len, self.ev_kind + 1) > WO):
                            m.d.sync += off_bad.eq(1)
                        with m.If((self.ev_kind == 2) & (self.ev_len > maxw)):
                            m.d.sync += maxw.eq(self.ev_len)
                        with m.If((self.ev_kind == 1) & (maxw < 2)):
                            m.d.sync += maxw.eq(2)
                with m.If(self.go):
                    m.d.comb += self.busy.eq(1)
                    m.d.sync += [n.eq(self.nvars[:VB + 1]), i.eq(0), c.eq(0), lp.eq(0)]
                    with m.If(off_bad | (maxw > MAXK) | (self.nvars == 0) | (self.nvars[:VB + 1] >= WV)
                              | (self.nvars >= NVMAX)):
                        m.d.sync += off_bad.eq(1)
                        m.next = "OFF"
                    with m.Else():
                        m.next = "CP_RD"
            # ---- copy every clause into the walker's literal store (the core waits: the arena is stable)
            with m.State("CP_RD"):
                m.d.comb += self.busy.eq(1)
                with m.If(c == nc):
                    m.d.sync += i.eq(0)
                    m.next = "CLR"
                with m.Else():
                    m.d.comb += ci_r.addr.eq(c[:CB])
                    m.next = "CP_INFO"
            with m.State("CP_INFO"):
                m.d.comb += self.busy.eq(1)
                d_ = ci_r.data
                m.d.sync += [kind.eq(d_[:2]), l0.eq(d_[2:2 + LB]), l1.eq(d_[2 + LB:2 + 2 * LB]),
                             cref.eq(d_[2:2 + AAW]), klen.eq(Mux(d_[:2] == 2, d_[2 + AAW:2 + AAW + 9],
                                                                  Mux(d_[:2] == 1, 2, 1))),
                             k.eq(0), cstart.eq(lp)]
                m.next = "CP_LIT"
            with m.State("CP_LIT"):
                m.d.comb += self.busy.eq(1)
                with m.If(k == klen):
                    m.next = "CP_END"
                with m.Elif(kind == 2):
                    m.d.comb += [self.walk_addr.eq(cref + 2 + k), self.walk_req.eq(1)]
                    m.next = "CP_ARENA"
                with m.Else():
                    m.d.comb += [lt_w.addr.eq(lp), lt_w.data.eq(Mux(k == 0, l0, l1)), lt_w.en.eq(1)]
                    m.d.sync += [lp.eq(lp + 1), k.eq(k + 1)]
            with m.State("CP_ARENA"):
                m.d.comb += self.busy.eq(1)
                with m.If(self.walk_ok):
                    m.d.comb += [lt_w.addr.eq(lp), lt_w.data.eq(self.arena_data), lt_w.en.eq(1)]
                    m.d.sync += [lp.eq(lp + 1), k.eq(k + 1)]
                    m.next = "CP_LIT"
                with m.Else():
                    m.d.comb += [self.walk_addr.eq(cref + 2 + k), self.walk_req.eq(1)]
            with m.State("CP_END"):
                m.d.comb += [self.busy.eq(1), ci_w.addr.eq(c[:CB]), ci_w.data.eq(Cat(Const(3, 2), cstart, klen[:9])),
                             ci_w.en.eq(1)]
                m.d.sync += c.eq(c + 1)
                m.next = "CP_RD"

            with m.State("CLR"):            # zero counts, break counts
                with m.If(off_bad | (maxw > MAXK) | (n == 0) | (n >= WV)):
                    m.next = "OFF"
                with m.Elif(i == 2 * WV):
                    m.d.sync += [cbsel.eq(Mux(maxw <= 3, 0, Mux(maxw <= 4, 1, Mux(maxw <= 5, 2, 3)))),
                                 c.eq(0), phase.eq(0), total.eq(0),
                                 restart_at.eq(100000 + (nc << 4) + (nc << 2))]
                    m.next = "CL_RD"
                with m.Else():
                    m.d.comb += [of_w.addr.eq(i), of_w.data.eq(0), of_w.en.eq(1)]
                    with m.If(i < WV):
                        m.d.comb += [br_w.addr.eq(i), br_w.data.eq(0), br_w.en.eq(1)]
                    m.d.sync += i.eq(i + 1)

            # ------------------------------------------------------------ walk every clause's literals
            # phase 0 count, 1 fill, 2 init (true counts); each literal goes to LIT_DO with `lit` set
            with m.State("CL_RD"):
                with m.If(c == nc):
                    with m.Switch(phase):
                        with m.Case(0):
                            m.d.sync += [i.eq(0), o.eq(0)]
                            m.next = "PREFIX_RD"
                        with m.Case(1):
                            m.d.sync += [i.eq(0)]
                            m.next = "ASSIGN"
                        with m.Case(2):
                            m.d.sync += [best_uns.eq(NONE_POS + 1)]
                            m.next = "BEST_CHK"
                with m.Else():
                    m.d.comb += ci_r.addr.eq(c[:CB])
                    m.next = "CL_INFO"
            with m.State("CL_INFO"):
                d_ = ci_r.data
                m.d.sync += [cref.eq(d_[2:2 + OB + 1]), klen.eq(d_[2 + OB + 1:2 + OB + 10]),
                             k.eq(0), tsum.eq(0), xsum.eq(0)]
                m.next = "CL_LIT"
            with m.State("CL_LIT"):
                with m.If(k == klen):
                    m.next = "CL_END"
                with m.Else():
                    m.d.comb += lt_r.addr.eq(cref + k)
                    m.next = "CL_ARENA"
            with m.State("CL_ARENA"):         # the literal, from the walker's own store
                m.d.sync += [lit.eq(lt_r.data), k.eq(k + 1)]
                m.next = "LIT_DO"
            with m.State("LIT_DO"):
                with m.Switch(phase):
                    with m.Case(0, 1):
                        m.d.comb += of_r.addr.eq(lit)
                        m.next = "LIT_OFF"
                    with m.Case(2):
                        m.d.comb += av_r.addr.eq(var(lit))
                        m.next = "LIT_AV"
            with m.State("LIT_OFF"):
                with m.If(phase == 0):
                    m.d.comb += [of_w.addr.eq(lit), of_w.data.eq(of_r.data + 1), of_w.en.eq(1)]
                    m.d.sync += total.eq(total + 1)
                with m.Else():
                    m.d.comb += [of_w.addr.eq(lit), of_w.data.eq(of_r.data - 1), of_w.en.eq(1),
                                 oc_w.addr.eq(of_r.data - 1), oc_w.data.eq(c), oc_w.en.eq(1)]
                m.next = "CL_LIT"
            with m.State("LIT_AV"):
                with m.If(lit_true(av_r.data, lit)):
                    m.d.sync += [tsum.eq(tsum + 1), xsum.eq(xsum ^ var(lit))]
                m.next = "CL_LIT"
            with m.State("CL_END"):
                with m.If(phase == 2):
                    m.d.comb += [cd_w.addr.eq(c), cd_w.data.eq(Cat(tsum, xsum)), cd_w.en.eq(1)]
                    with m.If(tsum == 0):
                        m.d.comb += [un_w.addr.eq(nuns), un_w.data.eq(c), un_w.en.eq(1),
                                     up_w.addr.eq(c), up_w.data.eq(nuns), up_w.en.eq(1)]
                        m.d.sync += nuns.eq(nuns + 1)
                        m.d.sync += c.eq(c + 1)
                        m.next = "CL_RD"
                    with m.Elif(tsum == 1):
                        m.d.comb += [up_w.addr.eq(c), up_w.data.eq(NONE_POS), up_w.en.eq(1), br_r.addr.eq(xsum)]
                        m.next = "CL_BRK"
                    with m.Else():
                        m.d.comb += [up_w.addr.eq(c), up_w.data.eq(NONE_POS), up_w.en.eq(1)]
                        m.d.sync += c.eq(c + 1)
                        m.next = "CL_RD"
                with m.Else():
                    m.d.sync += c.eq(c + 1)
                    m.next = "CL_RD"
            with m.State("CL_BRK"):          # the clause's only true literal: its variable breaks it
                m.d.comb += [br_w.addr.eq(xsum), br_w.data.eq(br_r.data + 1), br_w.en.eq(1)]
                m.d.sync += c.eq(c + 1)
                m.next = "CL_RD"

            # ------------------------------------------------------------ counts -> end offsets
            with m.State("PREFIX_RD"):
                with m.If(total > WO):
                    m.next = "OFF"
                with m.Elif(i == 2 * WV):
                    m.d.sync += [c.eq(0), phase.eq(1)]
                    m.next = "CL_RD"
                with m.Else():
                    m.d.comb += of_r.addr.eq(i)
                    m.next = "PREFIX"
            with m.State("PREFIX"):
                m.d.comb += [of_w.addr.eq(i), of_w.data.eq(o + of_r.data), of_w.en.eq(1)]
                m.d.sync += [o.eq(o + of_r.data), i.eq(i + 1)]
                m.next = "PREFIX_RD"

            # ------------------------------------------------------------ a fresh assignment, then the counts
            with m.State("ASSIGN"):
                with m.If(i == n):
                    m.d.sync += [c.eq(0), phase.eq(2), nuns.eq(0), i.eq(0)]
                    m.next = "BRK_CLR"
                with m.Else():
                    m.d.comb += [av_w.addr.eq(i), av_w.data.eq(rng[7]), av_w.en.eq(1)]
                    m.d.sync += i.eq(i + 1)
            with m.State("BRK_CLR"):
                with m.If(i == n):
                    m.d.sync += c.eq(0)
                    m.next = "CL_RD"
                with m.Else():
                    m.d.comb += [br_w.addr.eq(i), br_w.data.eq(0), br_w.en.eq(1)]
                    m.d.sync += i.eq(i + 1)

            # ------------------------------------------------------------ the walk
            with m.State("BEST_CHK"):
                with m.If(nuns == 0):
                    m.next = "SOLVED"
                with m.Elif(self.stop):
                    m.next = "OFF"
                with m.Elif(nuns < best_uns):
                    m.d.sync += [best_uns.eq(nuns), i.eq(0)]
                    m.next = "BEST_CP_RD"
                with m.Elif(self.flips >= restart_at):
                    m.d.sync += [i.eq(0), restart_at.eq(self.flips + 100000 + (nc << 4) + (nc << 2))]
                    m.next = "ASSIGN"
                with m.Else():
                    m.next = "PICK"
            with m.State("BEST_CP_RD"):
                with m.If(i == n):
                    m.next = "PICK"
                with m.Else():
                    m.d.comb += av_r.addr.eq(i)
                    m.next = "BEST_CP"
            with m.State("BEST_CP"):
                m.d.comb += [bs_w.addr.eq(i), bs_w.data.eq(av_r.data), bs_w.en.eq(1)]
                m.d.sync += i.eq(i + 1)
                m.next = "BEST_CP_RD"
            # a random unsatisfied clause
            with m.State("PICK"):
                m.d.comb += un_r.addr.eq((rng[:16] * nuns) >> 16)
                m.next = "PICK_C"
            with m.State("PICK_C"):
                m.d.sync += cc.eq(un_r.data)
                m.d.comb += ci_r.addr.eq(un_r.data)
                m.next = "PICK_INFO"
            with m.State("PICK_INFO"):
                d_ = ci_r.data
                m.d.sync += [cref.eq(d_[2:2 + OB + 1]), klen.eq(d_[2 + OB + 1:2 + OB + 10]),
                             k.eq(0), wsum.eq(0)]
                m.next = "PK_LIT"
            with m.State("PK_LIT"):
                with m.If(k == klen):
                    m.d.sync += [rr.eq((rng[:16] * wsum) >> 16), k.eq(0)]
                    m.next = "SEL_RD"
                with m.Else():
                    m.d.comb += lt_r.addr.eq(cref + k)
                    m.next = "PK_ARENA"
            with m.State("PK_ARENA"):
                m.d.sync += lit.eq(lt_r.data)
                m.d.comb += br_r.addr.eq(var(lt_r.data))
                m.next = "PK_W"
            with m.State("PK_W"):
                m.d.comb += bidx.eq(Mux(br_r.data > 63, 63, br_r.data[:6]))
                m.d.comb += [pk_w.addr.eq(k), pk_w.data.eq(Cat(var(lit), weight)), pk_w.en.eq(1)]
                m.d.sync += [wsum.eq(wsum + weight), k.eq(k + 1)]
                m.next = "PK_LIT"
            # the literal whose weight interval holds rr
            with m.State("SEL_RD"):
                m.d.comb += pk_r.addr.eq(k)
                m.next = "SEL"
            with m.State("SEL"):
                w_ = pk_r.data[VB:]
                with m.If((rr < w_) | (k + 1 == klen)):
                    m.d.sync += [x.eq(pk_r.data[:VB])]
                    m.d.comb += av_r.addr.eq(pk_r.data[:VB])
                    m.next = "FLIP"
                with m.Else():
                    m.d.sync += [rr.eq(rr - w_), k.eq(k + 1)]
                    m.next = "SEL_RD"

            # ------------------------------------------------------------ flip x
            with m.State("FLIP"):
                m.d.comb += [av_w.addr.eq(x), av_w.data.eq(~av_r.data), av_w.en.eq(1)]
                # tl: x's literal that was true and is now false
                m.d.sync += [a_old.eq(av_r.data), tl.eq(Cat(~av_r.data, x)), self.flips.eq(self.flips + 1)]
                m.d.comb += of_r.addr.eq(Cat(~av_r.data, x))
                m.next = "F_OFF_A"
            with m.State("F_OFF_A"):          # occ[tl] runs from off[tl] to off[tl + 1] (or the end)
                m.d.sync += o.eq(of_r.data)
                m.d.comb += of_r.addr.eq(tl + 1)
                m.next = "F_OFF_B"
            with m.State("F_OFF_B"):
                m.d.sync += [oe.eq(Mux(tl == 2 * n - 1, total, of_r.data)), phase.eq(0)]
                m.next = "F_OCC_RD"
            # phase 0: clauses that lost a true literal (occ[tl]); phase 1: that gained one (occ[tl ^ 1])
            with m.State("F_OCC_RD"):
                with m.If(o == oe):
                    with m.If(phase == 0):
                        m.d.sync += phase.eq(1)
                        m.d.comb += of_r.addr.eq(tl ^ 1)
                        m.next = "F_OFF2_A"
                    with m.Else():
                        m.next = "BEST_CHK"
                with m.Else():
                    m.d.comb += oc_r.addr.eq(o)
                    m.next = "F_OCC"
            with m.State("F_OFF2_A"):
                m.d.sync += o.eq(of_r.data)
                m.d.comb += of_r.addr.eq((tl ^ 1) + 1)
                m.next = "F_OFF2_B"
            with m.State("F_OFF2_B"):
                m.d.sync += oe.eq(Mux((tl ^ 1) == 2 * n - 1, total, of_r.data))
                m.next = "F_OCC_RD"
            with m.State("F_OCC"):
                m.d.sync += [cc.eq(oc_r.data), o.eq(o + 1)]
                m.d.comb += cd_r.addr.eq(oc_r.data)
                m.next = "F_CD"
            with m.State("F_CD"):
                t0, cx0 = cd_r.data[:TB], cd_r.data[TB:]
                with m.If(phase == 0):
                    nt = (t0 - 1)[:TB]
                    ncx = cx0 ^ x
                    m.d.comb += [cd_w.addr.eq(cc), cd_w.data.eq(Cat(nt, ncx)), cd_w.en.eq(1)]
                    with m.If(nt == 0):              # now unsatisfied: x no longer breaks it, it joins the list
                        m.d.comb += [un_w.addr.eq(nuns), un_w.data.eq(cc), un_w.en.eq(1),
                                     up_w.addr.eq(cc), up_w.data.eq(nuns), up_w.en.eq(1), br_r.addr.eq(x)]
                        m.d.sync += [nuns.eq(nuns + 1), bv.eq(x), t.eq(0)]   # bv: variable, t: 0 = decrement
                        m.next = "F_BRK"
                    with m.Elif(nt == 1):            # one true literal left: its variable now breaks it
                        m.d.comb += br_r.addr.eq(ncx)
                        m.d.sync += [bv.eq(ncx), t.eq(1)]
                        m.next = "F_BRK"
                    with m.Else():
                        m.next = "F_OCC_RD"
                with m.Else():
                    nt = (t0 + 1)[:TB]
                    with m.If(nt == 1):              # satisfied again: leave the list; x now breaks it
                        m.d.comb += [cd_w.addr.eq(cc), cd_w.data.eq(Cat(nt, cx0 ^ x)), cd_w.en.eq(1),
                                     up_r.addr.eq(cc)]
                        m.next = "F_RM"
                    with m.Elif(nt == 2):            # the old critical variable no longer breaks it
                        m.d.comb += [cd_w.addr.eq(cc), cd_w.data.eq(Cat(nt, cx0 ^ x)), cd_w.en.eq(1),
                                     br_r.addr.eq(cx0)]
                        m.d.sync += [bv.eq(cx0), t.eq(0)]
                        m.next = "F_BRK"
                    with m.Else():
                        m.d.comb += [cd_w.addr.eq(cc), cd_w.data.eq(Cat(nt, cx0 ^ x)), cd_w.en.eq(1)]
                        m.next = "F_OCC_RD"
            with m.State("F_BRK"):
                m.d.comb += [br_w.addr.eq(bv), br_w.data.eq(Mux(t == 1, br_r.data + 1, br_r.data - 1)), br_w.en.eq(1)]
                m.next = "F_OCC_RD"
            # remove cc from the unsat list: the last entry takes its place
            with m.State("F_RM"):
                m.d.sync += p.eq(up_r.data)
                m.d.comb += un_r.addr.eq(nuns - 1)
                m.next = "F_RM2"
            with m.State("F_RM2"):
                m.d.comb += [un_w.addr.eq(p), un_w.data.eq(un_r.data), un_w.en.eq(1),
                             up_w.addr.eq(un_r.data), up_w.data.eq(p), up_w.en.eq(1)]
                m.d.sync += [nuns.eq(nuns - 1), last.eq(un_r.data)]
                m.next = "F_RM3"
            with m.State("F_RM3"):
                m.d.comb += [up_w.addr.eq(cc), up_w.data.eq(NONE_POS), up_w.en.eq(1), br_r.addr.eq(x)]
                m.d.sync += [bv.eq(x), t.eq(1)]
                m.next = "F_BRK"

            with m.State("SOLVED"):
                m.d.comb += [self.solved.eq(1), av_r.addr.eq(self.model_addr[:VB])]
            with m.State("OFF"):
                m.d.comb += self.disabled.eq(1)
        return m
