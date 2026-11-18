"""Bramble's CDCL core, increment 2.3: one clause bank, linked watch lists, VMTF decisions, 1UIP learning with
recursive minimization, LBD, restarts on moving averages of LBD, and tiered clause-database reduction.

The algorithm follows the Bramble model (model/bramble.cpp) step for step; what is not here yet (minimization, LBD,
restarts, reduction, banks, stable mode, the walker) arrives in later increments.

Memories (one read and one write port each; every read takes a cycle):
  arena   clause bodies: [size] [lbd | learned << 8 | used << 9] lit0 lit1 ...   ARENA words of LB bits
  hist    reduction: learned-clause count per LBD

Reduction (every 2000 + 300k conflicts, or forced when the arena or the watch nodes pass 90%) runs at decision level
0. Learned clauses with LBD <= 2 stay; LBD <= 6 stay if used in a conflict since the last reduction; of the rest,
the worse half (three quarters when forced) by LBD goes, the earliest first among equal LBD - exactly the clauses a
stable sort by LBD would pick, found with a histogram instead of a sort. The surviving clauses are compacted to the
front of the arena, every watch list is rebuilt, and the root trail is propagated again (the rebuilt watches may sit
on literals already false at the root). Root-level reasons are never read, so their clauses may go.
  wnode   watch nodes: (clause, blocker, next) - a clause has two           WN nodes
  whead   per literal: first watch node, or NIL
  bnode   binary nodes: (implied literal, next)  - (a|b) is a node b on a's list and a on b's
  bhead   per literal: first binary node, or NIL
  val     per variable: assigned, value
  level, reason, trail, trail_lim, saved phase, seen, VMTF prev/next/stamp
  lbuf    the learned clause being built
  ana     the variables analysed for the current conflict (to clear `seen` and to bump)

A literal is 2*var + sign (sign 1 = negative). A watch node lives on the list of the literal it watches and is
visited when that literal becomes false; moving a watch relinks the same node onto another literal's list, so watch
lists never need compacting. Reasons: a clause address, BIN|literal for a binary clause, or NONE.

Soundness: UNSAT is reported only from a conflict at decision level 0; SAT only when every variable is assigned with
no conflict, and the model is the assignment itself. Running out of any memory gives UNKNOWN (or REJECTED while
loading), never a wrong answer.
"""

from amaranth import Array, Cat, Const, Elaboratable, Module, Mux, Signal, signed
from amaranth.lib.memory import Memory

VB = 12                  # variable index bits: up to 4096 variables
NV = 1 << VB
LB = VB + 1              # literal bits
AAW = 15                 # arena address bits
ARENA = 1 << AAW         # literal slots, headers included
WAW = 15                 # watch node address bits (two per long clause)
WN = 1 << WAW
BAW = 15                 # binary node address bits (two per binary clause)
BN = 1 << BAW
LMAX = 1024              # longest learned clause
NIL_W = (1 << WAW) - 1   # end of a watch list (node WN-1 is never allocated)
NIL_B = (1 << BAW) - 1
NIL_V = (1 << (VB + 1)) - 1
RW = 1 + max(AAW, LB)    # reason: BIN flag + clause address or literal
R_NONE = (1 << RW) - 1
R_BIN = 1 << (RW - 1)
SZW = 12                 # clause size field (longest clause 4095)

UNKNOWN, SAT, UNSAT = 0, 1, 2
INFO_REJECT_ARENA = 1 << 24
INFO_OUT_OF_MEMORY = 1 << 25
INFO_LEARN_TOO_LONG = 1 << 26


def mem(m, name, width, depth):
    mm = Memory(shape=width, depth=depth, init=[])
    m.submodules[name] = mm
    return mm.read_port(), mm.write_port()


class Cdcl(Elaboratable):
    """Interface (sync domain):
      load_valid/load_data/load_ready   the clause stream (as the shell gives it to the solver)
      nvars                             from the shell, stable before the first clause
      start                             1-cycle pulse after the stream: solve
      abort                             level: drop everything (the solver wraps this core in a ResetInserter)
      done/result/info                  the answer (held)
      model_addr -> model_val           one cycle later
      dbg_learn_*                       a learned clause, literal by literal (verification only; unused on a board)
    """

    def __init__(self):
        self.load_valid = Signal()
        self.load_data = Signal(signed(32))
        self.load_ready = Signal()
        self.nvars = Signal(32)
        self.start = Signal()
        self.done = Signal()
        self.rejected = Signal()
        self.result = Signal(2)
        self.info = Signal(32)
        self.model_addr = Signal(32)
        self.model_val = Signal()
        self.dbg_learn_lit = Signal(LB)
        self.dbg_learn_valid = Signal()
        self.dbg_learn_end = Signal()
        self.idle = Signal()             # in INIT or waiting for clauses: holds no solving state
        self.conflicts = Signal(32)
        self.decisions = Signal(32)
        self.restarts = Signal(32)
        self.reduces = Signal(32)

    def elaborate(self, platform):  # noqa: C901 - one controller, read top to bottom
        m = Module()

        arena_r, arena_w = mem(m, "arena", LB, ARENA)
        wn_r, wn_w = mem(m, "wnode", AAW + LB + WAW, WN)
        wh_r, wh_w = mem(m, "whead", WAW, 2 * NV)
        bn_r, bn_w = mem(m, "bnode", LB + BAW, BN)
        bh_r, bh_w = mem(m, "bhead", BAW, 2 * NV)
        val_r, val_w = mem(m, "val", 2, NV)
        lvl_r, lvl_w = mem(m, "level", VB + 1, NV)
        rsn_r, rsn_w = mem(m, "reason", RW, NV)
        tr_r, tr_w = mem(m, "trail", LB, NV + 1)
        tl_r, tl_w = mem(m, "trail_lim", VB + 1, NV + 1)
        sav_r, sav_w = mem(m, "saved", 1, NV)
        seen_r, seen_w = mem(m, "seen", 2, NV)          # 1: in the clause / analysed, 2: shown redundant
        sk_r, sk_w = mem(m, "mstack", LB, NV)               # minimization: DFS stack
        tc_r, tc_w = mem(m, "tclear", VB, NV)               # minimization: variables marked 2
        ls_r, ls_w = mem(m, "lstamp", 32, NV + 1)           # LBD: the conflict that last counted a level
        stm_r, stm_w = mem(m, "stamp_ld", 18, NV)         # loading: (clause no., pos seen, neg seen)
        pv_r, pv_w = mem(m, "vprev", VB + 1, NV)
        nx_r, nx_w = mem(m, "vnext", VB + 1, NV)
        st_r, st_w = mem(m, "vstamp", 32, NV)
        st2_r = m.submodules["vstamp"].read_port()          # a second read port: the search pointer's stamp
        lb_r, lb_w = mem(m, "lbuf", LB, LMAX)
        an_r, an_w = mem(m, "ana", VB, NV)
        hi_r, hi_w = mem(m, "hist", AAW + 1, 256)

        def wnode(cref, blocker, nxt):
            return Cat(cref[:AAW], blocker[:LB], nxt[:WAW])

        def wn_cref(d): return d[:AAW]
        def wn_blk(d): return d[AAW:AAW + LB]
        def wn_next(d): return d[AAW + LB:]

        def bnode(lit, nxt):
            return Cat(lit[:LB], nxt[:BAW])

        # ---------------------------------------------------------------- state
        n = Signal(VB + 1)                  # variables in this instance
        aptr = Signal(AAW + 1)              # arena bump pointer
        wptr = Signal(WAW + 1)              # watch nodes used
        bptr = Signal(BAW + 1)              # binary nodes used
        cl_start = Signal(AAW + 1)
        cl_len = Signal(SZW + 1)
        cl_no = Signal(16)
        cl_drop = Signal()
        cl_l0 = Signal(LB)
        cl_l1 = Signal(LB)
        reject = Signal()
        oom = Signal()
        unsat = Signal()
        sat = Signal()
        info_extra = Signal(32)

        tlen = Signal(VB + 1)               # trail length
        qhead = Signal(VB + 1)
        dl = Signal(VB + 1)                 # decision level
        vfirst = Signal(VB + 1)
        vlast = Signal(VB + 1)
        vsearch = Signal(VB + 1)
        sctr = Signal(32)

        i = Signal(AAW + 2)                 # general counter
        lit = Signal(LB)
        f = Signal(LB)                      # the literal that just became false
        cur = Signal(WAW)                   # watch node being visited
        prev = Signal(WAW)
        nxt = Signal(WAW)
        cref = Signal(AAW)
        blk = Signal(LB)
        csize = Signal(SZW)
        first = Signal(LB)
        k = Signal(SZW)
        klit = Signal(LB)
        bcur = Signal(BAW)
        confl_bin = Signal()
        confl_cref = Signal(AAW)
        confl_a = Signal(LB)                # binary conflict: the two false literals
        confl_b = Signal(LB)

        # analysis
        pathc = Signal(VB + 1)
        lsize = Signal(range(LMAX + 1))
        nana = Signal(VB + 1)
        idx = Signal(VB + 1)
        uip = Signal(LB)
        vq = Signal(LB)                     # literal being visited
        rsrc = Signal(RW)                   # reason being expanded
        rpos = Signal(SZW)
        rsize = Signal(SZW)
        btlvl = Signal(VB + 1)
        bmax = Signal(range(LMAX + 1))      # position of the highest-level literal after 0
        bmaxlvl = Signal(VB + 1)
        l1 = Signal(LB)
        learn_too_long = Signal()
        bump_v = Signal(VB)
        bt_to = Signal(VB + 1)
        # minimization
        abstract = Signal(32)
        j = Signal(range(LMAX + 1))
        mx = Signal(LB)                     # the literal being tested for redundancy
        sp = Signal(VB + 1)                 # stack depth
        ntc = Signal(VB + 1)                # entries in tclear
        tc_top = Signal(VB + 1)
        y = Signal(LB)
        u = Signal(VB + 1)                  # undo index into tclear
        curlvl = Signal(VB + 1)
        # LBD, restarts
        lbd = Signal(8)
        ema_fast = Signal(signed(34))       # fixed point, 16 fraction bits
        ema_slow = Signal(signed(34))
        last_restart = Signal(32)
        restarting = Signal()
        reducing = Signal()
        forced = Signal()
        reduce_at = Signal(32)
        reduce_k = Signal(16)
        rp = Signal(AAW + 1)                # read position in the arena
        wq = Signal(AAW + 1)                # write position (compaction)
        hsz = Signal(SZW)                   # size of the clause at rp
        hd2 = Signal(LB)                    # its second header word
        ncand = Signal(AAW + 1)
        kill = Signal(AAW + 1)
        acc = Signal(AAW + 1)
        thr = Signal(9)                     # LBD threshold (256: delete nothing)
        rem = Signal(AAW + 1)               # still to delete at LBD == thr
        cpos = Signal(SZW + 2)              # word being copied

        def var(l): return l[1:LB]

        def is_true(vdata, l):  # val word (assigned, value) and a literal
            return vdata[0] & (vdata[1] ^ l[0])

        def is_false(vdata, l):
            return vdata[0] & ~(vdata[1] ^ l[0])

        m.d.comb += [self.dbg_learn_valid.eq(0), self.dbg_learn_end.eq(0), self.rejected.eq(0)]

        # model readback: the value memory, read at model_addr (registered output)
        model_rd = Signal()
        start_pending = Signal()
        with m.If(self.start):
            m.d.sync += start_pending.eq(1)

        d = self.load_data
        a = Signal(32)
        m.d.comb += a.eq(Mux(d < 0, -d, d))
        dlit = Signal(LB)
        m.d.comb += dlit.eq(Cat(d < 0, (a - 1)[:VB]))

        with m.FSM(name="cdcl"):
            # ------------------------------------------------------------ init per-variable memories
            with m.State("INIT"):
                m.d.comb += self.idle.eq(1)
                with m.If(i == 2 * NV):
                    m.d.sync += [i.eq(0), aptr.eq(0), wptr.eq(0), bptr.eq(0), cl_start.eq(0), cl_len.eq(0),
                                 cl_no.eq(1), cl_drop.eq(0), reject.eq(0), oom.eq(0), unsat.eq(0), sat.eq(0),
                                 tlen.eq(0), qhead.eq(0), dl.eq(0), info_extra.eq(0), self.conflicts.eq(0),
                                 self.decisions.eq(0), ema_fast.eq(0), ema_slow.eq(0), last_restart.eq(0),
                                 restarting.eq(0), self.restarts.eq(0), self.reduces.eq(0), reducing.eq(0),
                                 reduce_at.eq(2000), reduce_k.eq(0)]
                    m.next = "LOAD"
                with m.Else():
                    m.d.comb += [wh_w.addr.eq(i), wh_w.data.eq(NIL_W), wh_w.en.eq(1),
                                 bh_w.addr.eq(i), bh_w.data.eq(NIL_B), bh_w.en.eq(1)]
                    with m.If(i < NV):
                        m.d.comb += [val_w.addr.eq(i), val_w.data.eq(0), val_w.en.eq(1),
                                     stm_w.addr.eq(i), stm_w.data.eq(0), stm_w.en.eq(1),
                                     seen_w.addr.eq(i), seen_w.data.eq(0), seen_w.en.eq(1),
                                     sav_w.addr.eq(i), sav_w.data.eq(0), sav_w.en.eq(1),
                                     ls_w.addr.eq(i), ls_w.data.eq(0), ls_w.en.eq(1)]
                    m.d.sync += i.eq(i + 1)

            # ------------------------------------------------------------ clause stream
            with m.State("LOAD"):
                m.d.comb += [self.load_ready.eq(1), self.idle.eq(1)]
                with m.If(self.start | start_pending):
                    m.d.sync += [n.eq(self.nvars[:VB + 1]), i.eq(0), start_pending.eq(0),
                                 reject.eq(reject | (self.nvars > NV))]
                    m.next = "VMTF_INIT"
                with m.Elif(self.load_valid):
                    with m.If(d == 0):
                        m.next = "CL_END"
                    with m.Elif(cl_drop | reject):
                        pass
                    with m.Elif((a > NV) | (a > self.nvars)):
                        m.d.sync += reject.eq(1)
                    with m.Else():
                        m.d.sync += lit.eq(dlit)
                        m.d.comb += stm_r.addr.eq(var(dlit))
                        m.next = "LD_LIT"
            with m.State("LD_LIT"):     # duplicate or tautology within this clause?
                sd = stm_r.data
                here = sd[:16] == cl_no
                pos_seen = here & sd[16]
                neg_seen = here & sd[17]
                dup = Mux(lit[0], neg_seen, pos_seen)
                taut = Mux(lit[0], pos_seen, neg_seen)
                with m.If(dup):
                    m.next = "LOAD"
                with m.Elif(taut):
                    m.d.sync += cl_drop.eq(1)
                    m.next = "LOAD"
                with m.Elif(cl_start + 2 + cl_len >= ARENA - 1):
                    m.d.sync += reject.eq(1)
                    m.next = "LOAD"
                with m.Else():
                    m.d.comb += [stm_w.addr.eq(var(lit)), stm_w.en.eq(1),
                                 stm_w.data.eq(Cat(cl_no, Mux(here, sd[16], 0) | ~lit[0], Mux(here, sd[17], 0) | lit[0]))]
                    m.d.comb += [arena_w.addr.eq(cl_start + 2 + cl_len), arena_w.data.eq(lit), arena_w.en.eq(1)]
                    with m.If(cl_len == 0):
                        m.d.sync += cl_l0.eq(lit)
                    with m.If(cl_len == 1):
                        m.d.sync += cl_l1.eq(lit)
                    m.d.sync += cl_len.eq(cl_len + 1)
                    m.next = "LOAD"
            with m.State("CL_END"):
                m.d.sync += [cl_len.eq(0), cl_drop.eq(0), cl_no.eq(cl_no + 1)]
                m.next = "LOAD"
                with m.If(cl_drop | reject):
                    pass
                with m.Elif(cl_len == 0):
                    m.d.sync += unsat.eq(1)                  # the empty clause
                with m.Elif(cl_len == 1):
                    m.d.comb += val_r.addr.eq(var(cl_l0))
                    m.d.sync += lit.eq(cl_l0)
                    m.next = "LD_UNIT"
                with m.Elif(cl_len == 2):
                    with m.If(bptr + 2 >= BN - 1):
                        m.d.sync += reject.eq(1)
                    with m.Else():
                        m.d.comb += bh_r.addr.eq(cl_l0)
                        m.d.sync += [lit.eq(cl_l0), klit.eq(cl_l1), i.eq(0)]
                        m.next = "BIN_ADD_RD"
                with m.Else():
                    with m.If(wptr + 2 >= WN - 1):
                        m.d.sync += reject.eq(1)
                    with m.Else():
                        m.d.comb += [arena_w.addr.eq(cl_start), arena_w.data.eq(cl_len), arena_w.en.eq(1)]
                        m.d.sync += [cref.eq(cl_start), cl_start.eq(cl_start + 2 + cl_len), aptr.eq(cl_start + 2 + cl_len),
                                     lit.eq(cl_l0), klit.eq(cl_l1), i.eq(0)]
                        m.next = "CL_HDR2"
            with m.State("CL_HDR2"):
                m.d.comb += [arena_w.addr.eq(cref + 1), arena_w.data.eq(0), arena_w.en.eq(1)]
                m.next = "WATCH_ADD_RD"
            with m.State("LD_UNIT"):
                with m.If(is_false(val_r.data, lit)):
                    m.d.sync += unsat.eq(1)
                    m.next = "LOAD"
                with m.Elif(is_true(val_r.data, lit)):
                    m.next = "LOAD"
                with m.Else():
                    m.d.comb += [val_w.addr.eq(var(lit)), val_w.data.eq(Cat(1, ~lit[0])), val_w.en.eq(1),
                                 lvl_w.addr.eq(var(lit)), lvl_w.data.eq(0), lvl_w.en.eq(1),
                                 rsn_w.addr.eq(var(lit)), rsn_w.data.eq(R_NONE), rsn_w.en.eq(1),
                                 tr_w.addr.eq(tlen), tr_w.data.eq(lit), tr_w.en.eq(1)]
                    m.d.sync += tlen.eq(tlen + 1)
                    m.next = "LOAD"
            # add a binary clause (lit | klit): node klit on lit's list, then node lit on klit's list
            with m.State("BIN_ADD_RD"):
                m.d.comb += bh_r.addr.eq(lit)
                m.next = "BIN_ADD"
            with m.State("BIN_ADD"):
                m.d.comb += [bn_w.addr.eq(bptr), bn_w.data.eq(bnode(klit, bh_r.data)), bn_w.en.eq(1),
                             bh_w.addr.eq(lit), bh_w.data.eq(bptr), bh_w.en.eq(1)]
                m.d.sync += [bptr.eq(bptr + 1), lit.eq(klit), klit.eq(lit), i.eq(i + 1)]
                with m.If(i == 1):
                    m.next = "BIN_DONE"
                with m.Else():
                    m.next = "BIN_ADD_RD"
            with m.State("BIN_DONE"):
                m.next = "BIN_RETURN"
            # add the two watches of the clause at cref: lit (= its literal 0) and klit (literal 1)
            with m.State("WATCH_ADD_RD"):
                m.d.comb += wh_r.addr.eq(lit)
                m.next = "WATCH_ADD"
            with m.State("WATCH_ADD"):
                m.d.comb += [wn_w.addr.eq(wptr), wn_w.data.eq(wnode(cref, klit, wh_r.data)), wn_w.en.eq(1),
                             wh_w.addr.eq(lit), wh_w.data.eq(wptr), wh_w.en.eq(1)]
                m.d.sync += [wptr.eq(wptr + 1), lit.eq(klit), klit.eq(lit), i.eq(i + 1)]
                with m.If(i == 1):
                    m.next = "WATCH_RETURN"
                with m.Else():
                    m.next = "WATCH_ADD_RD"
            # where to go after adding a clause: loading, or learning (then assign its first literal)
            learning = Signal()
            with m.State("BIN_RETURN"):
                m.next = "LOAD"
                with m.If(learning):
                    m.next = "LEARN_ASSIGN"
            with m.State("WATCH_RETURN"):
                m.next = "LOAD"
                with m.If(learning):
                    m.next = "LEARN_ASSIGN"

            # ------------------------------------------------------------ VMTF queue: 0, 1, ..., n-1
            with m.State("VMTF_INIT"):
                with m.If(reject):
                    m.next = "DONE_REJECT"
                with m.Elif(unsat):
                    m.next = "DONE"
                with m.Elif((i == n) | (i == NV)):
                    m.d.sync += [vfirst.eq(Mux(n == 0, NIL_V, 0)), vlast.eq(Mux(n == 0, NIL_V, n - 1)),
                                 vsearch.eq(Mux(n == 0, NIL_V, n - 1)), sctr.eq(n + 1), learning.eq(0)]
                    m.next = "PROP"
                with m.Else():
                    m.d.comb += [pv_w.addr.eq(i), pv_w.data.eq(Mux(i == 0, NIL_V, i - 1)), pv_w.en.eq(1),
                                 nx_w.addr.eq(i), nx_w.data.eq(Mux(i + 1 == n, NIL_V, i + 1)), nx_w.en.eq(1),
                                 st_w.addr.eq(i), st_w.data.eq(i + 1), st_w.en.eq(1)]
                    m.d.sync += i.eq(i + 1)

            # ------------------------------------------------------------ propagation
            with m.State("PROP"):
                with m.If(qhead == tlen):
                    m.next = "DECIDE_RD"
                with m.Else():
                    m.d.comb += tr_r.addr.eq(qhead)
                    m.next = "PROP_LIT"
            with m.State("PROP_LIT"):
                m.d.sync += [f.eq(tr_r.data ^ 1), qhead.eq(qhead + 1)]
                m.d.comb += bh_r.addr.eq(tr_r.data ^ 1)
                m.next = "BIN_HEAD"
            with m.State("BIN_HEAD"):
                m.d.sync += bcur.eq(bh_r.data)
                m.next = "BIN_NODE_RD"
            with m.State("BIN_NODE_RD"):
                with m.If(bcur == NIL_B):
                    m.d.comb += wh_r.addr.eq(f)
                    m.next = "W_HEAD"
                with m.Else():
                    m.d.comb += bn_r.addr.eq(bcur)
                    m.next = "BIN_NODE"
            with m.State("BIN_NODE"):
                m.d.sync += [klit.eq(bn_r.data[:LB]), bcur.eq(bn_r.data[LB:])]
                m.d.comb += val_r.addr.eq(var(bn_r.data[:LB]))
                m.next = "BIN_VAL"
            with m.State("BIN_VAL"):
                with m.If(is_false(val_r.data, klit)):
                    m.d.sync += [confl_bin.eq(1), confl_a.eq(klit), confl_b.eq(f)]
                    m.next = "CONFLICT"
                with m.Elif(~is_true(val_r.data, klit)):
                    m.d.sync += [lit.eq(klit), rsrc.eq(R_BIN | f)]
                    m.next = "ASSIGN_THEN_BIN"
                with m.Else():
                    m.next = "BIN_NODE_RD"
            with m.State("ASSIGN_THEN_BIN"):
                m.d.comb += [val_w.addr.eq(var(lit)), val_w.data.eq(Cat(1, ~lit[0])), val_w.en.eq(1),
                             lvl_w.addr.eq(var(lit)), lvl_w.data.eq(dl), lvl_w.en.eq(1),
                             rsn_w.addr.eq(var(lit)), rsn_w.data.eq(rsrc), rsn_w.en.eq(1),
                             tr_w.addr.eq(tlen), tr_w.data.eq(lit), tr_w.en.eq(1)]
                m.d.sync += tlen.eq(tlen + 1)
                m.next = "BIN_NODE_RD"

            # long clauses: walk f's watch list
            with m.State("W_HEAD"):
                m.d.sync += [cur.eq(wh_r.data), prev.eq(NIL_W)]
                m.next = "W_NODE_RD"
            with m.State("W_NODE_RD"):
                with m.If(cur == NIL_W):
                    m.next = "PROP"
                with m.Else():
                    m.d.comb += wn_r.addr.eq(cur)
                    m.next = "W_NODE"
            with m.State("W_NODE"):
                m.d.sync += [cref.eq(wn_cref(wn_r.data)), blk.eq(wn_blk(wn_r.data)), nxt.eq(wn_next(wn_r.data))]
                m.d.comb += val_r.addr.eq(var(wn_blk(wn_r.data)))
                m.next = "W_BLK"
            with m.State("W_BLK"):
                with m.If(is_true(val_r.data, blk)):
                    m.d.sync += [prev.eq(cur), cur.eq(nxt)]
                    m.next = "W_NODE_RD"
                with m.Else():
                    m.d.comb += arena_r.addr.eq(cref)
                    m.next = "W_HDR"
            with m.State("W_HDR"):
                m.d.sync += csize.eq(arena_r.data[:SZW])
                m.d.comb += arena_r.addr.eq(cref + 2)
                m.next = "W_L0"
            with m.State("W_L0"):
                m.d.sync += lit.eq(arena_r.data)
                m.d.comb += arena_r.addr.eq(cref + 3)
                m.next = "W_L1"
            with m.State("W_L1"):
                # make literal 1 the false one (f); literal 0 is then the other watch
                with m.If(lit == f):
                    m.d.comb += [arena_w.addr.eq(cref + 2), arena_w.data.eq(arena_r.data), arena_w.en.eq(1)]
                    m.d.sync += first.eq(arena_r.data)
                    m.next = "W_SWAP2"
                with m.Else():
                    m.d.sync += first.eq(lit)
                    m.next = "W_FIRST_RD"
            with m.State("W_SWAP2"):
                m.d.comb += [arena_w.addr.eq(cref + 3), arena_w.data.eq(f), arena_w.en.eq(1)]
                m.next = "W_FIRST_RD"
            with m.State("W_FIRST_RD"):
                m.d.comb += val_r.addr.eq(var(first))
                m.next = "W_FIRST"
            with m.State("W_FIRST"):
                with m.If(is_true(val_r.data, first)):
                    # satisfied by the other watch: make it the blocker, keep the node here
                    m.d.comb += [wn_w.addr.eq(cur), wn_w.data.eq(wnode(cref, first, nxt)), wn_w.en.eq(1)]
                    m.d.sync += [prev.eq(cur), cur.eq(nxt)]
                    m.next = "W_NODE_RD"
                with m.Else():
                    m.d.sync += k.eq(2)
                    m.next = "W_SCAN_RD"
            with m.State("W_SCAN_RD"):
                with m.If(k == csize):
                    m.next = "W_NOWATCH"
                with m.Else():
                    m.d.comb += arena_r.addr.eq(cref + 2 + k)
                    m.next = "W_SCAN_LIT"
            with m.State("W_SCAN_LIT"):
                m.d.sync += klit.eq(arena_r.data)
                m.d.comb += val_r.addr.eq(var(arena_r.data))
                m.next = "W_SCAN_VAL"
            with m.State("W_SCAN_VAL"):
                with m.If(~is_false(val_r.data, klit)):
                    # new watch klit: swap it into position 1, f to position k
                    m.d.comb += [arena_w.addr.eq(cref + 3), arena_w.data.eq(klit), arena_w.en.eq(1)]
                    m.next = "W_MOVE1"
                with m.Else():
                    m.d.sync += k.eq(k + 1)
                    m.next = "W_SCAN_RD"
            with m.State("W_MOVE1"):
                m.d.comb += [arena_w.addr.eq(cref + 2 + k), arena_w.data.eq(f), arena_w.en.eq(1)]
                # unlink cur from f's list
                with m.If(prev == NIL_W):
                    m.d.comb += [wh_w.addr.eq(f), wh_w.data.eq(nxt), wh_w.en.eq(1)]
                    m.next = "W_MOVE3_RD"
                with m.Else():
                    m.d.comb += wn_r.addr.eq(prev)
                    m.next = "W_MOVE2"
            with m.State("W_MOVE2"):
                d_ = wn_r.data
                m.d.comb += [wn_w.addr.eq(prev), wn_w.data.eq(Cat(d_[:AAW + LB], nxt)), wn_w.en.eq(1)]
                m.next = "W_MOVE3_RD"
            with m.State("W_MOVE3_RD"):
                m.d.comb += wh_r.addr.eq(klit)
                m.next = "W_MOVE3"
            with m.State("W_MOVE3"):
                # push cur onto klit's list, blocker = the other watch
                m.d.comb += [wn_w.addr.eq(cur), wn_w.data.eq(wnode(cref, first, wh_r.data)), wn_w.en.eq(1),
                             wh_w.addr.eq(klit), wh_w.data.eq(cur), wh_w.en.eq(1)]
                m.d.sync += cur.eq(nxt)          # prev stays: cur left this list
                m.next = "W_NODE_RD"
            with m.State("W_NOWATCH"):
                # unit or conflict on `first`; the node stays, blocker = first
                m.d.comb += [wn_w.addr.eq(cur), wn_w.data.eq(wnode(cref, first, nxt)), wn_w.en.eq(1),
                             val_r.addr.eq(var(first))]
                m.next = "W_UNIT"
            with m.State("W_UNIT"):
                with m.If(is_false(val_r.data, first)):
                    m.d.sync += [confl_bin.eq(0), confl_cref.eq(cref)]
                    m.next = "CONFLICT"
                with m.Else():
                    m.d.comb += [val_w.addr.eq(var(first)), val_w.data.eq(Cat(1, ~first[0])), val_w.en.eq(1),
                                 lvl_w.addr.eq(var(first)), lvl_w.data.eq(dl), lvl_w.en.eq(1),
                                 rsn_w.addr.eq(var(first)), rsn_w.data.eq(cref), rsn_w.en.eq(1),
                                 tr_w.addr.eq(tlen), tr_w.data.eq(first), tr_w.en.eq(1)]
                    m.d.sync += [tlen.eq(tlen + 1), prev.eq(cur), cur.eq(nxt)]
                    m.next = "W_NODE_RD"

            # ------------------------------------------------------------ conflict analysis (1UIP)
            with m.State("CONFLICT"):
                m.d.sync += self.conflicts.eq(self.conflicts + 1)
                with m.If(dl == 0):
                    m.d.sync += unsat.eq(1)
                    m.next = "DONE"
                with m.Else():
                    m.d.sync += [pathc.eq(0), lsize.eq(1), nana.eq(0), idx.eq(tlen), rpos.eq(0)]
                    with m.If(confl_bin):
                        m.d.sync += [rsrc.eq(R_BIN | confl_a), vq.eq(confl_b)]
                        m.next = "AN_VISIT_RD"          # visit confl_b, then the "reason" literal confl_a
                    with m.Else():
                        m.d.sync += [rsrc.eq(confl_cref), rsize.eq(0)]
                        m.d.comb += arena_r.addr.eq(confl_cref)
                        m.next = "AN_CL_HDR"
            # expand a clause (the conflict, rpos from 0; or a reason, rpos from 1)
            with m.State("AN_CL_HDR"):
                m.d.sync += rsize.eq(arena_r.data[:SZW])
                m.d.comb += arena_r.addr.eq(rsrc[:AAW] + 1)
                m.next = "AN_CL_HDR2"
            with m.State("AN_CL_HDR2"):         # a learned clause used in this conflict
                with m.If(arena_r.data[8]):
                    m.d.comb += [arena_w.addr.eq(rsrc[:AAW] + 1), arena_w.data.eq(arena_r.data | (1 << 9)),
                                 arena_w.en.eq(1)]
                m.next = "AN_CL_RD"
            with m.State("AN_CL_RD"):
                with m.If(rpos == rsize):
                    m.next = "AN_TRAIL_RD"
                with m.Else():
                    m.d.comb += arena_r.addr.eq(rsrc[:AAW] + 2 + rpos)
                    m.next = "AN_CL_LIT"
            with m.State("AN_CL_LIT"):
                m.d.sync += [vq.eq(arena_r.data), rpos.eq(rpos + 1)]
                m.next = "AN_VISIT_RD"
            with m.State("AN_VISIT_RD"):
                m.d.comb += [seen_r.addr.eq(var(vq)), lvl_r.addr.eq(var(vq))]
                m.next = "AN_VISIT"
            with m.State("AN_VISIT"):
                with m.If((seen_r.data == 0) & (lvl_r.data != 0)):
                    m.d.comb += [seen_w.addr.eq(var(vq)), seen_w.data.eq(1), seen_w.en.eq(1),
                                 an_w.addr.eq(nana), an_w.data.eq(var(vq)), an_w.en.eq(1)]
                    m.d.sync += nana.eq(nana + 1)
                    with m.If(lvl_r.data >= dl):
                        m.d.sync += pathc.eq(pathc + 1)
                    with m.Elif(lsize == LMAX):
                        m.d.sync += learn_too_long.eq(1)
                    with m.Else():
                        m.d.comb += [lb_w.addr.eq(lsize), lb_w.data.eq(vq), lb_w.en.eq(1)]
                        m.d.sync += lsize.eq(lsize + 1)
                with m.If(rsrc & R_BIN):
                    # binary: after the conflict's first literal, its second (the reason literal)
                    with m.If(rpos == 0):
                        m.d.sync += [vq.eq(rsrc[:LB]), rpos.eq(1)]
                        m.next = "AN_VISIT_RD"
                    with m.Else():
                        m.next = "AN_TRAIL_RD"
                with m.Else():
                    m.next = "AN_CL_RD"
            # walk the trail back to the next seen literal
            with m.State("AN_TRAIL_RD"):
                m.d.comb += tr_r.addr.eq(idx - 1)
                m.next = "AN_TRAIL_LIT"
            with m.State("AN_TRAIL_LIT"):
                m.d.sync += [uip.eq(tr_r.data), idx.eq(idx - 1)]
                m.d.comb += seen_r.addr.eq(var(tr_r.data))
                m.next = "AN_TRAIL_SEEN"
            with m.State("AN_TRAIL_SEEN"):
                with m.If(seen_r.data == 0):
                    m.next = "AN_TRAIL_RD"
                with m.Else():
                    m.d.comb += [seen_w.addr.eq(var(uip)), seen_w.data.eq(0), seen_w.en.eq(1)]
                    with m.If(pathc == 1):
                        m.d.comb += [lb_w.addr.eq(0), lb_w.data.eq(uip ^ 1), lb_w.en.eq(1)]
                        m.d.sync += [pathc.eq(0), i.eq(1), abstract.eq(0)]
                        m.next = "MIN_ABS_RD"
                    with m.Else():
                        m.d.sync += pathc.eq(pathc - 1)
                        m.d.comb += rsn_r.addr.eq(var(uip))
                        m.next = "AN_REASON"
            with m.State("AN_REASON"):
                r_ = rsn_r.data
                with m.If(r_ & R_BIN):
                    m.d.sync += [rsrc.eq(r_), vq.eq(r_[:LB]), rpos.eq(1)]
                    m.next = "AN_VISIT_RD"              # one literal, then back to the trail
                with m.Else():
                    m.d.sync += [rsrc.eq(r_), rpos.eq(1)]
                    m.d.comb += arena_r.addr.eq(r_[:AAW])
                    m.next = "AN_CL_HDR"
            # ------------------------------------------------------------ minimization (MiniSat's, recursive)
            # abstract levels of literals 1..
            with m.State("MIN_ABS_RD"):
                with m.If(i == lsize):
                    m.d.sync += [i.eq(1), j.eq(1), ntc.eq(0)]
                    m.next = "MIN_RD"
                with m.Else():
                    m.d.comb += lb_r.addr.eq(i)
                    m.next = "MIN_ABS_LIT"
            with m.State("MIN_ABS_LIT"):
                m.d.comb += lvl_r.addr.eq(var(lb_r.data))
                m.next = "MIN_ABS_LVL"
            with m.State("MIN_ABS_LVL"):
                m.d.sync += [abstract.eq(abstract | (Const(1, 32) << lvl_r.data[:5])), i.eq(i + 1)]
                m.next = "MIN_ABS_RD"
            # keep or drop each literal 1..
            with m.State("MIN_RD"):
                with m.If(i == lsize):
                    m.d.sync += [lsize.eq(j), i.eq(0)]
                    m.next = "TC_CLEAR_RD"
                with m.Else():
                    m.d.comb += lb_r.addr.eq(i)
                    m.next = "MIN_LIT"
            with m.State("MIN_LIT"):
                m.d.sync += mx.eq(lb_r.data)
                m.d.comb += rsn_r.addr.eq(var(lb_r.data))
                m.next = "MIN_RSN"
            with m.State("MIN_RSN"):
                with m.If(rsn_r.data == R_NONE):
                    m.next = "MIN_KEEP"
                with m.Else():
                    m.d.comb += [sk_w.addr.eq(0), sk_w.data.eq(mx), sk_w.en.eq(1)]
                    m.d.sync += [sp.eq(1), tc_top.eq(ntc)]
                    m.next = "RED_POP"
            with m.State("MIN_KEEP"):
                m.d.comb += [lb_w.addr.eq(j), lb_w.data.eq(mx), lb_w.en.eq(1)]
                m.d.sync += [j.eq(j + 1), i.eq(i + 1)]
                m.next = "MIN_RD"
            # is mx implied by the other literals? Depth-first over reasons.
            with m.State("RED_POP"):
                with m.If(sp == 0):
                    m.d.sync += i.eq(i + 1)             # redundant: dropped
                    m.next = "MIN_RD"
                with m.Else():
                    m.d.comb += sk_r.addr.eq(sp - 1)
                    m.next = "RED_POPPED"
            with m.State("RED_POPPED"):
                m.d.sync += [y.eq(sk_r.data), sp.eq(sp - 1)]
                m.d.comb += rsn_r.addr.eq(var(sk_r.data))
                m.next = "RED_RSN"
            with m.State("RED_RSN"):
                r_ = rsn_r.data
                m.d.sync += [rsrc.eq(r_), rpos.eq(1)]
                with m.If(r_ & R_BIN):
                    m.d.sync += vq.eq(r_[:LB])
                    m.next = "RED_Q_RD"
                with m.Else():
                    m.d.comb += arena_r.addr.eq(r_[:AAW])
                    m.next = "RED_CL_HDR"
            with m.State("RED_CL_HDR"):
                m.d.sync += rsize.eq(arena_r.data[:SZW])
                m.next = "RED_CL_RD"
            with m.State("RED_CL_RD"):
                with m.If(rpos == rsize):
                    m.next = "RED_POP"
                with m.Else():
                    m.d.comb += arena_r.addr.eq(rsrc[:AAW] + 2 + rpos)
                    m.next = "RED_CL_LIT"
            with m.State("RED_CL_LIT"):
                m.d.sync += [vq.eq(arena_r.data), rpos.eq(rpos + 1)]
                m.next = "RED_Q_RD"
            with m.State("RED_Q_RD"):
                m.d.comb += [seen_r.addr.eq(var(vq)), lvl_r.addr.eq(var(vq)), rsn_r.addr.eq(var(vq))]
                m.next = "RED_Q"
            with m.State("RED_Q"):
                skip = (seen_r.data != 0) | (lvl_r.data == 0)
                push = ~skip & (rsn_r.data != R_NONE) & abstract.bit_select(lvl_r.data[:5], 1)
                with m.If(~skip & ~push):
                    # q is a decision or at a level outside the clause: mx is not redundant
                    m.d.sync += u.eq(tc_top)
                    m.next = "RED_FAIL_RD"
                with m.Else():
                    with m.If(push):
                        m.d.comb += [seen_w.addr.eq(var(vq)), seen_w.data.eq(2), seen_w.en.eq(1),
                                     sk_w.addr.eq(sp), sk_w.data.eq(vq), sk_w.en.eq(1),
                                     tc_w.addr.eq(ntc), tc_w.data.eq(var(vq)), tc_w.en.eq(1)]
                        m.d.sync += [sp.eq(sp + 1), ntc.eq(ntc + 1)]
                    # next literal of this reason (a binary reason has only the one)
                    with m.If(rsrc & R_BIN):
                        m.next = "RED_POP"
                    with m.Else():
                        m.next = "RED_CL_RD"
            # not redundant: undo the marks made while testing mx, and keep it
            with m.State("RED_FAIL_RD"):
                with m.If(u == ntc):
                    m.d.sync += [ntc.eq(tc_top), sp.eq(0)]
                    m.next = "MIN_KEEP"
                with m.Else():
                    m.d.comb += tc_r.addr.eq(u)
                    m.next = "RED_FAIL"
            with m.State("RED_FAIL"):
                m.d.comb += [seen_w.addr.eq(tc_r.data), seen_w.data.eq(0), seen_w.en.eq(1)]
                m.d.sync += u.eq(u + 1)
                m.next = "RED_FAIL_RD"
            # clear the redundancy marks
            with m.State("TC_CLEAR_RD"):
                with m.If(i == ntc):
                    m.d.sync += i.eq(0)
                    m.next = "AN_CLEAR_RD"
                with m.Else():
                    m.d.comb += tc_r.addr.eq(i)
                    m.next = "TC_CLEAR"
            with m.State("TC_CLEAR"):
                m.d.comb += [seen_w.addr.eq(tc_r.data), seen_w.data.eq(0), seen_w.en.eq(1)]
                m.d.sync += i.eq(i + 1)
                m.next = "TC_CLEAR_RD"

            # clear `seen` of every analysed variable, bumping each in VMTF
            with m.State("AN_CLEAR_RD"):
                with m.If(i == nana):
                    m.d.sync += [i.eq(1), bmax.eq(1), bmaxlvl.eq(0), lbd.eq(1)]
                    m.d.comb += [ls_w.addr.eq(dl), ls_w.data.eq(self.conflicts), ls_w.en.eq(1)]
                    m.next = "BT_FIND_RD"
                with m.Else():
                    m.d.comb += an_r.addr.eq(i)
                    m.next = "AN_CLEAR"
            with m.State("AN_CLEAR"):
                m.d.comb += [seen_w.addr.eq(an_r.data), seen_w.data.eq(0), seen_w.en.eq(1)]
                m.d.sync += [bump_v.eq(an_r.data), i.eq(i + 1)]
                m.next = "BUMP_RD"
            # VMTF bump of bump_v: move to the end of the queue
            with m.State("BUMP_RD"):
                m.d.comb += [pv_r.addr.eq(bump_v), nx_r.addr.eq(bump_v)]
                m.next = "BUMP"
            with m.State("BUMP"):
                p_, n_ = pv_r.data, nx_r.data
                with m.If(n_ == NIL_V):
                    m.d.comb += [st_w.addr.eq(bump_v), st_w.data.eq(sctr), st_w.en.eq(1)]
                    m.d.sync += sctr.eq(sctr + 1)
                    m.next = "BUMP_SEARCH_RD"
                with m.Else():
                    # unlink: prev's next := next (or first := next); next's prev := prev
                    with m.If(p_ != NIL_V):
                        m.d.comb += [nx_w.addr.eq(p_), nx_w.data.eq(n_), nx_w.en.eq(1)]
                    with m.Else():
                        m.d.sync += vfirst.eq(n_)
                    m.d.comb += [pv_w.addr.eq(n_), pv_w.data.eq(p_), pv_w.en.eq(1)]
                    with m.If(vsearch == bump_v):
                        m.d.sync += vsearch.eq(Mux(p_ != NIL_V, p_, n_))
                    m.next = "BUMP_APPEND"
            with m.State("BUMP_APPEND"):
                m.d.comb += [pv_w.addr.eq(bump_v), pv_w.data.eq(vlast), pv_w.en.eq(1),
                             nx_w.addr.eq(vlast), nx_w.data.eq(bump_v), nx_w.en.eq(1),
                             st_w.addr.eq(bump_v), st_w.data.eq(sctr), st_w.en.eq(1)]
                m.d.sync += [vlast.eq(bump_v), sctr.eq(sctr + 1)]
                m.next = "BUMP_APPEND2"
            with m.State("BUMP_APPEND2"):
                m.d.comb += [nx_w.addr.eq(bump_v), nx_w.data.eq(NIL_V), nx_w.en.eq(1)]
                m.next = "BUMP_SEARCH_RD"
            with m.State("BUMP_SEARCH_RD"):
                m.d.comb += val_r.addr.eq(bump_v)
                m.next = "BUMP_SEARCH"
            with m.State("BUMP_SEARCH"):
                with m.If(~val_r.data[0]):
                    m.d.sync += vsearch.eq(bump_v)
                m.next = "AN_CLEAR_RD"

            # backjump level: the highest level among literals 1.., moved to position 1
            with m.State("BT_FIND_RD"):
                with m.If(i == lsize):
                    m.d.sync += btlvl.eq(Mux(lsize == 1, 0, bmaxlvl))
                    with m.If(learn_too_long):
                        m.d.sync += info_extra.eq(info_extra | INFO_LEARN_TOO_LONG)
                        m.next = "DONE"                   # UNKNOWN: a clause this long cannot be learned
                    with m.Elif(lsize > 2):
                        m.d.comb += lb_r.addr.eq(bmax)
                        m.next = "BT_SWAP_A"
                    with m.Else():
                        m.d.sync += i.eq(0)
                        m.next = "BT_START"
                with m.Else():
                    m.d.comb += lb_r.addr.eq(i)
                    m.next = "BT_FIND_LIT"
            with m.State("BT_FIND_LIT"):
                m.d.sync += vq.eq(lb_r.data)
                m.d.comb += lvl_r.addr.eq(var(lb_r.data))
                m.next = "BT_FIND_LVL"
            with m.State("BT_FIND_LVL"):
                with m.If(lvl_r.data > bmaxlvl):
                    m.d.sync += [bmaxlvl.eq(lvl_r.data), bmax.eq(i)]
                m.d.sync += curlvl.eq(lvl_r.data)
                m.d.comb += ls_r.addr.eq(lvl_r.data)
                m.next = "BT_LSTAMP"
            with m.State("BT_LSTAMP"):          # a level not counted yet for this conflict
                with m.If(ls_r.data != self.conflicts):
                    m.d.comb += [ls_w.addr.eq(curlvl), ls_w.data.eq(self.conflicts), ls_w.en.eq(1)]
                    with m.If(lbd != 255):
                        m.d.sync += lbd.eq(lbd + 1)
                m.d.sync += i.eq(i + 1)
                m.next = "BT_FIND_RD"
            with m.State("BT_SWAP_A"):
                m.d.sync += l1.eq(lb_r.data)            # the highest-level literal
                m.d.comb += lb_r.addr.eq(1)
                m.next = "BT_SWAP_B"
            with m.State("BT_SWAP_B"):
                m.d.comb += [lb_w.addr.eq(bmax), lb_w.data.eq(lb_r.data), lb_w.en.eq(1)]
                m.next = "BT_SWAP_C"
            with m.State("BT_SWAP_C"):
                m.d.comb += [lb_w.addr.eq(1), lb_w.data.eq(l1), lb_w.en.eq(1)]
                m.d.sync += i.eq(0)
                m.next = "BT_START"

            # backtrack to btlvl: unassign, save phases, keep the VMTF search pointer at the latest free variable
            with m.State("BT_START"):
                m.d.comb += tl_r.addr.eq(btlvl)
                m.next = "BT_LIM"
            with m.State("BT_LIM"):
                m.d.sync += bt_to.eq(Mux(btlvl == dl, tlen, tl_r.data))
                m.next = "BT_RD"
            with m.State("BT_RD"):
                with m.If((tlen == bt_to) & reducing):
                    m.d.sync += [dl.eq(0), qhead.eq(bt_to), i.eq(0)]
                    m.next = "RD_HCLR"
                with m.Elif((tlen == bt_to) & restarting):
                    m.d.sync += [dl.eq(btlvl), qhead.eq(bt_to), restarting.eq(0)]
                    m.next = "PROP"
                with m.Elif(tlen == bt_to):
                    m.d.sync += [dl.eq(btlvl), qhead.eq(bt_to), i.eq(0), learning.eq(1)]
                    m.next = "LEARN"
                with m.Else():
                    m.d.comb += tr_r.addr.eq(tlen - 1)
                    m.next = "BT_LIT"
            with m.State("BT_LIT"):
                v_ = var(tr_r.data)
                m.d.comb += [val_w.addr.eq(v_), val_w.data.eq(0), val_w.en.eq(1),
                             sav_w.addr.eq(v_), sav_w.data.eq(tr_r.data[0]), sav_w.en.eq(1),
                             st_r.addr.eq(v_), st2_r.addr.eq(vsearch[:VB])]
                m.d.sync += [tlen.eq(tlen - 1), bump_v.eq(v_)]
                m.next = "BT_STAMP"
            with m.State("BT_STAMP"):
                # the search pointer moves to the freed variable if it is later in the queue
                with m.If((vsearch == NIL_V) | (st_r.data > st2_r.data)):
                    m.d.sync += vsearch.eq(bump_v)
                m.next = "BT_RD"

            # ------------------------------------------------------------ learn the clause in lbuf[0:lsize]
            with m.State("LEARN"):
                # stream the clause out for verification
                with m.If(i == lsize):
                    m.d.comb += self.dbg_learn_end.eq(1)
                    m.d.sync += i.eq(0)
                    m.next = "LEARN_STORE"
                with m.Else():
                    m.d.comb += lb_r.addr.eq(i)
                    m.next = "LEARN_DBG"
            with m.State("LEARN_DBG"):
                m.d.comb += [self.dbg_learn_lit.eq(lb_r.data), self.dbg_learn_valid.eq(1)]
                m.d.sync += i.eq(i + 1)
                m.next = "LEARN"
            with m.State("LEARN_STORE"):
                with m.If(lsize == 1):
                    m.d.comb += lb_r.addr.eq(0)
                    m.d.sync += rsrc.eq(R_NONE)
                    m.next = "LEARN_UNIT"
                with m.Elif(lsize == 2):
                    m.d.comb += lb_r.addr.eq(0)
                    m.next = "LEARN_BIN0"
                with m.Elif((aptr + 2 + lsize >= ARENA - 1) | (wptr + 2 >= WN - 1)):
                    m.d.sync += [oom.eq(1), info_extra.eq(info_extra | INFO_OUT_OF_MEMORY)]
                    m.next = "DONE"
                with m.Else():
                    m.d.comb += [arena_w.addr.eq(aptr), arena_w.data.eq(lsize), arena_w.en.eq(1)]
                    m.d.sync += [cref.eq(aptr), i.eq(0)]
                    m.next = "LEARN_HDR2"
            with m.State("LEARN_HDR2"):
                m.d.comb += [arena_w.addr.eq(cref + 1), arena_w.data.eq(Cat(lbd, Const(1, 1))), arena_w.en.eq(1)]
                m.next = "LEARN_COPY_RD"
            with m.State("LEARN_UNIT"):
                m.d.sync += lit.eq(lb_r.data)
                m.next = "LEARN_ASSIGN"
            with m.State("LEARN_BIN0"):
                m.d.sync += lit.eq(lb_r.data)
                m.d.comb += lb_r.addr.eq(1)
                m.next = "LEARN_BIN1"
            with m.State("LEARN_BIN1"):
                with m.If(bptr + 2 >= BN - 1):
                    m.d.sync += [oom.eq(1), info_extra.eq(info_extra | INFO_OUT_OF_MEMORY)]
                    m.next = "DONE"
                with m.Else():
                    m.d.sync += [klit.eq(lb_r.data), rsrc.eq(R_BIN | lb_r.data), i.eq(0), first.eq(lit)]
                    m.next = "BIN_ADD_RD"
            with m.State("LEARN_COPY_RD"):
                with m.If(i == lsize):
                    m.d.sync += [aptr.eq(aptr + 2 + lsize), rsrc.eq(cref)]
                    m.d.comb += lb_r.addr.eq(0)
                    m.next = "LEARN_W0"
                with m.Else():
                    m.d.comb += lb_r.addr.eq(i)
                    m.next = "LEARN_COPY"
            with m.State("LEARN_COPY"):
                m.d.comb += [arena_w.addr.eq(cref + 2 + i), arena_w.data.eq(lb_r.data), arena_w.en.eq(1)]
                m.d.sync += i.eq(i + 1)
                m.next = "LEARN_COPY_RD"
            with m.State("LEARN_W0"):
                m.d.sync += [lit.eq(lb_r.data), first.eq(lb_r.data)]
                m.d.comb += lb_r.addr.eq(1)
                m.next = "LEARN_W1"
            with m.State("LEARN_W1"):
                m.d.sync += [klit.eq(lb_r.data), i.eq(0)]
                m.next = "WATCH_ADD_RD"
            with m.State("LEARN_ASSIGN"):
                # the asserting literal: lbuf[0] (in `first` for binary/long, `lit` for a unit)
                al = Mux(lsize == 1, lit, first)
                m.d.comb += [val_w.addr.eq(var(al)), val_w.data.eq(Cat(1, ~al[0])), val_w.en.eq(1),
                             lvl_w.addr.eq(var(al)), lvl_w.data.eq(dl), lvl_w.en.eq(1),
                             rsn_w.addr.eq(var(al)), rsn_w.data.eq(rsrc), rsn_w.en.eq(1),
                             tr_w.addr.eq(tlen), tr_w.data.eq(al), tr_w.en.eq(1)]
                m.d.sync += [tlen.eq(tlen + 1), learning.eq(0), learn_too_long.eq(0)]
                m.next = "EMA_UPD"
            # exponential moving averages of LBD, warm-up rate 2^-floor(log2 conflicts) (the model does the same)
            with m.State("EMA_UPD"):
                msb = Signal(5)
                for b_ in range(32):
                    with m.If(self.conflicts[b_]):
                        m.d.comb += msb.eq(b_)
                sf = Mux(msb > 5, 5, msb)
                ss = Mux(msb > 17, 17, msb)
                xv = Signal(signed(34))
                m.d.comb += xv.eq(lbd << 16)
                m.d.sync += [ema_fast.eq(ema_fast + ((xv - ema_fast) >> sf)),
                             ema_slow.eq(ema_slow + ((xv - ema_slow) >> ss))]
                m.next = "REDUCE_CHK"
            with m.State("REDUCE_CHK"):
                full = (aptr > (ARENA * 9) // 10) | (wptr > (WN * 9) // 10)
                with m.If(full | (self.conflicts >= reduce_at)):
                    m.d.sync += [forced.eq(full), reducing.eq(1), btlvl.eq(0), self.reduces.eq(self.reduces + 1)]
                    with m.If(~full):
                        m.d.sync += [reduce_k.eq(reduce_k + 1),
                                     reduce_at.eq(self.conflicts + 2000 + 300 * (reduce_k + 1))]
                    m.next = "BT_START"
                with m.Else():
                    m.next = "RESTART_CHK"
            with m.State("RESTART_CHK"):
                with m.If((dl != 0) & (self.conflicts - last_restart >= 2) &
                          (ema_fast > ema_slow + (ema_slow >> 3))):
                    m.d.sync += [self.restarts.eq(self.restarts + 1), last_restart.eq(self.conflicts),
                                 btlvl.eq(0), restarting.eq(1)]
                    m.next = "BT_START"
                with m.Else():
                    m.next = "PROP"

            # ------------------------------------------------------------ reduction (at level 0)
            with m.State("RD_HCLR"):            # clear the LBD histogram
                with m.If(i == 256):
                    m.d.sync += [rp.eq(0), ncand.eq(0)]
                    m.next = "RD1_RD"
                with m.Else():
                    m.d.comb += [hi_w.addr.eq(i), hi_w.data.eq(0), hi_w.en.eq(1)]
                    m.d.sync += i.eq(i + 1)
            # pass 1: histogram of the candidates
            with m.State("RD1_RD"):
                with m.If(rp >= aptr):
                    m.d.sync += [kill.eq(Mux(forced, ((ncand << 1) + ncand) >> 2, ncand >> 1)), acc.eq(0), thr.eq(255)]
                    m.next = "RD_TH_RD"
                with m.Else():
                    m.d.comb += arena_r.addr.eq(rp)
                    m.next = "RD1_HDR"
            with m.State("RD1_HDR"):
                m.d.sync += hsz.eq(arena_r.data[:SZW])
                m.d.comb += arena_r.addr.eq(rp + 1)
                m.next = "RD1_HDR2"
            candidate = lambda h: h[8] & ~(h[:8] <= 2) & ~((h[:8] <= 6) & h[9])
            with m.State("RD1_HDR2"):
                m.d.sync += [hd2.eq(arena_r.data), rp.eq(rp + 2 + hsz)]
                with m.If(candidate(arena_r.data)):
                    m.d.comb += hi_r.addr.eq(arena_r.data[:8])
                    m.next = "RD1_HIST"
                with m.Else():
                    m.next = "RD1_RD"
            with m.State("RD1_HIST"):
                m.d.comb += [hi_w.addr.eq(hd2[:8]), hi_w.data.eq(hi_r.data + 1), hi_w.en.eq(1)]
                m.d.sync += ncand.eq(ncand + 1)
                m.next = "RD1_RD"
            # threshold: delete every candidate with LBD > thr, and `rem` of those with LBD == thr
            with m.State("RD_TH_RD"):
                with m.If(kill == 0):
                    m.d.sync += [thr.eq(256), rem.eq(0), rp.eq(0), wq.eq(0)]
                    m.next = "RD2_RD"
                with m.Else():
                    m.d.comb += hi_r.addr.eq(thr[:8])
                    m.next = "RD_TH"
            with m.State("RD_TH"):
                with m.If(acc + hi_r.data >= kill):
                    m.d.sync += [rem.eq(kill - acc), rp.eq(0), wq.eq(0)]
                    m.next = "RD2_RD"
                with m.Else():
                    m.d.sync += [acc.eq(acc + hi_r.data), thr.eq(thr - 1)]
                    m.next = "RD_TH_RD"
            # pass 2: delete and compact
            with m.State("RD2_RD"):
                with m.If(rp >= aptr):
                    m.d.sync += [aptr.eq(wq), i.eq(0)]
                    m.next = "RD_WCLR"
                with m.Else():
                    m.d.comb += arena_r.addr.eq(rp)
                    m.next = "RD2_HDR"
            with m.State("RD2_HDR"):
                m.d.sync += hsz.eq(arena_r.data[:SZW])
                m.d.comb += arena_r.addr.eq(rp + 1)
                m.next = "RD2_HDR2"
            with m.State("RD2_HDR2"):
                h = arena_r.data
                lbd_ = Cat(h[:8], Const(0, 1))
                dele = candidate(h) & ((lbd_ > thr) | ((lbd_ == thr) & (rem != 0)))
                with m.If(dele):
                    with m.If(lbd_ == thr):
                        m.d.sync += rem.eq(rem - 1)
                    m.d.sync += rp.eq(rp + 2 + hsz)
                    m.next = "RD2_RD"
                with m.Else():
                    # keep: header words to wq (used flag cleared), then the literals
                    m.d.comb += [arena_w.addr.eq(wq), arena_w.data.eq(hsz), arena_w.en.eq(1)]
                    m.d.sync += [hd2.eq(h & ~(1 << 9)), cpos.eq(0)]
                    m.next = "RD2_HDR2W"
            with m.State("RD2_HDR2W"):
                m.d.comb += [arena_w.addr.eq(wq + 1), arena_w.data.eq(hd2), arena_w.en.eq(1)]
                m.next = "RD2_CP_RD"
            with m.State("RD2_CP_RD"):
                with m.If(cpos == hsz):
                    m.d.sync += [rp.eq(rp + 2 + hsz), wq.eq(wq + 2 + hsz)]
                    m.next = "RD2_RD"
                with m.Else():
                    m.d.comb += arena_r.addr.eq(rp + 2 + cpos)
                    m.next = "RD2_CP"
            with m.State("RD2_CP"):
                m.d.comb += [arena_w.addr.eq(wq + 2 + cpos), arena_w.data.eq(arena_r.data), arena_w.en.eq(1)]
                m.d.sync += cpos.eq(cpos + 1)
                m.next = "RD2_CP_RD"
            # rebuild every watch list
            with m.State("RD_WCLR"):
                with m.If(i == 2 * NV):
                    m.d.sync += [wptr.eq(0), rp.eq(0)]
                    m.next = "RD3_RD"
                with m.Else():
                    m.d.comb += [wh_w.addr.eq(i), wh_w.data.eq(NIL_W), wh_w.en.eq(1)]
                    m.d.sync += i.eq(i + 1)
            with m.State("RD3_RD"):
                with m.If(rp >= aptr):
                    # done: propagate the root trail again over the new watches
                    m.d.sync += [reducing.eq(0), qhead.eq(0)]
                    with m.If(forced & ((aptr > (ARENA * 9) // 10) | (wptr > (WN * 9) // 10))):
                        m.d.sync += [oom.eq(1), info_extra.eq(info_extra | INFO_OUT_OF_MEMORY)]
                        m.next = "DONE"                   # nothing left to delete: out of memory
                    with m.Else():
                        m.next = "PROP"
                with m.Else():
                    m.d.comb += arena_r.addr.eq(rp)
                    m.next = "RD3_HDR"
            with m.State("RD3_HDR"):
                m.d.sync += [hsz.eq(arena_r.data[:SZW]), cref.eq(rp)]
                m.d.comb += arena_r.addr.eq(rp + 2)
                m.next = "RD3_L0"
            with m.State("RD3_L0"):
                m.d.sync += lit.eq(arena_r.data)
                m.d.comb += arena_r.addr.eq(rp + 3)
                m.next = "RD3_L1"
            with m.State("RD3_L1"):
                m.d.sync += [klit.eq(arena_r.data), i.eq(0), rp.eq(rp + 2 + hsz)]
                m.next = "RD3_W_RD"
            with m.State("RD3_W_RD"):
                m.d.comb += wh_r.addr.eq(lit)
                m.next = "RD3_W"
            with m.State("RD3_W"):
                m.d.comb += [wn_w.addr.eq(wptr), wn_w.data.eq(wnode(cref, klit, wh_r.data)), wn_w.en.eq(1),
                             wh_w.addr.eq(lit), wh_w.data.eq(wptr), wh_w.en.eq(1)]
                m.d.sync += [wptr.eq(wptr + 1), lit.eq(klit), klit.eq(lit), i.eq(i + 1)]
                with m.If(i == 1):
                    m.next = "RD3_RD"
                with m.Else():
                    m.next = "RD3_W_RD"

            # ------------------------------------------------------------ decisions (VMTF)
            with m.State("DECIDE_RD"):
                with m.If(vsearch == NIL_V):
                    m.d.sync += sat.eq(1)
                    m.next = "DONE"
                with m.Else():
                    m.d.comb += [val_r.addr.eq(vsearch), pv_r.addr.eq(vsearch), sav_r.addr.eq(vsearch)]
                    m.next = "DECIDE"
            with m.State("DECIDE"):
                with m.If(val_r.data[0]):
                    m.d.sync += vsearch.eq(pv_r.data)
                    m.next = "DECIDE_RD"
                with m.Else():
                    dlit_ = Cat(sav_r.data, vsearch[:VB])
                    m.d.comb += [tl_w.addr.eq(dl), tl_w.data.eq(tlen), tl_w.en.eq(1),
                                 val_w.addr.eq(vsearch), val_w.data.eq(Cat(1, ~sav_r.data)), val_w.en.eq(1),
                                 lvl_w.addr.eq(vsearch), lvl_w.data.eq(dl + 1), lvl_w.en.eq(1),
                                 rsn_w.addr.eq(vsearch), rsn_w.data.eq(R_NONE), rsn_w.en.eq(1),
                                 tr_w.addr.eq(tlen), tr_w.data.eq(dlit_), tr_w.en.eq(1)]
                    m.d.sync += [dl.eq(dl + 1), tlen.eq(tlen + 1), self.decisions.eq(self.decisions + 1)]
                    m.next = "PROP"

            # ------------------------------------------------------------ answers
            with m.State("DONE"):
                m.d.comb += [self.done.eq(1), self.result.eq(Mux(unsat, UNSAT, Mux(sat, SAT, UNKNOWN))),
                             self.info.eq(info_extra), val_r.addr.eq(self.model_addr[:VB])]
                m.d.comb += model_rd.eq(1)
            with m.State("DONE_REJECT"):
                m.d.comb += [self.rejected.eq(1), self.info.eq(INFO_REJECT_ARENA)]

        m.d.comb += self.model_val.eq(val_r.data[1])
        return m
