"""Verification top: the CDCL core and the walker together (no Gauss front end, no shell)."""
from amaranth import Elaboratable, Module, Mux, Signal

from cdcl import Cdcl
from walker import Walker


class WalkTop(Elaboratable):
    def __init__(self):
        self.core = Cdcl()
        self.walker = Walker()
        c = self.core
        for name in ("load_valid", "load_data", "load_ready", "nvars", "start", "rejected", "info", "model_addr",
                     "idle", "dbg_learn_lit", "dbg_learn_valid", "dbg_learn_end", "conflicts", "decisions",
                     "restarts", "reduces"):
            setattr(self, name, getattr(c, name))
        self.done = Signal()
        self.result = Signal(2)
        self.model_val = Signal()
        self.walk_solved = Signal()
        self.flips = self.walker.flips

    def elaborate(self, platform):
        m = Module()
        m.submodules.core = c = self.core
        m.submodules.walker = w = self.walker
        m.d.comb += [
            w.ev_valid.eq(c.ev_valid), w.ev_kind.eq(c.ev_kind), w.ev_l0.eq(c.ev_l0), w.ev_l1.eq(c.ev_l1),
            w.ev_cref.eq(c.ev_cref), w.ev_len.eq(c.ev_len), w.nvars.eq(c.nvars), w.go.eq(c.ev_done), c.walk_busy.eq(w.busy),
            w.stop.eq(c.done), w.arena_data.eq(c.arena_data), w.walk_ok.eq(c.walk_ok),
            c.walk_addr.eq(w.walk_addr), c.walk_req.eq(w.walk_req), w.model_addr.eq(c.model_addr),
            self.walk_solved.eq(w.solved),
            self.done.eq(c.done | w.solved),
            self.result.eq(Mux(w.solved, 1, c.result)),
            self.model_val.eq(Mux(w.solved, w.model_val, c.model_val)),
        ]
        return m
