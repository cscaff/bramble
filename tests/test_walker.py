"""The local-search walker on its own: it copies the clauses the core announces, then walks. Whenever it claims SAT its
assignment must satisfy every clause (units, binaries and long clauses, planted-satisfiable formulas)."""
import random

import pytest
from amaranth.sim import Simulator

import walker


def lit(l):
    return 2 * (abs(l) - 1) + (1 if l < 0 else 0)


def planted(seed, nv, ratio):
    rnd = random.Random(seed)
    sol = {v: rnd.random() < 0.5 for v in range(1, nv + 1)}
    cls = []
    for _ in range(int(nv * ratio)):
        c = [rnd.choice((1, -1)) * v for v in rnd.sample(range(1, nv + 1), min(rnd.choice([1, 2, 2, 3, 3, 3, 4, 6, 9]), nv))]
        if not any((l > 0) == sol[abs(l)] for l in c):
            c[0] = -c[0]
        cls.append(c)
    return cls


def walk(cls, nv, cycles=400_000):
    dut = walker.Walker()
    sim = Simulator(dut)
    sim.add_clock(1e-6)
    arena = [0] * (sum(len(c) + 2 for c in cls) + 10)
    out = {}

    async def bench(ctx):
        pos = 0
        for c in cls:
            if len(c) == 1:
                ctx.set(dut.ev_kind, 0), ctx.set(dut.ev_l0, lit(c[0]))
            elif len(c) == 2:
                ctx.set(dut.ev_kind, 1), ctx.set(dut.ev_l0, lit(c[0])), ctx.set(dut.ev_l1, lit(c[1]))
            else:
                arena[pos] = len(c)
                for k, l in enumerate(c):
                    arena[pos + 2 + k] = lit(l)
                ctx.set(dut.ev_kind, 2), ctx.set(dut.ev_cref, pos), ctx.set(dut.ev_len, len(c))
                pos += 2 + len(c)
            ctx.set(dut.ev_valid, 1)
            await ctx.tick()
        ctx.set(dut.ev_valid, 0)
        ctx.set(dut.nvars, nv)
        ctx.set(dut.go, 1)
        await ctx.tick()
        ctx.set(dut.go, 0)
        granted, addr = 0, 0
        for _ in range(cycles):            # the arena answers last cycle's request
            ctx.set(dut.arena_data, arena[addr] if addr < len(arena) else 0)
            ctx.set(dut.walk_ok, granted)
            granted, addr = ctx.get(dut.walk_req), ctx.get(dut.walk_addr)
            await ctx.tick()
            if ctx.get(dut.solved):
                model = {}
                for v in range(nv):
                    ctx.set(dut.model_addr, v)
                    await ctx.tick()
                    await ctx.tick()
                    model[v + 1] = ctx.get(dut.model_val)
                out["model"] = model
                return

    sim.add_testbench(bench)
    sim.run()
    return out.get("model")


@pytest.mark.parametrize("seed,nv,ratio", [(1, 60, 2.5), (2, 60, 2.5), (4, 200, 3.0)])
def test_a_claimed_model_satisfies_every_clause(seed, nv, ratio):
    cls = planted(seed, nv, ratio)
    model = walk(cls, nv)
    assert model is not None, "the walker should find a planted solution this small"
    for c in cls:
        assert any((model[abs(l)] == 1) == (l > 0) for l in c), c
