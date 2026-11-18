"""Bramble through the real register-map shell, in simulation.

The Gauss front end is tested on its own (behind the same shell): UNSAT only when the formula's XOR constraints are
inconsistent, UNKNOWN otherwise. The full solver (front end, then the CDCL core) must answer every small formula
correctly, with a model for SAT.
"""

import itertools

import pytest
from amaranth.sim import Simulator

import design as D
from amaranth import Elaboratable, Module, Signal, signed
from amaranth.hdl import ResetInserter
from solver import GaussFront


class GaussOnly(Elaboratable):
    """The Gauss front end alone, with the solver interface (its UNKNOWN is final here)."""
    max_vars, max_clauses, max_lits = 512, 1 << 20, 1 << 22

    def __init__(self):
        self.f = GaussFront()
        for name in ("start", "abort", "nvars", "nclauses", "nlits", "load_valid", "load_data", "model_addr",
                     "idle", "load_ready", "done", "rejected", "result", "info", "model_val"):
            setattr(self, name, getattr(self.f, name))

    def elaborate(self, platform):
        m = Module()
        m.submodules.f = self.f
        return ResetInserter({"sync": self.abort})(m)

START, ABORT = 1, 2
S_BUSY, S_DONE, S_REJ = 1, 2, 4
UNKNOWN, SAT, UNSAT = 0, 1, 2


async def wb(ctx, dut, adr, we=False, data=0, wait=200000):
    ctx.set(dut.wb_adr, adr)
    ctx.set(dut.wb_we, int(we))
    ctx.set(dut.wb_dat_w, data & 0xFFFFFFFF)
    ctx.set(dut.wb_sel, 0xF)
    ctx.set(dut.wb_cyc, 1)
    ctx.set(dut.wb_stb, 1)
    for _ in range(wait):
        await ctx.tick()
        if ctx.get(dut.wb_ack):
            break
    else:
        raise AssertionError(f"no ack for address {adr}")
    value = ctx.get(dut.wb_dat_r)
    await ctx.tick()      # a real master holds the request through the edge that ends the ack cycle
    ctx.set(dut.wb_cyc, 0)
    ctx.set(dut.wb_stb, 0)
    await ctx.tick()
    return value


async def solve(ctx, dut, nvars, clauses, polls=20000):
    await wb(ctx, dut, D.R_CTRL, True, ABORT)
    for _ in range(100):
        if await wb(ctx, dut, D.R_STATUS) == 0:
            break
    await wb(ctx, dut, D.R_NVARS, True, nvars)
    await wb(ctx, dut, D.R_NCLAUSES, True, len(clauses))
    await wb(ctx, dut, D.R_NLITS, True, sum(len(c) for c in clauses))
    for c in clauses:
        for x in list(c) + [0]:
            await wb(ctx, dut, D.R_LOAD, True, x)
    await wb(ctx, dut, D.R_CTRL, True, START)
    for _ in range(polls):
        st = await wb(ctx, dut, D.R_STATUS)
        if st & (S_DONE | S_REJ):
            break
        for _ in range(50):
            await ctx.tick()
    else:
        raise AssertionError("no answer")
    assert st == S_DONE
    return await wb(ctx, dut, D.R_RESULT), await wb(ctx, dut, D.R_INFO)


def xor_clauses(vs, rhs):
    """CNF of x_vs[0] ^ ... = rhs: one clause per forbidden assignment."""
    out = []
    for bits in itertools.product((0, 1), repeat=len(vs)):
        if sum(bits) % 2 != rhs:               # forbidden: rule it out
            out.append([-v if b else v for v, b in zip(vs, bits)])
    return out


GAUSS_ONLY = 17   # declaring more variables than the brute force takes keeps these tests on the Gauss path


def run(cases):
    """cases: list of (nvars, clauses, expected result), run on one board with aborts in between, through the Gauss
    front end alone."""
    dut = D.Entry(solver_cls=GaussOnly)
    sim = Simulator(dut)
    sim.add_clock(1e-6)
    got = []

    async def bench(ctx):
        for nvars, clauses, _ in cases:
            got.append(await solve(ctx, dut, max(nvars, GAUSS_ONLY), clauses))

    sim.add_testbench(bench)
    sim.run()
    for (nv, cl, want), (res, info) in zip(cases, got):
        assert res == want, (nv, cl[:6], res, hex(info))
    return got


def triangle(rhs):   # x1^x2=1, x2^x3=1, x1^x3=rhs: inconsistent iff rhs == 1
    return xor_clauses([1, 2], 1) + xor_clauses([2, 3], 1) + xor_clauses([1, 3], rhs)


def test_capacity_is_declared():
    import cdcl
    from solver import Solver
    assert (Solver.max_vars, Solver.max_clauses, Solver.max_lits) == (cdcl.NV - 1, (1 << 16) - 1, cdcl.ARENA)


def test_inconsistent_xors_are_unsat_and_consistent_ones_unknown():
    run([(3, triangle(1), UNSAT), (3, triangle(0), UNKNOWN)])


def test_wide_xors_shuffled_literals_and_clause_order():
    import random
    rnd = random.Random(5)
    # x1^x2^x3^x4 = 1, x3^x4^x5 = 0, x1^x2^x5 = 0  ->  sum: 0 = 1
    cl = xor_clauses([1, 2, 3, 4], 1) + xor_clauses([3, 4, 5], 0) + xor_clauses([1, 2, 5], 0)
    for c in cl:
        rnd.shuffle(c)
    rnd.shuffle(cl)
    run([(5, cl, UNSAT)])


def test_seven_wide_xor():
    cl = xor_clauses(list(range(1, 8)), 1) + xor_clauses(list(range(1, 8)), 0)[:1] + [[1], [2], [3], [4], [5], [6], [-7]]
    # the units force x1..x6 true, x7 false: parity 6 -> 0, but the XOR wants 1
    run([(7, xor_clauses(list(range(1, 8)), 1) + [[1], [2], [3], [4], [5], [6], [-7]], UNSAT)])
    del cl


def test_a_missing_clause_subsumed_by_a_shorter_one_still_makes_an_xor():
    # MRB0-086's shape: x13^x14^x15 = 1 with (13, -14, -15) replaced by its subsumer (13, -15)
    x = xor_clauses([1, 2, 3], 1)
    x = [c for c in x if sorted(c, key=abs) != [1, -2, -3]] + [[1, -3]]
    cl = x + xor_clauses([1, 2], 1) + xor_clauses([3], 1)   # x1^x2 = 1, x3 = 1  ->  x1^x2^x3 = 0, not 1
    run([(3, cl, UNSAT)])
    # without the subsumer the set is not an XOR, and nothing is claimed
    cl2 = [c for c in cl if c != [1, -3]]
    run([(3, cl2, UNKNOWN)])


def test_every_missing_clause_must_be_subsumed_not_just_one():
    # x1^x2^x3 = 1 with TWO clauses gone and a subsumer for only one of them: not an XOR. Taking it as one
    # would "prove" UNSAT, but the formula is satisfiable (x1=1, x2=0, x3=1).
    x = [c for c in xor_clauses([1, 2, 3], 1) if sorted(c, key=abs) not in ([1, -2, -3], [-1, 2, -3])]
    cl = x + [[1, -3]] + xor_clauses([1, 2], 1) + xor_clauses([3], 1)
    model = {1: True, 2: False, 3: True}
    assert all(any(model[abs(l)] == (l > 0) for l in c) for c in cl)
    run([(3, cl, UNKNOWN)])


def test_satisfiable_and_non_xor_formulas_are_never_unsat():
    import random
    rnd = random.Random(1)
    cases = []
    for t in range(4):
        n = 12
        hidden = {v: rnd.random() < 0.5 for v in range(1, n + 1)}
        cl = []
        while len(cl) < 40:
            vs = rnd.sample(range(1, n + 1), 3)
            c = [v if rnd.random() < 0.5 else -v for v in vs]
            if any(hidden[abs(l)] == (l > 0) for l in c):
                cl.append(c)
        cases.append((n, cl, UNKNOWN))
    # a consistent XOR system mixed into a satisfiable formula
    cases.append((4, xor_clauses([1, 2, 3], 1) + xor_clauses([2, 3, 4], 0) + [[1, 2, -4]], UNKNOWN))
    run(cases)


def test_duplicates_tautologies_and_long_clauses_are_handled():
    cl = triangle(1)
    cl = [c + [c[0]] for c in cl]                       # duplicate literal in every clause
    cl += [[1, -1, 2], list(range(1, 4)) + [-1]]        # tautologies
    cl += [[1, 2, 3, 4, 5, 6, 7, 8]]                    # wider than K: left out
    run([(8, cl, UNSAT)])


def test_variables_past_the_columns_are_left_out_not_misread():
    # var 600 > 512: the instance is over the declared capacity, so the runner would skip it; if it is loaded
    # anyway the clauses with such a variable are dropped and nothing wrong is claimed.
    run([(3, triangle(1) + [[600, 1]], UNSAT), (3, xor_clauses([1, 600], 1) + xor_clauses([1], 0), UNKNOWN)])


def test_abort_mid_load_then_a_clean_second_instance():
    dut = D.Entry(solver_cls=GaussOnly)
    sim = Simulator(dut)
    sim.add_clock(1e-6)
    out = []

    async def bench(ctx):
        await wb(ctx, dut, D.R_CTRL, True, ABORT)
        for _ in range(100):
            if await wb(ctx, dut, D.R_STATUS) == 0:
                break
        await wb(ctx, dut, D.R_NVARS, True, GAUSS_ONLY)
        for c in triangle(1)[:3]:                       # half an inconsistent instance, then abort
            for x in c + [0]:
                await wb(ctx, dut, D.R_LOAD, True, x)
        out.append(await solve(ctx, dut, GAUSS_ONLY, triangle(0)))   # must not see the leftovers

    sim.add_testbench(bench)
    sim.run()
    assert out[0][0] == UNKNOWN


# ---------------------------------------------------------------------------- the full solver (front end + CDCL core)
TINY_SAT = (4, [[1, 2], [-1, 3], [-2, -3], [3, 4], [-4, 1]])      # the pre-flight's built-in instances
TINY_UNSAT = (2, [[1, 2], [-1, 2], [1, -2], [-1, -2]])


async def model_of(ctx, dut, nvars, window=True):
    out = []
    for i in range(nvars):
        out.append(await wb(ctx, dut, D.R_MODEL if not window else 256 + (i % 256)))
    return [x - (1 << 32) if x & (1 << 31) else x for x in out]


def solve_with_models(cases):
    dut = D.Entry()
    sim = Simulator(dut)
    sim.add_clock(1e-6)
    got = []

    async def bench(ctx):
        for nvars, clauses in cases:
            res, info = await solve(ctx, dut, nvars, clauses)
            mw = await model_of(ctx, dut, nvars, window=True) if res == SAT else None
            got.append((res, info, mw))

    sim.add_testbench(bench)
    sim.run()
    return got


def satisfies(model, clauses):
    val = {abs(x): x > 0 for x in model}
    return all(any(val[abs(l)] == (l > 0) for l in c) for c in clauses)


def test_the_preflight_builtins_are_answered_correctly_with_a_model():
    (r1, i1, m1), (r2, i2, _) = solve_with_models([TINY_SAT, TINY_UNSAT])
    assert r1 == SAT and sorted(abs(x) for x in m1) == [1, 2, 3, 4] and satisfies(m1, TINY_SAT[1])
    assert r2 == UNSAT


def test_random_small_formulas_match_exhaustive_search():
    import random
    rnd = random.Random(3)
    cases = []
    for t in range(8):
        n = rnd.randint(1, 10)
        cl = [[rnd.choice((1, -1)) * rnd.randint(1, n) for _ in range(rnd.randint(1, 3))] for _ in range(rnd.randint(1, 30))]
        cases.append((n, cl))
    cases += [(0, []), (1, [[]] if False else [[1], [-1]]), (16, [[16], [-1], [1, 2, -16]])]
    got = solve_with_models(cases)
    for (n, cl), (res, info, model) in zip(cases, got):
        exists = any(all(any(((a >> (abs(l) - 1)) & 1) == (l > 0) for l in c) for c in cl) for a in range(1 << n))
        if exists:
            assert res == SAT and satisfies(model, cl), (n, cl, res)
        else:
            assert res == UNSAT, (n, cl, res)


def test_start_abort_then_a_correct_solve():   # the pre-flight's abort smoke test
    dut = D.Entry()
    sim = Simulator(dut)
    sim.add_clock(1e-6)
    out = []

    async def bench(ctx):
        n, cl = TINY_SAT
        await wb(ctx, dut, D.R_CTRL, True, ABORT)
        for _ in range(100):
            if await wb(ctx, dut, D.R_STATUS) == 0:
                break
        await wb(ctx, dut, D.R_NVARS, True, n)
        await wb(ctx, dut, D.R_NCLAUSES, True, len(cl))
        await wb(ctx, dut, D.R_NLITS, True, sum(map(len, cl)))
        for c in cl:
            for x in c + [0]:
                await wb(ctx, dut, D.R_LOAD, True, x)
        await wb(ctx, dut, D.R_CTRL, True, START)
        res, info = await solve(ctx, dut, n, cl)        # aborts first, then solves again
        out.append((res, await model_of(ctx, dut, n, window=False)))

    sim.add_testbench(bench)
    sim.run()
    res, model = out[0]
    assert res == SAT and satisfies(model, TINY_SAT[1])


def test_the_core_takes_over_when_gauss_proves_nothing_and_gauss_answers_first_when_it_can():
    (r1, _, m1), (r2, i2, _) = solve_with_models([(17, [[17], [1, 2]]), (17, triangle(1))])
    assert r1 == SAT and satisfies(m1, [[17], [1, 2]])
    assert r2 == UNSAT and i2 & (1 << 19)     # INFO_GAUSS: the front end proved it
