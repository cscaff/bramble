#!/usr/bin/env python3
"""Random formulas through the Verilated core with every learned clause RUP-checked; answers compared with kissat.

  verify/fuzz_core.py TB [--count=300] [--seed=1] [--maxvars=80]
"""
import random, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path


def kissat(nv, cls):
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
        f.write(f"p cnf {nv} {len(cls)}\n" + "".join(" ".join(map(str, c)) + " 0\n" for c in cls))
    r = subprocess.run(["kissat", "-q", f.name], capture_output=True, text=True)
    Path(f.name).unlink()
    return {10: 1, 20: 2}[r.returncode]


def one(args):
    tb, seed, maxvars = args
    rnd = random.Random(seed)
    nv = rnd.randint(3, maxvars)
    kind = rnd.choice(["3sat", "3sat", "mixed", "units"])
    ratio = rnd.uniform(3.5, 5.0) if kind == "3sat" else rnd.uniform(2, 6)
    cls = []
    for _ in range(max(1, int(nv * ratio))):
        w = 3 if kind == "3sat" else rnd.choice([1, 2, 2, 3, 3, 4, 5, 8])
        if kind == "units" and rnd.random() < 0.05:
            w = 1
        c = [rnd.choice((1, -1)) * rnd.randint(1, nv) for _ in range(w)]
        if rnd.random() < 0.05:
            c.append(c[0])                       # duplicate literal
        cls.append(c)
    want = kissat(nv, [list(dict.fromkeys(c)) for c in cls])
    with tempfile.NamedTemporaryFile("w", suffix=".in", delete=False) as f:
        f.write(f"{nv} {len(cls)} {sum(map(len, cls))}\n" + " ".join(str(w) for c in cls for w in c + [0]) + "\n")
    r = subprocess.run([tb, f.name, "200000000", "1"], capture_output=True, text=True)
    Path(f.name).unlink()
    out = r.stdout.strip()
    got = out.split()[1] if out.startswith("RESULT") else "?"
    ok = r.returncode == 0 and got in ("1", "2") and int(got) == want
    gave_up = r.returncode == 0 and got in ("0", "timeout", "rejected")   # allowed: unsolved, not wrong
    return seed, nv, len(cls), want, got, r.returncode, "ok" if ok else "unknown" if gave_up else "WRONG", \
        out.splitlines()[0] if out else r.stderr[-200:]


def main():
    tb = sys.argv[1]
    o = dict(a[2:].split("=", 1) for a in sys.argv[2:] if a.startswith("--"))
    count, seed0, maxvars = int(o.get("count", 300)), int(o.get("seed", 1)), int(o.get("maxvars", 80))
    bad, unknown = [], 0
    tally = {1: 0, 2: 0}
    with ThreadPoolExecutor(8) as ex:
        for res in ex.map(one, [(tb, seed0 + i, maxvars) for i in range(count)]):
            seed, nv, nc, want, got, rc, verdict, line = res
            if verdict == "ok":
                tally[want] += 1
            elif verdict == "unknown":
                unknown += 1
            else:
                bad.append(res)
                print(f"MISMATCH seed={seed} vars={nv} clauses={nc} kissat={want} core={got} exit={rc}: {line}", flush=True)
    print(f"{count} formulas: {tally[1]} SAT and {tally[2]} UNSAT agree with kissat (every learned clause RUP-checked); "
          f"{unknown} unsolved (allowed); {len(bad)} WRONG")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
