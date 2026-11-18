#!/usr/bin/env python3
"""Every public instance through the Verilated entry, the way the runner drives it; each answer is checked.

  verify/run_public.py TB_BINARY [--cap=CYCLES] [--model=MODEL_BINARY]

UNSAT must match the instance's known result; SAT must come with a model that satisfies every clause. With
--model, the Bramble model's own verdict is printed alongside (its Gauss stage should agree exactly with stage 1).
Instances over the declared capacity (max_vars) are reported as skipped, as the runner would.
"""
import subprocess, sys, tempfile, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "entry"))
from solver import Solver  # noqa: E402


def clauses_of(path):
    nv, cls, cur = 0, [], []
    for line in open(path):
        t = line.split()
        if not t or t[0] in ("c", "%"):
            continue
        if t[0] == "p":
            nv = int(t[2]); continue
        for x in map(int, t):
            if x == 0:
                cls.append(cur); cur = []
            else:
                cur.append(x)
    return nv, cls


def main():
    tb = sys.argv[1]
    opts = dict(a[2:].split("=", 1) for a in sys.argv[2:] if a.startswith("--"))
    cap = int(opts.get("cap", 200_000_000))
    rows = [l.split("\t") for l in (ROOT / "bench" / "index.tsv").read_text().splitlines()]
    bad, tally = [], {}
    for r in rows:
        iid, known = r[0], r[1]
        nv, cls = clauses_of(ROOT / "bench" / f"{iid}.cnf")
        nl = sum(map(len, cls))
        if nv > Solver.max_vars or len(cls) > Solver.max_clauses or nl > Solver.max_lits:
            verdict, extra = "SKIPPED", ""
        else:
            with tempfile.NamedTemporaryFile("w", suffix=".in", delete=False) as f:
                f.write(f"{nv} {len(cls)} {nl}\n" + " ".join(str(w) for c in cls for w in c + [0]) + "\n")
            t = time.time()
            out = subprocess.run([tb, f.name, str(cap)], capture_output=True, text=True).stdout
            Path(f.name).unlink()
            head = out.splitlines()[0] if out else "no output"
            f_ = dict(zip(head.split()[::2], head.split()[1::2]))
            res = f_.get("RESULT")
            verdict = {"0": "UNKNOWN", "1": "SAT", "2": "UNSAT"}.get(res, head)
            extra = f"info=0x{int(f_.get('INFO', 0)):x} cycles={f_.get('CYCLES', '?')} [{time.time() - t:.1f}s]"
            if verdict == "SAT":
                model = {abs(x): x > 0 for x in map(int, out.split("MODEL")[1].split())}
                if not all(any(model.get(abs(l)) == (l > 0) for l in c) for c in cls):
                    verdict = "SAT_INVALID"
        wrong = verdict == "SAT_INVALID" or (verdict == "UNSAT" and known == "sat") or \
            (verdict == "SAT" and known == "unsat")
        if wrong:
            bad.append(iid)
        mv = ""
        if "model" in opts and verdict != "SKIPPED":
            line = subprocess.run([opts["model"], str(ROOT / "bench" / f"{iid}.cnf"), "--limit=0.001"],
                                  capture_output=True, text=True).stdout.split()
            mv = "model:" + ("UNSAT" if "by_gauss" in line else "-")
        tally[verdict] = tally.get(verdict, 0) + 1
        print(f"{iid:20} {known:5} {verdict:11} {extra} {mv}{'  <-- WRONG' if wrong else ''}", flush=True)
    print(f"\n{tally}  wrong: {len(bad)} {bad}")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
