#!/usr/bin/env python3
"""Run the Bramble model on the public instances and score it like the competition (PAR-2 at the limit).

  tools/bench.py NAME [--jobs=6] [--limit=300] [--only=ID,ID] -- [model options]

Writes results/NAME.tsv (id, known, result, simulated seconds, conflicts, P, how) and prints a summary.
A SAT answer is checked against the clauses by the model itself (SAT_INVALID otherwise); an UNSAT answer is
checked against the instance's known result. Any wrong answer is reported loudly.
"""
import subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    argv = sys.argv[1:]
    model_opts = argv[argv.index("--") + 1:] if "--" in argv else []
    own = argv[:argv.index("--")] if "--" in argv else argv
    name = own[0]
    opts = dict(a[2:].split("=", 1) for a in own[1:] if a.startswith("--") and "=" in a)
    jobs, limit = int(opts.get("jobs", 6)), float(opts.get("limit", 300))
    rows = [l.split("\t") for l in (ROOT / "bench" / "index.tsv").read_text().splitlines()]
    if "only" in opts:
        keep = set(opts["only"].split(","))
        rows = [r for r in rows if r[0] in keep]
    known = {r[0]: r[1] for r in rows}

    def one(r):
        iid = r[0]
        t = time.time()
        p = subprocess.run([str(ROOT / "model" / "bramble"), str(ROOT / "bench" / f"{iid}.cnf"),
                            f"--limit={limit}", *model_opts], capture_output=True, text=True, timeout=7200)
        line = (p.stdout.strip().splitlines() or [""])[-1].split()
        f = dict(zip(line[::2], line[1::2]))
        res = f.get("result", "CRASH")
        secs = float(f.get("time_s", "nan"))
        how = "walker" if "by_walker" in line else "cdcl"
        wrong = res == "SAT_INVALID" or (res == "SAT" and known[iid] == "unsat") or \
            (res == "UNSAT" and known[iid] == "sat") or res == "CRASH"
        return iid, known[iid], res, secs, f.get("conflicts", ""), f.get("P", ""), how, wrong, time.time() - t

    out = []
    with ThreadPoolExecutor(jobs) as ex:
        for r in ex.map(one, rows):
            out.append(r)
            flag = "  <-- WRONG" if r[7] else ""
            print(f"{r[0]:20} {r[1]:5} {r[2]:9} {r[3]:9.3f}s  conf={r[4]:>9} P={r[5]} {r[6]}{flag}", flush=True)
    (ROOT / "results").mkdir(exist_ok=True)
    with open(ROOT / "results" / f"{name}.tsv", "w") as fo:
        for r in out:
            fo.write("\t".join(map(str, r[:8])) + "\n")
    solved = [r for r in out if r[2] in ("SAT", "UNSAT") and not r[7]]
    par2 = sum(r[3] if r in solved else 2 * limit for r in out) / len(out)
    wrong = [r[0] for r in out if r[7]]
    rej = sum(r[2] == "REJECTED" for r in out)
    print(f"\n{name}: solved {len(solved)}/{len(out)} (sat {sum(r[2] == 'SAT' for r in solved)}, "
          f"unsat {sum(r[2] == 'UNSAT' for r in solved)}), rejected {rej}, PAR-2 {par2:.1f}s, "
          f"wrong {len(wrong)} {wrong}")


if __name__ == "__main__":
    main()
