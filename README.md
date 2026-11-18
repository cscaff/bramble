# Bramble

A SAT solver designed from scratch for the AgentSAT target: a Lattice ECP5-85F behind the competition's Wishbone
register map, scored on PAR-2 and chip share. Organizer-built; intended as a disclosed reference entry.

Nothing here is RTL yet. `model/bramble.cpp` is a cycle-costed model of the planned hardware: it really solves,
while charging each step the clock cycles the hardware would spend, so architecture choices are measured on the
competition's instances before any RTL is written. Its cost constants are estimates until the RTL is checked
against them in Verilator.

## Architecture (as modelled)

- **Clause-parallel propagation.** P clause banks; when a literal becomes false, every bank scans its own watch
  list for it at once. A clause goes to the bank whose watch lists for its two watched literals are shortest.
- **Binary-implication unit** beside the banks; binary clauses never touch them.
- **Elastic partitioning.** Watch-list heads cost 2 x vars words per bank, so a large instance runs on fewer banks
  instead of being rejected.
- **VMTF decisions** (constant-time list moves, no heap); an EVSIDS heap is optional in stable mode.
- **XOR recovery + Gauss-Jordan elimination over GF(2)** before search, in BRAM borrowed from the idle clause banks.
  An inconsistent system proves UNSAT; reduced rows give units and equivalences. A missing XOR clause is accepted
  when a shorter clause subsumes it.
- **Concurrent local search** (probSAT, critical variable as an XOR of true variables). Phases flow both ways.
- **Tiered clause-database reduction** by LBD, forced early when the banks fill up.

## Use

```
clang++ -std=c++17 -O2 -o model/bramble model/bramble.cpp
model/bramble bench/MRB0-084.cnf --limit=300 -v       # one instance
tools/bench.py NAME --jobs=6 --limit=300 -- [model options]   # all public instances, PAR-2 summary
```

`bench/` holds the 70 public instances (not committed). Options: `--P`, `--mhz`, `--limit`, `--no-sls`,
`--no-gauss`, `--stable=vsids|vmtf|off`, `--check` (proof-check every learned clause and audit every propagation;
slow). A SAT answer is always checked against the clauses.

## Status (2026-11-18)

- kissat on a ~3.5 GHz CPU, 300 s: 44/70 solved, PAR-2 249 s.
- Gauss alone solves all 7 Tseitin instances in under 3 ms simulated (kissat times out on 5) and MRB0-094
  (binary-tree parity, kissat times out) in 0.1 s.
