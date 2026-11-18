# Bramble

An AgentSAT entry for the Lattice ECP5-85F, built from scratch around the chip's block RAM. Organizer-built
reference entry, developed in stages; this is **stage 2**.

## How it solves

1. **Gauss front end.** Clauses of up to 7 literals go into a hash table keyed by their sorted variable set, with a
   mask of the sign patterns seen. A variable set is an XOR when its clauses cover every sign pattern of one parity
   (a missing pattern counts when a shorter clause subsumes it). The XOR rows are eliminated over GF(2), one 513-bit
   row-XOR per cycle; an all-zero row with right-hand side 1 proves the formula UNSAT. This proves the Tseitin
   formulas in milliseconds, which resolution-based solvers cannot do at all at this size.
2. **CDCL core**, on the same clause stream, if the front end proved nothing:
   - two watched literals with blockers, on linked node lists (moving a watch relinks the node; lists never need
     compacting), and a separate binary-implication list;
   - VMTF decisions with phase saving;
   - 1UIP learning with recursive minimization, LBD, restarts on moving averages of LBD;
   - tiered clause-database reduction (LBD <= 2 kept, <= 6 kept while used, the worse half of the rest deleted),
     compaction and a watch rebuild at the root.

UNSAT is claimed only from genuine XOR constraints or a conflict at decision level 0; SAT only with a full
assignment that satisfies every clause. Running out of any memory gives UNKNOWN (or a rejection at load), never a
wrong answer.

Declared capacity: 2,047 variables, 65,535 clauses, 32,768 literal slots for long clauses (at most 8K long and 4K
binary clauses). Resources (place and route at 50 MHz, full SoC): 167 of 208 block RAMs, about 18,800 LUTs and
8,100 FFs; user clock 57.6 MHz.

## Verification

- Every learned clause the hardware produces is RUP-checked in simulation (Verilator, a debug port streams them to
  the checker); 800 random formulas agree with kissat; public instances with up to 274,717 checked clauses.
- All 70 public instances in simulation: no wrong answer.
- On a real board: the pre-flight's checks and 10 public instances, 9 solved, no wrong answer.

## Next stages

A local-search engine (probSAT) beside the core, trading phases with it; stable mode and rephasing; a second
propagation bank.

## Files

- `design.py`: the competition register-map shell, unchanged from the template.
- `solver.py`: the Gauss front end, and the solver that runs it and then the core.
- `cdcl.py`: the CDCL core.
- `tests/`: simulation tests (`pytest`), including the shell's smoke tests.
