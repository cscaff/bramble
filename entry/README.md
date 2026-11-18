# Bramble

An AgentSAT entry for the Lattice ECP5-85F, built from scratch around the chip's block RAM. Organizer-built
reference entry, developed in stages; this is **stage 1**.

## Stage 1: XOR recovery and Gauss-Jordan elimination

1. **Load.** Every clause of up to 7 literals goes into a hash table keyed by its sorted variable set, with a mask of
   the sign patterns seen for that set. Duplicate literals are dropped; tautologies, longer clauses and clauses that
   find no slot are left out.
2. **Scan.** A variable set is an XOR when its clauses cover every sign pattern of one parity. A missing pattern still
   counts when a shorter clause subsumes it (some benchmark sets were preprocessed that way).
3. **Gauss-Jordan.** The XOR rows are eliminated over GF(2), one 513-bit row-XOR per cycle.
4. **Check.** An all-zero row with right-hand side 1 proves the formula UNSAT.
5. **Small instances** (up to 16 variables) are also tried exhaustively, giving SAT with a model or UNSAT.

Everything else is UNKNOWN. UNSAT is only claimed from genuine XOR constraints of the formula or from an exhausted
search, and SAT only with an assignment that satisfies every clause, so no overflow or capacity limit can make an
answer wrong.

On the public instances this proves the 7 Tseitin formulas and MRB0-001 UNSAT, each in under 5 ms at 50 MHz.

Declared capacity: 512 variables. Resources (place and route, 50 MHz, entry share): about 7,300 LUTs, 3,450 FFs,
27 block RAMs, no DSPs.

## Next stages

A CDCL core with clause-parallel propagation across BRAM banks, then a concurrent local-search engine that trades
phases with it, and vivification of learned clauses through the same propagation datapath.

## Files

- `design.py`: the competition register-map shell, unchanged from the template.
- `solver.py`: the solver.
- `tests/`: simulation tests (`pytest`), including the shell's smoke tests.
