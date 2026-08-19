# Dead Ends Catalog — MOVED

**The authoritative dead-ends catalog is now the Lean file
[`EM/Meta/DeadEnds.lean`](../EM/Meta/DeadEnds.lean)** (machine-checked where
possible: witnessed entries are re-exported there via `#check`). Prose
discussion lives in the paper: `paper/why_its_hard.tex` and the dead-ends
appendix in `paper/appendix.tex`.

This stub exists because agent prompts and the coordinator historically
pointed at `docs/dead_ends.md`. **Read `EM/Meta/DeadEnds.lean` instead** —
it is kept up to date by the formalizer alongside the code. Always read
`deadEndCount` / `witnessedDeadEndCount` / `revivableDeadEndCount` from that
file; the figures quoted anywhere else (including here) go stale. As of
Session 307 they were 159 / 27 / 10; as of 2026-08-17 (Dead End #160, see
`docs/pe_dsl_retirement.md`) they were 160 / 24 / 10. **As of 2026-08-18 the catalogue was
reconstructed in full from the session logs into `tools/dead_ends.tsv` (single source of
truth; `python3 tools/gen_dead_ends.py` regenerates the registry block, the paper table
`paper/dead_ends_table.tex` and `docs/dead_ends_catalog.md`): 160 numbers, 150 entries (#25,
#64–#72 were never assigned), 29 genuinely witnessed, 10 revivable.**
**As of 2026-08-19 (Session 312, entries #161–#166: six statement-level near-misses from the
seed-average programme of sessions 309–311, all repaired in flight): 166 numbers, 156 entries
(#25, #64–#72 still the only unassigned numbers), 29 genuinely witnessed, 15 revivable.**

The `File` column of the tables there was re-verified against disk in
Session 307. Historical numbering aliases (Session 180's "#136", Session
234's "#137", the old "#138") are listed in the Lean docstring — check them
before citing a number from an old session log.

## Quick orientation (mirror — do not edit here, edit the Lean file)

Categories: **OS** orbit-specificity · **TM** technique mismatch ·
**SM** scale mismatch · **CI** circularity · **SF** structurally false
(counterexample) · **CO** definitional collapse · **DG** decorrelation gap ·
**AG** aggregate gap. Each entry carries a weak-MC "revival score" 0–3.

The two meta-obstacles that subsume most entries:

- **Four-Way Blocker**: every known equidistribution technique needs at
  least one of (1) independence of steps, (2) multiplicativity,
  (3) algebraic-geometric structure, (4) ergodic stationarity.
  The EM walk has none of the four.
- **Marginal/Joint Barrier**: all proved reductions extract *marginal*
  information about multiplier residues; DH needs the *joint*
  (position, multiplier) law to hit the death curve m(n) = −w(n)⁻¹.

Fundamental entries: #90 (population ≠ orbit, the core obstruction,
revival 3 via ensemble averaging), #117 (MultCancel ≠ WalkCancel,
revival 0). Notable proved-impossible: #20/#130 (generation ≠ coverage,
Z/4Z witness `alternating_walk_misses_two`), #125 (pairwise ≠ k-wise,
XOR), #129 (FFLM false — cyclotomic counterexample over 𝔽₂), #131
(Dobrushin coefficient ≡ 1 for deterministic walks).

**Note (Session 307):** #90 and #117 — the two entries carrying the whole
"why MC is hard" thesis — were the only fundamental entries with no formal
witness, so everything machine-checked was peripheral. Both are now witnessed
in `EM/Meta/OrbitBarrier.lean`, assembled into `integer_orbit_barrier_thesis`
(the integer analogue of the function-field `orbit_barrier_thesis`).
Counts are now 159 / 27 / 10.
The revival score is a *weak-MC* axis and says nothing about MC proper;
use the `MC-proper ledger` section of the Lean file when the target is MC itself.

## Rules for adding a dead end (unchanged)

Only add approaches analyzed to a clear obstruction (counterexample,
equivalence proof, or confirmed missing infrastructure) — never
speculative "probably won't work". Add the entry to
`EM/Meta/DeadEnds.lean` (table + `#check` witness if one exists),
and update the technique catalogs in `agents/catalogs/`.
