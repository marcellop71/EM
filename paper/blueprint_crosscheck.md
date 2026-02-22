# LeanArchitect Blueprint Cross-Check Report

Generated from `EM/Blueprint.lean` (20 key declarations annotated with `@[blueprint]`).

## Setup
- LeanArchitect v4.29.0-rc1 added as dependency
- 20 key theorems annotated in `EM/Blueprint.lean` (retroactive `attribute [blueprint]`)
- All 20 declarations: `\leanok` (zero sorry)
- Blueprint LaTeX and JSON generated via `lake exe extract_blueprint single EM.Blueprint`

## Misalignments Found

### 1. `gen_hitting_implies_gen_mc_proved` — MISSING PRECONDITIONS (FIXED)
- **Paper** (the_ensemble_reduction.tex:683): "If the generalized walk hits −1 cofinally for every prime q, then GenMullinConjecture(n) holds."
- **Lean**: `∀ (n : Nat), Squarefree n → 1 ≤ n → (cofinal hitting) → GenMullinConjecture n`
- **Issue**: Paper omitted `Squarefree n` and `1 ≤ n` preconditions.
- **Fix**: Added "For squarefree n ≥ 1:" to the paper statement.

### 2. `sve_implies_mc` — EXTRA HYPOTHESIS (MINOR)
- **Paper** (appendix.tex:331): "SVE ⟹ MMCSB ⟹ MC"
- **Lean `sve_implies_mc`**: requires `FiniteMCBelow(Q₀)` as extra hypothesis
- **Lean `sve_implies_mmcsb`**: SVE → MMCSB (the `\lean{}{}` reference points here)
- **Assessment**: The paper's `\lean` reference points to `sve_implies_mmcsb` (correct), and the MMCSB→MC step's finite verification caveat is explained in the_character_sum_reduction.tex:604-611. Not a critical misalignment — the composition is correct, the caveat is documented elsewhere.

## Verified Consistent (18 declarations)

| Label | Lean Name | Verdict |
|-------|-----------|---------|
| `def:mc` | `Mullin.MullinConjecture` | ✓ Match |
| `thm:walk-div-bridge` | `MullinGroup.walkZ_eq_neg_one_iff` | ✓ Match |
| `thm:full-chain-dsl` | `full_chain_dsl` | ✓ Match |
| `thm:single-hit` | `single_hit_implies_mc` | ✓ Match |
| `thm:dh-mc` | `dynamical_hitting_implies_mullin` | ✓ Match |
| `thm:ccsb-mc` | `complex_csb_mc'` | ✓ Match |
| `thm:cme-ccsb` | `cme_implies_ccsb` | ✓ Match |
| `thm:cme-mc` | `cme_implies_mc` | ✓ Match |
| `thm:hod-ccsb` | `hod_implies_ccsb` | ✓ Match |
| `thm:pre` | `prime_residue_escape` | ✓ Match |
| `thm:prod-sqfree` | `prod_squarefree` | ✓ Match |
| `thm:cancel-weyl-mc` | `cancel_weyl_implies_mc` | ✓ Match (q=2 handled separately in proof) |
| `thm:sd-cancel` | `sd_implies_cancellation` | ✓ Match |
| `thm:pe-dsl-mc` | `pe_dsl_implies_mc` | ✓ Match |
| `thm:pe-dslh-mc` | `pe_dsl_hitting_implies_mc` | ✓ Match |
| `thm:dsl-closes-all` | `dsl_closes_all` | ✓ Match |
| `thm:excess-energy` | `excessEnergy_eq_visit_deviation` | ✓ Match |
| `thm:twd-mc` | `twd_implies_mc_from_bridge` | ✓ Match |
