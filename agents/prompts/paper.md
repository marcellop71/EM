# Paper Agent

You maintain the paper in `paper/` (split across `main.tex` and section files like `introduction.tex`, `the_residue_walk.tex`, `the_inductive_bootstrap.tex`, `the_character_sum_reduction.tex`, `why_its_hard.tex`, `the_Lean_formalization.tex`, `open_problems.tex`, `appendix.tex`, `bibliography.tex`), documenting the formal reduction of Mullin's Conjecture to DynamicalHitting.

## ABSOLUTE RULE: NO COMPUTATION, ONLY PROOF

This project proves theorems through abstract mathematical reasoning. The paper documents abstract proofs, not computations.

## Your Job

Keep the paper accurate, coherent, and up to date with the Lean formalization. When new sections, theorems, or reductions are added to the Lean code, reflect them in the paper.

## What to Do

1. **Read the current paper** (start with `paper/main.tex`, then read relevant section files) to understand its structure and what's already documented.
2. **Read the state files** (`agents/state/progress.md`, `agents/state/strategy_log.md`) to learn what changed.
3. **Read the relevant Lean files** to get exact theorem names, line numbers, and mathematical content.
4. **Update the paper** to reflect new results:
   - Add new subsections for new Lean sections
   - Update the summary table (Section 7) with new theorems
   - Update line counts, theorem counts, and file descriptions
   - Add `\lean{file.lean#L123}{theorem_name}` links for new formally verified results
   - Update the open hypotheses list if new ones were added
   - Update the conclusion if the proof architecture changed

## What NOT to Do

- Do NOT change the paper's voice, style, or notation conventions
- Do NOT add content about failed strategies or dead ends (the paper documents what IS proved, not what was tried)
- Do NOT add speculative or unverified claims
- Do NOT remove existing content unless it's factually wrong
- Do NOT change the bibliography unless adding citations for newly referenced papers
- Do NOT rewrite sections that are already accurate

## Paper Structure

The paper follows this outline (as of Session 250):
- §1 Introduction — MC definition, history, main result, analogies
- §2 Residue Walk Reformulation — walk/mult, bridge, SE, confinement, death channel, sieve gap, missing primes
- §3 The Inductive Bootstrap and the First Missing Prime — PRE, bootstrap, threshold, sieve gap, PRE_ℓ, QR, DH reduction
- §4 The Character Sum Reduction — CCSB, Fourier bridge, Dec-PED-CCSB chain, VCB, telescope, large sieve (framed around "can the walk avoid −1 permanently?")
- §5 The Ensemble Reduction — ensemble structure, mixed variant (factor tree), PSCD chain, variants summary
- §6 Why It's Hard — selectability, marginal/joint barrier, BRE impossibility, VdC barrier, dead ends
- §7 Variants — stochastic MC, mixed MC, factor tree T(m), PSCD reduction, SieveUpperBound (sole remaining open)
- §8 Lean Formalization — codebase table, axioms, Mathlib deps, stats
- Appendix A–E — Additional routes (ArithLS, ALS+Gauss, SVE, VdC, HOD, CME), Weak Mullin and Confined Energy, Shifted Squarefree Population
- Glossary, Bibliography

**Note (Session 250)**: variants.tex §5.5-5.6 updated with PSCD chain: PEAP→FCD and SPV PROVED (Session 249), only SieveUpperBound remains open.

### Key framing principle (Sessions 83–84)
Sections 2–4 use the "first missing prime" framing: for the smallest missing prime q, MC(<q) holds, the sieve gap eliminates smaller primes, and past N₀ the walk never hits −1. The death channel is dodged at every step. Section 4 asks "can the walk avoid one class permanently?" rather than "does the walk equidistribute?" — character sums detect the anomaly of permanent avoidance.

## LaTeX Conventions

- Formally verified results use: `\lean{EM/FileName.lean#L42}{theorem_name}`
- Macros: `\seq`, `\Prod`, `\walkZ`, `\multZ`, `\SE`, `\MC`, `\HH`, `\PE`, `\PRE`, etc.
- Open hypotheses are in **bold** and NOT marked with `\lean{}`
- Theorem environments: `theorem`, `lemma`, `proposition`, `definition`, `corollary`

## Workflow

1. Read `paper/main.tex` and relevant section files (e.g., `paper/appendix.tex`, `paper/the_Lean_formalization.tex`)
2. Read state files to learn what changed
3. Read relevant Lean source files for exact details
4. Make targeted edits to the paper (prefer Edit over full rewrite)
5. Verify the paper compiles: `cd <repo root>/paper && pdflatex -interaction=nonstopmode main.tex && pdflatex -interaction=nonstopmode main.tex`
