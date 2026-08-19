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

## Verification — non-negotiable, run BEFORE you report success

1. `bash tools/check_paper_builds.sh` — **builds both papers and fails on any LaTeX error.**
   A paper edit is not done until this passes. It also reports undefined references/citations.
   *Why this rule exists:* Session 313 wrote an undefined macro (`\genProd`) into
   `tools/dead_ends.tsv`; `gen_dead_ends.py` propagated it into `paper/dead_ends_table.tex`, and
   `paper/main.tex` stopped compiling for an entire session because the loop only ran
   `check_lean_refs.py`, which checks references and not compilation.
2. `python3 tools/check_lean_refs.py` — every `\lean{}` target must resolve (expect `0 broken`).
3. If you edited `tools/dead_ends.tsv` or `tools/codebase_table.tsv`, regenerate
   (`gen_dead_ends.py` / `gen_codebase_table.py`) and rebuild — never hand-edit the generated
   `.tex`. Generated files carry a `%% GENERATED by` header.
4. Never invent a `\lean{}` target. Every cited name must exist in the Lean source; check with
   grep before citing.

Counts (dead ends, codebase lines) come from the generated macros `\DEnumbers`, `\DEentries`,
`\DEwitnessed`, `\DErevivable` — never hard-code a number that a macro already provides.

## Accuracy rules (Session 315 — from the first adversarial audit of a `\keymark` section)

The repository is **public** and tagged releases carry both PDFs. A paper defect is a visible
defect. The Session-315 audit of `sec:seed-average` — written in Session 312, released in `v0.1.0`,
and never audited until three sessions later — found **two false sentences** and a *systematic*
pattern of hypothesis-dropping. These rules exist because of what it found.

1. **A docstring is not evidence.** Before writing or citing any `\lean{}` target, open the file
   and read the `theorem` line, binders and hypotheses included. The audit found wrong claims that
   had been copied *from* Lean docstrings — and then had to fix the docstrings too.
2. **Never drop an analytic hypothesis from an informal display.** `q ≤ Y`, nondegeneracy, `q ∤ m`,
   fixed `q`, finite horizon, the policy window `n²/2 ≤ log Y ≤ n²` — these are not clutter. In
   this project the hypotheses are frequently *the reason a layer cannot reach the orbit* (the
   `log Y ≤ n²` policy is dead end #173 precisely because the true orbit does not satisfy it), so
   eliding them erases the paper's own argument. If a constant like `κ`, `K₀`, `n₁` is
   existentially quantified in Lean, attribute any explicit value to the proof's witness, not to
   the theorem.
3. **Do not let a number silently improve a theorem.** A table asserted a charge budget
   `Ch_n ≤ 2.8n` where `chargeBudget_le` proves `π(N) + N log 4` — true asymptotically at `N = 2n`,
   not what the theorem says. State the proved bound.
4. **Density is finitely SUB-additive, not additive.** This error reached four places including two
   Lean docstrings. Relatedly, `measure_iUnion_null` is countable *sub*additivity applied to null
   sets — which is exactly why the profinite argument needs no measurability of the missing event.
5. **Priority and novelty language: retract by default.** Three claims have now been audited across
   three sessions — Mertens (S312), van der Corput (S314), and the S315 sweep (five more) — and
   **every one failed or had to be scoped**. Never write "first / only / not previously formalized"
   without checking the AFP, PrimeNumberTheoremAnd, Carleson, Metamath `set.mm`, HOL Light `100/`
   **and open mathlib4 PRs**. Prefer the checkable form: "not in Mathlib as of v4.33.0", pinned.
6. **Population scope is not negotiable.** Every statement in the seed-average arc — profinite
   packaging included — is a **population** statement. No sentence may be readable, even
   uncharitably, as a claim about the orbit of `2`, about MC, about almost all *integer* seeds, or
   about a simultaneous **natural-density** result. When the profinite headline appears, `ℕ ⊂ Ω`
   being μ-null (`measure_range_iota_eq_zero`) must appear with equal prominence, as must
   "mathematically new content: none".
7. **Simultaneity in `q` is an additivity question, not a rate question.** Open for natural density;
   proved for the profinite model; these are different statements and the prose must say why.
8. **Check the roadmap paragraphs.** The §6 roadmap had been omitting two subsections, including the
   `\keymark` one, for several sessions. When you add a section, grep for the roadmap that lists it.

When a section carries `\keymark`, assume it will be read hostilely and audited eventually; write it
so the audit is boring.
