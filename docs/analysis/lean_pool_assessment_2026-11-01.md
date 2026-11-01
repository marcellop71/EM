# Contributing EM to Lean Pool: assessment (2026-11-01)

Lean Pool: <https://github.com/LeanPool/lean-pool> (Apache-2.0; paper arXiv 2609.25199;
docs <https://leanpool.github.io/lean-pool/>; Zulip channel "Lean Pool"). A curated,
`sorry`-free archive of Lean formalizations outside Mathlib's scope: 317 projects, ~11.9M
lines, pinned to the latest Mathlib and maintained by the pool (it bumps projects for you).
Review is deterministic linters plus LLM review; AI-written work is accepted by design
(provenance on cards: 191 `AI`, 54 `mix`, 72 `human`). Read from a clone of `main` on
2026-11-01; the pool's rules may since have changed.

**Verdict:** worth doing, as a *curated subset* with a few unconditional headline
theorems, not the whole repository. Submitted as is, EM fails several CI gates and would
almost certainly be blocked by the faithfulness review.

## How to contribute

Two paths (`CONTRIBUTING.md`):

1. **Propose a repo:** open an issue with the GitHub URL; a maintainer imports it.
2. **Content PR:** add `LeanPool/<Project>/`, a card `LeanPool/projects/<slug>.yaml`
   (`slug`, `title`, `summary`, `branch`, `entry_module`, `authors`, `source` with
   arXiv/DOI/URL, `status: verified`, `provenance: human|AI|mix`, `main_declarations`,
   `main_results` with `informal` statements, `tags`, `msc`), run `lake exe mk_all --module`,
   commit `LeanPool/<Project>/Imports.lean`. Content PRs may touch only content files; checks
   and gates may never be modified or waived.

Then CI, then five independent LLM reviews (faithfulness, novelty, significance, sources,
code quality; rubrics in `.github/review-rubrics/`). Any blocking verdict blocks the PR.

## EM against the gates

| gate | EM today |
|---|---|
| license Apache-2.0 / MIT | ✅ Apache-2.0 |
| no `sorry`, axioms ⊆ {`propext`, `Classical.choice`, `Quot.sound`} | ✅ `tools/check_axioms.py` already enforces it |
| no `#eval`/`#print`/…, no `axiom`/`opaque`/`unsafe`/`partial` | ✅ none (grep hits are prose in comments) |
| **no `set_option` of any kind** (incl. `maxHeartbeats`, `linter.*`) | ❌ 28 uses outside `Archive/`: 14 `maxHeartbeats` (proof rework), 14 linter |
| **module system** (`module` header, `public import`) | ❌ 1 of 257 files; mechanical port, but every file |
| exact four-line file header | ❌ absent (mechanical) |
| no broad `import Mathlib` | ❌ 1 file |
| file ≤ 10,000 code lines | ✅ largest is ~1,760 |
| proof body ≤ 200 lines | ❓ not measured |
| toolchain | ⚠ pool on `v4.35.0-rc3`, EM on `v4.35.0`; match the pool's pin when submitting |
| no non-Mathlib/TauCeti deps | ⚠ `EM/Meta` (CA, LeanArchitect) and `EM/Archive` must stay out |

Size: EM is ~119k lines in 257 files; the pool's median project is ~2,800 lines.

## Where the review would bite

* **Faithfulness** (where every past pool defect was caught). The rubric targets
  *unexercised predicates* (a `Prop` def with no consuming theorem and no witness),
  *vacuity*, and *bundled hypotheses* not disclosed on the card. EM has 150 marked
  placeholder `Prop := True` defs, dozens of open-hypothesis `Prop`s (CME,
  `WalkEquidistribution`, `AdelicEquidist`, …) and many implications among them. Whole repo:
  near-certain block. Curated subset: fine if every conditional result's hypotheses are in
  the card summary (the pool accepted a conditional case of Erdős 132 on those terms).
* **Significance.** Wants "completed, self-contained" projects with named, graduate/research-
  level results; named open problems are explicitly welcome, "honestly bounded". An ongoing
  research programme with a dead-end catalogue does not read as completed.
* **Novelty.** Compared against Mathlib, Tau Ceti and the pool. `EM/IK` (Iwaniec–Kowalski
  chapters) and the large-sieve infrastructure may overlap; leave them out unless a headline
  needs them.

## Pros and cons

For: visibility with the AI-for-mathematics audience (the pool is a corpus, a search index
and a docs site); Mathlib bumps done by the pool; citable archive (Zenodo DOI); the
independent faithfulness review is itself a useful external audit.

Against: the pooled copy is a fork, while EM keeps moving; refactors go back through the
pool's process. The style port (no `set_option`, module system, headers) is a one-off cost.
Submitting conditional chains would invite exactly the overclaiming findings this project
has worked to avoid (`cme_iff_mc`: never call CME weaker).

## Recommended submission

A self-contained "Euclid–Mullin" project, target 10–20k lines, `provenance: mix` (or `AI`),
with unconditional headlines:

* `almost_all_genmc_density`: for each fixed prime `q`, almost every seed (natural density)
  captures `q`;
* `not_ffMullinConjecture_five`: the function-field Mullin conjecture is false over 𝔽₅[t];
* `cme_iff_mc`: conditional multiplier equidistribution is equivalent to MC;
* `no_cvdp_obstruction`: no congruence obstruction witnesses a missed prime (contrast the
  largest-factor sequence);
* optionally the composite floor / growth-constant results
  (`infinitelyManyComposite_iff_growthConstant_eq_zero`).

Conditional results stay out, or are listed with their hypotheses spelled out in `summary`.
`MullinConjecture` itself appears only as a statement. `source`: the arXiv paper, once the
almost-all GenMC write-up is out (strongest option); the GitHub URL until then.

## Next steps

1. Measure the import closure of the headline set: files, lines, `set_option`s and
   placeholders inside it. This decides whether the subset is 10k or 60k lines.
2. Prune the closure: drop placeholders and unused open-hypothesis defs; remove
   `maxHeartbeats` by splitting slow proofs.
3. Port to the module system and file headers in a branch; build against the pool's pinned
   Mathlib.
4. Write the card, then open the PR (or an issue first, to ask the maintainers about
   fit on Zulip).
