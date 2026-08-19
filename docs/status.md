> **2026-08-17:** the population layer PE / MFRE / DSL is retired (Dead End #160, false by head domination); the headline is now CME ⇒ CCSB ⇒ MC.  Full record: [`docs/pe_dsl_retirement.md`](pe_dsl_retirement.md).

> **2026-08-19 (Session 314): the profinite ensemble — μ-almost every profinite seed
> captures EVERY prime** (`ProfiniteHeadline.measure_some_prime_missed_eq_zero`:
> `μ {x : Ω | ∃ q : Nat.Primes, x q ≠ 0 ∧ ¬ ∃ j, profSeq x j = q} = 0`). Session 312 recorded
> (dead ends #167/#168) that the per-`q` seed-average law does **not** combine over all
> primes, because natural density is only finitely additive; that the obstruction is **not** a
> rate problem (summable per-`q` failure fractions are achievable); and that the repair is a
> **countably additive ambient measure**. Session 314 builds that measure and performs the
> union. Three new files, 938 lines, 0 sorry, full build green (8,938 jobs), axioms
> `propext, Classical.choice, Quot.sound`:
> `EM/Population/ProfiniteEnsemble.lean` (271 — the ambient space
> `Ω = Π (r : Nat.Primes), ZMod r` with `μ = MeasureTheory.Measure.infinitePi` of the uniform
> measures, `IsProbabilityMeasure`; the key lemmas are all **equalities**: `measure_cylinder`
> and **`measure_residue_classes`**: `μ {x | redMod P x ∈ T} = #T / ∏_{r ∈ P} r`, i.e. the
> measure of an `M`-periodic event *is* its period fraction; `redMod_iota`; and
> `measure_singleton_eq_zero`, **`measure_range_iota_eq_zero`** — `ℕ ⊂ Ω` is μ-null, proved.
> `Π ZMod r` and not `Ẑ = Π ℤ_p` because the programme only ever conditions on `m mod M` with
> `M` squarefree — `SelectionLaw.modulus q Y` is a product of distinct band primes — so
> `ZMod r` suffices per coordinate);
> `EM/Population/ProfiniteDynamics.lean` (277 — the greedy dynamics defined directly on a
> profinite point: a profinite point has no `minFac`, so the multiplier is `leastVanishing`,
> the least prime whose coordinate of the current Euclid element vanishes. The **agreement
> theorem**, proved unconditionally (only `1 ≤ m`): `profSeq (iota m) k = genSeq m k` and
> `profProd (iota m) k = iota (genProd m k)` — the profinite dynamics *is* the integer
> dynamics on the image of `ℕ`; plus band-local agreement `profProd_agree_of_agree`,
> `genSeq_eq_profSeq_of_agree`);
> `EM/Population/ProfiniteHeadline.lean` (390 — the headline, via
> `covering_strong → covering → measure_missing_le → measure_missing_eq_zero`, then countable
> additivity `measure_iUnion_null` over the primes).
> Also: the **Coupling Lemma** in `EM/Population/SeedCapture.lean`
> (`genSeqAvoid_eq_genSeq_of_missed`, `genProdAvoid_eq_genProd_of_missed`,
> `minFac_qfreePart_eq_minFac`); and `q ≤ Y` plus the band structure of the modulus exported
> through `AlmostAllGenMC.three_type_union_small`, `TypeBadSmall.type_bad_small`,
> `AlmostAllDensity.uncaptured_in_few_classes`, with new `SelectionLaw` lemmas
> `modulus_squarefree`, `coprime_modulus_self`, `prime_dvd_modulus`.
> **No `q`-uniform rate is used** anywhere: for each fixed `q` the horizon is sent to infinity
> separately. Simultaneity in `q` is an *additivity* question, not a *rate* question.
>
> **SCOPE — as prominent as the result itself.**
> * `ℕ ⊂ Ω` is **μ-null**. "μ-a.e. seed" is **not** "almost all integer seeds"; a μ-null set
>   can have upper density `1` in `ℕ`. This is a statement about a **random model**, and no
>   transfer to the integers is claimed or available.
> * It says **nothing** about the Euclid–Mullin orbit of the seed `2`. The orbit-specificity
>   dead ends **#90** and **#117** are **untouched**. Mullin's Conjecture is **not**
>   approached.
> * **Mathematically new content: none.** The already-proved finite counting chain
>   (`theorem_C → theorem_C_fiber → type_bad_small → uncaptured_in_few_classes`) is the
>   mathematics; the passage to all `q` is measure-theoretic packaging. That is a feature —
>   there is no analytic risk in packaging — and it must be **said, not hidden**.
> * Not to be conflated with dead end **#101** (`Ẑ` as a home for the *walk*) or **#155**
>   (the Loeb-measure receptacle). Here `Ω` is the sample space of a population statement: it
>   carries no walk and no orbit claim.
> * **Unconditional** — no equidistribution hypothesis anywhere in the chain.
>
> **Correction (audited this session):** the repo does **not** hold "the first van der Corput
> bound in any proof assistant"; that claim is **retracted**. The accurate description is
> "discrete (Weyl–van der Corput) inequality, `EM/ForMathlib/VanDerCorput.lean`, not in
> Mathlib as of `v4.33.0`". Record: `agents/state/findings_vdc_priorart.md`.

> **2026-08-18/19 (Session 309):** the seed-average program's (LS) frontier is now a
> **verified theorem with its deterministic core fully in Lean**. New files
> `EM/Population/SeedCapture.lean` (q-free dynamics, Lemma C coupling+capture, capture
> identity `captured_iff_mem_visited`, 548 lines) and
> `EM/Population/LargeStepRoughness.lean` (box process, harmonic charge budget
> `charge_sum_le_harmonic`, brink lemma, `mertens_upper` — first Mertens-type bound in the
> repo — B4/B5 far-band estimates, and the headline **`pathwise_compensator`**:
> `Σ_{k<n} S_k ≥ (c₁/2)·n` pathwise with absolute `c₁ = exp(−250)`, 1758 lines).
> Both 0 sorry; full build green. WP4 (Mertens-in-AP O(1)) deleted — the asymptotic
> Karamata form suffices (verified). Remaining for a.a. GenMC(q) per fixed q: tree-Chernoff
> consumption (needs the type-measure/selection-law layer), tail estimate, Lemma D,
> Theorem C. Adversarial verification record: `agents/state/findings_ls_verification.md`.

> **2026-08-19 (Session 310, commit f391732):** WP2 and Group 6 are CLOSED; **(LS+) is
> proved in Lean** (`LSPlus.ls_plus`). Four new files, ~2,750 lines, 0 sorry:
> `EM/Population/SelectionLaw.lean` (905 — type cells mod `M_Y/q`, dependent-family CRT
> counting `card_filter_crt`, **exact** `selection_law : #(cell ∩ Survives) = survival·#cell`);
> `EM/Population/TreeChernoff.lean` (616 — abstract finite-tree exponential supermartingale
> + Chernoff lower tail, C5 replacement, localized variants making C6 trivial, Mathlib-only);
> `EM/Population/MertensLower.lean` (755 — **`mertens_lower`**: `log n − 13 ≤ Σ_{p≤n} log p/p`,
> first lower Mertens in the repo, not in Mathlib; **`window_recip_lower`**:
> `log log Y − log log z − 16 ≤ Σ_{z<r≤Y} 1/r`); `EM/Population/LSPlus.lean` (469 — `ls_plus`:
> over one period, `#{m : < (c₁/8)n big steps} ≤ M_Y·e^{−(3/16)c₁n} + tail-term`).
> Remaining for a.a. GenMC(q) per fixed q: Group 7 tail assembly (unblocked by
> `window_recip_lower`), the D5c policy lemma (convenience), Lemma D, Theorem C.
> Population scope only; no orbit claim; #90/#117 untouched.

> **2026-08-19 (Session 312): the seed-average theorem in NATURAL-DENSITY form**
> (`AlmostAllDensity.almost_all_genmc_density`). For every prime `q` and every `ε > 0` there
> is a horizon `n` such that the seeds `m` coprime to `q` whose greedy Euclid–Mullin orbit
> misses `q` among its first `n` multipliers have **upper natural density ≤ ε** — genuine
> "almost all seeds", not a period fraction. Also `almost_all_genmc_limsup` and
> `finite_simultaneous_density` (uniform over any *finite* set of primes).
>
> The conversion was not bookkeeping. `TheoremC.GoodSeed` carries two clauses (`¬ q ∣ m`,
> `¬ ∃ j < n, genSeq m j = q`) that are **not** functions of `m mod M_Y`, because `M_Y`
> excludes `q`; by the capture identity, capture is a condition on the *fibre* coordinate
> `m mod q`. Over one period each class occurs once, so a period fraction is a **diagonal**
> count, while natural density needs the **product** count — and no inequality relates them.
> The repair: `guard_of_exposed` already forces the visited set full, and
> `captured_of_mem_visited` was already stated for a general fibre seed, so the two clauses
> weaken to "*some* seed in the residue fibre of `m` is coprime to `q` and uncaptured"
> (`FiberTheoremC.FiberGood`) with every constant unchanged, restoring `M_Y`-periodicity.
> New files: `EM/Population/FiberTheoremC.lean` (335, `theorem_C_fiber`),
> `EM/ForMathlib/PeriodicDensity.lean` (174, generic block counting),
> `EM/Population/TypeBadSmall.lean` (313, `type_bad_small`),
> `EM/Population/AlmostAllDensity.lean` (248, the headlines). 0 sorry, build green.
>
> **2026-08-19 (Session 313):** scoping only, **no new Lean mathematics**. The seed-average
> programme's one *orbit-valid* ingredient — the sure, per-path harmonic charge budget
> `LargeStepRoughness.charge_sum_le_harmonic` — was assessed against the question "can it
> constrain the primes **missed** by a *single* orbit?". Verdict **DEAD — budget vacuous**,
> reached independently by two attack agents run blind to each other and by the coordinator.
> The budget is an *identity*: the box starts at `r−1`, a charge decrements it by exactly one
> and a non-charge leaves it unchanged, so `Σ 1/|box| = H_{r−1} − H_{r−1−C}` and the theorem
> is *equivalent* to `C ≤ r−2`, which counting units mod `r` forces anyway. The surviving
> branch, "the box stays large", is `¬DynamicalHitting(r)` by definition (mirror of #166);
> and every sure theorem is proved about `genSeqAvoid q m`, which
> `SeedCapture.genSeqAvoid_ne_avoided` shows **never selects `q`** — so the whole layer is
> satisfied by a dynamics missing `q` by construction. Dead ends **#169–#174** (counts
> 168/158/31/15 → **174/164/32/15**; #171 witnessed). New principle recorded: the **sign
> asymmetry of `minFac`** — it yields infinitely many non-divisibility facts and exactly one
> divisibility fact, so the sure layer can only ever bound hit counts from *above*.
> Full record: [`docs/analysis/sure_layer_missed_primes.md`](analysis/sure_layer_missed_primes.md).

> Also: dead ends **#161–#168** (six seed-average near misses; log density for the
> simultaneous-in-`q` form; summable per-`q` rates). **§G frontier reframed**: simultaneity
> is an *additivity* problem, not a *rate* problem — natural and logarithmic density are both
> only finitely additive, so Borel–Cantelli does not apply; the profinite ensemble
> `(Ẑ, Haar)` would deliver it with no new analysis, at the cost of a scope change
> (`ℕ ⊂ Ẑ` is Haar-null). See `docs/analysis/simultaneous_in_q_scoping.md`.
>
> **Correction:** the repo does **not** hold priority for its Mertens bounds. Explicit
> two-sided Mertens I is in the Isabelle/HOL AFP since 2018 and in the Lean project
> `PrimeNumberTheoremAnd`; mathlib4#41394 is open. Only "not in Mathlib `v4.33.0`" is true.
> See `agents/state/findings_mertens_priorart.md`.
>
> Scope, unchanged: population theorem over the seed ensemble, per **fixed** `q`; the
> simultaneous-in-`q` form is OPEN; nothing is claimed about the orbit of `2`; #90/#117
> untouched.

> **2026-08-19 (Session 311): a.a. GenMC(q) IS PROVED IN LEAN**
> (`AlmostAllGenMC.almost_all_genmc`). The seed-average program (Sessions 308–311) is
> complete. Five new files, ~3,540 lines, 0 sorry, build green (8,931 jobs):
> `EM/Population/TailAssembly.lean` (558 — `tail_small` ≤ e²⁵·log n/n at policy
> `n²/2 ≤ log Y ≤ n³`; `policy_satisfiable`; `ls_plus_with_tail`);
> `EM/Population/LemmaD.lean` (278 — **`window_ap_recip_lower`**: primes ≡ a mod q in
> `(y,y²]` carry 1/p-mass ≥ 1/(8φ(q)), Karamata-only, A = 2; `window_recip_upper` ≤ 32);
> `EM/Population/LemmaDBox.lean` (815 — **`lemma_D_z`**: cell-form conditional multiplier
> bound κ·#(cell ∩ bigStep) ≤ #(cell ∩ bigStep ∩ {mult ≡ a}), κ = e⁻¹²⁸/(16φ(q)), via the
> exact hit-count identity `hitCell_card_mul`);
> `EM/Population/TheoremC.lean` (719 — **`theorem_C`**: #{uncaptured good seeds} ≤
> M·e^{−(3/8)κ((c₁/2)n−K₀)}, one application of `chernoff_quarter_local`, deterministic
> success cap ≤ 2q, no new probabilistic engine);
> `EM/Population/AlmostAllGenMC.lean` (452 — **`almost_all_genmc`**: ∀ q prime ∀ ε > 0
> ∃ n Y, #{m : q∤m ∧ q ∉ first n multipliers}/M_Y ≤ ε; D5c discharge `threshold_sq_le`).
> **Scope:** population theorem over the seed ensemble, per fixed q (simultaneous-in-q
> OPEN, §G); finite-horizon counting, no equidistribution hypothesis; nothing claimed
> about the orbit of 2 — #90/#117 untouched.

# EM Formalization — Status

> Maintained by the coordinator agent. Update **only when Lean code
> actually changed** (theorems compiled, not merely analyzed).
> Machine-readable ground truth: `registry/declarations.json` /
> `registry/meta.json`, regenerated by `lake build`.
>
> **Note:** `docs/` is excluded by `.gitignore`, so this file is local
> only — it is not published with the repository. The tracked, shareable
> summaries are `registry/*.json` and `paper/`.

## Snapshot (2026-08-19)

- **227 Lean files under `EM/`, 111,179 lines** — 208 files / 106,839 lines
  outside `EM/Archive/` (which holds stubs and is not imported by
  `EM.lean`).
- **Zero `sorry` in the built library.** `EM.lean` imports 206 modules;
  the only non-Archive files outside that list are `EM/Meta/Registry.lean`
  and `EM/Meta/Blueprint.lean`, which belong to the separate `EMRegistry`
  `lean_lib` and are imported by `EMRegistry.lean`.
- Registry (`registry/meta.json`): **358 declarations — 269 proved,
  68 conditional, 21 open points**, 337 published. Open points include the
  targets `MullinConjecture` and `HittingHypothesis` themselves.
- Headline machine-verified chain: **CME ⇒ CCSB ⇒ MC**
  (`cme_implies_mc`, `EM/CME/Reduction.lean`). CME is
  *equivalent* to MC (`EM/CME/Equivalences.lean`), so it is never to be
  described as a weaker hypothesis. The DSL rung (PE → CME) is retired —
  PE is false, Dead End #160.
- Sources are organized in subject subdirectories under `EM/`:
  Adelic, Archive, CME, Core, Ensemble, Equidist, ForMathlib,
  FunctionField, GaussEM, Group, IK, LargeSieve, Meta, Obstruction,
  Population, Reciprocity, Reduction, SDDS, Stochastic, Transfer. Grep for
  theorem names rather than trusting old flat filenames.
- Dead ends (`tools/dead_ends.tsv` is the single source of truth;
  `EM/Meta/DeadEnds.lean` carries the generated block; `docs/dead_ends.md`
  is a pointer stub): **174 numbers documented, 164 entries, 32 with formal
  Lean witnesses, 15 with weak-MC revival score ≥ 2** — read
  `deadEndCount`, `deadEndEntryCount`, `witnessedDeadEndCount`,
  `revivableDeadEndCount` from the Lean file rather than trusting these
  figures. Session 307 added #156–#159 (Run T-MC-Proper), corrected every
  stale `File` entry to the post-reorg layout, and added an **MC-proper
  ledger** section mapping each route to MC itself against the entries that
  constrain it; Session 312 added #161–#166 (seed-average near misses) and
  #167–#168 (the two refuted routes to the simultaneous-in-`q` form:
  logarithmic density, and summable per-`q` rates — the two that Session
  314's ambient measure replaces); Session 313 added #169–#174, closing the
  *orbit* direction for the sure (per-path) layer.
- Paper: `paper/main.tex` + section files, compiled with **lualatex**.

## Recent changes

_(coordinator: append dated entries here when the Lean code changes)_

### 2026-08-19 (Session 310) — WP2 + Group 6 closed; (LS+) proved

Commit f391732; four new files, ~2,750 lines, 0 sorry, build 8,925 jobs, axiom gate clean.
`SelectionLaw.lean`: WP2 (type cells, CRT counting, exact selection law).
`TreeChernoff.lean`: abstract finite Chernoff (C5 replacement; localized variants = C6 for
free; candidate ForMathlib promotion). `MertensLower.lean`: lower Mertens I (const 13) +
windowed log log lower bound (const 16) — Group 7's analytic gap closed.
`LSPlus.lean`: `ls_plus`, the honest (LS+) with rate `exp(−(3/16)c₁n)` + tail term.
Next: Group 7 tail assembly, D5c policy lemma, Lemma D, Theorem C.

### 2026-08-18 (c) — reader-review remediation, phases (1)–(4)

See `docs/review_2026-08-18.md` §E for the full log.  Highlights: **CME/CCSB/DH/SHH/HH/WFG are
equivalent to MC** (`EM/CME/Equivalences.lean`, published) and the paper now says so; **zero
`native_decide`** (axiom gate `tools/check_axioms.py`); **BV/EH/ALS restated faithfully** (`psiAP`,
`bvError`; primitive characters); three open points retired (21 left); CA is a git require at tag
v4.33.0 (tag created locally in `../CA`, commit 3465cc4 — push it); registry tooling in its own
`lean_lib EMRegistry`; `autoImplicit false`; `EM/ForMathlib/` (van der Corput, `ZMod.dft` Parseval,
affine coprime block) Mathlib-only; 19 landscape theorems unpublished (337 published); duplicate
Mathlib instances removed; `#check` → `example`.  Paper: factual fixes and de-over-claiming
throughout; **short paper `paper/short/main.tex` (10 pp)** + long document retitled as technical
report.  `lake build` clean (4177 jobs), `check_axioms` 358/0, `check_lean_refs` 810/0.

### 2026-08-18 (b) — the dead-ends catalogue, complete, with a rationale for every entry

* **Archive incident.** After the previous commit only `EM/Archive/Equidist/SieveTransferArchive.lean`
  remained on disk (the other 19 archive files had been deleted from the working tree, presumably
  by the git client on committing the `git rm --cached`).  Restored all 19 from commit `905e6a5`
  with `git show` (untracked, still gitignored).  Nothing else affected.
* **Reconstruction.** The registry tables covered ~70 of the 160 numbers; the rest lived only in
  `agents/state/strategy_log_old.md` and the prompts.  Four extraction passes over the logs
  reconstructed every number with approach, rationale, session, witness and status; ten numbers
  (#25, #64–#72) were never assigned in any log; several aliases/collisions recorded (S180 "#136" =
  #135; S234 "#137" = #140; old "#138" = #137; "#135" also used for product≠tree in S212; catalog
  cites of "#21", "#48", "#57" that mean #45, #52, #8; #115 = ACI (S109) re-described as the
  cofactor barrier; #130's meaning drifted).
* **Single source of truth: `tools/dead_ends.tsv`** (num, cat, name, approach, rationale, session,
  witness, revival, status).  `tools/gen_dead_ends.py` emits `paper/dead_ends_table.tex` (complete
  catalogue, longtable grouped by failure mode with a gloss per mode), `paper/dead_ends_stats.tex`
  (`\DEnumbers` 160, `\DEentries` 150, `\DEwitnessed` 29, `\DErevivable` 10, `\DEunassigned` 10),
  `docs/dead_ends_catalog.md`, and the block between `<!-- BEGIN/END GENERATED CATALOGUE -->` in
  `EM/Meta/DeadEnds.lean`.  New category **MR** (methodological rule) for #1–#3.
* **Registry.** `deadEndCount 160`, new `deadEndEntryCount 150`, `witnessedDeadEndCount 29` (24 +
  #26, #58, #93, #96, #110, #119, #120 found genuine in the reconstruction + #144 now witnessed by
  `Reciprocity.no_reciprocity_induction_proof`, S307), `revivableDeadEndCount 10`;
  `dead_end_registry` updated; `#check` for #144 added.
* **Paper.** Appendix "Dead Ends Catalogue" now carries the complete table (≈14 pages) with the
  nine failure modes glossed; counts via the `\DE…` macros in `why_its_hard.tex`, abstract, intro
  ("150 documented dead ends … 29 witnessed"), Lean table row.  Paper 193 pages, 0 undefined refs;
  `check_lean_refs` 748/0.

### 2026-08-18 — the growth projection, measured: three new files

Triggered by the remark that the growth-constant projection is less explored than the walk.
Assessment: structural — `C` sees only the floor `(C∞)`, MC is invisible from it (abstract now
says so: "not on a par").  Then three theorems (all theory, no numerics):

* `EM/Population/GrowthDensity.lean` — `HasDensityZero`, `hasDensityZero_prime` (elementary,
  `Nat.primeCounting'_add_le` with primorial modulus + `HeadDomination.cfun_tendsto_zero`),
  `hasDensityZero_comp_T` (density zero pulls back under `T`), `hasDensityZero_genProd_prime N`,
  **`hasDensityZero_perpetual N`** (prime-tower seed set from threshold `N` is null),
  `sgrowth_pos_subset_iUnion`, `growth_density_landscape`.  NOT claimed: `{C>0}` null (countable
  union; density not σ-subadditive) — recorded in docstring and paper.
* `EM/Population/SizeResidueDecoupling.lean` — `multiplier_residue_of_prime_stage`
  (`minFac(P+1) ≡ P+1` when prime), **`exists_seed_composite_residue_size`** (odd prime `q`,
  unit `w ≠ −1`, unit `a`, bound `K` ⇒ squarefree seed `m ≡ w`, `m+1` composite,
  `minFac(m+1) ≡ a`, `≥ K`; Dirichlet ×2 + `Nat.chineseRemainderOfFinset`),
  `size_residue_landscape`.
* `EM/Population/RelativeSize.lean` — `ratio`, `rho` (liminf), `rho_T` (exact invariance via
  `Filter.liminf_nat_add`), `rho_dichotomy`, `sgrowth_pos_iff_rho_eq_one`,
  `sgrowth_eq_zero_iff_rho_le_half`, `rho_eq_zero_of_seedRD`, `rho_two_eq_zero_of_rd`,
  `rho_two_eq_zero_of_mc`, `rho_two_le_half_iff`, `relative_size_landscape`.
  New rung: MC ⇒ RD ⇒ ρ(2)=0 ⇒ (C∞).
* Registry +16 publishes; TSV +3 rows; paper: three paragraphs in `composite_floor.tex`
  (§growth-density, §size-residue, §relative-size), intro story sentence, four table rows,
  abstract "not on a par" edit.  `lake build` clean; `check_lean_refs` 748/0.

### 2026-08-17 (n) — archive made local-only; abstract cut; the story in the introduction

**No Lean change.**  `EM/Archive/` untracked (`git rm --cached`) and gitignored: it stays on
disk, is not part of the public repo.  Paper: new macro `\archived{path}{name}` (no link,
gray `[local archive]` badge) replaces the 19 `\lean{EM/Archive/...}` links; the 7
`\code{EM/Archive/...}` mentions are marked "(local archive)"; a paragraph "The local
archive" in §Lean explains the convention.  Abstract rewritten to ~280 words (was ~850; now
about a quarter of a page); the "Statements and proofs" note moved into the introduction.
Introduction: the narrative of `docs/the_story.md` now sits under an explicit heading "The
story, told from above" (one map / two projections / the map, with a new item "dead ends as
the coastline" and the "what the telling changes" paragraph pointing at the seeded growth
constant and the bag law); duplicated visual-conventions text removed.
`zulip_mathlib_candidates.md` re-verified and extended (§A7 Karamata + Mertens in APs, §B12
affine block count, §B13 head domination).

### 2026-08-17 (m) — pass 4 of the audit: two new theorems from the retelling

Both ideas listed at the end of `docs/the_story.md` are now formalized (theory only, no
numeric certificates), wired into `EM.lean`, the TSV, the registry, and the paper.

* **`EM/Population/SeededGrowth.lean`** — the growth constant for every seed.  `sgrowth m`
  for `m ≥ 2` (the `DefectTelescope` argument on `genProd m`); the tail identity makes `C` a
  **semiconjugacy to doubling**: `sgrowth (T m) = 2 · sgrowth m`, `sgrowth (Tᵏ m) = 2ᵏ ·
  sgrowth m` (`sgrowth_T`, `sgrowth_iterate`).  Complete invariance seed by seed:
  `sgrowth m = 0 ↔ SeedInfinitelyManyComposite m`, `0 < sgrowth m ↔ eventual perpetual
  primality`; `sgrowth 2 = growthConstant`; and **`MixedDiversity ↔ ∀ m ≥ 2, sgrowth m = 0`**
  (`mixedDiversity_iff_sgrowth_zero`, via `mixedWalkProd acc minFacMixed n = genProd acc n`).
  So MixedDiversity is "the invariant set `{C > 0}` of the factor map is empty".  Paper:
  `composite_floor.tex` §"The seeded growth constant".
* **`EM/Population/BagConditionedLaw.lean`** — the bag-conditioned multiplier law.  For a
  prime `p ∤ P`, on the progression `m ≡ 1 (mod P)`: `minFac m = p ↔ p ∣ m ∧ Coprime m N'`
  with `N' = ∏_{r<p, r prime, r∤P} r` (`minFac_eq_iff_on_ap`); the two congruences combine to a
  class mod `pP` (`mem_class_iff`, `Nat.chineseRemainder`); an **affine block count**
  (`card_coprime_affine_block`: `#{t ∈ [k, k+N) : Coprime N (a t + b)} = φ N` for `Coprime a N`,
  via periodicity + `t ↦ (a t + b) % N` bijective on `range N` in `ZMod N`) gives the exact
  density.  Results: `tendsto_apCount_div` (the progression has density `1/P`),
  `tendsto_bagClassCount_div`, **`tendsto_bagClass_div_ap`** (relative density
  `bagWeight P p = (1/p)∏_{r<p, r∤P}(1−1/r)`), **`bagWeight_least_missing`** (least prime
  outside the bag: exactly `1/q`), `tendsto_least_missing_div_ap`.  Paper:
  `the_ensemble_reduction.tex` §"The bag-conditioned multiplier law".
* Registry: 11 new `publish` entries; open points unchanged (24).  `lake build` clean,
  `check_lean_refs` 0 broken, paper rebuilt.
* `docs/the_story.md`: pass-4 section rewritten as "status" with two follow-up directions
  (the *rate* `q_n` of the least missing prime as the precise orbit question; a second
  invariant of `T` on `{C = 0}`).

### 2026-08-17 (l) — siblings bumped to v4.33.0; a long-standing lakefile claim was false

**All three repos now declare `leanprover/lean4:v4.33.0`.** EM builds clean (0 errors,
0 warnings, 4038 jobs); registry unchanged at 288 published; both siblings build clean.

| Repo | Change |
|---|---|
| `../CA` | toolchain → v4.33.0; `batteries` and `Cli` → tag `v4.33.0`. Builds clean (13 jobs) |
| `../../proofinity/declbuild-meta` | toolchain → v4.33.0; `batteries` → `v4.33.0`; stale docstring "safe to import from any Lean 4 project on `v4.29.0-rc1`" corrected. Builds clean (11 jobs) |

Both siblings were on a clean tree at their v4.31.0 tags before the bump; the changes are
**uncommitted**, so the lakefile's known-good pins now read "`<hash>` + an uncommitted
v4.33.0 bump" and must be refreshed once those commits land.

**No dependency conflict**, by construction: `batteries v4.33.0` is exactly `4488d40d…` and
`Cli v4.33.0` is exactly `6130a478…` — the same revisions Mathlib v4.33.0 already pins in
EM's manifest. Verified before editing.

**A stale claim, found and corrected.** The lakefile asserted that
`EM/Meta/Strategies.lean` "lives outside the `EM.lean` import closure" because
declbuild-meta's `.olean` cache was toolchain-incompatible. Testing that after the bump
produced a *duplicate* import — because **`import EM.Meta.Strategies` has been in `EM.lean`
all along**, including at git HEAD, and the file builds on every full build (it is what
writes `registry/desiderata.json`). The claim was false. It was repeated in the lakefile
across today's two toolchain hops and in entries (j) and (k) above, which are now corrected
in place. `EM.lean`'s own header — "the ONLY files under `EM/` deliberately excluded are
those in `EM/Archive/`" — was the accurate statement all along.

Remaining sibling-related caveat: **LeanArchitect is still pinned to `main`** (no v4.33.0
tag). That is unchanged by this entry and still wants a tag when one appears.

### 2026-08-17 (k) — TOOLCHAIN: v4.31.0 → v4.33.0

**Build clean: 0 errors, 0 warnings, `sorry`-free, 4038 jobs.** Registry unchanged at
**288 published / 38 open / 219 proved / 69 conditional**; 326 declarations, **0 added,
0 removed** (only `type_hash`/`pp_type` churn on ~40 entries). Paper 171 pages, refs 749/0.
Headline chain `full_chain_dsl` and every landscape theorem still on
`propext, Classical.choice, Quot.sound`.

**Lakefile ordering matters now.** `lake update` failed with *"your project pins different
versions of some dependencies than Mathlib … failed to fetch cache"* because another
package's `batteries`/`Cli` pins won. Fixed by moving `require mathlib` **last** in the
lakefile (lake's own advice) — a comment records why. Without this the Mathlib olean cache
cannot be fetched at all.

**Only 3 real breakages** (again a two-release jump):

| File | Cause |
|---|---|
| `IK/DirichletDensity.lean` | `rw [primeFactorsP, Finset.mem_image]` failed — membership resolved through `SetLike.instMembership`. Replaced with a direct `Finset.mem_image.mpr` |
| `Obstruction/Calculus.lean` | `Relation.ReflTransGen.lift` now returns a *relation inequality* (`ReflTransGen r ≤ (ReflTransGen p on f)`) instead of consuming the proof. Apply it to the endpoints, then `simp only [Function.onFun]` before rewriting |

**Deprecation sweep:** `Set.mem_setOf_eq`→`Set.mem_ofPred_eq` (14 files),
`Set.mem_setOf`→`Set.mem_ofPred`, `Nat.infinite_setOf_prime_and_eq_mod`→
`Nat.infinite_setOfPred_prime_and_eq_mod`.

**New style linter `linter.style.haveILetI`** (4.33) fired 183 times: `haveI`/`letI` where
the goal is a Prop. Rewrote all 183 sites across **67 files** (169 `haveI`→`have`,
14 `letI`→`let`), driven off the compiler's own file:line:col so only flagged sites were
touched. Build stays 0-warning.

**Two regressions to be aware of — both deliberate, both flagged in the lakefile:**
1. **LeanArchitect has no `v4.33.0` tag** (newest is `v4.32.0`), so it is pinned to
   **`main`**. That is a reproducibility regression: `main` moves. Re-pin to a tag when one
   appears. `EM/Meta/Blueprint.lean` is in the `EM.lean` closure, so this is load-bearing.
2. **The sibling toolchain mismatch is back.** `../CA` and `../../proofinity/declbuild-meta`
   both declare `v4.31.0` while EM is on `v4.33.0`. Their *sources* compile fine under
   EM's toolchain, but their `.olean` caches are incompatible again. (Bumping the siblings
   is a change to *other repositories* and was not attempted here — see entry (l), which
   does it.) The claim in this entry that `EM/Meta/Strategies.lean` must stay outside the
   `EM.lean` closure was **repeated from a stale lakefile comment and is false**; see (l).

Zulip absence claims re-verified against v4.33 Mathlib: van der Corput, `ZMod.dft`
Parseval, the completely-multiplicative predicate, `liouville_eq_moebius_of_squarefree` and
the necklace identity are all still absent. Version strings updated in the paper and the
zulip file.

### 2026-08-17 (j) — TOOLCHAIN: Lean/Mathlib v4.29.0 → v4.31.0

**Build clean: 0 errors, 0 warnings, `sorry`-free, 3989 jobs.** Registry unchanged at
**288 published / 38 open / 219 proved / 69 conditional**. Paper 171 pages, refs 749/0.

`lean-toolchain` → `leanprover/lean4:v4.31.0`; lakefile: mathlib and LeanArchitect → tag
`v4.31.0`. `lake update` pulled the Mathlib cache (8542 oleans), so no Mathlib rebuild.

**Bonus: the sibling-toolchain mismatch is gone.** `../CA` and
`../../proofinity/declbuild-meta` both already declared `v4.31.0`; the lakefile comment
explaining why their `.olean` caches were incompatible has been replaced. (The lakefile also claimed
`EM/Meta/Strategies.lean` had to live outside the `EM.lean` import closure because of this
mismatch. **That claim was false** — see entry (l).)

**Nine breakages, all fixed** (remarkably few for a two-release jump over 180 files):

| File | Cause |
|---|---|
| `IK/AbelChain.lean` ×2 | `convert … using 1` now emits *instance-equality* side goals, so `field_simp` hit the wrong one. Replaced with `HasDerivAt.congr_deriv`, which fixes only the derivative value |
| `IK/Ch7HilbertB.lean` | same `convert` change; replaced with an explicit cast rewrite |
| `Group/DepartureGraph.lean` | `convert … using 1` no longer closes `{k \| w k = g} = w ⁻¹' {g}` by rfl → `exact hg` |
| `Group/Escape.lean` | `simp` no longer unfolds the `let mk := Units.mk0 …`; added `mk` to the `simpa` set |
| `Equidist/FourierB.lean` | `Complex.isAlgClosed` no longer transitively imported → added `Mathlib.Analysis.Complex.Polynomial.Basic` |
| `LargeSieve/Harmonic.lean` | `convert` change → used `MulChar.coe_equivToUnitHom` directly |
| `LargeSieve/Analytic.lean` | `eq_one_iff_conductor_eq_one` dropped its explicit `p ≠ 0` argument |
| `Population/AvoidanceTube.lean` | bare `simp only` (no lemmas) is now a no-op, not a beta-reducer |
| `Reduction/TailIdentity.lean` | `convert … using 2` left `1/↑S.card = 1/↑(sqfreeCount X)`; supplied the card equality |
| `Population/DefectTelescope.lean`, `FunctionField/DegreeTelescope.lean` | `Tendsto.div` returns the unapplied `f / g`; `simpa` no longer eta-expands. Fixed by stating the target shape explicitly |

**Theme:** most breakage is `convert` becoming stricter (instance-equality goals, fewer
rfl-closures). Where possible the fix removes `convert` entirely rather than patching it —
`congr_deriv`, direct rewrites — which is more robust across future bumps.

**Nine deprecation renames swept:** `tendsto_finset_sum`→`tendsto_finsetSum` (6 files),
`Prime.dvd_finset_prod_iff`→`…finsetProd_iff` (3, dot-notation), `Set.diff_subset`,
`Set.Infinite.diff`, `Set.mem_diff`, `Set.Finite.diff` → `…sdiff`,
`continuous_finset_sum`→`continuous_finsetSum`. One non-rename:
`Subgroup.inf_eq_bot_of_coprime` → `Subgroup.disjoint_of_coprime_natCard` (different type:
`Disjoint` not `⊓ = ⊥`), bridged with `← disjoint_iff`. Also removed one now-no-op
`push_cast`.

**Registry diff is hash-only.** 70–83 of 326 entries changed `type_hash` / `type_deps` /
`pp_type` — Mathlib renames flowing into content-addressed hashes. **Zero declarations
added, removed, or changed status.** Headline chain `full_chain_dsl` still depends only on
`propext, Classical.choice, Quot.sound`.

**The upgrade invalidated a Mathlib-gap claim.** `ArithmeticFunction.liouville` landed in
v4.30/v4.31 (`Mathlib/NumberTheory/ArithmeticFunction/Liouville.lean`). Re-verified every
absence claim in `zulip_mathlib_candidates.md` against the new Mathlib: van der Corput,
`ZMod.dft` Parseval, the necklace identity and the completely-multiplicative *predicate*
all still absent; the Liouville *definition* is not. Entry B2 rewritten — what survives is
`IsCompletelyMultiplicative` (Mathlib states complete multiplicativity only as a bare
per-function equation) and `liouville_eq_moebius_of_squarefree` (Mathlib's Liouville file
has no Möbius connection). **`IK.liouville` in `EM/IK/Ch1.lean` is now redundant and should
be replaced by Mathlib's** — flagged, not done.

Version strings updated in `paper/the_Lean_formalization.tex` (3 places) and the zulip file.

### 2026-08-17 (i) — pass 3: staleness sweep, checker hardened, zulip candidates rebuilt

**No Lean change** except `tools/check_lean_refs.py`. Paper 171 pages, 0 undefined refs.

**`check_lean_refs.py` only validated `\lean{}` macros.** `\code{...lean}` mentions are
prose, so nothing checked them — and they rotted silently through the 2026-08 layout
reorg. Found **19 stale path mentions** across 8 files: `Advanced/*` → `EM/Stochastic/*`,
`Probability/*` → `EM/Stochastic/*`, `Population/Tauberian.lean` and
`Population/AbelChain.lean` → `EM/IK/*`, `EM/Reduction/NoInvariant.lean` →
`EM/Obstruction/`, `IKCh7.lean` → `EM/IK/Ch7Hilbert.lean`, `LargeSieveAnalytic/Harmonic`
→ `EM/LargeSieve/*`, and `VanishingNoiseVariantD.lean` which **no longer exists** (content
is in `EM/Stochastic/NonFaithfulCharacterEscape.lean`).

**Checker extended** with `check_code_paths()`, including an explicit allow-list for the
three `\code{}` mentions that legitimately point at Mathlib (`AbelSummation.lean`,
`PrimesInAP.lean`). Now reports both counts and fails on either. **New invariant: run it
after any file move OR paper edit — it now covers prose mentions too.**

Also: normalised 20 prose `\code{}` mentions to the `EM/...` form to match `\lean{}`
(the generated `codebase_table.tex` is untouched); corrected AlladiDensity 275 → 267 lines
in `the_ensemble_reduction.tex` (the other five mentions already said 267).

**Verified current, no action:** dead-end counts 159/27/10 match `EM/Meta/DeadEnds.lean`;
the three quoted file line counts (Tauberian 557, AbelChain 641, AlladiDensity 267) are
exact.

**§10 (Min/Max Dichotomy) audited — healthy.** 10 subsections, 18 paragraphs, every
paragraph subordinate to its subsection (the "Move 1/2/3" trio is proof structure, not
accretion). No restructuring needed.

### `zulip_mathlib_candidates.md` rebuilt

Was badly stale: header said 78k lines / 148 files / `v4.29.0-rc1` (now 93k / 180 /
`v4.29.0`); **every file path predated the reorg**; line numbers throughout (they rot).

All **72 identifiers mechanically verified** to still exist; all paths corrected and line
numbers dropped in favour of greppable declaration names. **Two claims were false and are
now recorded as withdrawn rather than silently deleted:**
  * *Jordan's inequality* — Mathlib has `Real.mul_le_sin`
    (`Analysis/SpecialFunctions/Trigonometric/Bounds.lean`). Item re-scoped to the
    geometric-sum bound, which is still absent.
  * *Discrete Abel summation* — Mathlib has `Finset.sum_range_by_parts`
    (`Algebra/BigOperators/Module.lean`), in the general module setting. Withdrawn; the EM
    version is a `private` real-valued specialisation.

Re-checked and still genuinely absent: van der Corput, Parseval/Plancherel for `ZMod.dft`
(Mathlib's `Analysis/Fourier/ZMod.lean` has a full algebraic API but no norm-level result),
Liouville as an arithmetic function (only the unrelated `liouvilleNumber`), a
completely-multiplicative predicate (`CompletelyMultiplicative` is only a section name),
the necklace identity. Every Mathlib name cited in the file was verified to exist.

Restructured into tiers A/B/C with a three-item recommendation, flagged the four `private`
declarations (not exportable as-is), and added one not-yet-extracted suggestion (antitone
up to a summable error ⟹ convergent, currently inlined in `DefectTelescope.lean`).

### 2026-08-17 (h) — paper revision, pass 2: §11 restructured; §4.6 split out

**No Lean change.** Paper 171 pages, 0 undefined references; `check_lean_refs` 749/0.

**§11 (18 pp, 46 paragraphs, 6 subsections) — the same accretion as §8, worse.**
  * *Title/content mismatch.* Titled "Open Problems and Paths Forward"; the file is called
    `why_its_hard.tex` and the content is dominated by barriers. **Retitled** "Why It Is
    Hard, and What Would Close It".
  * *§11.3 was a grab-bag.* Nine paragraphs under "The Factorization Independence
    Heuristic", of which **six** were not about the heuristic: Dead Ends as a Roadmap, the
    Four-Way Blocker, The telescope exhausts the algebra, The Mathematical Landscape, The
    two fundamental barriers witnessed, Structural Features of the EM Walk.
  * *The Four-Way Blocker was buried.* The paper's single best explanation of why every
    classical tool fails (independence / multiplicativity / algebraic-geometric structure /
    ergodic stationarity — the EM walk has none) sat at line 281 inside a heuristic
    subsection. **Promoted** to open the section.

  New shape: **§11.1 The Barriers** (what must be proved → four-way blocker → telescope
  exhausts the algebra → the two witnessed barriers #90/#117 → dead ends as a roadmap →
  bridge) · **§11.2 What the Walk Has That Nothing Exploits** (the four structural
  features, promoted from line 400) · then selectability, BRE, the heuristic (now genuinely
  just the heuristic), NAAD, the precise frontier, **§11.8 Does the Walk Hit −1?** (split
  out of the 8-page frontier subsection), Four Questions. Roadmap box rewritten.

**§4.6 "Sieve Routes, in Brief"** — four paragraphs on the large sieve, Bombieri–Vinogradov
and additional sieve routes were filed under §4.5 "Walk Telescoping Identities". Promoted
to their own subsection with a one-paragraph frame pointing at Appendix A.3.

**Appendix A.4 ↔ §11.1 linked.** The Dead-Ends catalogue's grouping headings *are* the
four-way blocker's four requirements seen from the failure side; the table is the evidence
for the blocker. Said so, in both directions.

**Challenged and found sound — no action:**
  * §5.3 "Sieve Structure and Ensemble First Moments" (7 paragraphs) — suspected grab-bag,
    is actually a single argument spine (first moment → positive density → parity → death
    density → absorption → divergence hierarchy → conditional MFRE), framed as such by its
    own opening paragraph, with paragraph labels referenced elsewhere.
  * §4 and §6 — paragraph density low, subsection titles carry the argument.
  * Appendix A.4 vs §11 — complementary, not duplicative (counts/categories in §11.1, the
    meta-reason in the blocker, specific failures in the table).

**Remaining:** §10 (Min/Max Dichotomy, 10 subsections, 15 pp) not yet audited; §12 (Lean
formalization) and the appendix not yet read for staleness against the current registry.

### 2026-08-17 (g) — paper revision, pass 1: (C∞) promoted to its own section

**No Lean change.** Paper 171 pages, 0 undefined references; `check_lean_refs` 749/0.

**Diagnosis.** Six sessions of (C∞) work had accreted inside §8 "Variants of the
Conjecture" — 11 pages spread over three subsections, the last with five paragraphs added
one per session in chronological rather than logical order. Six concrete defects:
  1. **Misfiled.** (C∞) is not a variant of MC; the paper proves it is the necessary
     condition beneath *every* route to MC.
  2. **One map, three names, three homes.** `w ↦ w²+w` appears as `f` (§7.4, the branch
     residue walk), as the take-all rule's walk (§8 intro), and as `q` (§9.6, the map whose
     backward orbit is the (C∞) target) — never identified with itself.
  3. **Stale claim.** "Why the two elementary attacks are unavailable" described the
     congruence target as "a root of Φ₆" — superseded three paragraphs later by the level
     tower, with no forward pointer.
  4. **Invisible arc.** An 8-step narrative with no roadmap and no closing verdict.
  5. **Buried headline.** "MC is at least as hard as a Fermat-type statement" sat in a
     frontierbox at the end, and was duplicated in `why_its_hard.tex`.
  6. **Glossary coverage: zero.** No entry for (C∞), (S), C, PreZero, levels, or witnesses.

**Actions.**
  * New top-level **§9 "The Composite Floor: (C∞)"** (`paper/composite_floor.tex`, 9
    subsections), placed after Variants and before the Min/Max Dichotomy. Restructured
    motivation-first: why everything rests on it → the growth floor (S) → the defect
    telescope → the Sylvester tower → hitting → the level tower → the arboreal tower →
    the same telescope over `𝔽_p[t]` → **the Verdict**. Roadmap box added.
  * `§8.2` keeps the smallness family and the floor theorem, hands off to §9.
  * The FF degree-telescope paragraph **moved** out of `function_field.tex` into §9.8, with
    a pointer left behind — it is about the telescope, not the FF programme.
  * **Map unified**: explicit "one map, arrived at three times" paragraph in §9.6, with
    back-pointers added in §7.4 and §8's take-all discussion.
  * Stale congruence claim rewritten to point forward and to say why enlarging the target
    does not help.
  * New **§9.9 The Verdict**: (C∞) plainly, the hardness lower bound, and *the Fermat
    test* as an explicit filter — applied to every technique in the section.
  * `why_its_hard.tex` duplicate compressed to conclusion + pointer.
  * Abstract: new paragraph on (C∞) — it had **no** mention despite being 12 pages and the
    paper's only unconditional lower bound on MC's difficulty.
  * Introduction tour rewritten; glossary gained 10 entries.

**Remaining for pass 2** (not done): §11 "Open Problems" (18pp) and §4–§6 have not been
audited for the same accretion; `\paragraph` density is very high throughout; the
appendix Dead-Ends catalogue may duplicate §11.

### 2026-08-17 (f) — the arboreal tower: Chebotarev is NOT the missing ingredient

New file `EM/Population/ArborealTower.lean` (+~330 lines). Build clean, 0 warnings,
0 sorries; registry 276 → **288** published; `check_lean_refs` 742 → **751/0**; codebase
180 files / **93,004 lines**; paper 167 → **168 pages**, 0 undefined references.

**The setup.** `Ψ n (w) = q^[n](w) + 1`; level `n` occupied at `w` ⟺ `Ψ n (w) = 0`. Two
identities organise the tree:
  * `Ψ n (0) = 1` — every level polynomial has constant term 1, because `q(0) = 0`;
  * **`q^[n+1](w) = w · ∏_{j ≤ n} Ψ j (w)`** (`sylvWalk_iterate_succ_eq_prod`) — the
    Euclid–Mullin accumulator identity, on the tree. Hence the level values are pairwise
    coprime (`coprime_level_values`) — the Euclid cascade one level up.

**The qualitative Chebotarev question is answered unconditionally, by Euclid.** Feeding
`q^[n]` a multiple of `B!` returns a value `≡ 1 mod B!`, so every prime factor exceeds `B`:

  **`exists_large_prime_level_occupied`** — for every level `n` and bound `B` there is a
  prime `ℓ > B` at which level `n` is occupied; hence infinitely many
  (`levelPrimes_infinite`).

No density theorem used. Chebotarev would upgrade "infinitely many" to "positive density".

**And that upgrade is not what is missing.** Point the same construction at `w = prod N`:
a prime `ℓ` puts `walkZ ℓ N` at level `k` exactly when `ℓ ∣ Ψ k (prod N)`
(`level_witness_iff`), and `Ψ k (prod N)` is the `k`-th Sylvester tower term
(`tower_eq_sylvNat`). So a witness always exists (least prime factor), and by coprimality
the witnesses at distinct levels are **distinct primes** (`minFac_level_injective`) — each
stage `N` carries an infinite sequence of distinct primes, free.

  **`infinitelyManyComposite_iff_witness_proper`**:
  (C∞) ⟺ for every `N` some witness `minFac (Ψ k (prod N))` is a **proper** factor.

On the branch the witness at level `k` is forced to be `Ψ k (prod N)` itself, a prime
larger than `prod N` (`witness_eq_self_of_perpetual`) — exactly the branch.

**Verdict.** Same shape as (S) in `CompositeFloor`: not "does something exist" but "is the
thing that exists small". A density theorem over `ℓ` cannot supply it, because the prime it
must produce has to divide one specific integer. The arboreal picture makes Dead End #90 as
sharp as it can be made: **the arboreal input is free and the residual gap is disjoint from
it.** `ArborealChebotarev` is defined in the file purely to state what is *not* needed;
nothing uses it.

**Paper.** New paragraph "The arboreal tower: Chebotarev is not the missing ingredient" in
§sec:sylvester-tower, with eq:tree-accumulator, Theorem 8.10 (arboreal existence,
unconditional) and the "witnesses are free" keyresult.

### 2026-08-17 (e) — level three, and the engine behind every level

`EM/Population/BackwardLevels.lean` (+~200 lines). Build clean, 0 warnings, 0 sorries;
registry 266 → **276** published; `check_lean_refs` 736 → **742/0**; codebase
179 files / **92,607 lines**; paper **167 pages**, 0 undefined references.

**Level two was not a special case.** The two `q`-preimages of a point are `y` and `-1-y`
(since `q(-1-y) = q(y)`), so their discriminants satisfy the **ring identity**

    (1 + 4y)(1 + 4(-1-y)) = -3 - 16·q(y)      (`preimage_pair_discriminant`)

— provable by `ring`, no Vieta, no field hypothesis. Writing `Δ(z) = -3 - 16z`: the pair of
discriminants one level above `z` multiplies to `Δ(z)`, and the whole tower is governed by
evaluating `Δ` along backward orbits. The level-two constant `13` is just `Δ(-1)`.

**The lift** (`exists_death_level_add_two`): `z` at level `m`, `1+4z` a square, `Δ(z)` a
non-square ⟹ level `m+2` occupied. Level three is the `m = 1` instance
(`exists_death_level_three`), with constant `Δ(ω)Δ(ω²) = 217 = 7·31`
(`delta_pair_product_eq_217`). Since `217 ≡ 1 mod 4` too, the same Jacobi reciprocity
applies: `not_isSquare_iff_jacobiSym` handles both 13 and 217 uniformly
(`not_isSquare_217_iff`), so when both level-two branches are present the level-three
criterion is again a congruence on ℓ (`exists_death_level_three_of_split`).

**Two limits appeared at level three — the real information.**
  * *The criteria stop being rational.* When 13 is a non-residue only one level-two branch
    exists, and the level-three criterion `¬IsSquare (-3 - 16ω)` depends on **ω**, not on a
    rational constant. That is where the tower stops being decided by congruences on ℓ and
    becomes a splitting condition in a bigger field — an arboreal-Chebotarev question, NOT
    formalised and flagged as such.
  * *The tower is finite.* `realizedLevels_finite`: levels are disjoint subsets of a finite
    field, so only finitely many are occupied. Raising the level is a **bounded** resource;
    the depth of the backward-orbit tree of `-1` is an invariant of ℓ, and it is what the
    heuristic `|PreZero ℓ| ≍ √ℓ` actually measures.

**New branch constraint** (`psi_three_ne_zero_of_perpetual`), independent of levels 1 and 2
by disjointness: `w⁸+4w⁷+8w⁶+10w⁵+9w⁴+6w³+3w²+w+1 ≠ 0` for `w = walkZ ℓ N`, `ℓ ≤ prod N`.

**Paper.** §sec:sylvester-tower's "Raising the level past Φ₃" paragraph rewritten around the
identity (eq:delta-identity), Theorem 8.9 (the lift), a two-part keyresult for levels two
and three, and "Where the climb stops, and why that is worth knowing".

### 2026-08-17 (d) — raising the hit level past Φ₃

New file `EM/Population/BackwardLevels.lean` (+~330 lines). Build clean, 0 warnings,
0 sorries; registry 254 → **266** published; `check_lean_refs` 727 → **736/0**; codebase
179 files / **92,362 lines**; paper 165 → **167 pages**, 0 undefined references.

**The conjugacy — the whole point.** Translation by `1` conjugates the **take-all
(Sylvester) walk** `q(y) = y² + y` to `Φ₆`: `Φ₆(w+1) = (w+1)w + 1 = q(w) + 1`
(`phi6_add_one_eq`), hence `Φ₆^[k](w+1) = q^[k](w) + 1` (`iterate_phi6_add_one`). So

  **`walkZ ℓ N + 1 ∈ PreZero ℓ` ⟺ the take-all walk from `walkZ ℓ N` reaches `−1`**
  (`mem_preZero_iff_sylvWalk_reaches_neg_one`),

and **the hit level is the number of take-all steps before death**. Level 1 is `Φ₃(w) = 0`
— exactly the classical death equation. The two rules the paper contrasts (`minFac` vs
take-all) turn out to be the same object at different depths.

**Structure of the tower.**
  * `death_level_unique` — levels are **disjoint**: `q(−1) = 0`, `q(0) = 0`, so a dead
    orbit is absorbed and never returns.
  * `six_dvd_sub_one_of_death` — raising the level buys **no new moduli**: any hit at level
    ≥ 1 gives a Φ₃ root, hence `6 ∣ ℓ − 1`. Honest negative.

**Past Φ₃ — level two exists, by reciprocity not by search.**
  * `sylvWalk_step_of_isSquare` — level `m` → `m+1` needs `1 + 4z` to be a square.
  * `cube_root_pair_product_eq_thirteen` — Vieta (`ω + ω² = −1`, `ω³ = 1`) gives
    **`(1+4ω)(1+4ω²) = 1 − 4 + 16 = 13`**.
  * `exists_death_level_two` — if Φ₃ has a root and **13 is a quadratic non-residue**, the
    product of the two discriminants is a non-residue, so exactly one is a residue and
    level 2 is non-empty.
  * `isSquare_thirteen_iff` — quadratic reciprocity (13 ≡ 1 mod 4, sign trivial): 13 is a
    non-residue mod ℓ iff ℓ is a non-residue mod 13, i.e. `ℓ mod 13 ∈ {2,5,6,7,8,11}` —
    **density 1/2**.

**The payoff.** Since levels are disjoint, the branch acquires a constraint that is *not* a
consequence of the Φ₃ obstruction (`psi_two_ne_zero_of_perpetual`):

    walkZ ℓ N^4 + 2·walkZ ℓ N^3 + 2·walkZ ℓ N^2 + walkZ ℓ N + 1 ≠ 0

for every prime `ℓ ≤ prod N`. And the mechanism iterates: level `m+1` needs only some
level-`m` discriminant to be a square.

**Bounded gain, stated.** Moduli unchanged; barrier untouched (still one specific orbit).
What changed: the classical Φ₃ obstruction is now known to be rung one of a tower, and the
rungs above are reachable by reciprocity.

**Paper.** New paragraph "Raising the level past Φ₃" in §sec:sylvester-tower, with
Theorem 8.8 (levels are take-all steps) and the level-two keyresult.

### 2026-08-17 (c) — (C∞) as a hitting statement: the backward orbit of zero

New file `EM/Population/BackwardOrbit.lean` (+~290 lines). Build clean, 0 warnings,
0 sorries; registry 244 → **254** published; `check_lean_refs` 720 → **727/0**; codebase
178 files / **91,997 lines**; paper **165 pages**, 0 undefined references.

**The move.** Reduction mod `ℓ` commutes with the Sylvester recursion, so `ℓ` divides the
`k`-th tower term seeded at `s` exactly when `s mod ℓ` reaches `0` under `k` steps of
`Φ₆(x) = x² − x + 1` (`cast_tower`, `dvd_tower_iff`). With
`PreZero ℓ := {x : ∃ k, Φ₆^[k] x = 0}` (the backward orbit of `0`):

  * **`backwardOrbitHitting_iff_infinitelyManyComposite`** — (C∞) ⟺ for every `N` some
    prime `ℓ` puts `walkZ ℓ N + 1` in `PreZero ℓ`, witnessed below the tower term it kills.
    An *equivalence*, so nothing is lost and the whole target ladder transfers.
  * **`walkZ_notMem_preZero_of_perpetual`** — the contrapositive branch criterion: on the
    perpetual-primality branch the walk value at the branch point avoids `PreZero ℓ` for
    *every* prime `ℓ ≤ prod N` simultaneously.
  * `infinitelyManyComposite_of_small_backward_hit` — the usable sufficient form.

**Why it is worth having — the calibration.** MC asks the walk to hit a *single residue*
for *every* prime. (C∞) asks it to hit `PreZero ℓ` for *some* prime, per stage. Two formal
facts make the second target the larger one:

  * `mem_preZero_of_phi6_mem` — `PreZero` is backward-closed: a union of all preimage
    levels, not one point.
  * **`phi6_add_one`: `Φ₆(w+1) = w² + w + 1 = Φ₃(w)`** — so *level one* of `PreZero` is
    exactly the take-all rule's death equation, the one driving the density-1/2 failure.
    Every Φ₃ argument in the project uses one level; (C∞) may use any level.
    (`phi3_ne_zero_of_perpetual` records the level-1 branch criterion.)

Against that, `six_dvd_sub_one_of_phi6_root`: a nonzero element of `PreZero ℓ` forces a
primitive 6th root of unity, so `6 ∣ ℓ−1` — the target is `{0}` for half the primes.
Heuristically (NOT formalised, and flagged as such in the file and paper) the in-tree of a
node has size `≍ √ℓ`, so target density `ℓ^{-1/2}` vs `ℓ^{-1}`, and
`Σ_{ℓ≡1(6)} ℓ^{-1/2}` diverges at rate `√L/log L` vs `log log L`.

**Honest limit.** This does not evade Dead End #90: the criterion still asks where one
specific orbit sits modulo some prime, and no sieve constrains a single integer. What it
buys is that every hitting hypothesis in the repo is now visibly overkill for (C∞), and the
classical Φ₃ obstruction is located as level 1 of a much taller target.

**Audit** (`backward_orbit_landscape`): RD, MC, (V) and `growthConstant = 0` all imply
(BO), automatically, since (BO) ⟺ (C∞).

**Paper.** New paragraph "(C∞) as a hitting statement: the backward orbit of zero" in
§sec:sylvester-tower, with Theorem 8.7 and the MC-vs-(C∞) target table.

### 2026-08-17 (b) — CORRECTION + sharpening: the growth constant is a COMPLETE invariant

`EM/Population/CompositeFloor.lean`, `EM/Population/DefectTelescope.lean`,
`EM/FunctionField/DegreeTelescope.lean` (+~330 lines). Build clean, 0 warnings, 0 sorries;
registry 233 → **244** published (271 → **282** declarations); `check_lean_refs` 710 →
**720/0**; codebase 177 files / **91,625 lines**; paper 164 → **165 pages**, 0 undefined
references.

**The claim that was wrong.** The 2026-08-16 handoff asserted — and the earlier entry
today repeated into the paper — that `growthConstant > 0` describes a failure branch
"much wider than perpetual primality", since the least prime factor need only be
`(prod n)^{1−o(1)}`. **False.** Trial division: `minFac X > √X ⟹ X prime`
(`Euclid.minFac_sq_le`, already in the repo since Core). A ratio
`log(seq (n+1))/log(prod n)` eventually above `1/2` *is* primality. The branch is exactly
perpetual primality.

**What replaces it — the defect gap.** At a composite stage
`log (seq (n+1)) ≤ (1/2) log (prod n + 1)`, so `defect n ≥ (1/2) logProd n − 2^-(n+2)`; at
a prime stage `defect n ≤ 0`. Nothing in between (`defect_gap`). Feeding the composite
case into the telescope, one composite stage multiplies `normLogCorr` by `3/4`
(`normLogCorr_succ_le_of_not_prime`), giving the unconditional **damping bound**

    log (prod N) ≤ (log 2 + 1/3) · (3/4)^{compositeEuclidCount N} · 2^N

(`logProd_le_pow_mul`) — a refinement of `prod_add_one_le_three_pow`, which is the case of
no composite stages. Hence infinitely many composite stages force `C = 0`, and:

  * **`InfinitelyManyComposite ↔ growthConstant = 0`**
    (`infinitelyManyComposite_iff_growthConstant_eq_zero`);
  * **`0 < growthConstant ↔ ∃ N, PerpetualPrimality N`**
    (`growthConstant_pos_iff_perpetualPrimality`);
  * `defect_dichotomy` restated: both alternatives are equivalences.

**Why this is good news, not bad.** It costs the hope that the growth reformulation was
weaker than (C∞) — it is a complete invariant, so `CompositeFloor`'s "equivalent in
strength" remark is now literally a theorem. What it buys: the failure branch is *exactly*
the autonomous branch, so the autonomous-map obstruction, the Φ₃ density-1/2 exclusion, the
Φ₆ orbit counting and the `n ≤ 7` refutation bear on the **whole** of it. One might have
feared the analysable branch was a corner of the true failure set; it is all of it.

**Function field, same but exact.** `2 * ffDeg' n ≤ ffDeg n` when reducible
(`two_mul_ffDeg'_le_of_not_irreducible`) — an exact ℕ inequality, no error term. One
reducible stage multiplies `ffNormDeg` by exactly `3/4`, giving
`deg (ffProd N) ≤ (3/4)^{r(N)} · 2^N` (`ffDeg_le_pow_mul`, no constant, since
`deg ffProd 0 = 1`), and the same complete invariant
(`ffInfinitelyManyReducible_iff_ffGrowthConstant_eq_zero`,
`ffGrowthConstant_pos_iff_perpetual`). The earlier FF docstring claim that
`ffDefect n = 1` is compatible with a `(1−o(1))`-degree factor was also false and is
removed: reducibility forces `ffDefect n ≥ ffDeg n / 2`.

**Paper.** `variants_landscape.tex` §sec:defect-telescope rewritten from "How wide the
failure branch really is" onward (defect gap lemma, damping bound, complete-invariant
keyresult, sharp dichotomy). `why_its_hard.tex` Evidence-against item (0): the inserted
paragraph now says the branch is exactly this one. `function_field.tex`: trial-division
paragraph replaces the "same width" claim; table row `C = 0 ⟺ (C∞)`.

### 2026-08-17 — The growth technique: (S), the defect telescope, and the FF degree telescope

Three deliverables from `tmp/handoff_growth_technique_2026-08-16.md`. New files
`EM/Population/DefectTelescope.lean` (+~400 lines) and
`EM/FunctionField/DegreeTelescope.lean` (+~300 lines); `EM/Population/CompositeFloor.lean`
+~120 lines. Build clean, 0 warnings, 0 sorries; registry 224 → **233** published
(262 → **271** declarations); `check_lean_refs` 685/0 → **710/0**; codebase 175 → **177
files / 91,131 lines**; paper 160 → **164 pages**, 0 undefined references.

**1. The floor is not (C∞); it is (S), a growth statement.** The convergence proof in
`CompositeFloor` never used primality — only that `seq n` is eventually large, measured
against *any* benchmark with summable reciprocals (`summable_one_div_seq_of_lower_bound`).
Contrapositively `RD` forces the selected primes below every such benchmark infinitely
often (`exists_lt_of_reciprocalDivergence`); arithmetically, for every fixed `c`,
`minFac (prod n + 1) < 2^(n−c)` infinitely often
(`exists_small_minFac_of_reciprocalDivergence`). This is strictly stronger than (C∞),
which only asks for a *proper* factor; (S) with `c = 0` returns (C∞) because
`2^n < prod n + 1` (`infinitelyManyComposite_of_reciprocalDivergence_via_growth`).
Perpetual primality is now a corollary — the case `f n = 2^n`. Landscape:
`growth_floor_landscape`.

**2. The defect telescope.** `logProd (n+1) = 2·logProd n − defect n` exactly, where
`defect n = logProd n − log (seq (n+1))`; telescoping gives
`normLog N = logProd 0 − ∑_{n<N} defect n / 2^(n+1)`. The defect is negative by at most
`2^-(n+1)` (`neg_two_pow_le_defect`), so `normLog` is antitone up to a summable correction
and converges: **`growthConstant := lim log (prod N)/2^N ≥ 0`**. Then

  * `subtower_growth_iff_growthConstant_eq_zero` — the sub-tower criterion of
    `CompositeFloor` is *exactly* `C = 0` (so it is vacuous when `C > 0`, where
    `log₂log₂ prod N = N + log₂ C + o(1)`);
  * `infinitelyManyComposite_of_growthConstant_eq_zero` — (G) ⟹ (C∞);
  * `growthConstant_eq_zero_of_reciprocalDivergence` — **RD ⟹ C = 0**, a new floor
    strictly below (S): every smallness statement forces `log (prod N) = o(2^N)`, a
    statement about the orbit as a whole. Proof: `C > 0` makes the selected primes exceed
    `(√2)^n` eventually, and (S) then makes `∑ 1/seq k` converge;
  * `tendsto_log_seq_div_logProd_of_pos` — `C > 0 ⟹ log (seq (n+1))/log (prod n) → 1`.

  Combined (`defect_dichotomy`): **either (C∞), or `minFac (prod n + 1) = (prod n)^(1−o(1))`.**
  The failure branch is therefore *much* wider than perpetual primality — it requires no
  Euclid number to be prime — and on it there is no autonomous map to exploit, which is
  why every mechanism in `why_its_hard.tex` attacks only the extreme point. Note the
  `2^-n` weighting: no finite computation can contribute to `C`.

**3. The degree telescope over `𝔽_p[t]`** (handoff §4a). Degrees are additive exactly and
`deg (ffProd n + 1) = deg (ffProd n)` on the nose, so the defect is a **nonnegative
integer**, the recursion `ffDeg (n+1) + ffDefect n = 2·ffDeg n` is exact, `ffNormDeg` is
antitone with **no correction term**, and `ffDefect n = 0 ⟺ ffProd n + 1 irreducible` is an
**equivalence** (`ffDefect_eq_zero_iff`) rather than an approximation. `C_FF = 0 ⟹ (C∞_FF)`
becomes a two-line argument. **But the question does not move**: `ffDefect n = 1` still
means the factor has degree `deg (ffProd n) − 1 = (1−o(1))·deg`, so `ffDefect_dichotomy`
has exactly the same shape and width as over `ℤ`. What would close it is the least-degree
irreducible factor of *one* polynomial; the density of irreducibles, exactly computable
over `𝔽_p[t]`, is a population statement. Dead End #90 in the setting where every analytic
input is a theorem — the strongest available evidence that the analytic input was never
the obstruction.

**Paper.** `variants_landscape.tex`: sharpened §sec:composite-floor with the growth floor
keyresult, new §sec:defect-telescope (telescope, growth constant, defect landscape,
dichotomy). `function_field.tex`: new "degree telescope" paragraph + 3 new rows in the
side-by-side table. `why_its_hard.tex`: "the branch to be excluded is wider than perpetual
primality" inserted into Evidence-against item (0). `introduction.tex` updated.

### 2026-08-16 — Can either half be proved? (C∞) as a growth statement

`EM/Population/CompositeFloor.lean` (+~70 lines). Build clean, 0 warnings; registry
202 → **205** published; `check_lean_refs` 684/0; codebase 175 files / **89,965 lines**;
paper 159 → **160 pages**, 0 undefined references.

**The asymmetry.** Prime and composite stages partition `ℕ`, so *at least one* of
"infinitely many prime Euclid numbers" and (C∞) is true — free. But only one disjunct
carries content: if (C∞) fails, MC fails and every smallness statement fails with it; if
only finitely many are prime, nothing follows. The free disjunction says "either the
interesting statement holds or the harmless one does", which is no help.

**The prime half: no technique to try.** Every method producing infinitely many primes in
a sparse sequence needs either a positive-density family to sieve or algebraic structure
supporting Chebotarev. The Euclid numbers offer neither — one integer per index, and the
defining recursion invokes factorisation itself. Fermat, Mersenne and primorial numbers are
far more structured and all three questions are open.

**The composite half: a genuine reformulation.** Splitting the first `N` stages and
applying the self-limiting theorem,

    N ≤ #{n < N : prod n + 1 composite} + log₂log₂ (prod N)

(`le_compositeEuclidCount_add_log_log`), so composites occur past every stage as soon as
`N` outruns `log₂log₂ prod N` by an unbounded margin
(`infinitelyManyComposite_of_subtower_growth`). **(C∞) follows from any bound saying the
accumulator grows strictly slower than the maximal tower rate.**

**Its own difficulty, stated.** The selected factor never exceeds the Euclid number, so
`prod N + 1 ≤ 3^(2^N)` unconditionally (`prod_add_one_le_three_pow`), whence
`log₂log₂ prod N ≤ N + O(1)` and the inequality is vacuous unless the ceiling is beaten by
an unbounded margin — which is exactly what perpetual primality forbids. So the
reformulation is equivalent in strength to (C∞), not weaker. What it buys is a **change of
subject**: the difficulty moves from the primality of individual terms, where nothing can
be said, to the growth rate of one explicit recursion.


### 2026-08-16 — Why a Euclid number should generally not be prime

`EM/Population/CompositeFloor.lean` Part 5 (+~80 lines). Build clean, 0 warnings; registry
199 → **202** published; `check_lean_refs` 682/0; paper 158 → **159 pages**, 0 undefined
references.

**The mechanism.** Compare the two branches of one step. If `prod n + 1` is composite its
least factor is a *proper* factor and the accumulator grows by that factor. If it is prime
the least factor is the whole Euclid number, so `prod (n+1) = prod n · (prod n + 1) >
(prod n)²` — the accumulator **squares** (`sq_lt_prod_succ_of_prime`). Each prime Euclid
number doubles `log prod n`, so the next candidate, whose primality has probability of
order `1/log`, is twice as unlikely. Primality does not merely occur rarely here; it
consumes the resource that makes it possible.

**Theorem (unconditional).** If `m` of the first `N` Euclid numbers are prime then
`2^(2^m) ≤ prod N`, i.e. `m ≤ log₂ log₂ (prod N)`
(`two_pow_two_pow_primeEuclidCount_le_prod`, `primeEuclidCount_le_log_log`). Nothing is
assumed — the composite steps only help, since they enlarge the accumulator too.

**The matching heuristic** (derived, not measured). The Euclid number is coprime to the
whole bag, so it is rough, and roughness makes primality *more* likely, not less:
`P ≈ (1/log X)·∏_{p ∈ Sₙ}(1−1/p)^{-1}`. On MC-like behaviour the bag is essentially the
primes up to `pₙ`, so Mertens gives correction `≍ e^γ log pₙ` while
`log prod n = θ(pₙ) ≍ pₙ`. Hence `P(prod n + 1 prime) ≍ e^γ/n`. Two consequences pulling
opposite ways: the probability tends to 0, so the Euclid numbers should be composite for
*almost every* n — that is **(C∞) with density one**; but `∑ 1/n` diverges, so one should
expect **infinitely many prime Euclid numbers** as well. The sequence should enter the
autonomous branch again and again and leave it every time.

**The two estimates agree.** The heuristic predicts `≍ log N` primes among the first `N`;
the theorem caps the count at `log₂log₂ prod N ≍ log₂(n log n) ≍ log N` on the same
behaviour. So the unconditional bound is *saturated by the expected truth* and cannot be
improved without genuinely new input — the same conclusion as the Sylvester-tower section,
reached from the opposite side.

Paper: new paragraphs in §sec:composite-floor with the step dichotomy,
Theorem~\ref{thm:self-limiting}, and the Mertens derivation.


### 2026-08-16 — The autonomous branch: refuted where the data reaches, plus the discussion

`EM/Population/SylvesterTower.lean` Part 4 (+~70 lines). Build clean, 0 warnings; registry
195 → **199** published; `check_lean_refs` 680/0; codebase 175 files / **89,776 lines**;
paper 155 → **158 pages**, 0 undefined references (needed a third lualatex pass).

**The finding.** The autonomous branch is not exotic — *the sequence has been on it.*
`prod 6 + 1 = 6221671` and `prod 7 + 1 = 38709183810571` are both prime, so the
accumulator took the step `P ↦ P(P+1)` twice in a row at stages 6 and 7. It broke out at
stage 8:

    prod 8 + 1 = 1498400911280533294827535471 = 139 · 10779862671083836653435507

**The theorem.** `not_perpetualPrimality_of_le_seven` — the branch cannot begin at or
before stage 7. Crucially it needs **no primality certificate** for the 14-digit
`prod 7 + 1`: the hypothesis supplies what would otherwise have to be proved. Perpetual
primality from `N ≤ 7` gives primality at stage 7, hence forces
`prod 8 = prod 7 · (prod 7 + 1)`, and then demands `prod 8 + 1` be prime — refuted by 139.
Also `euclid_prime_at_six` (free from `seq_seven` + `prod_six`, no new primality proof) and
`prod_one` … `prod_seven`.

**The escape mechanism, quantified.** `ℓ ∣ q_{n+1}` iff `q_n` is a root of `Φ₆` mod `ℓ`,
which needs `ℓ ≡ 1 mod 6`. `Φ₆` has unique fixed point 1, `0 ↦ 1`, and the only preimages
of 1 are 0 and 1 — so an orbit not starting at 1 either passes through 0 (the branch dies)
or is trapped in another cycle. With `ρ(ℓ)` = proportion of residues whose orbit reaches 0:
mean `ρ ≈ 0.072` over the 207 primes `≡ 1 mod 6` below 3000 (`ρ(7) = 0.857`,
`ρ(13) = 0.615`), partial sums growing. So perpetual primality must dodge every such prime
forever — heuristic probability `∏(1−ρ) = 0`, by a mechanism internal to the autonomous
map rather than "large numbers are rarely prime".

**Why it does not become a proof** (checked, worth recording so nobody re-runs it): it
would suffice to find many `ℓ` for which *every* orbit reaches 0, since each would have to
lie in the finite bag at the branching stage. A search over all 330 primes `≡ 1 mod 6`
below 5000 finds **exactly one**, `ℓ = 7`. The condition "`{1}` is the only cycle" is rare,
so the counting argument is unavailable — orbit specificity again, in the one setting where
the dynamics is autonomous. Also note `Φ₆` is conjugate to `y ↦ y² + 1/4`, the cusp of the
Mandelbrot set: the fixed point has multiplier 1.

**Paper.** `why_its_hard.tex` gains the refutation and the escape estimate inside
"Evidence against" item (0), and a closing §sec:four-questions answering: what if MC is
false (every no-go here is one-directional evidence against falsity); what follows if it is
provable (the machinery, and (C∞)/WM/RD/(V) as open consequences); does RH imply MC (no —
and over `F_p[t]`, where RH *is* a theorem, the specific-orbit statement stays open); and
why believe it true and provable. Closes with the thesis: **MC is true because `minFac` is
structureless, and hard for exactly the same reason.**


### 2026-08-16 — CompositeFloor and SylvesterTower written into the paper

No Lean change. Paper 153 → **155 pages**, 0 undefined references, `check_lean_refs`
676/0. Two new subsections in `variants_landscape.tex`, placed after the target ladder.

**§sec:composite-floor — "The Smallness Family and Its Floor."** Tabulates
`MissingFinite` / `WM` / `RD`, records that every implication in the family runs
*downwards* from MC and that nothing in it was known unconditionally, then gives the
floor as a `keyresult`: each of the four implies (C∞), and on the perpetual-primality
branch all three smallness statements fail. Notes explicitly what is *not* consumed —
neither Bertrand nor the `Φ₃` mod-3 argument, only `2^(n+1) ≤ prod n` — so
`MC ⟹ (C∞)` is recovered from a strictly weaker hypothesis. Closes with the prefix
inequality `∑_{p < min M} 1/p ≤ ∑' 1/seq k` and its contrast with `WM ⟹ RD`.

**§sec:sylvester-tower — "(C∞) Identified: the Sylvester Tower."** The recursion
`s ↦ s² − s + 1`; `prod n + 1 = 3, 7, 43, 1807` is Sylvester from its second term; the
break at `1807 = 13·139` explaining `seq 4 = 13`; Theorem (tower primality iff perpetual
primality) and the (C∞) restatement; the loop with the take-all rule. The offline
attribution caveat is stated as a belief, not a citation. A paragraph shows both
elementary attacks are unavailable — congruence (roots of `Φ₆`, orbit specificity) and
reciprocity, with the full symbol computation and its numerical check at `p = 3, 7, 43`.
A frontierbox records that (V) ⟹ (C∞) too, so three independent lines — the target
ladder, the smallness family, and the obstruction programme of §sec:anatomy-axis —
terminate at the same open statement.

Cross-references restored in both directions: the anatomy frontierbox now points at
§sec:composite-floor. The introduction's Organization paragraph names the take-all rule,
the target ladder, the smallness family and the floor, and flags that the receptacle
section's conditional compositeness result has had its hypothesis weakened.

Two LaTeX traps hit and fixed: `\seq` takes the *starting point* as its argument
(`\seq{2}(k)`, not `\seq(k)`), and `$\mathrm{free\_transition}$` sends lualatex into an
input-stack overflow — Lean names in prose must go through `\lean{}{}`.


### 2026-08-16 — The anatomy axis, settled

New file `EM/Obstruction/Anatomy.lean` (~200 lines, built first try). Build clean, 0
warnings; registry 190 → **195** published; `check_lean_refs` 670/0; codebase **175 files
/ 89,695 lines**; paper 152 → **153 pages**, 0 undefined references.

**The question, made precise.** An omission proof reasons backwards from the selection
event, so the content of the axis is the strength of `Φ N = q ⟹ (property of N)`.

* **`minFac N = q` is a congruence condition** (`minFac_eq_iff`): `q ∣ N` and no odd prime
  below `q` divides `N`, nothing else. Every clause is divisibility by a prime `≤ q`,
  hence decided by `N mod M` at any rich `M` (`minFac_eq_congruence_determined`). The min
  rule hands a proof **no anatomy at all** — its selection condition is already inside the
  congruence fragment, empty at every modulus since `RuleTransition`.
* **`maxFac N = q` is decided by no modulus** (`maxFac_not_congruence_determined`). Cheap
  witness: `N₁ = 2M+1` and a Dirichlet prime `p ≡ 1 (mod M)` with `p > N₁`; then
  `maxFac p = p` while `maxFac N₁ ≤ N₁ < p`. That is the anatomy Cox–van der Poorten's
  second move consumes.

**Anatomy as state is inert.** `AnatomyInductionProof q m α` has its invariant on pairs
(residue, anatomy value) with a step clause admitting *every* anatomy value — the honest
model, since the anatomy of `Pₙ₊₁` is not a function of the residue of `Pₙ` and the
candidate; a proof that could predict it would already be the anatomy theorem being
sought. It projects onto its first coordinate to a `CongruenceInductionProof`
(`toCongruenceProof`), so the fragment is empty for every missing prime at every modulus
(`no_anatomy_induction_proof`). The avoid clause never consulted the anatomy: whether `q`
is selected at `N` depends on `N`, not on how the accumulator factors.

**What this leaves.** Nothing on this axis is an *invariant* question any more. What
survives is a demand for a theorem about the anatomy of the specific integers
`prod n + 1` — composite infinitely often (C∞), largest prime factor large, not smooth.
Those are number-theoretic facts about one orbit; Dead End #90 applies verbatim. **The
residue of the obstruction programme is not a wider class of invariants to kill; it is a
single, named, open anatomy statement.**

Recorded as a remark, not formalised: the accumulator's own `ω` is the stage index
(`prod n` is a product of `n+1` distinct primes), so tracking it is the graded fragment —
which still carries the parity hypothesis `RuleTransition` removed from the plain
fragment, so that combination is covered only at odd moduli for now.

Paper: new §sec:anatomy-axis in `the_min_max_dichotomy.tex` with both determination
theorems, the inertness theorem, and a frontierbox stating the residue. It answers the
question the chapter previously ended on.

**Not yet in the paper**: the `CompositeFloor` and `SylvesterTower` results of earlier
today are machine-checked and logged but appear only as `\lean{}` citations, without their
own section.


### 2026-08-16 — The Cox–van der Poorten obstruction class, unified

New file `EM/Obstruction/RuleTransition.lean` (~250 lines). Build clean, 0 warnings;
registry 185 → **190** published; `check_lean_refs` 665/0; codebase **174 files /
89,426 lines**; paper 151 → **152 pages**, 0 undefined references.

This discharges the "Reconciliation TODO" that `EM/Obstruction/MaxVariant.lean` had
carried since Session 300.

**The gap.** `Obstruction.no_congruence_induction_proof` proved the min-side fragment
empty only at **odd** moduli, while the one inhabited instance in the literature —
`maxProofFive` / `max_cvdp_obstruction_five` — lives at **m = 12**. The technique that
works sat outside the theorem saying the technique fails.

**The repair.** Oddness entered at exactly one point: extraction must produce an odd
`N ≥ 3` in the class `r + 1`, and for even `m` a class can be entirely even. Carry the
parity as a witness — `OddRepresentable m r` = the class `r+1` contains an odd natural.
It holds along the orbit (`prod n` even); it is closed under the transition for a reason
cheaper than expected (`r+1` odd ⟹ `r` even ⟹ `r·s` even for **any** multiplier — no
hypothesis on `s`); and `N = c + 2mK` realises it above any bound at every modulus.
Intersecting the invariant with it gives a certificate at every modulus:
`no_congruence_induction_proof_of_ne_zero` has hypothesis `m ≠ 0`.

**The unification.** `R Φ m r r' ↔ ∃ N odd ≥ 3, N ≡ r+1 (m), r' = r·Φ N`, with
`Propagating` / `ForcingState` / `Blocks` / `RuleObstruction` built from it.
`MaxVariant.MaxR` and `CvdP.Transition` are the cases `Φ = maxFac` and `Φ = Nat.minFac`
by `Iff.rfl` (`maxR_iff`, `minR_iff`). A min-side obstruction **is** a
congruence-invariant induction proof (`toCongruenceProof`): propagation is the step case,
tail-containment the base, blocking the avoid clause. The semantic and proof-theoretic
no-gos are two readings of one theorem.

**The dichotomy** (`cvdp_dichotomy`): one class, inhabited at `(maxFac, 5, 12)`, empty at
`(minFac, q, m)` for every missing `q` and every `m ≠ 0`. This supersedes the
single-number witness `cvdp_selection_rule_asymmetry` (the integer 35, kept as
illustration) with a statement about the whole class of arguments.

**Scope recorded honestly.** `ForcingState Φ` here is the *existential* reading (some
candidate selects `q`) — the notion MaxVariant verifies. `CvdP.ForcingState` is the
*universal* reading used inside the certificate machinery. Universal implies existential
when the class holds an odd candidate, so `no_min_rule_obstruction` does **not** subsume
`CvdP.no_cvdp_obstruction`; it trades that direction for dropping both the parity and the
richness hypotheses, which is exactly what reaching `m = 12` requires.

Downstream: `BagInformation.bag_information_landscape` clause (3) strengthened from
`Odd m` to `m ≠ 0`; `MaxVariant`'s Reconciliation TODO marked discharged; paper
`the_min_max_dichotomy.tex` keyresult rewritten over the unified system, plus two new
paragraphs ("Why 'every modulus' is the load-bearing word", "A min-side obstruction *is*
an induction proof").


### 2026-08-16 — Codebase accounting: the four unlisted files

No mathematics changed. `gen_codebase_table.py` reported four `.lean` files on disk but
absent from `tools/codebase_table.tsv`; all four are now resolved and the generator runs
clean. Active codebase 170 → **173 files / 89,126 lines**; 185 incl. Archive.

**`EM/Reciprocity/NoInvariant.lean` → `EM/Archive/Reciprocity/NoInvariantDraft.lean`.**
Not an orphaned working file but an *incomplete draft* that never compiled:

* dead import — `Mathlib.NumberTheory.DirichletCharacter` was split upstream into
  `DirichletCharacter/Basic.lean` (repaired in the archived copy so the graph stays valid);
* **8 `sorry`s**, including both headline theorems and `forcing_reach`. The live codebase
  is genuinely `sorry`-free (the 68 other occurrences repo-wide are documentation text
  reading "zero sorry"), so it could not be admitted to the build;
* a duplicated tail from a bad merge — `no_reciprocity_invariant` and `min_max_dichotomy`
  each appear twice, the second copies outside the namespace with an unbound `m` and a
  one-argument `CvdP.CvdPObstruction`; they would not typecheck even with the `sorry`s.

Archived under the RED-chain `import + #exit` pattern with a banner recording the
supersession, which is total:

| draft declaration (sorried) | live replacement (proved) |
|---|---|
| `no_reciprocity_invariant` | `Reciprocity.no_reciprocity_induction_proof` |
| `forcing_reach` | `Obstruction.congruence_reaches_forcing`, on `CvdP.free_transition` |
| `min_max_dichotomy` right conjunct | `MaxVariant.max_cvdp_obstruction_five` |

The draft's thesis — the reciprocity symbol algebra cannot block a prime in the min
sequence, the min factor support being cofinite — survives intact as
`no_reciprocity_induction_proof`.

**`EpsilonDegeneration.lean`, `RandomVariant.lean`, `ThreeAlmostSure.lean`.** Complete,
`sorry`-free, and already imported by `EM.lean` — only their TSV rows were missing. Added.


### 2026-08-16 — (C∞) identified: the Sylvester tower

New file `EM/Population/SylvesterTower.lean` (~180 lines). Build clean, 0 warnings;
registry 181 → **185** published, 38 open points; `check_lean_refs` 659/0; codebase
170 files / 86,667 lines.

**The identification.** On the perpetual-primality branch the Euclid numbers satisfy
`(prod (n+1) + 1) = (prod n + 1)² − (prod n + 1) + 1` — *Sylvester's recursion*. And
`prod n + 1` for `n = 0,1,2,3` is `3, 7, 43, 1807`, i.e. Sylvester's sequence from its
second term: **the Euclid–Mullin sequence is Sylvester's sequence for exactly as long as
the Euclid numbers stay prime**, and it broke away at `1807 = 13·139`, which is why
`seq 4 = 13`. Verified numerically.

`perpetualPrimality_iff_tower_prime` makes it exact, and
`infinitelyManyComposite_iff_tower_composite` restates (C∞) as: for every `N`, the
Sylvester tower seeded at `prod N + 1` contains a composite term. Whether Sylvester's own
sequence has only finitely many primes is (to the author's knowledge, unverified offline)
a recognised open problem. This also closes a loop with the take-all selection rule, which
*is* Sylvester's sequence — the `minFac` rule degenerates to the take-all rule precisely on
the perpetual-primality branch.

**Why the two elementary attacks are dead.** *Congruence*: forcing a small prime `ℓ` into
`prod n + 1` requires steering `prod n mod ℓ` onto a root of `Φ₆` (which exist iff
`ℓ ≡ 1 mod 6`) — orbit specificity, Dead End #90, `CvdP.free_transition`. *Reciprocity*:
the symbol data is automatically consistent. Since `prod n ≡ 2 (mod 4)` and
`p ≡ 1 (mod seq k)`, reciprocity gives `(seq k / p) = (−1)^((seq k − 1)/2)`, hence
`(prod n / p) = (2/p)·(−1)^t` with `t = #{k ≤ n : seq k ≡ 3 mod 4}`; but
`(prod n / p) = (−1/p) = −1` and `(2/p)` is fixed by `prod n mod 8`, which is fixed by the
*same* `t`. Both sides agree identically — verified numerically at `p = 3, 7, 43`. This is
the concrete instance of `Reciprocity.no_reciprocity_induction_proof`.

**The floor reaches the whole ladder.**
`infinitelyManyComposite_of_everyPrimeDividesEuclid`: even (V) — the weakest orbit target,
asking only that every odd prime *divide* some Euclid number — forces (C∞). Bertrand
supplies a prime strictly between `prod T + 1` and the next Euclid number; it is too large
to divide the earlier ones and too small to equal any later one, all of which are prime.
So (C∞) sits beneath `HH → MC → V` as well as beneath the reciprocal-sum family.


### 2026-08-16 — The composite floor under every smallness statement

New file `EM/Population/CompositeFloor.lean` (~200 lines). Build clean, 0 warnings;
registry 175 → **181** published, 35 → **38** open points; `check_lean_refs` 659/0;
codebase 168 files / 86,245 lines.

**The question.** `EM/Population/WeakMullin.lean` already defines the natural weakenings
of MC that speak about the *size* of the missing set — `MissingFinite`, `WeakMullin`
(`∑_{q missed} 1/q` converges), `ReciprocalDivergence` (`∑_k 1/seq k` diverges) — and
proves `MC → WM`, `MissingFinite → WM`, `WM → RD`. Every theorem there is downstream of
MC; the section had no unconditional content.

**The finding.** The whole family rests on one elementary anatomy statement. On the
perpetual-primality branch `seq (n+1) = prod n + 1`, and the accumulator already grows
geometrically for trivial reasons (`two_pow_le_prod : 2^(n+1) ≤ prod n`, unconditional),
so `∑ 1/seq k` converges by comparison with `∑ 2⁻ⁿ`. That is `¬ RD`, and `wm_implies_rd`
propagates it up: `¬ WM`, `¬ MissingFinite`. Contrapositively:

    RD → (C∞),  WM → (C∞),  MissingFinite → (C∞),  MC → (C∞)

where (C∞) = `AutonomousBranch.InfinitelyManyComposite` — `prod n + 1` composite
infinitely often — which is **open**.

Note what is *not* used. `AutonomousBranch` already derives `¬MC` on this branch via
Bertrand (`eventually_prime_implies_not_mullin`) and the density-1/2 failure via `Φ₃`
having no root mod `q ≡ 2 (mod 3)`. Neither is needed: geometric growth alone kills the
reciprocal-sum statements, which sit far below MC. So
`mullin_implies_infinitelyManyComposite` is recovered from a strictly weaker hypothesis
by a strictly more elementary route.

**Consequence.** No smallness statement about the missing set is accessible without
first settling (C∞), and (C∞) is not about the distribution of primes — it is about the
anatomy of the numbers `prod n + 1`. The family does not route around the anatomy axis
of `EM/Meta/BagInformation.lean`; it lands on it.

**Also proved.** `sum_inv_primes_below_le_tsum` — every prime below the least missing
prime has been selected, so `∑_{p < min M} 1/p ≤ ∑' 1/seq k` whenever the latter
converges. The only unconditional quantitative link between the sequence's reciprocal
sum and the location of the first gap; it runs opposite to `wm_implies_rd`.


### 2026-08-16 — Paper: growth vs capture, Sylvester, and the target ladder

No Lean change. `variants_landscape.tex` +~130 lines; PDF 150 → 151 pages,
`check_lean_refs` 659/0, zero undefined references.

- Selection-rule table gains a row: *every factor (Sylvester)* — **False**,
  "autonomous closure".
- **Growth against capture.** New paragraph with the computation:
  `P_{n+1} = P_n·rad(P_n+1) = P_n(P_n+1)` for squarefree Euclid numbers, i.e.
  Sylvester's sequence; the walk closes into `w ↦ w²+w`; death needs `w²+w+1 = 0`,
  which has no root when `q ≡ 2 mod 3`. So take-all provably misses half the primes
  (numerically ~92% below 400). Ordering the rules by growth rate gives the *same*
  order as ordering them by how badly they fail — the far end of the
  greedy-for-slow-growth analysis in §bag.
- **New §target-ladder.** Definition of (V), the five-rung table
  (HH / SingleHit / MC / V / GenMixedMC(2)) with what each asks of the walk, and the
  matching hypothesis ladder (one window per prime versus a window past every stage).
- An `aside` records the honest measurement: **(V) is weaker than MC only by a finite
  prefix.** Past the sieve gap a hit forces capture, so MC and (V) differ only on
  hits before the gap — at most `π(q)`, each shielded by a distinct smaller prime.
  Widening capture buys a finite prefix per prime, not a different problem: the
  bottleneck was never selection, which is free past the gap, but hitting.

### 2026-08-16 — The weakest orbit target (V), and the four-rung ladder

`EM/Equidist/WeakHitting.lean` (NEW). Registry 172 → 175 published, open points
33 → 35. Build 3852 jobs, 0 warnings, 0 errors; `check_lean_refs` 655/0.

Prompted by an author question: keep the `minFac` accumulator but count a prime as
captured as soon as it *divides* a Euclid number, rather than requiring it to be the
factor selected.

- **`EveryPrimeDividesEuclid`** (V) — `∀ odd prime q, ∃ n, q ∣ prod n + 1`; equal to
  `HittingSet q ≠ ∅` (`everyPrimeDividesEuclid_iff_hittingSet`). The oddness is
  forced: `Pₙ` is even, so `2` divides no Euclid number.
- **`weak_hitting_ladder`** — `HH ⟹ MC ⟹ (V) ⟹ (−1 ∈ reachableEver q 2)`. The
  repo already had rungs 1, 2 and 4; **(V) was the missing third**. `HH` asks for
  cofinally many hits, `MC` for a hit where `q` is minimal, `(V)` for one hit ever.
- **`OneWindowGain`** + `oneWindowGain_implies_V` — the matching weakest Fourier
  criterion: one window, anywhere, per prime. No cofinality, no first-missing-prime
  bootstrap. `windowFourierGain_implies_oneWindowGain` records that
  `OneHorizon.WindowFourierGain` is strictly stronger.

**Why this weakening and not the obvious one.** Taking *all* factors (the natural
"be generous" move) gives `Pₙ₊₁ = Pₙ · rad(Pₙ+1)`, which for squarefree Euclid
numbers is `Pₙ(Pₙ+1)` — Sylvester's sequence. The walk closes into the autonomous
map `w ↦ w²+w`, death needs `w²+w+1 = 0`, and that has no root when `q ≡ 2 mod 3`:
the variant **provably misses half of all primes** (empirically ~92% below 400).
Generous capture bought at the cost of fast growth is a net loss. (V) keeps the
slow-growth accumulator and only widens what counts as success.

**Honest limit, stated in the file.** (V) changes the notion of success, not the
object — the same single orbit must still hit `−1`, so Dead End #90 applies
verbatim and generation-is-not-coverage (#20/#130) still blocks. Empirically the
gain is real but concentrated on easy primes: after seven steps the generous rule
has `139, 443, 248867` ahead of the min rule, while `19, 23, 29, 31, 37, 41` divide
none of the first thirteen Euclid numbers.

### 2026-08-16 — Build warnings cleared (zero warnings, zero errors)

All six were in code written this session. Two were silencing candidates that
turned out to be real superfluous hypotheses, so they were removed rather than
underscored — each theorem is now strictly more general:

- `MinFac Shifted.minFac_two_mul_add_one_eq_three_iff` no longer takes `1 ≤ n`.
  `omega` had been deriving `2n+1 ≠ 1` from `3 ∣ 2n+1`, not from the hypothesis.
  The statement holds at `n = 0` too: `minFac 1 = 1 ≠ 3` and `(0 : ZMod 3) ≠ 1`,
  so both sides are false.
- `OneHorizon.multipliers_exceed` and `rough_at_missing` no longer take
  `Nat.Prime q`. Primality of `q` was never used: `hbelow` quantifies over primes
  below `q`, and the multiplier's own primality comes from `seq_isPrime`.

The other four were cosmetic: two named binders in a `∀` statement that the
statement body does not mention (`windowFourierGain_hits`, now arrows), and two
`simpa … using` where `simp` alone closes the goal.

Call sites updated in `minFacShifted_landscape` and `bag_information_landscape`.
`lake build`: 3851 jobs, **0 warnings, 0 errors**. `check_lean_refs` 655/0, PDF 150
pages, paper unaffected (no cited name changed).

### 2026-08-16 — The bag-information assembly

`EM/Meta/BagInformation.lean` (NEW) + `the_bag_structure.tex`
§bag-information. Registry 171 → 172 published, 134 → 135 proved. PDF 149 → 150
pages, `check_lean_refs` 655/0.

**`bag_information_landscape`** — six clauses answering "does the next prime have
anything to do with the bag?":

*Three senses in which it does not.* `crt_multiplier_invariance_finset` (the
multiplier ignores any finite death-free coordinate set); `free_transition` (every
unit one transition away, so no residue datum predicts it);
`no_congruence_induction_proof` + `no_reciprocity_induction_proof` (no invariant of
the killed classes blocks).

*Two senses in which it does — and these are the problem.* New:
`seq_not_dvd_prod_succ`, the orthogonal-bag property in Lean (no collected prime
divides the next Euclid number — Euclid's argument, a permanent dependence); and
`multipliers_exceed` (past the gap, every multiplier exceeds `q`).

*One clause that exists only to block a misreading.*
`tendsto_minFacThree_density` — half the correct-parity ensemble has first
multiplier exactly `3`. Independence is not uniformity, and any reading of the
first three clauses as "the next prime is random" is refuted, not merely unproved.

The honest summary the file and section both give: **not "nothing to do with" but
"nothing beyond the exclusion and the roughness it forces"** — and that conditional
independence, stated distributionally, is exactly CME. The intuition sharpened is
not adjacent to the conjecture; it is the conjecture.

Both the file docstring and the paper subsection carry the two-axis scope warning:
these results concern congruence *state* and guard-weakened *obligations*; an
invariant whose state records anatomy is a different object and is covered by none
of them.

### 2026-08-16 — Coordinate blindness generalized; smoothness axis closed

Registry 168 → 171 published, 131 → 134 proved. Build green, `check_lean_refs`
650/0, PDF 149 pp with zero undefined references.

**`MullinCRT.crt_multiplier_invariance_finset`.** The multiplier is blind not to
one coordinate but to *any finite death-free set*: if `P ≡ P'` outside a finite
`T` and no prime of `T` divides either candidate, the least prime factors agree.
The generalization is free — `m = minFac(P+1)` divides `P+1`, so `m ∉ T`, so the
congruence transfers. The one-prime version is now derived as the singleton case,
so there is one proof rather than two.

**`no_smooth_graded_induction_proof` — the smoothness axis closes.** For a missing
prime, an odd modulus, and *any* admissible growing guard `y(n)`, the fragment is
empty. The mechanism is an order-of-quantifiers point: by
`exists_recurrent_residue` the orbit returns to some residue mod `m'` cofinally
often, and the candidates' defining conditions mention the stage *only* through
that residue — so the candidates may be chosen **first** and the stage
**afterwards**. Once fixed they are two specific naturals; `eventually_rough` then
forces `y(n)` above their largest prime factor at all late stages. No bound
*formula* for the candidates is needed, which removed the finiteness bookkeeping
budgeted for. `guard_analysis_complete` assembles it.

**A distinction the write-up now makes explicit.** There are two widening axes and
only one is closed:
- *Obligations (guards)* — which candidates the clauses must handle. Size, ω,
  smoothness: all free. **Closed.**
- *State (enrichment)* — what the invariant may track. Congruence mod `m` and mod
  the growing `Πₙ`: killed. An invariant whose state records **anatomy** (`ω`,
  `P⁺`) is a different object and is **not** covered.

An earlier draft of this entry said "no invariant-induction proof can establish an
omission". That is too strong and has been corrected throughout.

**Paper.** Third pass on this passage, as predicted. Corrected: both frontierboxes
in `the_min_max_dichotomy.tex`, the abstract, the Organization paragraph, the
section roadmap, and the bag-structure claim that "the surviving axis is smoothness
rather than anything else". The closing statement is now the two-axis version, with
the residue named as anatomical *state* — cross-referenced to the eventually-prime
branch, which is the live min-side example, and to Cox–van der Poorten, which is
the max-side one. Two superseded expectations (ω survives; growing smoothness
survives) are recorded as such rather than silently dropped.

### 2026-08-16 — Paper: items 1–4 written up

No Lean change. PDF 147 → 148 pages; `check_lean_refs` 646/0; zero undefined
references.

**The correctness fix that mattered.** The reciprocity-frontier subsection of
`the_min_max_dichotomy.tex` stated the result as a `conjecture` marked *not
formalized*, with a `proof` marked *Sketch, not machine-verified*. It is now a
`theorem` citing `no_reciprocity_induction_proof`, with the actual proof route
replacing the sketch.

Worth recording: the formalized proof is **not** the sketched one. The sketch ran
through `char_non_constancy` (finite vs cofinite factor support); the formal proof
runs through fullness at the growing modulus `Πₙ`. Both are now stated — the lemma
is labelled as the conceptual account of *why* the max argument cannot transfer,
not as the engine of the proof. The section also explains why the formalization was
tractable: (R1)/`symbolModulus_spec` lets the fragment be first-order (a predicate
closed under congruence mod `Πₙ`) instead of a tuple of symbol coordinates with a
realisability side condition.

**The proof-fragment subsection.** The `frontierbox` claiming smoothness as the
surviving axis is replaced by a `keyresult` (`fragment_analysis_complete`:
below-guards free, above-guard inadmissible) plus a `frontierbox` naming the actual
residue — a *growing* smoothness guard, admissible only under an unproven anatomy
statement. Also corrects the earlier "anatomy survives" expectation as too
pessimistic.

**`why_its_hard.tex`.** Added "Exhibit one horizon" to the Paths-to-MC box
(`covers_of_charSum_lt`, `windowFourierGain_implies_mc`), followed by two paragraphs
whose honesty matters: the caveat that the criterion is weaker globally but
*stronger per character* by a factor `q`, giving the `O(q²)` coverage target without
lowering the barrier; and "The one unconditional constraint at a missing prime"
(`multipliers_exceed`, `rough_at_missing`) with the negative scoping verdict — it
confines the orbit to a positive-density set forever, and nothing forbids that.

Abstract, Organization and the section roadmap updated. Codebase table has rows for
both new files.

### 2026-08-15 — Items 1–4: the obstruction programme closed (Session 307)

Four campaigns, ~900 lines. Standard axioms throughout. Registry 161 → 168
published, 125 → 131 proved. Full build green, `check_lean_refs` 634/0.

**1. The smoothness axis closed** (`Obstruction/{NoInvariant,Fragment}.lean`).
`CvdP.eventually_rough` — the Euclid numbers are eventually `y`-rough for every
`y`, from `no_finite_prime_covering`. Hence `CvdP.smooth_guard_inadmissible`: no
fixed smoothness threshold is admissible, because the guard excludes the orbit's
own candidates. `SmoothGuardedInductionProof` + `smooth_fragment_never_sound` +
**`fragment_analysis_complete`** — below-guards (stage, size, ω) are free and the
fragment stays empty; the above-guard is unusable. Fixed-threshold guards are
now settled in both directions.

**2. The reciprocity frontier proved** (`Reciprocity/NoReciprocityInvariant.lean`,
NEW ~330 lines). **`no_reciprocity_induction_proof`** — no propagating invariant
closed under congruence mod the growing symbol modulus `Πₙ = 8·m·Pₙ` blocks a
missing prime. Plus `reciprocity_provability_iff` and
`reciprocity_no_invariant_landscape`. This is the EXTENDS verdict of
`docs/analysis/reciprocity_invariants.md` as a theorem, and Dead End #144's
witness.

Route taken, cheaper than the blueprint's items 4–9: (R1) `symbolModulus_spec`
already says symbol data is determined by `π mod Πₙ`, so the fragment is stated
*without dependent types* — the invariant is a predicate on accumulators closed
under congruence mod `Πₙ`. Eviction is then automatic (`Πₙ` contains `8` and
`Pₙ`, so the Euclid unit law and mod-4 law are consequences of the class, not
hypotheses); fullness is `free_transition_large` **at `Πₙ`**, since
`free_transition` was proved for an arbitrary modulus; the CRT unit lifts along
`ZMod.unitsMap_surjective`. The blueprint's flagged risks (realisability,
variable-length CRT) do not arise.

**3. The one-horizon Fourier criterion** (`Equidist/OneHorizon.lean`, NEW).
`covers_of_charSum_lt` — if `∑_{χ≠1} ‖∑_{n<N} χ(w n)‖ < N` then the walk covers
every unit before `N`. `WindowFourierGain` (new open point),
`windowFourierGain_implies_mc`. Docstring states the honest comparison: weaker
globally (one horizon), **stronger per character** (factor `1/q`), and for
square-root cancellation it bites at `N ≳ q²` — the "cover within `O(q²)` steps"
target. Explicitly does *not* lower the barrier.

**4. The multiplier constraint** (`Equidist/OneHorizon.lean` +
`tmp/scoping_multiplier_constraint_2026-08-15.md`). `multipliers_exceed` /
`rough_at_missing`: past the sieve gap every multiplier is a prime `> q` and
`Pₙ + 1` is `q`-rough. Unconditional, non-distributional. Scoping pass came back
**negative** — three angles tried, all convert the combinatorial constraint into
a distributional one and die at #90/#152. Formalized anyway: it is the cleanest
statement of what a missing prime costs the orbit, and the starting hypothesis
for any anatomy argument.

**Where this leaves the programme.** Congruence, graded, size-, ω-guarded,
fixed-smoothness and reciprocity fragments are all closed. What survives is a
*growing* smoothness guard, admissible only under an unproven anatomy statement
about `P⁺(Pₙ+1)` — and in the tight regime that is the autonomous branch, where
MC is false anyway. Net: **any proof that a prime is omitted must first
establish an unproven anatomy property of the Euclid numbers.**

### 2026-08-15 — Tropical detour assessed: negative (Session 307)

No Lean change. `check_lean_refs` 633/0; PDF 147 pp, zero undefined refs.

Author asked whether minFac's `min`-structure opens a tropical-geometry route.
**Verdict: no**, and the earlier "tropical invariant" phrasing in `sec:minfac`
was wrong and has been corrected.

- **The phrasing.** The genuine tropicalization of `ℤ` is `n ↦ (v_p(n))_p`,
  sending `×` to `+` (tropical multiplication); `min` is tropical *addition*.
  `minFac` sends `×` to `min` — the wrong slot — and its minimum runs over `ℙ`
  ordered by archimedean size, not over valuation values. It is a homomorphism
  of idempotent semilattices, not a valuation.
- **The obstruction (new `rem:tropical`).** The only general tool is the
  ultrametric inequality with its equality case. At `a = P`, `b = 1`: for
  `r ∈ S_n`, `v_r(P) ≥ 1 ≠ 0` fires the equality case and gives
  `v_r(P+1) = 0` — *exactly Euclid's coprimality*. For `r ∉ S_n`,
  `v_r(P) = 0 = v_r(1)`, the equality case does not fire, and the inequality
  gives `≥ 0`, vacuous. But `r ∉ S_n` is precisely the candidate new primes.
  So the valuation calculus reproduces Euclid and is silent exactly where the
  conjecture lives.
- **Structural, not a ℤ artifact.** Over `𝔽_p[t]` the degree valuation is
  honest and `ffProdPlusOne_natDegree` (already proved) says
  `deg(ffProd n + 1) = deg(ffProd n)`: tropicalization of the FF-EM step is the
  identity on the only tropical coordinate.
- **No variety.** Tropical geometry proper needs a family over a valued field;
  MC is one orbit of a non-algebraic map. Passing to a family is #90.
- Distinct from #128, which rules out p-adic *geometry* (perfectoid, diamonds,
  Hecke) on the different ground of needing a fixed algebraic correspondence.

**Offered, not yet done:** formalize this as a *valuation enrichment* in the
obstruction calculus — State = trackable valuation data, Trans = everything the
ultrametric inequality permits. By the above the relation is maximally
permissive at unseen primes, so killability should follow from
`free_transition` almost immediately, converting the assessment into a theorem
and earning a catalogue entry beside #128.

### 2026-08-15 — Paper: the minFac analysis (Session 307, author remarks)

No Lean change. PDF 144 → 147 pages; `check_lean_refs` 632/0; two lualatex
passes, zero undefined references.

**Remark 1 — the starting point in §The Residue Walk.** Author's note was that
`s` should be a prime. Investigation: the section's own Tail Identification
theorem restarts from `Prod_s(M)`, a product of many primes, and the Lean
hypotheses are `1 ≤ n` for `genSeq_prime` but `Squarefree n` for
`genSeq_injective` / `genProd_squarefree` — so a blanket "s prime" would make
the tail identity unstatable. Resolved with the author (option: keep `s ≥ 2`,
add a distinction): new `rem:two-generalizations` separating (i) `s` prime —
the faithful generalization, the motivating object of §§4–5 — from (ii) `s`
squarefree — the bag, the ensemble setting — and noting the tail identity
*forces* (ii).

**Remark 2 — what it means to be the least prime factor.** The paper had two
heuristic paragraphs on minFac, both about *growth*. New subsection
`sec:minfac` in `the_bag_structure.tex` (+~180 lines), absorbing them as items
6–7, with the arithmetic added:

1. `minFac(nm) = min(minFac n, minFac m)` with no coprimality — minFac is a
   homomorphism onto `(ℙ, min)`; the `+1` is exactly what breaks it.
2. "minFac N = q" ⟺ `q ∣ N` and `N` is `q`-rough: an open congruence
   condition of density `~ e^{-γ}/(q log q)`. `minFac ≤ y` is decided by
   `N mod ∏_{p≤y} p` — which is *why* forcing states exist and the
   No-Invariant theorem has bite, and simultaneously why it is only a no-go.
3. What minFac discards is the **large** part (cofinite support); maxFac
   discards the small part (finite support). That single dichotomy is
   `char_non_constancy`, the min/max asymmetry, and the smoothness boundary.
4. Distribution: Buchstab/`sieveDensity` for shifted squarefree; the
   correct-parity weights `w_ℓ` with `w₃ = 1/2` proved; tail `≍ 1/log y` so
   `E[log minFac]` diverges — small-biased *and* heavy-tailed at once, which is
   the empirical signature (`a(7) = 6221671`, 41 absent in 51 terms).
5. Not multiplicative, no Euler product — Halász / LSD unavailable by *type*
   mismatch (Dead Ends #109, #154); the sieve is the only handle, and it sees
   minFac through roughness.
6–7. The existing greedy-growth and 0-accessibility material, renumbered.

Closes with a seven-row min/max comparison table, and the observation that
rows 2 and 3 pull opposite ways: minFac is the *more visible* rule (capture is
congruential — hence the no-go theorems) and the *less constrained* one (what
it discards is unbounded).

### 2026-08-15 — Paper: obstruction calculus + proof fragment written up (Session 307)

No Lean change. `paper/` +374 lines; PDF 138 → 144 pages, `check_lean_refs`
623/0, two lualatex passes, zero undefined references.

**Corrections first.** `abstract.tex` and `why_its_hard.tex` still carried
**138 dead ends / 13 witnessed / 8 revivable** in five places — stale by several
sessions, not just this one. Now 159 / 27 / 10. Two historical alias bugs fixed:
`variants_ensemble_weak.tex` and `the_ensemble_reduction.tex:609` attributed the
AEP falsity to #138 (it is #137); the appendix had it right, and
`the_ensemble_reduction.tex:101` already said #137, so the file was internally
inconsistent.

**The gap that was found.** Five Lean files totalling 3,111 lines had no prose at
all — only auto-generated codebase-table rows: `Obstruction/Calculus.lean` (657),
`Obstruction/Fragment.lean` (850), `IK/DirichletDensity.lean` Parts 9–10,
`Meta/OrbitBarrier.lean` (309), `Ensemble/MinFacShifted.lean` (240). The first two
predate this session: `the_min_max_dichotomy.tex` covered `NoInvariant.lean` and
`MaxVariant.lean` in 776 lines and then stopped, so the abstraction and the
proof-theoretic upgrade were invisible to a reader.

**Written.**
- `the_min_max_dichotomy.tex` §§5.5–5.6 (+284 lines): the obstruction calculus
  (Enrichment / Certificate / Killable / Emptiness Theorem; the abstraction test
  recovering the No-Invariant Theorem; max provably *not* killable — derived, not
  asserted; refinement; graded certificates and one-step killability; the
  TraceComplete ≡ MC honesty remark) and the proof-theoretic dichotomy (the
  fragment, soundness, proof mining, unprovability, Euclid's argument as the
  inhabitant for appeared primes, **provability decides appearance**, the max-side
  control, the three-axis widening, and a `frontierbox` stating that smoothness —
  not anatomy — is what survives).
- `why_its_hard.tex` (+72): "The two fundamental barriers, witnessed" — the
  `(ZMod 5)ˣ` counterexamples for #90 and #117, the generation-vs-coverage corollary,
  and `integer_orbit_barrier_thesis` as the assembly.
- Roadmap, section opener, `introduction.tex` Organization, and the abstract updated
  to give the no-go content proportionate space.

**Still uncovered** (deliberately deferred): `MinFacShifted.lean` and
`DirichletDensity.lean` Parts 9–10 belong in `the_ensemble_reduction.tex` beside the
#157 material. Also open: moving `the_min_max_dichotomy` before the five
variants/FF sections so the MC-proper spine is contiguous — touches cross-references,
so left as a separate decision.

### 2026-08-15 — The ω guard is free; smoothness is the boundary (Session 307)

`EM/Obstruction/{NoInvariant,Fragment}.lean` (+~230 lines). Standard axioms.
Registry 159 → 161 published, 123 → 125 proved.

This was the check flagged before committing to Extension B, and it came out
**positive** — the blueprint's boundary claim was too pessimistic.

- **`CvdP.exists_class_omega`** — the enabling lemma. Multiplying by a prime
  `p ≡ 1 (mod m)` taken above the current value changes **neither the residue
  class nor the least prime factor**, while raising `ω` by one. Iterating pushes
  `ω` arbitrarily high without disturbing anything the congruence machinery sees.
  (This is much cheaper than the "build `N = π·M₁⋯M_k` from scratch" route in
  `tmp/scoping_obstruction_extension_2026-08-15.md`.)
- `CvdP.free_transition_omega`, `CvdP.exists_large_odd_in_class_omega` — the two
  candidate-producing lemmas, now meeting a size guard *and* an ω guard.
- **`no_omega_graded_induction_proof`** — the fragment is still empty when the
  proof may additionally assume the candidate has as many distinct prime factors
  as the Euclid number actually has (`K n ≤ ω(prod n + 1)`).
- `omega_graded_provability_iff`; `graded_proof_theoretic_dichotomy` extended to
  eight clauses; `no_graded_induction_proof` re-derived as the `K ≡ 0` case, so
  the argument exists in one copy.

**Consequence for the programme.** `ω` is *not* the surviving part of anatomy.
The blueprint (`docs/analysis/reciprocity_invariants.md` §6) listed anatomy
wholesale as unkilled, on the grounds that fullness uses `N = π·M` with `ω = 2`.
That is now refuted. What survives is the **opposite** direction: every
construction produces candidates with huge prime cofactors, so a fragment
demanding `y`-smoothness, or bounding the largest prime factor, is never
reached. Smoothness — precisely the max-side ingredient, since `maxFac N = q`
*is* a smoothness condition — is the boundary.

Written into `Fragment.lean`'s "Scope, honestly" section, which now names
smoothness rather than anatomy.

### 2026-08-15 — Extension A: graded + size-guarded fragments (Session 307)

`EM/Obstruction/{NoInvariant,Calculus,Fragment}.lean` (+~330 lines). Standard
axioms. Registry 156 → 159 published, 120 → 123 proved.

`Fragment.lean`'s "Scope, honestly" disclaimed three things the fragment did not
cover. **Two of them are now dead.**

- `GradedInductionProof q m B` — the invariant may depend on the step index, and
  the step/avoid clauses need only hold for candidates `N ≥ B n`. Admissible
  guards are `B n ≤ prod n + 1`, i.e. up to the size of the actual Euclid number
  (beyond that the fragment excludes the orbit's own candidate and is unsound).
- **`no_graded_induction_proof`** (CA 4642a48e) — still empty for every missing
  prime, at every odd modulus, with no richness hypothesis.
- **`graded_provability_iff`** (CA c874aa5a) — provability still decides
  appearance after both relaxations.
- `graded_proof_theoretic_dichotomy` — the four clauses in one statement.
- `no_congruence_induction_proof_of_graded` — coherence: the widened theorem
  subsumes the Part-2 original.

Why each relaxation dies:
- **Time-dependence**: `congruence_killable`'s witness is a *single* transition.
  Recorded as `congruence_killableIn : KillableIn`, and `no_graded_certificate`
  is the calculus-level statement (graded certificates, `ReachesIn`,
  `Certificate.toGraded`).
- **Size guards**: `free_transition_large` and `exists_large_odd_in_class` give
  candidates above any bound — Dirichlet supplies arbitrarily large primes, so an
  archimedean *lower* bound is free.

Refactor: `congruence_reaches_forcing` extracted from `congruence_killable` (the
CRT/forcing core, stated without committing to how the transition is realized);
`congruence_killable` and the fragment proof now share it.

**Boundary, unchanged and now stated in the file**: an *upper* bound on the
candidate, smoothness, or largest-prime-factor control is NOT covered — both
constructions produce huge prime cofactors. That is the max-side ingredient of
Cox–van der Poorten and the anatomy facet of Dead End #146. Next fragment is
reciprocity (Extension B), per `tmp/scoping_obstruction_extension_2026-08-15.md`.

Also registered `Obstruction.proof_theoretic_dichotomy` (Session 298), which was
proved but never in the registry.

### 2026-08-15 — The orbit-specificity barrier, witnessed (Session 307)

`EM/Meta/OrbitBarrier.lean` (NEW, ~300 lines). Standard axioms.
Registry 153 → 156 published, 118 → 120 proved.
**Dead-end counts 159 / 25 / 10 → 159 / 27 / 10.**

Dead Ends #90 and #117 carry the entire "why MC is hard" thesis and were the
only *fundamental* entries with `—` in the witness column — every machine-checked
dead end was a peripheral one. Both are now witnessed, by finite computations in
`(ZMod 5)ˣ` built from two periodic multiplier sequences:

- `mulA` = period `(2,2,3,3)`, walk `1,2,4,2,1,…` — **hits** the death class `4 = -1`;
- `mulB` = period `(2,3,2,3)`, walk `1,2,1,2,…` — provably **never** hits it.

`mulB` is a rearrangement of `mulA`: `block_counts_agree` shows both use each
multiplier value equally often in *every* window of four steps. Same population
statistics, opposite hitting behaviour.

- **`population_does_not_determine_hitting`** (CA 8327dd1a) — Dead End #90.
  Both sequences are prime-valued at every step.
- **`mult_cancel_not_walk_cancel`** (CA 41094226) — Dead End #117. With `chi5`
  the order-4 character (`χ(2) = i`, so `χ(3) = -i`): multiplier sums bounded by
  `1` for all `K`, walk sums `≥ M` after `2M` steps. `chi5` carries exactly the
  side conditions of the repo's own `MultCancelToWalkCancel` (`normSq ≤ 1`,
  `χ 0 = 0`, orthogonality), so #117 is not an artifact of a weak hypothesis.
- `multipliers_generate` — `{2,3}` generates `(ZMod 5)ˣ` yet the walk visits only
  `{1,2}`: #20/#130 in multiplicative form. SubgroupEscape cannot close the gap.
- **`integer_orbit_barrier_thesis`** (CA c1ea5ac3) — the assembly, mirroring
  `FunctionFieldAnalog.orbit_barrier_thesis`, which the FF side had and the integer
  side did not. Clauses (1)–(3) the proved sufficient reductions (`HH → MC`,
  `DH → MC`, `CME → MC`), (4)–(5) the proved free structural inputs
  (`walkZ = -1 ↔ q ∣ prod n + 1`, `PrimeResidueEscape`), (6)–(8) the three
  witnesses. The gap between (4)–(5) and (6)–(8) is the barrier.

`Meta/DeadEnds.lean` updated: #90 and #117 witness columns filled, MC-proper
ledger consequence (i) rewritten from "largest structural gap" to closed.

### 2026-08-15 — First multiplier at the correct parity (Session 307, tier 1)

`EM/Ensemble/MinFacShifted.lean` (NEW, ~215 lines) + `IK/DirichletDensity.lean`
Part 10. Standard axioms. Registry 148 → 153 published, 113 → 118 proved.

Dead End #157 refutes `EnsembleMultiplierEquidist` over all squarefree `n` by a
**parity artifact** (half the `n` are odd, so `genSeq n 0 = 2`). The real EM
accumulator is always even, so one might hope the defect is an artifact of the
wrong ensemble. It is not.

- `minFac_two_mul_add_one_eq_three_iff` (CA 77717487) — arithmetic core, no
  analysis: for `n ≥ 1`, `minFac (2n+1) = 3 ↔ n ≡ 1 (mod 3)`.
- **`tendsto_minFacThree_density`** (CA 4c96fbc7) — on the smallest correct-parity
  family (starts `2p`, `p` prime, `ω = 2`), the Dirichlet density of
  `{p : minFac (2p+1) = 3}` is **exactly 1/2**.
- `first_multiplier_not_equidistributed` (CA 269502d3) — for every *prime* modulus
  `Q ≥ 5`, the class of `3` carries density `≥ 1/2 > 1/(Q-1) = 1/φ(Q)`. Primality is
  load-bearing, not cosmetic: `φ(6) = 2` and the numbers would not separate.
- `minFacThree_absorbed` — walk reading: `3 ∣ genProd (2p) 1`, i.e. half this
  ensemble is absorbed mod 3 at the *first* step (Dead End #137's mechanism, now
  with a density attached).

Part 10 of `DirichletDensity.lean` adds the modulus-free denominator
`primeZetaSum σ = ∑_p p^{-σ}` (`tendsto_unitPrimeSum_div_primeZetaSum`: the two
normalizations have ratio → 1), without which densities at different moduli — the
condition read mod 3 against a class read mod `Q` — cannot be compared.

Verified numerically before committing: zero counterexamples to the arithmetic core
over the 33,860 primes below 4·10⁵, empirical density 0.4989 against the proved 1/2.
The same check confirms the tier-2 weights `w_ℓ` at `ℓ = 5,7,11,13` to three digits.

**Still Dirichlet density, not natural density**, and still an ensemble statement —
it does not cross Dead End #90 (see the file's "Scope, honestly" section).
Dead End #157's entry in `Meta/DeadEnds.lean` updated to record this.

### 2026-08-15 — Dirichlet **density** (Session 307, tier 0)

`EM/IK/DirichletDensity.lean` Part 9 (+~200 lines). Standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). Registry 146 → 148 published,
111 → 113 proved.

The file previously extracted only *divergence* from its three inputs. Part 9
extracts the **ratio**:

- `tendsto_classPrimeSum_div_unitPrimeSum` (CA 7e757314) — for `q ≥ 2` and an
  invertible class `a`, `(∑_{p ≡ a} p^{-σ}) / (∑_{p ∤ q} p^{-σ}) → 1/φ(q)` as
  `σ → 1⁺`.
- `tendsto_setPrimeSum_div_unitPrimeSum` (CA f1cf9baa) — `|A|/φ(q)` for a
  `Finset` of invertible classes. **This is the consumable form**: a congruence
  condition unfolds by CRT into membership of a fixed `Finset` of unit classes.
- `tendsto_unitPrimeSum_atTop` — the only genuinely new ingredient:
  `unitPrimeSum q` is antitone in `σ` (`unitPrimeSum_antitone`), which upgrades
  `exists_lt_unitPrimeSum` (large *somewhere* on `(1,2]`) to a limit.
- `exists_nonprincipal_bound` — two-sided uniform error bound
  `|φ(q)·∑_{p ≡ a} p^{-σ} − ∑_{p ∤ q} p^{-σ}| ≤ Mtot` on `(1,2]`, uniform in the
  class.
- `re_charSum_split` — extracted from `re_charSum_ge` (which now uses it), so the
  two-sided estimate shares the principal/non-principal split.
- `tendsto_classPrimeSum_atTop` — coherence check: the density statement subsumes
  the file's previous headline.

**Honesty**: this is *Dirichlet* density, not natural density. `π(x;q,a) ~ π(x)/φ(q)`
needs PNT in APs — Mathlib lacks it, and the repo carries it as the open
`IK.WeightedPNTinAP`, recorded infeasible from existing infrastructure in Session 156.
Stated in the docstring and in the Registry comment.

Scoping for what this was built for: `tmp/scoping_minfac_shifted_2026-08-15.md`
(tiers 1–2, the `minFac(2·q₁⋯q_k + 1)` distribution). Tier 0 is standalone
infrastructure and a plausible Mathlib candidate.

### 2026-08-15 — `EM/Stochastic/RandomVariant.lean` (new, 1112 lines)

The random Euclid–Mullin process as a theorem in its own right. Standard axioms.

- **Selection kernels**: `IsKernel w` (non-negative, sums to 1 over prime
  factors of `P+1`), `LowerBounded w λ` (full support, `w P p ≥ λ/ω(P+1)`),
  `uniformKernel` (= `epsStepWeight 1`), `failWeightK w q m n`
  (`failWeight ε = failWeightK (epsStepWeight ε)`). Every theorem is for an
  arbitrary kernel — uniform, ε-mixture, or a min-skewed rule with full support.
- **Conjectures**: `CapturesAS w q m` (a.s. capture), `RandomMC q`,
  `RandomMullinConjecture`, `RandomMCFrom m q`.
- **Unconditional hierarchy** (any kernel): trapped ⟹ `failWeightK ≡ 1`
  (`failWeightK_eq_one_of_trapped`); a.s. ⟹ reachable
  (`capturesAS_implies_reachable`); `RandomMC q → PureRandomMC q`
  (`randomMC_implies_pureRandomMC`); reachable ⟹ eventually `< 1`
  (`failWeightK_lt_one_of_reachable`).
- **General engine**: `failWeightK_le_of_capture` (a first-capturing path of
  weight W forces `failWeightK ≤ 1 - W`), `failWeightK_add_le` (block
  composition), `failWeightK_le_prod_blocks`, **`capturesAS_of_blocks`**
  (block reachability `BlockCapture` + `∑ wt = ∞` ⟹ a.s.).
- **q = 3, any start coprime to 3, any lower-bounded kernel**:
  `three_capturesAS_of_omegaPair` from `OmegaPairLB m v`
  (`v j ≤ 1/(ω(P_{2j}+1)ω(P_{2j+1}+1))` along 3-avoiding walks) + divergence.
  Specialisations `three_random_almost_sure` (`RandomMC 3` conditional on
  anatomy), `three_random_almost_sure_from`, `three_eps_almost_sure_general`
  (mixture, `0 < ε ≤ 1`, no parity).
- **q = 2, any odd start**: `two_capturesAS_of_omega_odd` from `OmegaLB 2 m v`.

### 2026-08-15 — `EM/Stochastic/EpsilonDegeneration.lean` (new)

The `(1-ε)·minFac + ε·random` family and its deterministic limit. Standard axioms.

- `epsStepWeight_zero_minFac` / `epsStepWeight_one_eq_uniform` — the family's two
  endpoints are the two classical rules: `ε = 0` is minFac (point mass), `ε = 1`
  is the uniform random rule. One object, `failWeight ε q m N`, covers both.
- `failWeight_ge_one_sub_pow` — if the minFac walk avoids `q` for `N` steps then
  `(1-ε)^N ≤ failWeight ε q m N`: the deterministic orbit is itself a failing
  path, never negligible at finite horizon.
- **`mullin_capture_of_failWeight_bound`** — the ε → 0 transfer. A capture bound
  `failWeight ε q 2 N ≤ 1 - c` at a SINGLE `ε` with `N·ε < c` proves
  `∃ n, seq n = q`, i.e. Mullin's conjecture at `q`.
- `horizon_ge_of_minFacAvoids` — sharpness: outside the window (`N ≥ c/ε`) no
  such bound exists unless the conjecture already holds at `q`.
- `failWeight_ge_of_mullin_fails` — if `q` never occurs then
  `failWeight ε q 2 N ≥ (1-ε)^N` for every `ε`, `N`; since `(1-ε)^N → 0`, this is
  compatible with almost-sure capture at every fixed `ε > 0`. So a.s. capture for
  all `ε > 0` does NOT imply Mullin's conjecture.
- **`mullin_iff_exists_failWeight_bound`** — for `q ≠ 2`, Mullin's conjecture at
  `q` IS the existence of such an `(ε, N, c)`. The noisy family is a faithful
  reformulation, not a relaxation.

### 2026-08-15 — `EM/Stochastic/ThreeAlmostSure.lean` (new, 751 lines)

Almost-sure capture of `q = 3` by the `(1-ε)·minFac + ε·random` process,
conditional only on an anatomy hypothesis about `ω` of Euclid numbers.
All new declarations use the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

- `failWeight ε q m n` — the exact `ε`-process probability that the first
  `n` steps from accumulator `m` never select `q`, as a finite recursion
  over the exact kernel `epsStepWeight` (`EM/Stochastic/TransitionKernel.lean`)
  rather than the conservative lower bound `stepWeightLB`. Proved
  non-negative, `≤ 1`, and antitone in `n` (`failWeight_antitone`). This is
  the object the earlier "almost-sure" statements lacked: `pathWeightLB`
  lower-bounds ONE cylinder, whereas an a.s. statement needs an upper
  bound on ALL failing paths.
- `minFac_succ_eq_three` / `minFac_captures_three` / `epsStepWeight_three_ge`
  — unconditional parity lemmas: if `P` is even and `3 ∣ P+1` then
  `minFac(P+1) = 3`, so the deterministic branch takes a `3`-opportunity by
  itself at weight `≥ 1 - ε`, a cost independent of `ω`. Accumulators of the
  standard process are even, so this is free — and it is what reduces the
  required divergence from `Σ 1/(ω_k ω_{k+1})` to `Σ 1/ω_k`.
- `exists_three_opportunity_step` (added public to
  `EM/Stochastic/TreeSieveDecay.lean`) — from EVERY `P ≥ 2` coprime to `3`,
  either `3 ∣ P+1`, or some prime `f ∣ P+1`, `f ≠ 3`, has `3 ∣ P·f + 1`:
  uniform block depth 1, unconditional.
- `prod_one_sub_tendsto_zero` — `∏(1 - x_k) → 0` from `Σ x_k = ∞`; strict
  generalization of `product_failure_tendsto_zero`
  (`EM/Stochastic/GeometricCapture.lean`), which requires a uniform `δ`
  that cannot exist here.
- `three_almost_sure_capture_of_omega_divergence` /
  `three_almost_sure_capture_from_two` — the main theorems.

Net effect: for `q = 3` the reachability side (the entire content of
`Regeneration` and `TreeSieveDecay`) is discharged unconditionally; the only
remaining input is the anatomy hypothesis `OmegaBlockLB` + divergence.
