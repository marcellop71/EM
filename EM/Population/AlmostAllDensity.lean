import EM.Population.TypeBadSmall
import EM.ForMathlib.PeriodicDensity

/-!
# Almost all seeds capture `q` — the natural-density form

This file converts the one-period counting bound of Session 312 Part C
(`TypeBadSmall.type_bad_small`) into a statement about **natural density on `[1, X]`**:
for a fixed prime `q` and any `ε > 0` there is a horizon `n` beyond which, for all large
`X`, the seeds `m ≤ X` that are coprime to `q` and whose genuine greedy orbit fails to
select `q` in its first `n` steps number at most `ε · X`.

The truncation parameter `Y` — and with it the period `M_Y = SelectionLaw.modulus q Y` and
the exclusion-window constant `Cc` — has **disappeared from the statement**.  It survives
only inside the proof, as the period of the residue-class covering.

## Scope — read this before quoting the result

* **Population / density, not orbit.**  `almost_all_genmc_density` counts *seeds* `m` in
  `[1, X]`.  It says nothing whatsoever about the actual Euclid–Mullin orbit of the seed
  `2`, i.e. about the classical sequence `2, 3, 7, 43, 13, …`.  The orbit-specificity gap
  (dead ends #90 and #117) is **untouched**: no statement here specializes to a single
  seed, and no argument here transfers a positive-density conclusion to a fixed orbit.
* **One prime at a time.**  The prime `q` is *fixed* before `ε`, and the horizon `n` and
  the threshold `X₀` both depend on `q` and `ε`.  The simultaneous-in-`q` form — a single
  density-one set of seeds capturing *every* prime — is **OPEN** (§G).  Natural density is
  only finitely additive, so the per-`q` statements do **not** combine into a statement
  about the intersection over all `q`.
* **Finite horizon.**  For each `ε` there is a horizon `n(q, ε)`; no limit in `n` is taken.
  The result is a finite-horizon counting bound, not a capture theorem.
* **Unconditional.**  Every input is unconditional: no equidistribution hypothesis occurs
  anywhere in the chain `TheoremC.theorem_C → FiberTheoremC.theorem_C_fiber →
  TypeBadSmall.type_bad_small → almost_all_genmc_density`.

## Why the fibre form was needed

The Session-311 headline `AlmostAllGenMC.almost_all_genmc` bounds the uncaptured seeds
inside **one period** `sampleSpace q Y = [1, M_Y]`.  Two of the four clauses of
`TheoremC.GoodSeed` — namely `¬ q ∣ m` and `¬ ∃ j < n, genSeq m j = q` — are *not*
functions of the residue `m mod M_Y` (the modulus deliberately omits `q`, and the genuine
orbit sees the seed itself).  A bound on such a predicate inside one period is a
**diagonal** count: it constrains the pairs "(residue, seed)" only on the diagonal.
Natural density on `[1, X]`, by contrast, needs a **product** count: a set of admissible
residues, hit by every block of length `M_Y`.  The two disagree, and the transfer fails.

`FiberTheoremC.FiberGood` repairs exactly this.  It replaces the two seed-dependent clauses
by the *fibre existential* "some `m'` in the residue class of `m` is coprime to `q` and
uncaptured", which depends on `m` only through `m mod M_Y`.  With that replacement the bad
set is genuinely `M_Y`-periodic, and the generic block-counting lemma
`PeriodicDensity.eventually_density_le` applies verbatim.

## Finitely many primes at a time, and no further

`finite_simultaneous_density` is the strongest simultaneous statement natural density
supports.  It does *not* extend to all primes: natural density is only finitely additive,
so there is no Borel–Cantelli, and increasing sets of density `≤ δ` can have union of
density `1`.  Making the per-`q` failure fractions summable does not help — summability is
a hypothesis of a theorem about countably additive measures.  The simultaneous-in-`q` form
therefore needs a genuinely different ambient measure (see
`docs/analysis/simultaneous_in_q_scoping.md`); it is **OPEN**.

## Main results

* `uncaptured_in_few_classes` — the covering lemma: the uncaptured seeds coprime to `q`
  live in a set `T` of residue classes modulo a period `M` with `#T ≤ (ε/2) · M`.
* `almost_all_genmc_density` — the headline, in the `∀ X ≥ X₀` form.
* `almost_all_genmc_limsup` — the `limsup` restatement.
* `finite_simultaneous_density` — the finite-union form, uniform over a `Finset` of primes.

Session 312, WP-N Part D.
-/

noncomputable section
open Classical

namespace AlmostAllDensity

open SeedCapture SeedTypes LargeStepRoughness SelectionLaw LSPlus TailAssembly
open TheoremC TypeBadSmall

/-! ## 1. The covering lemma -/

/-- **The uncaptured seeds occupy few residue classes.**

For a fixed prime `q` and any `ε > 0` there is a horizon `n`, a period `M ≥ 1` and a set
`T` of residue classes modulo `M` with `#T ≤ (ε/2)·M`, such that *every* positive integer
`m` which is coprime to `q` and whose genuine orbit misses `q` before depth `n` has its
representative `PeriodicDensity.periodRep M m` in `T`.

This is the whole content of the density transfer.  `M` is `SelectionLaw.modulus q Y` and
`T` is the three-bad-type filter of `TypeBadSmall.type_bad_small`; the point is that each
of the three types is a function of the residue alone, the third one because
`FiberTheoremC.FiberGood` quantifies existentially over the residue fibre — and the seed
`m` itself is available as that witness. -/
theorem uncaptured_in_few_classes (q : ℕ) (hq : q.Prime) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n M : ℕ) (T : Finset ℕ), 1 ≤ M ∧ (T.card : ℝ) ≤ ε / 2 * (M : ℝ) ∧
      ∀ m, 1 ≤ m → (¬ q ∣ m ∧ ¬ ∃ j < n, genSeq m j = q) →
        PeriodicDensity.periodRep M m ∈ T := by
  classical
  obtain ⟨n, Y, Cc, hM, hT⟩ := TypeBadSmall.type_bad_small q hq (ε / 2) (by positivity)
  refine ⟨n, modulus q Y, (sampleSpace q Y).filter (fun m =>
      ¬ (∀ j < n + 1, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y)
      ∨ (1 : ℝ) / Cc ≤ ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter (fun r => r.Prime ∧ r ∣ m),
            (1 : ℝ) / r
      ∨ FiberTheoremC.FiberGood q Y Cc n m), hM, ?_, ?_⟩
  · -- the cardinality bound, with `#(sampleSpace q Y) = modulus q Y`
    rw [card_sampleSpace] at hT
    exact hT
  · -- the covering: the representative of an uncaptured seed is a bad type
    intro m hm1 ⟨hqm, hcap⟩
    set c : ℕ := PeriodicDensity.periodRep (modulus q Y) m with hc
    have hcmem : c ∈ sampleSpace q Y := PeriodicDensity.periodRep_mem_Ico hM
    have hcong : c ≡ m [MOD modulus q Y] := (PeriodicDensity.periodRep_modEq _ m).symm
    refine Finset.mem_filter.mpr ⟨hcmem, ?_⟩
    by_cases hnd : ∀ j < n + 1, 2 ≤ genSeqAvoid q c j ∧ genSeqAvoid q c j ≤ Y
    · by_cases hmass : (1 : ℝ) / Cc ≤
          ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter (fun r => r.Prime ∧ r ∣ c), (1 : ℝ) / r
      · exact Or.inr (Or.inl hmass)
      · exact Or.inr (Or.inr ⟨hnd, le_of_lt (not_le.mp hmass), m, hm1, hqm, hcong, hcap⟩)
    · exact Or.inl hnd

/-! ## 2. The headline -/

/-- **Almost all seeds capture `q` — the natural-density form.**

For a fixed prime `q` and any `ε > 0` there is a horizon `n` and a threshold `X₀` such that
for every `X ≥ X₀`, the seeds `m ∈ [1, X]` which are coprime to `q` and whose genuine
greedy orbit `genSeq m ·` does not select `q` in its first `n` steps number at most `ε · X`.

Note that the truncation `Y` of the one-period statements has been eliminated: it occurs
neither in the hypotheses nor in the conclusion.

*Proof.*  `uncaptured_in_few_classes` puts the uncaptured seeds into a set `T` of residue
classes modulo `M` with `#T ≤ (ε/2)·M`; `PeriodicDensity.eventually_density_le` converts a
residue-class covering of density `ε/2` into a density bound `ε` on `[1, X]`, the extra
factor `2` absorbing the incomplete final block.

**Scope.**  This is a statement about the seed ensemble, for one fixed prime, at a finite
horizon.  See the module docstring. -/
theorem almost_all_genmc_density (q : ℕ) (hq : q.Prime) {ε : ℝ} (hε : 0 < ε) :
    ∃ n X₀ : ℕ, ∀ X, X₀ ≤ X →
      (((Finset.Icc 1 X).filter (fun m => ¬ q ∣ m ∧ ¬ ∃ j < n, genSeq m j = q)).card : ℝ)
        ≤ ε * (X : ℝ) := by
  classical
  obtain ⟨n, M, T, hM, hTcard, hP⟩ := uncaptured_in_few_classes q hq hε
  obtain ⟨X₀, hX₀⟩ := PeriodicDensity.eventually_density_le hM T
    (fun m => ¬ q ∣ m ∧ ¬ ∃ j < n, genSeq m j = q) hP hε hTcard
  refine ⟨n, X₀, fun X hX => ?_⟩
  have h := hX₀ X hX
  convert h using 4

/-- **`limsup` restatement of the headline.**  The upper natural density of the seeds that
are coprime to `q` and miss `q` in the first `n` steps is at most `ε`.

Same scope caveats as `almost_all_genmc_density`: population, one fixed prime, finite
horizon, unconditional. -/
theorem almost_all_genmc_limsup (q : ℕ) (hq : q.Prime) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, Filter.limsup
      (fun X : ℕ => (((Finset.Icc 1 X).filter
          (fun m => ¬ q ∣ m ∧ ¬ ∃ j < n, genSeq m j = q)).card : ℝ) / (X : ℝ))
      Filter.atTop ≤ ε := by
  classical
  obtain ⟨n, M, T, hM, hTcard, hP⟩ := uncaptured_in_few_classes q hq hε
  refine ⟨n, ?_⟩
  have h := PeriodicDensity.limsup_density_le hM T
    (fun m => ¬ q ∣ m ∧ ¬ ∃ j < n, genSeq m j = q) hP hε hTcard
  convert h using 5

/-! ## 3. Finitely many primes at a time -/

/-- **The finite-union form.**  For any *finite* set `S` of primes and any `ε > 0` there is
a single horizon `n` and a single threshold `X₀` such that for all `X ≥ X₀` the seeds
`m ∈ [1, X]` failing to capture *some* `q ∈ S` before depth `n` number at most `ε · X`.

*Proof.*  Apply `almost_all_genmc_density` to each `q ∈ S` with the smaller tolerance
`ε / #S`, take `n` and `X₀` to be the suprema of the resulting horizons and thresholds
(the bad predicate is antitone in the horizon, so raising `n` only shrinks the bad set),
and sum the `#S` bounds.

**Scope.**  `S` is *finite*, and `n`, `X₀` depend on `S`.  This does **not** extend to all
primes: natural density is only finitely additive, so there is no Borel–Cantelli, and an
increasing union of sets of density `≤ δ` can have density `1`.  See the module
docstring — the simultaneous-in-`q` form is **OPEN**. -/
theorem finite_simultaneous_density (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ n X₀ : ℕ, ∀ X, X₀ ≤ X →
      (((Finset.Icc 1 X).filter
          (fun m => ∃ q ∈ S, ¬ q ∣ m ∧ ¬ ∃ j < n, genSeq m j = q)).card : ℝ)
        ≤ ε * (X : ℝ) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · -- no primes to capture: the bad set is empty
    refine ⟨0, 0, fun X _ => ?_⟩
    refine le_trans (le_of_eq ?_) (mul_nonneg hε.le (Nat.cast_nonneg X))
    simp
  · have hcard : (0 : ℝ) < (S.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hSne
    have hε' : 0 < ε / (S.card : ℝ) := div_pos hε hcard
    -- totalise before choosing, so that `choose` yields plain functions `ℕ → ℕ`
    have key : ∀ q : ℕ, ∃ n X₀ : ℕ, q ∈ S → ∀ X, X₀ ≤ X →
        (((Finset.Icc 1 X).filter
            (fun m => ¬ q ∣ m ∧ ¬ ∃ j < n, genSeq m j = q)).card : ℝ)
          ≤ ε / (S.card : ℝ) * (X : ℝ) := by
      intro q
      by_cases hq : q ∈ S
      · obtain ⟨n, X₀, h⟩ := almost_all_genmc_density q (hS q hq) hε'
        exact ⟨n, X₀, fun _ => h⟩
      · exact ⟨0, 0, fun h => absurd h hq⟩
    choose N B hNB using key
    refine ⟨S.sup N, S.sup B, fun X hX => ?_⟩
    -- the bad set is covered by the union of the per-`q` bad sets at their own horizons
    have hsub : ((Finset.Icc 1 X).filter
        (fun m => ∃ q ∈ S, ¬ q ∣ m ∧ ¬ ∃ j < S.sup N, genSeq m j = q)) ⊆
        S.biUnion (fun q => (Finset.Icc 1 X).filter
          (fun m => ¬ q ∣ m ∧ ¬ ∃ j < N q, genSeq m j = q)) := by
      intro m hm
      rw [Finset.mem_filter] at hm
      obtain ⟨hmIcc, q, hqS, hqm, hcap⟩ := hm
      refine Finset.mem_biUnion.mpr ⟨q, hqS, Finset.mem_filter.mpr ⟨hmIcc, hqm, ?_⟩⟩
      rintro ⟨j, hj, hjq⟩
      exact hcap ⟨j, lt_of_lt_of_le hj (Finset.le_sup (f := N) hqS), hjq⟩
    have h1 : (((Finset.Icc 1 X).filter
        (fun m => ∃ q ∈ S, ¬ q ∣ m ∧ ¬ ∃ j < S.sup N, genSeq m j = q)).card : ℝ)
        ≤ ((S.biUnion (fun q => (Finset.Icc 1 X).filter
            (fun m => ¬ q ∣ m ∧ ¬ ∃ j < N q, genSeq m j = q))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h2 : ((S.biUnion (fun q => (Finset.Icc 1 X).filter
        (fun m => ¬ q ∣ m ∧ ¬ ∃ j < N q, genSeq m j = q))).card : ℝ)
        ≤ ∑ q ∈ S, (((Finset.Icc 1 X).filter
            (fun m => ¬ q ∣ m ∧ ¬ ∃ j < N q, genSeq m j = q)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have h3 : ∑ q ∈ S, (((Finset.Icc 1 X).filter
        (fun m => ¬ q ∣ m ∧ ¬ ∃ j < N q, genSeq m j = q)).card : ℝ)
        ≤ ∑ _q ∈ S, ε / (S.card : ℝ) * (X : ℝ) :=
      Finset.sum_le_sum fun q hq =>
        hNB q hq X (le_trans (Finset.le_sup (f := B) hq) hX)
    have h4 : ∑ _q ∈ S, ε / (S.card : ℝ) * (X : ℝ) = ε * (X : ℝ) := by
      have hne : (S.card : ℝ) ≠ 0 := ne_of_gt hcard
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp
    linarith [h1, h2, h3, h4.le, h4.ge]

end AlmostAllDensity

end
