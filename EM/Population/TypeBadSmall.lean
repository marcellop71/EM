import EM.Population.FiberTheoremC
import EM.Population.AlmostAllGenMC

/-!
# The bad seed types are rare — the fibre-measurable form

`AlmostAllGenMC.almost_all_genmc` bounds the fraction of *uncaptured* seeds in one period of
`SelectionLaw.modulus q Y`.  Two of its ingredients, the clauses `¬ q ∣ m` and
`¬ ∃ j < n, genSeq m j = q` of `TheoremC.GoodSeed`, are **not** functions of the residue
`m mod (modulus q Y)`, so that statement does not by itself transfer to natural density.

`FiberTheoremC.FiberGood` removes that obstruction, and this file re-runs the Session-311
assembly on top of it.  The resulting `type_bad_small` bounds the union of the **three
fibre-measurable bad types**

* a degenerate or oversized `(n+1)`-prefix of the `q`-free dynamics,
* a heavy divisor mass in the exclusion window `(Cc², Y]`,
* fibre-goodness `FiberTheoremC.FiberGood`,

with *no* coprimality clause anywhere.  The exclusion-window constant `Cc` is reported
alongside `n` and `Y` because the density transfer needs it.

## Main results

* `bad_type_decomposition` — the three-disjunct filter sits inside the union of the three
  single-type filters.
* `type_bad_small` — the headline: for every `ε > 0` there are `n`, `Y`, `Cc` making the
  union at most an `ε`-fraction of the period.
* `almost_all_genmc_of_type_bad` — sanity check: `type_bad_small` recovers the Session-311
  headline `AlmostAllGenMC.almost_all_genmc`.

Session 312, WP-N Part C.
-/

noncomputable section
open Classical

namespace TypeBadSmall

open SeedCapture SeedTypes LargeStepRoughness SelectionLaw LSPlus TailEstimate TailAssembly
open TheoremC AlmostAllGenMC

/-! ## 1. The three-type decomposition -/

/-- **The three fibre-measurable bad types decompose.**  A seed satisfying the disjunction of
the three bad types lies in the union of the three single-type filters.  This is the
`FiberGood` analogue of `AlmostAllGenMC.uncaptured_decomposition`, with the (non-periodic)
coprimality and capture clauses absent. -/
theorem bad_type_decomposition (q Y Cc n : ℕ) :
    (sampleSpace q Y).filter (fun m =>
        ¬ (∀ j < n + 1, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y)
        ∨ (1 : ℝ) / Cc ≤ ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter (fun r => r.Prime ∧ r ∣ m),
              (1 : ℝ) / r
        ∨ FiberTheoremC.FiberGood q Y Cc n m)
      ⊆ ((sampleSpace q Y).filter (fun m => FiberTheoremC.FiberGood q Y Cc n m)
          ∪ (sampleSpace q Y).filter (fun m =>
              ¬ (∀ j < n + 1, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y)))
        ∪ (sampleSpace q Y).filter (fun m =>
            (1 : ℝ) / Cc ≤ ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter (fun r => r.Prime ∧ r ∣ m),
              (1 : ℝ) / r) := by
  intro m hm
  rw [Finset.mem_filter] at hm
  obtain ⟨hmem, hcase⟩ := hm
  rcases hcase with hdeg | hheavy | hfib
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨hmem, hdeg⟩))
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hmem, hheavy⟩)
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨hmem, hfib⟩))

/-! ## 2. The headline -/

/-- **The fibre-measurable bad types are rare.**

For a fixed prime `q` and any `ε > 0` there are a horizon `n`, a truncation `Y` and an
exclusion-window constant `Cc` such that the seeds of one period `sampleSpace q Y` exhibiting
*any* of the three bad types — degenerate/oversized `(n+1)`-prefix, heavy window divisor mass
in `(Cc², Y]`, or `FiberTheoremC.FiberGood` — number at most an `ε`-fraction of the period.

Unlike `AlmostAllGenMC.almost_all_genmc`, **every** clause here is determined by
`m mod (modulus q Y)`: there is no `¬ q ∣ m` and no genuine-orbit capture clause.  That is
exactly what the transfer from a one-period count to a natural-density statement needs, and
it is why `Cc` is reported.

*Proof.*  The generic assembly `AlmostAllGenMC.three_type_union_small`, fed with
`FiberTheoremC.theorem_C_fiber` in place of `TheoremC.theorem_C`; the nondegeneracy input it
asks for is the first clause of `FiberGood`.  The three-type containment is
`bad_type_decomposition`. -/
theorem type_bad_small (q : ℕ) (hq : q.Prime) (ε : ℝ) (hε : 0 < ε) :
    ∃ n Y Cc : ℕ, 1 ≤ SelectionLaw.modulus q Y ∧
      (((sampleSpace q Y).filter (fun m =>
          ¬ (∀ j < n + 1, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y)
          ∨ (1 : ℝ) / Cc ≤ ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter (fun r => r.Prime ∧ r ∣ m),
                (1 : ℝ) / r
          ∨ FiberTheoremC.FiberGood q Y Cc n m)).card : ℝ)
        ≤ ε * ((sampleSpace q Y).card : ℝ) := by
  classical
  obtain ⟨n, Y, Cc, -, hbound⟩ := AlmostAllGenMC.three_type_union_small q hq hε
    (fun Y Cc n => (sampleSpace q Y).filter (fun m => FiberTheoremC.FiberGood q Y Cc n m))
    (fun _ _ _ _ hm => (Finset.mem_filter.mp hm).2.1)
    (fun Cc hCc => by
      obtain ⟨κ, hκ, K₀, n₁, h⟩ := FiberTheoremC.theorem_C_fiber q Cc hq hCc
      exact ⟨κ, hκ, K₀, n₁, fun Y n hn hCcn hpol hthr =>
        h Y n hn hCcn hpol fun m hm hg => hthr m hm (Finset.mem_filter.mpr ⟨hm, hg⟩)⟩)
  exact ⟨n, Y, Cc, modulus_pos q Y, le_trans (Nat.cast_le.mpr
    (Finset.card_le_card (bad_type_decomposition q Y Cc n))) hbound⟩

/-! ## 3. Sanity check: the Session-311 headline is recovered -/

/-- **`type_bad_small` implies `AlmostAllGenMC.almost_all_genmc`.**  An uncaptured seed
coprime to `q` either has a degenerate prefix, or a heavy window divisor mass, or is a
`TheoremC.GoodSeed` — and hence, by `FiberTheoremC.goodSeed_fiberGood`, `FiberGood`.  So the
uncaptured set is contained in the three-type union, and nothing was lost in Part C. -/
theorem almost_all_genmc_of_type_bad (q : ℕ) (hq : q.Prime) :
    ∀ ε : ℝ, 0 < ε → ∃ n Y : ℕ,
      (((sampleSpace q Y).filter (fun m => ¬ q ∣ m ∧ ¬ ∃ j < n, genSeq m j = q)).card : ℝ)
        ≤ ε * ((sampleSpace q Y).card : ℝ) := by
  intro ε hε
  obtain ⟨n, Y, Cc, _, hbound⟩ := type_bad_small q hq ε hε
  refine ⟨n, Y, le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) hbound⟩
  intro m hm
  rw [Finset.mem_filter] at hm ⊢
  obtain ⟨hmem, hdvd, hcap⟩ := hm
  refine ⟨hmem, ?_⟩
  by_cases hnd : ∀ j < n + 1, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y
  · by_cases hmass : (∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter (fun r => r.Prime ∧ r ∣ m),
        (1 : ℝ) / r) ≤ 1 / Cc
    · exact Or.inr (Or.inr (FiberTheoremC.goodSeed_fiberGood (mem_sampleSpace.mp hmem).1
        ⟨hdvd, hcap, hnd, hmass⟩))
    · exact Or.inr (Or.inl (le_of_lt (not_le.mp hmass)))
  · exact Or.inl hnd

end TypeBadSmall

end
