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

*Proof.*  Verbatim the Session-311 assembly, with `FiberTheoremC.theorem_C_fiber` in place of
`TheoremC.theorem_C` (identical constants, so the threshold arithmetic is unchanged),
`TailAssembly.tail_small` for the degenerate prefixes and `TailEstimate.markov_divisor_mass`
at `z = Cc²`, `δ = 1/Cc` for the heavy divisor mass.  `AlmostAllGenMC.threshold_sq_le`
discharges the localization hypothesis of the fibre Theorem C — it needs only the
nondegeneracy clause, which is the first clause of `FiberGood`.  The policy witness `Y` comes
from `AlmostAllGenMC.policy_shifted`, and `Cc = max (48 q) ⌈3/ε⌉₊` makes each of the three
pieces at most `ε/3`. -/
theorem type_bad_small (q : ℕ) (hq : q.Prime) (ε : ℝ) (hε : 0 < ε) :
    ∃ n Y Cc : ℕ, 1 ≤ SelectionLaw.modulus q Y ∧
      (((sampleSpace q Y).filter (fun m =>
          ¬ (∀ j < n + 1, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y)
          ∨ (1 : ℝ) / Cc ≤ ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter (fun r => r.Prime ∧ r ∣ m),
                (1 : ℝ) / r
          ∨ FiberTheoremC.FiberGood q Y Cc n m)).card : ℝ)
        ≤ ε * ((sampleSpace q Y).card : ℝ) := by
  classical
  -- the exclusion-window constant
  set Cc : ℕ := max (48 * q) ⌈3 / ε⌉₊ with hCcdef
  have hCc48 : 48 * q ≤ Cc := le_max_left _ _
  have hq2 := hq.two_le
  have hCc1 : 1 ≤ Cc := by omega
  have hCcR : (0 : ℝ) < (Cc : ℝ) := by exact_mod_cast hCc1
  have hCceps : (1 : ℝ) / Cc ≤ ε / 3 := by
    have h1 : (3 : ℝ) / ε ≤ (Cc : ℝ) := by
      have h2 : (⌈3 / ε⌉₊ : ℝ) ≤ (Cc : ℝ) := by
        exact_mod_cast le_max_right (48 * q) ⌈3 / ε⌉₊
      exact le_trans (Nat.le_ceil _) h2
    have h2 : (1 : ℝ) / (Cc : ℝ) ≤ 1 / ((3 : ℝ) / ε) :=
      one_div_le_one_div_of_le (by positivity) h1
    rwa [one_div_div] at h2
  -- fibre Theorem C constants
  obtain ⟨κ, hκpos, K₀, n₁, hC⟩ := FiberTheoremC.theorem_C_fiber q Cc hq hCc48
  obtain ⟨n₀, htail⟩ := tail_small
  -- the exponential threshold
  set A : ℝ := 3 / 8 * (κ * (c₁ / 2)) with hA
  set Bc : ℝ := 3 / 8 * (κ * (K₀ : ℝ)) with hBc
  have hApos : 0 < A := by
    rw [hA]; have := c₁_pos; positivity
  set E₁ : ℝ := (Real.log (3 / ε) + Bc) / A with hE₁
  set E₂ : ℝ := (6 * Real.exp 25 / ε) ^ 2 with hE₂
  set n : ℕ := n₁ + Cc + 4000 + n₀ + ⌈E₁⌉₊ + ⌈E₂⌉₊ with hn
  have hn₁ : n₁ ≤ n := by omega
  have hnCc : Cc ≤ n := by omega
  have hn4000 : 4000 ≤ n := by omega
  have hn₀ : n₀ ≤ n + 1 := by omega
  have hE₁n : E₁ ≤ (n : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast (by omega : ⌈E₁⌉₊ ≤ n)
  have hE₂n : E₂ ≤ (n : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast (by omega : ⌈E₂⌉₊ ≤ n)
  have hnR4 : (4000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4000
  have hCcRn : (Cc : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnCc
  -- the policy witness
  obtain ⟨Y, hlow, hhigh⟩ := policy_shifted n (by omega)
  refine ⟨n, Y, Cc, modulus_pos q Y, ?_⟩
  have hlown : ((n : ℝ)) ^ 2 / 2 ≤ Real.log Y := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  -- ### piece 1 : fibre-good seeds
  have hthr2 : ∀ m ∈ sampleSpace q Y, FiberTheoremC.FiberGood q Y Cc n m →
      ∀ k < n, (bigThreshold q m Cc k) ^ 2 ≤ Y := by
    intro m _ hgood
    exact threshold_sq_le q Cc Y n hnCc hn4000 hlown m
      (fun j hj => hgood.1 j (by omega))
  have hgoodcount := hC Y n hn₁ hCcRn hhigh hthr2
  have hexp : Real.exp (-(3 / 8) * (κ * (c₁ / 2 * (n : ℝ) - (K₀ : ℝ)))) ≤ ε / 3 := by
    have hkey : Real.log (3 / ε) ≤ A * (n : ℝ) - Bc := by
      rw [hE₁, div_le_iff₀ hApos] at hE₁n
      linarith
    have hstep : -(3 / 8) * (κ * (c₁ / 2 * (n : ℝ) - (K₀ : ℝ))) ≤ -Real.log (3 / ε) := by
      have : A * (n : ℝ) - Bc = 3 / 8 * (κ * (c₁ / 2 * (n : ℝ) - (K₀ : ℝ))) := by
        rw [hA, hBc]; ring
      linarith [hkey, this]
    have h2 : Real.exp (-(3 / 8) * (κ * (c₁ / 2 * (n : ℝ) - (K₀ : ℝ))))
        ≤ Real.exp (-Real.log (3 / ε)) := Real.exp_le_exp.mpr hstep
    have h3 : Real.exp (-Real.log (3 / ε)) = ε / 3 := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
    linarith [h2, h3.le, h3.ge]
  have hcard0 : (0 : ℝ) ≤ ((sampleSpace q Y).card : ℝ) := by positivity
  have hpiece1 : (((sampleSpace q Y).filter
        (fun m => FiberTheoremC.FiberGood q Y Cc n m)).card : ℝ)
      ≤ ε / 3 * ((sampleSpace q Y).card : ℝ) := by
    refine le_trans hgoodcount ?_
    have := mul_le_mul_of_nonneg_left hexp hcard0
    linarith [this]
  -- ### piece 2 : degenerate prefixes
  have hlowshift : (((n + 1 : ℕ) : ℝ)) ^ 2 / 2 ≤ Real.log Y := by push_cast; linarith
  have hhighshift : Real.log Y ≤ (((n + 1 : ℕ) : ℝ)) ^ 3 := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have htailcount := htail q Y (n + 1) hq hn₀ hlowshift hhighshift
  have hlogsmall : Real.exp 25 * Real.log ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ)) : ℝ) ≤ ε / 3 := by
    set x : ℝ := ((n + 1 : ℕ) : ℝ) with hx
    have hxpos : (0 : ℝ) < x := by
      rw [hx]; exact_mod_cast Nat.succ_pos n
    set s : ℝ := Real.sqrt x with hs
    have hspos : 0 < s := Real.sqrt_pos.mpr hxpos
    have hsq : s ^ 2 = x := Real.sq_sqrt hxpos.le
    have hlogx : Real.log x ≤ 2 * s := log_le_two_sqrt hxpos
    have hslarge : 6 * Real.exp 25 / ε ≤ s := by
      have hE₂x : E₂ ≤ x := by rw [hx]; push_cast; linarith
      have hnn : (0 : ℝ) ≤ 6 * Real.exp 25 / ε := by positivity
      have := Real.sqrt_le_sqrt hE₂x
      rw [hE₂, Real.sqrt_sq hnn] at this
      exact this
    have he25 : (0 : ℝ) < Real.exp 25 := Real.exp_pos _
    have hsne : s ≠ 0 := ne_of_gt hspos
    have hkey : Real.exp 25 * Real.log x / x ≤ 2 * Real.exp 25 / s := by
      rw [div_le_iff₀ hxpos]
      have h1 : Real.exp 25 * Real.log x ≤ Real.exp 25 * (2 * s) :=
        mul_le_mul_of_nonneg_left hlogx he25.le
      have h2 : 2 * Real.exp 25 / s * x = 2 * Real.exp 25 * s := by
        rw [← hsq]; field_simp
      linarith [h1, h2.le, h2.ge]
    have hfin : 2 * Real.exp 25 / s ≤ ε / 3 := by
      rw [div_le_iff₀ hspos]
      have h1 : 6 * Real.exp 25 ≤ s * ε := by
        rw [div_le_iff₀ hε] at hslarge
        linarith
      nlinarith [h1]
    linarith
  have hpiece2 : (((sampleSpace q Y).filter (fun m =>
      ¬ (∀ j < n + 1, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y))).card : ℝ)
      ≤ ε / 3 * ((sampleSpace q Y).card : ℝ) := by
    refine le_trans htailcount ?_
    exact mul_le_mul_of_nonneg_right hlogsmall hcard0
  -- ### piece 3 : heavy window divisor mass
  have hmk := markov_divisor_mass (Cc ^ 2) Y (modulus q Y) (Nat.one_le_pow _ _ hCc1)
    (show (0:ℝ) < 1 / Cc by positivity)
  have hfilterEq : ∀ m : ℕ,
      ((Finset.Ioc (Cc ^ 2) Y).filter Nat.Prime).filter (fun r => r ∣ m)
        = (Finset.Ioc (Cc ^ 2) Y).filter (fun r => r.Prime ∧ r ∣ m) := by
    intro m; rw [Finset.filter_filter]
  have hpiece3 : (((sampleSpace q Y).filter (fun m =>
      (1 : ℝ) / Cc ≤ ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter (fun r => r.Prime ∧ r ∣ m),
        (1 : ℝ) / r)).card : ℝ) ≤ ε / 3 * ((sampleSpace q Y).card : ℝ) := by
    have hrw : ((sampleSpace q Y).filter (fun m =>
        (1 : ℝ) / Cc ≤ ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter (fun r => r.Prime ∧ r ∣ m),
          (1 : ℝ) / r))
        = (Finset.Ico 1 (modulus q Y + 1)).filter (fun m =>
          (1 : ℝ) / Cc ≤ ∑ r ∈ ((Finset.Ioc (Cc ^ 2) Y).filter Nat.Prime).filter
            (fun r => r ∣ m), (1 : ℝ) / r) := by
      simp only [sampleSpace, hfilterEq]
    rw [hrw]
    refine le_trans hmk ?_
    have hden : ((Cc : ℝ) ^ 2) * ((1 : ℝ) / Cc) = (Cc : ℝ) := by field_simp
    have hcast : ((Cc ^ 2 : ℕ) : ℝ) = ((Cc : ℝ)) ^ 2 := by push_cast; ring
    rw [hcast, hden]
    have hcardeq : ((sampleSpace q Y).card : ℝ) = ((modulus q Y : ℕ) : ℝ) := by
      rw [card_sampleSpace]
    rw [hcardeq]
    have hM0 : (0 : ℝ) ≤ ((modulus q Y : ℕ) : ℝ) := by positivity
    have : ((modulus q Y : ℕ) : ℝ) / (Cc : ℝ) = (1 / (Cc : ℝ)) * ((modulus q Y : ℕ) : ℝ) := by
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hCceps hM0
  -- ### assembly
  have hsub := bad_type_decomposition q Y Cc n
  calc (((sampleSpace q Y).filter (fun m =>
        ¬ (∀ j < n + 1, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y)
        ∨ (1 : ℝ) / Cc ≤ ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter (fun r => r.Prime ∧ r ∣ m),
              (1 : ℝ) / r
        ∨ FiberTheoremC.FiberGood q Y Cc n m)).card : ℝ)
      ≤ ((((sampleSpace q Y).filter (fun m => FiberTheoremC.FiberGood q Y Cc n m)
            ∪ (sampleSpace q Y).filter (fun m =>
                ¬ (∀ j < n + 1, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y)))
          ∪ (sampleSpace q Y).filter (fun m =>
              (1 : ℝ) / Cc ≤ ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter
                (fun r => r.Prime ∧ r ∣ m), (1 : ℝ) / r)).card : ℝ) := by
        exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ε * ((sampleSpace q Y).card : ℝ) := by
        have h1 := Finset.card_union_le
          ((sampleSpace q Y).filter (fun m => FiberTheoremC.FiberGood q Y Cc n m)
            ∪ (sampleSpace q Y).filter (fun m =>
              ¬ (∀ j < n + 1, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y)))
          ((sampleSpace q Y).filter (fun m =>
              (1 : ℝ) / Cc ≤ ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter
                (fun r => r.Prime ∧ r ∣ m), (1 : ℝ) / r))
        have h2 := Finset.card_union_le
          ((sampleSpace q Y).filter (fun m => FiberTheoremC.FiberGood q Y Cc n m))
          ((sampleSpace q Y).filter (fun m =>
              ¬ (∀ j < n + 1, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y)))
        have hc1 : (((((sampleSpace q Y).filter (fun m => FiberTheoremC.FiberGood q Y Cc n m)
            ∪ (sampleSpace q Y).filter (fun m =>
              ¬ (∀ j < n + 1, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y)))
          ∪ (sampleSpace q Y).filter (fun m =>
              (1 : ℝ) / Cc ≤ ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter
                (fun r => r.Prime ∧ r ∣ m), (1 : ℝ) / r)).card : ℕ) : ℝ)
            ≤ ((((sampleSpace q Y).filter
                  (fun m => FiberTheoremC.FiberGood q Y Cc n m)).card : ℕ) : ℝ)
              + ((((sampleSpace q Y).filter (fun m =>
                  ¬ (∀ j < n + 1, 2 ≤ genSeqAvoid q m j
                    ∧ genSeqAvoid q m j ≤ Y))).card : ℕ) : ℝ)
              + ((((sampleSpace q Y).filter (fun m =>
                  (1 : ℝ) / Cc ≤ ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter
                    (fun r => r.Prime ∧ r ∣ m), (1 : ℝ) / r)).card : ℕ) : ℝ) := by
          have := Nat.le_trans h1 (Nat.add_le_add_right h2 _)
          exact_mod_cast this
        linarith [hpiece1, hpiece2, hpiece3, hc1]

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
