import EM.FunctionField.AutonomousDegrees
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The `𝔽_2` threshold: `1 ∈ Im (F+1)^k` on `𝔽_{2^d}` iff `k < 2^{v₂(d)}`

Over `𝔽_2[X]` the autonomous (take-all) Euclid step is `P ↦ P² + P = (F + 1) P`, Frobenius plus
one, an `𝔽_2`-linear operator.  A capture of an irreducible `π` of degree `d` after `k`
consecutive autonomous steps requires `1 ∈ Im (F + 1)^k` on the residue field `𝔽_{2^d}`
(`sylv^[k] (P_n(β)) = 1` for a root `β` of `π`).  This file proves the closed form announced in
`docs/analysis/feedback_selection_2026-11-08.md` §3:

* **Necessity** (`two_pow_succ_dvd_minimalPeriod_of_sylv_iterate_eq_one`): if `sylv^[k] y = 1`
  and `2^v ≤ k`, then `2^{v+1}` divides the Frobenius period of `y`.  Proof without the relative
  trace: `(F+1)^{2^v} = F^{2^v} + 1` in characteristic `2` (`sylv_iterate_two_pow`), so
  `z := sylv^[k - 2^v] y` satisfies `z^{2^{2^v}} = z + 1`; such a `z` has Frobenius period exactly
  `2^{v+1}` (`minimalPeriod_eq_of_sylv_iterate_two_pow_eq_one`, generalising the period-`2` and
  period-`4` computations of `CharTwo.lean`), and the period of `z` divides the period of `y`
  because `sylv` commutes with Frobenius.
* **Sharpness** (`exists_sylv_iterate_pred_eq_one`): in `𝔽_{2^{2^v}}` some `x` has
  `sylv^[2^v - 1] x = 1`.  Root counting: `sylv^[j]` is evaluation of a monic polynomial of degree
  `2^j`, so `sylv^[2^v-1]` has at most `2^{2^v-1} < 2^{2^v}` zeros, while `sylv^[2^v] = 0` on
  `𝔽_{2^{2^v}}`; a nonzero value in `ker sylv = {0, 1}` is `1`.
* **The iff** (`one_mem_sylv_iterate_image_iff`): for `d ≠ 0`,
  `(∃ x, x^{2^d} = x ∧ sylv^[k] x = 1) ↔ k < 2 ^ padicValNat 2 d`.

Applied to the Euclid sequence over `𝔽_2` (`lt_two_pow_padicValNat_natDegree_of_run`): after `k`
consecutive irreducible stages every irreducible factor `f` of the next Euclid polynomial has
`k < 2^{v₂(deg f)}`, i.e. `2^{v+1} ∣ deg f` whenever `2^v ≤ k`.  The cases `k = 1, 2` are
`AutonomousDegrees.even_natDegree_of_dvd_euclid_succ` and `four_dvd_natDegree_of_two_irreducible`.
The actual `𝔽_2` sequence attains the bound: its first three Euclid polynomials are irreducible
(`CharTwo.ff_two_attains_three`) and the fourth splits into two quartics, `k = 3 = 2² - 1` with
`v₂(4) = 2`.

Reading in the language of feedback selection: for an odd-degree target the step immediately
before a capture must deviate; for degree `2^v · odd` the feedback must arrive within `2^v - 1`
steps of the capture.  This is the function-field twin of `FeedbackSelection.deviates_of_dvd_two_mod_three`.
-/

namespace FunctionFieldAnalog

namespace AutonomousThreshold

open Polynomial FrobeniusOrbit CompositeFloors FunctionFieldAnalog.CharTwo

/-! ## 1. The Sylvester map on `𝔽̄_2` -/

/-- The autonomous step over `𝔽_2`: `y ↦ y² + y = (F + 1) y`. -/
noncomputable def sylv (y : Lp 2) : Lp 2 := y ^ 2 + y

theorem sylv_apply (y : Lp 2) : sylv y = y ^ 2 + y := rfl

/-- `sylv` commutes with Frobenius. -/
theorem commute_φ_sylv : Function.Commute (⇑(φ 2)) sylv := by
  intro y
  simp only [sylv, map_add, map_pow]

theorem φ_iterate_sylv_iterate (m j : ℕ) (y : Lp 2) :
    (⇑(φ 2))^[m] (sylv^[j] y) = sylv^[j] ((⇑(φ 2))^[m] y) :=
  (commute_φ_sylv.iterate_iterate m j).semiconj.eq y

/-- `(F + 1)^{2^v} = F^{2^v} + 1` in characteristic two. -/
theorem sylv_iterate_two_pow (v : ℕ) (z : Lp 2) : sylv^[2 ^ v] z = z ^ 2 ^ 2 ^ v + z := by
  induction v generalizing z with
  | zero => simp [sylv]
  | succ v ih =>
    have hQ : (2 : ℕ) ^ 2 ^ v * 2 ^ 2 ^ v = 2 ^ 2 ^ (v + 1) := by
      rw [← pow_add, ← mul_two, ← pow_succ]
    rw [pow_succ, mul_two, Function.iterate_add_apply, ih, ih, add_pow_char_pow, ← pow_mul, hQ]
    linear_combination CharTwo.add_self_eq_zero (z ^ 2 ^ 2 ^ v)

/-- A solution of `z^{2^{2^v}} = z + 1` has Frobenius period exactly `2^{v+1}`. -/
theorem minimalPeriod_eq_of_sylv_iterate_two_pow_eq_one {v : ℕ} {z : Lp 2}
    (h : sylv^[2 ^ v] z = 1) : Function.minimalPeriod (⇑(φ 2)) z = 2 ^ (v + 1) := by
  rw [sylv_iterate_two_pow] at h
  have hz : z ^ 2 ^ 2 ^ v = z + 1 := by linear_combination h + (-z) * two_eq_zero_L
  have hper : Function.IsPeriodicPt (⇑(φ 2)) (2 ^ (v + 1)) z := by
    show (⇑(φ 2))^[2 ^ (v + 1)] z = z
    rw [pow_succ, mul_two, Function.iterate_add_apply, φ_iterate, φ_iterate, hz, add_pow_char_pow,
      hz, one_pow]
    linear_combination two_eq_zero_L
  have hnot : ¬ Function.IsPeriodicPt (⇑(φ 2)) (2 ^ v) z := by
    intro h'
    have h'' : (⇑(φ 2))^[2 ^ v] z = z := h'
    rw [φ_iterate, hz] at h''
    exact one_ne_zero (by linear_combination h'' : (1 : Lp 2) = 0)
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hper.minimalPeriod_dvd
  rcases Nat.lt_or_ge k (v + 1) with hlt | hge
  · exfalso
    apply hnot
    have hdvd : Function.minimalPeriod (⇑(φ 2)) z ∣ 2 ^ v := by
      rw [hkeq]; exact Nat.pow_dvd_pow 2 (by omega)
    exact (Function.isPeriodicPt_minimalPeriod _ _).trans_dvd hdvd
  · rw [hkeq]; congr 1; omega

/-- The Frobenius period of `sylv^[j] y` divides that of `y`. -/
theorem minimalPeriod_sylv_iterate_dvd (j : ℕ) (y : Lp 2) :
    Function.minimalPeriod (⇑(φ 2)) (sylv^[j] y) ∣ Function.minimalPeriod (⇑(φ 2)) y := by
  apply Function.IsPeriodicPt.minimalPeriod_dvd
  show (⇑(φ 2))^[Function.minimalPeriod (⇑(φ 2)) y] (sylv^[j] y) = sylv^[j] y
  rw [φ_iterate_sylv_iterate, (Function.isPeriodicPt_minimalPeriod (⇑(φ 2)) y).eq]

/-- **Necessity.** If `sylv^[k] y = 1` and `2^v ≤ k`, then `2^{v+1}` divides the Frobenius
period of `y`. -/
theorem two_pow_succ_dvd_minimalPeriod_of_sylv_iterate_eq_one {v k : ℕ} (hk : 2 ^ v ≤ k)
    {y : Lp 2} (h : sylv^[k] y = 1) : 2 ^ (v + 1) ∣ Function.minimalPeriod (⇑(φ 2)) y := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Function.iterate_add_apply] at h
  rw [← minimalPeriod_eq_of_sylv_iterate_two_pow_eq_one h]
  exact minimalPeriod_sylv_iterate_dvd j y

/-- Closed form of necessity: an element of `𝔽_{2^d}` reaching `1` after `k` autonomous steps
forces `k < 2^{v₂(d)}`. -/
theorem lt_two_pow_padicValNat_of_sylv_iterate_eq_one {d k : ℕ} (hd : d ≠ 0) {y : Lp 2}
    (hy : y ^ 2 ^ d = y) (h : sylv^[k] y = 1) : k < 2 ^ padicValNat 2 d := by
  by_contra hlt
  push Not at hlt
  have h1 := two_pow_succ_dvd_minimalPeriod_of_sylv_iterate_eq_one hlt h
  have h2 : Function.minimalPeriod (⇑(φ 2)) y ∣ d := by
    apply Function.IsPeriodicPt.minimalPeriod_dvd
    show (⇑(φ 2))^[d] y = y
    rw [φ_iterate]; exact hy
  exact pow_succ_padicValNat_not_dvd hd (h1.trans h2)

/-! ## 2. Sharpness by root counting -/

/-- The polynomial form of the autonomous step, `P ↦ P² + P`. -/
noncomputable def sylvPoly (P : (ZMod 2)[X]) : (ZMod 2)[X] := P ^ 2 + P

theorem aeval_sylvPoly_iterate (j : ℕ) (P : (ZMod 2)[X]) (y : Lp 2) :
    aeval y (sylvPoly^[j] P) = sylv^[j] (aeval y P) := by
  induction j generalizing P with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    congr 1
    simp only [sylvPoly, sylv, map_add, map_pow]

/-- `sylvPoly^[j] X` is monic of degree `2^j`. -/
theorem sylvPoly_iterate_monic_natDegree (j : ℕ) :
    (sylvPoly^[j] X).Monic ∧ (sylvPoly^[j] X).natDegree = 2 ^ j := by
  induction j with
  | zero => exact ⟨monic_X, by simp⟩
  | succ j ih =>
    obtain ⟨hm, hd⟩ := ih
    rw [Function.iterate_succ_apply', sylvPoly]
    have hsq : (sylvPoly^[j] X ^ 2).Monic := hm.pow 2
    have hdeg : (sylvPoly^[j] X ^ 2).natDegree = 2 ^ (j + 1) := by
      rw [hm.natDegree_pow, hd, pow_succ, mul_comm]
    have hlt : (sylvPoly^[j] X).natDegree < (sylvPoly^[j] X ^ 2).natDegree := by
      rw [hd, hdeg]; exact pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self j)
    exact ⟨hsq.add_of_left (degree_lt_degree hlt),
      by rw [natDegree_add_eq_left_of_natDegree_lt hlt, hdeg]⟩

open Classical in
/-- **Sharpness.** In `𝔽_{2^{2^v}}` some element reaches `1` after exactly `2^v - 1` autonomous
steps. -/
theorem exists_sylv_iterate_pred_eq_one (v : ℕ) :
    ∃ x : Lp 2, x ^ 2 ^ 2 ^ v = x ∧ sylv^[2 ^ v - 1] x = 1 := by
  have hv : (2 : ℕ) ^ v ≠ 0 := pow_ne_zero _ two_ne_zero
  have hQ1 : 1 < (2 : ℕ) ^ 2 ^ v := Nat.one_lt_two_pow hv
  obtain ⟨hGm, hGd⟩ := sylvPoly_iterate_monic_natDegree (2 ^ v - 1)
  set G : (ZMod 2)[X] := sylvPoly^[2 ^ v - 1] X with hG
  set G' : (Lp 2)[X] := G.map (algebraMap (ZMod 2) (Lp 2)) with hG'
  have hsep : Separable (X ^ 2 ^ 2 ^ v - X : (Lp 2)[X]) :=
    galois_poly_separable 2 (2 ^ 2 ^ v) (dvd_pow_self 2 hv)
  have hcard : ((X ^ 2 ^ 2 ^ v - X : (Lp 2)[X]).roots.toFinset).card = 2 ^ 2 ^ v := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
      FiniteField.X_pow_card_sub_X_natDegree_eq (Lp 2) hQ1]
  have hGcard : (G'.roots.toFinset).card < ((X ^ 2 ^ 2 ^ v - X : (Lp 2)[X]).roots.toFinset).card := by
    rw [hcard]
    calc (G'.roots.toFinset).card ≤ Multiset.card G'.roots := Multiset.toFinset_card_le _
      _ ≤ G'.natDegree := card_roots' _
      _ = 2 ^ (2 ^ v - 1) := by rw [hG', natDegree_map, hGd]
      _ < 2 ^ 2 ^ v := pow_lt_pow_right₀ (by norm_num) (Nat.sub_lt (Nat.pos_of_ne_zero hv) Nat.one_pos)
  obtain ⟨x, hx, hxG⟩ := Finset.exists_mem_notMem_of_card_lt_card hGcard
  have hxQ : x ^ 2 ^ 2 ^ v = x := by
    rw [Multiset.mem_toFinset, mem_roots (FiniteField.X_pow_card_sub_X_ne_zero (Lp 2) hQ1),
      IsRoot.def, eval_sub, eval_pow, eval_X, sub_eq_zero] at hx
    exact hx
  have hw : sylv^[2 ^ v - 1] x ≠ 0 := by
    intro h0
    apply hxG
    rw [Multiset.mem_toFinset, mem_roots (hGm.map (algebraMap (ZMod 2) (Lp 2))).ne_zero,
      IsRoot.def, eval_map_algebraMap, hG, aeval_sylvPoly_iterate, aeval_X, h0]
  refine ⟨x, hxQ, ?_⟩
  have hs : sylv (sylv^[2 ^ v - 1] x) = 0 := by
    rw [← Function.iterate_succ_apply' sylv (2 ^ v - 1) x, Nat.succ_eq_add_one,
      Nat.sub_add_cancel Nat.one_le_two_pow, sylv_iterate_two_pow, hxQ]
    exact CharTwo.add_self_eq_zero x
  rw [sylv_apply] at hs
  have hmul : sylv^[2 ^ v - 1] x * (sylv^[2 ^ v - 1] x + 1) = 0 := by linear_combination hs
  rcases mul_eq_zero.mp hmul with h | h
  · exact absurd h hw
  · linear_combination h - two_eq_zero_L

/-- Every `k < 2^v` is realised inside `𝔽_{2^{2^v}}`. -/
theorem exists_sylv_iterate_eq_one_of_lt {v k : ℕ} (hk : k < 2 ^ v) :
    ∃ x : Lp 2, x ^ 2 ^ 2 ^ v = x ∧ sylv^[k] x = 1 := by
  obtain ⟨x, hx, hx1⟩ := exists_sylv_iterate_pred_eq_one v
  refine ⟨sylv^[2 ^ v - 1 - k] x, ?_, ?_⟩
  · have h := φ_iterate_sylv_iterate (2 ^ v) (2 ^ v - 1 - k) x
    rw [φ_iterate, φ_iterate, hx] at h
    exact h
  · rw [← Function.iterate_add_apply, show k + (2 ^ v - 1 - k) = 2 ^ v - 1 by omega]
    exact hx1

/-- **The `𝔽_2` threshold.** `1 ∈ Im (F + 1)^k` on `𝔽_{2^d}` iff `k < 2^{v₂(d)}`. -/
theorem one_mem_sylv_iterate_image_iff {d : ℕ} (hd : d ≠ 0) (k : ℕ) :
    (∃ x : Lp 2, x ^ 2 ^ d = x ∧ sylv^[k] x = 1) ↔ k < 2 ^ padicValNat 2 d := by
  constructor
  · rintro ⟨x, hx, h⟩
    exact lt_two_pow_padicValNat_of_sylv_iterate_eq_one hd hx h
  · intro hk
    obtain ⟨x, hx, h⟩ := exists_sylv_iterate_eq_one_of_lt hk
    refine ⟨x, ?_, h⟩
    obtain ⟨m, hm⟩ := (pow_padicValNat_dvd : 2 ^ padicValNat 2 d ∣ d)
    have hper : Function.IsPeriodicPt (⇑(φ 2)) (2 ^ padicValNat 2 d) x := by
      show (⇑(φ 2))^[2 ^ padicValNat 2 d] x = x
      rw [φ_iterate]; exact hx
    have h' : (⇑(φ 2))^[2 ^ padicValNat 2 d * m] x = x := hper.mul_const m
    rw [φ_iterate, ← hm] at h'
    exact h'

/-- The sharp witness has Frobenius period exactly `2^v` (for `v ≥ 1`): the threshold is attained
by an element generating `𝔽_{2^{2^v}}`. -/
theorem exists_minimalPeriod_eq_two_pow (v : ℕ) (hv : 1 ≤ v) :
    ∃ x : Lp 2, Function.minimalPeriod (⇑(φ 2)) x = 2 ^ v ∧ sylv^[2 ^ v - 1] x = 1 := by
  obtain ⟨x, hx, hx1⟩ := exists_sylv_iterate_pred_eq_one v
  refine ⟨x, ?_, hx1⟩
  have hper : Function.IsPeriodicPt (⇑(φ 2)) (2 ^ v) x := by
    show (⇑(φ 2))^[2 ^ v] x = x
    rw [φ_iterate]; exact hx
  have hdvd1 : 2 ^ (v - 1 + 1) ∣ Function.minimalPeriod (⇑(φ 2)) x :=
    two_pow_succ_dvd_minimalPeriod_of_sylv_iterate_eq_one
      (show 2 ^ (v - 1) ≤ 2 ^ v - 1 by
        have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (Nat.sub_lt hv Nat.one_pos)
        rw [show v = v - 1 + 1 by omega, pow_succ] at this ⊢
        omega) hx1
  rw [Nat.sub_add_cancel hv] at hdvd1
  exact Nat.dvd_antisymm hper.minimalPeriod_dvd hdvd1

/-! ## 3. The Euclid sequence over `𝔽_2` -/

/-- `k` consecutive irreducible stages compose to `k` autonomous steps:
`P_{n+k} = sylvPoly^[k] P_n`. -/
theorem ffProd_add_of_run (d : FFEMData 2) (n k : ℕ)
    (h : ∀ j, j < k → Irreducible (d.ffProd (n + j) + 1)) :
    d.ffProd (n + k) = sylvPoly^[k] (d.ffProd n) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← add_assoc, ffProd_succ_of_irreducible d (n + k) (h k (Nat.lt_succ_self k)),
      ih (fun j hj => h j (by omega)), Function.iterate_succ_apply', sylvPoly]
    ring

/-- **Threshold for the Euclid sequence over `𝔽_2`, divisibility form.** After `k` consecutive
irreducible stages with `2^v ≤ k`, every irreducible factor of the next Euclid polynomial has
degree divisible by `2^{v+1}`. -/
theorem two_pow_succ_dvd_natDegree_of_run (d : FFEMData 2) (n k v : ℕ)
    (h : ∀ j, j < k → Irreducible (d.ffProd (n + j) + 1)) (hk : 2 ^ v ≤ k)
    {f : (ZMod 2)[X]} (hf : Irreducible f) (hdvd : f ∣ d.ffProd (n + k) + 1) :
    2 ^ (v + 1) ∣ f.natDegree := by
  rw [ffProd_add_of_run d n k h] at hdvd
  obtain ⟨β, hβ⟩ := exists_aeval_eq_zero 2 hf
  obtain ⟨g, hg⟩ := hdvd
  have hy : sylv^[k] (aeval β (d.ffProd n)) = 1 := by
    have := congrArg (aeval β) hg
    rw [map_mul, hβ, zero_mul, map_add, map_one, aeval_sylvPoly_iterate] at this
    linear_combination this - two_eq_zero_L
  exact (two_pow_succ_dvd_minimalPeriod_of_sylv_iterate_eq_one hk hy).trans
    (minimalPeriod_aeval_dvd_natDegree 2 hf hβ _)

/-- **Threshold for the Euclid sequence over `𝔽_2`, closed form.** After `k` consecutive
irreducible stages every irreducible factor `f` of the next Euclid polynomial satisfies
`k < 2^{v₂(deg f)}`. -/
theorem lt_two_pow_padicValNat_natDegree_of_run (d : FFEMData 2) (n k : ℕ)
    (h : ∀ j, j < k → Irreducible (d.ffProd (n + j) + 1))
    {f : (ZMod 2)[X]} (hf : Irreducible f) (hdvd : f ∣ d.ffProd (n + k) + 1) :
    k < 2 ^ padicValNat 2 f.natDegree := by
  by_contra hlt
  push Not at hlt
  have hpos : f.natDegree ≠ 0 :=
    (natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hf)).ne'
  exact pow_succ_padicValNat_not_dvd hpos (two_pow_succ_dvd_natDegree_of_run d n k _ h hlt hf hdvd)

/-- The selected factor after `k` consecutive irreducible stages has degree `D` with
`k < 2^{v₂(D)}`. -/
theorem ffSeq_lt_two_pow_padicValNat_of_run (d : FFEMData 2) (n k : ℕ)
    (h : ∀ j, j < k → Irreducible (d.ffProd (n + j) + 1)) :
    k < 2 ^ padicValNat 2 (d.ffSeq (n + k + 1)).natDegree := by
  obtain ⟨_, hirr, hdvd⟩ := d.ffSeq_succ (n + k)
  exact lt_two_pow_padicValNat_natDegree_of_run d n k h hirr hdvd

/-- The bound is attained by the actual `𝔽_2` sequence: the first three Euclid polynomials are
irreducible and the fourth has quartic factors, so `k = 3 = 2^{v₂(4)} - 1`. -/
theorem threshold_attained_at_three (d : FFEMData 2) :
    (∀ j, j < 3 → Irreducible (d.ffProd (0 + j) + 1)) ∧
      (X ^ 4 + X ^ 3 + 1 : (ZMod 2)[X]) ∣ d.ffProd (0 + 3) + 1 ∧
      (3 : ℕ) + 1 = 2 ^ padicValNat 2 (X ^ 4 + X ^ 3 + 1 : (ZMod 2)[X]).natDegree := by
  obtain ⟨h0, h1, h2, -⟩ := ff_two_attains_three d
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    interval_cases j <;> simpa
  · rw [zero_add, euclid_three_factor d]
    exact dvd_mul_right _ _
  · have hdeg : (X ^ 4 + X ^ 3 + 1 : (ZMod 2)[X]).natDegree = 4 := by
      compute_degree!
    rw [hdeg, show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
    norm_num

end AutonomousThreshold

end FunctionFieldAnalog
