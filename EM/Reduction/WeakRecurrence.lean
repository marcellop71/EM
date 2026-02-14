import EM.Reduction.SelfCorrecting
import EM.Reduction.Master

/-!
# Weak Recurrence Reductions

## Overview

We define hypotheses strictly weaker than SelfCorrectingDrift (SCD) that still
suffice for Mullin's Conjecture. The key insight: SCD requires R(N) = o(N²),
giving L(N) = o(N²) and V(a,N)/N → 1/(q-1). But MC only needs V(-1,N) → ∞,
which requires only L(N) = O(N).

## Hierarchy (strictly weaker going down)
```
SCD (R = o(N²))      LinearDrift (|R| ≤ CN)
     ↘                    ↕ (iff)
    MC ← VisitGrowth ← WeakVisitEquidist ← SublinearLyapunov
```
LinearDrift (O(N)) implies SCD (o(N²)) since O(N) ⊂ o(N²).
The value of LinearDrift is the threshold-free route through VisitGrowth → HH → MC,
which avoids the FiniteMCBelow threshold required by the SCD → VE → MC route.

## Key Results
* `linearDrift_iff_sublinearLyapunov`    — equivalence via telescope
* `sublinearLyapunov_implies_weakVE`     — Cauchy-Schwarz on L ≤ CN
* `weakVE_implies_visitGrowth`           — trivial
* `visitGrowth_implies_mc`               — via HittingHypothesis
* `linearDrift_implies_mc`               — end-to-end chain
* `cumulativeDrift_lower_bound`          — FREE: R(N) ≥ -N(q-2)/(2(q-1))
* `weak_recurrence_landscape`            — summary conjunction
-/

noncomputable section
open Classical
open Mullin Euclid MullinGroup RotorRouter
open scoped BigOperators

/-! ## Section 1: Definitions -/

section WeakDefs

/-- **LinearDrift**: the cumulative drift R(N) grows at most linearly.
    Strictly weaker than SCD (o(N²)). If |R(N)| ≤ C·N, then L(N) = O(N),
    hence visit deviations are O(√N), hence every class is visited Θ(N) times. -/
def LinearDrift : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, |cumulativeDrift hq hne N| ≤ C * (N : ℝ)

/-- **SublinearLyapunov**: the Lyapunov function L(N) grows at most linearly.
    Equivalent to LinearDrift via the telescope identity L = 2R + O(N). -/
def SublinearLyapunov : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, lyapunov hq hne N ≤ C * (N : ℝ)

/-- **VisitGrowth**: every residue class is visited infinitely often.
    Strictly weaker than VE (which requires V(a,N)/N → 1/(q-1)).
    VG only asks V(a,N) → ∞. -/
def VisitGrowth : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    ∀ a : (ZMod q)ˣ, Filter.Tendsto
      (fun N => (emVisitCount q hq hne a N : ℝ)) Filter.atTop Filter.atTop

/-- **WeakVisitEquidist**: V(a,N) ≥ c·N for some c > 0, eventually.
    Stronger than VG (linear lower bound), weaker than VE (exact rate 1/(q-1)). -/
def WeakVisitEquidist : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ (N : ℕ) in Filter.atTop,
      ∀ a : (ZMod q)ˣ, c * (N : ℝ) ≤ (emVisitCount q hq hne a N : ℝ)

end WeakDefs

/-! ## Section 2: LinearDrift ↔ SublinearLyapunov -/

section LDiffSL

/-- LinearDrift → SublinearLyapunov via L = 2R + N(q-2)/(q-1) ≤ 2CN + N. -/
theorem linearDrift_implies_sublinearLyapunov : LinearDrift → SublinearLyapunov := by
  intro hld q inst hq hne
  haveI : Fact (Nat.Prime q) := inst
  obtain ⟨C, hC_pos, hC⟩ := hld q hq hne
  refine ⟨2 * C + 1, by linarith, fun N => ?_⟩
  rw [lyapunov_telescope hq hne N]
  have hq1_pos : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime q).one_lt
    linarith
  have hfrac_le : ((q : ℝ) - 2) / ((q : ℝ) - 1) ≤ 1 := by
    rw [div_le_one hq1_pos]; linarith
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  -- 2 * R(N) ≤ 2 * |R(N)| ≤ 2 * C * N
  have hR := hC N
  have hR_upper : 2 * cumulativeDrift hq hne N ≤ 2 * C * (N : ℝ) := by
    have := le_abs_self (cumulativeDrift hq hne N)
    nlinarith
  -- N * (q-2)/(q-1) ≤ N
  have hlinear : (N : ℝ) * ((q : ℝ) - 2) / ((q : ℝ) - 1) ≤ (N : ℝ) := by
    rw [mul_div_assoc]; exact mul_le_of_le_one_right hN_nn hfrac_le
  linarith

/-- SublinearLyapunov → LinearDrift via 2R = L - N(q-2)/(q-1), with L ≥ 0.
    Upper: 2R = L - linear ≤ L ≤ CN.
    Lower: 2R = L - linear ≥ 0 - N ≥ -N. -/
theorem sublinearLyapunov_implies_linearDrift : SublinearLyapunov → LinearDrift := by
  intro hsl q inst hq hne
  haveI : Fact (Nat.Prime q) := inst
  obtain ⟨C, hC_pos, hC⟩ := hsl q hq hne
  refine ⟨(C + 1) / 2, by linarith, fun N => ?_⟩
  have htel := lyapunov_telescope hq hne N
  have hL := hC N
  have hL_nn := lyapunov_nonneg hq hne N
  have hq1_pos : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime q).one_lt
    linarith
  have hfrac_nn : (0 : ℝ) ≤ ((q : ℝ) - 2) / ((q : ℝ) - 1) := by
    apply div_nonneg
    · have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime q).two_le
      linarith
    · linarith
  have hfrac_le : ((q : ℝ) - 2) / ((q : ℝ) - 1) ≤ 1 := by
    rw [div_le_one hq1_pos]; linarith
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  -- From telescope: 2R = L - N*(q-2)/(q-1)
  have h2R : 2 * cumulativeDrift hq hne N =
      lyapunov hq hne N - (N : ℝ) * ((q : ℝ) - 2) / ((q : ℝ) - 1) := by linarith
  -- The linear term is nonneg and ≤ N
  have hlin_nn : (0 : ℝ) ≤ (N : ℝ) * ((q : ℝ) - 2) / ((q : ℝ) - 1) := by
    apply div_nonneg (mul_nonneg hN_nn _) (le_of_lt hq1_pos)
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime q).two_le
    linarith
  have hlin_le : (N : ℝ) * ((q : ℝ) - 2) / ((q : ℝ) - 1) ≤ (N : ℝ) := by
    rw [div_le_iff₀ hq1_pos]
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime q).two_le
    nlinarith
  -- Upper: 2R ≤ L ≤ CN
  have hR_upper : 2 * cumulativeDrift hq hne N ≤ C * (N : ℝ) := by
    rw [h2R]; linarith
  -- Lower: 2R ≥ -N (from L ≥ 0 and linear ≤ N)
  have hR_lower : -(N : ℝ) ≤ 2 * cumulativeDrift hq hne N := by
    rw [h2R]; linarith
  -- |2R| ≤ max(CN, N) ≤ (C+1)N
  rw [abs_le]
  constructor
  · -- -(C+1)/2 * N ≤ R
    nlinarith
  · -- R ≤ (C+1)/2 * N
    nlinarith

/-- LinearDrift ↔ SublinearLyapunov: the two formulations are equivalent. -/
theorem linearDrift_iff_sublinearLyapunov : LinearDrift ↔ SublinearLyapunov :=
  ⟨linearDrift_implies_sublinearLyapunov, sublinearLyapunov_implies_linearDrift⟩

end LDiffSL

/-! ## Section 3: SublinearLyapunov → WeakVE -/

section SLtoWVE

/-- **SublinearLyapunov → WeakVisitEquidist**: from L(N) ≤ CN, each visit count
    satisfies V(a,N) ≥ N/(2(q-1)) for large N.

    Proof by contradiction: if V < N/(2(q-1)) for some a at large N, then
    (V - N/(q-1))² ≥ (N/(2(q-1)))² = N²/(4(q-1)²). But (V - N/(q-1))² ≤
    L(N) ≤ CN, so N² ≤ 4C(q-1)²·N, contradicting N > 4C(q-1)². -/
theorem sublinearLyapunov_implies_weakVE : SublinearLyapunov → WeakVisitEquidist := by
  intro hsl q inst hq hne
  haveI : Fact (Nat.Prime q) := inst
  obtain ⟨C, hC_pos, hC⟩ := hsl q hq hne
  have hq1_pos : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime q).one_lt
    linarith
  set c := 1 / (2 * ((q : ℝ) - 1)) with hc_def
  have hc_pos : (0 : ℝ) < c := by positivity
  refine ⟨c, hc_pos, ?_⟩
  -- Threshold: N₀ = ⌈4C(q-1)²⌉ + 1
  set thr := Nat.ceil (4 * C * ((q : ℝ) - 1) ^ 2) + 1
  rw [Filter.eventually_atTop]
  refine ⟨thr, fun N hN a => ?_⟩
  -- Proof by contradiction: assume V(a,N) < c * N
  by_contra h_neg
  push Not at h_neg
  -- h_neg : (emVisitCount ... a N : ℝ) < c * (N : ℝ)
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg' N
  -- V(a,N) < c * N = N / (2(q-1))
  -- So visitDeviation = V - N/(q-1) < c*N - N/(q-1) = -c*N  (since 1/(q-1) = 2c)
  have h2c : 1 / ((q : ℝ) - 1) = 2 * c := by rw [hc_def]; field_simp
  have hdev_bound : visitDeviation hq hne N a < -(c * (N : ℝ)) := by
    simp only [visitDeviation]
    have hmean : (N : ℝ) / ((q : ℝ) - 1) = 2 * c * (N : ℝ) := by rw [← h2c]; field_simp
    linarith
  -- d < -cN implies d² > (cN)²
  have hdev_sq : (c * (N : ℝ)) ^ 2 < (visitDeviation hq hne N a) ^ 2 := by nlinarith
  -- But d² ≤ L(N) ≤ C * N
  have hd2_le := sq_visitDeviation_le_lyapunov hq hne N a
  have hCN := hC N
  -- So c² * N² < C * N, i.e., c² * N < C (for N > 0)
  have h_ineq : c ^ 2 * (N : ℝ) ^ 2 < C * (N : ℝ) := by linarith
  -- N ≥ thr ≥ 1
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    have : 1 ≤ thr := by omega
    exact_mod_cast show 0 < N by omega
  -- From h_ineq: c² * N² < C * N, and hN_pos: 0 < N
  -- Dividing: c² * N < C
  -- But N ≥ thr = ⌈4C(q-1)²⌉ + 1, so N > 4C(q-1)²
  -- And c = 1/(2(q-1)), so c² = 1/(4(q-1)²), so c² * N > c² * 4C(q-1)² = C. Contradiction.
  have hN_large : 4 * C * ((q : ℝ) - 1) ^ 2 < (N : ℝ) := by
    have hthr_le : thr ≤ N := hN
    have hceil : 4 * C * ((q : ℝ) - 1) ^ 2 ≤ ↑(Nat.ceil (4 * C * ((q : ℝ) - 1) ^ 2)) :=
      Nat.le_ceil _
    have : (Nat.ceil (4 * C * ((q : ℝ) - 1) ^ 2)) + 1 ≤ N := hthr_le
    have : (Nat.ceil (4 * C * ((q : ℝ) - 1) ^ 2) : ℝ) < (N : ℝ) := by exact_mod_cast this
    linarith
  -- c² * N > c² * 4C(q-1)² = C  (since c² = 1/(4(q-1)²))
  have hc_sq : c ^ 2 * (4 * C * ((q : ℝ) - 1) ^ 2) = C := by
    rw [hc_def]; field_simp; ring
  -- c² * N > C
  have hc2_pos : (0 : ℝ) < c ^ 2 := by positivity
  have : C < c ^ 2 * (N : ℝ) := by nlinarith [hc_sq, hN_large, hc2_pos]
  -- But c² * N² < C * N implies c² * N < C (dividing by N > 0)
  have : c ^ 2 * (N : ℝ) < C := by nlinarith
  linarith

end SLtoWVE

/-! ## Section 4: WeakVE → VisitGrowth → MC -/

section VGtoMC

/-- WeakVE → VisitGrowth: linear lower bound trivially implies divergence. -/
theorem weakVE_implies_visitGrowth : WeakVisitEquidist → VisitGrowth := by
  intro hwve q inst hq hne a
  haveI : Fact (Nat.Prime q) := inst
  obtain ⟨c, hc_pos, hev⟩ := hwve q hq hne
  rw [Filter.tendsto_atTop_atTop]
  intro b
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N₁, hN₁⟩ := hev
  set N₂ := Nat.ceil (b / c) + 1
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  have hNN1 : N₁ ≤ N := le_of_max_le_left hN
  have hNN2 : N₂ ≤ N := le_of_max_le_right hN
  have hVa := hN₁ N hNN1 a
  calc b = c * (b / c) := by field_simp
    _ ≤ c * ↑(Nat.ceil (b / c)) := by
        exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (le_of_lt hc_pos)
    _ ≤ c * (N₂ : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hc_pos)
        exact_mod_cast Nat.le_succ _
    _ ≤ c * (N : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hc_pos)
        exact_mod_cast hNN2
    _ ≤ (emVisitCount q hq hne a N : ℝ) := hVa

/-- Helper: if emVisitCount exceeds N₀, there is a visit at index ≥ N₀.
    Pure combinatorics: the filter set has more elements than can fit below N₀. -/
private theorem exists_visit_past_bound {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (a : (ZMod q)ˣ) (N₀ N : Nat)
    (_ : N₀ ≤ N)
    (hcount : N₀ < emVisitCount q hq hne a N) :
    ∃ n, N₀ ≤ n ∧ n < N ∧ emWalkUnit q hq hne n = a := by
  by_contra h_none
  push Not at h_none
  -- All visits must be at indices < N₀
  have hsub : (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)
      ⊆ Finset.range N₀ := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    by_contra hge
    push Not at hge
    exact h_none n hge hn.1 hn.2
  have hcard_le := Finset.card_le_card hsub
  simp only [Finset.card_range] at hcard_le
  simp only [emVisitCount] at hcount
  omega

/-- Helper: emWalkUnit = -1 implies q | prod(n) + 1 via the walk bridge.
    emWalkUnit is defined as Units.mk0 (walkZ q n) _, so its coercion to
    ZMod q equals walkZ q n. When this equals -1, walkZ_eq_neg_one_iff gives
    the divisibility. -/
private theorem emWalkUnit_neg_one_dvd {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (n : Nat)
    (h : emWalkUnit q hq hne n = (-1 : (ZMod q)ˣ)) :
    q ∣ prod n + 1 := by
  rw [← walkZ_eq_neg_one_iff]
  -- emWalkUnit = Units.mk0 (walkZ q n) _, so (emWalkUnit).val = walkZ q n
  have : (emWalkUnit q hq hne n).val = walkZ q n := rfl
  rw [← this]
  -- h : emWalkUnit = -1 as units, so .val = (-1 : units).val = -1
  simp [h]

/-- **VisitGrowth → HittingHypothesis**: for each missing prime q,
    V(-1, N) → ∞ gives cofinal hits. -/
theorem visitGrowth_implies_hh : VisitGrowth → HittingHypothesis := by
  intro hvg q hq hne N₀
  haveI : Fact (Nat.Prime q) := ⟨IsPrime.toNatPrime hq⟩
  have htend := hvg q hq hne (-1 : (ZMod q)ˣ)
  rw [Filter.tendsto_atTop_atTop] at htend
  obtain ⟨N₁, hN₁⟩ := htend ((N₀ + 1 : ℕ) : ℝ)
  set N := max N₁ (N₀ + 1) with hN_def
  have hN_ge₁ : N₁ ≤ N := le_max_left _ _
  have hN_ge₀ : N₀ + 1 ≤ N := le_max_right _ _
  have hcount_real := hN₁ N hN_ge₁
  -- hcount_real : ↑(N₀ + 1) ≤ ↑(emVisitCount ...)
  have hcount_nat : N₀ < emVisitCount q hq hne (-1) N := by
    have : N₀ + 1 ≤ emVisitCount q hq hne (-1) N := by exact_mod_cast hcount_real
    omega
  obtain ⟨n, hn_ge, _, hn_walk⟩ :=
    exists_visit_past_bound hq hne (-1) N₀ N (by omega) hcount_nat
  exact ⟨n, hn_ge, emWalkUnit_neg_one_dvd hq hne n hn_walk⟩

/-- **VisitGrowth → MC**: via HittingHypothesis. -/
theorem visitGrowth_implies_mc : VisitGrowth → MullinConjecture :=
  fun hvg => hh_implies_mullin (visitGrowth_implies_hh hvg)

end VGtoMC

/-! ## Section 5: End-to-End Chains -/

section Chains

/-- The end-to-end chain: LinearDrift → MC. -/
theorem linearDrift_implies_mc : LinearDrift → MullinConjecture :=
  fun hld =>
    visitGrowth_implies_mc
      (weakVE_implies_visitGrowth
        (sublinearLyapunov_implies_weakVE
          (linearDrift_implies_sublinearLyapunov hld)))

/-- WeakVE → MC: the intermediate chain. -/
theorem weakVE_implies_mc : WeakVisitEquidist → MullinConjecture :=
  fun hwve => visitGrowth_implies_mc (weakVE_implies_visitGrowth hwve)

/-- SCD and LD both imply MC independently. SCD goes through SVE;
    LD goes through VG. They are logically independent hypotheses
    (o(N²) and O(N) are incomparable growth classes). -/
theorem scd_and_ld_both_imply_mc :
    (SelfCorrectingDrift → ∃ Q₀, FiniteMCBelow Q₀ → MullinConjecture) ∧
    (LinearDrift → MullinConjecture) := by
  exact ⟨fun hscd => ⟨_, scd_implies_mc hscd⟩, linearDrift_implies_mc⟩

end Chains

/-! ## Section 6: Free Lower Bound on Cumulative Drift -/

section FreeBound

variable {q : ℕ} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)

/-- **Free lower bound**: R(N) ≥ -N(q-2)/(2(q-1)).
    Follows from L(N) ≥ 0 and the telescope L = 2R + N(q-2)/(q-1).
    This is unconditional — no hypothesis needed. -/
theorem cumulativeDrift_lower_bound (N : ℕ) :
    -((N : ℝ) * ((q : ℝ) - 2) / (2 * ((q : ℝ) - 1))) ≤ cumulativeDrift hq hne N := by
  have hL := lyapunov_nonneg hq hne N
  have htel := lyapunov_telescope hq hne N
  have hq1_pos : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime q).one_lt
    linarith
  -- From L ≥ 0 and telescope: 0 ≤ 2R + N(q-2)/(q-1)
  -- Also: N(q-2)/(q-1) = 2 * (N(q-2)/(2(q-1)))
  have key : (N : ℝ) * ((q : ℝ) - 2) / ((q : ℝ) - 1) =
      2 * ((N : ℝ) * ((q : ℝ) - 2) / (2 * ((q : ℝ) - 1))) := by
    field_simp
  -- So 0 ≤ 2R + 2*(N(q-2)/(2(q-1))), i.e., 0 ≤ 2*(R + N(q-2)/(2(q-1)))
  -- Hence R + N(q-2)/(2(q-1)) ≥ 0, i.e., R ≥ -N(q-2)/(2(q-1))
  linarith

/-- **The upper bound is the only gap**: any upper bound R(N) ≤ C·N implies MC.
    The lower bound R(N) ≥ -N/2 is free from L ≥ 0. -/
theorem upper_drift_bound_implies_mc
    (hupper : ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, cumulativeDrift hq hne N ≤ C * (N : ℝ)) :
    MullinConjecture := by
  apply linearDrift_implies_mc
  intro q inst hq hne
  haveI : Fact (Nat.Prime q) := inst
  obtain ⟨C, hC_pos, hC⟩ := hupper q hq hne
  have hq1_pos : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime q).one_lt
    linarith
  have hfrac_le : ((q : ℝ) - 2) / (2 * ((q : ℝ) - 1)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [(Fact.out : Nat.Prime q).two_le]
  refine ⟨max C 1, by positivity, fun N => ?_⟩
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  rw [abs_le]
  constructor
  · -- Lower: R ≥ -N(q-2)/(2(q-1)) ≥ -N ≥ -max(C,1)*N
    have hlb := cumulativeDrift_lower_bound hq hne N
    calc -(max C 1 * (N : ℝ)) ≤ -(1 * (N : ℝ)) := by
          apply neg_le_neg; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hN_nn
      _ = -(N : ℝ) := by ring
      _ ≤ -((N : ℝ) * ((q : ℝ) - 2) / (2 * ((q : ℝ) - 1))) := by
          rw [neg_le_neg_iff, mul_div_assoc]
          exact mul_le_of_le_one_right hN_nn hfrac_le
      _ ≤ cumulativeDrift hq hne N := hlb
  · -- Upper: R ≤ C * N ≤ max(C,1) * N
    calc cumulativeDrift hq hne N ≤ C * (N : ℝ) := hC N
      _ ≤ max C 1 * (N : ℝ) := mul_le_mul_of_nonneg_right (le_max_left _ _) hN_nn

end FreeBound

/-! ## Section 7: Landscape Theorem -/

section Landscape

/-- **Weak recurrence landscape**: summary of all proved chains. -/
theorem weak_recurrence_landscape :
    -- Chain 1: LD ↔ SL → WVE → VG → MC
    (LinearDrift ↔ SublinearLyapunov) ∧
    (SublinearLyapunov → WeakVisitEquidist) ∧
    (WeakVisitEquidist → VisitGrowth) ∧
    (VisitGrowth → MullinConjecture) ∧
    -- Chain 2: LD → MC (end-to-end)
    (LinearDrift → MullinConjecture) ∧
    -- Chain 3: VG → HH → MC (factoring through HittingHypothesis)
    (VisitGrowth → HittingHypothesis) :=
  ⟨linearDrift_iff_sublinearLyapunov,
   sublinearLyapunov_implies_weakVE,
   weakVE_implies_visitGrowth,
   visitGrowth_implies_mc,
   linearDrift_implies_mc,
   visitGrowth_implies_hh⟩

end Landscape

end
