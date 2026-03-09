import EM.VisitEquidistribution
import EM.MasterReduction

/-!
# Self-Correcting Drift for the EM Walk

## Overview

We define a Lyapunov function L(N) = sum_c (V_N(c) - N/(q-1))^2 measuring how far
the EM walk's visit counts deviate from uniform. The one-step identity

  L(N+1) = L(N) + 2 * d_{w(N)}(N) + (q-2)/(q-1)

decomposes the evolution into a drift term (visit deviation at current position)
and a constant correction. Telescoping:

  L(N) = 2 * R(N) + N * (q-2)/(q-1)

where R(N) = sum_{n<N} d_{w(n)}(n) is the cumulative drift.

**SelfCorrectingDrift** (SCD) asserts R(N) = o(N^2), which implies L(N) = o(N^2),
giving visit equidistribution and hence MC via the proved SVE -> MC chain.

## Key Results
* `visitDeviation_sum_zero`       -- deviations sum to 0
* `lyapunov_one_step`             -- one-step algebraic identity
* `lyapunov_telescope`            -- L(N) = 2*R(N) + linear term
* `scd_implies_ve`                -- SCD -> VisitEquidistribution
* `scd_implies_sve`               -- SCD -> SubquadraticVisitEnergy
* `scd_implies_mc`                -- SCD -> MC (with FiniteMCBelow)
* `group_walk_doubly_stochastic`  -- uniform mu gives doubly stochastic transitions
* `uniform_multiplier_zero_drift` -- zero expected drift under uniform multiplier
* `sve_implies_scd_above_threshold` -- SVE implies SCD for primes above the SVE threshold

## Equivalence with SVE (Dead End #120)

SCD is algebraically equivalent to SVE (SubquadraticVisitEnergy) for each fixed
prime q >= Q_0, via the Lyapunov telescope identity L(N) = 2*R(N) + O(N).
The quantifier structure differs: SCD quantifies over ALL primes, while SVE
only claims the bound for q >= Q_0. For the purpose of proving MC, both suffice
equally well (the threshold is handled via FiniteMCBelow).

SCD provides no new proof leverage beyond SVE. See Dead End #120.
-/

noncomputable section
open Classical
open Mullin Euclid MullinGroup RotorRouter
open scoped BigOperators

/-! ## Section 1: Definitions -/

section SelfCorrectingDefs

variable {q : ℕ} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)

/-- Visit deviation: V_N(a) - N/(q-1). -/
def visitDeviation (N : ℕ) (a : (ZMod q)ˣ) : ℝ :=
  (emVisitCount q hq hne a N : ℝ) - (N : ℝ) / ((q : ℝ) - 1)

/-- Lyapunov function: L(N) = sum_a (V_N(a) - N/(q-1))^2. -/
def lyapunov (N : ℕ) : ℝ :=
  ∑ a : (ZMod q)ˣ, (visitDeviation hq hne N a) ^ 2

/-- Cumulative drift: R(N) = sum_{n<N} d_{w(n)}(n). -/
def cumulativeDrift (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, visitDeviation hq hne n (emWalkUnit q hq hne n)

end SelfCorrectingDefs

/-! ## Section 2: Basic Properties -/

section BasicProperties

variable {q : ℕ} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)

/-- The Lyapunov function is nonneg (sum of squares). -/
theorem lyapunov_nonneg (N : ℕ) : 0 ≤ lyapunov hq hne N :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- At N=0, the Lyapunov function vanishes. -/
theorem lyapunov_zero : lyapunov hq hne 0 = 0 := by
  simp only [lyapunov, visitDeviation, emVisitCount, Finset.range_zero, Finset.filter_empty,
    Finset.card_empty, Nat.cast_zero, zero_div, sub_zero, sq, mul_zero,
    Finset.sum_const_zero]

end BasicProperties

/-! ## Section 3: Visit Count Sum and Deviation Sum -/

section VisitCountSum

variable {q : ℕ} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)

/-- Visit counts sum to N: each step n < N is counted in exactly one fiber. -/
theorem emVisitCount_sum (N : ℕ) :
    ∑ a : (ZMod q)ˣ, (emVisitCount q hq hne a N : ℝ) = (N : ℝ) := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Finset.range N) (t := Finset.univ)
    (f := fun n => emWalkUnit q hq hne n)
    (fun _ _ => Finset.mem_univ _)
  simp only [Finset.card_range] at h
  have key : (∑ a : (ZMod q)ˣ, emVisitCount q hq hne a N) = N := by
    simp only [emVisitCount]; exact h.symm
  exact_mod_cast key

/-- Visit deviations sum to zero. -/
theorem visitDeviation_sum_zero (N : ℕ) :
    ∑ a : (ZMod q)ˣ, visitDeviation hq hne N a = 0 := by
  simp only [visitDeviation]
  rw [Finset.sum_sub_distrib]
  rw [emVisitCount_sum hq hne N]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient,
    Nat.totient_prime (Fact.out : Nat.Prime q)]
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime q).one_lt
  have hq1_ne : (q : ℝ) - 1 ≠ 0 := by linarith
  rw [nsmul_eq_mul]
  push_cast [Nat.cast_sub (Nat.Prime.one_le (Fact.out : Nat.Prime q))]
  field_simp
  ring

end VisitCountSum

/-! ## Section 4: Visit Count Update Lemmas -/

section VisitCountUpdate

variable {q : ℕ} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)

/-- Visit count at the current position increases by 1. -/
theorem emVisitCount_succ_at (N : ℕ) :
    emVisitCount q hq hne (emWalkUnit q hq hne N) (N + 1) =
    emVisitCount q hq hne (emWalkUnit q hq hne N) N + 1 := by
  simp only [emVisitCount]
  rw [Finset.range_add_one, Finset.filter_insert, if_pos rfl]
  rw [Finset.card_insert_of_notMem]
  intro hmem
  simp only [Finset.mem_filter, Finset.mem_range] at hmem
  exact Nat.lt_irrefl N hmem.1

/-- Visit count at other positions stays the same. -/
theorem emVisitCount_succ_other (N : ℕ) {a : (ZMod q)ˣ}
    (ha : a ≠ emWalkUnit q hq hne N) :
    emVisitCount q hq hne a (N + 1) = emVisitCount q hq hne a N := by
  simp only [emVisitCount]
  rw [Finset.range_add_one, Finset.filter_insert, if_neg (fun h => ha h.symm)]

/-- Visit deviation at the current position: increases by (q-2)/(q-1). -/
theorem visitDeviation_succ_at (N : ℕ) :
    visitDeviation hq hne (N + 1) (emWalkUnit q hq hne N) =
    visitDeviation hq hne N (emWalkUnit q hq hne N) +
    ((q : ℝ) - 2) / ((q : ℝ) - 1) := by
  simp only [visitDeviation]
  rw [emVisitCount_succ_at hq hne N]
  have hq1 : (q : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime q).one_lt
    linarith
  push_cast
  field_simp
  ring

/-- Visit deviation at other positions: decreases by 1/(q-1). -/
theorem visitDeviation_succ_other (N : ℕ) {a : (ZMod q)ˣ}
    (ha : a ≠ emWalkUnit q hq hne N) :
    visitDeviation hq hne (N + 1) a =
    visitDeviation hq hne N a - 1 / ((q : ℝ) - 1) := by
  simp only [visitDeviation]
  rw [emVisitCount_succ_other hq hne N ha]
  have hq1 : (q : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime q).one_lt
    linarith
  push_cast
  field_simp
  ring

end VisitCountUpdate

/-! ## Section 5: Lyapunov One-Step Identity -/

section LyapunovOneStep

variable {q : ℕ} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)

/-- The sum of deviations over a =/= c equals the negation of the deviation at c. -/
private theorem deviation_sum_erase (N : ℕ) :
    ∑ a ∈ (Finset.univ : Finset (ZMod q)ˣ).erase (emWalkUnit q hq hne N),
      visitDeviation hq hne N a =
    -(visitDeviation hq hne N (emWalkUnit q hq hne N)) := by
  have htot := visitDeviation_sum_zero hq hne N
  have hsplit := Finset.sum_erase_eq_sub (f := visitDeviation hq hne N)
    (Finset.mem_univ (emWalkUnit q hq hne N))
  linarith [hsplit]

/-- **Lyapunov one-step identity**:
    L(N+1) = L(N) + 2 * d_c(N) + (q-2)/(q-1)
    where c = w(N) is the current walk position.

    Proof strategy: split univ = {c} ∪ (univ \ {c}), substitute the deviation
    updates, expand squares, use ∑_{a/=c} d_a = -d_c, and simplify. -/
theorem lyapunov_one_step (N : ℕ) :
    lyapunov hq hne (N + 1) =
    lyapunov hq hne N +
    2 * visitDeviation hq hne N (emWalkUnit q hq hne N) +
    ((q : ℝ) - 2) / ((q : ℝ) - 1) := by
  have hq1 : (q : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime q).one_lt
    linarith
  set c := emWalkUnit q hq hne N
  -- Suffices to show L(N+1) - L(N) = 2*d_c + (q-2)/(q-1)
  suffices h : lyapunov hq hne (N + 1) - lyapunov hq hne N =
      2 * visitDeviation hq hne N c + ((q : ℝ) - 2) / ((q : ℝ) - 1) by linarith
  -- L(N+1) - L(N) = ∑_a [(d_{N+1}(a))^2 - (d_N(a))^2]
  simp only [lyapunov]
  rw [← Finset.sum_sub_distrib]
  -- Split univ = {c} ∪ (univ \ {c})
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c)]
  -- For the c-term:
  have hc : visitDeviation hq hne (N + 1) c ^ 2 - visitDeviation hq hne N c ^ 2 =
      2 * visitDeviation hq hne N c * (((q : ℝ) - 2) / ((q : ℝ) - 1)) +
      (((q : ℝ) - 2) / ((q : ℝ) - 1)) ^ 2 := by
    rw [visitDeviation_succ_at hq hne N]; ring
  rw [hc]
  -- For a /= c terms:
  have ha_sum : ∑ a ∈ (Finset.univ : Finset (ZMod q)ˣ).erase c,
      (visitDeviation hq hne (N + 1) a ^ 2 - visitDeviation hq hne N a ^ 2) =
    -2 / ((q : ℝ) - 1) *
      ∑ a ∈ (Finset.univ : Finset (ZMod q)ˣ).erase c, visitDeviation hq hne N a +
    ((Finset.univ : Finset (ZMod q)ˣ).erase c).card * (1 / ((q : ℝ) - 1)) ^ 2 := by
    have expand : ∀ a ∈ (Finset.univ : Finset (ZMod q)ˣ).erase c,
        visitDeviation hq hne (N + 1) a ^ 2 - visitDeviation hq hne N a ^ 2 =
        -2 / ((q : ℝ) - 1) * visitDeviation hq hne N a +
        (1 / ((q : ℝ) - 1)) ^ 2 := by
      intro a ha
      rw [visitDeviation_succ_other hq hne N (Finset.ne_of_mem_erase ha)]
      field_simp; ring
    rw [Finset.sum_congr rfl expand, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [← Finset.mul_sum]
  rw [ha_sum]
  -- Substitute deviation_sum_erase and card
  have hdevsum := deviation_sum_erase hq hne N
  rw [hdevsum]
  have hcard : ((Finset.univ : Finset (ZMod q)ˣ).erase c).card = q - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : Nat.Prime q)]
    omega
  -- Now pure algebra with (q-1) ≠ 0, card = q-2
  push_cast [hcard, Nat.cast_sub (show 2 ≤ q from (Fact.out : Nat.Prime q).two_le)]
  field_simp
  ring

end LyapunovOneStep

/-! ## Section 6: Telescoping -/

section Telescoping

variable {q : ℕ} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)

/-- **Lyapunov telescoping**: L(N) = 2*R(N) + N*(q-2)/(q-1). -/
theorem lyapunov_telescope (N : ℕ) :
    lyapunov hq hne N =
    2 * cumulativeDrift hq hne N + (N : ℝ) * ((q : ℝ) - 2) / ((q : ℝ) - 1) := by
  induction N with
  | zero =>
    simp [lyapunov_zero, cumulativeDrift, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
    rw [lyapunov_one_step hq hne n, ih]
    simp only [cumulativeDrift, Finset.sum_range_succ]
    push_cast
    ring

end Telescoping

/-! ## Section 7: SCD Definition and Implications -/

section SelfCorrectingDriftDef

/-- **Self-Correcting Drift**: the cumulative visit-deviation correlation is subquadratic. -/
def SelfCorrectingDrift : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (ε : ℝ), 0 < ε →
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    |cumulativeDrift hq hne N| ≤ ε * (N : ℝ) ^ 2

end SelfCorrectingDriftDef

section SCDImplications

variable {q : ℕ} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)

/-- SCD implies the Lyapunov function is subquadratic. -/
theorem scd_implies_lyapunov_subquadratic (hscd : SelfCorrectingDrift) :
    ∀ (ε : ℝ), 0 < ε →
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      lyapunov hq hne N ≤ ε * (N : ℝ) ^ 2 := by
  intro ε hε
  -- Get the SCD bound with ε/4
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  obtain ⟨N₁, hN₁⟩ := hscd q hq hne (ε / 4) hε4
  -- For large N, the linear term N*(q-2)/(q-1) ≤ N ≤ (ε/2)*N^2
  -- Need N ≥ 2/ε so that (ε/2)*N ≥ 1, hence N ≤ (ε/2)*N^2
  set N₂ := Nat.ceil (2 / ε) + 1
  use max N₁ N₂
  intro N hN
  have hNN1 : N ≥ N₁ := le_of_max_le_left hN
  have hNN2 : N ≥ N₂ := le_of_max_le_right hN
  rw [lyapunov_telescope hq hne N]
  -- |R(N)| ≤ (ε/4)*N^2
  have hR := hN₁ N hNN1
  -- 2*R(N) ≤ 2*|R(N)| ≤ (ε/2)*N^2
  have hR_upper : 2 * cumulativeDrift hq hne N ≤ ε / 2 * (N : ℝ) ^ 2 := by
    have h1 : cumulativeDrift hq hne N ≤ |cumulativeDrift hq hne N| := le_abs_self _
    have h2 : |cumulativeDrift hq hne N| ≤ ε / 4 * (N : ℝ) ^ 2 := hR
    nlinarith
  -- N*(q-2)/(q-1) ≤ N
  have hq_pos : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime q).one_lt
    linarith
  have hfrac_le : ((q : ℝ) - 2) / ((q : ℝ) - 1) ≤ 1 := by
    rw [div_le_one hq_pos]; linarith
  have hN_pos : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hlinear : (N : ℝ) * ((q : ℝ) - 2) / ((q : ℝ) - 1) ≤ (N : ℝ) := by
    rw [mul_div_assoc]; exact mul_le_of_le_one_right hN_pos hfrac_le
  -- N ≤ (ε/2)*N^2 for large N
  have hN_ge : (N₂ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNN2
  have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : (1 : ℕ) ≤ N₂ := by omega
    exact_mod_cast le_trans this hNN2
  have hceil_le : 2 / ε ≤ (N : ℝ) := by
    calc 2 / ε ≤ ↑(Nat.ceil (2 / ε)) := Nat.le_ceil _
      _ ≤ (N₂ : ℝ) := by exact_mod_cast Nat.le_succ _
      _ ≤ (N : ℝ) := hN_ge
  have hN_large : (N : ℝ) ≤ ε / 2 * (N : ℝ) ^ 2 := by
    have hε_half_N : 1 ≤ ε / 2 * (N : ℝ) := by
      have h2ε : 2 / ε ≤ (N : ℝ) := hceil_le
      -- ε/2 * N ≥ ε/2 * (2/ε) = 1
      have := mul_le_mul_of_nonneg_left h2ε (le_of_lt (show (0 : ℝ) < ε / 2 by linarith))
      rw [show ε / 2 * (2 / ε) = 1 from by field_simp] at this
      linarith
    calc (N : ℝ) = 1 * (N : ℝ) := (one_mul _).symm
      _ ≤ (ε / 2 * (N : ℝ)) * (N : ℝ) :=
        mul_le_mul_of_nonneg_right hε_half_N hN_pos
      _ = ε / 2 * (N : ℝ) ^ 2 := by ring
  linarith

/-- Each individual squared deviation is at most the Lyapunov function. -/
theorem sq_visitDeviation_le_lyapunov (N : ℕ) (a : (ZMod q)ˣ) :
    (visitDeviation hq hne N a) ^ 2 ≤ lyapunov hq hne N :=
  Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ a)

end SCDImplications

/-! ## Section 8: SCD implies Visit Equidistribution -/

section SCDImpliesVE

/-- **SCD implies Visit Equidistribution.** -/
theorem scd_implies_ve (hscd : SelfCorrectingDrift) : VisitEquidistribution := by
  -- Use Q₀ = 3 (any prime q ≥ 3 has q-1 ≥ 2)
  use 3
  intro q inst hq_ge hq hne ε hε
  haveI : Fact (Nat.Prime q) := inst
  -- Get Lyapunov bound: L(N) ≤ ε^2 * N^2 for large N
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  obtain ⟨N₁, hN₁⟩ := scd_implies_lyapunov_subquadratic hq hne hscd (ε ^ 2) hε2
  use max N₁ 1
  intro N hN a
  have hNN1 : N ≥ N₁ := le_of_max_le_left hN
  have hN1 : N ≥ 1 := le_of_max_le_right hN
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  -- The VE statement uses the filter card, which is emVisitCount
  have hrewrite :
      ((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card =
      emVisitCount q hq hne a N := rfl
  rw [hrewrite]
  -- |emVisitCount/N - 1/(q-1)| = |visitDeviation / N|
  have hq1_ne : (q : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime q).one_lt
    linarith
  -- Rewrite as |visitDeviation / N|
  have hdev_eq : (emVisitCount q hq hne a N : ℝ) / (N : ℝ) - 1 / ((q : ℝ) - 1) =
      visitDeviation hq hne N a / (N : ℝ) := by
    simp only [visitDeviation]
    field_simp
  rw [hdev_eq, abs_div, abs_of_pos hN_pos]
  -- Need: |visitDeviation| / N ≤ ε, i.e. |visitDeviation| ≤ ε * N
  rw [div_le_iff₀ hN_pos]
  -- From: d^2 ≤ L(N) ≤ ε^2 * N^2 ≤ (ε*N)^2
  have hL := hN₁ N hNN1
  have hd2 := sq_visitDeviation_le_lyapunov hq hne N a
  have hd_sq_bound : (visitDeviation hq hne N a) ^ 2 ≤ (ε * (N : ℝ)) ^ 2 := by
    calc (visitDeviation hq hne N a) ^ 2 ≤ lyapunov hq hne N := hd2
      _ ≤ ε ^ 2 * (N : ℝ) ^ 2 := hL
      _ = (ε * (N : ℝ)) ^ 2 := by ring
  exact abs_le_of_sq_le_sq hd_sq_bound (by positivity)

end SCDImpliesVE

/-! ## Section 8b: Helper Bijection -/

section HelperBijection

variable {q : ℕ} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)

/-- Visit count bijection: walkVisitCount on Fin N equals emVisitCount on range N. -/
private theorem walkVisitCount_eq_emVisitCount (N : ℕ) (a : (ZMod q)ˣ) :
    walkVisitCount (fun (n : Fin N) => emWalkUnit q hq hne n.val) a =
    emVisitCount q hq hne a N := by
  simp only [walkVisitCount, emVisitCount]
  set s := Finset.univ.filter (fun n : Fin N => emWalkUnit q hq hne n.val = a)
  set t := (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)
  suffices h : s.map Fin.valEmbedding = t by rw [← h]; exact (Finset.card_map _).symm
  ext n
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_range, Fin.valEmbedding_apply, s, t]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i.isLt, hi⟩
  · intro ⟨hlt, heq⟩; exact ⟨⟨n, hlt⟩, heq, rfl⟩

end HelperBijection

/-! ## Section 9: SCD implies SVE and MC -/

section SCDImpliesMC

/-- **SCD implies SubquadraticVisitEnergy.** -/
theorem scd_implies_sve (hscd : SelfCorrectingDrift) : SubquadraticVisitEnergy := by
  -- SVE: exists Q₀, for q ≥ Q₀, for all ε > 0, exists N₀, for N ≥ N₀,
  --   excessEnergy w ≤ ε * N^2
  -- where w(n) = emWalkUnit(n) on Fin N.
  --
  -- excessEnergy w = (q-1) * ∑_a (V(a) - N/(q-1))^2 = (q-1) * lyapunov
  -- So if L(N) ≤ (ε/(q-1)) * N^2, then excessEnergy ≤ ε * N^2.
  -- SCD gives L(N) = o(N^2), so this works for any fixed q.
  use 3
  intro q inst hq_ge hq hne ε hε
  haveI : Fact (Nat.Prime q) := inst
  have hq1_pos : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime q).one_lt
    linarith
  have hε' : (0 : ℝ) < ε / ((q : ℝ) - 1) := div_pos hε hq1_pos
  obtain ⟨N₀, hN₀⟩ := scd_implies_lyapunov_subquadratic hq hne hscd
    (ε / ((q : ℝ) - 1)) hε'
  use N₀
  intro N hN
  -- excessEnergy = (q-1) * ∑(V - N/(q-1))^2
  have hp1 : 1 < q := (Fact.out : Nat.Prime q).one_lt
  rw [excessEnergy_eq_visit_deviation _ hp1]
  -- ∑(V - N/(q-1))^2 where V uses walkVisitCount on Fin N
  have hsum_eq :
      ∑ a : (ZMod q)ˣ,
        ((walkVisitCount (fun (n : Fin N) => emWalkUnit q hq hne n.val) a : ℝ) -
         (N : ℝ) / ((q : ℝ) - 1)) ^ 2 =
      ∑ a : (ZMod q)ˣ, (visitDeviation hq hne N a) ^ 2 := by
    simp only [visitDeviation, walkVisitCount_eq_emVisitCount hq hne N]
  rw [hsum_eq]
  -- Now: (q-1) * lyapunov ≤ (q-1) * (ε/(q-1)) * N^2 = ε * N^2
  change ((q : ℝ) - 1) * lyapunov hq hne N ≤ ε * (N : ℝ) ^ 2
  calc ((q : ℝ) - 1) * lyapunov hq hne N
      ≤ ((q : ℝ) - 1) * (ε / ((q : ℝ) - 1) * (N : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left (hN₀ N hN) (le_of_lt hq1_pos)
    _ = ε * (N : ℝ) ^ 2 := by field_simp

/-- **SCD implies MC**, assuming finite verification below the SVE threshold. -/
theorem scd_implies_mc (hscd : SelfCorrectingDrift)
    (hfin : FiniteMCBelow (sve_implies_mmcsb (scd_implies_sve hscd)).choose) :
    MullinConjecture :=
  sve_implies_mc (scd_implies_sve hscd) hfin

end SCDImpliesMC

/-! ## Section 9b: SVE implies SCD above threshold -/

section SVEImpliesSCD

/-- **SVE implies SCD above the SVE threshold**: for primes q ≥ Q₀, the cumulative
    drift R(N) is subquadratic. This is the converse direction of `scd_implies_sve`
    (modulo the threshold Q₀).

    Proof: SVE gives excessEnergy ≤ ε'·N². By `excessEnergy_eq_visit_deviation`,
    excessEnergy = (q-1)·L(N), so L(N) ≤ ε'·N²/(q-1) ≤ ε'·N².
    By `lyapunov_telescope`: 2·R(N) = L(N) - N·(q-2)/(q-1).
    Upper bound: R ≤ L/2 ≤ ε'/2·N².
    Lower bound: R ≥ -N·(q-2)/(2(q-1)) ≥ -N/2 ≥ -ε'/2·N² for large N.
    Choosing ε' = 2ε gives |R| ≤ ε·N². -/
theorem sve_implies_scd_above_threshold (hsve : SubquadraticVisitEnergy) :
    ∃ Q₀ : ℕ, ∀ (q : Nat) [Fact (Nat.Prime q)], q ≥ Q₀ →
    ∀ (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    ∀ (ε : ℝ), 0 < ε →
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |cumulativeDrift hq hne N| ≤ ε * (N : ℝ) ^ 2 := by
  obtain ⟨Q₀, hQ₀⟩ := hsve
  use Q₀
  intro q inst hq_ge hq hne ε hε
  haveI : Fact (Nat.Prime q) := inst
  -- Use SVE with ε' = 2ε
  have hε2 : (0 : ℝ) < 2 * ε := by linarith
  obtain ⟨N₁, hN₁⟩ := hQ₀ q hq_ge hq hne (2 * ε) hε2
  -- Need N ≥ 1/ε for the linear term bound
  set N₂ := Nat.ceil (1 / ε) + 1
  use max N₁ N₂
  intro N hN
  have hNN1 : N ≥ N₁ := le_of_max_le_left hN
  have hNN2 : N ≥ N₂ := le_of_max_le_right hN
  -- Basic facts about q
  have hp1 : 1 < q := (Fact.out : Nat.Prime q).one_lt
  have hq1_pos : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hp1
    linarith
  have hfrac_le : ((q : ℝ) - 2) / ((q : ℝ) - 1) ≤ 1 := by
    rw [div_le_one hq1_pos]; linarith
  have hfrac_nonneg : (0 : ℝ) ≤ ((q : ℝ) - 2) / ((q : ℝ) - 1) := by
    apply div_nonneg
    · have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime q).two_le
      linarith
    · linarith
  have hN_pos : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hSVE := hN₁ N hNN1
  rw [excessEnergy_eq_visit_deviation _ hp1] at hSVE
  simp only [walkVisitCount_eq_emVisitCount hq hne N] at hSVE
  -- So (q-1) * lyapunov ≤ 2ε * N²
  change ((q : ℝ) - 1) * lyapunov hq hne N ≤ 2 * ε * (N : ℝ) ^ 2 at hSVE
  -- Hence lyapunov ≤ 2ε * N² / (q-1) ≤ 2ε * N²
  have hq1_ge_one : (1 : ℝ) ≤ (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime q).two_le
    linarith
  have hL_bound : lyapunov hq hne N ≤ 2 * ε * (N : ℝ) ^ 2 := by
    have hL := lyapunov_nonneg hq hne N
    calc lyapunov hq hne N
        = lyapunov hq hne N * 1 := (mul_one _).symm
      _ ≤ lyapunov hq hne N * ((q : ℝ) - 1) :=
          mul_le_mul_of_nonneg_left hq1_ge_one hL
      _ = ((q : ℝ) - 1) * lyapunov hq hne N := by ring
      _ ≤ 2 * ε * (N : ℝ) ^ 2 := hSVE
  -- Step 2: Use lyapunov_telescope: L = 2R + N*(q-2)/(q-1)
  -- So 2R = L - N*(q-2)/(q-1)
  have htel := lyapunov_telescope hq hne N
  -- htel: L = 2R + N*(q-2)/(q-1)
  -- Upper bound on R: 2R = L - N*(q-2)/(q-1) ≤ L ≤ 2ε*N²
  have hR_upper : cumulativeDrift hq hne N ≤ ε * (N : ℝ) ^ 2 := by
    have h2R : 2 * cumulativeDrift hq hne N =
        lyapunov hq hne N - (N : ℝ) * ((q : ℝ) - 2) / ((q : ℝ) - 1) := by linarith
    have hlin_nonneg : (0 : ℝ) ≤ (N : ℝ) * ((q : ℝ) - 2) / ((q : ℝ) - 1) := by
      rw [mul_div_assoc]
      exact mul_nonneg hN_pos (div_nonneg (by linarith [hq1_ge_one]) (by linarith))
    have : 2 * cumulativeDrift hq hne N ≤ lyapunov hq hne N := by linarith
    have : 2 * cumulativeDrift hq hne N ≤ 2 * ε * (N : ℝ) ^ 2 := by linarith [hL_bound]
    linarith
  -- Lower bound on R: 2R = L - N*(q-2)/(q-1) ≥ 0 - N = -N
  -- And -N ≥ -ε*N² for N ≥ 1/ε
  have hR_lower : -(ε * (N : ℝ) ^ 2) ≤ cumulativeDrift hq hne N := by
    have h2R : 2 * cumulativeDrift hq hne N =
        lyapunov hq hne N - (N : ℝ) * ((q : ℝ) - 2) / ((q : ℝ) - 1) := by linarith
    have hL_nonneg := lyapunov_nonneg hq hne N
    have hlin_le_N : (N : ℝ) * ((q : ℝ) - 2) / ((q : ℝ) - 1) ≤ (N : ℝ) := by
      rw [mul_div_assoc]; exact mul_le_of_le_one_right hN_pos hfrac_le
    -- 2R ≥ 0 - N = -N
    have h2R_lower : -((N : ℝ)) ≤ 2 * cumulativeDrift hq hne N := by linarith
    -- N ≤ ε * N² for large N
    have hN_ge : (N₂ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNN2
    have hceil : 1 / ε ≤ (N : ℝ) := by
      calc 1 / ε ≤ ↑(Nat.ceil (1 / ε)) := Nat.le_ceil _
        _ ≤ (N₂ : ℝ) := by exact_mod_cast Nat.le_succ _
        _ ≤ (N : ℝ) := hN_ge
    have hN_sq : (N : ℝ) ≤ ε * (N : ℝ) ^ 2 := by
      have hεN : 1 ≤ ε * (N : ℝ) := by
        have := mul_le_mul_of_nonneg_left hceil (le_of_lt hε)
        rw [show ε * (1 / ε) = 1 from by field_simp] at this
        linarith
      calc (N : ℝ) = 1 * (N : ℝ) := (one_mul _).symm
        _ ≤ (ε * (N : ℝ)) * (N : ℝ) := mul_le_mul_of_nonneg_right hεN hN_pos
        _ = ε * (N : ℝ) ^ 2 := by ring
    -- -ε*N² ≤ -N ≤ -N/2 ≤ R
    linarith
  -- Combine: |R| ≤ ε * N²
  rw [abs_le]
  exact ⟨by linarith, hR_upper⟩

end SVEImpliesSCD

/-! ## Section 10: Doubly Stochastic and Zero Drift -/

section DoublyStochastic

/-- Group multiplication by a fixed element is a bijection, giving doubly stochastic
    transitions under uniform measure. -/
theorem group_walk_doubly_stochastic {G : Type*} [Fintype G] [Group G] [DecidableEq G]
    (μ : G → ℝ) (hμ_sum : ∑ g : G, μ g = 1) :
    ∀ b : G, ∑ a : G, μ (b * a⁻¹) = 1 := by
  intro b
  -- a ↦ b * a⁻¹ is a bijection on G (with inverse g ↦ g⁻¹ * b)
  let e : G ≃ G := {
    toFun := fun a => b * a⁻¹
    invFun := fun g => g⁻¹ * b
    left_inv := fun a => by group
    right_inv := fun g => by group
  }
  calc ∑ a : G, μ (b * a⁻¹) = ∑ a : G, μ (e a) := rfl
    _ = ∑ g : G, μ g := Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = 1 := hμ_sum

variable {q : ℕ} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)

/-- Under uniform multiplier measure, the expected drift is zero.
    This is because ∑_g visitDeviation(c*g) = ∑_a visitDeviation(a) = 0
    via the group bijection g ↦ c*g. -/
theorem uniform_multiplier_zero_drift (N : ℕ) (c : (ZMod q)ˣ) :
    (1 / ((q : ℝ) - 1)) * ∑ g : (ZMod q)ˣ, visitDeviation hq hne N (c * g) = 0 := by
  -- Reindex g ↦ c * g to get ∑_a visitDeviation a = 0
  let e : (ZMod q)ˣ ≃ (ZMod q)ˣ := {
    toFun := fun g => c * g
    invFun := fun a => c⁻¹ * a
    left_inv := fun g => by group
    right_inv := fun a => by group
  }
  have : ∑ g : (ZMod q)ˣ, visitDeviation hq hne N (c * g) =
      ∑ a : (ZMod q)ˣ, visitDeviation hq hne N a :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [this, visitDeviation_sum_zero hq hne N, mul_zero]

end DoublyStochastic

end
