import EM.Stochastic.MixedTree

/-!
# The order of vanishing in `ε` of the capture probability

Under the mixture "`ε`·uniform + `(1-ε)`·greedy" started at `m`, let
`capProb ε q m N` be the probability that `q` is selected within the first `N` steps.
A **detour** is a step that does not take the least prime factor. `CapWithin q N d m` says
that some branch from `m` selects `q` within `N` steps using at most `d` detours (the
selecting step counts as a detour unless `q` is the least prime factor there).

## Main results (fixed horizon `N`, all `0 < ε ≤ 1`)

* `capProb_le_of_not_capWithin` — if no branch selects `q` within `N` steps with `≤ d`
  detours, then `capProb ε q m N ≤ 3^N · ε^(d+1)`.
* `exists_le_capProb_of_capWithin` — if some branch does, then `c · ε^d ≤ capProb ε q m N`
  for a constant `c > 0` independent of `ε`.
* `capProb_order` — hence if `d` is the least number of detours with which `q` can be
  selected within `N` steps, `c · ε^d ≤ capProb ε q m N ≤ C · ε^d`.
* `capWithin_zero_two_iff` — with no detour, from `2`: `q` is one of `seq 1, …, seq N`.
* `mem_seq_iff_capProb_bounded_below` — `q` is among `seq 1, …, seq N` iff the capture
  probability within `N` steps stays bounded away from `0` as `ε → 0`. This is the precise
  sense in which the Euclid–Mullin sequence is the `ε → 0` limit of the mixture.
* `mixedMC_iff_exists_capWithin` — `MixedMC q` iff `CapWithin q N d 2` for some `N`, `d`.

## Scope

The statement is for a **fixed horizon**. The constant `3^N` grows with `N`, and it must:
for fixed `ε > 0` the process has unboundedly many chances to detour, so the probability of
*ever* selecting `q` is not `O(ε^d)` uniformly in `N`. Nothing here bounds the least number
of detours for any particular `q`.
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

namespace MixedTree

/-! ## Definitions -/

/-- `CapWithin q N d m`: some branch of the Euclid tree from `m` selects `q` within `N`
    steps using at most `d` detours. -/
def CapWithin (q : ℕ) : ℕ → ℕ → ℕ → Prop
  | 0, _, _ => False
  | n + 1, d, m =>
      (q ∣ m + 1 ∧ (q = (m + 1).minFac ∨ 1 ≤ d)) ∨
      ((m + 1).minFac ≠ q ∧ CapWithin q n d (m * (m + 1).minFac)) ∨
      (∃ p ∈ (m + 1).primeFactors, p ≠ q ∧ p ≠ (m + 1).minFac ∧ 1 ≤ d ∧
        CapWithin q n (d - 1) (m * p))

theorem capWithin_succ (q n d m : ℕ) :
    CapWithin q (n + 1) d m ↔
      (q ∣ m + 1 ∧ (q = (m + 1).minFac ∨ 1 ≤ d)) ∨
      ((m + 1).minFac ≠ q ∧ CapWithin q n d (m * (m + 1).minFac)) ∨
      (∃ p ∈ (m + 1).primeFactors, p ≠ q ∧ p ≠ (m + 1).minFac ∧ 1 ≤ d ∧
        CapWithin q n (d - 1) (m * p)) := Iff.rfl

/-- The probability that the `ε`-mixture from `m` selects `q` within `N` steps. -/
def capProb (ε : ℝ) (q m N : ℕ) : ℝ := 1 - failWeightK (epsStepWeight ε) q m N

/-! ## Basic facts -/

section Basic

variable {ε : ℝ} {q m : ℕ}

theorem capProb_zero (ε : ℝ) (q m : ℕ) : capProb ε q m 0 = 0 := by simp [capProb]

theorem capProb_nonneg (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hm : 1 ≤ m) (N : ℕ) :
    0 ≤ capProb ε q m N :=
  sub_nonneg.mpr (failWeightK_le_one (isKernel_epsStepWeight hε0 hε1) q N m hm)

theorem capProb_le_one (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (N : ℕ) : capProb ε q m N ≤ 1 := by
  have := failWeightK_nonneg (isKernel_epsStepWeight hε0 hε1) q N m
  unfold capProb
  linarith

private theorem omega_pos' (hm : 1 ≤ m) : (0 : ℝ) < ((m + 1).primeFactors.card : ℝ) :=
  Nat.cast_pos.mpr (Nat.nonempty_primeFactors.mpr (by omega)).card_pos

private theorem one_le_omega (hm : 1 ≤ m) : (1 : ℝ) ≤ ((m + 1).primeFactors.card : ℝ) := by
  have : 1 ≤ (m + 1).primeFactors.card := (Nat.nonempty_primeFactors.mpr (by omega)).card_pos
  exact_mod_cast this

private theorem minFac_mem (hm : 1 ≤ m) : (m + 1).minFac ∈ (m + 1).primeFactors :=
  Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd _, by omega⟩

/-- A prime factor other than the least has weight exactly `ε / ω`. -/
theorem epsStepWeight_of_ne_minFac {p : ℕ} (hp : p ∈ (m + 1).primeFactors)
    (hne : p ≠ (m + 1).minFac) :
    epsStepWeight ε m p = ε / ((m + 1).primeFactors.card : ℝ) := by
  simp [epsStepWeight, hp, hne]

/-- The least prime factor has weight at least `1 / ω`, uniformly in `ε ∈ [0, 1]`. -/
theorem epsStepWeight_minFac_ge_inv (_hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hm : 1 ≤ m) :
    1 / ((m + 1).primeFactors.card : ℝ) ≤ epsStepWeight ε m (m + 1).minFac := by
  have hW := omega_pos' hm
  have hW1 := one_le_omega hm
  have hval : epsStepWeight ε m (m + 1).minFac =
      (1 - ε) + ε / ((m + 1).primeFactors.card : ℝ) := by
    simp [epsStepWeight, minFac_mem hm]
  have h1 : 1 / ((m + 1).primeFactors.card : ℝ) ≤ 1 := by
    rw [div_le_one hW]; exact hW1
  have hid : (1 - ε) + ε / ((m + 1).primeFactors.card : ℝ)
      - 1 / ((m + 1).primeFactors.card : ℝ)
      = (1 - ε) * (1 - 1 / ((m + 1).primeFactors.card : ℝ)) := by
    field_simp
    ring
  rw [hval]
  nlinarith [mul_nonneg (sub_nonneg.mpr hε1) (sub_nonneg.mpr h1)]

/-- **One-step recursion** for the capture probability. -/
theorem capProb_succ (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hm : 1 ≤ m) (n : ℕ) :
    capProb ε q m (n + 1) =
      (if q ∈ (m + 1).primeFactors then epsStepWeight ε m q else 0) +
        ∑ p ∈ (m + 1).primeFactors.erase q, epsStepWeight ε m p * capProb ε q (m * p) n := by
  have hK := isKernel_epsStepWeight hε0 hε1
  have hsum : (if q ∈ (m + 1).primeFactors then epsStepWeight ε m q else 0) +
      ∑ p ∈ (m + 1).primeFactors.erase q, epsStepWeight ε m p = 1 := by
    rw [← hK.2 m hm]
    split_ifs with hq
    · exact Finset.add_sum_erase _ (epsStepWeight ε m) hq
    · rw [Finset.erase_eq_of_notMem hq, zero_add]
  unfold capProb
  rw [failWeightK_succ]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  linarith

end Basic

/-! ## Upper bound -/

/-- **Upper bound.** If no branch from `m` selects `q` within `N` steps using at most `d`
    detours, the capture probability within `N` steps is at most `3^N · ε^(d+1)`. -/
theorem capProb_le_of_not_capWithin {q : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∀ N d m, 1 ≤ m → ¬ CapWithin q N d m → capProb ε q m N ≤ 3 ^ N * ε ^ (d + 1) := by
  have hK := isKernel_epsStepWeight hε0 hε1
  intro N
  induction N with
  | zero =>
    intro d m _ _
    rw [capProb_zero]
    exact mul_nonneg (by positivity) (pow_nonneg hε0 _)
  | succ n ih =>
    intro d m hm hnot
    have hA : ¬ (q ∣ m + 1 ∧ (q = (m + 1).minFac ∨ 1 ≤ d)) := fun h => hnot (Or.inl h)
    have hB : (m + 1).minFac ≠ q → ¬ CapWithin q n d (m * (m + 1).minFac) :=
      fun h1 h2 => hnot (Or.inr (Or.inl ⟨h1, h2⟩))
    have hC : ∀ p ∈ (m + 1).primeFactors, p ≠ q → p ≠ (m + 1).minFac → 1 ≤ d →
        ¬ CapWithin q n (d - 1) (m * p) :=
      fun p hp h1 h2 h3 h4 => hnot (Or.inr (Or.inr ⟨p, hp, h1, h2, h3, h4⟩))
    have hW := omega_pos' hm
    have hW1 := one_le_omega hm
    have h3n : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
    have hX : 0 ≤ ε ^ (d + 1) := pow_nonneg hε0 _
    have hF : 0 ≤ (3 : ℝ) ^ n * ε ^ (d + 1) := mul_nonneg (by positivity) hX
    have hE : 0 ≤ ε / ((m + 1).primeFactors.card : ℝ) * (3 ^ n * ε ^ d) :=
      mul_nonneg (div_nonneg hε0 hW.le) (mul_nonneg (by positivity) (pow_nonneg hε0 _))
    rw [capProb_succ hε0 hε1 hm]
    -- the term for selecting `q` now
    have hT0 : (if q ∈ (m + 1).primeFactors then epsStepWeight ε m q else 0) ≤ ε ^ (d + 1) := by
      split_ifs with hq
      · have hqd := Nat.dvd_of_mem_primeFactors hq
        have hne : q ≠ (m + 1).minFac := fun h => hA ⟨hqd, Or.inl h⟩
        have hd0 : d = 0 := by
          by_contra h
          exact hA ⟨hqd, Or.inr (Nat.one_le_iff_ne_zero.mpr h)⟩
        rw [epsStepWeight_of_ne_minFac hq hne, hd0, zero_add, pow_one]
        exact div_le_self hε0 hW1
      · exact hX
    -- each child
    have hterm : ∀ p ∈ (m + 1).primeFactors.erase q,
        epsStepWeight ε m p * capProb ε q (m * p) n ≤
          (if p = (m + 1).minFac then 3 ^ n * ε ^ (d + 1) else 0) +
            ε / ((m + 1).primeFactors.card : ℝ) * (3 ^ n * ε ^ d) := by
      intro p hp
      obtain ⟨hpq, hpf⟩ := Finset.mem_erase.mp hp
      have hpp := Nat.prime_of_mem_primeFactors hpf
      have hmp : 1 ≤ m * p := by have := hpp.two_le; nlinarith
      have hc0 : 0 ≤ capProb ε q (m * p) n := capProb_nonneg hε0 hε1 hmp n
      by_cases hmin : p = (m + 1).minFac
      · rw [if_pos hmin]
        have hchild : capProb ε q (m * p) n ≤ 3 ^ n * ε ^ (d + 1) := by
          refine ih d (m * p) hmp ?_
          rw [hmin]
          exact hB (fun h => hpq (hmin.trans h))
        have hw1 : epsStepWeight ε m p ≤ 1 := epsStepWeight_le_one hε0 hε1 hm
        have h1 : epsStepWeight ε m p * capProb ε q (m * p) n ≤ 1 * capProb ε q (m * p) n :=
          mul_le_mul_of_nonneg_right hw1 hc0
        linarith
      · rw [if_neg hmin, zero_add, epsStepWeight_of_ne_minFac hpf hmin]
        refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hε0 hW.le)
        rcases Nat.eq_zero_or_pos d with hd | hd
        · rw [hd, pow_zero, mul_one]
          exact (capProb_le_one hε0 hε1 n).trans h3n
        · have := ih (d - 1) (m * p) hmp (hC p hpf hpq hmin hd)
          rwa [Nat.sub_add_cancel hd] at this
    have hsum : ∑ p ∈ (m + 1).primeFactors.erase q,
        epsStepWeight ε m p * capProb ε q (m * p) n ≤
          3 ^ n * ε ^ (d + 1) + 3 ^ n * ε ^ (d + 1) := by
      calc ∑ p ∈ (m + 1).primeFactors.erase q, epsStepWeight ε m p * capProb ε q (m * p) n
          ≤ ∑ p ∈ (m + 1).primeFactors.erase q,
              ((if p = (m + 1).minFac then 3 ^ n * ε ^ (d + 1) else 0) +
                ε / ((m + 1).primeFactors.card : ℝ) * (3 ^ n * ε ^ d)) :=
            Finset.sum_le_sum hterm
        _ ≤ ∑ p ∈ (m + 1).primeFactors,
              ((if p = (m + 1).minFac then 3 ^ n * ε ^ (d + 1) else 0) +
                ε / ((m + 1).primeFactors.card : ℝ) * (3 ^ n * ε ^ d)) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_
            intro p _ _
            refine add_nonneg ?_ hE
            split_ifs
            · exact hF
            · exact le_rfl
        _ = (if (m + 1).minFac ∈ (m + 1).primeFactors then 3 ^ n * ε ^ (d + 1) else 0) +
              (m + 1).primeFactors.card •
                (ε / ((m + 1).primeFactors.card : ℝ) * (3 ^ n * ε ^ d)) := by
            rw [Finset.sum_add_distrib,
              Finset.sum_ite_eq' _ _ (fun _ => (3 : ℝ) ^ n * ε ^ (d + 1)), Finset.sum_const]
        _ ≤ 3 ^ n * ε ^ (d + 1) + 3 ^ n * ε ^ (d + 1) := by
            have h1 : (if (m + 1).minFac ∈ (m + 1).primeFactors
                then (3 : ℝ) ^ n * ε ^ (d + 1) else 0) ≤ 3 ^ n * ε ^ (d + 1) := by
              split_ifs
              · exact le_rfl
              · exact hF
            have hWε : ((m + 1).primeFactors.card : ℝ) *
                (ε / ((m + 1).primeFactors.card : ℝ)) = ε := by
              field_simp
            have h2 : (m + 1).primeFactors.card •
                (ε / ((m + 1).primeFactors.card : ℝ) * (3 ^ n * ε ^ d)) =
                  3 ^ n * ε ^ (d + 1) := by
              rw [nsmul_eq_mul, ← mul_assoc, hWε]
              ring
            linarith
    have hstep : ε ^ (d + 1) ≤ 3 ^ n * ε ^ (d + 1) := by
      have := mul_le_mul_of_nonneg_right h3n hX
      linarith
    have hpow : (3 : ℝ) ^ (n + 1) * ε ^ (d + 1) = 3 * (3 ^ n * ε ^ (d + 1)) := by ring
    rw [hpow]
    linarith

/-! ## Lower bound -/

/-- **Lower bound.** If some branch from `m` selects `q` within `N` steps using at most `d`
    detours, the capture probability within `N` steps is at least `c · ε^d`, with `c > 0`
    independent of `ε ∈ (0, 1]`. -/
theorem exists_le_capProb_of_capWithin {q : ℕ} (hq : q.Prime) :
    ∀ N d m, 1 ≤ m → CapWithin q N d m →
      ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → c * ε ^ d ≤ capProb ε q m N := by
  intro N
  induction N with
  | zero => intro d m _ h; exact absurd h id
  | succ n ih =>
    intro d m hm h
    have hW := omega_pos' hm
    have hinv : (0 : ℝ) < 1 / ((m + 1).primeFactors.card : ℝ) := one_div_pos.mpr hW
    have hT0 : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        0 ≤ (if q ∈ (m + 1).primeFactors then epsStepWeight ε m q else 0) := by
      intro ε h0 h1
      split_ifs
      · exact epsStepWeight_nonneg h0.le h1
      · exact le_rfl
    have hnn : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ p ∈ (m + 1).primeFactors.erase q,
        0 ≤ epsStepWeight ε m p * capProb ε q (m * p) n := by
      intro ε h0 h1 p hp
      have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
      have hmp : 1 ≤ m * p := by have := hpp.two_le; nlinarith
      exact mul_nonneg (epsStepWeight_nonneg h0.le h1) (capProb_nonneg h0.le h1 hmp n)
    rcases h with ⟨hqd, hor⟩ | ⟨hne, hch⟩ | ⟨p, hp, hpq, hpmin, hd, hch⟩
    · -- select `q` now
      refine ⟨1 / ((m + 1).primeFactors.card : ℝ), hinv, fun ε h0 h1 => ?_⟩
      have hqmem : q ∈ (m + 1).primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqd, by omega⟩
      rw [capProb_succ h0.le h1 hm, if_pos hqmem]
      have hS := Finset.sum_nonneg (hnn ε h0 h1)
      have hwq : 1 / ((m + 1).primeFactors.card : ℝ) * ε ^ d ≤ epsStepWeight ε m q := by
        rcases hor with hqm | hd
        · have hge := epsStepWeight_minFac_ge_inv h0.le h1 hm
          rw [← hqm] at hge
          have := mul_le_mul_of_nonneg_left (pow_le_one₀ h0.le h1 (n := d)) hinv.le
          linarith
        · have hge := epsStepWeight_ge_eps_div_omega h0.le h1 hqmem
          have := mul_le_mul_of_nonneg_left (pow_le_of_le_one h0.le h1 (by omega : d ≠ 0))
            hinv.le
          have hrw : 1 / ((m + 1).primeFactors.card : ℝ) * ε =
              ε / ((m + 1).primeFactors.card : ℝ) := by ring
          linarith
      linarith
    · -- greedy step, then capture below
      have hmp : 1 ≤ m * (m + 1).minFac := by
        have := (Nat.minFac_prime (by omega : m + 1 ≠ 1)).two_le; nlinarith
      obtain ⟨c, hc, hcb⟩ := ih d _ hmp hch
      refine ⟨1 / ((m + 1).primeFactors.card : ℝ) * c, mul_pos hinv hc, fun ε h0 h1 => ?_⟩
      have hmem : (m + 1).minFac ∈ (m + 1).primeFactors.erase q :=
        Finset.mem_erase.mpr ⟨hne, minFac_mem hm⟩
      rw [capProb_succ h0.le h1 hm]
      have hsingle : epsStepWeight ε m (m + 1).minFac * capProb ε q (m * (m + 1).minFac) n ≤
          ∑ p ∈ (m + 1).primeFactors.erase q, epsStepWeight ε m p * capProb ε q (m * p) n :=
        Finset.single_le_sum (f := fun p => epsStepWeight ε m p * capProb ε q (m * p) n)
          (hnn ε h0 h1) hmem
      have hprod : 1 / ((m + 1).primeFactors.card : ℝ) * (c * ε ^ d) ≤
          epsStepWeight ε m (m + 1).minFac * capProb ε q (m * (m + 1).minFac) n :=
        mul_le_mul (epsStepWeight_minFac_ge_inv h0.le h1 hm) (hcb ε h0 h1)
          (mul_nonneg hc.le (pow_nonneg h0.le _)) (epsStepWeight_nonneg h0.le h1)
      have hassoc : 1 / ((m + 1).primeFactors.card : ℝ) * c * ε ^ d =
          1 / ((m + 1).primeFactors.card : ℝ) * (c * ε ^ d) := by ring
      linarith [hT0 ε h0 h1]
    · -- one detour, then capture below with one detour fewer
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      rw [Nat.add_sub_cancel] at hch
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hmp : 1 ≤ m * p := by have := hpp.two_le; nlinarith
      obtain ⟨c, hc, hcb⟩ := ih d' _ hmp hch
      refine ⟨1 / ((m + 1).primeFactors.card : ℝ) * c, mul_pos hinv hc, fun ε h0 h1 => ?_⟩
      have hmem : p ∈ (m + 1).primeFactors.erase q := Finset.mem_erase.mpr ⟨hpq, hp⟩
      rw [capProb_succ h0.le h1 hm]
      have hsingle : epsStepWeight ε m p * capProb ε q (m * p) n ≤
          ∑ p ∈ (m + 1).primeFactors.erase q, epsStepWeight ε m p * capProb ε q (m * p) n :=
        Finset.single_le_sum (f := fun p => epsStepWeight ε m p * capProb ε q (m * p) n)
          (hnn ε h0 h1) hmem
      have hprod : ε / ((m + 1).primeFactors.card : ℝ) * (c * ε ^ d') ≤
          epsStepWeight ε m p * capProb ε q (m * p) n :=
        mul_le_mul (epsStepWeight_ge_eps_div_omega h0.le h1 hp) (hcb ε h0 h1)
          (mul_nonneg hc.le (pow_nonneg h0.le _)) (epsStepWeight_nonneg h0.le h1)
      have hassoc : 1 / ((m + 1).primeFactors.card : ℝ) * c * ε ^ (d' + 1) =
          ε / ((m + 1).primeFactors.card : ℝ) * (c * ε ^ d') := by ring
      linarith [hT0 ε h0 h1]

/-! ## The order of vanishing -/

/-- **Order of vanishing.** If `q` can be selected from `m` within `N` steps with `d`
    detours and with no fewer, then the capture probability within `N` steps is of exact
    order `ε^d`: `c · ε^d ≤ capProb ε q m N ≤ C · ε^d` for all `ε ∈ (0, 1]`. -/
theorem capProb_order {q : ℕ} (hq : q.Prime) {N d m : ℕ} (hm : 1 ≤ m)
    (hcap : CapWithin q N d m) (hmin : ∀ d' < d, ¬ CapWithin q N d' m) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      c * ε ^ d ≤ capProb ε q m N ∧ capProb ε q m N ≤ C * ε ^ d := by
  obtain ⟨c, hc, hcb⟩ := exists_le_capProb_of_capWithin hq N d m hm hcap
  refine ⟨c, 3 ^ N, hc, by positivity, fun ε h0 h1 => ⟨hcb ε h0 h1, ?_⟩⟩
  rcases Nat.eq_zero_or_pos d with hd | hd
  · rw [hd, pow_zero, mul_one]
    exact (capProb_le_one h0.le h1 N).trans (one_le_pow₀ (by norm_num))
  · have := capProb_le_of_not_capWithin h0.le h1 N (d - 1) m hm (hmin (d - 1) (by omega))
    rwa [Nat.sub_add_cancel hd] at this

/-! ## Level zero is the Euclid–Mullin sequence -/

/-- Shifting the start of the greedy walk by one step. -/
theorem mixedWalkProd_minFac_shift (m : ℕ) :
    ∀ k, mixedWalkProd (m * (m + 1).minFac) minFacMixed k =
      mixedWalkProd m minFacMixed (k + 1) := by
  intro k
  induction k with
  | zero =>
    rw [mixedWalkProd_zero, mixedWalkProd_succ, mixedWalkFactor_minFac_eq, mixedWalkProd_zero]
  | succ k ih =>
    rw [mixedWalkProd_succ, mixedWalkFactor_minFac_eq, ih, mixedWalkProd_succ (n := k + 1),
      mixedWalkFactor_minFac_eq]

/-- With no detour: `q` is the least prime factor of one of the first `N` greedy Euclid
    numbers from `m`. -/
theorem capWithin_zero_iff (q : ℕ) :
    ∀ N m, CapWithin q N 0 m ↔
      ∃ k < N, (mixedWalkProd m minFacMixed k + 1).minFac = q := by
  intro N
  induction N with
  | zero => intro m; simp [CapWithin]
  | succ n ih =>
    intro m
    rw [capWithin_succ]
    constructor
    · rintro (⟨_, hqm | h⟩ | ⟨_, hch⟩ | ⟨_, _, _, _, h, _⟩)
      · exact ⟨0, Nat.succ_pos _, by rw [mixedWalkProd_zero]; exact hqm.symm⟩
      · omega
      · obtain ⟨k, hk, hkq⟩ := (ih _).mp hch
        exact ⟨k + 1, by omega, by rw [← mixedWalkProd_minFac_shift]; exact hkq⟩
      · omega
    · rintro ⟨k, hk, hkq⟩
      by_cases hmin : (m + 1).minFac = q
      · exact Or.inl ⟨hmin ▸ Nat.minFac_dvd _, Or.inl hmin.symm⟩
      · refine Or.inr (Or.inl ⟨hmin, (ih _).mpr ?_⟩)
        rcases k with _ | k
        · rw [mixedWalkProd_zero] at hkq; exact absurd hkq hmin
        · exact ⟨k, by omega, by rw [mixedWalkProd_minFac_shift]; exact hkq⟩

/-- From `2` with no detour: `q` is one of `seq 1, …, seq N`. -/
theorem capWithin_zero_two_iff (q N : ℕ) :
    CapWithin q N 0 2 ↔ ∃ k < N, seq (k + 1) = q := by
  rw [capWithin_zero_iff]
  refine exists_congr fun k => and_congr_right fun _ => ?_
  rw [mixedWalkProd_two_minFac_eq_prod, seq_succ,
    euclid_minFac_eq_nat_minFac _ (by have := prod_ge_two k; omega)]

/-- **The Euclid–Mullin sequence is the `ε → 0` limit.** `q` is one of `seq 1, …, seq N` iff
    the probability that the `ε`-mixture from `2` selects `q` within `N` steps stays bounded
    away from `0` as `ε → 0`. -/
theorem mem_seq_iff_capProb_bounded_below {q : ℕ} (hq : q.Prime) (N : ℕ) :
    (∃ k < N, seq (k + 1) = q) ↔
      ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → c ≤ capProb ε q 2 N := by
  rw [← capWithin_zero_two_iff]
  constructor
  · intro h
    obtain ⟨c, hc, hcb⟩ := exists_le_capProb_of_capWithin hq N 0 2 (by norm_num) h
    exact ⟨c, hc, fun ε h0 h1 => by simpa using hcb ε h0 h1⟩
  · rintro ⟨c, hc, hcb⟩
    by_contra hnot
    have h3 : (0 : ℝ) < 3 ^ N := by positivity
    set ε : ℝ := min 1 (c / (2 * 3 ^ N)) with hεdef
    have hε0 : 0 < ε := lt_min one_pos (div_pos hc (by positivity))
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hεc : ε ≤ c / (2 * 3 ^ N) := min_le_right _ _
    have hup := capProb_le_of_not_capWithin hε0.le hε1 N 0 2 (by norm_num) hnot
    rw [zero_add, pow_one] at hup
    have hlow := hcb ε hε0 hε1
    have h1 : 3 ^ N * ε ≤ 3 ^ N * (c / (2 * 3 ^ N)) := mul_le_mul_of_nonneg_left hεc h3.le
    have h2 : (3 : ℝ) ^ N * (c / (2 * 3 ^ N)) = c / 2 := by
      field_simp
    linarith

/-! ## `MixedMC` in terms of `CapWithin` -/

/-- `MixedMC q` holds iff some branch from `2` selects `q` within some number of steps with
    some number of detours. -/
theorem mixedMC_iff_exists_capWithin {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    MixedMC q ↔ ∃ N d, CapWithin q N d 2 := by
  have hhalf0 : (0 : ℝ) < 1 / 4 := by norm_num
  have hhalf1 : (1 : ℝ) / 4 ≤ 1 := by norm_num
  rw [mixedMC_iff_eps_capture hhalf0 hhalf1 hq hq3]
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    by_contra hnone
    push Not at hnone
    have hpos : 0 < capProb (1 / 4) q 2 N := by unfold capProb; linarith
    have h3 : (0 : ℝ) < 3 ^ N := by positivity
    obtain ⟨d, hd⟩ := exists_pow_lt_of_lt_one (div_pos hpos h3) (by norm_num : (1 : ℝ) / 4 < 1)
    have hup := capProb_le_of_not_capWithin hhalf0.le hhalf1 N d 2 (by norm_num) (hnone d)
    have hle : ((1 : ℝ) / 4) ^ (d + 1) ≤ (1 / 4) ^ d :=
      pow_le_pow_of_le_one hhalf0.le hhalf1 (Nat.le_succ d)
    have h1 : 3 ^ N * ((1 : ℝ) / 4) ^ d < capProb (1 / 4) q 2 N := by
      rw [lt_div_iff₀ h3] at hd
      linarith
    have h2 := mul_le_mul_of_nonneg_left hle h3.le
    linarith
  · rintro ⟨N, d, h⟩
    obtain ⟨c, hc, hcb⟩ := exists_le_capProb_of_capWithin hq N d 2 (by norm_num) h
    have := hcb (1 / 4) hhalf0 hhalf1
    have hpos : 0 < c * ((1 : ℝ) / 4) ^ d := mul_pos hc (by positivity)
    exact ⟨N, by unfold capProb at this; linarith⟩

end MixedTree
