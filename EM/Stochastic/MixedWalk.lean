import EM.Stochastic.DenseCapture
import EM.Stochastic.IteratedProductCoverage

/-!
# Mixed Walk: Mixed minFac + Random Factor Selection

## Overview

This file formalizes the **mixed selection rule** variant of the Euclid-Mullin walk
(Parts 1-11 of the original epsilon-random MC development). At each step, the walk
either chooses minFac(P+1) (the standard EM choice) or a specified prime factor of
P+1 (modeling a "random" choice from the factor set).

The selection is parameterized by `MixedSelection = N -> Option N`:
- `none` at step k means choose minFac(P_k + 1)
- `some p` at step k means choose prime p dividing P_k + 1

This models the "(1-eps) minFac + eps random" variant where with probability (1-eps)
we choose minFac and with probability eps we choose a uniformly random prime factor.
The formal treatment is nondeterministic (all valid selection sequences) rather than
probabilistic.

## Contents

* Part 1: Definitions -- `MixedSelection`, `minFacMixed`, `mixedWalkProd`,
  `mixedWalkFactor`, `ValidMixedSelection`, `mixedCaptures`, `mixedCaptureSet`,
  `isRandomStep`, `randomStepCount`, `InfinitelyManyRandomSteps`
* Part 2: Basic properties -- `mixedWalkProd_zero`, `mixedWalkProd_succ`,
  `mixedWalkFactor_eq`, `mixedWalkFactor_prime`, `mixedWalkFactor_dvd`,
  `mixedWalkProd_ge_two`
* Part 3: q=3 unconditional capture -- `mixed_capture_three`, `mixed_captures_three`
* Part 4: Bridge to two-point walk -- `mixedWalkProd_minFac_eq`,
  `mixedWalkFactor_minFac_eq`, `minFacMixed_valid`
* Part 5: Factor possibility at hits -- `mixedWalkFactor_some_eq`, `valid_at_hit`,
  `valid_random_prime_dvd`, `mixedWalkFactor_none_eq_minFac`
* Part 6: Prefix dependence -- `mixedWalkProd_depends_on_prefix`,
  `mixedWalkFactor_depends_on_prefix`
* Part 7: Tail restart -- `mixedWalkProd_tail_restart`
* Part 8: Diversity hypothesis -- `MixedDiversity`, `not_prime_has_proper_minFac`
* Part 9: Monotonicity -- `mixedWalkProd_strict_mono`, `mixedWalkProd_mono`
* Part 10: Factor injectivity -- `mixedWalkFactor_dvd_succ_prod`,
  `mixedWalkFactor_not_dvd_prod`
* Part 11: Landscape -- `eps_random_mc_landscape`

## Connection to Existing Infrastructure

The two-point walk (`epsWalkProdFrom` in `RandomTwoPointMC.lean`) uses `N -> Bool`
with `true = minFac`, `false = secondMinFac`. The mixed walk generalizes this to
arbitrary prime factor choices. The bridge `mixedWalkProd_minFac_eq` shows that the
all-minFac mixed selection produces the same walk as the all-true two-point selection.
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Part 1: Definitions -/

section Definitions

/-- The mixed selection type: at each step, either choose minFac (none)
    or a specific prime factor (some p). -/
abbrev MixedSelection := ℕ → Option ℕ

/-- The all-minFac selection: always choose minFac (= standard EM). -/
def minFacMixed : MixedSelection := fun _ => none

/-- The mixed walk accumulator from starting point acc.
    At each step, if sigma(k) = none, multiply by minFac(P+1);
    if sigma(k) = some p, multiply by p (validity checked separately). -/
def mixedWalkProd (acc : ℕ) (σ : MixedSelection) : ℕ → ℕ
  | 0 => acc
  | n + 1 =>
    let P := mixedWalkProd acc σ n
    let factor := match σ n with
      | none => (P + 1).minFac
      | some p => p
    P * factor

/-- The factor chosen at step n in the mixed walk from acc. -/
def mixedWalkFactor (acc : ℕ) (σ : MixedSelection) (n : ℕ) : ℕ :=
  let P := mixedWalkProd acc σ n
  match σ n with
  | none => (P + 1).minFac
  | some p => p

/-- The all-minFac mixed walk from starting point m equals the generalized
    EM accumulator genProd m k. Both start at m and multiply by minFac(P+1)
    at each step. -/
theorem mixedWalkProd_minFac_eq_genProd (m : ℕ) (k : ℕ) :
    mixedWalkProd m minFacMixed k = genProd m k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [mixedWalkProd, minFacMixed, genProd_succ, genSeq]
    rw [ih]

/-- Validity: every random choice is a prime dividing the current accumulator + 1.
    For deterministic steps (none), no condition is imposed. -/
def ValidMixedSelection (acc : ℕ) (σ : MixedSelection) : Prop :=
  ∀ k, match σ k with
  | none => True
  | some p => p.Prime ∧ p ∣ (mixedWalkProd acc σ k + 1)

/-- The mixed walk captures q if some factor equals q. -/
def mixedCaptures (q acc : ℕ) (σ : MixedSelection) : Prop :=
  ∃ k, mixedWalkFactor acc σ k = q

/-- The set of valid mixed selections that capture q from accumulator acc. -/
def mixedCaptureSet (q acc : ℕ) : Set MixedSelection :=
  {σ | ValidMixedSelection acc σ ∧ mixedCaptures q acc σ}

/-- A step n is "random" if sigma n is not none (a specific factor was chosen). -/
def isRandomStep (σ : MixedSelection) (n : ℕ) : Prop := σ n ≠ none

/-- The count of random steps in the first N steps. -/
def randomStepCount (σ : MixedSelection) (N : ℕ) : ℕ :=
  (Finset.range N).filter (fun n => (σ n).isSome) |>.card

/-- Infinitely many random steps in the selection sequence. -/
def InfinitelyManyRandomSteps (σ : MixedSelection) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ (σ n).isSome = true

end Definitions

/-! ## Part 2: Basic Properties -/

section BasicProperties

/-- The initial value of the mixed walk accumulator is acc. -/
theorem mixedWalkProd_zero (acc : ℕ) (σ : MixedSelection) :
    mixedWalkProd acc σ 0 = acc := rfl

/-- The recurrence for the mixed walk. -/
theorem mixedWalkProd_succ (acc : ℕ) (σ : MixedSelection) (n : ℕ) :
    mixedWalkProd acc σ (n + 1) =
    mixedWalkProd acc σ n * mixedWalkFactor acc σ n := by
  simp [mixedWalkProd, mixedWalkFactor]

/-- The factor at each step matches the walk recurrence. -/
theorem mixedWalkFactor_eq (acc : ℕ) (σ : MixedSelection) (n : ℕ) :
    mixedWalkFactor acc σ n =
    match σ n with
    | none => (mixedWalkProd acc σ n + 1).minFac
    | some p => p := by
  rfl

/-- For valid sigma, the factor at each step is prime (given accumulator >= 2). -/
theorem mixedWalkFactor_prime (acc : ℕ) (σ : MixedSelection)
    (hv : ValidMixedSelection acc σ) (n : ℕ)
    (hge : 2 ≤ mixedWalkProd acc σ n) :
    (mixedWalkFactor acc σ n).Prime := by
  simp only [mixedWalkFactor]
  have hspec := hv n
  cases hσ : σ n with
  | none =>
    exact Nat.minFac_prime (by omega)
  | some p =>
    simp only [hσ] at hspec
    exact hspec.1

/-- For valid sigma, the factor at each step divides P+1. -/
theorem mixedWalkFactor_dvd (acc : ℕ) (σ : MixedSelection)
    (hv : ValidMixedSelection acc σ) (n : ℕ) :
    mixedWalkFactor acc σ n ∣ (mixedWalkProd acc σ n + 1) := by
  simp only [mixedWalkFactor]
  have hspec := hv n
  cases hσ : σ n with
  | none =>
    exact Nat.minFac_dvd _
  | some p =>
    simp only [hσ] at hspec
    exact hspec.2

/-- For valid sigma from acc >= 2, the accumulator stays >= 2 at all steps. -/
theorem mixedWalkProd_ge_two (acc : ℕ) (hacc : 2 ≤ acc) (σ : MixedSelection)
    (hv : ValidMixedSelection acc σ) (n : ℕ) :
    2 ≤ mixedWalkProd acc σ n := by
  induction n with
  | zero => simp [mixedWalkProd]; exact hacc
  | succ n ih =>
    rw [mixedWalkProd_succ]
    have hfac_prime := mixedWalkFactor_prime acc σ hv n ih
    calc 2 = 1 * 2 := by omega
      _ ≤ mixedWalkProd acc σ n * mixedWalkFactor acc σ n :=
        Nat.mul_le_mul (by omega) hfac_prime.two_le

end BasicProperties

/-! ## Part 3: q=3 Unconditional Capture -/

section CaptureThree

/-- At step 0 from acc=2, the accumulator is 2 and P+1=3.
    For any valid sigma, the factor at step 0 must be 3:
    - If sigma(0) = none: factor = minFac(3) = 3 (since 3 is prime)
    - If sigma(0) = some p: validity gives p prime, p | 3, so p = 3 -/
theorem mixed_capture_three (σ : MixedSelection) (hv : ValidMixedSelection 2 σ) :
    mixedWalkFactor 2 σ 0 = 3 := by
  unfold mixedWalkFactor
  have hspec := hv 0
  have hprod0 : mixedWalkProd 2 σ 0 = 2 := rfl
  rw [hprod0]
  cases hσ : σ 0 with
  | none =>
    -- factor = minFac(2 + 1) = minFac(3) = 3
    show Nat.minFac (2 + 1) = 3
    norm_num
  | some p =>
    -- Need: p = 3. From validity: p.Prime and p | (2 + 1) = 3
    rw [hσ, hprod0] at hspec
    obtain ⟨hp, hdvd⟩ := hspec
    have h3 : Nat.Prime 3 := by decide
    exact (h3.eq_one_or_self_of_dvd p hdvd).resolve_left (hp.ne_one)

/-- q=3 is captured at step 0 for any valid selection from acc=2. -/
theorem mixed_captures_three (σ : MixedSelection) (hv : ValidMixedSelection 2 σ) :
    mixedCaptures 3 2 σ :=
  ⟨0, mixed_capture_three σ hv⟩

end CaptureThree

/-! ## Part 4: Bridge to Two-Point Walk -/

section MinFacBridge

/-- Under the all-minFac selection, the mixed walk agrees with the two-point
    walk under all-true decisions. Both always choose minFac(P+1). -/
theorem mixedWalkProd_minFac_eq (acc : ℕ) (n : ℕ) :
    mixedWalkProd acc minFacMixed n = epsWalkProdFrom acc (fun _ => true) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [mixedWalkProd, epsWalkProdFrom, minFacMixed]
    rw [ih]
    simp

/-- The factor at each step under the all-minFac selection equals minFac(P+1). -/
theorem mixedWalkFactor_minFac_eq (acc : ℕ) (n : ℕ) :
    mixedWalkFactor acc minFacMixed n =
    (mixedWalkProd acc minFacMixed n + 1).minFac := by
  simp [mixedWalkFactor, minFacMixed]

/-- The all-minFac selection is always valid (no conditions to check at none steps). -/
theorem minFacMixed_valid (acc : ℕ) : ValidMixedSelection acc minFacMixed := by
  intro k
  simp [minFacMixed]

end MinFacBridge

/-! ## Part 5: Factor Possibility at Hits -/

section FactorPossibility

/-- If q is prime and q divides P+1, then choosing some q at a step where
    the accumulator is P gives factor = q (by definition of mixedWalkFactor).
    This is trivial by the definition of mixedWalkFactor when sigma(n) = some q. -/
theorem mixedWalkFactor_some_eq (acc : ℕ) (σ : MixedSelection) (n : ℕ) (p : ℕ)
    (hσn : σ n = some p) :
    mixedWalkFactor acc σ n = p := by
  simp [mixedWalkFactor, hσn]

/-- If q is prime and q divides P_n + 1, then setting sigma(n) = some q
    satisfies the validity condition at step n. This shows that whenever the
    walk accumulator P has q | P+1, there is a valid choice that captures q. -/
theorem valid_at_hit (acc : ℕ) (σ : MixedSelection) (n : ℕ) (q : ℕ)
    (hq : q.Prime) (hdvd : q ∣ mixedWalkProd acc σ n + 1) :
    q.Prime ∧ q ∣ (mixedWalkProd acc σ n + 1) :=
  ⟨hq, hdvd⟩

/-- For valid sigma, a random step gives a prime that divides P+1. -/
theorem valid_random_prime_dvd (acc : ℕ) (σ : MixedSelection)
    (hv : ValidMixedSelection acc σ) (n : ℕ) (p : ℕ) (hσn : σ n = some p) :
    p.Prime ∧ p ∣ (mixedWalkProd acc σ n + 1) := by
  have hspec := hv n
  simp only [hσn] at hspec
  exact hspec

/-- Every deterministic (none) step produces a factor that is minFac. -/
theorem mixedWalkFactor_none_eq_minFac (acc : ℕ) (σ : MixedSelection) (n : ℕ)
    (hσn : σ n = none) :
    mixedWalkFactor acc σ n = (mixedWalkProd acc σ n + 1).minFac := by
  simp [mixedWalkFactor, hσn]

end FactorPossibility

/-! ## Part 6: Prefix Dependence -/

section PrefixDependence

/-- The mixed walk accumulator at step k depends only on sigma(0),...,sigma(k-1).
    If two selection sequences agree on the first k steps, the accumulators agree. -/
theorem mixedWalkProd_depends_on_prefix (acc : ℕ) (σ τ : MixedSelection)
    (k : ℕ) (h : ∀ i, i < k → σ i = τ i) :
    mixedWalkProd acc σ k = mixedWalkProd acc τ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [mixedWalkProd]
    have hpref : ∀ i, i < k → σ i = τ i := fun i hi => h i (by omega)
    rw [ih hpref, h k (by omega)]

/-- The mixed walk factor at step k depends only on sigma(0),...,sigma(k).
    If two selection sequences agree on the first k+1 values, the factors agree. -/
theorem mixedWalkFactor_depends_on_prefix (acc : ℕ) (σ τ : MixedSelection)
    (k : ℕ) (h : ∀ i, i ≤ k → σ i = τ i) :
    mixedWalkFactor acc σ k = mixedWalkFactor acc τ k := by
  simp only [mixedWalkFactor]
  have hpref : ∀ i, i < k → σ i = τ i := fun i hi => h i (by omega)
  rw [mixedWalkProd_depends_on_prefix acc σ τ k hpref, h k (le_refl k)]

end PrefixDependence

/-! ## Part 7: Tail Restart -/

section TailRestart

/-- The mixed walk from step K onward is a fresh walk starting from the
    accumulator at step K, with the shifted selection sequence. -/
theorem mixedWalkProd_tail_restart (acc : ℕ) (σ : MixedSelection) (K j : ℕ) :
    mixedWalkProd acc σ (K + j) =
    mixedWalkProd (mixedWalkProd acc σ K) (fun i => σ (K + i)) j := by
  induction j with
  | zero => simp [mixedWalkProd]
  | succ j ih =>
    have hkj : K + (j + 1) = K + j + 1 := by omega
    rw [hkj]
    simp only [mixedWalkProd]
    rw [ih]

end TailRestart

/-! ## Part 8: Diversity Hypothesis -/

section Diversity

/-- Diversity hypothesis: cofinally many steps have factor sets with more than
    one prime factor available. This means the nondeterministic walk has genuine
    branching at infinitely many steps.

    **Status**: open hypothesis. -/
def MixedDiversity : Prop :=
  ∀ (acc : ℕ), 2 ≤ acc → ∀ N : ℕ, ∃ n, N ≤ n ∧
    ¬ (mixedWalkProd acc minFacMixed n + 1).Prime

/-- When P+1 is not prime, it has at least two prime factors (possibly equal).
    In particular, minFac(P+1) < P+1, so there are at least two choices of
    prime factor. This means diversity gives genuine branching. -/
theorem not_prime_has_proper_minFac {m : ℕ} (hm : 2 ≤ m) (hnp : ¬ m.Prime) :
    m.minFac < m :=
  Nat.not_prime_iff_minFac_lt hm |>.mp hnp

end Diversity

/-! ## Part 9: Monotonicity -/

section Monotonicity

/-- For valid sigma from acc >= 2, the accumulator is strictly increasing. -/
theorem mixedWalkProd_strict_mono (acc : ℕ) (hacc : 2 ≤ acc) (σ : MixedSelection)
    (hv : ValidMixedSelection acc σ) (n : ℕ) :
    mixedWalkProd acc σ n < mixedWalkProd acc σ (n + 1) := by
  rw [mixedWalkProd_succ]
  have hge := mixedWalkProd_ge_two acc hacc σ hv n
  have hfac_prime := mixedWalkFactor_prime acc σ hv n hge
  have hP_pos : 0 < mixedWalkProd acc σ n := by omega
  calc mixedWalkProd acc σ n
      = mixedWalkProd acc σ n * 1 := by omega
    _ < mixedWalkProd acc σ n * mixedWalkFactor acc σ n :=
        Nat.mul_lt_mul_of_pos_left hfac_prime.one_lt hP_pos

/-- The accumulator is monotonically increasing (weak form). -/
theorem mixedWalkProd_mono (acc : ℕ) (hacc : 2 ≤ acc) (σ : MixedSelection)
    (hv : ValidMixedSelection acc σ) {m n : ℕ} (hmn : m ≤ n) :
    mixedWalkProd acc σ m ≤ mixedWalkProd acc σ n := by
  induction hmn with
  | refl => rfl
  | step _ ih =>
    exact le_of_lt (ih.trans_lt (mixedWalkProd_strict_mono acc hacc σ hv _))

end Monotonicity

/-! ## Part 10: Factor Injectivity -/

section Injectivity

/-- For valid sigma from acc >= 2, if the factor at step n divides the accumulator
    at step n, then the factor at step n also divides the accumulator at step n+1.
    This is because P_{n+1} = P_n * factor_n, so factor_n | P_{n+1}. -/
theorem mixedWalkFactor_dvd_succ_prod (acc : ℕ) (σ : MixedSelection) (n : ℕ) :
    mixedWalkFactor acc σ n ∣ mixedWalkProd acc σ (n + 1) := by
  rw [mixedWalkProd_succ]
  exact dvd_mul_left _ _

/-- The factor at step n does NOT divide the accumulator at step n (for valid
    sigma from acc >= 2). This is because factor_n | P_n + 1 and P_n >= 2,
    so if factor_n | P_n, then factor_n | (P_n + 1 - P_n) = 1, contradicting
    factor_n >= 2. -/
theorem mixedWalkFactor_not_dvd_prod (acc : ℕ) (hacc : 2 ≤ acc) (σ : MixedSelection)
    (hv : ValidMixedSelection acc σ) (n : ℕ) :
    ¬ (mixedWalkFactor acc σ n ∣ mixedWalkProd acc σ n) := by
  intro hdvd_P
  have hge := mixedWalkProd_ge_two acc hacc σ hv n
  have hdvd_P1 := mixedWalkFactor_dvd acc σ hv n
  have hfac_prime := mixedWalkFactor_prime acc σ hv n hge
  set P := mixedWalkProd acc σ n
  set f := mixedWalkFactor acc σ n
  have hf_ge : 2 ≤ f := hfac_prime.two_le
  obtain ⟨a, ha⟩ := hdvd_P
  obtain ⟨b, hb⟩ := hdvd_P1
  -- P = f*a and P+1 = f*b, so f*b = f*a + 1
  have hab : f * b = f * a + 1 := by omega
  have hba : a < b := by nlinarith
  have hba1 : b = a + 1 := by nlinarith
  -- Then f * (a + 1) = f * a + 1, so f * a + f = f * a + 1, so f = 1
  have : f = 1 := by nlinarith
  omega

end Injectivity

/-! ## Part 11: Landscape -/

section Landscape

/-- **Epsilon-random MC landscape**: summary of all proved results.

    1. mixedWalkProd_ge_two -- accumulator stays >= 2 under validity
    2. mixedWalkFactor_prime -- factor is prime under validity
    3. mixedWalkFactor_dvd -- factor divides P+1 under validity
    4. mixed_capture_three -- q=3 captured unconditionally from acc=2
    5. mixedWalkProd_minFac_eq -- minFac-only = two-point all-true walk
    6. minFacMixed_valid -- all-minFac selection is always valid
    7. mixedWalkProd_strict_mono -- accumulator strictly increasing
    8. mixedWalkFactor_not_dvd_prod -- factor coprime to accumulator -/
theorem eps_random_mc_landscape (acc : ℕ) (hacc : 2 ≤ acc) (σ : MixedSelection)
    (hv : ValidMixedSelection acc σ) :
    -- 1. Accumulator >= 2
    (∀ n, 2 ≤ mixedWalkProd acc σ n)
    ∧
    -- 2. Factor is prime
    (∀ n, (mixedWalkFactor acc σ n).Prime)
    ∧
    -- 3. Factor divides P+1
    (∀ n, mixedWalkFactor acc σ n ∣ (mixedWalkProd acc σ n + 1))
    ∧
    -- 4. q=3 from acc=2 (conditional on acc=2)
    (acc = 2 → mixedCaptures 3 acc σ)
    ∧
    -- 5. minFac bridge (unconditional)
    (∀ n, mixedWalkProd acc minFacMixed n = epsWalkProdFrom acc (fun _ => true) n)
    ∧
    -- 6. minFacMixed is valid
    ValidMixedSelection acc minFacMixed
    ∧
    -- 7. Strict monotonicity
    (∀ n, mixedWalkProd acc σ n < mixedWalkProd acc σ (n + 1))
    ∧
    -- 8. Factor coprime to accumulator
    (∀ n, ¬ (mixedWalkFactor acc σ n ∣ mixedWalkProd acc σ n)) := by
  refine ⟨
    mixedWalkProd_ge_two acc hacc σ hv,
    fun n => mixedWalkFactor_prime acc σ hv n (mixedWalkProd_ge_two acc hacc σ hv n),
    fun n => mixedWalkFactor_dvd acc σ hv n,
    fun heq => by subst heq; exact mixed_captures_three σ hv,
    mixedWalkProd_minFac_eq acc,
    minFacMixed_valid acc,
    mixedWalkProd_strict_mono acc hacc σ hv,
    mixedWalkFactor_not_dvd_prod acc hacc σ hv⟩

end Landscape
