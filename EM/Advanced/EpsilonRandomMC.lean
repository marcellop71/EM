import EM.Advanced.DenseCapture
import EM.Advanced.IteratedProductCoverage

/-!
# Epsilon-Random MC: Mixed minFac + Random Factor Variant

## Overview

This file formalizes a **mixed selection rule** variant of the Euclid-Mullin walk.
At each step, the walk either chooses minFac(P+1) (the standard EM choice) or
a specified prime factor of P+1 (modeling a "random" choice from the factor set).

The selection is parameterized by `MixedSelection = N -> Option N`:
- `none` at step k means choose minFac(P_k + 1)
- `some p` at step k means choose prime p dividing P_k + 1

This models the "(1-eps) minFac + eps random" variant where with probability (1-eps)
we choose minFac and with probability eps we choose a uniformly random prime factor.
The formal treatment is nondeterministic (all valid selection sequences) rather than
probabilistic.

## Key Results

### Proved Theorems
* `mixedWalkProd_zero` -- initial value is acc
* `mixedWalkProd_succ` -- recurrence via mixedWalkFactor
* `mixedWalkFactor_prime` -- factor is prime under validity + acc >= 2
* `mixedWalkFactor_dvd` -- factor divides accumulator + 1 under validity + acc >= 2
* `mixedWalkProd_ge_two` -- accumulator stays >= 2 under validity
* `mixed_capture_three` -- q=3 captured at step 0 for any valid sigma from acc=2
* `mixedWalkProd_minFac_eq` -- minFac-only selection recovers two-point walk
* `valid_at_hit` -- q prime and q | P+1 implies some q is valid at that step
* `minFacMixed_valid` -- the all-minFac selection is always valid
* `valid_random_prime_dvd` -- valid random step gives prime divisor
* `eps_random_mc_landscape` -- summary conjunction

### Open Hypotheses
* `MixedDiversity` -- cofinally many steps have multi-element factor sets

## Connection to Existing Infrastructure

The two-point walk (`epsWalkProdFrom` in `RandomTwoPointMC.lean`) uses `N -> Bool`
with `true = minFac`, `false = secondMinFac`. The mixed walk generalizes this to
arbitrary prime factor choices. The bridge `mixedWalkProd_minFac_eq` shows that the
all-minFac mixed selection produces the same walk as the all-true two-point selection.

## Factor Tree Perspective

The mixed walk from acc=2 implicitly defines the factor tree T(2):
- Root has accumulator 2
- At each node with accumulator P, children are P*p for each prime p | P+1
- Standard EM = leftmost path (always choosing minFac)
- MixedMC asks: does some path capture q? (= does -1 ∈ R_inf(q,2)?)

Key structural results (all proved):
- reachableAt_from_factor: every prime factor extends R_inf
- reachableEver_not_in_coset: R_inf escapes every proper coset
- factor_confinement: if R_inf is proper, ALL factors are sieve-confined
- mixed_mc_two/three: unconditional for q=2,3

The sole remaining gap is FactorEscapeHypothesis: along the standard
EM orbit, Euclid numbers eventually escape step-dependent factor confinement.
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
    native_decide
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

/-! ## Part 12: Mixed MC Framework

We define the Mixed Mullin Conjecture: every prime is "captured" by the mixed walk.
Since all accumulators starting from acc=2 are even, P(n)+1 is always odd, so
q=2 can never appear as a factor. We handle q=2 separately via disjunction. -/

section MixedMCDefs

/-- Mixed MC for a single prime: either q=2 (trivially in the initial accumulator)
    or there exists a valid selection that captures q from acc=2. -/
def MixedMC (q : ℕ) : Prop :=
  q.Prime → q = 2 ∨ ∃ σ : MixedSelection, ValidMixedSelection 2 σ ∧ mixedCaptures q 2 σ

/-- Mixed MC below: all primes less than q have MixedMC. -/
def MixedMCBelow (q : ℕ) : Prop :=
  ∀ r, r.Prime → r < q → MixedMC r

/-- Full Mixed Mullin Conjecture: every prime has MixedMC. -/
def MixedMullinConjecture : Prop :=
  ∀ q, q.Prime → MixedMC q

end MixedMCDefs

/-! ## Part 13: q=2 and q=3 Base Cases -/

section BaseCases

/-- q=2 is trivially captured since 2 divides the initial accumulator acc=2. -/
theorem mixed_mc_two : MixedMC 2 := by
  intro _
  left
  rfl

/-- q=3 is captured at step 0 for any valid selection from acc=2.
    This follows from `mixed_capture_three` and `minFacMixed_valid`. -/
theorem mixed_mc_three : MixedMC 3 := by
  intro _
  right
  exact ⟨minFacMixed, minFacMixed_valid 2, 0, mixed_capture_three minFacMixed (minFacMixed_valid 2)⟩

end BaseCases

/-! ## Part 14: MixedDiversityWeak Hypothesis

The weak steering hypothesis: for every prime q >= 5 and accumulator acc >= 2
with q not dividing acc, if the minFac walk from acc produces composite P+1 at
cofinally many steps (diversity), then some valid selection captures q.

This is genuinely weaker than DynamicalHitting: the mixed walk has freedom to
choose non-minFac factors, providing more paths to hit any given prime. -/

section DiversityWeak

/-- Weak diversity-implies-capture hypothesis for the mixed walk.
    Given diversity (cofinally many composite P+1), we can steer the walk
    to capture any target prime q >= 5.

    **Status**: open hypothesis. This is the sole gap for MixedMullinConjecture. -/
def MixedDiversityWeak : Prop :=
  ∀ (q : ℕ), q.Prime → 5 ≤ q →
    ∀ (acc : ℕ), 2 ≤ acc → ¬(q ∣ acc) →
    (∀ N, ∃ n, N ≤ n ∧ ¬(mixedWalkProd acc minFacMixed n + 1).Prime) →
    ∃ σ : MixedSelection, ValidMixedSelection acc σ ∧ mixedCaptures q acc σ

end DiversityWeak

/-! ## Part 15: Main Theorem — Strong Induction

The core reduction: MixedDiversityWeak + MixedDiversity implies MixedMullinConjecture.
The proof uses strong induction on the prime q. For q=2 and q=3, we use the base
cases. For q >= 5, we apply MixedDiversityWeak with acc=2. -/

section MainReduction

/-- For q >= 5, q does not divide 2. -/
private theorem not_dvd_two_of_ge_five {q : ℕ} (h5 : 5 ≤ q) :
    ¬(q ∣ 2) := by
  intro hdvd
  have := Nat.le_of_dvd (by omega : 0 < 2) hdvd
  omega

/-- For q prime and q not equal to 2 or 3, we have q >= 5. -/
private theorem prime_ge_five_of_ne {q : ℕ} (hq : q.Prime) (hne2 : q ≠ 2) (hne3 : q ≠ 3) :
    5 ≤ q := by
  by_contra h
  push Not at h
  have h2 := hq.two_le
  -- q ∈ {2, 3, 4}; only 2 and 3 are prime
  interval_cases q <;> first | omega | exact absurd hq (by decide)

/-- **Main theorem**: MixedDiversityWeak + MixedDiversity implies MixedMullinConjecture.

    Proof by strong induction on q:
    - q = 2: trivial (2 | acc = 2)
    - q = 3: unconditional from mixed_capture_three
    - q >= 5: apply MixedDiversityWeak with acc = 2, using MixedDiversity for the
      cofinality hypothesis and the inductive hypothesis for MixedMCBelow. -/
theorem mixed_diversity_weak_implies_mixed_mc
    (hdw : MixedDiversityWeak) (hdiv : MixedDiversity) :
    MixedMullinConjecture := by
  -- Strong induction: suffices to show MixedMC q for all q <= k
  suffices ∀ k q, q ≤ k → q.Prime → MixedMC q by
    intro q hq; exact this q q le_rfl hq
  intro k
  induction k with
  | zero =>
    intro q hle hq
    exact absurd hq.one_lt (by omega)
  | succ k ih =>
    intro q hle hq
    -- If q < k+1, use the inductive hypothesis
    match Nat.lt_or_ge q (k + 1) with
    | .inl hlt => exact ih q (by omega) hq
    | .inr _ =>
      -- q = k + 1 case (since q <= k+1 and q >= k+1)
      intro _hprime
      -- Handle small primes directly
      by_cases hq2 : q = 2
      · left; exact hq2
      by_cases hq3 : q = 3
      · right
        subst hq3
        exact ⟨minFacMixed, minFacMixed_valid 2, 0,
               mixed_capture_three minFacMixed (minFacMixed_valid 2)⟩
      -- q >= 5: apply MixedDiversityWeak
      right
      have hq5 : 5 ≤ q := prime_ge_five_of_ne hq hq2 hq3
      have hndvd : ¬(q ∣ 2) := not_dvd_two_of_ge_five hq5
      have hdiv2 : ∀ N, ∃ n, N ≤ n ∧ ¬(mixedWalkProd 2 minFacMixed n + 1).Prime :=
        hdiv 2 (by omega)
      exact hdw q hq hq5 2 (by omega) hndvd hdiv2

/-- MixedDiversity alone is insufficient: we also need MixedDiversityWeak to steer.
    But MixedDiversityWeak is the SOLE hypothesis beyond MixedDiversity. -/
theorem mixed_diversity_weak_is_sole_gap :
    (MixedDiversityWeak → MixedDiversity → MixedMullinConjecture) :=
  mixed_diversity_weak_implies_mixed_mc

end MainReduction

/-! ## Part 16: MixedMCBelow from Induction

The strong induction gives MixedMCBelow at each step. We extract this as
a standalone theorem for use in downstream proofs. -/

section MCBelowExtraction

/-- MixedDiversityWeak + MixedDiversity implies MixedMCBelow for all q. -/
theorem mixed_diversity_weak_implies_mc_below
    (hdw : MixedDiversityWeak) (hdiv : MixedDiversity) (q : ℕ) :
    MixedMCBelow q := by
  intro r hr hrq
  exact mixed_diversity_weak_implies_mixed_mc hdw hdiv r hr

end MCBelowExtraction

/-! ## Part 17: Mixed MC Landscape

Summary of the entire mixed MC framework: base cases, main reduction, and
the single open hypothesis. -/

section MixedMCLandscape

/-- **Mixed MC landscape**: summary of the complete framework.

    1. MixedMC 2 -- q=2 is trivial
    2. MixedMC 3 -- q=3 is unconditional
    3. MixedDiversityWeak + MixedDiversity implies MixedMullinConjecture
    4. MixedDiversityWeak is the sole open hypothesis for q >= 5 -/
theorem mixed_mc_landscape
    (hdw : MixedDiversityWeak) (hdiv : MixedDiversity) :
    -- 1. q=2 is trivial
    MixedMC 2
    ∧
    -- 2. q=3 is unconditional
    MixedMC 3
    ∧
    -- 3. Full Mixed MC holds
    MixedMullinConjecture
    ∧
    -- 4. Sole gap is MixedDiversityWeak
    (MixedDiversityWeak → MixedDiversity → MixedMullinConjecture) :=
  ⟨mixed_mc_two,
   mixed_mc_three,
   mixed_diversity_weak_implies_mixed_mc hdw hdiv,
   mixed_diversity_weak_implies_mixed_mc⟩

end MixedMCLandscape

/-! ## Part 18: Walk-mod-q Structural Lemmas

The walk modulo a prime q stays coprime to q until the walk captures q.
These lemmas formalize the structural fact that if no factor chosen along
the walk equals q, then q cannot divide the accumulator product at any step.
This is because each factor is prime and distinct from q (hence coprime to q),
and the product of terms coprime to q remains coprime to q. -/

section WalkModQ

/-- For any prime factor f different from prime q, q does not divide f.
    This is because f is prime, so its only divisors are 1 and f.
    If q | f, then q = 1 or q = f; but q is prime so q ≠ 1, hence q = f,
    contradicting f ≠ q. -/
theorem prime_factor_ne_not_dvd {q : ℕ} (hq : Nat.Prime q)
    (f : ℕ) (hf : f.Prime) (hfq : f ≠ q) :
    ¬(q ∣ f) := by
  intro hdvd
  exact hfq ((hf.eq_one_or_self_of_dvd q hdvd).resolve_left (Nat.Prime.ne_one hq)).symm

/-- The walk stays coprime to q until capture: if q does not divide the initial
    accumulator and no factor chosen at steps 0, ..., n-1 equals q, then q does
    not divide the accumulator at step n.

    Proof by induction on n. At n=0 this is the hypothesis q ∤ acc. At n+1,
    the product P_{n+1} = P_n * f_n. By IH, q ∤ P_n. The factor f_n is prime
    (from validity + acc ≥ 2) and f_n ≠ q (from hnocap), so q ∤ f_n by
    `prime_factor_ne_not_dvd`. Therefore q ∤ P_n * f_n. -/
theorem walk_coprime_until_capture {q : ℕ} (hq : Nat.Prime q)
    (acc : ℕ) (hacc : 2 ≤ acc)
    (σ : MixedSelection) (hv : ValidMixedSelection acc σ)
    (hndvd : ¬(q ∣ acc))
    (n : ℕ) (hnocap : ∀ k, k < n → mixedWalkFactor acc σ k ≠ q) :
    ¬(q ∣ mixedWalkProd acc σ n) := by
  induction n with
  | zero => simp [mixedWalkProd]; exact hndvd
  | succ n ih =>
    rw [mixedWalkProd_succ]
    have hih : ¬(q ∣ mixedWalkProd acc σ n) :=
      ih (fun k hk => hnocap k (by omega))
    have hge := mixedWalkProd_ge_two acc hacc σ hv n
    have hfac_prime := mixedWalkFactor_prime acc σ hv n hge
    have hfac_neq : mixedWalkFactor acc σ n ≠ q := hnocap n (by omega)
    have hfac_ndvd : ¬(q ∣ mixedWalkFactor acc σ n) :=
      prime_factor_ne_not_dvd hq _ hfac_prime hfac_neq
    exact Nat.Prime.not_dvd_mul hq hih hfac_ndvd

/-- If q divides P_σ(n)+1 for some valid σ and q does not divide acc, we can
    construct a new valid selection σ' that captures q. The selection σ' agrees
    with σ on steps [0, n) and sets σ'(n) = some q, σ'(k) = none for k > n.

    Key facts:
    1. σ' agrees with σ on [0, n), so mixedWalkProd acc σ' n = mixedWalkProd acc σ n
    2. At step n: σ'(n) = some q, validity requires q prime (from hq) and q | P(n)+1
    3. For k > n: σ'(k) = none, validity is trivially True
    4. Capture: mixedWalkFactor acc σ' n = q -/
theorem hit_implies_capture' {q : ℕ} (hq : Nat.Prime q)
    (acc : ℕ)
    (σ : MixedSelection) (hv : ValidMixedSelection acc σ) (n : ℕ)
    (hdvd : q ∣ mixedWalkProd acc σ n + 1) :
    ∃ σ' : MixedSelection, ValidMixedSelection acc σ' ∧ mixedCaptures q acc σ' := by
  -- Define σ': agree with σ on [0,n), use some q at n, none after
  let σ' : MixedSelection := fun k =>
    if k < n then σ k
    else if k = n then some q
    else none
  have hpref : ∀ i, i < n → σ' i = σ i :=
    fun i hi => by simp only [σ', if_pos hi]
  have hwalk_eq : mixedWalkProd acc σ' n = mixedWalkProd acc σ n :=
    mixedWalkProd_depends_on_prefix acc σ' σ n hpref
  -- σ' at step n
  have hsn : σ' n = some q := by
    simp only [σ', show ¬(n < n) from lt_irrefl n, ite_false, ite_true]
  -- σ' at step k > n
  have hsk : ∀ k, ¬(k < n) → k ≠ n → σ' k = none := by
    intro k hlt hne
    simp only [σ', if_neg hlt, if_neg hne]
  -- Validity of σ'
  have hv' : ValidMixedSelection acc σ' := by
    intro k
    by_cases hlt : k < n
    · -- k < n: σ'(k) = σ(k), walk agrees
      rw [hpref k hlt]
      have hwk : mixedWalkProd acc σ' k = mixedWalkProd acc σ k :=
        mixedWalkProd_depends_on_prefix acc σ' σ k
          (fun i hi => hpref i (by omega))
      have hspec := hv k
      cases hσk : σ k with
      | none => trivial
      | some p =>
        simp only [hσk] at hspec ⊢
        exact ⟨hspec.1, by rw [hwk]; exact hspec.2⟩
    · by_cases heq : k = n
      · subst heq; rw [hsn]; exact ⟨hq, by rw [hwalk_eq]; exact hdvd⟩
      · rw [hsk k hlt heq]; trivial
  -- Capture: factor at step n equals q
  have hcap : mixedWalkFactor acc σ' n = q :=
    mixedWalkFactor_some_eq acc σ' n q hsn
  exact ⟨σ', hv', n, hcap⟩

end WalkModQ

/-! ## Part 19: MixedHitting -- Cleaner Hitting Formulation

MixedHitting is a cleaner formulation of the steering hypothesis: for any
target prime q >= 5, if the standard minFac walk produces composite P+1 at
cofinally many steps, then there exists SOME valid walk (not necessarily the
minFac walk) where q divides P+1 at some step. This immediately implies
capture via `hit_implies_capture'`.

MixedHitting + MixedDiversity together imply MixedMullinConjecture. -/

section MixedHitting

/-- MixedHitting: for any prime q >= 5 and acc >= 2 with q not dividing acc,
    if the minFac walk from acc produces composite P+1 at cofinally many steps,
    then there exists some valid walk from acc where q divides P+1 at some step.

    This is a sufficient condition for capture: once q | P+1, we can select
    factor = q to complete the capture.

    **Status**: open hypothesis. Strictly weaker than DynamicalHitting because
    the mixed walk has freedom to choose non-minFac factors. -/
def MixedHitting : Prop :=
  ∀ (q : ℕ), q.Prime → 5 ≤ q →
    ∀ (acc : ℕ), 2 ≤ acc → ¬(q ∣ acc) →
    (∀ N, ∃ n, N ≤ n ∧ ¬(mixedWalkProd acc minFacMixed n + 1).Prime) →
    ∃ (σ : MixedSelection) (n : ℕ),
      ValidMixedSelection acc σ ∧ q ∣ (mixedWalkProd acc σ n + 1)

/-- MixedHitting implies MixedDiversityWeak: a hit gives a walk with q | P+1,
    then `hit_implies_capture'` converts this to a valid capturing walk. -/
theorem mixed_hitting_implies_diversity_weak :
    MixedHitting → MixedDiversityWeak := by
  intro hmh q hq h5 acc hacc hndvd hdiv
  obtain ⟨σ, n, hv, hdvd⟩ := hmh q hq h5 acc hacc hndvd hdiv
  exact hit_implies_capture' hq acc σ hv n hdvd

/-- MixedHitting + MixedDiversity implies MixedMullinConjecture.
    Composition of mixed_hitting_implies_diversity_weak with the main
    reduction mixed_diversity_weak_implies_mixed_mc. -/
theorem mixed_hitting_diversity_implies_mc
    (hmh : MixedHitting) (hdiv : MixedDiversity) :
    MixedMullinConjecture :=
  mixed_diversity_weak_implies_mixed_mc (mixed_hitting_implies_diversity_weak hmh) hdiv

/-- MixedHitting is sufficient: with MixedDiversity, it closes the entire
    MixedMullinConjecture. This makes MixedHitting an alternative to
    MixedDiversityWeak as the sole open hypothesis. -/
theorem mixed_hitting_is_sufficient :
    (MixedHitting → MixedDiversity → MixedMullinConjecture) :=
  mixed_hitting_diversity_implies_mc

end MixedHitting

/-! ## Part 20: Bridge from Two-Point Walk to MixedMC

The two-point walk (`epsWalkProdFrom` from `RandomTwoPointMC.lean`) uses `ℕ → Bool`
with `true = minFac`, `false = secondMinFac`. The mixed walk uses `MixedSelection`
with `none = minFac`, `some p = specific prime`.

We embed any two-point decision sequence `σ : ℕ → Bool` into a mixed selection
`embedBoolToMixed acc σ` by mapping:
- `true` at step k → `none` (= choose minFac)
- `false` at step k → `some (secondMinFac(P+1))` where P is the TWO-POINT walk's
  accumulator at step k

The key theorem `embed_walk_agreement` shows that under this embedding, the mixed walk
produces exactly the same accumulator sequence as the two-point walk. This is proved
by induction: at each step, both walks use the same factor (either minFac or
secondMinFac of the same value P+1), because the accumulators agree by the IH.

From this, we derive:
1. The embedded selection is valid (factors are prime and divide P+1).
2. If the two-point walk captures q (some factor = q), the mixed walk does too.
3. Composition: any two-point capture gives MixedMC.

This bridges the two-point spectral analysis (UFDStrong → path existence) to the
mixed walk framework, reducing MixedMC to two-point capture from acc = 2. -/

section TwoPointBridge

/-- Embed a Bool decision sequence into a MixedSelection.
    `true` → `none` (choose minFac), `false` → `some (secondMinFac(P+1))`
    where P is the two-point walk's accumulator at that step. -/
def embedBoolToMixed (acc : ℕ) (σ : ℕ → Bool) : MixedSelection :=
  fun k =>
    if σ k then none
    else some (secondMinFac (epsWalkProdFrom acc σ k + 1))

/-- Under the embedding, the mixed walk factor at step n agrees with the
    two-point walk factor, given that the accumulators agree at step n. -/
private theorem embed_factor_eq_aux (acc : ℕ) (σ : ℕ → Bool) (n : ℕ)
    (hwalk : mixedWalkProd acc (embedBoolToMixed acc σ) n = epsWalkProdFrom acc σ n) :
    mixedWalkFactor acc (embedBoolToMixed acc σ) n = epsWalkFactorFrom acc σ n := by
  simp only [mixedWalkFactor, epsWalkFactorFrom, embedBoolToMixed]
  cases σ n with
  | true => simp [hwalk]
  | false => simp

/-- **Walk agreement**: the mixed walk under the Bool embedding produces
    exactly the same accumulator sequence as the two-point walk.

    Proof by induction on n. Base case: both start at acc. Inductive step:
    by IH the accumulators agree at step n, so the factors agree
    (via `embed_factor_eq_aux`), hence the products at step n+1 agree. -/
theorem embed_walk_agreement (acc : ℕ) (σ : ℕ → Bool) (n : ℕ) :
    mixedWalkProd acc (embedBoolToMixed acc σ) n = epsWalkProdFrom acc σ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [mixedWalkProd_succ, epsWalkProdFrom_succ, ih,
        embed_factor_eq_aux acc σ n ih]

/-- **Factor agreement**: the mixed walk factor under the Bool embedding
    agrees with the two-point walk factor. -/
theorem embed_factor_agreement (acc : ℕ) (σ : ℕ → Bool) (n : ℕ) :
    mixedWalkFactor acc (embedBoolToMixed acc σ) n = epsWalkFactorFrom acc σ n :=
  embed_factor_eq_aux acc σ n (embed_walk_agreement acc σ n)

/-- **Validity**: the Bool embedding produces a valid mixed selection
    for acc >= 2. At `true` steps: `none`, trivially valid. At `false` steps:
    `some (secondMinFac(P+1))`, which is prime and divides P+1. -/
theorem embed_valid (acc : ℕ) (hacc : 2 ≤ acc) (σ : ℕ → Bool) :
    ValidMixedSelection acc (embedBoolToMixed acc σ) := by
  intro k
  simp only [embedBoolToMixed]
  cases σ k with
  | true =>
    simp
  | false =>
    simp
    constructor
    · exact secondMinFac_prime (by
        have := epsWalkProdFrom_ge_two acc hacc σ k
        omega)
    · rw [embed_walk_agreement]
      exact secondMinFac_dvd (by
        have := epsWalkProdFrom_ge_two acc hacc σ k
        omega)

/-- If the two-point walk from acc captures q at step n (factor = q), then
    there exists a valid mixed selection from acc that also captures q. -/
theorem two_point_capture_implies_mixed_capture (q acc : ℕ) (hacc : 2 ≤ acc)
    (σ : ℕ → Bool) (n : ℕ) (hcap : epsWalkFactorFrom acc σ n = q) :
    ∃ σ' : MixedSelection, ValidMixedSelection acc σ' ∧ mixedCaptures q acc σ' :=
  ⟨embedBoolToMixed acc σ, embed_valid acc hacc σ, n,
   by rw [embed_factor_agreement]; exact hcap⟩

/-- If ANY two-point walk from acc=2 captures q, then MixedMC q.
    This converts the two-point reachability framework into MixedMC. -/
theorem two_point_capture_implies_mixed_mc (q : ℕ)
    (σ : ℕ → Bool) (n : ℕ) (hcap : epsWalkFactorFrom 2 σ n = q) :
    MixedMC q := by
  intro _
  right
  exact two_point_capture_implies_mixed_capture q 2 (by omega) σ n hcap

/-- The embedding commutes with the `mixedWalkProd_minFac_eq` bridge:
    embedding the all-true sequence gives the all-minFac mixed selection. -/
theorem embed_all_true_eq_minFac (acc : ℕ) :
    embedBoolToMixed acc (fun _ => true) = minFacMixed := by
  ext k
  simp [embedBoolToMixed, minFacMixed]

end TwoPointBridge

/-! ## Part 20b: UFDStrong to MixedMC Bridge

The UFDStrong → path existence chain operates in the abstract group (ZMod q)ˣ
via `paddedUnitSet` (which uses the STANDARD EM sequence's factors from `prod(n)+1`).
The mixed walk is self-consistent: factors depend on the walk's own accumulator,
not the standard sequence's.

This creates a gap: `ufdStrong_implies_path_existence` proves that every element
of (ZMod q)ˣ appears in the abstract product multiset, but the product multiset
models selections from FIXED factor sets (the standard EM orbit), not the
path-dependent factor sets of a mixed walk.

We define `UFDStrongImpliesMixedMC` as an open Prop capturing this gap, and prove
that if it holds, the full chain from UFDStrong to MixedMC is closed. -/

section UFDBridge

/-- **UFDStrongImpliesMixedMC**: bridge from UFDStrong's abstract path existence
    (over padded unit sets of the standard EM orbit) to concrete MixedMC.

    The gap: `ufdStrong_implies_path_existence` shows every unit mod q is reachable
    in the product multiset of `paddedUnitSet` (the standard orbit's factor sets).
    But MixedMC requires constructing a valid `MixedSelection` that achieves this
    reachability through a self-consistent walk (where each step's factor set depends
    on the walk's own accumulator, not the standard orbit's).

    This is the "self-consistent vs non-self-consistent" gap (Session 217).

    **Status**: open hypothesis. -/
def UFDStrongImpliesMixedMC : Prop :=
  ∀ (q : ℕ), q.Prime → 5 ≤ q →
    (∀ (hqp : Fact (Nat.Prime q)), @UFDStrong q hqp) →
    MixedMC q

/-- If UFDStrongImpliesMixedMC holds and UFDStrong holds at every prime q >= 5,
    then MixedMC holds for all primes. -/
theorem ufd_strong_implies_mixed_mc_chain
    (hbridge : UFDStrongImpliesMixedMC)
    (hufd : ∀ (q : ℕ) (hqp : Fact (Nat.Prime q)), 5 ≤ q → @UFDStrong q hqp) :
    MixedMullinConjecture := by
  intro q hq_prime
  by_cases hq2 : q = 2
  · subst hq2; exact mixed_mc_two
  by_cases hq3 : q = 3
  · subst hq3; exact mixed_mc_three
  · have h5 : 5 ≤ q := prime_ge_five_of_ne hq_prime hq2 hq3
    exact hbridge q hq_prime h5 (fun hqp => hufd q hqp h5)

/-- **Two-Point to MixedMC landscape**: summary of the bridge framework.

    1. embed_walk_agreement -- mixed walk = two-point walk under embedding (PROVED)
    2. embed_valid -- embedded selection is valid (PROVED)
    3. embed_factor_agreement -- factors agree (PROVED)
    4. two_point_capture_implies_mixed_capture -- two-point capture gives mixed capture (PROVED)
    5. embed_all_true_eq_minFac -- all-true embedding = all-minFac (PROVED)
    6. UFDStrongImpliesMixedMC is the open bridge from abstract to concrete (OPEN)
    7. ufd_strong_implies_mixed_mc_chain -- UFDStrongImpliesMixedMC closes everything (PROVED) -/
theorem two_point_mixed_mc_landscape (acc : ℕ) (hacc : 2 ≤ acc) (σ : ℕ → Bool) :
    -- 1. Walk agreement
    (∀ n, mixedWalkProd acc (embedBoolToMixed acc σ) n = epsWalkProdFrom acc σ n)
    ∧
    -- 2. Embedding is valid
    ValidMixedSelection acc (embedBoolToMixed acc σ)
    ∧
    -- 3. Factor agreement
    (∀ n, mixedWalkFactor acc (embedBoolToMixed acc σ) n = epsWalkFactorFrom acc σ n)
    ∧
    -- 4. All-true embedding = all-minFac
    (embedBoolToMixed acc (fun _ => true) = minFacMixed)
    ∧
    -- 5. Bridge chain exists
    (UFDStrongImpliesMixedMC →
      (∀ (q : ℕ) (hqp : Fact (Nat.Prime q)), 5 ≤ q → @UFDStrong q hqp) →
      MixedMullinConjecture) :=
  ⟨embed_walk_agreement acc σ,
   embed_valid acc hacc σ,
   embed_factor_agreement acc σ,
   embed_all_true_eq_minFac acc,
   ufd_strong_implies_mixed_mc_chain⟩

end UFDBridge

/-! ## Part 21: Reachable Set Infrastructure

The **reachable set** R_n(acc, q) is the set of positions mod q that can be reached
by some valid mixed walk from accumulator acc in exactly n steps. This captures the
"breadth-first search" advantage of the mixed walk over the deterministic minFac walk.

Key properties:
1. R_0 = {acc mod q} (singleton)
2. R_n ⊆ R_{n+1} is FALSE in general (positions change every step)
3. ⋃_n R_n grows monotonically (union of all reachable positions)
4. MixedHitting ↔ ∃n, (-1 : ZMod q) ∈ R_n (hitting = reachable)
-/

section ReachableSet

/-- The set of positions mod q reachable by a valid mixed walk from accumulator acc
    in exactly n steps. A position `a : ZMod q` is in `reachableAt q acc n` if there
    exists a valid mixed selection sigma such that the walk accumulator at step n
    is congruent to `a` mod q. -/
def reachableAt (q acc : ℕ) (n : ℕ) : Set (ZMod q) :=
  {a : ZMod q | ∃ σ : MixedSelection, ValidMixedSelection acc σ ∧
    (mixedWalkProd acc σ n : ZMod q) = a}

/-- The set of all positions mod q reachable at any step by some valid mixed walk. -/
def reachableEver (q acc : ℕ) : Set (ZMod q) :=
  ⋃ n, reachableAt q acc n

/-- At step 0, the only reachable position is the starting accumulator mod q.
    Every walk starts at `acc`, so `reachableAt q acc 0 = {(acc : ZMod q)}`. -/
theorem reachableAt_zero (q acc : ℕ) :
    reachableAt q acc 0 = {(acc : ZMod q)} := by
  ext a
  simp only [reachableAt, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, _, h⟩
    simp [mixedWalkProd] at h
    exact h.symm
  · intro ha
    exact ⟨minFacMixed, minFacMixed_valid acc, by simp [mixedWalkProd, ha]⟩

/-- The reachable set at any step is nonempty: the all-minFac walk always
    provides a witness. -/
theorem reachableAt_nonempty (q acc : ℕ) (n : ℕ) :
    (reachableAt q acc n).Nonempty :=
  ⟨(mixedWalkProd acc minFacMixed n : ZMod q),
   ⟨minFacMixed, minFacMixed_valid acc, rfl⟩⟩

/-- The ever-reachable set is nonempty: step 0 already provides a position. -/
theorem reachableEver_nonempty (q acc : ℕ) :
    (reachableEver q acc).Nonempty := by
  exact Set.nonempty_iUnion.mpr ⟨0, reachableAt_nonempty q acc 0⟩

/-- The standard minFac walk's position at step n is always in the reachable set. -/
theorem minFac_walk_in_reachable (q acc : ℕ) (n : ℕ) :
    (mixedWalkProd acc minFacMixed n : ZMod q) ∈ reachableAt q acc n :=
  ⟨minFacMixed, minFacMixed_valid acc, rfl⟩

/-- **Hitting ↔ Reachable**: A valid walk captures q (i.e., q divides P+1 at
    some step) if and only if -1 mod q is in the reachable set at some step.

    More precisely: for q prime, q >= 5, acc >= 2 with q not dividing acc,
    the existence of a valid walk with q | P(n)+1 is equivalent to
    (-1 : ZMod q) appearing in some reachable set.

    This reformulates the hitting condition as a reachability condition. -/
theorem mixed_hitting_iff_neg_one_reachable (q : ℕ) (acc : ℕ) :
    (∃ (σ : MixedSelection) (n : ℕ),
      ValidMixedSelection acc σ ∧ q ∣ (mixedWalkProd acc σ n + 1))
    ↔ ∃ n, (-1 : ZMod q) ∈ reachableAt q acc n := by
  constructor
  · rintro ⟨σ, n, hv, hdvd⟩
    refine ⟨n, σ, hv, ?_⟩
    have h0 : ((mixedWalkProd acc σ n + 1 : ℕ) : ZMod q) = 0 := by
      rwa [ZMod.natCast_eq_zero_iff]
    have h1 : (mixedWalkProd acc σ n : ZMod q) + 1 = 0 := by
      push_cast at h0; exact h0
    calc (mixedWalkProd acc σ n : ZMod q)
        = (mixedWalkProd acc σ n : ZMod q) + 1 - 1 := by ring
      _ = 0 - 1 := by rw [h1]
      _ = -1 := by ring
  · rintro ⟨n, σ, hv, hmod⟩
    refine ⟨σ, n, hv, ?_⟩
    have h1 : (mixedWalkProd acc σ n : ZMod q) + 1 = 0 := by
      rw [hmod]; ring
    have h2 : ((mixedWalkProd acc σ n + 1 : ℕ) : ZMod q) = 0 := by
      push_cast; exact h1
    rwa [ZMod.natCast_eq_zero_iff] at h2

end ReachableSet

/-! ## Part 22: Reachable Set Growth from Branching

When P+1 is composite, the factor set has ≥ 2 distinct prime factors. If these
give different residues mod q, the reachable set at the next step gains new elements.
We formalize the factor set modulo q and its basic cardinality properties. -/

section FactorSet

/-- The factor set of P+1 modulo q: the set of residues mod q of prime factors
    of P+1 that are different from q. These are the possible "multipliers" for
    the walk at a step where the accumulator is P.

    We filter `Finset.range (P + 2)` by: the value is prime, divides P+1, and is not q. -/
def factorSetModQ (q P : ℕ) : Finset (ZMod q) :=
  ((Finset.range (P + 2)).filter (fun p => p.Prime ∧ p ∣ (P + 1) ∧ p ≠ q)).image
    (fun (p : ℕ) => (p : ZMod q))

/-- minFac(P+1) is always in the factor set (when P ≥ 1 and minFac(P+1) ≠ q).
    Since P ≥ 1, P+1 ≥ 2, so minFac(P+1) is a well-defined prime dividing P+1.
    We also need minFac(P+1) < P+2, which holds since minFac(P+1) ≤ P+1 < P+2. -/
theorem minFac_mem_factorSetModQ {q P : ℕ} (hP : 1 ≤ P)
    (hneq : (P + 1).minFac ≠ q) :
    ((P + 1).minFac : ZMod q) ∈ factorSetModQ q P := by
  apply Finset.mem_image.mpr
  refine ⟨(P + 1).minFac, ?_, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr ?_, Nat.minFac_prime (by omega), Nat.minFac_dvd _, hneq⟩
  have := Nat.minFac_le (by omega : 0 < P + 1)
  omega

/-- The factor set is nonempty when P ≥ 1 and minFac(P+1) ≠ q:
    minFac(P+1) is always a valid member. -/
theorem factorSetModQ_nonempty {q P : ℕ} (hP : 1 ≤ P)
    (hneq : (P + 1).minFac ≠ q) :
    (factorSetModQ q P).Nonempty :=
  ⟨_, minFac_mem_factorSetModQ hP hneq⟩

/-- When P+1 is composite and P ≥ 1, P+1 has at least two prime factor slots
    (counting multiplicity): minFac(P+1) and a prime factor of the quotient
    (P+1)/minFac(P+1). These may be the SAME prime (e.g. P+1 = p²), but the
    quotient is ≥ 2 and has its own prime factor.

    We prove: there exists a prime p (possibly equal to minFac) with p | (P+1)
    and p | (P+1)/minFac(P+1). -/
theorem not_prime_exists_quotient_factor {P : ℕ} (hP : 1 ≤ P)
    (hnp : ¬(P + 1).Prime) :
    ∃ p, p.Prime ∧ p ∣ (P + 1) ∧ (P + 1).minFac ≤ p := by
  have hmf_lt : (P + 1).minFac < P + 1 :=
    Nat.not_prime_iff_minFac_lt (by omega) |>.mp hnp
  have hdvd : (P + 1).minFac ∣ (P + 1) := Nat.minFac_dvd _
  obtain ⟨c, hc⟩ := hdvd
  have hc_ne_one : c ≠ 1 := by intro heq; rw [heq, mul_one] at hc; omega
  set p := c.minFac
  have hp_prime : p.Prime := Nat.minFac_prime hc_ne_one
  have hp_dvd_c : p ∣ c := Nat.minFac_dvd c
  have hp_dvd : p ∣ (P + 1) := by rw [hc]; exact dvd_mul_of_dvd_right hp_dvd_c _
  have hp_ge : (P + 1).minFac ≤ p :=
    Nat.minFac_le_of_dvd hp_prime.two_le hp_dvd
  exact ⟨p, hp_prime, hp_dvd, hp_ge⟩

/-- When P+1 is composite and P ≥ 1, the quotient (P+1)/minFac(P+1) is at least 2,
    and it has its own prime factor. This gives a second prime dividing P+1 (possibly
    equal to minFac). In fact, the underlying set of primes dividing P+1 has at
    least 2 elements as naturals (but they might be equal, e.g. P+1 = p²). -/
theorem not_prime_quotient_ge_two {P : ℕ} (hP : 1 ≤ P)
    (hnp : ¬(P + 1).Prime) :
    2 ≤ (P + 1) / (P + 1).minFac := by
  have hmf_lt : (P + 1).minFac < P + 1 :=
    Nat.not_prime_iff_minFac_lt (by omega) |>.mp hnp
  have hmf_pos : 0 < (P + 1).minFac := Nat.minFac_pos _
  have hmf_dvd : (P + 1).minFac ∣ (P + 1) := Nat.minFac_dvd _
  obtain ⟨c, hc⟩ := hmf_dvd
  have hc_ne_one : c ≠ 1 := by
    intro heq; rw [heq, mul_one] at hc; omega
  have hmf_ge2 : 2 ≤ (P + 1).minFac :=
    (Nat.minFac_prime (by omega : P + 1 ≠ 1)).two_le
  have hc_ge2 : 2 ≤ c := by
    by_contra h; push Not at h
    interval_cases c <;> omega
  have hdiv_eq : (P + 1) / (P + 1).minFac = c := by
    have : (P + 1).minFac * c / (P + 1).minFac = c :=
      Nat.mul_div_cancel_left c hmf_pos
    rwa [← hc] at this
  omega

end FactorSet

/-! ## Part 23: Perpetual Primality Structural Constraints

If the minFac walk produces P(n)+1 prime for ALL n ≥ N, then the walk follows
the recurrence P(n+1) = P(n) * (P(n)+1) (since minFac of a prime is itself),
giving P(n+1) + 1 = P(n)² + P(n) + 1.

This is the cyclotomic polynomial Phi_3 evaluated at P(n). We prove:
- The recurrence P → P*(P+1) holds under perpetual primality.
- P² + P + 1 ≡ 0 mod 3 whenever P ≡ 1 mod 3.
- Therefore, under perpetual primality, the walk can never reach P ≡ 1 mod 3
  (which would force P²+P+1 to be composite, contradicting perpetual primality). -/

section PerpetualPrimality

/-- Under perpetual primality (P+1 is prime at all steps from N onward),
    the walk follows P(n+1) = P(n) * (P(n)+1), because minFac of a prime is
    itself, so the factor chosen at each step is P(n)+1. -/
theorem perpetual_prime_recurrence (acc : ℕ) (N : ℕ)
    (hperp : ∀ k, (mixedWalkProd acc minFacMixed (N + k) + 1).Prime) (k : ℕ) :
    mixedWalkProd acc minFacMixed (N + k + 1) =
    mixedWalkProd acc minFacMixed (N + k) *
      (mixedWalkProd acc minFacMixed (N + k) + 1) := by
  rw [mixedWalkProd_succ]
  congr 1
  simp only [mixedWalkFactor, minFacMixed]
  exact (hperp k).minFac_eq

/-- Under perpetual primality, the "+1 recurrence" takes the form
    P(n+1) + 1 = P(n)² + P(n) + 1, which is Phi_3(P(n)). -/
theorem perpetual_prime_cyclotomic (acc : ℕ) (N : ℕ)
    (hperp : ∀ k, (mixedWalkProd acc minFacMixed (N + k) + 1).Prime) (k : ℕ) :
    mixedWalkProd acc minFacMixed (N + k + 1) + 1 =
    (mixedWalkProd acc minFacMixed (N + k)) ^ 2 +
      mixedWalkProd acc minFacMixed (N + k) + 1 := by
  rw [perpetual_prime_recurrence acc N hperp k]
  ring

/-- If P ≡ 1 mod 3 and P ≥ 2, then 3 divides P² + P + 1.

    Proof: P ≡ 1 mod 3 means P = 3k+1 for some k. Then
    P² + P + 1 = (3k+1)² + (3k+1) + 1 = 9k² + 6k + 1 + 3k + 1 + 1
    = 9k² + 9k + 3 = 3(3k² + 3k + 1). -/
theorem mod3_one_divides_cyclotomic (P : ℕ) (hmod : P % 3 = 1) :
    3 ∣ P ^ 2 + P + 1 := by
  obtain ⟨k, hk⟩ : ∃ k, P = 3 * k + 1 := by
    exact ⟨P / 3, by omega⟩
  rw [hk]; ring_nf
  -- 9*k^2 + 9*k + 3 = 3 * (3*k^2 + 3*k + 1)
  exact ⟨3 * k ^ 2 + 3 * k + 1, by ring⟩

/-- If P ≡ 1 mod 3 and P ≥ 2, then P² + P + 1 ≥ 7. -/
theorem cyclotomic_ge_seven (P : ℕ) (hP : 2 ≤ P) :
    7 ≤ P ^ 2 + P + 1 := by
  nlinarith [sq_nonneg P]

/-- If P ≡ 1 mod 3 and P ≥ 2, then P² + P + 1 is composite (divisible by 3 and ≥ 7,
    hence not 1, 2, or 3). -/
theorem cyclotomic_not_prime_of_mod3_one (P : ℕ) (hP : 2 ≤ P) (hmod : P % 3 = 1) :
    ¬(P ^ 2 + P + 1).Prime := by
  have hdvd := mod3_one_divides_cyclotomic P hmod
  have hge := cyclotomic_ge_seven P hP
  intro hprime
  have h3_or := hprime.eq_one_or_self_of_dvd 3 hdvd
  rcases h3_or with h1 | h3
  · omega
  · omega

/-- Under perpetual primality from step N, the walk at step N+k can never
    satisfy P ≡ 1 mod 3 (for k ≥ 1): if it did, P²+P+1 would be composite
    (by `cyclotomic_not_prime_of_mod3_one`), contradicting perpetual primality.

    This gives a structural constraint: the walk mod 3 stays in {0, 2} forever. -/
theorem perpetual_prime_excludes_mod3_one (acc : ℕ) (hacc : 2 ≤ acc) (N : ℕ)
    (hperp : ∀ k, (mixedWalkProd acc minFacMixed (N + k) + 1).Prime) (k : ℕ) :
    (mixedWalkProd acc minFacMixed (N + k)) % 3 ≠ 1 := by
  intro hmod
  have hge := mixedWalkProd_ge_two acc hacc minFacMixed (minFacMixed_valid acc) (N + k)
  have hcycl := perpetual_prime_cyclotomic acc N hperp k
  have hnp := cyclotomic_not_prime_of_mod3_one
    (mixedWalkProd acc minFacMixed (N + k)) hge hmod
  have hp := hperp (k + 1)
  rw [show N + (k + 1) = N + k + 1 from by omega] at hp
  rw [hcycl] at hp
  exact hnp hp

/-- **Perpetual primality landscape**: summary of structural constraints.

    1. perpetual_prime_recurrence -- P(n+1) = P(n) * (P(n)+1) under perpetual primality
    2. perpetual_prime_cyclotomic -- P(n+1)+1 = P(n)² + P(n) + 1 (Phi_3 recurrence)
    3. mod3_one_divides_cyclotomic -- P ≡ 1 mod 3 ⇒ 3 | P²+P+1
    4. cyclotomic_not_prime_of_mod3_one -- P ≡ 1 mod 3, P ≥ 2 ⇒ P²+P+1 composite
    5. perpetual_prime_excludes_mod3_one -- perpetual primality ⇒ walk never ≡ 1 mod 3
    6. not_prime_quotient_ge_two -- composite P+1 ⇒ (P+1)/minFac ≥ 2
    7. not_prime_exists_quotient_factor -- composite P+1 ⇒ ∃ prime factor ≥ minFac -/
theorem perpetual_primality_landscape (acc : ℕ) (hacc : 2 ≤ acc) (N : ℕ)
    (hperp : ∀ k, (mixedWalkProd acc minFacMixed (N + k) + 1).Prime) :
    -- 1. Recurrence holds
    (∀ k, mixedWalkProd acc minFacMixed (N + k + 1) =
      mixedWalkProd acc minFacMixed (N + k) *
        (mixedWalkProd acc minFacMixed (N + k) + 1))
    ∧
    -- 2. Cyclotomic form
    (∀ k, mixedWalkProd acc minFacMixed (N + k + 1) + 1 =
      (mixedWalkProd acc minFacMixed (N + k)) ^ 2 +
        mixedWalkProd acc minFacMixed (N + k) + 1)
    ∧
    -- 3. Walk never ≡ 1 mod 3
    (∀ k, (mixedWalkProd acc minFacMixed (N + k)) % 3 ≠ 1)
    ∧
    -- 4. Phi_3 at P ≡ 1 mod 3 is composite
    (∀ P, 2 ≤ P → P % 3 = 1 → ¬(P ^ 2 + P + 1).Prime) :=
  ⟨perpetual_prime_recurrence acc N hperp,
   perpetual_prime_cyclotomic acc N hperp,
   perpetual_prime_excludes_mod3_one acc hacc N hperp,
   fun P hP hmod => cyclotomic_not_prime_of_mod3_one P hP hmod⟩

end PerpetualPrimality

/-! ## Part 24: Reachable Set Growth Properties

The reachable set `reachableAt q acc n` grows as the walk branches. At each step,
any valid walk can be extended by choosing any prime factor of P+1 as the next
multiplier. We formalize:

1. `reachableAt_subset_reachableEver` — R_n ⊆ R_∞ (trivially from union)
2. `reachableAt_from_factor` — given a walk σ reaching P at step n, any prime p
   dividing P+1 yields (P * p : ZMod q) ∈ R_{n+1} (by constructing σ' that
   agrees with σ on [0,n) and chooses p at step n)
3. `reachable_grows_pair` — if P+1 has two distinct prime factors p₁ ≠ p₂
   (both ≠ q), then BOTH (P * p₁ : ZMod q) and (P * p₂ : ZMod q) are in R_{n+1}
4. `reachable_growth_landscape` — summary conjunction

The key construction: given σ valid reaching position a at step n, define
  σ'(k) := if k < n then σ(k) else if k = n then some p else none
Then σ' is valid, agrees with σ on [0,n), and chooses p at step n. -/

section ReachableGrowth

/-- Every position reachable at step n is in the ever-reachable set. -/
theorem reachableAt_subset_reachableEver (q acc : ℕ) (n : ℕ) :
    reachableAt q acc n ⊆ reachableEver q acc :=
  Set.subset_iUnion _ n

/-- The starting position is in the ever-reachable set. -/
theorem acc_mem_reachableEver (q acc : ℕ) :
    (acc : ZMod q) ∈ reachableEver q acc := by
  apply reachableAt_subset_reachableEver q acc 0
  rw [reachableAt_zero]
  exact Set.mem_singleton _

/-- **Core growth lemma**: Given a valid walk σ reaching accumulator P at step n,
    and any prime p with p | P+1, the position (P * p : ZMod q) is reachable
    at step n+1.

    The construction builds σ' that agrees with σ on [0,n), chooses p at step n,
    and uses minFac (none) for all subsequent steps. Validity of σ' follows from:
    - Steps k < n: σ'(k) = σ(k), walk agrees with σ, so validity inherits from hv
    - Step n: σ'(n) = some p, need p prime and p | P+1 (given by hypotheses)
    - Steps k > n: σ'(k) = none, validity is trivially True -/
theorem reachableAt_from_factor {q acc : ℕ} {n : ℕ}
    {σ : MixedSelection} (hv : ValidMixedSelection acc σ)
    {p : ℕ} (hp : p.Prime) (hdvd : p ∣ mixedWalkProd acc σ n + 1) :
    (mixedWalkProd acc σ n * p : ZMod q) ∈ reachableAt q acc (n + 1) := by
  -- Define σ': agree with σ on [0,n), use some p at n, none after
  let σ' : MixedSelection := fun k =>
    if k < n then σ k
    else if k = n then some p
    else none
  -- Prefix agreement
  have hpref : ∀ i, i < n → σ' i = σ i :=
    fun i hi => by simp only [σ', if_pos hi]
  -- Walk agreement at step n
  have hwalk_eq : mixedWalkProd acc σ' n = mixedWalkProd acc σ n :=
    mixedWalkProd_depends_on_prefix acc σ' σ n hpref
  -- σ' at step n
  have hsn : σ' n = some p := by
    simp only [σ', show ¬(n < n) from lt_irrefl n, ite_false, ite_true]
  -- Validity of σ'
  have hv' : ValidMixedSelection acc σ' := by
    intro k
    by_cases hlt : k < n
    · -- k < n: σ'(k) = σ(k), walk agrees
      rw [hpref k hlt]
      have hwk : mixedWalkProd acc σ' k = mixedWalkProd acc σ k :=
        mixedWalkProd_depends_on_prefix acc σ' σ k
          (fun i hi => hpref i (by omega))
      have hspec := hv k
      cases hσk : σ k with
      | none => trivial
      | some r =>
        simp only [hσk] at hspec ⊢
        exact ⟨hspec.1, by rw [hwk]; exact hspec.2⟩
    · by_cases heq : k = n
      · subst heq; rw [hsn]; exact ⟨hp, by rw [hwalk_eq]; exact hdvd⟩
      · have : σ' k = none := by
          simp only [σ', if_neg hlt, if_neg heq]
        rw [this]; trivial
  -- Walk at step n+1
  have hstep : mixedWalkProd acc σ' (n + 1) = mixedWalkProd acc σ n * p := by
    rw [mixedWalkProd_succ, hwalk_eq]
    congr 1
    exact mixedWalkFactor_some_eq acc σ' n p hsn
  -- Conclusion: (P * p : ZMod q) ∈ R_{n+1}
  exact ⟨σ', hv', by simp only [hstep, Nat.cast_mul]⟩

/-- The minFac walk's next position is always reachable: since minFac(P+1) is
    prime and divides P+1, the standard walk naturally extends the reachable set. -/
theorem reachableAt_minFac_step (q acc : ℕ) (hacc : 2 ≤ acc) (n : ℕ) :
    (mixedWalkProd acc minFacMixed n *
      (mixedWalkProd acc minFacMixed n + 1).minFac : ZMod q) ∈
    reachableAt q acc (n + 1) := by
  apply reachableAt_from_factor (minFacMixed_valid acc)
  · exact Nat.minFac_prime (by
      have := mixedWalkProd_ge_two acc hacc minFacMixed (minFacMixed_valid acc) n
      omega)
  · exact Nat.minFac_dvd _

/-- **Growth pair**: If the accumulator P at step n (via walk σ) satisfies P+1
    having two prime factors p₁ and p₂ (both dividing P+1), then BOTH
    (P * p₁ : ZMod q) and (P * p₂ : ZMod q) are in R_{n+1}.

    When p₁ and p₂ give distinct residues mod q (i.e., (p₁ : ZMod q) ≠ (p₂ : ZMod q)),
    and (P : ZMod q) is a unit, this means |R_{n+1}| ≥ 2 along this branch.

    This is the mechanism by which composite P+1 causes the reachable set to grow. -/
theorem reachable_grows_pair {q acc : ℕ} {n : ℕ}
    {σ : MixedSelection} (hv : ValidMixedSelection acc σ)
    {p₁ p₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime)
    (hdvd₁ : p₁ ∣ mixedWalkProd acc σ n + 1)
    (hdvd₂ : p₂ ∣ mixedWalkProd acc σ n + 1) :
    (mixedWalkProd acc σ n * p₁ : ZMod q) ∈ reachableAt q acc (n + 1) ∧
    (mixedWalkProd acc σ n * p₂ : ZMod q) ∈ reachableAt q acc (n + 1) :=
  ⟨reachableAt_from_factor hv hp₁ hdvd₁,
   reachableAt_from_factor hv hp₂ hdvd₂⟩

/-- **Composite branching**: When P+1 is composite (P ≥ 1), it has at least
    two prime divisor slots. Together with `reachable_grows_pair`, this shows
    that composite accumulators yield at least two reachable positions at the
    next step (as naturals, though they may collide mod q). -/
theorem reachable_composite_branch {q acc : ℕ} (hacc : 2 ≤ acc) {n : ℕ}
    {σ : MixedSelection} (hv : ValidMixedSelection acc σ)
    (hnp : ¬(mixedWalkProd acc σ n + 1).Prime) :
    ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
    p₁ ∣ (mixedWalkProd acc σ n + 1) ∧ p₂ ∣ (mixedWalkProd acc σ n + 1) ∧
    (mixedWalkProd acc σ n + 1).minFac ≤ p₂ ∧
    (mixedWalkProd acc σ n * p₁ : ZMod q) ∈ reachableAt q acc (n + 1) ∧
    (mixedWalkProd acc σ n * p₂ : ZMod q) ∈ reachableAt q acc (n + 1) := by
  set P := mixedWalkProd acc σ n
  have hP : 1 ≤ P := by
    have := mixedWalkProd_ge_two acc hacc σ hv n; omega
  obtain ⟨p₂, hp₂_prime, hp₂_dvd, hp₂_ge⟩ := not_prime_exists_quotient_factor hP hnp
  set p₁ := (P + 1).minFac
  have hp₁_prime : p₁.Prime := Nat.minFac_prime (by omega)
  have hp₁_dvd : p₁ ∣ (P + 1) := Nat.minFac_dvd _
  exact ⟨p₁, p₂, hp₁_prime, hp₂_prime, hp₁_dvd, hp₂_dvd, hp₂_ge,
    reachableAt_from_factor hv hp₁_prime hp₁_dvd,
    reachableAt_from_factor hv hp₂_prime hp₂_dvd⟩

/-- **Reachable-ever growth**: If a ∈ reachableEver and σ witnesses a at step n,
    then for any prime p dividing the walk accumulator + 1, the next position
    (a * p : ZMod q) is also in reachableEver. -/
theorem reachableEver_from_factor {q acc : ℕ} {n : ℕ}
    {σ : MixedSelection} (hv : ValidMixedSelection acc σ)
    {p : ℕ} (hp : p.Prime) (hdvd : p ∣ mixedWalkProd acc σ n + 1) :
    (mixedWalkProd acc σ n * p : ZMod q) ∈ reachableEver q acc :=
  reachableAt_subset_reachableEver q acc (n + 1)
    (reachableAt_from_factor hv hp hdvd)

/-- **Reachable set growth landscape**: summary of reachable set growth properties.

    1. reachableAt_subset_reachableEver — R_n ⊆ R_∞
    2. acc_mem_reachableEver — starting position is reachable
    3. reachableAt_from_factor — prime factor branching grows R_{n+1}
    4. reachable_grows_pair — two prime factors give two elements in R_{n+1}
    5. reachable_composite_branch — composite P+1 yields branching -/
theorem reachable_growth_landscape (q acc : ℕ) (hacc : 2 ≤ acc) :
    -- 1. Reachable sets nest into ever-reachable
    (∀ n, reachableAt q acc n ⊆ reachableEver q acc)
    ∧
    -- 2. Starting position is ever-reachable
    ((acc : ZMod q) ∈ reachableEver q acc)
    ∧
    -- 3. Factor branching (existential witness)
    (∀ n (σ : MixedSelection), ValidMixedSelection acc σ →
      ∀ p : ℕ, p.Prime → p ∣ (mixedWalkProd acc σ n + 1) →
      (mixedWalkProd acc σ n * p : ZMod q) ∈ reachableAt q acc (n + 1))
    ∧
    -- 4. Composite branching yields two positions
    (∀ n (σ : MixedSelection), ValidMixedSelection acc σ →
      ¬(mixedWalkProd acc σ n + 1).Prime →
      ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
        (mixedWalkProd acc σ n * p₁ : ZMod q) ∈ reachableAt q acc (n + 1) ∧
        (mixedWalkProd acc σ n * p₂ : ZMod q) ∈ reachableAt q acc (n + 1)) :=
  ⟨fun n => reachableAt_subset_reachableEver q acc n,
   acc_mem_reachableEver q acc,
   fun n σ hv p hp hdvd => reachableAt_from_factor hv hp hdvd,
   fun n σ hv hnp => by
     obtain ⟨p₁, p₂, hp₁, hp₂, hd₁, hd₂, _, hr₁, hr₂⟩ :=
       reachable_composite_branch hacc hv hnp
     exact ⟨p₁, p₂, hp₁, hp₂, hr₁, hr₂⟩⟩

end ReachableGrowth

/-! ## Part 25: Reachable Set Coset Impossibility

Under MC(< q) (all primes below q appear in the EM sequence) and the assumption
that q itself never appears, the ever-reachable set R_∞(q, 2) is NOT contained
in any proper coset g·H of (ZMod q)ˣ.

The proof uses PrimeResidueEscape (proved elementarily in Bootstrap.lean):
for any proper subgroup H < (ZMod q)ˣ, there exists a prime r ∈ [3, q) with
r mod q ∉ H. By MC(< q), r = seq(k) for some k ≥ 1. Then r | prod(k-1) + 1,
so both prod(k-1) mod q and prod(k-1)·r mod q are in R_∞. Their ratio is
r mod q ∉ H, contradicting R_∞ ⊆ g·H (which forces all ratios into H).
-/

section CosetImpossibility

/-- The standard all-minFac mixed walk from accumulator 2 recovers the EM product.
    Chain: mixedWalkProd_minFac_eq → epsWalkProdFrom_two_eq → epsWalkProd_emDecision. -/
theorem mixedWalkProd_two_minFac_eq_prod (n : ℕ) :
    mixedWalkProd 2 minFacMixed n = prod n := by
  rw [mixedWalkProd_minFac_eq, epsWalkProdFrom_two_eq]
  exact epsWalkProd_emDecision n

/-- Under hne (q never in seq), q does not divide prod(n), hence
    (prod n : ZMod q) is nonzero. -/
private theorem prod_cast_ne_zero {q : ℕ} [Fact (Nat.Prime q)]
    (hne : ∀ k, seq k ≠ q) (n : ℕ) : ((prod n : ℕ) : ZMod q) ≠ 0 := by
  intro h
  have hdvd : q ∣ prod n := (ZMod.natCast_eq_zero_iff (prod n) q).mp h
  exact prime_not_in_seq_not_dvd_prod (Fact.out : Nat.Prime q).toIsPrime hne n hdvd

/-- A prime r < q maps to a nonzero element of ZMod q. -/
private theorem natCast_prime_ne_zero' {q r : ℕ} [Fact (Nat.Prime q)]
    (hr : Nat.Prime r) (hrq : r < q) : ((r : ℕ) : ZMod q) ≠ 0 := by
  intro h
  have hdvd : q ∣ r := (ZMod.natCast_eq_zero_iff r q).mp h
  exact absurd (Nat.le_of_dvd hr.pos hdvd) (by omega)

/-- The standard EM walk position at step n is in R_∞(q, 2).
    This is `minFac_walk_in_reachable` lifted to `reachableEver`. -/
private theorem prod_in_reachableEver (q : ℕ) (n : ℕ) :
    (mixedWalkProd 2 minFacMixed n : ZMod q) ∈ reachableEver q 2 :=
  reachableAt_subset_reachableEver q 2 n (minFac_walk_in_reachable q 2 n)

/-- If r is a prime dividing prod(k) + 1, then ((prod k : ℕ) : ZMod q) * (r : ZMod q)
    is in R_∞(q, 2). -/
private theorem prod_mul_prime_in_reachableEver (q : ℕ) {k : ℕ} {r : ℕ}
    (hr : r.Prime) (hdvd : r ∣ prod k + 1) :
    ((prod k : ℕ) : ZMod q) * ((r : ℕ) : ZMod q) ∈ reachableEver q 2 := by
  have hmem := @reachableEver_from_factor q 2 k minFacMixed (minFacMixed_valid 2)
    r hr (by rw [mixedWalkProd_two_minFac_eq_prod]; exact hdvd)
  simp only [mixedWalkProd_two_minFac_eq_prod] at hmem
  exact_mod_cast hmem

/-- Under hne, the product of prod(k) * r mod q is nonzero when r < q is prime. -/
private theorem prod_mul_prime_cast_ne_zero {q : ℕ} [Fact (Nat.Prime q)]
    (hne : ∀ k, seq k ≠ q) (k : ℕ) {r : ℕ} (hr : Nat.Prime r) (hrq : r < q) :
    ((prod k * r : ℕ) : ZMod q) ≠ 0 := by
  push_cast
  exact mul_ne_zero (prod_cast_ne_zero hne k) (natCast_prime_ne_zero' hr hrq)

/-- **Escaping prime produces escaping ratio**: Given a prime r ∈ [3, q) from
    PrimeResidueEscape and its index k from MC(< q), both prod(k-1) mod q and
    prod(k-1)·r mod q are in R_∞, and their ratio r mod q is in (ZMod q)ˣ.

    Concretely: if c = prod(k') and c·r are both in R_∞ and both nonzero mod q,
    then (Units.mk0 (c·r) h₁) * (Units.mk0 c h₂)⁻¹ = Units.mk0 r h₃. -/
private theorem ratio_of_reachable_pair {q : ℕ} [hfact : Fact (Nat.Prime q)]
    (hne : ∀ k, seq k ≠ q) (k' : ℕ) {r : ℕ} (hr : Nat.Prime r) (hrq : r < q) :
    Units.mk0 ((prod k' * r : ℕ) : ZMod q) (prod_mul_prime_cast_ne_zero hne k' hr hrq) *
    (Units.mk0 ((prod k' : ℕ) : ZMod q) (prod_cast_ne_zero hne k'))⁻¹ =
    Units.mk0 ((r : ℕ) : ZMod q) (natCast_prime_ne_zero' hr hrq) := by
  ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
  have hc : ((prod k' : ℕ) : ZMod q) ≠ 0 := prod_cast_ne_zero hne k'
  have hcast : ((prod k' * r : ℕ) : ZMod q) = ((prod k' : ℕ) : ZMod q) * ((r : ℕ) : ZMod q) := by
    push_cast; ring
  rw [hcast]
  field_simp

/-- **Reachable ratio escape**: Under MC(< q) and q never in seq, for every
    proper subgroup H < (ZMod q)ˣ, there exist two elements of R_∞(q, 2)
    (both nonzero mod q) whose ratio as units lies outside H.

    Proof: PRE gives r ∈ [3, q) prime with r mod q ∉ H. MC(< q) gives k with
    seq(k) = r. Since k ≥ 1 (as r ≥ 3 ≠ 2 = seq(0)), write k = k' + 1.
    Then r | prod(k') + 1 (by seq_dvd_succ_prod). Both prod(k') mod q and
    prod(k') · r mod q are in R_∞, and their ratio is r mod q ∉ H. -/
theorem reachableEver_ratios_escape_subgroup
    (q : ℕ) [hfact : Fact (Nat.Prime q)] (hq5 : 5 ≤ q)
    (hmc : MCBelow q) (hne : ∀ k, seq k ≠ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ (u₁ u₂ : (ZMod q)ˣ),
      (↑u₁ : ZMod q) ∈ reachableEver q 2 ∧
      (↑u₂ : ZMod q) ∈ reachableEver q 2 ∧
      u₁ * u₂⁻¹ ∉ H := by
  -- Step 1: Get escaping prime from PrimeResidueEscape
  obtain ⟨r, hr_prime, hrq, hr3, hr_escape⟩ := prime_residue_escape q hq5 H hH
  -- Step 2: Get index where r enters the sequence from MC(< q)
  obtain ⟨k, hk⟩ := hmc r hr_prime hrq
  -- Step 3: k ≥ 1 since seq(0) = 2 and r ≥ 3
  have hk_pos : 0 < k := by
    rcases k with _ | k'
    · simp only [seq_zero] at hk; omega
    · omega
  -- Step 4: Write k = k' + 1
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  -- Step 5: seq(k'+1) = r, so r | prod(k') + 1
  have hr_dvd : r ∣ prod k' + 1 := by
    have : seq (k' + 1) ∣ prod k' + 1 := seq_dvd_succ_prod k'
    rwa [hk] at this
  -- Step 6: Construct the two units
  set u₁ : (ZMod q)ˣ := Units.mk0 ((prod k' * r : ℕ) : ZMod q)
    (prod_mul_prime_cast_ne_zero hne k' hr_prime hrq)
  set u₂ : (ZMod q)ˣ := Units.mk0 ((prod k' : ℕ) : ZMod q)
    (prod_cast_ne_zero hne k')
  refine ⟨u₁, u₂, ?_, ?_, ?_⟩
  -- Step 7: u₁ ∈ R_∞ (prod(k') * r mod q is reachable)
  · show ((prod k' * r : ℕ) : ZMod q) ∈ reachableEver q 2
    have := prod_mul_prime_in_reachableEver q hr_prime hr_dvd
    exact_mod_cast this
  -- Step 8: u₂ ∈ R_∞ (prod(k') mod q is reachable)
  · show ((prod k' : ℕ) : ZMod q) ∈ reachableEver q 2
    have := prod_in_reachableEver q k'
    simp only [mixedWalkProd_two_minFac_eq_prod] at this
    exact this
  -- Step 9: u₁ * u₂⁻¹ = r mod q ∉ H
  · rw [ratio_of_reachable_pair hne k' hr_prime hrq]
    exact hr_escape

/-- **Reachable set coset impossibility**: Under MC(< q) and q never in seq,
    the ever-reachable set R_∞(q, 2) is not contained in any left coset g·H
    of a proper subgroup H < (ZMod q)ˣ.

    This means R_∞ cannot be "trapped" in any coset structure, which is a
    key obstruction to algebraic approaches trying to confine the walk.

    Proof: If R_∞ ⊆ g·H, then for any u₁, u₂ ∈ R_∞ we have u₁·u₂⁻¹ ∈ H.
    But `reachableEver_ratios_escape_subgroup` gives u₁, u₂ ∈ R_∞ with
    u₁·u₂⁻¹ ∉ H. Contradiction. -/
theorem reachableEver_not_in_coset
    (q : ℕ) [hfact : Fact (Nat.Prime q)] (hq5 : 5 ≤ q)
    (hmc : MCBelow q) (hne : ∀ k, seq k ≠ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) (g : (ZMod q)ˣ) :
    ¬ (∀ x ∈ reachableEver q 2, ∃ h ∈ H, (x : ZMod q) = ↑(g * h)) := by
  intro hcoset
  -- Get escaping pair from ratio escape
  obtain ⟨u₁, u₂, hu₁, hu₂, hratio⟩ :=
    reachableEver_ratios_escape_subgroup q hq5 hmc hne H hH
  -- Both u₁ and u₂ are in the coset g·H
  obtain ⟨h₁, hh₁, heq₁⟩ := hcoset (↑u₁) hu₁
  obtain ⟨h₂, hh₂, heq₂⟩ := hcoset (↑u₂) hu₂
  -- So u₁ = g·h₁ and u₂ = g·h₂ as units
  have hu₁_eq : u₁ = g * h₁ := Units.ext heq₁
  have hu₂_eq : u₂ = g * h₂ := Units.ext heq₂
  -- Therefore u₁·u₂⁻¹ = (g·h₁)·(g·h₂)⁻¹ = h₁·h₂⁻¹ ∈ H
  -- (using commutativity of (ZMod q)ˣ)
  have : u₁ * u₂⁻¹ = h₁ * h₂⁻¹ := by
    rw [hu₁_eq, hu₂_eq, mul_inv_rev,
        ← mul_assoc (g * h₁) h₂⁻¹ g⁻¹, mul_assoc g h₁ h₂⁻¹,
        mul_assoc g (h₁ * h₂⁻¹) g⁻¹, mul_comm (h₁ * h₂⁻¹) g⁻¹,
        ← mul_assoc g g⁻¹, mul_inv_cancel, one_mul]
  exact hratio (this ▸ H.mul_mem hh₁ (H.inv_mem hh₂))

/-- **Coset impossibility landscape**: summary of the reachable set coset
    impossibility results.

    1. mixedWalkProd_two_minFac_eq_prod — bridge to standard EM product
    2. reachableEver_ratios_escape_subgroup — ratio of two R_∞ elements ∉ H
    3. reachableEver_not_in_coset — R_∞ not contained in any proper coset -/
theorem coset_impossibility_landscape
    (q : ℕ) [hfact : Fact (Nat.Prime q)] (hq5 : 5 ≤ q)
    (hmc : MCBelow q) (hne : ∀ k, seq k ≠ q) :
    -- 1. Bridge: mixed walk from 2 = EM product
    (∀ n, mixedWalkProd 2 minFacMixed n = prod n)
    ∧
    -- 2. Ratio escape: R_∞ ratios escape every proper subgroup
    (∀ (H : Subgroup (ZMod q)ˣ), H ≠ ⊤ →
      ∃ (u₁ u₂ : (ZMod q)ˣ),
        (↑u₁ : ZMod q) ∈ reachableEver q 2 ∧
        (↑u₂ : ZMod q) ∈ reachableEver q 2 ∧
        u₁ * u₂⁻¹ ∉ H)
    ∧
    -- 3. Coset impossibility: R_∞ not in any proper coset
    (∀ (H : Subgroup (ZMod q)ˣ), H ≠ ⊤ → ∀ (g : (ZMod q)ˣ),
      ¬ (∀ x ∈ reachableEver q 2, ∃ h ∈ H, (x : ZMod q) = ↑(g * h))) :=
  ⟨mixedWalkProd_two_minFac_eq_prod,
   fun H hH => reachableEver_ratios_escape_subgroup q hq5 hmc hne H hH,
   fun H hH g => reachableEver_not_in_coset q hq5 hmc hne H hH g⟩

end CosetImpossibility

/-! ## Part 26: Factor Confinement and Sieve Obstruction

This section formalizes the **factor confinement** principle: if the reachable set
R_∞(q, acc) is proper (i.e., not all of ZMod q), then the prime factors of every
reachable Euclid number are constrained to lie in a specific "allowed" subset of
residues mod q.

### Key results

* `allowedFactors` — the set of residues m such that c * m ∈ R for a given position c
* `AllFactorsInSet` — predicate: every prime factor of N has its residue in a set F
* `factor_confinement` — every prime factor of a reachable Euclid number is in the
  allowed set (immediate from `reachableEver_from_factor`)
* `all_factors_confined` — all prime factors of P+1 are confined when P is reachable
* `standard_euclid_factors_confined` — specialization to the standard EM walk
* `forbidden_nonempty_of_unit` — if c is a unit and R ≠ univ, the forbidden set
  is nonempty (since multiplication by a unit is bijective)
* `FactorEscapeHypothesis` — open hypothesis: EM Euclid numbers escape any proper
  factor confinement
* `factor_escape_implies_mixed_hitting` — FactorEscapeHypothesis + MC(< q) ⇒
  MixedHitting at q (the chain: confinement + escape = contradiction)

### Connection to sieve theory

Factor confinement is the formal obstruction that a sieve-theoretic approach must
overcome: if the walk's reachable set were to stabilize at a proper subset, every
Euclid number's factors would be sieved out of the forbidden residues — a constraint
that becomes increasingly difficult to satisfy as the numbers grow.
-/

section FactorConfinement

/-- The set of "allowed" factor residues at walk position c in ZMod q,
    given a target set R. A residue m is allowed if c * m ∈ R. -/
def allowedFactors (q : ℕ) (c : ZMod q) (R : Set (ZMod q)) : Set (ZMod q) :=
  {m : ZMod q | c * m ∈ R}

/-- The complement: residues m such that c * m ∉ R. -/
def forbiddenFactors (q : ℕ) (c : ZMod q) (R : Set (ZMod q)) : Set (ZMod q) :=
  {m : ZMod q | c * m ∉ R}

/-- An integer N is factor-confined to a set F ⊆ ZMod q if every prime factor
    of N has its residue mod q in F. -/
def AllFactorsInSet (q : ℕ) (N : ℕ) (F : Set (ZMod q)) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ N → (p : ZMod q) ∈ F

/-- Allowed and forbidden partition ZMod q. -/
theorem allowed_union_forbidden (q : ℕ) (c : ZMod q) (R : Set (ZMod q)) :
    allowedFactors q c R ∪ forbiddenFactors q c R = Set.univ := by
  ext m; simp only [allowedFactors, forbiddenFactors, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_univ, iff_true]; tauto

/-- Allowed and forbidden are disjoint. -/
theorem allowed_inter_forbidden (q : ℕ) (c : ZMod q) (R : Set (ZMod q)) :
    allowedFactors q c R ∩ forbiddenFactors q c R = ∅ := by
  ext m; simp [allowedFactors, forbiddenFactors]

/-- **Factor confinement**: every prime factor of a reachable Euclid number
    P + 1 has its residue in the allowed factor set at position P mod q.

    Proof: `reachableEver_from_factor` shows P * p mod q ∈ R_∞ whenever
    p is prime and p ∣ P + 1. The definition of `allowedFactors` is exactly
    {m | c * m ∈ R}, so (p : ZMod q) ∈ allowedFactors. -/
theorem factor_confinement {q acc : ℕ} {n : ℕ}
    {σ : MixedSelection} (hv : ValidMixedSelection acc σ)
    {p : ℕ} (hp : p.Prime) (hdvd : p ∣ mixedWalkProd acc σ n + 1) :
    (p : ZMod q) ∈ allowedFactors q (mixedWalkProd acc σ n : ZMod q)
      (reachableEver q acc) := by
  exact @reachableEver_from_factor q acc n σ hv p hp hdvd

/-- All prime factors of a reachable Euclid number are confined to the
    allowed set at the walk position. -/
theorem all_factors_confined {q acc : ℕ} {n : ℕ}
    {σ : MixedSelection} (hv : ValidMixedSelection acc σ) :
    AllFactorsInSet q (mixedWalkProd acc σ n + 1)
      (allowedFactors q (mixedWalkProd acc σ n : ZMod q) (reachableEver q acc)) :=
  fun _ hp hdvd => factor_confinement hv hp hdvd

/-- Standard walk specialization: all prime factors of every standard Euclid
    number prod(n) + 1 are confined to the allowed set at the walk position. -/
theorem standard_euclid_factors_confined (q : ℕ) (n : ℕ) :
    AllFactorsInSet q (mixedWalkProd 2 minFacMixed n + 1)
      (allowedFactors q (mixedWalkProd 2 minFacMixed n : ZMod q)
        (reachableEver q 2)) :=
  all_factors_confined (minFacMixed_valid 2)

/-- Via the bridge `mixedWalkProd_two_minFac_eq_prod`: all prime factors of
    prod(n) + 1 are confined to the allowed set at the walk position. -/
theorem standard_euclid_factors_confined' (q : ℕ) (n : ℕ) :
    AllFactorsInSet q (prod n + 1)
      (allowedFactors q ((prod n : ℕ) : ZMod q) (reachableEver q 2)) := by
  have h := standard_euclid_factors_confined q n
  rw [mixedWalkProd_two_minFac_eq_prod] at h
  exact h

/-- If c is a unit and R ⊊ Set.univ, the forbidden factor set is nonempty.

    Proof: since c is a unit, left multiplication by c is a bijection on ZMod q.
    If R ≠ univ, there exists x ∉ R. Setting m = c⁻¹ * x gives c * m = x ∉ R,
    so m ∈ forbiddenFactors. -/
theorem forbidden_nonempty_of_unit {q : ℕ} [NeZero q]
    {c : ZMod q} (hc : IsUnit c)
    {R : Set (ZMod q)} (hR : R ≠ Set.univ) :
    (forbiddenFactors q c R).Nonempty := by
  rw [Set.ne_univ_iff_exists_notMem] at hR
  obtain ⟨x, hx⟩ := hR
  obtain ⟨u, rfl⟩ := hc
  refine ⟨↑u⁻¹ * x, ?_⟩
  show ↑u * (↑u⁻¹ * x) ∉ R
  rw [Units.mul_inv_cancel_left]
  exact hx

/-- If c is a unit and R ⊊ Set.univ, the allowed factor set is proper.
    Contrapositive of `forbidden_nonempty_of_unit`. -/
theorem allowed_ne_univ_of_unit {q : ℕ} [NeZero q]
    {c : ZMod q} (hc : IsUnit c)
    {R : Set (ZMod q)} (hR : R ≠ Set.univ) :
    allowedFactors q c R ≠ Set.univ := by
  intro hall
  have ⟨m, hm⟩ := forbidden_nonempty_of_unit hc hR
  have := Set.mem_univ m
  rw [← hall] at this
  exact hm this

/-- `AllFactorsInSet` is monotone in the target set: if F ⊆ G and all factors
    of N are in F, then all factors of N are in G. -/
theorem allFactorsInSet_mono {q N : ℕ} {F G : Set (ZMod q)} (h : F ⊆ G) :
    AllFactorsInSet q N F → AllFactorsInSet q N G :=
  fun hF p hp hdvd => h (hF p hp hdvd)

/-- `AllFactorsInSet` for 1 is vacuously true (1 has no prime factors). -/
theorem allFactorsInSet_one {q : ℕ} {F : Set (ZMod q)} :
    AllFactorsInSet q 1 F :=
  fun p hp hdvd => absurd (Nat.le_of_dvd Nat.one_pos hdvd) (by have := hp.two_le; omega)

/-! ### Factor Escape Hypothesis -/

/-- **Factor Escape Hypothesis**: The standard EM walk's Euclid numbers do not
    eventually have ALL prime factors confined to any proper subset of residues.

    Formally: for any step-dependent family of proper sets F(n) ⊊ ZMod q,
    the Euclid numbers prod(n) + 1 are not eventually all-factors-confined to F(n).

    This captures the sieve-theoretic content: the EM sequence's Euclid numbers
    produce prime factors in every residue class, not just a proper subset. -/
def FactorEscapeHypothesis (q : ℕ) : Prop :=
  ∀ (F : ℕ → Set (ZMod q)),
    (∀ n, F n ≠ Set.univ) →
    ¬(∃ N₀, ∀ n ≥ N₀, AllFactorsInSet q (prod n + 1) (F n))

/-- Under MC(< q) and q never in seq, the walk position prod(n) mod q is
    nonzero in ZMod q. (Restated from CosetImpossibility section.) -/
private theorem walk_pos_ne_zero' {q : ℕ} [hfact : Fact (Nat.Prime q)]
    (hne : ∀ k, seq k ≠ q) (n : ℕ) :
    ((prod n : ℕ) : ZMod q) ≠ 0 := by
  intro h
  have hdvd : q ∣ prod n := (ZMod.natCast_eq_zero_iff (prod n) q).mp h
  exact prime_not_in_seq_not_dvd_prod (Fact.out : Nat.Prime q).toIsPrime hne n hdvd

/-- Under MC(< q) and q never in seq, the walk position is a unit in ZMod q.
    Uses the fact that ZMod p is a field for prime p, so nonzero implies unit. -/
private theorem walk_pos_isUnit {q : ℕ} [hfact : Fact (Nat.Prime q)]
    (hne : ∀ k, seq k ≠ q) (n : ℕ) :
    IsUnit ((prod n : ℕ) : ZMod q) :=
  IsUnit.mk0 _ (walk_pos_ne_zero' hne n)

/-- **Factor escape implies mixed hitting**: If the FactorEscapeHypothesis holds
    at q, and MC(< q) and q never appears in seq, then -1 ∈ R_∞(q, 2),
    which means there exists a valid mixed walk capturing q.

    Proof by contradiction: Suppose -1 ∉ R_∞. Then R_∞ ≠ Set.univ.
    Factor confinement gives: for all n, every prime factor of prod(n) + 1
    is in allowedFactors(prod(n) mod q, R_∞). Since prod(n) mod q is a unit
    (from hne) and R_∞ ≠ univ, each allowedFactors set is proper (by
    `allowed_ne_univ_of_unit`). This contradicts FactorEscapeHypothesis. -/
theorem factor_escape_implies_mixed_hitting
    (q : ℕ) [hfact : Fact (Nat.Prime q)]
    (hne : ∀ k, seq k ≠ q)
    (hFE : FactorEscapeHypothesis q) :
    (-1 : ZMod q) ∈ reachableEver q 2 := by
  by_contra h_not_neg_one
  -- R_∞ ≠ Set.univ since -1 ∉ R_∞
  have hR_ne : reachableEver q 2 ≠ Set.univ := by
    intro heq
    exact h_not_neg_one (heq ▸ Set.mem_univ _)
  -- Define F(n) = allowedFactors at walk position prod(n)
  let F : ℕ → Set (ZMod q) := fun n =>
    allowedFactors q ((prod n : ℕ) : ZMod q) (reachableEver q 2)
  -- Each F(n) is proper: prod(n) is a unit and R_∞ ≠ univ
  have hF_proper : ∀ n, F n ≠ Set.univ := by
    intro n
    exact allowed_ne_univ_of_unit (walk_pos_isUnit hne n) hR_ne
  -- Factor confinement gives AllFactorsInSet for all n (with N₀ = 0)
  have hconf : ∃ N₀, ∀ n ≥ N₀, AllFactorsInSet q (prod n + 1) (F n) :=
    ⟨0, fun n _ => standard_euclid_factors_confined' q n⟩
  -- Contradiction with FactorEscapeHypothesis
  exact hFE F hF_proper hconf

/-- **Factor escape implies reachable set is full**: Under q never in seq,
    FactorEscapeHypothesis forces R_∞(q, 2) = Set.univ.

    Proof: if R_∞ ≠ univ, factor confinement + walk_pos_isUnit give each
    allowedFactors set proper, contradicting FactorEscapeHypothesis. -/
theorem factor_escape_implies_reachable_full
    (q : ℕ) [hfact : Fact (Nat.Prime q)]
    (hne : ∀ k, seq k ≠ q)
    (hFE : FactorEscapeHypothesis q) :
    reachableEver q 2 = Set.univ := by
  by_contra hR_ne
  let F : ℕ → Set (ZMod q) := fun n =>
    allowedFactors q ((prod n : ℕ) : ZMod q) (reachableEver q 2)
  have hF_proper : ∀ n, F n ≠ Set.univ :=
    fun n => allowed_ne_univ_of_unit (walk_pos_isUnit hne n) hR_ne
  have hconf : ∃ N₀, ∀ n ≥ N₀, AllFactorsInSet q (prod n + 1) (F n) :=
    ⟨0, fun n _ => standard_euclid_factors_confined' q n⟩
  exact hFE F hF_proper hconf

/-- **Factor escape implies mixed MC at q**: combining with the hitting ↔ reachable
    bridge, FactorEscapeHypothesis gives a valid mixed walk capturing q. -/
theorem factor_escape_implies_mixed_mc_at
    (q : ℕ) [hfact : Fact (Nat.Prime q)]
    (hne : ∀ k, seq k ≠ q)
    (hFE : FactorEscapeHypothesis q) :
    ∃ (σ : MixedSelection) (n : ℕ),
      ValidMixedSelection 2 σ ∧ q ∣ (mixedWalkProd 2 σ n + 1) := by
  rw [mixed_hitting_iff_neg_one_reachable]
  have hmem := factor_escape_implies_mixed_hitting q hne hFE
  rw [reachableEver, Set.mem_iUnion] at hmem
  exact hmem

/-! ### Confinement strength: factor confinement constrains ALL walks -/

/-- Factor confinement for arbitrary valid walks (not just minFac): if σ is any
    valid walk from acc, every prime factor of the Euclid number at step n is
    in the allowed set at the walk position. -/
theorem factor_confinement_arbitrary {q acc : ℕ} {n : ℕ}
    (σ : MixedSelection) (hv : ValidMixedSelection acc σ)
    (p : ℕ) (hp : p.Prime) (hdvd : p ∣ mixedWalkProd acc σ n + 1) :
    (p : ZMod q) ∈ allowedFactors q (mixedWalkProd acc σ n : ZMod q)
      (reachableEver q acc) :=
  factor_confinement hv hp hdvd

/-- The reachable set is closed under allowed factor multiplication: if c ∈ R_∞
    and m ∈ allowedFactors(c, R_∞), then c * m ∈ R_∞ (tautological from the
    definition, but worth stating). -/
theorem reachable_closed_under_allowed {q acc : ℕ}
    {c : ZMod q} (_ : c ∈ reachableEver q acc)
    {m : ZMod q} (hm : m ∈ allowedFactors q c (reachableEver q acc)) :
    c * m ∈ reachableEver q acc :=
  hm

/-- **Factor confinement landscape**: summary of the factor confinement results.

    1. factor_confinement — prime factors of reachable Euclid numbers are confined
    2. standard_euclid_factors_confined' — specialization to standard EM walk
    3. forbidden_nonempty_of_unit — forbidden set nonempty when R ⊊ univ and c is unit
    4. allowed_ne_univ_of_unit — allowed set proper when R ⊊ univ and c is unit
    5. factor_escape_implies_mixed_hitting — FEH ⇒ -1 ∈ R_∞
    6. factor_escape_implies_reachable_full — FEH ⇒ R_∞ = univ -/
theorem factor_confinement_landscape
    (q : ℕ) [hfact : Fact (Nat.Prime q)]
    (hne : ∀ k, seq k ≠ q)
    (hFE : FactorEscapeHypothesis q) :
    -- 1. Factor confinement: all factors of prod(n)+1 are confined
    (∀ n, AllFactorsInSet q (prod n + 1)
      (allowedFactors q ((prod n : ℕ) : ZMod q) (reachableEver q 2)))
    ∧
    -- 2. Walk positions are units
    (∀ n, IsUnit ((prod n : ℕ) : ZMod q))
    ∧
    -- 3. Factor escape gives -1 ∈ R_∞
    ((-1 : ZMod q) ∈ reachableEver q 2)
    ∧
    -- 4. Factor escape gives R_∞ = univ
    (reachableEver q 2 = Set.univ)
    ∧
    -- 5. Factor escape gives mixed MC at q
    (∃ (σ : MixedSelection) (n : ℕ),
      ValidMixedSelection 2 σ ∧ q ∣ (mixedWalkProd 2 σ n + 1)) :=
  ⟨standard_euclid_factors_confined' q,
   walk_pos_isUnit hne,
   factor_escape_implies_mixed_hitting q hne hFE,
   factor_escape_implies_reachable_full q hne hFE,
   factor_escape_implies_mixed_mc_at q hne hFE⟩

end FactorConfinement
