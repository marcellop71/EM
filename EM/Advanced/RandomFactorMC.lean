import EM.Advanced.EpsilonRandomMC
import EM.SDDS.Bridge

/-!
# Random Factor Variant of Mullin's Conjecture

## Overview

This file formalizes the **pure random-factor variant** of the Euclid-Mullin sequence:
at each step, instead of choosing minFac(P(n)+1), choose a uniformly random prime
factor of P(n)+1. The main result is that the pure random-factor variant is
**equivalent** to the mixed variant (MixedMC) via a purification lemma.

The key insight: any valid mixed walk (which may use minFac at some steps) can be
converted to a **pure random walk** (which always specifies an explicit prime factor)
that follows the exact same trajectory. This is because minFac(P+1) is itself a prime
factor of P+1, so choosing `some (minFac(P+1))` is a valid "random" choice that
reproduces the minFac behavior.

## Main Results

### Proved Theorems
* `purify_walk_eq` — purified walk has same accumulator at every step
* `purify_valid` — purified selection is valid when original is valid
* `purify_is_pure_random` — purified selection is pure random (σ(k) ≠ none ∀k)
* `purify_captures` — purified walk captures q whenever original does
* `pure_random_mc_iff_mixed_mc` — PureRandomMC q ↔ MixedMC q
* `pure_random_mc_two` — PureRandomMC 2 (trivial)
* `pure_random_mc_three` — PureRandomMC 3 (unconditional)
* `pure_random_mc_iff_reachable` — PureRandomMC q ↔ -1 ∈ reachableEver (for prime q)
* `standard_mc_implies_pure_random` — MC ⇒ PureRandomMC
* `random_factor_mc_landscape` — summary conjunction

## Motivation

Random MC is provable: independence of multiplier from walk position (by
construction) gives Diaconis-Shahshahani mixing. The sole obstruction to
standard MC is the deterministic nature of minFac.

The factor tree T(m) encodes all possible factor choices. GenMixedMC asks
whether T(m) reaches every prime -- the mathematical distillation of what
randomness achieves (every element reachable) without the probabilistic
machinery.

PureRandomMC <-> MixedMC (purification lemma): the distinction between
"minFac-first" and "all-random" is illusory at the nondeterministic level,
since minFac(P+1) is itself a valid explicit choice.

## Probabilistic Interpretation

`PureRandomMC q` states: there EXISTS a pure-random valid selection capturing q.
The probabilistic version says: a uniformly random selection captures q with
probability 1. The implication (existential → probabilistic) follows from:

1. If -1 ∈ reachableEver q 2, there exists a finite path σ₀,...,σ_{N-1} reaching -1
2. Each σ_k is a prime factor of P_k+1, chosen with probability ≥ 1/ω(P_k+1) > 0
3. The probability of following this exact path is ∏ 1/ω(P_k+1) > 0
4. By the Markov property, the random walk hits -1 mod q infinitely often
5. Each hit gives probability ≥ 1/ω(P_k+1) of selecting q
6. Borel-Cantelli: infinitely many chances with positive probability → q captured a.s.

This probabilistic argument is NOT formalized (requires measure theory infrastructure
absent from the project). The nondeterministic formulation suffices for the reduction
landscape.
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Part 1: Pure Random Selection -/

section PureRandom

/-- A MixedSelection is **pure random** if it never uses the default minFac rule:
    σ(k) = some p for all k. This models a walk where every factor is explicitly
    chosen from the factor bag, with no deterministic fallback. -/
def IsPureRandom (σ : MixedSelection) : Prop := ∀ k, σ k ≠ none

/-- Construct a pure random selection from any mixed selection: replace every `none`
    (minFac default) with `some (mixedWalkFactor acc σ k)`. Since minFac(P+1) is
    always a prime dividing P+1, this is a valid explicit choice that reproduces
    the same walk trajectory. -/
def purify (acc : ℕ) (σ : MixedSelection) : MixedSelection := fun k =>
  some (mixedWalkFactor acc σ k)

end PureRandom

/-! ## Part 2: Purification Preserves Walk -/

section PurifyWalk

/-- The purified walk produces the same accumulator at every step.
    Proof by induction: at each step, the purified selection chooses the same
    factor as the original (either minFac or the explicit choice), so the
    accumulators stay synchronized. -/
theorem purify_walk_eq (acc : ℕ) (σ : MixedSelection) (n : ℕ) :
    mixedWalkProd acc (purify acc σ) n = mixedWalkProd acc σ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [mixedWalkProd]
    show (let P := mixedWalkProd acc (purify acc σ) n
          let factor := match (purify acc σ) n with
            | none => (P + 1).minFac
            | some p => p
          P * factor) =
         (let P := mixedWalkProd acc σ n
          let factor := match σ n with
            | none => (P + 1).minFac
            | some p => p
          P * factor)
    have h1 : purify acc σ n = some (mixedWalkFactor acc σ n) := rfl
    simp only [h1, ih, mixedWalkFactor]
    rfl

/-- The purified walk produces the same factor at every step. -/
theorem purify_factor_eq (acc : ℕ) (σ : MixedSelection) (n : ℕ) :
    mixedWalkFactor acc (purify acc σ) n = mixedWalkFactor acc σ n := by
  simp only [mixedWalkFactor, purify]

end PurifyWalk

/-! ## Part 3: Purification Preserves Validity -/

section PurifyValid

/-- The purified selection is valid whenever the original is valid and acc ≥ 2. -/
theorem purify_valid (acc : ℕ) (hacc : 2 ≤ acc) (σ : MixedSelection)
    (hv : ValidMixedSelection acc σ) :
    ValidMixedSelection acc (purify acc σ) := by
  intro k
  simp only [purify]
  constructor
  · exact mixedWalkFactor_prime acc σ hv k (mixedWalkProd_ge_two acc hacc σ hv k)
  · rw [purify_walk_eq]
    exact mixedWalkFactor_dvd acc σ hv k

/-- The purified selection is pure random: every step is an explicit choice. -/
theorem purify_is_pure_random (acc : ℕ) (σ : MixedSelection) :
    IsPureRandom (purify acc σ) := by
  intro k
  simp [purify]

end PurifyValid

/-! ## Part 4: Purification Preserves Captures -/

section PurifyCaptures

/-- If the original walk captures q, so does the purified walk. -/
theorem purify_captures (acc : ℕ) (σ : MixedSelection) (q : ℕ)
    (hcap : mixedCaptures q acc σ) :
    mixedCaptures q acc (purify acc σ) := by
  obtain ⟨k, hk⟩ := hcap
  exact ⟨k, by rw [purify_factor_eq]; exact hk⟩

end PurifyCaptures

/-! ## Part 5: Pure Random MC Definition -/

section PureRandomMC

/-- Pure Random MC for a single prime: either q=2 (in the initial accumulator)
    or there exists a **pure random** valid selection capturing q from acc=2. -/
def PureRandomMC (q : ℕ) : Prop :=
  q.Prime → q = 2 ∨
    ∃ σ : MixedSelection, IsPureRandom σ ∧ ValidMixedSelection 2 σ ∧ mixedCaptures q 2 σ

/-- Full Pure Random Mullin Conjecture. -/
def PureRandomMullinConjecture : Prop :=
  ∀ q, q.Prime → PureRandomMC q

end PureRandomMC

/-! ## Part 6: Equivalence with MixedMC -/

section Equivalence

/-- PureRandomMC q ↔ MixedMC q: the pure random and mixed formulations are equivalent.

    Forward: a pure random selection is in particular a mixed selection.
    Backward: any mixed selection can be purified to a pure random one with the
    same trajectory (and hence the same captures). -/
theorem pure_random_mc_iff_mixed_mc (q : ℕ) : PureRandomMC q ↔ MixedMC q := by
  constructor
  · -- PureRandomMC → MixedMC: forget the IsPureRandom constraint
    intro hpr hprime
    rcases hpr hprime with h2 | ⟨σ, _, hv, hcap⟩
    · left; exact h2
    · right; exact ⟨σ, hv, hcap⟩
  · -- MixedMC → PureRandomMC: purify the witness
    intro hmixed hprime
    rcases hmixed hprime with h2 | ⟨σ, hv, hcap⟩
    · left; exact h2
    · right
      exact ⟨purify 2 σ,
             purify_is_pure_random 2 σ,
             purify_valid 2 le_rfl σ hv,
             purify_captures 2 σ q hcap⟩

/-- Full conjecture equivalence: PureRandomMullinConjecture ↔ MixedMullinConjecture. -/
theorem pure_random_mc_iff_mixed :
    PureRandomMullinConjecture ↔ MixedMullinConjecture := by
  constructor
  · intro h q hq; exact (pure_random_mc_iff_mixed_mc q).mp (h q hq)
  · intro h q hq; exact (pure_random_mc_iff_mixed_mc q).mpr (h q hq)

end Equivalence

/-! ## Part 7: Base Cases -/

section BaseCases

/-- q=2 is trivially in PureRandomMC. -/
theorem pure_random_mc_two : PureRandomMC 2 := by
  intro _; left; rfl

/-- q=3 is unconditionally in PureRandomMC: purify the minFac witness. -/
theorem pure_random_mc_three : PureRandomMC 3 := by
  rw [pure_random_mc_iff_mixed_mc]
  exact mixed_mc_three

end BaseCases

/-! ## Part 8: Reachable Set Connection -/

section ReachableConnection

/-- Helper: walks that agree on [0, n) have the same accumulator at step n. -/
private theorem mixedWalkProd_agree_prefix (acc : ℕ) (σ₁ σ₂ : MixedSelection) (n : ℕ)
    (hagree : ∀ k, k < n → σ₁ k = σ₂ k) :
    mixedWalkProd acc σ₁ n = mixedWalkProd acc σ₂ n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [mixedWalkProd]
    have him := ih (fun k hk => hagree k (Nat.lt_succ_of_lt hk))
    rw [him, hagree m (Nat.lt_succ_iff.mpr le_rfl)]

/-- For prime q ≥ 3: PureRandomMC q ↔ -1 ∈ reachableEver q 2.

    Both reduce to the existence of a valid walk hitting -1 mod q.
    The purification lemma makes the IsPureRandom constraint free. -/
theorem pure_random_mc_iff_reachable {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    PureRandomMC q ↔ (-1 : ZMod q) ∈ reachableEver q 2 := by
  rw [pure_random_mc_iff_mixed_mc]
  constructor
  · intro hmixed
    rcases hmixed hq with h2 | ⟨σ, hv, k, hk⟩
    · omega
    · -- Walk captures q at step k: mixedWalkFactor 2 σ k = q
      -- This means q | P_k + 1, so walkProd ≡ -1 mod q
      have hdvd := mixedWalkFactor_dvd 2 σ hv k
      rw [hk] at hdvd
      rw [reachableEver, Set.mem_iUnion]
      refine ⟨k, σ, hv, ?_⟩
      have h0 : ((mixedWalkProd 2 σ k + 1 : ℕ) : ZMod q) = 0 := by
        rwa [ZMod.natCast_eq_zero_iff]
      calc (mixedWalkProd 2 σ k : ZMod q)
          = (mixedWalkProd 2 σ k : ZMod q) + 1 - 1 := by ring
        _ = 0 - 1 := by push_cast at h0; rw [h0]
        _ = -1 := by ring
  · intro hmem _
    right
    rw [reachableEver, Set.mem_iUnion] at hmem
    obtain ⟨n, σ, hv, hmod⟩ := hmem
    -- -1 ∈ reachableAt means some walk has P_n ≡ -1 mod q, i.e., q | P_n + 1
    have hq_dvd : q ∣ (mixedWalkProd 2 σ n + 1) := by
      have h1 : (mixedWalkProd 2 σ n : ZMod q) + 1 = 0 := by rw [hmod]; ring
      have h2 : ((mixedWalkProd 2 σ n + 1 : ℕ) : ZMod q) = 0 := by push_cast; exact h1
      rwa [ZMod.natCast_eq_zero_iff] at h2
    -- Build a selection: σ for steps < n, `some q` at step n, minFac after
    let σ' : MixedSelection := fun k =>
      if k < n then σ k else if k = n then some q else none
    have hσ'_agree : ∀ k, k < n → σ' k = σ k := by
      intro k hk; simp [σ', hk]
    have hσ'_prod_eq : mixedWalkProd 2 σ' n = mixedWalkProd 2 σ n :=
      mixedWalkProd_agree_prefix 2 σ' σ n hσ'_agree
    refine ⟨σ', ?_, n, ?_⟩
    · -- Validity of σ'
      intro k
      simp only [σ']
      by_cases hkn : k < n
      · -- k < n: σ'(k) = σ(k), walks agree, use hv
        simp only [hkn, ite_true]
        have hwalk_eq : mixedWalkProd 2 σ' k = mixedWalkProd 2 σ k :=
          mixedWalkProd_agree_prefix 2 σ' σ k (fun j hj => hσ'_agree j (lt_trans hj hkn))
        have hvk := hv k
        match hσk : σ k with
        | none => simp [hσk] at hvk ⊢
        | some p =>
          simp [hσk] at hvk ⊢
          exact ⟨hvk.1, by rw [hwalk_eq]; exact hvk.2⟩
      · push Not at hkn
        by_cases hkeq : k = n
        · -- k = n: choosing q
          subst hkeq
          simp only [lt_irrefl, ite_false, ite_true]
          exact ⟨hq, by rw [hσ'_prod_eq]; exact hq_dvd⟩
        · -- k > n: σ'(k) = none, always valid
          have hkgt : ¬ (k < n) := not_lt.mpr hkn
          simp only [hkgt, ite_false, hkeq, ite_false]
    · -- Captures q at step n
      simp only [mixedWalkFactor, σ']
      simp only [lt_irrefl, ite_false, ite_true]

end ReachableConnection

/-! ## Part 9: Standard MC Bridge -/

section StandardMCBridge

/-- The factor at step n of the all-minFac mixed walk from acc=2 equals seq(n+1).
    This connects the mixed walk framework to the standard EM sequence.
    Uses `euclid_minFac_eq_nat_minFac` to bridge the two minFac implementations. -/
theorem mixedWalkFactor_two_minFac_eq_seq (n : ℕ) :
    mixedWalkFactor 2 minFacMixed n = seq (n + 1) := by
  simp only [mixedWalkFactor, minFacMixed]
  rw [mixedWalkProd_two_minFac_eq_prod, seq_succ]
  exact (euclid_minFac_eq_nat_minFac (prod n + 1) (by have := prod_ge_two n; omega)).symm

/-- Standard MC implies PureRandomMC: if minFac captures q, any variant does too.

    MullinConjecture says ∃ n, seq n = q. If n = 0, q = 2 (trivial).
    If n = k+1, then seq(k+1) = q, so the minFac walk captures q at step k. -/
theorem standard_mc_implies_pure_random (hmc : MullinConjecture) :
    PureRandomMullinConjecture := by
  intro q hq
  rw [pure_random_mc_iff_mixed_mc]
  intro _
  obtain ⟨n, hn⟩ := hmc q ((isPrime_iff_natPrime q).mpr hq)
  cases n with
  | zero => left; rw [seq_zero] at hn; exact hn.symm
  | succ k =>
    right
    exact ⟨minFacMixed, minFacMixed_valid 2, k, by
      rw [mixedWalkFactor_two_minFac_eq_seq]; exact hn⟩

end StandardMCBridge

/-! ## Part 10: Characterization of the Gap

The gap between standard MC and PureRandomMC/MixedMC is precisely:

  **Standard MC** asks: does the ALL-MINFAC walk hit -1 mod q?
  **PureRandomMC** asks: does SOME valid walk hit -1 mod q?

Since the all-minFac walk is one particular valid walk, Standard MC ⇒ PureRandomMC.
The converse fails: there may exist a walk hitting -1 that the minFac walk doesn't follow.

DSL bridges this gap: it shows the minFac walk visits every position that
any valid walk can reach. Equivalently, DSL says the minFac walk's visit set
equals the full reachable set modulo q. -/

/-! ## Part 11: Landscape -/

section Landscape

/-- **Random factor MC landscape**: summary of the pure random variant analysis.

    1. pure_random_mc_iff_mixed_mc — PureRandomMC ↔ MixedMC (purification)
    2. pure_random_mc_two — PureRandomMC 2 (trivial)
    3. pure_random_mc_three — PureRandomMC 3 (unconditional)
    4. purify_walk_eq — purified walk = original walk
    5. purify_is_pure_random — purified selection is pure random
    6. standard_mc_implies_pure_random — MC ⇒ PureRandomMC -/
theorem random_factor_mc_landscape :
    -- (1) PureRandomMC ↔ MixedMC for all q
    (∀ q, PureRandomMC q ↔ MixedMC q) ∧
    -- (2) q=2 base case
    PureRandomMC 2 ∧
    -- (3) q=3 base case
    PureRandomMC 3 ∧
    -- (4) Purification preserves walk
    (∀ (acc : ℕ) (σ : MixedSelection) (n : ℕ),
      mixedWalkProd acc (purify acc σ) n = mixedWalkProd acc σ n) ∧
    -- (5) Purification is pure random
    (∀ (acc : ℕ) (σ : MixedSelection), IsPureRandom (purify acc σ)) ∧
    -- (6) MC ⇒ PureRandomMC
    (MullinConjecture → PureRandomMullinConjecture) :=
  ⟨pure_random_mc_iff_mixed_mc,
   pure_random_mc_two,
   pure_random_mc_three,
   purify_walk_eq,
   purify_is_pure_random,
   standard_mc_implies_pure_random⟩

end Landscape
