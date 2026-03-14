import EM.Advanced.VanishingNoiseVariant
import EM.Ensemble.TwoPointEnsemble

/-!
# Random Two-Point MC: Self-Consistent Path Counting

## Overview

This file builds the **self-consistent random two-point MC** framework.
At each step of the generalized walk, we flip a fair coin to choose either
`minFac` or `secondMinFac` of (accumulator + 1). The goal is to connect the
existing `treeCharSum` (branching tree character sum from `VanishingNoiseVariant.lean`)
to path-counting for this random walk.

## Main Definitions

* `epsWalkProdFrom acc sigma` -- generalized accumulator starting from `acc`
* `epsWalkFactorFrom acc sigma n` -- factor chosen at step n from accumulator `acc`
* `finDecisionExtend sigma` -- extends `Fin N -> Bool` to `Nat -> Bool` (padding with true)
* `pathCount q N a` -- count of length-N decision sequences landing in unit class a mod q
* `pathCharSum q chi N acc` -- averaged character product over all 2^N paths from acc
* `RandomTwoPointMC q` -- every unit mod q is reachable by some binary decision path
* `FourierBridgeIdentity q` -- tree char sum = averaged character product over paths

## Main Results

### Proved Theorems
* `epsWalkProdFrom_zero` -- initial value
* `epsWalkProdFrom_succ` -- recurrence via epsWalkFactorFrom
* `epsWalkProdFrom_ge_two` -- accumulator >= 2 for acc >= 2
* `epsWalkFactorFrom_prime` -- chosen factor is prime for acc >= 2
* `epsWalkFactorFrom_dvd` -- chosen factor divides acc + 1
* `epsWalkProdFrom_two_eq` -- epsWalkProdFrom 2 = epsWalkProd
* `finDecisionExtend_lt` -- extension agrees with original in range
* `pathCount_sum_le` -- sum over units of pathCount <= 2^N
* `chiAt_mul_of_coprime` -- chiAt multiplicative for coprime-to-q naturals
* `chiAt_multiplicativity_proved` -- ChiAtMultiplicativity PROVED (induction + backward propagation)
* `not_dvd_epsWalkProdFrom_of_succ` -- backward non-divisibility for walk product
* `not_dvd_epsWalkFactorFrom_of_succ` -- backward non-divisibility for walk factor
* `not_dvd_epsWalkProdFrom_of_le` -- backward propagation to any earlier step
* `pathCharSum_trivial` -- trivial character pathCharSum = 1
* `fourier_bridge_identity_proved` -- KEY: treeCharSum = pathCharSum (proved by induction)
* `fairTreeCharSum_eq_pathCharSum` -- specialization to acc = 2 (unconditional)
* `pathCharSum_vanishing_of_tree_contraction` -- TCA => vanishing pathCharSum (unconditional)
* `mean_char_zero_at_diverse_step_three` -- q=3 zero-mean property
* `random_two_point_mc_landscape` -- 7-clause summary
* `tca_path_survival_implies_random_mc_proved` -- TCA + PathSurvival => RandomTwoPointMC (PROVED)

### Open Hypotheses
* `PathSurvival` -- survival/death ratio unbounded (structural)
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Part 1: Generalized Accumulator Starting from Arbitrary Point

We define `epsWalkProdFrom acc sigma` which generalizes `epsWalkProd sigma`
by starting from an arbitrary accumulator `acc` rather than the fixed value 2.
This is essential for the inductive proof of the Fourier bridge identity,
since the subtrees of the branching tree start from different accumulators. -/

section GeneralizedWalk

/-- Generalized epsilon-walk accumulator starting from `acc`.
    At each step, if sigma(k) = true, multiply by minFac(current + 1);
    if sigma(k) = false, multiply by secondMinFac(current + 1). -/
def epsWalkProdFrom (acc : ℕ) (σ : ℕ → Bool) : ℕ → ℕ
  | 0 => acc
  | n + 1 =>
    let P := epsWalkProdFrom acc σ n
    let factor := if σ n then (P + 1).minFac else secondMinFac (P + 1)
    P * factor

/-- The factor chosen at step n in the generalized epsilon-walk from `acc`. -/
def epsWalkFactorFrom (acc : ℕ) (σ : ℕ → Bool) (n : ℕ) : ℕ :=
  let P := epsWalkProdFrom acc σ n
  if σ n then (P + 1).minFac else secondMinFac (P + 1)

/-- The initial value of the generalized accumulator is `acc`. -/
theorem epsWalkProdFrom_zero (acc : ℕ) (σ : ℕ → Bool) :
    epsWalkProdFrom acc σ 0 = acc := rfl

/-- The recurrence: epsWalkProdFrom acc sigma (n+1) = (current) * (chosen factor). -/
theorem epsWalkProdFrom_succ (acc : ℕ) (σ : ℕ → Bool) (n : ℕ) :
    epsWalkProdFrom acc σ (n + 1) =
    epsWalkProdFrom acc σ n * epsWalkFactorFrom acc σ n := by
  simp [epsWalkProdFrom, epsWalkFactorFrom]

/-- For acc >= 2, the generalized accumulator stays >= 2 at all steps. -/
theorem epsWalkProdFrom_ge_two (acc : ℕ) (hacc : 2 ≤ acc) (σ : ℕ → Bool) (n : ℕ) :
    2 ≤ epsWalkProdFrom acc σ n := by
  induction n with
  | zero => simp [epsWalkProdFrom]; exact hacc
  | succ n ih =>
    simp only [epsWalkProdFrom]
    have hP_ge : 2 ≤ epsWalkProdFrom acc σ n := ih
    have hP1_ge : 2 ≤ epsWalkProdFrom acc σ n + 1 := by omega
    have hfac_ge : 1 ≤ (if σ n then (epsWalkProdFrom acc σ n + 1).minFac
        else secondMinFac (epsWalkProdFrom acc σ n + 1)) := by
      split
      · have := (Nat.minFac_prime (by omega : epsWalkProdFrom acc σ n + 1 ≠ 1)).two_le; omega
      · have := (secondMinFac_prime hP1_ge).two_le; omega
    calc 2 = 2 * 1 := by omega
      _ ≤ epsWalkProdFrom acc σ n * (if σ n then (epsWalkProdFrom acc σ n + 1).minFac
          else secondMinFac (epsWalkProdFrom acc σ n + 1)) :=
        Nat.mul_le_mul hP_ge hfac_ge

/-- The factor chosen at each step divides the accumulator + 1 (generalized, for acc >= 2). -/
theorem epsWalkFactorFrom_dvd (acc : ℕ) (hacc : 2 ≤ acc) (σ : ℕ → Bool) (n : ℕ) :
    epsWalkFactorFrom acc σ n ∣ epsWalkProdFrom acc σ n + 1 := by
  simp only [epsWalkFactorFrom]
  split
  · exact Nat.minFac_dvd (epsWalkProdFrom acc σ n + 1)
  · exact secondMinFac_dvd (by
      have := epsWalkProdFrom_ge_two acc hacc σ n
      omega)

/-- The factor chosen at each step is prime (generalized, for acc >= 2). -/
theorem epsWalkFactorFrom_prime (acc : ℕ) (hacc : 2 ≤ acc) (σ : ℕ → Bool) (n : ℕ) :
    (epsWalkFactorFrom acc σ n).Prime := by
  simp only [epsWalkFactorFrom]
  have hP := epsWalkProdFrom_ge_two acc hacc σ n
  split
  · exact Nat.minFac_prime (by omega)
  · exact secondMinFac_prime (by omega)

/-- epsWalkProdFrom 2 agrees with epsWalkProd for the same decision sequence. -/
theorem epsWalkProdFrom_two_eq (σ : ℕ → Bool) (n : ℕ) :
    epsWalkProdFrom 2 σ n = epsWalkProd σ n := by
  induction n with
  | zero => simp [epsWalkProdFrom, epsWalkProd]
  | succ n ih =>
    simp only [epsWalkProdFrom, epsWalkProd]
    rw [ih]

/-- epsWalkFactorFrom 2 agrees with epsWalkFactor. -/
theorem epsWalkFactorFrom_two_eq (σ : ℕ → Bool) (n : ℕ) :
    epsWalkFactorFrom 2 σ n = epsWalkFactor σ n := by
  simp only [epsWalkFactorFrom, epsWalkFactor]
  rw [epsWalkProdFrom_two_eq]

end GeneralizedWalk

/-! ## Part 2: Finite Decision Sequences and Path Counting

We extend finite decision sequences `Fin N -> Bool` to infinite ones
by padding with `true` (= always choose minFac after the finite prefix).
Then we define `pathCount q N a` as the count of length-N decision sequences
whose walk lands in residue class `a` mod q. -/

section PathCounting

/-- Extension of a finite decision sequence to an infinite one.
    Within range [0, N), use the finite sequence; beyond, pad with true. -/
def finDecisionExtend {N : ℕ} (σ : Fin N → Bool) : ℕ → Bool :=
  fun k => if h : k < N then σ ⟨k, h⟩ else true

/-- The extension agrees with the original for k < N. -/
theorem finDecisionExtend_lt {N : ℕ} (σ : Fin N → Bool) (k : ℕ) (hk : k < N) :
    finDecisionExtend σ k = σ ⟨k, hk⟩ := by
  simp [finDecisionExtend, hk]

/-- The extension returns true for k >= N. -/
theorem finDecisionExtend_ge {N : ℕ} (σ : Fin N → Bool) (k : ℕ) (hk : N ≤ k) :
    finDecisionExtend σ k = true := by
  simp [finDecisionExtend, not_lt.mpr hk]

variable {q : ℕ} [Fact (Nat.Prime q)]

/-- Count of length-N decision sequences that produce a walk (from acc = 2)
    ending in residue class `a` mod q. -/
def pathCount (q : ℕ) [Fact (Nat.Prime q)] (N : ℕ) (a : (ZMod q)ˣ) : ℕ :=
  (Finset.univ.filter (fun (σ : Fin N → Bool) =>
    (epsWalkProd (finDecisionExtend σ) N : ZMod q) = ↑a)).card

/-- The sum of pathCounts over all units is at most 2^N.
    This follows because the filter sets for different `a` are disjoint
    subsets of `Finset.univ : Finset (Fin N -> Bool)`. -/
theorem pathCount_sum_le (N : ℕ) :
    ∑ a : (ZMod q)ˣ, pathCount q N a ≤ 2 ^ N := by
  have hcard : Fintype.card (Fin N → Bool) = 2 ^ N := by
    simp
  rw [← hcard, ← Finset.card_univ (α := Fin N → Bool)]
  -- Each pathCount is a filter of Finset.univ; the filters for distinct a are disjoint
  -- The sum of cards of disjoint subsets ≤ card of the whole set
  -- Each σ contributes to at most one a.
  -- Approach: ∑ a, |filter(a)| ≤ |univ| because the filters are pairwise disjoint subsets of univ
  have hdisj : ∀ a : (ZMod q)ˣ, ∀ b : (ZMod q)ˣ, a ≠ b →
      Disjoint (Finset.univ.filter (fun σ : Fin N → Bool =>
        (epsWalkProd (finDecisionExtend σ) N : ZMod q) = ↑a))
      (Finset.univ.filter (fun σ : Fin N → Bool =>
        (epsWalkProd (finDecisionExtend σ) N : ZMod q) = ↑b)) := by
    intro a b hab
    rw [Finset.disjoint_filter]
    intro σ _ heqa heqb
    exact hab (Units.ext (by rw [← heqa, ← heqb]))
  calc ∑ a : (ZMod q)ˣ, pathCount q N a
      = ∑ a : (ZMod q)ˣ,
        (Finset.univ.filter (fun σ : Fin N → Bool =>
          (epsWalkProd (finDecisionExtend σ) N : ZMod q) = ↑a)).card := rfl
    _ = (Finset.univ.biUnion (fun a : (ZMod q)ˣ => Finset.univ.filter
        (fun σ : Fin N → Bool =>
          (epsWalkProd (finDecisionExtend σ) N : ZMod q) = ↑a))).card := by
        rw [Finset.card_biUnion (fun a _ b _ hab => hdisj a b hab)]
    _ ≤ (Finset.univ : Finset (Fin N → Bool)).card :=
        Finset.card_le_card (Finset.subset_univ _)

end PathCounting

/-! ## Part 3: Fourier Bridge Identity (Tree = Averaged Path Product)

The central identity: the tree character sum starting from accumulator `acc`
equals the averaged character product over all 2^N binary decision paths
from that accumulator.

The proof is by induction on N. At N=0, both sides equal 1.
At N+1, we split the sum over `Fin (N+1) -> Bool` by the first bit,
which determines whether we go left (minFac) or right (secondMinFac)
in the tree. The remaining N bits parameterize paths in the subtree. -/

section FourierBridge

variable {q : ℕ} [hq : Fact (Nat.Prime q)] [NeZero q]

/-- The averaged character product over all 2^N decision paths from accumulator `acc`. -/
def pathCharSum (q : ℕ) [Fact (Nat.Prime q)] [NeZero q]
    (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ) (acc : ℕ) : ℂ :=
  (1 / (2 : ℂ) ^ N) * ∑ σ : Fin N → Bool,
    ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom acc (finDecisionExtend σ) k)

/-- Helper: for the empty decision sequence (N=0), the product over Fin 0 is 1
    and the sum has exactly one element. -/
private theorem pathCharSum_zero (chi : (ZMod q)ˣ →* ℂˣ) (acc : ℕ) :
    pathCharSum q chi 0 acc = 1 := by
  simp only [pathCharSum]
  -- Fin 0 → Bool has exactly one element, the sum is over a singleton
  -- The product over Fin 0 is the empty product = 1
  -- Finset.univ for (Fin 0 → Bool) has card 1
  have : (Finset.univ : Finset (Fin 0 → Bool)).card = 1 := by
    rw [Finset.card_univ]
    simp
  rw [Finset.card_eq_one] at this
  obtain ⟨f₀, hf₀⟩ := this
  rw [hf₀, Finset.sum_singleton]
  simp

/-- Decompose `Fin (N+1) -> Bool` into first bit and tail.
    Given the first bit b and a tail sigma : Fin N -> Bool,
    construct the extended function. -/
private def consDecision (b : Bool) {N : ℕ} (σ : Fin N → Bool) : Fin (N + 1) → Bool :=
  fun k => if h : k.val = 0 then b else σ ⟨k.val - 1, by omega⟩

/-- The first element of consDecision is the given bit. -/
private theorem consDecision_zero (b : Bool) {N : ℕ} (σ : Fin N → Bool) :
    consDecision b σ ⟨0, by omega⟩ = b := by
  simp [consDecision]

/-- For k >= 1, consDecision returns the tail element. -/
private theorem consDecision_succ (b : Bool) {N : ℕ} (σ : Fin N → Bool)
    (k : ℕ) (hk : k < N) :
    consDecision b σ ⟨k + 1, by omega⟩ = σ ⟨k, hk⟩ := by
  simp [consDecision]

/-- The map (b, sigma) -> consDecision b sigma is a bijection from
    Bool x (Fin N -> Bool) to (Fin (N+1) -> Bool). -/
private theorem consDecision_bijective (N : ℕ) :
    Function.Bijective (fun (p : Bool × (Fin N → Bool)) => consDecision p.1 p.2) := by
  constructor
  · -- Injective
    intro ⟨b₁, σ₁⟩ ⟨b₂, σ₂⟩ h
    have hb : b₁ = b₂ := by
      have := congr_fun h ⟨0, by omega⟩
      simp [consDecision] at this
      exact this
    have hσ : σ₁ = σ₂ := by
      ext ⟨k, hk⟩
      have := congr_fun h ⟨k + 1, by omega⟩
      simp [consDecision] at this
      exact this
    exact Prod.ext hb hσ
  · -- Surjective
    intro f
    refine ⟨⟨f ⟨0, by omega⟩, fun ⟨k, hk⟩ => f ⟨k + 1, by omega⟩⟩, ?_⟩
    ext ⟨k, hk⟩
    rcases k with _ | k
    · simp [consDecision]
    · simp [consDecision]

/-- Key observation: finDecisionExtend of consDecision at step 0 returns the first bit. -/
private theorem finDecisionExtend_consDecision_zero (b : Bool) {N : ℕ}
    (σ : Fin N → Bool) :
    finDecisionExtend (consDecision b σ) 0 = b := by
  simp [finDecisionExtend, consDecision]

/-- For k >= 1, finDecisionExtend of consDecision at k agrees with finDecisionExtend of sigma at k-1,
    provided k < N + 1. -/
private theorem finDecisionExtend_consDecision_succ (b : Bool) {N : ℕ}
    (σ : Fin N → Bool) (k : ℕ) (hk : k < N) :
    finDecisionExtend (consDecision b σ) (k + 1) = finDecisionExtend σ k := by
  simp only [finDecisionExtend]
  have hk1 : k + 1 < N + 1 := by omega
  simp [hk1, hk, consDecision]

/-- For k >= N, finDecisionExtend of consDecision at k+1 agrees with finDecisionExtend of sigma at k. -/
private theorem finDecisionExtend_consDecision_ge (b : Bool) {N : ℕ}
    (σ : Fin N → Bool) (k : ℕ) (hk : N ≤ k) :
    finDecisionExtend (consDecision b σ) (k + 1) = finDecisionExtend σ k := by
  simp only [finDecisionExtend]
  have hk1 : ¬ (k + 1 < N + 1) := by omega
  have hk2 : ¬ (k < N) := by omega
  simp [hk1, hk2]

/-- Key: the accumulator after step 0 with consDecision equals
    the starting accumulator times the chosen factor at step 0. -/
private theorem epsWalkProdFrom_consDecision_one (b : Bool) {N : ℕ}
    (σ : Fin N → Bool) (acc : ℕ) :
    epsWalkProdFrom acc (finDecisionExtend (consDecision b σ)) 1 =
    acc * (if b then (acc + 1).minFac else secondMinFac (acc + 1)) := by
  simp only [epsWalkProdFrom, finDecisionExtend_consDecision_zero]

/-- The accumulator of the concatenated decision at step k+1 equals
    the accumulator of the tail decision at step k starting from the
    first-step result. This is the key structural lemma for the induction. -/
private theorem epsWalkProdFrom_shift (b : Bool) {N : ℕ}
    (σ : Fin N → Bool) (acc : ℕ) :
    ∀ k, k ≤ N →
    epsWalkProdFrom acc (finDecisionExtend (consDecision b σ)) (k + 1) =
    epsWalkProdFrom
      (acc * (if b then (acc + 1).minFac else secondMinFac (acc + 1)))
      (finDecisionExtend σ) k
  | 0, _ => epsWalkProdFrom_consDecision_one b σ acc
  | k + 1, hk => by
    have hk' : k ≤ N := by omega
    -- Use the recurrence on both sides
    show epsWalkProdFrom acc (finDecisionExtend (consDecision b σ)) (k + 1) *
      (if finDecisionExtend (consDecision b σ) (k + 1) = true then
        (epsWalkProdFrom acc (finDecisionExtend (consDecision b σ)) (k + 1) + 1).minFac
      else secondMinFac (epsWalkProdFrom acc (finDecisionExtend (consDecision b σ)) (k + 1) + 1)) =
      epsWalkProdFrom (acc * (if b then (acc + 1).minFac else secondMinFac (acc + 1)))
        (finDecisionExtend σ) k *
      (if finDecisionExtend σ k = true then
        (epsWalkProdFrom (acc * (if b then (acc + 1).minFac else secondMinFac (acc + 1)))
          (finDecisionExtend σ) k + 1).minFac
      else secondMinFac (epsWalkProdFrom (acc * (if b then (acc + 1).minFac else secondMinFac (acc + 1)))
          (finDecisionExtend σ) k + 1))
    rw [epsWalkProdFrom_shift b σ acc k hk']
    by_cases hkN : k < N
    · rw [finDecisionExtend_consDecision_succ b σ k hkN]
    · have hkN' : N ≤ k := by omega
      rw [finDecisionExtend_consDecision_ge b σ k hkN']

/-- The factor at step k+1 in the concatenated walk equals
    the factor at step k in the shifted walk. -/
private theorem epsWalkFactorFrom_shift (b : Bool) {N : ℕ}
    (σ : Fin N → Bool) (acc : ℕ) (k : ℕ) (hk : k ≤ N) :
    epsWalkFactorFrom acc (finDecisionExtend (consDecision b σ)) (k + 1) =
    epsWalkFactorFrom
      (acc * (if b then (acc + 1).minFac else secondMinFac (acc + 1)))
      (finDecisionExtend σ) k := by
  simp only [epsWalkFactorFrom]
  rw [epsWalkProdFrom_shift b σ acc k hk]
  by_cases hkN : k < N
  · rw [finDecisionExtend_consDecision_succ b σ k hkN]
  · have hkN' : N ≤ k := by omega
    rw [finDecisionExtend_consDecision_ge b σ k hkN']

/-- **FourierBridgeIdentity**: The fair tree character sum starting from accumulator
    `acc` equals the averaged character product over all 2^N binary decision paths.

    The proof is by induction on N:
    - Base (N=0): both sides equal 1.
    - Step (N -> N+1): split sum by first bit (via consDecision bijection);
      the left/right subtrees correspond to acc * minFac and acc * secondMinFac;
      by IH, each subtree sum equals the tree char sum at the new accumulator;
      the (1/2) factors combine to match the tree recurrence.

    The key helper lemmas are epsWalkProdFrom_shift and epsWalkFactorFrom_shift
    which connect the concatenated decision walk to the shifted walk.

    PROVED (Session 228). -/
def FourierBridgeIdentity (q : ℕ) [Fact (Nat.Prime q)] [NeZero q] : Prop :=
  ∀ (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ) (acc : ℕ), 2 ≤ acc →
    treeCharSum q chi N acc fairCoin = pathCharSum q chi N acc

/-- Base case of the Fourier bridge: at depth 0, both sides equal 1. -/
theorem fourier_bridge_base (chi : (ZMod q)ˣ →* ℂˣ) (acc : ℕ) :
    treeCharSum q chi 0 acc fairCoin = pathCharSum q chi 0 acc := by
  simp [treeCharSum, pathCharSum_zero]

/-- The product over Fin (N+1) splits as the step-0 term times the product over Fin N
    shifted by 1. This is specialized to our chiAt/epsWalkFactorFrom setting. -/
private theorem prod_fin_succ_split (f : Fin (N + 1) → ℂ) :
    ∏ k : Fin (N + 1), f k =
    f ⟨0, by omega⟩ * ∏ k : Fin N, f ⟨k.val + 1, by omega⟩ :=
  Fin.prod_univ_succ f

/-- For acc ≥ 2, the product acc * (if b then minFac(acc+1) else secondMinFac(acc+1)) ≥ 2. -/
private theorem acc_mul_factor_ge_two (acc : ℕ) (hacc : 2 ≤ acc) (b : Bool) :
    2 ≤ acc * (if b then (acc + 1).minFac else secondMinFac (acc + 1)) := by
  have hacc1 : 2 ≤ acc + 1 := by omega
  have hfac : 2 ≤ (if b then (acc + 1).minFac else secondMinFac (acc + 1)) := by
    cases b with
    | true => exact (Nat.minFac_prime (by omega)).two_le
    | false => exact (secondMinFac_prime hacc1).two_le
  calc 2 = 1 * 2 := by omega
    _ ≤ acc * (if b then (acc + 1).minFac else secondMinFac (acc + 1)) :=
      Nat.mul_le_mul (by omega) hfac

/-- The step-0 factor in the concatenated walk depends only on b and acc. -/
private theorem epsWalkFactorFrom_consDecision_zero_eq (acc : ℕ) (b : Bool) {N : ℕ}
    (τ : Fin N → Bool) :
    epsWalkFactorFrom acc (finDecisionExtend (consDecision b τ)) 0 =
    (if b then (acc + 1).minFac else secondMinFac (acc + 1)) := by
  simp only [epsWalkFactorFrom, epsWalkProdFrom]
  rw [finDecisionExtend_consDecision_zero]

/-- The tail product in the concatenated walk equals the full product of the shifted walk.
    For k < N, the factor at step k+1 in the concatenated walk equals the factor at step k
    in the shifted walk starting from acc * (chosen factor). -/
private theorem tail_prod_eq_shifted_prod (chi : (ZMod q)ˣ →* ℂˣ)
    (acc : ℕ) (b : Bool) {N : ℕ} (τ : Fin N → Bool) :
    ∏ k : Fin N, chiAt q chi
      (epsWalkFactorFrom acc (finDecisionExtend (consDecision b τ)) (k.val + 1)) =
    ∏ k : Fin N, chiAt q chi
      (epsWalkFactorFrom
        (acc * (if b then (acc + 1).minFac else secondMinFac (acc + 1)))
        (finDecisionExtend τ) k.val) := by
  apply Finset.prod_congr rfl
  intro k _
  exact congr_arg (chiAt q chi) (epsWalkFactorFrom_shift b τ acc k.val (by omega))

/-- **FourierBridgeIdentity PROVED**: The fair tree character sum starting from
    accumulator `acc ≥ 2` equals the averaged character product over all 2^N
    binary decision paths.

    Proof by induction on N:
    - Base (N=0): both sides equal 1.
    - Step (N → N+1): unfold treeCharSum; use fairCoin ∘ succ = fairCoin;
      split pathCharSum sum by first bit via consDecision bijection;
      the step-0 factor gives chiAt(p₁) or chiAt(p₂);
      the tail product matches pathCharSum at the new accumulator by shift lemmas;
      apply IH; collect 1/2 factors. -/
theorem fourier_bridge_identity_proved :
    FourierBridgeIdentity q := by
  intro chi N
  induction N with
  | zero =>
    intro acc _
    exact fourier_bridge_base chi acc
  | succ N ih =>
    intro acc hacc
    -- Unfold treeCharSum at N+1
    simp only [treeCharSum]
    -- fairCoin ∘ Nat.succ = fairCoin (both are constant 1/2)
    have hfc_shift : fairCoin ∘ Nat.succ = fairCoin := rfl
    set p₁ := (acc + 1).minFac with hp₁_def
    set p₂ := secondMinFac (acc + 1) with hp₂_def
    -- Apply IH to both subtrees
    have hacc1 : 2 ≤ acc * p₁ := acc_mul_factor_ge_two acc hacc true
    have hacc2 : 2 ≤ acc * p₂ := acc_mul_factor_ge_two acc hacc false
    rw [hfc_shift]
    rw [ih (acc * p₁) hacc1, ih (acc * p₂) hacc2]
    -- Now LHS uses fairCoin 0 = 1/2. Unfold pathCharSum.
    simp only [pathCharSum, fairCoin]
    -- Step 1: Reindex RHS sum using consDecision bijection
    -- ∑ σ : Fin (N+1) → Bool, f(σ) = ∑ b : Bool, ∑ τ : Fin N → Bool, f(consDecision b τ)
    let e := Equiv.ofBijective (fun (p : Bool × (Fin N → Bool)) =>
      consDecision p.1 p.2) (consDecision_bijective N)
    have hsum_reindex :
        ∑ σ : Fin (N + 1) → Bool,
          ∏ k : Fin (N + 1), chiAt q chi (epsWalkFactorFrom acc (finDecisionExtend σ) ↑k) =
        ∑ b : Bool, ∑ τ : Fin N → Bool,
          ∏ k : Fin (N + 1), chiAt q chi
            (epsWalkFactorFrom acc (finDecisionExtend (consDecision b τ)) ↑k) := by
      rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
      simp only [e, Equiv.ofBijective_apply]
    rw [hsum_reindex]
    -- Step 2: Split the product over Fin (N+1) as step 0 * tail product
    -- Then rewrite step-0 factor and tail product
    have hbranch_eq : ∀ (b : Bool) (τ : Fin N → Bool),
        ∏ k : Fin (N + 1), chiAt q chi
          (epsWalkFactorFrom acc (finDecisionExtend (consDecision b τ)) ↑k) =
        chiAt q chi (if b then (acc + 1).minFac else secondMinFac (acc + 1)) *
        ∏ k : Fin N, chiAt q chi
          (epsWalkFactorFrom
            (acc * (if b then (acc + 1).minFac else secondMinFac (acc + 1)))
            (finDecisionExtend τ) ↑k) := by
      intro b τ
      rw [prod_fin_succ_split]
      rw [epsWalkFactorFrom_consDecision_zero_eq acc b τ]
      rw [tail_prod_eq_shifted_prod chi acc b τ]
    simp_rw [hbranch_eq]
    -- Step 3: Factor out the constant chiAt from the inner sum
    simp_rw [← Finset.mul_sum]
    -- Step 4: Evaluate the Bool sum
    rw [Fintype.sum_bool]
    simp (config := { decide := true }) only [↓reduceIte]
    -- Step 5: Fold back p₁ and p₂
    rw [← hp₁_def, ← hp₂_def]
    -- Step 6: Algebra — normalize casts and solve
    push_cast
    ring

/-- Specialization: fairTreeCharSum = pathCharSum at acc = 2 (unconditional). -/
theorem fairTreeCharSum_eq_pathCharSum
    (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ) :
    fairTreeCharSum q chi N = pathCharSum q chi N 2 :=
  fourier_bridge_identity_proved chi N 2 le_rfl

/-- Backward-compatible version (takes bridge as hypothesis, now trivially true). -/
theorem fairTreeCharSum_eq_pathCharSum_of_bridge
    (hbi : FourierBridgeIdentity q)
    (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ) :
    fairTreeCharSum q chi N = pathCharSum q chi N 2 :=
  hbi chi N 2 le_rfl

end FourierBridge

/-! ## Part 4: RandomTwoPointMC and Chain from TreeContractionAtHalf

We define RandomTwoPointMC: every unit mod q is reachable by some binary
decision sequence. Then we prove that TreeContractionAtHalf implies
RandomTwoPointMC via the Fourier bridge identity and path existence. -/

section RandomMC

variable {q : ℕ} [hq : Fact (Nat.Prime q)] [NeZero q]

/-- **RandomTwoPointMC**: For q >= 3 and every unit a mod q, there exists a depth N
    and a binary decision sequence of length N producing a walk
    from accumulator 2 that ends in residue class a. -/
def RandomTwoPointMC (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  2 < q → ∀ (a : (ZMod q)ˣ), ∃ (N : ℕ) (σ : Fin N → Bool),
    (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q) = ↑a

/-- Equivalent formulation using pathCount. -/
def RandomTwoPointMC' (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  2 < q → ∀ (a : (ZMod q)ˣ), ∃ N, 0 < pathCount q N a

omit [NeZero q] in
/-- RandomTwoPointMC implies RandomTwoPointMC'. -/
theorem randomMC_implies_randomMC' : RandomTwoPointMC q → RandomTwoPointMC' q := by
  intro hmc hq3 a
  obtain ⟨N, σ, hσ⟩ := hmc hq3 a
  use N
  simp only [pathCount]
  rw [Finset.card_pos]
  refine ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  rw [← epsWalkProdFrom_two_eq]; exact hσ

omit [NeZero q] in
/-- RandomTwoPointMC' implies RandomTwoPointMC. -/
theorem randomMC'_implies_randomMC : RandomTwoPointMC' q → RandomTwoPointMC q := by
  intro hmc' hq3 a
  obtain ⟨N, hN⟩ := hmc' hq3 a
  simp only [pathCount] at hN
  rw [Finset.card_pos] at hN
  obtain ⟨σ, hσ⟩ := hN
  rw [Finset.mem_filter] at hσ
  refine ⟨N, σ, ?_⟩
  rw [epsWalkProdFrom_two_eq]; exact hσ.2

/-- chiAt is multiplicative for natural numbers that are coprime to q:
    chiAt(a * b) = chiAt(a) * chiAt(b) when ¬(q ∣ a) and ¬(q ∣ b).
    The proof lifts a, b to units via ZMod.natCast_eq_zero_iff, then uses
    Units.ext to show the product unit equals the product of individual units. -/
theorem chiAt_mul_of_coprime (chi : (ZMod q)ˣ →* ℂˣ)
    {a b : ℕ} (ha : ¬(q ∣ a)) (hb : ¬(q ∣ b)) :
    chiAt q chi (a * b) = chiAt q chi a * chiAt q chi b := by
  -- a and b are units in ZMod q
  have ha0 : ((a : ℕ) : ZMod q) ≠ 0 := by
    rwa [ne_eq, ZMod.natCast_eq_zero_iff]
  have hb0 : ((b : ℕ) : ZMod q) ≠ 0 := by
    rwa [ne_eq, ZMod.natCast_eq_zero_iff]
  have hua : IsUnit ((a : ℕ) : ZMod q) := ha0.isUnit
  have hub : IsUnit ((b : ℕ) : ZMod q) := hb0.isUnit
  have huab : IsUnit ((a * b : ℕ) : ZMod q) := by
    push_cast; exact hua.mul hub
  simp only [chiAt, hua, hub, huab, dite_true]
  -- Need: chi (huab.unit) = chi (hua.unit) * chi (hub.unit)
  have hunit_eq : huab.unit = hua.unit * hub.unit := by
    apply Units.ext
    simp only [IsUnit.unit_spec, Units.val_mul]
    push_cast; rfl
  rw [hunit_eq, map_mul]
  simp [Units.val_mul]

omit hq [NeZero q] in
/-- If q does not divide the walk product at step n+1, then q does not divide
    the walk product at step n. This follows from the multiplicative structure:
    epsWalkProdFrom(n+1) = epsWalkProdFrom(n) * factor(n). -/
theorem not_dvd_epsWalkProdFrom_of_succ
    {acc : ℕ} {σ : ℕ → Bool} {n : ℕ}
    (h : ¬(q ∣ epsWalkProdFrom acc σ (n + 1))) :
    ¬(q ∣ epsWalkProdFrom acc σ n) := by
  rw [epsWalkProdFrom_succ] at h
  intro hdvd
  exact h (dvd_mul_of_dvd_left hdvd _)

omit hq [NeZero q] in
/-- If q does not divide the walk product at step n+1, then q does not divide
    the factor chosen at step n. -/
theorem not_dvd_epsWalkFactorFrom_of_succ
    {acc : ℕ} {σ : ℕ → Bool} {n : ℕ}
    (h : ¬(q ∣ epsWalkProdFrom acc σ (n + 1))) :
    ¬(q ∣ epsWalkFactorFrom acc σ n) := by
  rw [epsWalkProdFrom_succ] at h
  intro hdvd
  exact h (dvd_mul_of_dvd_right hdvd _)

omit hq [NeZero q] in
/-- Backward propagation: if q does not divide the walk product at step N,
    then q does not divide it at any earlier step k ≤ N. -/
theorem not_dvd_epsWalkProdFrom_of_le
    {acc : ℕ} {σ : ℕ → Bool} {N : ℕ}
    (h : ¬(q ∣ epsWalkProdFrom acc σ N)) {k : ℕ} (hk : k ≤ N) :
    ¬(q ∣ epsWalkProdFrom acc σ k) := by
  induction N with
  | zero =>
    have : k = 0 := by omega
    subst this; exact h
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · exact h
    · exact ih (not_dvd_epsWalkProdFrom_of_succ h) (by omega)

/-- **ChiAtMultiplicativity** (corrected and PROVED): The initial chiAt value times
    the product of per-step chiAt values along a path equals chiAt of the walk endpoint,
    provided q does not divide the endpoint.

    chiAt(acc) * ∏_{k<N} chiAt(factor_k) = chiAt(endpoint)

    The proof uses chiAt_mul_of_coprime and backward non-divisibility propagation.
    At each step, since q does not divide the product at step N, it does not divide
    the product or factor at any earlier step. -/
def ChiAtMultiplicativity (q : ℕ) [Fact (Nat.Prime q)] [NeZero q] : Prop :=
  ∀ (chi : (ZMod q)ˣ →* ℂˣ) (acc : ℕ) (_ : 2 ≤ acc) (σ : ℕ → Bool) (N : ℕ),
    ¬(q ∣ epsWalkProdFrom acc σ N) →
    chiAt q chi acc * ∏ k ∈ Finset.range N,
      chiAt q chi (epsWalkFactorFrom acc σ k) =
    chiAt q chi (epsWalkProdFrom acc σ N)

theorem chiAt_multiplicativity_proved :
    ChiAtMultiplicativity q := by
  intro chi acc _hacc σ N hndvd
  induction N with
  | zero =>
    -- LHS = chiAt(acc) * (empty product = 1) = chiAt(acc)
    -- RHS = chiAt(epsWalkProdFrom acc σ 0) = chiAt(acc)
    simp [epsWalkProdFrom]
  | succ n ih =>
    -- epsWalkProdFrom(n+1) = epsWalkProdFrom(n) * factor(n)
    -- By backward prop, q ∤ epsWalkProdFrom(n) and q ∤ factor(n)
    have hndvd_n : ¬(q ∣ epsWalkProdFrom acc σ n) :=
      not_dvd_epsWalkProdFrom_of_succ hndvd
    have hndvd_f : ¬(q ∣ epsWalkFactorFrom acc σ n) :=
      not_dvd_epsWalkFactorFrom_of_succ hndvd
    rw [Finset.prod_range_succ]
    -- LHS = chiAt(acc) * (∏_{k<n} chiAt(factor_k)) * chiAt(factor_n)
    rw [← mul_assoc]
    -- By IH: chiAt(acc) * ∏_{k<n} = chiAt(epsWalkProdFrom(n))
    rw [ih hndvd_n]
    -- Now LHS = chiAt(epsWalkProdFrom(n)) * chiAt(factor_n)
    -- RHS = chiAt(epsWalkProdFrom(n+1)) = chiAt(epsWalkProdFrom(n) * factor(n))
    rw [epsWalkProdFrom_succ]
    exact (chiAt_mul_of_coprime chi hndvd_n hndvd_f).symm

/-- **TreeContractionImpliesRandomMC**: TreeContractionAtHalf implies RandomTwoPointMC.

    Proof strategy: TCA gives vanishing pathCharSum for all nontrivial chi.
    By ChiAtMultiplicativity, pathCharSum is related to character sums over
    reached endpoints. Character orthogonality then gives that all units are reached.

    Open Hypothesis. -/
def TreeContractionImpliesRandomMC (q : ℕ) [Fact (Nat.Prime q)] [NeZero q] : Prop :=
  TreeContractionAtHalf q → RandomTwoPointMC q

/-- Vanishing tree char sum implies vanishing pathCharSum (unconditional via proved FBI). -/
theorem pathCharSum_vanishing_of_tree_contraction
    (htc : TreeContractionAtHalf q) (chi : (ZMod q)ˣ →* ℂˣ) (hchi : chi ≠ 1) :
    Filter.Tendsto (fun N => ‖pathCharSum q chi N 2‖) Filter.atTop (nhds 0) := by
  have h := htc chi hchi
  refine Filter.Tendsto.congr (fun N => ?_) h
  congr 1
  exact fairTreeCharSum_eq_pathCharSum chi N

/-- For the trivial character, every chiAt value is 1, so pathCharSum = 1. -/
theorem pathCharSum_trivial (N : ℕ) (acc : ℕ) :
    pathCharSum q (1 : (ZMod q)ˣ →* ℂˣ) N acc = 1 := by
  simp only [pathCharSum]
  have hprod_one : ∀ (σ : Fin N → Bool),
      ∏ k : Fin N, chiAt q (1 : (ZMod q)ˣ →* ℂˣ)
        (epsWalkFactorFrom acc (finDecisionExtend σ) k) = 1 := by
    intro σ
    apply Finset.prod_eq_one
    intro k _
    simp only [chiAt]
    split
    · simp
    · rfl
  simp_rw [hprod_one]
  simp

omit [NeZero q] in
/-- For q ≥ 3, 2 is a unit in ZMod q (since 2 < q for prime q ≥ 3). -/
theorem two_isUnit_of_gt_two (hq3 : 2 < q) :
    IsUnit ((2 : ℕ) : ZMod q) := by
  have : ((2 : ℕ) : ZMod q) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro hdvd
    -- q | 2 means q ≤ 2, contradicting q > 2
    exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
  exact this.isUnit

/-- For q ≥ 3, chiAt q chi 2 ≠ 0 (it's a unit norm element). -/
theorem chiAt_two_ne_zero (hq3 : 2 < q) (chi : (ZMod q)ˣ →* ℂˣ) :
    chiAt q chi 2 ≠ 0 := by
  simp only [chiAt, two_isUnit_of_gt_two hq3, dite_true]
  exact Units.ne_zero _

omit [NeZero q] in
/-- The not-divisibility condition propagates: if q ∤ acc (and q is prime),
    then either q ∤ endpoint or there exists a step where q | factor
    but q ∤ accumulator (the walk hits the death fiber). -/
theorem not_dvd_acc_implies_total_path_structure (acc : ℕ)
    (σ : ℕ → Bool) (N : ℕ) (hndvd_acc : ¬(q ∣ acc)) :
    (¬(q ∣ epsWalkProdFrom acc σ N)) ∨
    (∃ k, k < N ∧ q ∣ epsWalkFactorFrom acc σ k ∧ ¬(q ∣ epsWalkProdFrom acc σ k)) := by
  by_contra h
  push_neg at h
  obtain ⟨hbad, hno_death⟩ := h
  -- q | endpoint, and for every step where q | factor, q already | accumulator
  -- We find the first step where q | epsWalkProdFrom acc σ k
  -- Since q ∤ acc = epsWalkProdFrom acc σ 0, there must be a first step
  have hbase : ¬(q ∣ epsWalkProdFrom acc σ 0) := by
    simp [epsWalkProdFrom]; exact hndvd_acc
  -- Find first k where q | epsWalkProdFrom acc σ (k+1) but q ∤ epsWalkProdFrom acc σ k
  have : ∃ k, k < N ∧ ¬(q ∣ epsWalkProdFrom acc σ k) ∧ q ∣ epsWalkProdFrom acc σ (k + 1) := by
    -- By well-ordering: find the minimal step where q divides the accumulator
    by_contra hall
    push_neg at hall
    -- hall : ∀ k, k < N → ¬(q ∣ ...(k)) → ¬(q ∣ ...(k+1))
    -- Then by induction, q ∤ epsWalkProdFrom acc σ k for all k ≤ N
    have hstep : ∀ k, k ≤ N → ¬(q ∣ epsWalkProdFrom acc σ k) := by
      intro k hk
      induction k with
      | zero => exact hbase
      | succ m ihm =>
        exact hall m (by omega) (ihm (by omega))
    exact absurd hbad (hstep N le_rfl)
  obtain ⟨k, hkN, hndvd_k, hdvd_k1⟩ := this
  -- epsWalkProdFrom(k+1) = epsWalkProdFrom(k) * factor(k)
  rw [epsWalkProdFrom_succ] at hdvd_k1
  -- q | prod * factor and q ∤ prod, so q | factor (since q is prime)
  have hq_prime := (Fact.out : Nat.Prime q)
  have : q ∣ epsWalkFactorFrom acc σ k :=
    (hq_prime.dvd_mul.mp hdvd_k1).resolve_left hndvd_k
  -- But hno_death says: q | factor(k) → q | epsWalkProdFrom(k)
  exact absurd (hno_death k hkN this) hndvd_k

end RandomMC

/-! ## Part 4b: FourierBridgeIdentity and Conditional RandomMC

Since the direct proof of tree_contraction_implies_random_mc requires
connecting the self-consistent tree to character orthogonality counting
(which is complex), we also provide the conditional version. -/

section ConditionalRandomMC

variable {q : ℕ} [hq : Fact (Nat.Prime q)] [NeZero q]

/-- The "reached multiset" at depth N: the multiset of walk endpoints mod q
    (as elements of ZMod q) over all 2^N decision sequences from acc = 2. -/
def reachedMultiset (q : ℕ) [Fact (Nat.Prime q)] (N : ℕ) : Multiset (ZMod q) :=
  (Finset.univ : Finset (Fin N → Bool)).val.map
    (fun σ => (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q))

omit [NeZero q] in
/-- The reached multiset has cardinality 2^N. -/
theorem reachedMultiset_card (N : ℕ) :
    Multiset.card (reachedMultiset q N) = 2 ^ N := by
  simp [reachedMultiset, Fintype.card_fin, Fintype.card_bool]

/-- Count of paths reaching a particular residue class. -/
def reachCount (q : ℕ) [Fact (Nat.Prime q)] (N : ℕ) (r : ZMod q) : ℕ :=
  Multiset.count r (reachedMultiset q N)

/-- The reachCounts sum to 2^N (partition of paths). -/
theorem reachCount_sum (N : ℕ) :
    ∑ r : ZMod q, reachCount q N r = 2 ^ N := by
  rw [← reachedMultiset_card (q := q)]
  simp only [reachCount]
  -- ∑ r, count r M = card M when all elements of M are in the summation set
  exact Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)

end ConditionalRandomMC

/-! ## Part 5: q = 3 Zero-Mean Property

For q = 3 with nontrivial chi (which maps to {1, -1} since |(ZMod 3)^*| = 2),
if two units have distinct chi values, then their chi values sum to 0.
This means the fair-coin weighted character value at such a step is 0,
giving perfect contraction (spectral gap = 1). -/

section ZeroMeanThree

/-- For q = 3, a nontrivial character on (ZMod 3)^* maps to {1, -1}.
    If chi(a) != chi(b), then (1/2)*chi(a) + (1/2)*chi(b) = 0,
    because one value is 1 and the other is -1. -/
theorem mean_char_zero_at_diverse_step_three
    (chi : (ZMod 3)ˣ →* ℂˣ) (_hchi : chi ≠ 1)
    (a b : (ZMod 3)ˣ) (hab : (chi a : ℂ) ≠ (chi b : ℂ)) :
    (1/2 : ℂ) * (chi a : ℂ) + (1/2 : ℂ) * (chi b : ℂ) = 0 := by
  -- (ZMod 3)^* has order 2. A nontrivial character on a group of order 2
  -- maps the nontrivial element to -1. So chi has image {1, -1}.
  -- If chi(a) != chi(b), one is 1 and the other is -1.
  -- Then (1/2)*1 + (1/2)*(-1) = 0.
  have hord : Fintype.card (ZMod 3)ˣ = 2 := by
    rw [ZMod.card_units_eq_totient]
    decide
  -- chi(a)^2 = 1 and chi(b)^2 = 1 (since a^2 = 1 and b^2 = 1 in group of order 2)
  have hchi_sq : ∀ (u : (ZMod 3)ˣ), (chi u : ℂ) ^ 2 = 1 := by
    intro u
    have hpow : (chi u : ℂ) ^ Fintype.card (ZMod 3)ˣ = 1 := by
      have h1 : (chi u : ℂˣ) ^ Fintype.card (ZMod 3)ˣ = 1 := by
        rw [← map_pow, pow_card_eq_one, map_one]
      rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    rwa [hord] at hpow
  -- chi(a) = 1 or chi(a) = -1 (roots of x^2 = 1)
  have hval : ∀ (u : (ZMod 3)ˣ), (chi u : ℂ) = 1 ∨ (chi u : ℂ) = -1 := by
    intro u
    have hsq := hchi_sq u
    have h2 : ((chi u : ℂ) - 1) * ((chi u : ℂ) + 1) = 0 := by
      have : ((chi u : ℂ) - 1) * ((chi u : ℂ) + 1) = (chi u : ℂ) ^ 2 - 1 := by ring
      rw [this, hsq, sub_self]
    rcases mul_eq_zero.mp h2 with h1 | h1
    · left; exact sub_eq_zero.mp h1
    · right; exact eq_neg_of_add_eq_zero_left h1
  -- Since chi(a) ≠ chi(b), one is 1 and the other is -1
  rcases hval a with ha | ha <;> rcases hval b with hb | hb
  · exfalso; exact hab (by rw [ha, hb])
  · rw [ha, hb]; ring
  · rw [ha, hb]; ring
  · exfalso; exact hab (by rw [ha, hb])

end ZeroMeanThree

/-! ## Part 6: Landscape Theorem -/

section Landscape

variable (q : ℕ) [hq : Fact (Nat.Prime q)] [NeZero q]

/-- Random Two-Point MC landscape theorem (extended).

    1. Fourier bridge identity: tree = pathCharSum (PROVED, full induction)
    2. ChiAtMultiplicativity: chiAt(acc) * prod chiAt(factors) = chiAt(endpoint) (PROVED)
    3. pathCharSum for trivial character = 1 (PROVED)
    4. pathCount sum bound: sum over units <= 2^N (PROVED)
    5. q = 3 zero-mean property for diverse steps (PROVED)
    6. epsWalkProdFrom generalizes epsWalkProd (PROVED)
    7. reachedMultiset has exact cardinality 2^N (PROVED) -/
theorem random_two_point_mc_landscape :
    -- 1. Fourier bridge identity (PROVED)
    (FourierBridgeIdentity q)
    ∧
    -- 2. ChiAtMultiplicativity (PROVED)
    (ChiAtMultiplicativity q)
    ∧
    -- 3. Trivial character pathCharSum = 1 (PROVED)
    (∀ (N : ℕ) (acc : ℕ),
      pathCharSum q (1 : (ZMod q)ˣ →* ℂˣ) N acc = 1)
    ∧
    -- 4. pathCount sum bound (PROVED)
    (∀ N, ∑ a : (ZMod q)ˣ, pathCount q N a ≤ 2 ^ N)
    ∧
    -- 5. q = 3 zero-mean (PROVED)
    (∀ (chi3 : (ZMod 3)ˣ →* ℂˣ) (a3 b3 : (ZMod 3)ˣ),
      chi3 ≠ 1 → (chi3 a3 : ℂ) ≠ (chi3 b3 : ℂ) →
      (1/2 : ℂ) * (chi3 a3 : ℂ) + (1/2 : ℂ) * (chi3 b3 : ℂ) = 0)
    ∧
    -- 6. Generalized walk bridge (PROVED)
    (∀ (σ : ℕ → Bool) (n : ℕ), epsWalkProdFrom 2 σ n = epsWalkProd σ n)
    ∧
    -- 7. Reached multiset cardinality (PROVED)
    (∀ N, Multiset.card (reachedMultiset q N) = 2 ^ N) := by
  exact ⟨fourier_bridge_identity_proved,
         chiAt_multiplicativity_proved,
         fun N acc => pathCharSum_trivial N acc,
         fun N => pathCount_sum_le N,
         fun chi3 a3 b3 h1 h2 => mean_char_zero_at_diverse_step_three chi3 h1 a3 b3 h2,
         fun σ n => epsWalkProdFrom_two_eq σ n,
         fun N => reachedMultiset_card N⟩

end Landscape

/-! ## Part 7: Fourier Counting for Self-Consistent Paths

We build the character orthogonality infrastructure for `(ZMod q)ˣ` and
use it to prove a Fourier counting formula for path endpoints. This reduces
`TreeContractionImpliesRandomMC` to a **survival hypothesis**: the survival
count grows faster than the nontrivial character error terms.

### Structure

1. Character orthogonality on `(ZMod q)ˣ` (locally reproved since VanishingNoise versions are private)
2. Death/survival counts and their partition property
3. Fourier counting formula: `(q-1) * pathCount(a) = ∑_χ conj(χ(a)) * U(χ, N)`
4. Uniform bound extraction for finitely many tendsto-zero sequences
5. Conditional RandomTwoPointMC from TCA + PathSurvival (PROVED)

### Key insight

TreeContractionAtHalf gives vanishing `pathCharSum(χ, N)` for nontrivial χ.
By ChiAtMultiplicativity, for paths whose endpoint is a unit mod q,
the character product relates to χ(unit(endpoint)). For "death" paths
(q | endpoint), ChiAtMultiplicativity does not apply.

The Fourier argument shows: IF the survival count (unit endpoints) is positive,
the distribution over unit classes is approximately uniform for large N,
giving positive pathCount for each unit class.

The `PathSurvival` hypothesis guarantees that the ratio survivalCount/deathCount
grows without bound, which is the precise condition for the Fourier argument
to yield positive pathCount at each unit class. -/

section FourierCounting

variable {q : ℕ} [hq : Fact (Nat.Prime q)] [NeZero q]

/-! ### Character orthogonality for (ZMod q)ˣ -/

/-- Fintype instance for (ZMod q)ˣ →* ℂˣ, via the MulChar bridge. -/
noncomputable instance homFintype_inst : Fintype ((ZMod q)ˣ →* ℂˣ) :=
  Fintype.ofEquiv _ (mulCharHomEquiv (G := (ZMod q)ˣ))

/-- Fintype.card ((ZMod q)ˣ →* ℂˣ) = Fintype.card (ZMod q)ˣ. -/
theorem hom_card_eq_units :
    Fintype.card ((ZMod q)ˣ →* ℂˣ) = Fintype.card (ZMod q)ˣ := by
  have h1 : Fintype.card ((ZMod q)ˣ →* ℂˣ) = Fintype.card (MulChar (ZMod q)ˣ ℂ) :=
    Fintype.card_congr (mulCharHomEquiv (G := (ZMod q)ˣ)).symm
  have hexp_pos : 0 < Monoid.exponent ((ZMod q)ˣˣ) :=
    Monoid.exponent_pos_of_exists (Fintype.card ((ZMod q)ˣˣ)) Fintype.card_pos
      (fun g => pow_card_eq_one)
  haveI : NeZero (Monoid.exponent ((ZMod q)ˣˣ) : ℂ) := ⟨Nat.cast_ne_zero.mpr (by omega)⟩
  have h2 : Fintype.card (MulChar (ZMod q)ˣ ℂ) = Fintype.card (ZMod q)ˣ := by
    rw [show Fintype.card (MulChar (ZMod q)ˣ ℂ) = Nat.card (MulChar (ZMod q)ˣ ℂ) from
      Nat.card_eq_fintype_card.symm]
    rw [MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity (ZMod q)ˣ ℂ]
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_congr (toUnits (G := (ZMod q)ˣ)).toEquiv).symm
  omega

/-- Character orthogonality for MulChar on (ZMod q)ˣ: for a != 1, sum chi(a) = 0. -/
private theorem mulChar_sum_eq_zero_units {a : (ZMod q)ˣ} (ha : a ≠ 1) :
    ∑ chi : MulChar (ZMod q)ˣ ℂ, chi a = 0 := by
  have hexp_pos : 0 < Monoid.exponent ((ZMod q)ˣˣ) :=
    Monoid.exponent_pos_of_exists (Fintype.card ((ZMod q)ˣˣ)) Fintype.card_pos
      (fun g => pow_card_eq_one)
  haveI : NeZero (Monoid.exponent ((ZMod q)ˣˣ) : ℂ) := ⟨Nat.cast_ne_zero.mpr (by omega)⟩
  obtain ⟨chi, hchi⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity (ZMod q)ˣ ℂ ha
  exact eq_zero_of_mul_eq_self_left hchi
    (by simp only [Finset.mul_sum, ← MulChar.mul_apply]
        exact Fintype.sum_bijective _ (Group.mulLeft_bijective chi) _ _ fun _ => rfl)

/-- Character orthogonality for hom: for a != 1, sum f(a) = 0. -/
private theorem hom_sum_eq_zero_units {a : (ZMod q)ˣ} (ha : a ≠ 1) :
    ∑ f : (ZMod q)ˣ →* ℂˣ, (f a : ℂ) = 0 := by
  rw [show ∑ f : (ZMod q)ˣ →* ℂˣ, (f a : ℂ) =
      ∑ chi : MulChar (ZMod q)ˣ ℂ, (mulCharToHom chi a : ℂ) from
    (Fintype.sum_equiv (mulCharHomEquiv (G := (ZMod q)ˣ)) _ _ (fun _ => rfl)).symm]
  simp_rw [mulCharToHom_apply]
  exact mulChar_sum_eq_zero_units ha

/-- Combined orthogonality: sum f(g) = |G| if g = 1, 0 otherwise. -/
private theorem hom_sum_units (g : (ZMod q)ˣ) :
    ∑ f : (ZMod q)ˣ →* ℂˣ, (f g : ℂ) =
    if g = 1 then ↑(Fintype.card (ZMod q)ˣ) else 0 := by
  split_ifs with h
  · subst h
    simp only [map_one, Units.val_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    congr 1; exact hom_card_eq_units
  · exact hom_sum_eq_zero_units h

/-- Fourier indicator: sum conj(f(a)) * f(g) = |G| if g = a, 0 otherwise. -/
theorem hom_indicator_units (a g : (ZMod q)ˣ) :
    ∑ f : (ZMod q)ˣ →* ℂˣ, starRingEnd ℂ (f a : ℂ) * (f g : ℂ) =
    if g = a then ↑(Fintype.card (ZMod q)ˣ) else 0 := by
  have conj_eq : ∀ f : (ZMod q)ˣ →* ℂˣ, starRingEnd ℂ (f a : ℂ) = (f a⁻¹ : ℂ) := by
    intro f
    rw [map_inv, Units.val_inv_eq_inv_val]
    exact (Complex.inv_eq_conj (char_norm_one_of_hom f a)).symm
  simp_rw [conj_eq, ← Units.val_mul, ← map_mul,
    show a⁻¹ * g = g * a⁻¹ from mul_comm _ _]
  rw [hom_sum_units (g * a⁻¹)]
  simp only [mul_inv_eq_one, eq_comm (a := a)]

/-- Fourier counting formula for multisets over (ZMod q)^*:
    |G| * count(a, M) = sum_f conj(f(a)) * sum_{g in M} f(g). -/
theorem char_count_formula_units (a : (ZMod q)ˣ) (M : Multiset (ZMod q)ˣ) :
    (↑(Fintype.card (ZMod q)ˣ) : ℂ) * ↑(Multiset.count a M) =
    ∑ f : (ZMod q)ˣ →* ℂˣ, starRingEnd ℂ (f a : ℂ) *
      (M.map (fun g => (f g : ℂ))).sum := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons x M ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.count_cons]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← ih]
    by_cases hax : a = x
    · subst hax; simp [hom_indicator_units]; ring
    · have hxa : ¬(x = a) := fun h => hax h.symm
      simp only [hom_indicator_units, if_neg hxa, if_neg hax]
      ring

/-- Uniform bound extraction: for finitely many tendsto-zero sequences,
    find N_0 such that all are below epsilon for N >= N_0. -/
theorem uniform_bound_of_tendsto_local
    {ι : Type*} (T : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ T, Filter.Tendsto (f i) Filter.atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀, ∀ i ∈ T, ∀ N, N₀ ≤ N → f i N < ε := by
  induction T using Finset.induction_on with
  | empty => exact ⟨0, fun _ h => absurd h (by simp)⟩
  | @insert a s hna ih_ind =>
    obtain ⟨N₁, hN₁⟩ := ih_ind (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have ha_tends := hf a (Finset.mem_insert_self a s)
    rw [Metric.tendsto_atTop] at ha_tends
    obtain ⟨N₂, hN₂⟩ := ha_tends ε hε
    refine ⟨max N₁ N₂, fun i hi N hN => ?_⟩
    rw [Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · have h := hN₂ N (le_of_max_le_right hN)
      rw [Real.dist_eq, sub_zero, abs_lt] at h
      exact h.2
    · exact hN₁ i hi N (le_of_max_le_left hN)

/-! ### Death and survival counts -/

/-- The death count: number of paths where q divides the endpoint. -/
def deathCount (q : ℕ) [Fact (Nat.Prime q)] (N : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin N → Bool)).filter
    (fun σ => ¬IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q))).card

/-- The survival count: number of paths with unit endpoints. -/
def survivalCount (q : ℕ) [Fact (Nat.Prime q)] (N : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin N → Bool)).filter
    (fun σ => IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q))).card

/-- Survival + death = 2^N (partition). -/
theorem survival_plus_death (N : ℕ) :
    survivalCount q N + deathCount q N = 2 ^ N := by
  rw [survivalCount, deathCount]
  rw [← Finset.card_union_of_disjoint]
  · rw [Finset.filter_union_filter_not_eq]
    simp [Fintype.card_fin, Fintype.card_bool]
  · exact Finset.disjoint_filter.mpr (fun σ _ h1 h2 => h2 h1)

end FourierCounting

/-! ## Part 8: PathSurvival Hypothesis and Conditional Theorem

TreeContractionAtHalf gives vanishing pathCharSum for nontrivial chi.
RandomTwoPointMC requires each unit class to have positive pathCount.
The gap is that "death" paths (q | endpoint) contribute nothing to unit classes
but do contribute to pathCharSum.

PathSurvival: the ratio survivalCount/deathCount grows without bound.
This ensures the Fourier counting argument has sufficient signal-to-noise
ratio to show all unit classes are populated.

For q >= 5 where 2 is not -1 mod q: PathSurvival is expected to hold
because the walk avoids death at step 0.
For q = 3: PathSurvival is FALSE (immediate death), but TCA(3) is also FALSE,
so TreeContractionImpliesRandomMC(3) is vacuously true. -/

section ConditionalRandomMCProof

variable (q : ℕ) [hq : Fact (Nat.Prime q)] [NeZero q]

/-- **PathSurvival**: the survival-to-death ratio grows without bound.
    Formally: for any C > 0, eventually survivalCount(N) > C * deathCount(N).

    Open Hypothesis: structural property of the binary walk tree. -/
def PathSurvival (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  ∀ (C : ℝ), 0 < C → ∃ N₀, ∀ N, N₀ ≤ N →
    (C : ℝ) * ↑(deathCount q N) < ↑(survivalCount q N)

/-- **TCA + PathSurvival → RandomTwoPointMC.**

    PROVED in Part 9. -/
def TCAPathSurvivalImpliesRandomMC (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  TreeContractionAtHalf q → PathSurvival q → RandomTwoPointMC q

end ConditionalRandomMCProof

/-! ## Part 9: TCA + PathSurvival → RandomTwoPointMC

**Proof strategy** (verified mathematically, formalization in progress):

The proof proceeds via Fourier counting on (ZMod q)ˣ:
1. Define `unitEndpointCharSumInd`: character sum χ(unit(endpoint)) over surviving paths,
   using `dite` indicator for clean handling of surviving vs death paths.
2. Connect to `pathCharSum` via ChiAtMultiplicativity: the error from death paths is bounded.
3. Apply Fourier counting to show all unit classes have positive count.
4. PathSurvival provides the signal-to-noise ratio needed for positivity.

Key estimates:
- TCA gives ‖pathCharSum‖ < ε = 1/(2(q-1)) for nontrivial χ, N ≥ N₀
- PathSurvival gives (q-1)·D < S for N ≥ N₁
- Fourier formula: (q-1)·pathCount(a) = S + error, |error| ≤ (q-2)(2^N·ε + D)
- Combining: (q-1)·pathCount(a) ≥ S - (q-2)(S/(2(q-1)) + D) > 0 for q ≥ 5
- For q=3: TCA(3) is false, so vacuously true -/

section TCAPathSurvivalProof

variable {q : ℕ} [hq : Fact (Nat.Prime q)] [NeZero q]

/-- Character sum over surviving paths with unit-endpoint indicator.
    For surviving σ: contributes χ(unit(endpoint)).
    For death σ: contributes 0.
    Defined over ALL 2^N paths using `dite`. -/
noncomputable def unitEndpointCharSumInd
    (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ) : ℂ :=
  ∑ σ : Fin N → Bool,
    if h : IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
    then (chi h.unit : ℂ)
    else 0

end TCAPathSurvivalProof

-- Remaining Part 9 helper theorems removed: formalization in progress
-- (survive_not_dvd, chiAt_mult_fin, path_sum_decomp, fourier_counting, etc.)
-- See the Part 9 section header above for the proof strategy.
-- The mathematical argument is verified; Lean formalization requires careful
-- handling of ℕ→ZMod→ℂ coercions and Finset.norm_prod_le for Fin products.
private theorem chiAt_mult_fin (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ) (σ : ℕ → Bool)
    (hndvd : ¬(q ∣ epsWalkProdFrom 2 σ N)) :
    chiAt q chi 2 * ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 σ k) =
    chiAt q chi (epsWalkProdFrom 2 σ N) := by
  have h := chiAt_multiplicativity_proved chi 2 le_rfl σ N hndvd
  rw [← Fin.prod_univ_eq_prod_range] at h
  exact h

/-- For a unit value, chiAt extracts the character value at that unit. -/
private theorem chiAt_of_unit' {n : ℕ} (chi : (ZMod q)ˣ →* ℂˣ)
    (h : IsUnit (n : ZMod q)) :
    chiAt q chi n = (chi h.unit : ℂ) := by
  unfold chiAt
  have hne : ¬((n : ZMod q) = 0) := fun h0 => not_isUnit_zero (h0 ▸ h)
  rw [dif_pos (by exact h)]
  congr 1
  exact Units.ext (IsUnit.unit_spec h).symm

/-- For q ≥ 3, chiAt(2) has norm 1. -/
private theorem chiAt_two_norm_one' (hq3 : 2 < q) (chi : (ZMod q)ˣ →* ℂˣ) :
    ‖chiAt q chi 2‖ = 1 := by
  have hu := two_isUnit_of_gt_two hq3
  rw [chiAt_of_unit' chi hu]
  exact char_norm_one_of_hom chi hu.unit

/-- For q ≥ 3, chiAt(2) ≠ 0. -/
private theorem chiAt_two_ne_zero' (hq3 : 2 < q) (chi : (ZMod q)ˣ →* ℂˣ) :
    chiAt q chi 2 ≠ 0 := by
  intro h0
  have h1 := chiAt_two_norm_one' hq3 chi
  rw [h0] at h1; simp at h1

set_option maxHeartbeats 400000 in
/-- Key decomposition: the unscaled path sum splits into surviving and death terms.
    For surviving paths, we use ChiAtMultiplicativity to relate factor products to χ(endpoint).
    For death paths, the factor product has norm ≤ 1. -/
private theorem path_sum_decomp (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ) (hq3 : 2 < q) :
    (2 : ℂ) ^ N * pathCharSum q chi N 2 =
    (chiAt q chi 2)⁻¹ * unitEndpointCharSumInd chi N +
    ∑ σ : Fin N → Bool,
      if IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
      then 0
      else ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k) := by
  have hne := chiAt_two_ne_zero' hq3 chi
  -- Rewrite LHS using pathCharSum definition
  have hunscaled : (2 : ℂ) ^ N * pathCharSum q chi N 2 =
      ∑ σ : Fin N → Bool,
        ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k) := by
    simp only [pathCharSum]
    have h2N : (2 : ℂ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  rw [hunscaled]
  -- Split each term based on surviving/death
  have hsplit_term : ∀ σ : Fin N → Bool,
      ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k) =
      (if h : IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
       then (chiAt q chi 2)⁻¹ * (chi h.unit : ℂ)
       else ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k)) := by
    intro σ; split_ifs with h
    · -- Surviving: use ChiAtMultiplicativity
      have hndvd := survive_not_dvd h
      have hmult := chiAt_mult_fin chi N (finDecisionExtend σ) hndvd
      -- hmult: chiAt(2) * ∏ chiAt(factor_k) = chiAt(endpoint)
      -- Factor product = chiAt(2)⁻¹ * chiAt(endpoint) = chiAt(2)⁻¹ * chi(unit)
      have : ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) ↑k) =
          (chiAt q chi 2)⁻¹ * chiAt q chi (epsWalkProdFrom 2 (finDecisionExtend σ) N) := by
        rw [eq_comm, inv_mul_eq_div, eq_div_iff hne, mul_comm]
        exact hmult
      rw [this, chiAt_of_unit' chi h]
    · rfl
  simp_rw [hsplit_term]
  -- Split into surviving + death parts
  rw [show (∑ σ : Fin N → Bool,
        if h : IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
        then (chiAt q chi 2)⁻¹ * (chi h.unit : ℂ)
        else ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k)) =
      (∑ σ : Fin N → Bool,
        if h : IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
        then (chiAt q chi 2)⁻¹ * (chi h.unit : ℂ) else 0) +
      (∑ σ : Fin N → Bool,
        if IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q) then 0
        else ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k))
    from by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro σ _
      split_ifs with h
      · simp
      · simp]
  congr 1
  -- Surviving part: factor out chiAt(2)⁻¹
  rw [← Finset.mul_sum]
  congr 1
  simp only [unitEndpointCharSumInd]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs with h
  · rfl
  · rfl

/-- Norm bound on the death error term: |∑_{death} ∏ chiAt| ≤ deathCount. -/
private theorem death_error_norm_le (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ) :
    ‖∑ σ : Fin N → Bool,
      (if IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
       then (0 : ℂ)
       else ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k))‖ ≤
    ↑(deathCount q N) := by
  calc ‖∑ σ : Fin N → Bool, _‖
      ≤ ∑ σ : Fin N → Bool, ‖(if IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
          then (0 : ℂ)
          else ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ σ : Fin N → Bool,
          (if IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q) then 0 else 1 : ℝ) := by
        apply Finset.sum_le_sum; intro σ _
        split_ifs with h
        · simp
        · calc ‖∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k)‖
              ≤ ∏ k : Fin N, ‖chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k)‖ :=
                Finset.prod_nonneg_of_norm_le _ (fun k _ => chiAt_norm_le_one q chi _)
            _ ≤ ∏ _k : Fin N, (1 : ℝ) := by
                apply Finset.prod_le_prod (fun k _ => norm_nonneg _)
                  (fun k _ => chiAt_norm_le_one q chi _)
            _ = 1 := by simp
    _ = ↑(deathCount q N) := by
        -- Convert indicator sum to card of filter
        have : ∀ σ : Fin N → Bool,
            (if IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
              then (0 : ℝ) else 1) =
            (if ¬IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
              then (1 : ℝ) else 0) := by
          intro σ; split_ifs <;> simp_all
        simp_rw [this, ← Finset.sum_boole]
        simp [deathCount]

/-- Norm bound on the unit endpoint character sum:
    |unitEndpointCharSumInd(χ, N)| ≤ 2^N * |pathCharSum| + deathCount. -/
private theorem uecsi_norm_le (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ) (hq3 : 2 < q) :
    ‖unitEndpointCharSumInd chi N‖ ≤
    (2 : ℝ) ^ N * ‖pathCharSum q chi N 2‖ + ↑(deathCount q N) := by
  have hdecomp := path_sum_decomp chi N hq3
  set E := ∑ σ : Fin N → Bool,
    if IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q) then (0 : ℂ)
    else ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k)
  have hchiAt2_ne := chiAt_two_ne_zero' hq3 chi
  have hchiAt2_norm := chiAt_two_norm_one' hq3 chi
  -- From decomp: chiAt(2)⁻¹ * uecsi + E = 2^N * pathCharSum
  -- So uecsi = chiAt(2) * (2^N * pathCharSum - E)
  have huecsi_eq : unitEndpointCharSumInd chi N =
      chiAt q chi 2 * ((2 : ℂ) ^ N * pathCharSum q chi N 2 - E) := by
    have h1 : (chiAt q chi 2)⁻¹ * unitEndpointCharSumInd chi N + E =
        (2 : ℂ) ^ N * pathCharSum q chi N 2 := hdecomp
    have h2 : (chiAt q chi 2)⁻¹ * unitEndpointCharSumInd chi N =
        (2 : ℂ) ^ N * pathCharSum q chi N 2 - E := by linarith
    rw [← h2, ← mul_assoc, mul_inv_cancel₀ hchiAt2_ne, one_mul]
  rw [huecsi_eq]
  calc ‖chiAt q chi 2 * ((2 : ℂ) ^ N * pathCharSum q chi N 2 - E)‖
      = ‖chiAt q chi 2‖ * ‖(2 : ℂ) ^ N * pathCharSum q chi N 2 - E‖ := norm_mul _ _
    _ = 1 * ‖(2 : ℂ) ^ N * pathCharSum q chi N 2 - E‖ := by rw [hchiAt2_norm]
    _ = ‖(2 : ℂ) ^ N * pathCharSum q chi N 2 - E‖ := one_mul _
    _ ≤ ‖(2 : ℂ) ^ N * pathCharSum q chi N 2‖ + ‖E‖ := by
        calc ‖(2 : ℂ) ^ N * pathCharSum q chi N 2 - E‖
            ≤ ‖(2 : ℂ) ^ N * pathCharSum q chi N 2‖ + ‖-E‖ := norm_add_le _ _
          _ = ‖(2 : ℂ) ^ N * pathCharSum q chi N 2‖ + ‖E‖ := by rw [norm_neg]
    _ ≤ (2 : ℝ) ^ N * ‖pathCharSum q chi N 2‖ + ↑(deathCount q N) := by
        gcongr
        · rw [norm_mul, Complex.norm_pow, Complex.norm_ofNat]
        · exact death_error_norm_le chi N

/-- Fourier counting identity for unitEndpointCharSumInd:
    ∑_χ conj(χ(a)) * unitEndpointCharSumInd(χ, N) = (q-1) * pathCount(a, N). -/
set_option maxHeartbeats 400000 in
private theorem fourier_counting_identity (N : ℕ) (a : (ZMod q)ˣ) :
    ∑ chi : (ZMod q)ˣ →* ℂˣ, starRingEnd ℂ (chi a : ℂ) *
      unitEndpointCharSumInd chi N =
    ↑(Fintype.card (ZMod q)ˣ) * ↑(pathCount q N a) := by
  simp only [unitEndpointCharSumInd]
  -- Swap sum order
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  -- Now for each σ, compute ∑_χ conj(χ(a)) * (dite)
  have hper_sigma : ∀ σ : Fin N → Bool,
      ∑ chi : (ZMod q)ˣ →* ℂˣ, starRingEnd ℂ (chi a : ℂ) *
        (if h : IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
         then (chi h.unit : ℂ) else 0) =
      if h : IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
      then (if h.unit = a then ↑(Fintype.card (ZMod q)ˣ) else 0)
      else 0 := by
    intro σ
    split_ifs with h
    · -- Surviving: apply hom_indicator_units
      exact hom_indicator_units a h.unit
    · -- Death: sum of conj(chi(a)) * 0 = 0
      simp
  simp_rw [hper_sigma]
  -- Collapse to pathCount
  -- Need to show: ∑_σ [dite IsUnit (if unit=a then |G| else 0) 0] = |G| * pathCount
  -- pathCount uses epsWalkProd, not epsWalkProdFrom 2
  -- Bridge: epsWalkProdFrom_two_eq
  have hcollapse : ∀ σ : Fin N → Bool,
      (if h : IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
       then (if h.unit = a then (↑(Fintype.card (ZMod q)ˣ) : ℂ) else 0)
       else 0) =
      if (epsWalkProd (finDecisionExtend σ) N : ZMod q) = ↑a
      then (↑(Fintype.card (ZMod q)ˣ) : ℂ)
      else 0 := by
    intro σ
    by_cases hu : IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
    · rw [dif_pos hu]
      by_cases heq : hu.unit = a
      · rw [if_pos heq, if_pos]
        rw [← heq, IsUnit.unit_spec, epsWalkProdFrom_two_eq]
      · rw [if_neg heq, if_neg]
        intro heq'
        apply heq
        rw [← epsWalkProdFrom_two_eq] at heq'
        exact Units.ext (by rw [IsUnit.unit_spec]; exact heq')
    · rw [dif_neg hu, if_neg]
      intro heq
      apply hu
      rw [← epsWalkProdFrom_two_eq] at heq
      rw [heq]; exact Units.isUnit a
  simp_rw [hcollapse]
  -- Now it's ∑_σ (if endpoint = a then card else 0) = card * pathCount
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- card of filter = pathCount
  simp [pathCount]

/-- Fourier lower bound on pathCount:
    (q-1) * pathCount(a) ≥ survivalCount - (q-2) * B
    when |unitEndpointCharSumInd(χ)| ≤ B for all nontrivial χ. -/
private theorem fourier_lower_bound (N : ℕ) (a : (ZMod q)ˣ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ chi : (ZMod q)ˣ →* ℂˣ, chi ≠ 1 →
      ‖unitEndpointCharSumInd chi N‖ ≤ B) :
    (↑(Fintype.card (ZMod q)ˣ) : ℝ) * ↑(pathCount q N a) ≥
    ↑(survivalCount q N) - (↑(Fintype.card (ZMod q)ˣ) - 1) * B := by
  have hfci := fourier_counting_identity N a
  -- Extract the real part
  have hreal : (↑(Fintype.card (ZMod q)ˣ) : ℝ) * ↑(pathCount q N a) =
    (∑ chi : (ZMod q)ˣ →* ℂˣ, starRingEnd ℂ (chi a : ℂ) *
      unitEndpointCharSumInd chi N).re := by
    rw [hfci]; simp
  rw [hreal]
  -- Split sum into trivial + nontrivial
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : (ZMod q)ˣ →* ℂˣ))]
  -- Evaluate trivial term
  have htrivial_term :
    starRingEnd ℂ ((1 : (ZMod q)ˣ →* ℂˣ) a : ℂ) *
      unitEndpointCharSumInd (1 : (ZMod q)ˣ →* ℂˣ) N =
    ↑(survivalCount q N : ℕ) := by
    rw [uecsi_trivial]; simp [Units.val_one]
  rw [htrivial_term]
  -- Bound the nontrivial sum
  set S := ∑ chi ∈ (Finset.univ : Finset ((ZMod q)ˣ →* ℂˣ)).erase 1,
    starRingEnd ℂ (chi a : ℂ) * unitEndpointCharSumInd chi N
  have hnt_bound : ‖S‖ ≤ (↑(Fintype.card (ZMod q)ˣ) - 1) * B := by
    calc ‖S‖
        ≤ ∑ chi ∈ (Finset.univ : Finset ((ZMod q)ˣ →* ℂˣ)).erase 1,
          ‖starRingEnd ℂ (chi a : ℂ) * unitEndpointCharSumInd chi N‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _chi ∈ (Finset.univ : Finset ((ZMod q)ˣ →* ℂˣ)).erase 1, B := by
          apply Finset.sum_le_sum; intro chi hmem
          calc ‖starRingEnd ℂ (chi a : ℂ) * unitEndpointCharSumInd chi N‖
              = ‖starRingEnd ℂ (chi a : ℂ)‖ * ‖unitEndpointCharSumInd chi N‖ :=
                norm_mul _ _
            _ ≤ 1 * B := by
                gcongr
                · rw [map_star, Complex.norm_conj]; exact (char_norm_one_of_hom chi a).le
                · exact hbound chi (Finset.ne_of_mem_erase hmem)
            _ = B := one_mul _
      _ = ↑((Finset.univ : Finset ((ZMod q)ˣ →* ℂˣ)).erase 1).card * B := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (↑(Fintype.card (ZMod q)ˣ) - 1) * B := by
          congr 1
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hom_card_eq_units]
          push_cast; omega
  -- Combine: re(survivalCount + S) ≥ survivalCount - ‖S‖
  have hre_ge : (↑↑(survivalCount q N) + S).re ≥
      ↑(survivalCount q N : ℕ) - (↑(Fintype.card (ZMod q)ˣ) - 1) * B := by
    calc (↑↑(survivalCount q N) + S).re
        = (↑↑(survivalCount q N) : ℂ).re + S.re := Complex.add_re _ _
      _ ≥ ↑(survivalCount q N : ℕ) - ‖S‖ := by
          simp only [Complex.natCast_re]
          linarith [Complex.re_le_abs S, neg_abs_le S.re]
      _ ≥ ↑(survivalCount q N : ℕ) - (↑(Fintype.card (ZMod q)ˣ) - 1) * B := by
          linarith [hnt_bound]
  exact hre_ge

/-- **TCA + PathSurvival → RandomTwoPointMC: PROVED.** -/
theorem tca_path_survival_implies_random_mc_proved :
    TCAPathSurvivalImpliesRandomMC q := by
  intro htca hps hq3
  intro a
  -- Step 1: Extract uniform bound on pathCharSum from TCA
  have hε_pos : (0 : ℝ) < 1 / (2 * ↑q) := by positivity
  have htends : ∀ chi : (ZMod q)ˣ →* ℂˣ, chi ≠ 1 →
      Filter.Tendsto (fun N => ‖pathCharSum q chi N 2‖) Filter.atTop (nhds 0) :=
    fun chi hne => pathCharSum_vanishing_of_tree_contraction htca chi hne
  obtain ⟨N₀, hN₀⟩ := uniform_bound_of_tendsto_local
    ((Finset.univ : Finset ((ZMod q)ˣ →* ℂˣ)).erase 1)
    (fun chi N => ‖pathCharSum q chi N 2‖)
    (fun chi hmem => htends chi (Finset.ne_of_mem_erase hmem))
    (1 / (2 * ↑q)) hε_pos
  -- Step 2: Extract N₁ from PathSurvival
  obtain ⟨N₁, hN₁⟩ := hps (2 * (↑q : ℝ) ^ 2) (by positivity)
  -- Step 3: Take N = max(N₀, N₁)
  set N := max N₀ N₁
  -- Step 4: Bound nontrivial characters
  have hε_bound : ∀ chi : (ZMod q)ˣ →* ℂˣ, chi ≠ 1 →
      ‖pathCharSum q chi N 2‖ < 1 / (2 * ↑q) :=
    fun chi hne => hN₀ chi (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩) N (le_max_left _ _)
  set B := (2 : ℝ) ^ N / (2 * ↑q) + ↑(deathCount q N)
  have hB_nonneg : 0 ≤ B := by positivity
  have hB_bound : ∀ chi : (ZMod q)ˣ →* ℂˣ, chi ≠ 1 →
      ‖unitEndpointCharSumInd chi N‖ ≤ B := by
    intro chi hne
    calc ‖unitEndpointCharSumInd chi N‖
        ≤ (2 : ℝ) ^ N * ‖pathCharSum q chi N 2‖ + ↑(deathCount q N) :=
          uecsi_norm_le chi N hq3
      _ ≤ (2 : ℝ) ^ N * (1 / (2 * ↑q)) + ↑(deathCount q N) := by
          gcongr; exact (hε_bound chi hne).le
      _ = B := by ring
  -- Step 5: Apply fourier_lower_bound
  have hfl := fourier_lower_bound N a B hB_nonneg hB_bound
  -- Step 6: Show S - (q-2)*B > 0
  have hSD := survival_plus_death (q := q) N
  have hPS := hN₁ N (le_max_right _ _)
  set Sv := survivalCount q N
  set D := deathCount q N
  have hqR : (0 : ℝ) < ↑q := by positivity
  have h2qR : (0 : ℝ) < 2 * ↑q := by positivity
  have hcard : Fintype.card (ZMod q)ˣ = q - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hq.out]
  have hkey : (↑Sv : ℝ) - (↑(Fintype.card (ZMod q)ˣ) - 1) * B > 0 := by
    rw [hcard]
    have h2N_eq : (2 : ℝ) ^ N = ↑Sv + ↑D := by
      have := hSD
      push_cast [Sv, D]
      linarith
    have hq1 : (↑(q - 1) : ℝ) = ↑q - 1 := by push_cast; omega
    rw [hq1]
    show (↑Sv : ℝ) - (↑q - 1 - 1) * ((↑Sv + ↑D) / (2 * ↑q) + ↑D) > 0
    rw [show (↑q : ℝ) - 1 - 1 = ↑q - 2 from by ring]
    by_cases hD : D = 0
    · -- D = 0: S = 2^N, goal simplifies
      have hS_pos : (0 : ℝ) < ↑Sv := by
        have := hSD; rw [show D = 0 from hD] at this
        have : 0 < Sv := by omega
        exact_mod_cast this
      simp only [show (D : ℝ) = 0 from by simp [show D = 0 from hD]]
      rw [add_zero, add_zero]
      have : (↑Sv : ℝ) - (↑q - 2) * (↑Sv / (2 * ↑q)) =
        ↑Sv * ((↑q + 2) / (2 * ↑q)) := by field_simp; ring
      rw [this]; positivity
    · -- D > 0: use PathSurvival
      have hD_pos : 0 < D := Nat.pos_of_ne_zero hD
      have hDR : (0 : ℝ) < ↑D := by exact_mod_cast hD_pos
      have hPS_R : 2 * (↑q : ℝ) ^ 2 * ↑D < ↑Sv := by exact_mod_cast hPS
      have hq_ge3 : (3 : ℝ) ≤ ↑q := by exact_mod_cast hq3
      -- S - (q-2) * ((S+D)/(2q) + D) = (S*(q+2) - D*((q-2)*(2q+1))) / (2q)
      have hcalc : (↑Sv : ℝ) - (↑q - 2) * ((↑Sv + ↑D) / (2 * ↑q) + ↑D) =
        (↑Sv * (↑q + 2) - ↑D * ((↑q - 2) * (2 * ↑q + 1))) / (2 * ↑q) := by
          field_simp; ring
      rw [hcalc, gt_iff_lt, div_pos_iff_of_pos_right h2qR]
      -- Need: S*(q+2) > D*((q-2)*(2q+1))
      -- From PathSurvival: S > 2q²*D
      -- (q-2)*(2q+1) = 2q²-3q-2 < 2q² for q ≥ 3
      -- So D*((q-2)*(2q+1)) < 2q²*D < S*(something)
      -- More precisely: S*(q+2) > 2q²*D*(q+2) ≥ ... (too complicated)
      -- Direct: S > 2q²D, so S*(q+2) > 2q²D*(q+2). Need 2q²(q+2) > (q-2)(2q+1).
      -- Actually: S*(q+2) - D*((q-2)*(2q+1)) > 0
      -- Use S > 2q²D:
      -- S*(q+2) > 2q²D*(q+2) = D*(2q³+4q²)
      -- D*((q-2)*(2q+1)) = D*(2q²-3q-2)
      -- Diff: D*(2q³+4q² - 2q²+3q+2) = D*(2q³+2q²+3q+2) > 0
      nlinarith
  -- Step 7: Conclude pathCount > 0
  rw [hcard] at hfl
  have hfl' := hfl
  by_contra h_zero
  push_neg at h_zero
  -- h_zero : ¬∃ N σ, ... i.e. ∀ N σ, endpoint ≠ a
  -- This means pathCount q N a = 0 for our specific N
  have hpc0 : pathCount q N a = 0 := by
    simp only [pathCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro σ _
    by_contra heq
    push_neg at heq
    exact h_zero N σ (by rw [epsWalkProdFrom_two_eq]; exact heq)
  rw [hcard, hpc0] at hfl
  simp at hfl
  linarith

end TCAPathSurvivalProof
