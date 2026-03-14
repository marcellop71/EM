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
* `fourier_bridge_identity_proved` -- KEY: treeCharSum = pathCharSum (proved by induction)
* `fairTreeCharSum_eq_pathCharSum` -- specialization to acc = 2 (unconditional)
* `pathCharSum_vanishing_of_tree_contraction` -- TCA => vanishing pathCharSum (unconditional)
* `mean_char_zero_at_diverse_step_three` -- q=3 zero-mean property
* `random_two_point_mc_landscape` -- 5-clause summary

### Open Hypotheses
* `ChiAtMultiplicativity` -- product of chiAt values = chiAt of walk endpoint
* `TreeContractionImpliesRandomMC` -- TCA => RandomTwoPointMC (needs ChiAtMultiplicativity)
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

/-- **ChiAtMultiplicativity**: The product of chiAt values along a path equals
    chi evaluated at the walk endpoint, provided the walk stays in the unit group.
    This is the bridge between `pathCharSum` (product of per-step chiAt values)
    and `reachedMultiset` (walk endpoint mod q).

    The gap: chiAt returns 1 for non-units, so the product of chiAt values is NOT
    automatically chi of the product. We need each factor to be coprime to q,
    which holds when the factors are primes distinct from q.

    Open Hypothesis. -/
def ChiAtMultiplicativity (q : ℕ) [Fact (Nat.Prime q)] [NeZero q] : Prop :=
  ∀ (chi : (ZMod q)ˣ →* ℂˣ) (acc : ℕ) (_ : 2 ≤ acc) (σ : ℕ → Bool) (N : ℕ),
    ¬(q ∣ epsWalkProdFrom acc σ N) →
    ∏ k ∈ Finset.range N,
      chiAt q chi (epsWalkFactorFrom acc σ k) =
    chiAt q chi (epsWalkProdFrom acc σ N)

/-- **TreeContractionImpliesRandomMC**: TreeContractionAtHalf implies RandomTwoPointMC.

    This requires connecting the self-consistent tree character sums (proved equal to
    pathCharSum via `tree_eq_pathCharSum`) to character orthogonality counting on the
    reached multiset. The missing step is ChiAtMultiplicativity.

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

/-- Random Two-Point MC landscape theorem.

    1. Fourier bridge base case: at depth 0, tree = pathCharSum
    2. pathCount sum bound: sum over units <= 2^N
    3. q = 3 zero-mean property for diverse steps
    4. epsWalkProdFrom generalizes epsWalkProd (bridge to existing infrastructure)
    5. reachedMultiset has exact cardinality 2^N -/
theorem random_two_point_mc_landscape :
    -- 1. Fourier bridge base case (PROVED)
    (∀ (chi : (ZMod q)ˣ →* ℂˣ) (acc : ℕ),
      treeCharSum q chi 0 acc fairCoin = pathCharSum q chi 0 acc)
    ∧
    -- 2. pathCount sum bound (PROVED)
    (∀ N, ∑ a : (ZMod q)ˣ, pathCount q N a ≤ 2 ^ N)
    ∧
    -- 3. q = 3 zero-mean (PROVED)
    (∀ (chi3 : (ZMod 3)ˣ →* ℂˣ) (a3 b3 : (ZMod 3)ˣ),
      chi3 ≠ 1 → (chi3 a3 : ℂ) ≠ (chi3 b3 : ℂ) →
      (1/2 : ℂ) * (chi3 a3 : ℂ) + (1/2 : ℂ) * (chi3 b3 : ℂ) = 0)
    ∧
    -- 4. Generalized walk bridge (PROVED)
    (∀ (σ : ℕ → Bool) (n : ℕ), epsWalkProdFrom 2 σ n = epsWalkProd σ n)
    ∧
    -- 5. Reached multiset cardinality (PROVED)
    (∀ N, Multiset.card (reachedMultiset q N) = 2 ^ N) := by
  exact ⟨fun chi acc => fourier_bridge_base chi acc,
         fun N => pathCount_sum_le N,
         fun chi3 a3 b3 h1 h2 => mean_char_zero_at_diverse_step_three chi3 h1 a3 b3 h2,
         fun σ n => epsWalkProdFrom_two_eq σ n,
         fun N => reachedMultiset_card N⟩

end Landscape
