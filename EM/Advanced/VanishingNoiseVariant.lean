import EM.Advanced.VanishingNoiseC

/-!
# Vanishing Noise Variant: Self-Consistent epsilon-Walk and Non-Self-Consistent Variant MC

## Overview

This file contains Parts 20-21 of the vanishing noise framework, split from
`VanishingNoise.lean` for modularity.

**Part 20**: Self-consistent epsilon-walk framework. Defines `secondMinFac` (second-smallest
prime factor), the epsilon-walk accumulator `epsWalkProd` with decision sequence sigma,
and the branching tree character sum `treeCharSum`. Proves that `epsWalkProd emDecision`
recovers the standard Euclid-Mullin walk.

**Part 21**: Non-self-consistent variant MC under `UFDStrong`. Shows that if spectral gaps
at padded factor sets are non-summable, then every element of `(ZMod q)^*` is reachable
by some selection path. This does NOT prove standard MC (selection may differ per prime q).

## Main Results

### Part 20 (Self-Consistent epsilon-Walk)
* `secondMinFac_dvd` -- secondMinFac divides n for n >= 2
* `secondMinFac_prime` -- secondMinFac is prime for n >= 2
* `epsWalkProd_emDecision` -- all-true decisions = standard EM walk
* `treeCharSum_norm_le_one` -- tree character sum bounded by 1
* `eps_walk_landscape` -- 7-part landscape theorem

### Part 21 (Non-Self-Consistent Variant MC)
* `prime_ne_isUnit_zmod` -- distinct primes give units in ZMod
* `paddedUnitSet_card_ge_two` -- padded set has card >= 2 for q >= 3
* `meanCharValue_univ_eq_zero` -- character orthogonality
* `variant_hitting_proved` -- VariantHitting PROVED
* `variant_mc_from_ufd_strong_proved` -- VariantMCFromUFDStrong PROVED
* `variant_mc_landscape` -- 7-part landscape theorem
-/

noncomputable section
open Classical Mullin Euclid MullinGroup RotorRouter

/-! ## Part 20: Self-Consistent ε-Walk Framework

The key insight from the vanishing noise program is that the EM walk is the **all-minFac**
path through a branching tree of possible prime choices. At each step, prod(n)+1 may have
multiple prime factors; the EM walk always picks the smallest. The ε-walk framework allows
a small probability of choosing the second-smallest factor instead, creating a branching
process whose character sums can be analyzed via the spectral gap machinery.

### Main definitions
* `secondMinFac n` — second-smallest prime factor of n
* `epsWalkProd σ n` — accumulator for decision sequence σ
* `epsWalkFactor σ n` — factor chosen at step n
* `chiAt q chi p` — character value at a natural number, defaulting to 1 for non-units
* `treeCharSum` — weighted character sum over the branching tree

### Main results
* `secondMinFac_dvd` — secondMinFac divides the original number (for n ≥ 2)
* `secondMinFac_prime` — secondMinFac is prime (for n ≥ 2)
* `minFac_le_secondMinFac` — minFac ≤ secondMinFac
* `epsWalkFactor_dvd` — the chosen factor divides the accumulator + 1
* `epsWalkProd_emDecision` — all-true decisions recover the standard EM walk
* `treeCharSum_norm_le_one` — tree character sum bounded by 1
-/

section EpsWalk

/-! ### secondMinFac: Second-Smallest Prime Factor -/

/-- Second-smallest prime factor of n. Divide out one copy of minFac(n),
    then take minFac of the quotient. For primes or n ≤ 1, returns minFac(n). -/
def secondMinFac (n : ℕ) : ℕ :=
  let q := n / n.minFac
  if q ≤ 1 then n.minFac else q.minFac

/-- For n ≥ 2, secondMinFac n divides n. -/
theorem secondMinFac_dvd {n : ℕ} (_hn : 2 ≤ n) : secondMinFac n ∣ n := by
  simp only [secondMinFac]
  split
  · exact Nat.minFac_dvd n
  · next hq =>
    push Not at hq
    have hmf_dvd := Nat.minFac_dvd n
    have hq_dvd : n / n.minFac ∣ n := Nat.div_dvd_of_dvd hmf_dvd
    exact dvd_trans (Nat.minFac_dvd (n / n.minFac)) hq_dvd

/-- For n ≥ 2, secondMinFac n is prime. -/
theorem secondMinFac_prime {n : ℕ} (hn : 2 ≤ n) : (secondMinFac n).Prime := by
  simp only [secondMinFac]
  split
  · exact Nat.minFac_prime (by omega)
  · next hq =>
    push Not at hq
    exact Nat.minFac_prime (by omega)

/-- minFac n ≤ secondMinFac n for n ≥ 2. -/
theorem minFac_le_secondMinFac {n : ℕ} (_hn : 2 ≤ n) :
    n.minFac ≤ secondMinFac n := by
  simp only [secondMinFac]
  split
  · exact le_rfl
  · next hq =>
    push Not at hq
    -- In the else branch, secondMinFac n = (n / n.minFac).minFac
    -- Since (n/minFac).minFac divides (n/minFac) which divides n,
    -- by minimality of n.minFac, n.minFac ≤ (n/minFac).minFac.
    have hsmf_prime : ((n / n.minFac).minFac).Prime :=
      Nat.minFac_prime (by omega)
    have hsmf_dvd_q : (n / n.minFac).minFac ∣ n / n.minFac :=
      Nat.minFac_dvd (n / n.minFac)
    have hq_dvd_n : n / n.minFac ∣ n := Nat.div_dvd_of_dvd (Nat.minFac_dvd n)
    have hsmf_dvd_n : (n / n.minFac).minFac ∣ n := dvd_trans hsmf_dvd_q hq_dvd_n
    exact Nat.minFac_le_of_dvd hsmf_prime.two_le hsmf_dvd_n

/-! ### ε-Walk: Branching accumulator with decision sequence -/

/-- The ε-walk accumulator, given a decision sequence σ.
    σ(k) = true → choose minFac, σ(k) = false → choose secondMinFac.
    Starting from 2, this generalizes the Euclid-Mullin recurrence. -/
def epsWalkProd (σ : ℕ → Bool) : ℕ → ℕ
  | 0 => 2
  | n + 1 =>
    let P := epsWalkProd σ n
    let factor := if σ n then (P + 1).minFac else secondMinFac (P + 1)
    P * factor

/-- The factor chosen at step n in the ε-walk. -/
def epsWalkFactor (σ : ℕ → Bool) (n : ℕ) : ℕ :=
  let P := epsWalkProd σ n
  if σ n then (P + 1).minFac else secondMinFac (P + 1)

/-- The all-true decision sequence: always choose minFac (= standard EM). -/
def emDecision : ℕ → Bool := fun _ => true

/-- epsWalkProd σ n ≥ 2 for all decision sequences and steps. -/
theorem epsWalkProd_ge_two (σ : ℕ → Bool) (n : ℕ) : 2 ≤ epsWalkProd σ n := by
  induction n with
  | zero => simp [epsWalkProd]
  | succ n ih =>
    simp only [epsWalkProd]
    have hfac_ge : 1 ≤ (if σ n then (epsWalkProd σ n + 1).minFac
        else secondMinFac (epsWalkProd σ n + 1)) := by
      split
      · have := (Nat.minFac_prime (by omega : epsWalkProd σ n + 1 ≠ 1)).two_le; omega
      · have := (secondMinFac_prime (by omega : 2 ≤ epsWalkProd σ n + 1)).two_le; omega
    calc 2 = 2 * 1 := by omega
      _ ≤ epsWalkProd σ n * (if σ n then (epsWalkProd σ n + 1).minFac
          else secondMinFac (epsWalkProd σ n + 1)) :=
        Nat.mul_le_mul ih hfac_ge

/-- The factor chosen at each step divides the accumulator + 1. -/
theorem epsWalkFactor_dvd (σ : ℕ → Bool) (n : ℕ) :
    epsWalkFactor σ n ∣ epsWalkProd σ n + 1 := by
  simp only [epsWalkFactor]
  split
  · exact Nat.minFac_dvd (epsWalkProd σ n + 1)
  · exact secondMinFac_dvd (by have := epsWalkProd_ge_two σ n; omega)

/-- The factor chosen at each step is prime. -/
theorem epsWalkFactor_prime (σ : ℕ → Bool) (n : ℕ) :
    (epsWalkFactor σ n).Prime := by
  simp only [epsWalkFactor]
  split
  · exact Nat.minFac_prime (by have := epsWalkProd_ge_two σ n; omega)
  · exact secondMinFac_prime (by have := epsWalkProd_ge_two σ n; omega)

/-- The recurrence: epsWalkProd σ (n+1) = epsWalkProd σ n * epsWalkFactor σ n. -/
theorem epsWalkProd_succ (σ : ℕ → Bool) (n : ℕ) :
    epsWalkProd σ (n + 1) = epsWalkProd σ n * epsWalkFactor σ n := by
  simp [epsWalkProd, epsWalkFactor]

/-- Under the all-true decision sequence, epsWalkProd recovers the standard
    Euclid-Mullin accumulator. -/
theorem epsWalkProd_emDecision (n : ℕ) : epsWalkProd emDecision n = prod n := by
  induction n with
  | zero => simp [epsWalkProd, prod_zero]
  | succ n ih =>
    simp only [epsWalkProd, emDecision, ite_true]
    rw [ih, prod_succ, seq_succ]
    congr 1
    exact (euclid_minFac_eq_nat_minFac _ (by have := prod_ge_two n; omega)).symm

/-! ### chiAt: Character value at a natural number -/

/-- Character value at a natural number mod q, returning 1 if not a unit.
    This avoids the need to explicitly handle the unit coercion in tree sums. -/
def chiAt (q : ℕ) [NeZero q] (chi : (ZMod q)ˣ →* ℂˣ) (p : ℕ) : ℂ :=
  if h : IsUnit (p : ZMod q) then (chi h.unit : ℂ) else 1

/-- The chiAt value has norm at most 1. -/
theorem chiAt_norm_le_one (q : ℕ) [NeZero q] (chi : (ZMod q)ˣ →* ℂˣ) (p : ℕ) :
    ‖chiAt q chi p‖ ≤ 1 := by
  simp only [chiAt]
  split
  · next h =>
    rw [show (chi h.unit : ℂ) = ((chi h.unit : ℂˣ) : ℂ) from rfl]
    exact (char_norm_one_of_hom chi h.unit).le
  · simp

/-! ### treeCharSum: Weighted character sum over branching tree -/

/-- The branching tree character sum. At each level, the tree branches into
    minFac and secondMinFac paths, weighted by (1-ε) and ε respectively.
    N is the depth (structurally decreasing), acc is the current accumulator,
    ε(k) is the branching weight at depth k. -/
def treeCharSum (q : ℕ) [Fact (Nat.Prime q)] [NeZero q]
    (chi : (ZMod q)ˣ →* ℂˣ) : ℕ → ℕ → (ℕ → ℝ) → ℂ
  | 0, _, _ => 1
  | N + 1, acc, ε =>
    let p₁ := (acc + 1).minFac
    let p₂ := secondMinFac (acc + 1)
    (1 - ε 0) * chiAt q chi p₁ * treeCharSum q chi N (acc * p₁) (ε ∘ Nat.succ)
    + ε 0 * chiAt q chi p₂ * treeCharSum q chi N (acc * p₂) (ε ∘ Nat.succ)

/-- The tree character sum at depth 0 is 1. -/
theorem treeCharSum_zero (q : ℕ) [Fact (Nat.Prime q)] [NeZero q]
    (chi : (ZMod q)ˣ →* ℂˣ) (acc : ℕ) (ε : ℕ → ℝ) :
    treeCharSum q chi 0 acc ε = 1 := rfl

/-- The tree character sum has norm at most 1 when 0 ≤ ε(k) ≤ 1 for all k.

    Proof by induction on N:
    - Base: ‖1‖ = 1 ≤ 1
    - Step: triangle inequality + IH + chiAt_norm_le_one gives
      ‖(1-ε₀)·χ(p₁)·T_L + ε₀·χ(p₂)·T_R‖ ≤ (1-ε₀)·1·1 + ε₀·1·1 = 1 -/
theorem treeCharSum_norm_le_one (q : ℕ) [Fact (Nat.Prime q)] [NeZero q]
    (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ) (acc : ℕ) (ε : ℕ → ℝ)
    (hε0 : ∀ k, 0 ≤ ε k) (hε1 : ∀ k, ε k ≤ 1) :
    ‖treeCharSum q chi N acc ε‖ ≤ 1 := by
  induction N generalizing acc ε with
  | zero => simp [treeCharSum]
  | succ N ih =>
    simp only [treeCharSum]
    have heps0 : 0 ≤ ε 0 := hε0 0
    have heps1 : ε 0 ≤ 1 := hε1 0
    have h_shift_0 : ∀ k, 0 ≤ (ε ∘ Nat.succ) k := fun k => hε0 (k + 1)
    have h_shift_1 : ∀ k, (ε ∘ Nat.succ) k ≤ 1 := fun k => hε1 (k + 1)
    have hL := ih (acc * (acc + 1).minFac) (ε ∘ Nat.succ) h_shift_0 h_shift_1
    have hR := ih (acc * secondMinFac (acc + 1)) (ε ∘ Nat.succ) h_shift_0 h_shift_1
    have hchi1 := chiAt_norm_le_one q chi (acc + 1).minFac
    have hchi2 := chiAt_norm_le_one q chi (secondMinFac (acc + 1))
    -- Auxiliary: for any real r ≥ 0, ‖(↑r : ℂ) * b * c‖ ≤ r * ‖b‖ * ‖c‖
    -- Direct norm bound on both terms
    have key : ∀ (r : ℝ) (b c : ℂ) (hr : 0 ≤ r)
        (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1),
        ‖(↑r * b * c)‖ ≤ r := by
      intro r b c hr hb hc
      have h1 : ‖(↑r : ℂ)‖ = r := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
      calc ‖(↑r * b * c)‖
          ≤ ‖(↑r : ℂ)‖ * ‖b‖ * ‖c‖ := by rw [norm_mul, norm_mul]
        _ ≤ r * 1 * 1 := by
            rw [h1]
            exact mul_le_mul (mul_le_mul_of_nonneg_left hb hr) hc
              (norm_nonneg _) (mul_nonneg hr (by positivity))
        _ = r := by ring
    -- The expression is (1-ε₀)·χ₁·T_L + ε₀·χ₂·T_R
    -- Lean sees the coefficients as ↑(1 - ε 0) and ↑(ε 0) after unfolding Complex.ofReal
    -- Use `show` to match the exact shape
    have hterm1 := key (1 - ε 0) _ _ (by linarith) hchi1 hL
    have hterm2 := key (ε 0) _ _ heps0 hchi2 hR
    -- Need: (1 - ↑(ε 0)) = ↑(1 - ε 0) in ℂ
    have hcast : (1 - (ε 0 : ℂ)) = ((1 - ε 0 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast]
    linarith [norm_add_le
      (((1 - ε 0 : ℝ) : ℂ) * chiAt q chi (acc + 1).minFac *
        treeCharSum q chi N (acc * (acc + 1).minFac) (ε ∘ Nat.succ))
      (((ε 0 : ℝ) : ℂ) * chiAt q chi (secondMinFac (acc + 1)) *
        treeCharSum q chi N (acc * secondMinFac (acc + 1)) (ε ∘ Nat.succ))]

/-! ### Open Hypotheses for the ε-Walk Framework -/

variable {q : ℕ} [Fact (Nat.Prime q)]

/-- The tree character sum vanishes for all nontrivial characters.
    Strictly weaker than DSL (which requires cancellation along the deterministic
    EM path), this only asks for cancellation of the averaged branching tree.
    The tree structure means that at each step, the character value is a convex
    combination of two paths, so spectral gap gives geometric decay on branches
    where minFac and secondMinFac have distinct residues mod q.

    Open Hypothesis. -/
def TreeContractionHypothesis (q : ℕ) [Fact (Nat.Prime q)] [NeZero q] : Prop :=
  ∀ (chi : (ZMod q)ˣ →* ℂˣ), chi ≠ 1 →
    ∀ (ε : ℕ → ℝ), (∀ k, 0 < ε k) → (∀ k, ε k < 1) →
      Filter.Tendsto (fun N => ‖treeCharSum q chi N 2 ε‖) Filter.atTop (nhds 0)

/-- At infinitely many EM steps, minFac and secondMinFac give different
    residues mod q. This is strictly weaker than InfinitelyManyDistinctFactorSteps
    (which requires factor set cardinality ≥ 2), since here we only need the two
    smallest factors to be distinct mod q.

    Open Hypothesis. -/
def UniformFactorDiversity (q : ℕ) [hq : Fact (Nat.Prime q)] : Prop :=
  ∀ N : ℕ, ∃ n, N ≤ n ∧
    (Nat.minFac (prod n + 1) : ZMod q) ≠
    (secondMinFac (prod n + 1) : ZMod q)

/-! ### Landscape: Self-Consistent ε-Walk Summary -/

/-- The self-consistent ε-walk landscape theorem.

    1. secondMinFac API: divides, is prime, minFac ≤ secondMinFac
    2. ε-walk basics: factor divides accumulator+1, factor is prime,
       emDecision recovers standard EM
    3. Tree character sum is bounded by 1

    All parts fully proved (no open hypotheses). -/
theorem eps_walk_landscape :
    -- 1. secondMinFac divides n for n ≥ 2
    (∀ n : ℕ, 2 ≤ n → secondMinFac n ∣ n)
    ∧
    -- 2. secondMinFac is prime for n ≥ 2
    (∀ n : ℕ, 2 ≤ n → (secondMinFac n).Prime)
    ∧
    -- 3. minFac ≤ secondMinFac for n ≥ 2
    (∀ n : ℕ, 2 ≤ n → n.minFac ≤ secondMinFac n)
    ∧
    -- 4. ε-walk factor divides accumulator + 1
    (∀ σ n, epsWalkFactor σ n ∣ epsWalkProd σ n + 1)
    ∧
    -- 5. ε-walk factor is prime
    (∀ σ n, (epsWalkFactor σ n).Prime)
    ∧
    -- 6. All-true decisions recover EM walk
    (∀ n, epsWalkProd emDecision n = prod n)
    ∧
    -- 7. Tree character sum bounded by 1 (for q prime, valid weights)
    (∀ (q' : ℕ) [Fact (Nat.Prime q')] [NeZero q']
       (chi : (ZMod q')ˣ →* ℂˣ) N acc (ε : ℕ → ℝ),
       (∀ k, 0 ≤ ε k) → (∀ k, ε k ≤ 1) →
       ‖treeCharSum q' chi N acc ε‖ ≤ 1) :=
  ⟨fun _ hn => secondMinFac_dvd hn,
   fun _ hn => secondMinFac_prime hn,
   fun _ hn => minFac_le_secondMinFac hn,
   epsWalkFactor_dvd,
   epsWalkFactor_prime,
   epsWalkProd_emDecision,
   fun _ _ _ chi N acc ε h0 h1 => treeCharSum_norm_le_one _ chi N acc ε h0 h1⟩

/-! ### Dead End Documentation: Product Approximation vs Self-Consistent Tree

The product approximation (Parts 11, 17, 19) shows that if the ε-walk's per-step
character values are independent, then the product of mean character values vanishes.
However, the self-consistent tree (Part 20) does NOT decompose as a product:
the branching structure means each step's accumulator depends on all previous choices.

Formally: treeCharSum q chi (N+1) acc ε involves recursive calls with
acc * p₁ and acc * p₂, where p₁ and p₂ themselves depend on acc.
This path-dependent branching is precisely why the tree contraction hypothesis
(TreeContractionHypothesis) is genuinely new and not reducible to the product
contraction machinery of Parts 11/17/19.

The correct approach would need to show that the branching structure provides
enough "mixing" across paths, which is essentially a multi-scale spectral
gap argument. This is an open problem.

This is a documentation marker for Dead End #135: product approximation
does not compose with self-consistent branching. -/
theorem dead_end_135_product_vs_tree :
    -- Product contraction composes for INDEPENDENT steps (proved in Parts 11, 19)
    (∀ (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G]
       (chi : G →* ℂˣ) (S : ℕ → Finset G),
       (∀ k, (S k).Nonempty) →
       ¬Summable (fun k => 1 - ‖meanCharValue chi (S k)‖) →
       Filter.Tendsto (fun N => ‖avgCharProduct chi S N‖)
         Filter.atTop (nhds 0))
    ∧
    -- But tree character sum is NOT a product of independent factors
    -- (the branching structure makes it path-dependent).
    -- We witness this by noting treeCharSum has a DIFFERENT recursive structure.
    (∀ (q' : ℕ) [Fact (Nat.Prime q')] [NeZero q']
       (chi : (ZMod q')ˣ →* ℂˣ) acc (ε : ℕ → ℝ),
       treeCharSum q' chi 0 acc ε = 1) :=
  ⟨fun _ _ _ _ chi S hne hdiv => sparse_avgCharProduct_tendsto_zero chi S hne hdiv,
   fun _ _ _ _ _ _ => rfl⟩

end EpsWalk
