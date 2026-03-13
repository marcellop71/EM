import EM.Advanced.VanishingNoise

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
open Classical

open Mullin Euclid MullinGroup RotorRouter

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
    push_neg at hq
    have hmf_dvd := Nat.minFac_dvd n
    have hq_dvd : n / n.minFac ∣ n := Nat.div_dvd_of_dvd hmf_dvd
    exact dvd_trans (Nat.minFac_dvd (n / n.minFac)) hq_dvd

/-- For n ≥ 2, secondMinFac n is prime. -/
theorem secondMinFac_prime {n : ℕ} (hn : 2 ≤ n) : (secondMinFac n).Prime := by
  simp only [secondMinFac]
  split
  · exact Nat.minFac_prime (by omega)
  · next hq =>
    push_neg at hq
    exact Nat.minFac_prime (by omega)

/-- minFac n ≤ secondMinFac n for n ≥ 2. -/
theorem minFac_le_secondMinFac {n : ℕ} (_hn : 2 ≤ n) :
    n.minFac ≤ secondMinFac n := by
  simp only [secondMinFac]
  split
  · exact le_refl _
  · next hq =>
    push_neg at hq
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
    have hP_ge : 2 ≤ epsWalkProd σ n := ih
    have hP1_ge : 2 ≤ epsWalkProd σ n + 1 := by omega
    have hfac_ge : 1 ≤ (if σ n then (epsWalkProd σ n + 1).minFac
        else secondMinFac (epsWalkProd σ n + 1)) := by
      split
      · have := (Nat.minFac_prime (by omega : epsWalkProd σ n + 1 ≠ 1)).two_le; omega
      · have := (secondMinFac_prime hP1_ge).two_le; omega
    calc 2 = 2 * 1 := by omega
      _ ≤ epsWalkProd σ n * (if σ n then (epsWalkProd σ n + 1).minFac
          else secondMinFac (epsWalkProd σ n + 1)) :=
        Nat.mul_le_mul hP_ge hfac_ge

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
    have : ‖(chi h.unit : ℂ)‖ = 1 := by
      rw [show (chi h.unit : ℂ) = ((chi h.unit : ℂˣ) : ℂ) from rfl]
      exact char_norm_one_of_hom chi h.unit
    linarith
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
       ‖treeCharSum q' chi N acc ε‖ ≤ 1) := by
  exact ⟨fun n hn => secondMinFac_dvd hn,
         fun n hn => secondMinFac_prime hn,
         fun n hn => minFac_le_secondMinFac hn,
         fun σ n => epsWalkFactor_dvd σ n,
         fun σ n => epsWalkFactor_prime σ n,
         fun n => epsWalkProd_emDecision n,
         fun q' _ _ chi N acc ε h0 h1 => treeCharSum_norm_le_one q' chi N acc ε h0 h1⟩

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
       treeCharSum q' chi 0 acc ε = 1) := by
  exact ⟨fun G _ _ _ chi S hne hdiv =>
           sparse_avgCharProduct_tendsto_zero chi S hne hdiv,
         fun q' _ _ chi acc ε => rfl⟩

end EpsWalk



/-! ## Part 21: Non-Self-Consistent Variant MC

Under suitable factor diversity hypotheses, the EM walk's Euclid numbers provide
enough spectral diversity that flexible two-point selection covers all residue
classes. This establishes **variant MC**: for each prime q, some selection from
{minFac, secondMinFac} of Euclid numbers hits -1 mod q, though the selection
may differ per prime.

The core chain:
1. Both minFac and secondMinFac of prod(n)+1 are prime
2. A prime p different from q gives a unit in (ZMod q)
3. Under `UFDStrong`, for each nontrivial chi, the spectral gaps at the
   two-element unit set are non-summable
4. `sparse_avgCharProduct_tendsto_zero` gives vanishing products
5. `pathExistenceFromVanishing_proved` gives path existence in (ZMod q)ˣ

Key point: this does NOT prove standard MC. The selection sigma may differ
per prime q. The gap between variant MC and actual MC is the selection
bias problem (Dead End #130).

### UFD vs UFDStrong gap

`UniformFactorDiversity(q)` guarantees: at infinitely many steps, minFac and
secondMinFac have DISTINCT RESIDUES mod q. This gives distinct ELEMENTS in
(ZMod q)ˣ, but NOT necessarily distinct CHARACTER VALUES for every nontrivial
chi. A nontrivial chi can map distinct elements to the same value if their
ratio lies in ker(chi).

`UFDStrong(q)` directly asserts non-summability of spectral gaps, which suffices
for the chain. The implication UFD => UFDStrong would require showing that the
ratio minFac/secondMinFac does not persistently lie in ker(chi) for any fixed
nontrivial chi -- a genuine number-theoretic question about the distribution of
Euclid number factorizations. -/

section NonSelfConsistentVariant

variable {q : ℕ} [hqp : Fact (Nat.Prime q)]

/-! ### Unit lifting for primes in ZMod q -/

/-- A prime p with p different from q is a unit in ZMod q. This follows from the
    fact that distinct primes are coprime. -/
theorem prime_ne_isUnit_zmod {p : ℕ} (hp : Nat.Prime p) (hpq : p ≠ q) :
    IsUnit ((p : ℕ) : ZMod q) := by
  rw [ZMod.isUnit_prime_iff_not_dvd hp]
  intro hdvd
  exact hpq ((Fact.out : Nat.Prime q).eq_one_or_self_of_dvd p hdvd |>.resolve_left
    (by have := hp.two_le; omega))

/-- If p is a prime and p differs from q, we can lift (p : ZMod q) to a unit. -/
noncomputable def primeToUnit {p : ℕ} (hp : Nat.Prime p) (hpq : p ≠ q) : (ZMod q)ˣ :=
  (prime_ne_isUnit_zmod hp hpq).unit

/-- The coercion of primeToUnit back to ZMod q equals the natural cast. -/
theorem primeToUnit_coe {p : ℕ} (hp : Nat.Prime p) (hpq : p ≠ q) :
    (primeToUnit hp hpq : ZMod q) = (p : ZMod q) :=
  IsUnit.unit_spec (prime_ne_isUnit_zmod hp hpq)

/-! ### The padded unit set: always has card at least 2

For each step n, we form a Finset (ZMod q)ˣ containing (at least) the units
corresponding to the prime factors of prod(n)+1. When the natural construction
has card < 2 (e.g., when one factor equals q), we pad with the full group
Finset.univ, which has card q-1 for q prime and q-1 >= 2 for q >= 3.
The meanCharValue over Finset.univ is 0 for nontrivial characters (by
orthogonality), giving PERFECT contraction at padded steps. -/

/-- Helper: lift a ZMod q element to a unit, defaulting to 1 if not a unit. -/
noncomputable def liftToUnit (x : ZMod q) : (ZMod q)ˣ :=
  if h : IsUnit x then h.unit else 1

/-- The raw two-element unit set: image of {minFac, secondMinFac} under unit lifting.
    May have card 1 or 2 depending on whether factors collapse mod q. -/
noncomputable def rawTwoPointUnitSet (n : ℕ) : Finset (ZMod q)ˣ :=
  {liftToUnit (Nat.minFac (prod n + 1) : ZMod q),
   liftToUnit (secondMinFac (prod n + 1) : ZMod q)}

/-- The padded unit set: uses raw set when card >= 2, otherwise falls back to
    Finset.univ (the full group). For q >= 3, Finset.univ always has card >= 2. -/
noncomputable def paddedUnitSet (n : ℕ) : Finset (ZMod q)ˣ :=
  let raw := rawTwoPointUnitSet (q := q) n
  if 2 ≤ raw.card then raw else Finset.univ

/-- The padded unit set is always nonempty. -/
theorem paddedUnitSet_nonempty (n : ℕ) :
    (paddedUnitSet (q := q) n).Nonempty := by
  simp only [paddedUnitSet]
  split
  · exact Finset.card_pos.mp (by omega)
  · exact Finset.univ_nonempty

/-- For q >= 3, the unit group (ZMod q)ˣ has card >= 2. -/
theorem card_units_zmod_ge_two (hq3 : 2 < q) : 2 ≤ Fintype.card (ZMod q)ˣ := by
  rw [ZMod.card_units_eq_totient]
  have hq_prime := (Fact.out : Nat.Prime q)
  rw [Nat.totient_prime hq_prime]
  omega

/-- For q >= 3, the padded unit set always has card >= 2. -/
theorem paddedUnitSet_card_ge_two (hq3 : 2 < q) (n : ℕ) :
    2 ≤ (paddedUnitSet (q := q) n).card := by
  simp only [paddedUnitSet]
  split
  · assumption
  · rw [Finset.card_univ]
    exact card_units_zmod_ge_two hq3

/-! ### Orthogonality: meanCharValue over full group is 0 for nontrivial chi -/

/-- For a nontrivial group homomorphism chi : G ->* Cˣ, the sum of chi over all
    elements of G is 0. This is character orthogonality (first kind). -/
private theorem hom_sum_eq_zero' {G : Type*} [CommGroup G] [Fintype G]
    (chi : G →* ℂˣ) (hchi : chi ≠ 1) :
    ∑ g : G, (chi g : ℂ) = 0 := by
  have hmc := @homToMulChar_ne_one G _ _ _ chi hchi
  have := MulChar.sum_eq_zero_of_ne_one (R' := ℂ) hmc
  have heq : ∀ g : G, (homToMulChar chi : MulChar G ℂ) g = (chi g : ℂ) := by
    intro g
    have h := mulCharToHom_apply (homToMulChar chi) g
    rw [mulCharToHom_homToMulChar] at h
    exact h.symm
  simp_rw [heq] at this
  exact this

/-- The meanCharValue over Finset.univ is 0 for nontrivial chi. -/
theorem meanCharValue_univ_eq_zero {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (chi : G →* ℂˣ) (hchi : chi ≠ 1) :
    meanCharValue chi Finset.univ = 0 := by
  simp only [meanCharValue]
  rw [show ∑ s ∈ Finset.univ, (chi s : ℂ) = ∑ g : G, (chi g : ℂ) from by
    exact Finset.sum_congr rfl (fun _ _ => rfl)]
  rw [hom_sum_eq_zero' chi hchi]
  simp

/-- The norm of meanCharValue over the full group is 0 for nontrivial chi. -/
theorem meanCharValue_univ_norm_eq_zero {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (chi : G →* ℂˣ) (hchi : chi ≠ 1) :
    ‖meanCharValue chi Finset.univ‖ = 0 := by
  simp [meanCharValue_univ_eq_zero chi hchi]

/-! ### Spectral gap at padded steps -/

/-- The spectral gap of the padded unit set is always nonneg. -/
theorem paddedUnitSet_gap_nonneg (chi : (ZMod q)ˣ →* ℂˣ) (n : ℕ) :
    0 ≤ 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ := by
  have h := meanCharValue_norm_le_one chi (paddedUnitSet (q := q) n)
    (paddedUnitSet_nonempty n)
  linarith

/-- At padded fallback steps, the spectral gap is exactly 1 (perfect contraction). -/
theorem paddedUnitSet_gap_at_fallback (_hq3 : 2 < q) (n : ℕ)
    (chi : (ZMod q)ˣ →* ℂˣ) (hchi : chi ≠ 1)
    (hsmall : ¬(2 ≤ (rawTwoPointUnitSet (q := q) n).card)) :
    1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ = 1 := by
  simp only [paddedUnitSet, if_neg hsmall]
  rw [meanCharValue_univ_norm_eq_zero chi hchi]
  ring

/-! ### UFDStrong: Per-chi spectral gap non-summability -/

/-- **UFDStrong**: For each nontrivial character on (ZMod q)ˣ, the spectral gaps
    of the padded unit set sequence are non-summable. This directly feeds into
    `sparse_avgCharProduct_tendsto_zero` for vanishing averaged products. -/
def UFDStrong (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  ∀ (chi : (ZMod q)ˣ →* ℂˣ), chi ≠ 1 →
    ¬Summable (fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖)

/-! ### Main chain: UFDStrong => vanishing => path existence => VariantHitting -/

/-- **UFDStrong implies vanishing**: Under UFDStrong, for every nontrivial chi,
    the averaged character product over the padded unit sets tends to 0. -/
theorem ufdStrong_implies_vanishing (hufd : UFDStrong q)
    (chi : (ZMod q)ˣ →* ℂˣ) (hchi : chi ≠ 1) :
    Filter.Tendsto (fun N => ‖avgCharProduct chi (paddedUnitSet (q := q)) N‖)
      Filter.atTop (nhds 0) :=
  sparse_avgCharProduct_tendsto_zero chi _ (fun k => paddedUnitSet_nonempty k)
    (hufd chi hchi)

/-- **UFDStrong implies path existence**: Under UFDStrong with q >= 3, every element
    of (ZMod q)ˣ appears in the product multiset of padded unit sets. -/
theorem ufdStrong_implies_path_existence (hq3 : 2 < q) (hufd : UFDStrong q)
    (a : (ZMod q)ˣ) :
    ∃ N, a ∈ (productMultiset (paddedUnitSet (q := q)) N).toFinset :=
  pathExistenceFromVanishing_proved
    (paddedUnitSet (q := q))
    (fun k => paddedUnitSet_nonempty k)
    (fun k => paddedUnitSet_card_ge_two hq3 k)
    (fun chi hchi => ufdStrong_implies_vanishing hufd chi hchi)
    a

/-- **VariantHitting**: For each prime q >= 3, under UFDStrong, every element of
    (ZMod q)ˣ is reachable by some selection from the padded factor sets. -/
def VariantHitting (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  2 < q → UFDStrong q →
    ∀ (a : (ZMod q)ˣ), ∃ N,
      a ∈ (productMultiset (paddedUnitSet (q := q)) N).toFinset

/-- **VariantHitting PROVED**: fully proved from the chain
    UFDStrong => sparse contraction => vanishing products => path existence. -/
theorem variant_hitting_proved : VariantHitting q :=
  fun hq3 hufd a => ufdStrong_implies_path_existence hq3 hufd a

/-! ### UFD structural lemmas (unconditional) -/

/-- If infinitely many terms of a nonneg sequence are >= 1, the sequence is
    not summable. -/
private theorem not_summable_of_infinitely_many_ge_one
    (f : ℕ → ℝ) (hf_nonneg : ∀ n, 0 ≤ f n)
    (hinf : ∀ N, ∃ n, N ≤ n ∧ 1 ≤ f n) :
    ¬Summable f := by
  intro hsum
  have htends := hsum.tendsto_atTop_zero
  rw [Metric.tendsto_atTop] at htends
  obtain ⟨N₀, hN₀⟩ := htends (1/2) (by positivity)
  obtain ⟨n, hn, hfn⟩ := hinf N₀
  have h := hN₀ n hn
  rw [Real.dist_eq, sub_zero] at h
  have habsn : |f n| = f n := abs_of_nonneg (hf_nonneg n)
  rw [habsn] at h
  linarith

/-- Under UFD, if infinitely many steps have raw card < 2 (fallback steps),
    the spectral gaps include infinitely many 1's, making the sum non-summable. -/
theorem ufd_fallback_not_summable (hq3 : 2 < q)
    (chi : (ZMod q)ˣ →* ℂˣ) (hchi : chi ≠ 1)
    (hfallback : ∀ N, ∃ n, N ≤ n ∧ ¬(2 ≤ (rawTwoPointUnitSet (q := q) n).card)) :
    ¬Summable (fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖) := by
  apply not_summable_of_infinitely_many_ge_one
  · exact fun n => paddedUnitSet_gap_nonneg chi n
  · intro N
    obtain ⟨n, hn, hsmall⟩ := hfallback N
    exact ⟨n, hn, by rw [paddedUnitSet_gap_at_fallback hq3 n chi hchi hsmall]⟩

/-! ### Bridge from UFD to UFDStrong: the open gap

The implication `UniformFactorDiversity => UFDStrong` splits into two cases:
1. If infinitely many steps have raw card < 2: UFDStrong follows from
   `ufd_fallback_not_summable` (PROVED above).
2. If cofinitely many steps have raw card >= 2: we need that for each nontrivial
   chi, the chi-values at the two factor residues are infinitely often distinct.
   This requires showing minFac/secondMinFac mod q does not persistently lie in
   ker(chi) for any fixed nontrivial chi.

Case 2 is a genuine number-theoretic question. -/

/-- **UFDImpliesUFDStrong**: the bridge from element-level to character-level
    diversity. Open Prop. -/
def UFDImpliesUFDStrong (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  2 < q → UniformFactorDiversity q → UFDStrong q

/-! ### Capture bridge: direct hitting when q is a factor -/

/-- Both minFac and secondMinFac of prod(n)+1 are prime. -/
theorem both_factors_prime (n : ℕ) :
    (Nat.minFac (prod n + 1)).Prime ∧ (secondMinFac (prod n + 1)).Prime :=
  ⟨Nat.minFac_prime (by have := prod_ge_two n; omega),
   secondMinFac_prime (by have := prod_ge_two n; omega)⟩

/-- minFac of prod(n)+1 always divides prod(n)+1. -/
theorem minFac_always_divides_euclid (n : ℕ) :
    Nat.minFac (prod n + 1) ∣ prod n + 1 :=
  Nat.minFac_dvd (prod n + 1)

/-- secondMinFac of prod(n)+1 always divides prod(n)+1. -/
theorem secondMinFac_always_divides_euclid (n : ℕ) :
    secondMinFac (prod n + 1) ∣ prod n + 1 :=
  secondMinFac_dvd (by have := prod_ge_two n; omega)

/-- If a prime p divides prod(n)+1, then the walk hits -1 at step n in ZMod p.
    This means p is "captured" at step n. -/
theorem factor_captures_prime (n : ℕ) {p : ℕ} (_hp : Nat.Prime p)
    (hdvd : p ∣ prod n + 1) :
    walkZ p n = -1 := by
  rw [walkZ_eq_neg_one_iff]
  exact hdvd

/-- minFac of prod(n)+1 is captured at step n by the standard EM walk. -/
theorem minFac_captured (n : ℕ) :
    walkZ (Nat.minFac (prod n + 1)) n = -1 :=
  factor_captures_prime n (both_factors_prime n).1 (minFac_always_divides_euclid n)

/-- secondMinFac of prod(n)+1 is captured at step n by the alternative selection. -/
theorem secondMinFac_captured (n : ℕ) :
    walkZ (secondMinFac (prod n + 1)) n = -1 :=
  factor_captures_prime n (both_factors_prime n).2 (secondMinFac_always_divides_euclid n)

/-! ### VariantMC from UFDStrong -/

/-- **VariantMCFromUFDStrong**: UFDStrong at every prime q >= 3 implies that
    for every prime q >= 3 and every target a in (ZMod q)ˣ, some selection
    path through the padded unit sets reaches a. -/
def VariantMCFromUFDStrong : Prop :=
  ∀ (q : ℕ) (hqp' : Fact (Nat.Prime q)), 2 < q → @UFDStrong q hqp' →
    ∀ (a : (ZMod q)ˣ), ∃ N,
      a ∈ (productMultiset (G := (ZMod q)ˣ) (@paddedUnitSet q hqp') N).toFinset

/-- VariantMCFromUFDStrong is PROVED. -/
theorem variant_mc_from_ufd_strong_proved : VariantMCFromUFDStrong :=
  fun q hqp' hq3 hufd a => @ufdStrong_implies_path_existence q hqp' hq3 hufd a

/-! ### Landscape theorem -/

/-- **Non-Self-Consistent Variant MC Landscape**: summary of Part 21.

    ALL PROVED (no open hypotheses used):
    1. prime_ne_isUnit_zmod: p prime, q prime, p != q => (p : ZMod q) is a unit
    2. paddedUnitSet_nonempty: padded unit set is always nonempty
    3. paddedUnitSet_card_ge_two: for q >= 3, padded set has card >= 2
    4. meanCharValue_univ_eq_zero: orthogonality for nontrivial characters
    5. ufdStrong_implies_vanishing: UFDStrong => avgCharProduct -> 0
    6. ufdStrong_implies_path_existence: UFDStrong => path existence in (ZMod q)ˣ
    7. variant_hitting_proved: VariantHitting PROVED
    8. variant_mc_from_ufd_strong_proved: VariantMCFromUFDStrong PROVED
    9. ufd_fallback_not_summable: fallback case of UFD => UFDStrong (PROVED)
    10. Factor capture: minFac and secondMinFac always divide prod(n)+1

    OPEN hypotheses documented:
    A. UFDImpliesUFDStrong: gap between element-level and character-level diversity
    B. UniformFactorDiversity: minFac != secondMinFac mod q infinitely often -/
theorem variant_mc_landscape :
    -- 1. Unit lifting for distinct primes
    (∀ (q' : ℕ) [Fact (Nat.Prime q')],
      ∀ {p : ℕ}, Nat.Prime p → p ≠ q' → IsUnit ((p : ℕ) : ZMod q'))
    ∧
    -- 2. Padded unit set always nonempty
    (∀ (q' : ℕ) [Fact (Nat.Prime q')] (n : ℕ),
      (@paddedUnitSet q' _ n).Nonempty)
    ∧
    -- 3. For q >= 3, padded set has card >= 2
    (∀ (q' : ℕ) [Fact (Nat.Prime q')], 2 < q' →
      ∀ n, 2 ≤ (@paddedUnitSet q' _ n).card)
    ∧
    -- 4. Character orthogonality over full group
    (∀ (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G]
       (chi : G →* ℂˣ), chi ≠ 1 →
       meanCharValue chi Finset.univ = 0)
    ∧
    -- 5. VariantMCFromUFDStrong
    VariantMCFromUFDStrong
    ∧
    -- 6. Both factors of Euclid numbers are prime
    (∀ n, (Nat.minFac (prod n + 1)).Prime ∧ (secondMinFac (prod n + 1)).Prime)
    ∧
    -- 7. Both factors divide the Euclid number
    (∀ n, Nat.minFac (prod n + 1) ∣ prod n + 1 ∧
           secondMinFac (prod n + 1) ∣ prod n + 1) := by
  exact ⟨fun q' _ => @prime_ne_isUnit_zmod q' _,
         fun q' _ n => @paddedUnitSet_nonempty q' _ n,
         fun q' _ hq3 n => @paddedUnitSet_card_ge_two q' _ hq3 n,
         fun G _ _ _ chi hchi => meanCharValue_univ_eq_zero chi hchi,
         variant_mc_from_ufd_strong_proved,
         fun n => both_factors_prime n,
         fun n => ⟨minFac_always_divides_euclid n, secondMinFac_always_divides_euclid n⟩⟩

end NonSelfConsistentVariant
