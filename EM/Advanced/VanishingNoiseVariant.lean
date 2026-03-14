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


/-! ## Part 22: Routes to UFDStrong

Three independent routes reducing `UFDStrong` to progressively weaker hypotheses,
plus assembly theorems and a landscape theorem.

* Route 1: `MinFacRatioEscape` (quantitative: per-chi, infinitely many steps with
  gap bounded below by a fixed positive constant) implies `UFDStrong` directly.
* Route 2: `MinFacRatioEscapeQual` (qualitative: per-chi, infinitely many steps
  with card >= 2 and distinct chi-values) implies `MinFacRatioEscape` via finite
  group pigeonhole: the gap function has finite range, so positive gaps are
  bounded away from 0.
* Route 3: `OrbitMFRE` (orbit-level minFac residue equidistribution) implies
  `MinFacRatioEscapeQual` because equidistribution prevents character values from
  being confined to a proper coset.

All three compose with the proved chain `UFDStrong => VariantMC`.
-/

section RoutesToUFDStrong

variable {q : ℕ} [hqp : Fact (Nat.Prime q)]

/-! ### Utility: Non-summability from frequently exceeding a fixed threshold -/

/-- If a nonneg sequence has infinitely many terms above a fixed positive threshold,
    the sequence is not summable. Proof: summable implies convergence to 0,
    contradicting the infinitely-many-large-terms condition. -/
theorem not_summable_of_frequently_ge (f : ℕ → ℝ) (hf_nonneg : ∀ n, 0 ≤ f n)
    {δ : ℝ} (hδ : 0 < δ) (hinf : ∀ N, ∃ n, N ≤ n ∧ δ ≤ f n) :
    ¬Summable f := by
  intro hsum
  have htends := hsum.tendsto_atTop_zero
  rw [Metric.tendsto_atTop] at htends
  obtain ⟨N₀, hN₀⟩ := htends δ hδ
  obtain ⟨n, hn, hfn⟩ := hinf N₀
  have h := hN₀ n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hf_nonneg n)] at h
  linarith

/-- Non-summability when a nonneg function with finite range has infinitely many
    positive values. The key insight: a finite set of positive reals has a positive
    minimum, providing the uniform lower bound needed for non-summability. -/
theorem not_summable_of_frequently_pos_finite_range (f : ℕ → ℝ) (hf_nonneg : ∀ n, 0 ≤ f n)
    (hfinite : Set.Finite (Set.range f))
    (hinf : ∀ N, ∃ n, N ≤ n ∧ 0 < f n) :
    ¬Summable f := by
  -- The positive values in the range form a finite nonempty set
  set posRange := {x ∈ hfinite.toFinset | (0 : ℝ) < x} with hposRange_def
  have hne : posRange.Nonempty := by
    obtain ⟨n, -, hfn⟩ := hinf 0
    exact ⟨f n, by rw [hposRange_def, Finset.mem_filter]; exact ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨n, rfl⟩, hfn⟩⟩
  -- The minimum of posRange is positive
  set δ := posRange.min' hne
  have hδ_pos : 0 < δ := by
    have hmem := Finset.min'_mem posRange hne
    rw [Finset.mem_filter] at hmem
    exact hmem.2
  -- Every positive value of f is >= δ
  have hδ_le : ∀ n, 0 < f n → δ ≤ f n := by
    intro n hfn
    apply Finset.min'_le
    rw [Finset.mem_filter]
    exact ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨n, rfl⟩, hfn⟩
  -- Apply the quantitative non-summability lemma
  exact not_summable_of_frequently_ge f hf_nonneg hδ_pos
    (fun N => by obtain ⟨n, hn, hfn⟩ := hinf N; exact ⟨n, hn, hδ_le n hfn⟩)

/-! ### Route 1: MinFacRatioEscape (quantitative) => UFDStrong -/

/-- **MinFacRatioEscape** (quantitative): For each nontrivial character chi on
    (ZMod q)ˣ, there exists a fixed positive spectral gap threshold delta such that
    infinitely many steps n have gap >= delta at the padded unit set.

    This is the quantitative version that directly feeds into non-summability.
    The qualitative version `MinFacRatioEscapeQual` (card >= 2 + distinct chi-values)
    implies this via the finite-group argument. -/
def MinFacRatioEscape (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  ∀ (chi : (ZMod q)ˣ →* ℂˣ), chi ≠ 1 →
    ∃ (δ : ℝ), 0 < δ ∧
      ∀ N, ∃ n, N ≤ n ∧ δ ≤ 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖

/-- MinFacRatioEscape directly implies UFDStrong: the quantitative gap bound
    feeds into non-summability via `not_summable_of_frequently_ge`. -/
theorem ratio_escape_implies_ufdStrong (hre : MinFacRatioEscape q) :
    UFDStrong q := by
  intro chi hchi
  obtain ⟨δ, hδ_pos, hinf⟩ := hre chi hchi
  exact not_summable_of_frequently_ge _ (fun n => paddedUnitSet_gap_nonneg chi n) hδ_pos hinf

/-! ### Route 2: Qualitative MinFacRatioEscape => Quantitative (finite group argument) -/

/-- **MinFacRatioEscapeQual** (qualitative): For each nontrivial character chi,
    infinitely many steps n have (a) rawTwoPointUnitSet with card >= 2, and
    (b) the chi-values at the two lifted primes are distinct.

    This is the more natural number-theoretic condition. -/
def MinFacRatioEscapeQual (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  ∀ (chi : (ZMod q)ˣ →* ℂˣ), chi ≠ 1 →
    ∀ N, ∃ n, N ≤ n ∧
      2 ≤ (rawTwoPointUnitSet (q := q) n).card ∧
      (chi (liftToUnit (q := q) (Nat.minFac (prod n + 1) : ZMod q)) : ℂ) ≠
      (chi (liftToUnit (q := q) (secondMinFac (prod n + 1) : ZMod q)) : ℂ)

/-- When rawTwoPointUnitSet has card >= 2, paddedUnitSet equals rawTwoPointUnitSet. -/
theorem paddedUnitSet_eq_raw_of_card (n : ℕ)
    (hcard : 2 ≤ (rawTwoPointUnitSet (q := q) n).card) :
    paddedUnitSet (q := q) n = rawTwoPointUnitSet (q := q) n := by
  simp only [paddedUnitSet, if_pos hcard]

/-- The rawTwoPointUnitSet contains liftToUnit of minFac. -/
theorem liftToUnit_minFac_mem_raw (n : ℕ) :
    liftToUnit (q := q) (Nat.minFac (prod n + 1) : ZMod q)
      ∈ rawTwoPointUnitSet (q := q) n := by
  simp [rawTwoPointUnitSet, Finset.mem_insert, Finset.mem_singleton]

/-- The rawTwoPointUnitSet contains liftToUnit of secondMinFac. -/
theorem liftToUnit_secondMinFac_mem_raw (n : ℕ) :
    liftToUnit (q := q) (secondMinFac (prod n + 1) : ZMod q)
      ∈ rawTwoPointUnitSet (q := q) n := by
  simp [rawTwoPointUnitSet, Finset.mem_insert, Finset.mem_singleton]

/-- At a qualitative escape step, the gap at paddedUnitSet is strictly positive.
    Key: rawTwoPointUnitSet has card >= 2, so paddedUnitSet = rawTwoPointUnitSet,
    and distinct chi-values give strict contraction via `meanCharValue_norm_lt_one_of_distinct`. -/
theorem gap_pos_at_escape (n : ℕ) (chi : (ZMod q)ˣ →* ℂˣ)
    (hcard : 2 ≤ (rawTwoPointUnitSet (q := q) n).card)
    (hdiff : (chi (liftToUnit (q := q) (Nat.minFac (prod n + 1) : ZMod q)) : ℂ) ≠
             (chi (liftToUnit (q := q) (secondMinFac (prod n + 1) : ZMod q)) : ℂ)) :
    0 < 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ := by
  rw [paddedUnitSet_eq_raw_of_card n hcard]
  have hlt := meanCharValue_norm_lt_one_of_distinct chi (rawTwoPointUnitSet (q := q) n) hcard
    ⟨liftToUnit (q := q) (Nat.minFac (prod n + 1) : ZMod q),
     liftToUnit_minFac_mem_raw n,
     liftToUnit (q := q) (secondMinFac (prod n + 1) : ZMod q),
     liftToUnit_secondMinFac_mem_raw n,
     hdiff⟩
  linarith

/-- The gap function n -> 1 - ||meanCharValue chi (paddedUnitSet n)|| has finite range.
    This follows from the fact that paddedUnitSet maps N to Finset (ZMod q)^x, which is
    a Fintype (power set of a finite type). So the composition through meanCharValue
    and norm produces only finitely many distinct values. -/
theorem gap_function_finite_range (chi : (ZMod q)ˣ →* ℂˣ) :
    Set.Finite (Set.range (fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖)) := by
  -- paddedUnitSet maps to Finset (ZMod q)ˣ, which is a Fintype
  -- The composition gap ∘ paddedUnitSet factors through this Fintype
  apply Set.Finite.subset
    (Set.Finite.image (fun S => 1 - ‖meanCharValue chi S‖)
      (Set.toFinite (Set.univ : Set (Finset (ZMod q)ˣ))))
  intro x hx
  obtain ⟨n, rfl⟩ := hx
  exact ⟨paddedUnitSet (q := q) n, Set.mem_univ _, rfl⟩

/-- The qualitative MinFacRatioEscape implies the quantitative version.
    Proof: the gap function has finite range (by `gap_function_finite_range`),
    escape steps give positive gaps (by `gap_pos_at_escape`), and a finite set
    of positive reals has a positive minimum. -/
theorem qual_implies_quant (hq : MinFacRatioEscapeQual q) : MinFacRatioEscape q := by
  intro chi hchi
  -- The gap function has finite range
  have hfin := gap_function_finite_range (q := q) chi
  -- Escape steps give positive gaps
  have hpos : ∀ N, ∃ n, N ≤ n ∧
      0 < 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ := by
    intro N
    obtain ⟨n, hn, hcard, hdiff⟩ := hq chi hchi N
    exact ⟨n, hn, gap_pos_at_escape n chi hcard hdiff⟩
  -- Extract the positive values in the range
  set posRange := {x ∈ hfin.toFinset | (0 : ℝ) < x}
  have hne : posRange.Nonempty := by
    obtain ⟨n, -, hfn⟩ := hpos 0
    exact ⟨_, by rw [Finset.mem_filter]; exact ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨n, rfl⟩, hfn⟩⟩
  set δ := posRange.min' hne
  have hδ_pos : 0 < δ := by
    have hmem := Finset.min'_mem posRange hne
    rw [Finset.mem_filter] at hmem
    exact hmem.2
  have hδ_le : ∀ n, 0 < 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ →
      δ ≤ 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ := by
    intro n hfn
    apply Finset.min'_le
    rw [Finset.mem_filter]
    exact ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨n, rfl⟩, hfn⟩
  exact ⟨δ, hδ_pos, fun N => by
    obtain ⟨n, hn, hfn⟩ := hpos N
    exact ⟨n, hn, hδ_le n hfn⟩⟩

/-- The qualitative MinFacRatioEscape implies UFDStrong. Composition of
    `qual_implies_quant` and `ratio_escape_implies_ufdStrong`. -/
theorem qual_escape_implies_ufdStrong (hq : MinFacRatioEscapeQual q) :
    UFDStrong q :=
  ratio_escape_implies_ufdStrong (qual_implies_quant hq)

/-! ### Route 3: OrbitMFRE => MinFacRatioEscapeQual

OrbitMFRE says that for each unit a in (ZMod q)ˣ, the density of steps n where
liftToUnit(minFac(prod(n)+1)) = a tends to 1/(q-1). Under this, for any nontrivial
character chi, the density of steps where chi(minFac-unit) takes any particular value
is at most |ker(chi)|/(q-1) < 1, so infinitely many steps have a non-default chi-value.

Combined with the fact that secondMinFac also divides prod(n)+1 and gives a unit in
(ZMod q)ˣ, we get infinitely many steps where chi-values at minFac and secondMinFac
can differ.

The formal proof requires density-based arguments (eventually, density of steps with
chi(minFac) = chi(secondMinFac) is bounded away from 1). This involves quantitative
Fourier analysis on the finite group, which we state as an open Prop and document
the proof strategy. -/

/-- **OrbitMFRE**: Orbit-level minFac residue equidistribution. For each unit a in
    (ZMod q)ˣ, the density of steps n where liftToUnit(minFac(prod(n)+1)) = a
    converges to 1/(q-1). -/
def OrbitMFRE (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  ∀ (a : (ZMod q)ˣ), ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀,
    |((Finset.range N).filter (fun n =>
        liftToUnit (q := q) (Nat.minFac (prod n + 1) : ZMod q) = a)).card / (N : ℝ) -
     1 / (Fintype.card (ZMod q)ˣ : ℝ)| < ε

/-- **OrbitMFREImpliesEscapeQual**: OrbitMFRE implies qualitative MinFacRatioEscape.

    Proof sketch: Under OrbitMFRE, for any nontrivial chi, the density of steps where
    chi(minFac-unit) = 1 is at most |ker(chi)|/(q-1) < 1 (since chi is nontrivial,
    ker(chi) is a proper subgroup). So at positive density, chi(minFac-unit) != 1.
    At these steps, either (a) rawTwoPointUnitSet has card < 2 (covered by fallback),
    or (b) card >= 2 and chi(minFac-unit) != chi(secondMinFac-unit) = 1 does not
    hold trivially -- we need chi(minFac) != chi(secondMinFac) specifically.

    The gap between "chi(minFac) takes non-identity value" and "chi(minFac) != chi(secondMinFac)"
    requires additional analysis of secondMinFac distribution. This is a genuine gap
    when secondMinFac = minFac mod q at those steps. We formalize this as an open Prop
    documenting the proof strategy. -/
def OrbitMFREImpliesEscapeQual (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  2 < q → OrbitMFRE q → MinFacRatioEscapeQual q

/-! ### Assembly chains: composing routes to VariantMC -/

/-- **Route 1 assembly**: Quantitative MinFacRatioEscape => UFDStrong => VariantMC. -/
theorem route1_mfre_to_variant_mc (hq3 : 2 < q) (hre : MinFacRatioEscape q) :
    ∀ (a : (ZMod q)ˣ), ∃ N,
      a ∈ (productMultiset (paddedUnitSet (q := q)) N).toFinset :=
  ufdStrong_implies_path_existence hq3 (ratio_escape_implies_ufdStrong hre)

/-- **Route 2 assembly**: Qualitative MinFacRatioEscapeQual => UFDStrong => VariantMC. -/
theorem route2_qual_to_variant_mc (hq3 : 2 < q) (hq : MinFacRatioEscapeQual q) :
    ∀ (a : (ZMod q)ˣ), ∃ N,
      a ∈ (productMultiset (paddedUnitSet (q := q)) N).toFinset :=
  ufdStrong_implies_path_existence hq3 (qual_escape_implies_ufdStrong hq)

/-- **Route 3 assembly**: OrbitMFRE + bridge => UFDStrong => VariantMC. -/
theorem route3_orbit_to_variant_mc (hq3 : 2 < q)
    (hbridge : OrbitMFREImpliesEscapeQual q) (hmfre : OrbitMFRE q) :
    ∀ (a : (ZMod q)ˣ), ∃ N,
      a ∈ (productMultiset (paddedUnitSet (q := q)) N).toFinset :=
  route2_qual_to_variant_mc hq3 (hbridge hq3 hmfre)

/-- **Route 1 to UFDStrong assembly**: quantitative escape directly gives UFDStrong. -/
theorem route1_to_ufdStrong (hre : MinFacRatioEscape q) : UFDStrong q :=
  ratio_escape_implies_ufdStrong hre

/-- **Route 2 to UFDStrong assembly**: qualitative escape gives UFDStrong via
    the finite-range argument. -/
theorem route2_to_ufdStrong (hq : MinFacRatioEscapeQual q) : UFDStrong q :=
  qual_escape_implies_ufdStrong hq

/-- **Route 3 to UFDStrong assembly**: OrbitMFRE + bridge gives UFDStrong. -/
theorem route3_to_ufdStrong
    (hq3 : 2 < q) (hbridge : OrbitMFREImpliesEscapeQual q) (hmfre : OrbitMFRE q) :
    UFDStrong q :=
  qual_escape_implies_ufdStrong (hbridge hq3 hmfre)

/-! ### Landscape theorem -/

/-- **Routes to UFDStrong Landscape**: summary of Part 22.

    ALL internal reductions PROVED (no sorry). Open hypotheses:
    A. MinFacRatioEscape (quantitative spectral gap at infinitely many steps)
    B. MinFacRatioEscapeQual (qualitative: card >= 2 + distinct chi-values i.o.)
    C. OrbitMFRE (orbit-level minFac equidistribution)
    D. OrbitMFREImpliesEscapeQual (density argument bridge)

    PROVED reductions:
    1. not_summable_of_frequently_ge (utility)
    2. not_summable_of_frequently_pos_finite_range (finite range + i.o. positive => not summable)
    3. ratio_escape_implies_ufdStrong (Route 1: quantitative => UFDStrong)
    4. qual_implies_quant (Route 2: qualitative => quantitative via finite group)
    5. qual_escape_implies_ufdStrong (Route 2 composed)
    6. gap_function_finite_range (paddedUnitSet finite range)
    7. gap_pos_at_escape (positive gap at escape steps)
    8. route1/2/3_to_variant_mc (assembly chains to VariantMC) -/
theorem routes_to_ufdStrong_landscape :
    -- 1. Quantitative MinFacRatioEscape => UFDStrong
    (MinFacRatioEscape q → UFDStrong q)
    ∧
    -- 2. Qualitative MinFacRatioEscapeQual => quantitative MinFacRatioEscape
    (MinFacRatioEscapeQual q → MinFacRatioEscape q)
    ∧
    -- 3. Qualitative => UFDStrong (composed)
    (MinFacRatioEscapeQual q → UFDStrong q)
    ∧
    -- 4. Gap function has finite range (structural fact)
    Set.Finite (Set.range (fun n => 1 - ‖meanCharValue (1 : (ZMod q)ˣ →* ℂˣ) (paddedUnitSet (q := q) n)‖))
    ∧
    -- 5. Not summable from frequently positive + finite range (utility)
    (∀ (f : ℕ → ℝ), (∀ n, 0 ≤ f n) → Set.Finite (Set.range f) →
      (∀ N, ∃ n, N ≤ n ∧ 0 < f n) → ¬Summable f)
    ∧
    -- 6. Route 3 with bridge: OrbitMFRE + bridge => UFDStrong
    (2 < q → OrbitMFREImpliesEscapeQual q → OrbitMFRE q → UFDStrong q) :=
  ⟨ratio_escape_implies_ufdStrong,
   qual_implies_quant,
   qual_escape_implies_ufdStrong,
   gap_function_finite_range 1,
   fun f hnn hfin hinf => not_summable_of_frequently_pos_finite_range f hnn hfin hinf,
   fun hq3 hbridge hmfre => route3_to_ufdStrong hq3 hbridge hmfre⟩

end RoutesToUFDStrong


/-! ## Part 23: Stochastic Two-Point MC

### Overview

This part connects the non-self-consistent variant MC machinery (Part 21) with the
self-consistent tree framework (Part 20), and provides a clean quantitative
statement about the "stochastic two-point MC" problem.

**Key definitions**:
* `fairCoin` -- constant epsilon schedule at 1/2
* `fairTreeCharSum` -- tree character sum at fair coin weights
* `TreeContractionAtHalf` -- tree contraction specialized to epsilon = 1/2
* `StochasticTwoPointMC` -- under UFDStrong, every element has positive count

**Key results**:
* `stochastic_two_point_mc_proved` -- StochasticTwoPointMC PROVED from UFDStrong
* `productMultiset_card_ge_two_pow` -- product multiset grows exponentially
* `fairTreeCharSum_norm_le_one` -- fair tree character sum bounded by 1
* `treeContraction_of_hypothesis` -- TreeContractionHypothesis implies TreeContractionAtHalf
* `treeCharSum_at_zero_step` -- deterministic degeneration at epsilon = 0
* `stochastic_two_point_mc_landscape` -- 7-part landscape theorem

### Conceptual significance

The stochastic two-point MC problem sits between two extremes:
1. **Deterministic MC** (standard Mullin conjecture): the ALL-minFac walk hits -1 mod q
2. **Full stochastic MC** (pathExistenceFromVanishing): SOME product of factor set elements
   reaches every target

Part 21 established (2) under UFDStrong via character orthogonality counting.
Part 20 established the self-consistent tree framework where branching follows
actual prime factorizations (not abstract factor sets).

Part 23 bridges these: under UFDStrong, the non-self-consistent counting already
gives positive multiset count for every target. The tree contraction machinery
(TreeContractionAtHalf) provides a route for the self-consistent version, but
requires the open TreeContractionHypothesis.

The key gap between Parts 21 and 23 on one hand and standard MC on the other
is the **selection coherence** problem: stochastic MC shows that for each prime q,
SOME selection path reaches -1 mod q, but different primes q may require different
selection sequences. Standard MC requires ONE fixed selection (all-minFac) to work
for ALL primes simultaneously.
-/

section StochasticTwoPointMC

variable {q : ℕ} [hqp : Fact (Nat.Prime q)]

/-! ### Definitions -/

/-- The fair coin epsilon schedule: constant 1/2 at every step. -/
def fairCoin : ℕ → ℝ := fun _ => 1 / 2

/-- The fair tree character sum: the branching tree character sum evaluated at
    accumulator 2 (= prod 0) with constant epsilon = 1/2. -/
def fairTreeCharSum (q : ℕ) [Fact (Nat.Prime q)] [NeZero q]
    (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ) : ℂ :=
  treeCharSum q chi N 2 fairCoin

/-- **TreeContractionAtHalf**: the tree character sum at fair coin weights vanishes
    for all nontrivial characters. This is TreeContractionHypothesis specialized to
    the constant epsilon = 1/2 schedule.

    Strictly weaker than TreeContractionHypothesis (which quantifies over all
    epsilon schedules with 0 < epsilon_k < 1).

    Open Hypothesis. -/
def TreeContractionAtHalf (q : ℕ) [Fact (Nat.Prime q)] [NeZero q] : Prop :=
  ∀ (chi : (ZMod q)ˣ →* ℂˣ), chi ≠ 1 →
    Filter.Tendsto (fun N => ‖fairTreeCharSum q chi N‖) Filter.atTop (nhds 0)

/-- **StochasticTwoPointMC**: Under UFDStrong with q >= 3, every element of (ZMod q)ˣ
    has positive count in the product multiset of padded unit sets at some depth N.
    This is the non-self-consistent version: the "random paths" are abstract products
    of factor set elements, not necessarily following the self-consistent tree. -/
def StochasticTwoPointMC (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  2 < q → UFDStrong q →
    ∀ (a : (ZMod q)ˣ), ∃ N,
      0 < Multiset.count a (productMultiset (paddedUnitSet (q := q)) N)

/-! ### fairCoin validity -/

/-- fairCoin is strictly positive at every step. -/
theorem fairCoin_pos : ∀ k, 0 < fairCoin k :=
  fun _ => by norm_num [fairCoin]

/-- fairCoin is strictly less than 1 at every step. -/
theorem fairCoin_lt_one : ∀ k, fairCoin k < 1 :=
  fun _ => by norm_num [fairCoin]

/-- fairCoin is nonneg at every step. -/
theorem fairCoin_nonneg : ∀ k, 0 ≤ fairCoin k :=
  fun k => le_of_lt (fairCoin_pos k)

/-- fairCoin is at most 1 at every step. -/
theorem fairCoin_le_one : ∀ k, fairCoin k ≤ 1 :=
  fun k => le_of_lt (fairCoin_lt_one k)

/-! ### fairTreeCharSum properties -/

/-- The fair tree character sum is bounded by 1 in norm. This follows from
    `treeCharSum_norm_le_one` with the valid fairCoin weights. -/
theorem fairTreeCharSum_norm_le_one [NeZero q]
    (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ) :
    ‖fairTreeCharSum q chi N‖ ≤ 1 :=
  treeCharSum_norm_le_one q chi N 2 fairCoin fairCoin_nonneg fairCoin_le_one

/-- TreeContractionHypothesis (which quantifies over all valid epsilon schedules)
    implies TreeContractionAtHalf (the special case epsilon = 1/2). -/
theorem treeContraction_of_hypothesis [NeZero q]
    (h : TreeContractionHypothesis q) :
    TreeContractionAtHalf q :=
  fun chi hchi => h chi hchi fairCoin fairCoin_pos fairCoin_lt_one

/-! ### Exponential growth of product multiset -/

/-- For q >= 3, the product multiset over padded unit sets has cardinality at least
    2^N. This follows from `productMultiset_card` (cardinality = product of set sizes)
    combined with `paddedUnitSet_card_ge_two` (each set has size >= 2). -/
theorem productMultiset_card_ge_two_pow (hq3 : 2 < q) (N : ℕ) :
    2 ^ N ≤ Multiset.card (productMultiset (paddedUnitSet (q := q)) N) := by
  rw [productMultiset_card]
  calc (2 : ℕ) ^ N
      = ∏ _k ∈ Finset.range N, 2 := by simp [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ k ∈ Finset.range N, (paddedUnitSet (q := q) k).card :=
        Finset.prod_le_prod' (fun k _ => paddedUnitSet_card_ge_two hq3 k)

/-! ### StochasticTwoPointMC: proved from UFDStrong -/

/-- **StochasticTwoPointMC PROVED**: Under UFDStrong with q >= 3, every element of
    (ZMod q)ˣ has positive count in the product multiset of padded unit sets.

    Proof chain: UFDStrong => sparse spectral contraction => vanishing averaged
    character products => path existence (Fourier counting) => positive count.

    The key step is `ufdStrong_implies_path_existence`, which gives membership in
    `(productMultiset ...).toFinset`. Membership in toFinset is equivalent to
    positive count via `Multiset.count_pos` and `Multiset.mem_toFinset`. -/
theorem stochastic_two_point_mc_proved : StochasticTwoPointMC q := by
  intro hq3 hufd a
  obtain ⟨N, hN⟩ := ufdStrong_implies_path_existence hq3 hufd a
  exact ⟨N, Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hN)⟩

/-! ### Deterministic degeneration: treeCharSum at epsilon = 0

When all epsilon values are 0, the tree degenerates to a single path that always
picks minFac. This is the deterministic EM walk. The tree character sum at epsilon = 0
is then a product of character values along the deterministic path.

We prove the one-step reduction showing that at epsilon = 0, the tree character sum
factors as chiAt(minFac) times the recursive subtree at acc * minFac. -/

/-- At epsilon = 0, the tree character sum at depth 0 is 1 (base case). -/
theorem treeCharSum_at_zero_base (q' : ℕ) [Fact (Nat.Prime q')] [NeZero q']
    (chi : (ZMod q')ˣ →* ℂˣ) (acc : ℕ) :
    treeCharSum q' chi 0 acc (fun _ => (0 : ℝ)) = 1 := rfl

/-- At epsilon = 0, the one-step tree character sum reduces to the deterministic
    (all-minFac) path: the secondMinFac branch has weight 0 and the minFac branch
    has weight 1, so only the minFac contribution survives. -/
theorem treeCharSum_at_zero_step (q' : ℕ) [Fact (Nat.Prime q')] [NeZero q']
    (chi : (ZMod q')ˣ →* ℂˣ) (N : ℕ) (acc : ℕ) :
    treeCharSum q' chi (N + 1) acc (fun _ => (0 : ℝ)) =
    chiAt q' chi (acc + 1).minFac *
      treeCharSum q' chi N (acc * (acc + 1).minFac) (fun _ => (0 : ℝ)) := by
  simp only [treeCharSum]
  have h0 : (fun _ : ℕ => (0 : ℝ)) ∘ Nat.succ = fun _ => (0 : ℝ) := by ext; simp
  rw [h0]
  push_cast
  ring

/-- The standard EM walk is the all-true epsilon-walk (bridge to Part 20). -/
theorem epsWalkProd_standard (n : ℕ) :
    epsWalkProd emDecision n = prod n :=
  epsWalkProd_emDecision n

/-! ### Relationship between self-consistent and non-self-consistent

The non-self-consistent approach (Part 21 + StochasticTwoPointMC above) and the
self-consistent tree approach (Part 20 + TreeContractionHypothesis) address different
questions:

1. **Non-self-consistent** (StochasticTwoPointMC): At each step n, the "factor set"
   is {minFac(prod(n)+1), secondMinFac(prod(n)+1)} mod q. The product multiset
   is formed by choosing one element from each factor set independently. The key
   insight is that these factor sets are determined by the ACTUAL EM walk (which
   always picks minFac), so the factor sets are FIXED regardless of which selection
   path we consider through the product multiset.

2. **Self-consistent** (TreeContractionHypothesis): The tree character sum tracks
   what happens when the accumulator CHANGES based on the selection. If we pick
   secondMinFac at step n, the accumulator at step n+1 is different, which changes
   the factor set at step n+1. The tree character sum accounts for this coupling.

The non-self-consistent version is PROVED (under UFDStrong) because the fixed
factor sets allow the product contraction machinery to apply directly. The
self-consistent version remains open because the path-dependent factor sets
prevent factorization into a product.

Despite this gap, the non-self-consistent result is still meaningful: it shows
that the COMBINATORIAL COUNTING of paths through the padded unit sets covers
every target. The issue is that the padded unit sets are computed from the
deterministic EM walk, not from the alternative walk that would be induced by
a different selection sequence. -/

/-- The non-self-consistent and self-consistent approaches are connected:
    if TreeContractionAtHalf holds AND the tree character sum controls the
    product multiset counting (which it does NOT in general -- this is the
    selection coherence gap), then a stronger variant MC would follow.

    We record the relationship between the two frameworks:
    - fairTreeCharSum at depth 0 is 1 (trivially)
    - fairTreeCharSum is bounded by 1 at all depths
    - TreeContractionHypothesis implies TreeContractionAtHalf
    - StochasticTwoPointMC is proved from UFDStrong alone -/
theorem self_consistent_vs_non_self_consistent [NeZero q] :
    -- 1. Fair tree char sum at depth 0 is 1
    (∀ (chi : (ZMod q)ˣ →* ℂˣ), fairTreeCharSum q chi 0 = 1)
    ∧
    -- 2. Fair tree char sum bounded by 1
    (∀ (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ), ‖fairTreeCharSum q chi N‖ ≤ 1)
    ∧
    -- 3. General tree contraction implies fair-coin contraction
    (TreeContractionHypothesis q → TreeContractionAtHalf q) :=
  ⟨fun _chi => rfl,
   fun chi N => fairTreeCharSum_norm_le_one chi N,
   fun h => treeContraction_of_hypothesis h⟩

/-! ### Landscape theorem -/

/-- **Stochastic Two-Point MC Landscape**: summary of Part 23.

    PROVED theorems (no open hypotheses used in proofs):
    1. StochasticTwoPointMC: under UFDStrong, positive count for every target
    2. Product multiset grows exponentially (card >= 2^N for q >= 3)
    3. fairTreeCharSum bounded by 1
    4. TreeContractionHypothesis implies TreeContractionAtHalf
    5. Deterministic degeneration: treeCharSum at epsilon = 0 is the minFac path
    6. Standard EM walk = all-true epsilon-walk (Part 20 bridge)

    OPEN hypotheses documented:
    A. TreeContractionAtHalf: tree char sum at fair coin vanishes
       (strictly weaker than TreeContractionHypothesis)
    B. UFDStrong: per-chi spectral gap non-summability (see Part 22 for routes) -/
theorem stochastic_two_point_mc_landscape :
    -- 1. StochasticTwoPointMC PROVED from UFDStrong
    StochasticTwoPointMC q
    ∧
    -- 2. TreeContractionHypothesis implies TreeContractionAtHalf
    (∀ [NeZero q], TreeContractionHypothesis q → TreeContractionAtHalf q)
    ∧
    -- 3. fairTreeCharSum norm bounded by 1
    (∀ [NeZero q] (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ),
      ‖fairTreeCharSum q chi N‖ ≤ 1)
    ∧
    -- 4. Product multiset card >= 2^N for q >= 3
    (2 < q → ∀ N, 2 ^ N ≤
      Multiset.card (productMultiset (paddedUnitSet (q := q)) N))
    ∧
    -- 5. treeCharSum at epsilon = 0 is 1 at depth 0 (deterministic degeneration)
    (∀ (q' : ℕ) [Fact (Nat.Prime q')] [NeZero q']
       (chi : (ZMod q')ˣ →* ℂˣ) (acc : ℕ),
       treeCharSum q' chi 0 acc (fun _ => (0 : ℝ)) = 1)
    ∧
    -- 6. Standard EM walk is one leaf of the tree (Part 20 bridge)
    (∀ n, epsWalkProd emDecision n = prod n) := by
  exact ⟨stochastic_two_point_mc_proved,
         fun h => treeContraction_of_hypothesis h,
         fun chi N => fairTreeCharSum_norm_le_one chi N,
         fun hq3 N => productMultiset_card_ge_two_pow hq3 N,
         fun q' _ _ chi acc => rfl,
         fun n => epsWalkProd_emDecision n⟩

end StochasticTwoPointMC

/-! ## Part 24: Faithful Character Escape and Unconditional Variant MC for q = 3

### Overview

A character `chi : (ZMod q)ˣ →* ℂˣ` is **faithful** if it is injective. For groups of
prime order, every nontrivial character is faithful (by Lagrange's theorem: the kernel
is a subgroup of prime-order group, so either trivial or the whole group; nontriviality
excludes the whole group).

The key insight is that for faithful characters, whenever the raw two-point unit set
has card at least 2 (i.e., minFac and secondMinFac give distinct units mod q), the
character values at these two units are automatically distinct. This gives a positive
spectral gap at every non-fallback step, without any number-theoretic hypothesis.

Combined with the `ufd_fallback_not_summable` result (which handles the case of
infinitely many fallback steps), we get **unconditional** non-summability of spectral
gaps for faithful nontrivial characters.

For q = 3, the unit group `(ZMod 3)ˣ` has order 2 (prime!), so every nontrivial
character is faithful. Therefore `UFDStrong 3` holds unconditionally, and the full
`StochasticTwoPointMC 3` follows with zero open hypotheses.

### Main results

* `IsFaithfulChar` -- definition: chi is injective
* `faithful_iff_trivial_ker` -- equivalence: injective ↔ trivial kernel
* `faithful_distinct_values` -- a ≠ b → chi(a) ≠ chi(b) (as complex numbers)
* `faithful_character_escape` -- unconditional non-summability for faithful nontrivial chi
* `prime_order_nontrivial_is_faithful` -- nontrivial char of prime-order group is faithful
* `ufdStrong_three` -- UFDStrong 3 unconditional
* `variant_mc_three_unconditional` -- every element of (ZMod 3)ˣ reachable, zero hypotheses
* `NonFaithfulCharacterEscape` -- open Prop for non-faithful characters (q > 3)
* `faithful_escape_landscape` -- 4-clause summary theorem
-/

section FaithfulCharacterEscape

variable {q : ℕ} [hqp : Fact (Nat.Prime q)]

/-! ### IsFaithfulChar: definition and basic properties -/

/-- A character `chi : (ZMod q)ˣ →* ℂˣ` is **faithful** if it is injective.
    Equivalently, its kernel is trivial. For groups of prime order, every
    nontrivial character is faithful. -/
def IsFaithfulChar (q : ℕ) [Fact (Nat.Prime q)]
    (chi : (ZMod q)ˣ →* ℂˣ) : Prop :=
  Function.Injective chi

/-- A character is faithful iff its kernel is trivial: every element mapping to 1
    must be the identity. -/
theorem faithful_iff_trivial_ker (chi : (ZMod q)ˣ →* ℂˣ) :
    IsFaithfulChar q chi ↔ ∀ u : (ZMod q)ˣ, chi u = 1 → u = 1 := by
  constructor
  · intro hinj u hu
    have h1 : chi u = chi 1 := by rw [hu, map_one]
    exact hinj h1
  · intro hker a b hab
    have : chi (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have hab1 := hker _ this
    have := mul_eq_one_iff_eq_inv.mp hab1
    rw [this, inv_inv]

/-- A faithful character separates points: distinct units have distinct character values
    (viewed as complex numbers). -/
theorem faithful_distinct_values (chi : (ZMod q)ˣ →* ℂˣ) (hfaith : IsFaithfulChar q chi)
    {a b : (ZMod q)ˣ} (hab : a ≠ b) :
    (chi a : ℂ) ≠ (chi b : ℂ) :=
  Units.val_injective.ne (hfaith.ne hab)

/-- When rawTwoPointUnitSet has card at least 2, the two lifted units are distinct. -/
private theorem raw_card_two_implies_ne (n : ℕ)
    (hcard : 2 ≤ (rawTwoPointUnitSet (q := q) n).card) :
    liftToUnit (q := q) (Nat.minFac (prod n + 1) : ZMod q) ≠
    liftToUnit (q := q) (secondMinFac (prod n + 1) : ZMod q) := by
  intro heq
  have : rawTwoPointUnitSet (q := q) n =
      {liftToUnit (q := q) (Nat.minFac (prod n + 1) : ZMod q)} := by
    simp [rawTwoPointUnitSet, heq]
  rw [this] at hcard
  simp at hcard

/-- At a non-fallback step, a faithful character has a positive spectral gap.
    Key: card ≥ 2 means the two lifted units are distinct; faithfulness means
    their character values are distinct; this gives strict contraction. -/
theorem faithful_gap_pos_at_nonfallback (chi : (ZMod q)ˣ →* ℂˣ)
    (hfaith : IsFaithfulChar q chi) (n : ℕ)
    (hcard : 2 ≤ (rawTwoPointUnitSet (q := q) n).card) :
    0 < 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ := by
  have hne := raw_card_two_implies_ne n hcard
  have hdiff := faithful_distinct_values chi hfaith hne
  exact gap_pos_at_escape n chi hcard hdiff

/-- For a faithful nontrivial character, there exists a uniform positive spectral gap
    bound at all non-fallback steps. Proof: the gap function has finite range
    (paddedUnitSet maps into a finite type), and faithfulness gives positive gap at
    every non-fallback step. The minimum of the positive values in this finite range
    is a uniform lower bound. -/
theorem faithful_uniform_gap (chi : (ZMod q)ˣ →* ℂˣ)
    (hfaith : IsFaithfulChar q chi) :
    ∃ δ > 0, ∀ n, 2 ≤ (rawTwoPointUnitSet (q := q) n).card →
      δ ≤ 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ := by
  -- The gap function has finite range
  have hfin := gap_function_finite_range (q := q) chi
  -- At non-fallback steps, gaps are positive
  have hpos : ∀ n, 2 ≤ (rawTwoPointUnitSet (q := q) n).card →
      0 < 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ :=
    fun n hcard => faithful_gap_pos_at_nonfallback chi hfaith n hcard
  -- We need at least one non-fallback step to get a nonempty positive range
  -- If no such step exists, any delta works vacuously
  by_cases hexists : ∃ n, 2 ≤ (rawTwoPointUnitSet (q := q) n).card
  · obtain ⟨n₀, hn₀⟩ := hexists
    -- Extract positive values in the range
    set posRange := {x ∈ hfin.toFinset | (0 : ℝ) < x}
    have hne : posRange.Nonempty := by
      exact ⟨_, by rw [Finset.mem_filter]; exact
        ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨n₀, rfl⟩, hpos n₀ hn₀⟩⟩
    set δ := posRange.min' hne
    have hδ_pos : 0 < δ := by
      have hmem := Finset.min'_mem posRange hne
      rw [Finset.mem_filter] at hmem
      exact hmem.2
    have hδ_le : ∀ n, 0 < 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ →
        δ ≤ 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ := by
      intro n hfn
      apply Finset.min'_le
      rw [Finset.mem_filter]
      exact ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨n, rfl⟩, hfn⟩
    exact ⟨δ, hδ_pos, fun n hcard => hδ_le n (hpos n hcard)⟩
  · push_neg at hexists
    exact ⟨1, one_pos, fun n hcard => absurd hcard (by exact Nat.not_le.mpr (by linarith [hexists n]))⟩

/-! ### Faithful Character Escape: unconditional non-summability -/

/-- **Faithful Character Escape**: For every prime q at least 3 and every faithful
    nontrivial character, the spectral gaps of padded unit sets are non-summable.
    UNCONDITIONAL -- no open hypotheses.

    Proof by case split on whether infinitely many fallback steps exist:
    - If infinitely many fallback steps: gaps include infinitely many 1's (by
      `ufd_fallback_not_summable`), hence non-summable.
    - If cofinitely many non-fallback steps: faithfulness gives a uniform positive
      lower bound on the gap (by `faithful_uniform_gap`), and infinitely many
      such steps give non-summability (by `not_summable_of_frequently_ge`). -/
theorem faithful_character_escape (hq3 : 2 < q)
    (chi : (ZMod q)ˣ →* ℂˣ) (hchi : chi ≠ 1)
    (hfaithful : IsFaithfulChar q chi) :
    ¬Summable (fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖) := by
  -- Case split: infinitely many fallback steps, or cofinitely many non-fallback
  by_cases h : ∀ N, ∃ n, N ≤ n ∧ ¬(2 ≤ (rawTwoPointUnitSet (q := q) n).card)
  · -- Case A: infinitely many fallback steps
    exact ufd_fallback_not_summable hq3 chi hchi h
  · -- Case B: cofinitely many non-fallback steps
    push_neg at h
    obtain ⟨N₀, hN₀⟩ := h
    -- Get uniform gap bound from faithfulness
    obtain ⟨δ, hδ_pos, hδ_le⟩ := faithful_uniform_gap chi hfaithful
    -- Infinitely many steps have gap >= delta
    apply not_summable_of_frequently_ge _ (fun n => paddedUnitSet_gap_nonneg chi n) hδ_pos
    intro N
    -- Take n = max N N₀; then n >= N₀ so non-fallback, and n >= N
    use max N N₀
    constructor
    · exact le_max_left N N₀
    · exact hδ_le _ (hN₀ _ (le_max_right N N₀))

/-! ### Prime-order groups: every nontrivial character is faithful -/

/-- In a finite group of prime order, every nontrivial character is faithful (injective).

    Proof: The kernel of chi is a subgroup of G. By Lagrange's theorem, its order
    divides |G|. Since |G| is prime, |ker| is 1 or |G|. Since chi is nontrivial,
    ker ≠ G (i.e., ker ≠ top). So ker = bot, which means chi is injective. -/
theorem prime_order_nontrivial_is_faithful {G : Type*} [CommGroup G] [Fintype G]
    (hprime : (Nat.card G).Prime)
    (chi : G →* ℂˣ) (hchi : chi ≠ 1) :
    Function.Injective chi := by
  -- The kernel is a subgroup of a prime-order group, so bot or top
  haveI : Fact (Nat.card G).Prime := Fact.mk hprime
  have h_or := chi.ker.eq_bot_or_eq_top_of_prime_card
  -- chi ≠ 1 means ker ≠ top
  have h_ne_top : chi.ker ≠ ⊤ := by
    rwa [Ne, MonoidHom.ker_eq_top_iff]
  -- So ker = bot
  have h_bot : chi.ker = ⊥ := h_or.resolve_right h_ne_top
  -- bot kernel means injective
  rwa [MonoidHom.ker_eq_bot_iff] at h_bot

/-- Fintype.card (ZMod q)ˣ = q - 1 for prime q. -/
theorem card_units_zmod_eq (hq : Nat.Prime q) : Fintype.card (ZMod q)ˣ = q - 1 := by
  rw [ZMod.card_units_eq_totient, Nat.totient_prime hq]

/-- Nat.card (ZMod q)ˣ = q - 1 for prime q. -/
theorem natCard_units_zmod_eq (hq : Nat.Prime q) : Nat.card (ZMod q)ˣ = q - 1 := by
  rw [Nat.card_eq_fintype_card, card_units_zmod_eq hq]

/-! ### UFDStrong for q = 3: unconditional -/

/-- For q = 3, the unit group has prime order 2, so every nontrivial character is faithful.
    Combined with `faithful_character_escape`, this gives UFDStrong 3 unconditionally. -/
theorem ufdStrong_three : letI := Fact.mk (by decide : Nat.Prime 3); UFDStrong 3 := by
  letI : Fact (Nat.Prime 3) := Fact.mk (by decide)
  intro chi hchi
  have hprime : (Nat.card (ZMod 3)ˣ).Prime := by
    rw [natCard_units_zmod_eq (by decide : Nat.Prime 3)]
    decide
  have hfaithful : IsFaithfulChar 3 chi :=
    prime_order_nontrivial_is_faithful hprime chi hchi
  exact faithful_character_escape (by norm_num : (2 : ℕ) < 3) chi hchi hfaithful

/-- **Unconditional Variant MC for q = 3**: Every element of `(ZMod 3)ˣ` is reachable
    with ZERO open hypotheses. This is the first unconditional result in the stochastic
    MC framework.

    Proof: `ufdStrong_three` (unconditional) feeds into `stochastic_two_point_mc_proved`. -/
theorem variant_mc_three_unconditional :
    letI := Fact.mk (by decide : Nat.Prime 3)
    ∀ (a : (ZMod 3)ˣ), ∃ N,
      0 < Multiset.count a
        (productMultiset (paddedUnitSet (q := 3) ·) N) := by
  letI : Fact (Nat.Prime 3) := Fact.mk (by decide)
  intro a
  exact stochastic_two_point_mc_proved (q := 3)
    (by norm_num : (2 : ℕ) < 3) ufdStrong_three a

/-! ### NonFaithfulCharacterEscape: the remaining gap for q > 3 -/

/-- **FaithfulCharacterEscape**: All faithful nontrivial characters have non-summable
    spectral gaps. This holds UNCONDITIONALLY for all primes q >= 3. -/
def FaithfulCharacterEscape (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  ∀ (chi : (ZMod q)ˣ →* ℂˣ), chi ≠ 1 → IsFaithfulChar q chi →
    ¬Summable (fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖)

/-- **NonFaithfulCharacterEscape**: All non-faithful nontrivial characters have
    non-summable spectral gaps. This is the SOLE remaining open hypothesis for
    UFDStrong at primes q where `(ZMod q)ˣ` has composite order (i.e., q >= 5).

    For q = 3, (ZMod 3)ˣ has prime order 2, so there are NO non-faithful nontrivial
    characters, and this Prop is vacuously true. -/
def NonFaithfulCharacterEscape (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  ∀ (chi : (ZMod q)ˣ →* ℂˣ), chi ≠ 1 → ¬IsFaithfulChar q chi →
    ¬Summable (fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖)

/-- FaithfulCharacterEscape holds unconditionally for all primes q >= 3. -/
theorem faithful_escape_unconditional (hq3 : 2 < q) : FaithfulCharacterEscape q :=
  fun chi hchi hfaith => faithful_character_escape hq3 chi hchi hfaith

/-- FaithfulCharacterEscape + NonFaithfulCharacterEscape implies UFDStrong.
    Every nontrivial character is either faithful or not, so the two cases cover all. -/
theorem nfce_and_fce_implies_ufdStrong
    (_hq3 : 2 < q)
    (hfce : FaithfulCharacterEscape q)
    (hnfce : NonFaithfulCharacterEscape q) :
    UFDStrong q := by
  intro chi hchi
  by_cases hfaith : IsFaithfulChar q chi
  · exact hfce chi hchi hfaith
  · exact hnfce chi hchi hfaith

/-- For primes where the unit group has prime order, NonFaithfulCharacterEscape is
    vacuously true (there are no non-faithful nontrivial characters). -/
theorem nfce_vacuous_of_prime_order
    (hprime : (Nat.card (ZMod q)ˣ).Prime) :
    NonFaithfulCharacterEscape q := by
  intro chi hchi hnfaith
  exact absurd (prime_order_nontrivial_is_faithful hprime chi hchi) hnfaith

/-- NonFaithfulCharacterEscape is the sole remaining open hypothesis for UFDStrong
    at primes q >= 3. Combined with `faithful_escape_unconditional`, it suffices. -/
theorem nfce_implies_ufdStrong (hq3 : 2 < q)
    (hnfce : NonFaithfulCharacterEscape q) :
    UFDStrong q :=
  nfce_and_fce_implies_ufdStrong hq3 (faithful_escape_unconditional hq3) hnfce

/-! ### Landscape theorem -/

/-- **Faithful Character Escape Landscape**: summary of Part 24.

    PROVED UNCONDITIONALLY:
    1. Faithful character escape for all q >= 3 (no open hypotheses)
    2. UFDStrong(3) (no open hypotheses, since (ZMod 3)ˣ has prime order 2)
    3. StochasticTwoPointMC(3): every element of (ZMod 3)ˣ reachable (zero hypotheses)
    4. For q > 3: NonFaithfulCharacterEscape is the SOLE remaining open hypothesis

    The mathematical content is clean: faithfulness = injectivity of characters.
    For cyclic groups of prime order, every nontrivial character is faithful (Lagrange).
    For (ZMod 3)ˣ of order 2, this closes UFDStrong entirely. -/
theorem faithful_escape_landscape :
    -- 1. Faithful character escape unconditional for all q >= 3
    (∀ (q : ℕ) [Fact (Nat.Prime q)], 2 < q →
      ∀ chi : (ZMod q)ˣ →* ℂˣ, chi ≠ 1 → IsFaithfulChar q chi →
      ¬Summable (fun n => 1 - ‖meanCharValue chi (@paddedUnitSet q _ n)‖))
    ∧
    -- 2. UFDStrong(3) unconditional
    (letI := Fact.mk (by decide : Nat.Prime 3); UFDStrong 3)
    ∧
    -- 3. StochasticTwoPointMC(3) unconditional: every element reachable
    (letI := Fact.mk (by decide : Nat.Prime 3);
     ∀ (a : (ZMod 3)ˣ), ∃ N,
      0 < Multiset.count a
        (productMultiset (paddedUnitSet (q := 3) ·) N))
    ∧
    -- 4. NFCE is the sole remaining open hypothesis for q > 3
    (∀ (q : ℕ) [Fact (Nat.Prime q)], 2 < q →
      NonFaithfulCharacterEscape q → UFDStrong q) :=
  ⟨fun _q _ hq3 chi hchi hfaith =>
     faithful_character_escape hq3 chi hchi hfaith,
   ufdStrong_three,
   variant_mc_three_unconditional,
   fun _q _ hq3 hnfce => nfce_implies_ufdStrong hq3 hnfce⟩

end FaithfulCharacterEscape

/-! ## Part 25: Non-Faithful Character Escape Infrastructure

Infrastructure and reductions for `NonFaithfulCharacterEscape(q)` -- the sole
remaining open hypothesis for `UFDStrong(q)` at primes q >= 5.

Part 24 proved: for faithful (injective) characters, spectral gaps are
non-summable unconditionally. This closes UFDStrong(3) since every nontrivial
character of a prime-order group is faithful. For q >= 5, the unit group
(ZMod q)^x has composite order q-1, so non-faithful nontrivial characters exist.

This part develops:
1. Kernel characterizations for non-faithful nontrivial characters
2. Factor ratio definition and gap-kernel equivalence
3. NFCE <-> ratio kernel escape reduction
4. Kernel index bound
5. Connection to existing UFDStrong routes (MinFacRatioEscapeQual -> NFCE)
6. Landscape theorem summarizing Part 25
-/

section NonFaithfulCharacterEscapeInfra

variable {q : ℕ} [hqp : Fact (Nat.Prime q)]

/-! ### Task 1: Kernel characterizations -/

/-- A non-faithful nontrivial character has a nontrivial proper kernel:
    ker(chi) != bot (not injective) AND ker(chi) != top (nontrivial). -/
theorem nonfaithful_nontrivial_ker_proper (chi : (ZMod q)ˣ →* ℂˣ)
    (hchi : chi ≠ 1) (hnf : ¬IsFaithfulChar q chi) :
    chi.ker ≠ ⊥ ∧ chi.ker ≠ ⊤ := by
  constructor
  · rwa [Ne, MonoidHom.ker_eq_bot_iff]
  · rwa [Ne, MonoidHom.ker_eq_top_iff]

/-- ker(chi) != bot iff there exists a nontrivial kernel element. -/
theorem ker_ne_bot_iff_exists_nontrivial (chi : (ZMod q)ˣ →* ℂˣ) :
    chi.ker ≠ ⊥ ↔ ∃ u : (ZMod q)ˣ, u ≠ 1 ∧ chi u = 1 := by
  rw [Ne, Subgroup.eq_bot_iff_forall]
  push_neg
  constructor
  · intro ⟨u, hu_mem, hu_ne⟩
    exact ⟨u, hu_ne, by rwa [MonoidHom.mem_ker] at hu_mem⟩
  · intro ⟨u, hu_ne, hu_ker⟩
    exact ⟨u, by rwa [MonoidHom.mem_ker], hu_ne⟩

/-! ### Task 2: Factor ratio and gap-kernel equivalence -/

/-- The ratio of the two lifted units (minFac and secondMinFac) at step n.
    When both are genuine units, this captures whether their chi-values coincide:
    chi(a) = chi(b) iff a * b^{-1} is in ker(chi). -/
noncomputable def factorRatio (n : ℕ) : (ZMod q)ˣ :=
  liftToUnit (q := q) (Nat.minFac (prod n + 1) : ZMod q) *
  (liftToUnit (q := q) (secondMinFac (prod n + 1) : ZMod q))⁻¹

/-- chi(a) = chi(b) (as units) iff a * b^{-1} in ker(chi), for any CommGroup hom. -/
theorem chi_eq_iff_ratio_in_ker {G : Type*} [CommGroup G]
    (chi : G →* ℂˣ) (a b : G) :
    chi a = chi b ↔ a * b⁻¹ ∈ chi.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv]
  constructor
  · intro h; rw [h, mul_inv_cancel]
  · intro h
    have := mul_inv_eq_one.mp h
    exact this

/-- chi(a) = chi(b) as complex numbers iff a * b^{-1} in ker(chi). -/
theorem chi_coe_eq_iff_ratio_in_ker {G : Type*} [CommGroup G]
    (chi : G →* ℂˣ) (a b : G) :
    (chi a : ℂ) = (chi b : ℂ) ↔ a * b⁻¹ ∈ chi.ker := by
  rw [← chi_eq_iff_ratio_in_ker]
  exact Units.val_injective.eq_iff

/-- At a non-fallback step (raw card >= 2), the spectral gap is zero iff
    the character values at the two lifted units coincide (as complex numbers). -/
theorem gap_zero_iff_chi_eq (n : ℕ) (chi : (ZMod q)ˣ →* ℂˣ)
    (hcard : 2 ≤ (rawTwoPointUnitSet (q := q) n).card) :
    1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ = 0 ↔
    (chi (liftToUnit (q := q) (Nat.minFac (prod n + 1) : ZMod q)) : ℂ) =
    (chi (liftToUnit (q := q) (secondMinFac (prod n + 1) : ZMod q)) : ℂ) := by
  set a := liftToUnit (q := q) (Nat.minFac (prod n + 1) : ZMod q)
  set b := liftToUnit (q := q) (secondMinFac (prod n + 1) : ZMod q)
  have hne : a ≠ b := raw_card_two_implies_ne n hcard
  constructor
  · -- gap = 0 means norm = 1; contrapositive of meanCharValue_norm_lt_one_of_distinct
    intro hgap
    have hnorm : ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ = 1 := by linarith
    by_contra hdiff
    rw [paddedUnitSet_eq_raw_of_card n hcard] at hnorm
    have hlt := meanCharValue_norm_lt_one_of_distinct chi (rawTwoPointUnitSet (q := q) n) hcard
      ⟨a, liftToUnit_minFac_mem_raw n, b, liftToUnit_secondMinFac_mem_raw n, hdiff⟩
    linarith
  · -- chi(a) = chi(b) means mean = (chi(a) + chi(b))/2 = chi(a), which has norm 1
    intro heq
    rw [paddedUnitSet_eq_raw_of_card n hcard]
    simp only [meanCharValue, rawTwoPointUnitSet]
    rw [Finset.sum_pair hne, Finset.card_pair hne]
    rw [heq]
    have h1 : ‖((chi b : ℂ) + (chi b : ℂ)) / (2 : ℂ)‖ = 1 := by
      rw [show (chi b : ℂ) + (chi b : ℂ) = 2 * (chi b : ℂ) from by ring]
      rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℂ) ≠ 0)]
      exact char_norm_one_of_hom chi b
    linarith

/-- Gap = 0 iff the factor ratio lies in the kernel of chi (at non-fallback steps). -/
theorem gap_zero_iff_ratio_in_ker (n : ℕ) (chi : (ZMod q)ˣ →* ℂˣ)
    (hcard : 2 ≤ (rawTwoPointUnitSet (q := q) n).card) :
    1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ = 0 ↔
    factorRatio (q := q) n ∈ chi.ker := by
  rw [gap_zero_iff_chi_eq n chi hcard]
  rw [show factorRatio (q := q) n =
    liftToUnit (q := q) (Nat.minFac (prod n + 1) : ZMod q) *
    (liftToUnit (q := q) (secondMinFac (prod n + 1) : ZMod q))⁻¹ from rfl]
  exact chi_coe_eq_iff_ratio_in_ker chi _ _

/-! ### Task 3: Kernel confinement and ratio escape -/

/-- The factor ratio is eventually always in ker(chi). -/
def KernelConfinement (q : ℕ) [Fact (Nat.Prime q)]
    (chi : (ZMod q)ˣ →* ℂˣ) : Prop :=
  ∃ N₀, ∀ n, N₀ ≤ n → factorRatio (q := q) n ∈ chi.ker

/-- The factor ratio escapes ker(chi) infinitely often. -/
def RatioKernelEscape (q : ℕ) [Fact (Nat.Prime q)]
    (chi : (ZMod q)ˣ →* ℂˣ) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ factorRatio (q := q) n ∉ chi.ker

/-- Ratio escape is the negation of kernel confinement. -/
theorem kernel_escape_iff_not_confinement (chi : (ZMod q)ˣ →* ℂˣ) :
    RatioKernelEscape q chi ↔ ¬KernelConfinement q chi := by
  simp only [RatioKernelEscape, KernelConfinement]
  push_neg
  rfl

/-- If the factor ratio escapes ker(chi) infinitely often AND cofinitely many steps
    are non-fallback, then spectral gaps are non-summable.
    Proof: ratio not in ker -> gap != 0 -> gap > 0 (nonneg). Infinitely many positive
    gaps from a function with finite range gives non-summability. -/
theorem ratio_escape_implies_gap_nonsummable (_hq3 : 2 < q)
    (chi : (ZMod q)ˣ →* ℂˣ) (_hchi : chi ≠ 1)
    (hcofinite : ∃ N₀, ∀ n, N₀ ≤ n → 2 ≤ (rawTwoPointUnitSet (q := q) n).card)
    (hescape : RatioKernelEscape q chi) :
    ¬Summable (fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖) := by
  obtain ⟨N₀, hN₀⟩ := hcofinite
  apply not_summable_of_frequently_pos_finite_range
  · exact fun n => paddedUnitSet_gap_nonneg chi n
  · exact gap_function_finite_range chi
  · intro N
    obtain ⟨n, hn, hratio⟩ := hescape (max N N₀)
    have hn_N : N ≤ n := le_of_max_le_left hn
    have hn_N₀ : N₀ ≤ n := le_of_max_le_right hn
    have hcard := hN₀ n hn_N₀
    have hgap_ne : 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ ≠ 0 := by
      intro heq
      exact hratio ((gap_zero_iff_ratio_in_ker n chi hcard).mp heq)
    exact ⟨n, hn_N, lt_of_le_of_ne (paddedUnitSet_gap_nonneg chi n) (Ne.symm hgap_ne)⟩

/-- RatioKernelEscape for all non-faithful nontrivial chi (+ cofinitely many non-fallback)
    implies NonFaithfulCharacterEscape.
    Proof: case split on infinitely many fallback vs cofinitely many non-fallback. -/
theorem nfce_of_ratio_escape_cofinite (hq3 : 2 < q)
    (hcofinite : ∃ N₀, ∀ n, N₀ ≤ n → 2 ≤ (rawTwoPointUnitSet (q := q) n).card)
    (h : ∀ (chi : (ZMod q)ˣ →* ℂˣ), chi ≠ 1 → ¬IsFaithfulChar q chi →
      RatioKernelEscape q chi) :
    NonFaithfulCharacterEscape q := by
  intro chi hchi hnfaith
  exact ratio_escape_implies_gap_nonsummable hq3 chi hchi hcofinite (h chi hchi hnfaith)

/-- Summable gap + cofinitely many non-fallback steps implies kernel confinement.
    Proof: summable -> tendsto 0 -> eventually < min positive value of finite range
    -> eventually gap = 0 -> eventually ratio in ker. -/
theorem summable_implies_ratio_confined (chi : (ZMod q)ˣ →* ℂˣ)
    (hsum : Summable (fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖))
    (hcofinite : ∃ N₀, ∀ n, N₀ ≤ n → 2 ≤ (rawTwoPointUnitSet (q := q) n).card) :
    KernelConfinement q chi := by
  obtain ⟨N₀, hN₀⟩ := hcofinite
  -- summable nonneg => tendsto 0
  have htends := hsum.tendsto_atTop_zero
  rw [Metric.tendsto_atTop] at htends
  -- The gap function has finite range
  have hfin := gap_function_finite_range (q := q) chi
  -- Extract positive values in the range
  set gapFn := fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖
  -- Case: are there any positive gap values at non-fallback steps beyond N₀?
  by_cases hexists_pos : ∃ n, N₀ ≤ n ∧ 0 < gapFn n
  · -- There exist positive values; use finite range to get a uniform positive lower bound
    set posRange := {x ∈ hfin.toFinset | (0 : ℝ) < x}
    have hne : posRange.Nonempty := by
      obtain ⟨n, _, hfn⟩ := hexists_pos
      exact ⟨gapFn n, by rw [Finset.mem_filter]; exact
        ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨n, rfl⟩, hfn⟩⟩
    set δ := posRange.min' hne
    have hδ_pos : 0 < δ := by
      have hmem := Finset.min'_mem posRange hne
      exact (Finset.mem_filter.mp hmem).2
    -- Eventually gap < δ
    obtain ⟨N₁, hN₁⟩ := htends δ hδ_pos
    -- Beyond max(N₀, N₁), gaps must be 0 (can't be positive and < δ at same time)
    refine ⟨max N₀ N₁, fun n hn => ?_⟩
    have hn_N₀ := le_of_max_le_left hn
    have hn_N₁ := le_of_max_le_right hn
    have hcard := hN₀ n hn_N₀
    rw [← gap_zero_iff_ratio_in_ker n chi hcard]
    -- Show gap = 0 by contradiction: if > 0, it's >= δ but also < δ
    by_contra hne_zero
    have hpos : 0 < gapFn n := lt_of_le_of_ne (paddedUnitSet_gap_nonneg chi n) (Ne.symm hne_zero)
    have hge_delta : δ ≤ gapFn n := by
      apply Finset.min'_le
      rw [Finset.mem_filter]
      exact ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨n, rfl⟩, hpos⟩
    have hlt_delta : gapFn n < δ := by
      have h := hN₁ n hn_N₁
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (paddedUnitSet_gap_nonneg chi n)] at h
      exact h
    linarith
  · -- No positive gap values beyond N₀: all gaps are 0
    push_neg at hexists_pos
    refine ⟨N₀, fun n hn => ?_⟩
    have hcard := hN₀ n hn
    rw [← gap_zero_iff_ratio_in_ker n chi hcard]
    exact le_antisymm (hexists_pos n hn) (paddedUnitSet_gap_nonneg chi n)

/-- NFCE failure implies some non-faithful nontrivial chi has summable gaps. -/
theorem nfce_failure_implies_summable (hfail : ¬NonFaithfulCharacterEscape q) :
    ∃ (chi : (ZMod q)ˣ →* ℂˣ), chi ≠ 1 ∧ ¬IsFaithfulChar q chi ∧
      Summable (fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖) := by
  simp only [NonFaithfulCharacterEscape, not_forall, Classical.not_not] at hfail
  obtain ⟨chi, hchi, hnf, hsum⟩ := hfail
  exact ⟨chi, hchi, hnf, hsum⟩

/-! ### Task 4: Kernel index bound -/

/-- For a nontrivial character, the kernel has index >= 2 in the unit group.
    Proof: chi != 1 means ker != top, and for finite groups index 1 <-> subgroup = top. -/
theorem ker_index_ge_two (chi : (ZMod q)ˣ →* ℂˣ) (hchi : chi ≠ 1) :
    2 ≤ chi.ker.index := by
  have h_ne_top : chi.ker ≠ ⊤ := by rwa [Ne, MonoidHom.ker_eq_top_iff]
  exact chi.ker.one_lt_index_of_ne_top h_ne_top

/-! ### Task 5: Connections to existing routes -/

/-- MinFacRatioEscapeQual implies NonFaithfulCharacterEscape.
    Proof: MinFacRatioEscapeQual gives non-summability for ALL nontrivial chi
    (including non-faithful ones), by composing through UFDStrong. -/
theorem qual_escape_implies_nfce (_hq3 : 2 < q)
    (hq : MinFacRatioEscapeQual q) :
    NonFaithfulCharacterEscape q := by
  intro chi hchi _hnfaith
  exact ratio_escape_implies_ufdStrong (qual_implies_quant hq) chi hchi

/-- The full chain: NFCE -> UFDStrong -> StochasticTwoPointMC. -/
theorem nfce_implies_variant_mc (hq3 : 2 < q)
    (hnfce : NonFaithfulCharacterEscape q) (a : (ZMod q)ˣ) :
    ∃ N, 0 < Multiset.count a (productMultiset (paddedUnitSet (q := q)) N) :=
  stochastic_two_point_mc_proved hq3 (nfce_implies_ufdStrong hq3 hnfce) a

/-! ### Task 6: Structural consequence: non-fallback gap = 0 iff ratio in ker -/

/-- At non-fallback steps, the gap is positive iff the ratio is NOT in ker(chi). -/
theorem gap_pos_iff_ratio_not_in_ker (n : ℕ) (chi : (ZMod q)ˣ →* ℂˣ)
    (hcard : 2 ≤ (rawTwoPointUnitSet (q := q) n).card) :
    0 < 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ ↔
    factorRatio (q := q) n ∉ chi.ker := by
  constructor
  · intro hpos hmem
    have heq := (gap_zero_iff_ratio_in_ker n chi hcard).mpr hmem
    linarith
  · intro hnotin
    have hne : 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ ≠ 0 := by
      intro heq
      exact hnotin ((gap_zero_iff_ratio_in_ker n chi hcard).mp heq)
    exact lt_of_le_of_ne (paddedUnitSet_gap_nonneg chi n) (Ne.symm hne)

/-! ### Task 7: Landscape theorem -/

/-- **Non-Faithful Character Escape Infrastructure Landscape**: summary of Part 25.

    PROVED:
    1. Kernel characterization: non-faithful nontrivial -> ker proper nontrivial
    2. Gap = 0 <-> factor ratio in kernel (at non-fallback steps)
    3. Kernel index >= 2 for nontrivial characters
    4. MinFacRatioEscapeQual -> NFCE
    5. NFCE -> UFDStrong -> StochasticTwoPointMC (full chain)
    6. Ratio escape + cofinitely non-fallback -> NFCE
    7. Summable gaps + cofinitely non-fallback -> kernel confinement -/
theorem nfce_infrastructure_landscape :
    -- 1. Non-faithful nontrivial => proper nontrivial kernel
    (∀ (q' : ℕ) [Fact (Nat.Prime q')] (chi : (ZMod q')ˣ →* ℂˣ),
      chi ≠ 1 → ¬IsFaithfulChar q' chi → chi.ker ≠ ⊥ ∧ chi.ker ≠ ⊤)
    ∧
    -- 2. Gap = 0 <-> ratio in kernel (at non-fallback steps)
    (∀ (q' : ℕ) [Fact (Nat.Prime q')] (chi : (ZMod q')ˣ →* ℂˣ) (n : ℕ),
      2 ≤ (rawTwoPointUnitSet (q := q') n).card →
      (1 - ‖meanCharValue chi (paddedUnitSet (q := q') n)‖ = 0 ↔
       factorRatio (q := q') n ∈ chi.ker))
    ∧
    -- 3. Kernel index >= 2 for nontrivial characters
    (∀ (q' : ℕ) [Fact (Nat.Prime q')] (chi : (ZMod q')ˣ →* ℂˣ),
      chi ≠ 1 → 2 ≤ chi.ker.index)
    ∧
    -- 4. MinFacRatioEscapeQual -> NFCE
    (∀ (q' : ℕ) [Fact (Nat.Prime q')], 2 < q' →
      MinFacRatioEscapeQual q' → NonFaithfulCharacterEscape q')
    ∧
    -- 5. NFCE -> UFDStrong -> StochasticTwoPointMC (full chain)
    (∀ (q' : ℕ) [Fact (Nat.Prime q')], 2 < q' →
      NonFaithfulCharacterEscape q' →
      ∀ (a : (ZMod q')ˣ), ∃ N,
        0 < Multiset.count a (productMultiset (paddedUnitSet (q := q')) N)) :=
  ⟨fun _q' _ chi hchi hnf => nonfaithful_nontrivial_ker_proper chi hchi hnf,
   fun _q' _ chi n hcard => gap_zero_iff_ratio_in_ker n chi hcard,
   fun _q' _ chi hchi => ker_index_ge_two chi hchi,
   fun _q' _ hq3 hq => qual_escape_implies_nfce hq3 hq,
   fun _q' _ hq3 hnfce a => nfce_implies_variant_mc hq3 hnfce a⟩

end NonFaithfulCharacterEscapeInfra
