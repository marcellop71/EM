import EM.Advanced.StochasticEM
import EM.Ensemble.BagArithmetic
import EM.Advanced.VanishingNoiseC

/-!
# Factor Diversity: Ensemble-Level Factor Set Structure

## Overview

This file connects the ensemble-level prime factor structure of Euclid numbers
`genProd(n, k) + 1` to the spectral contraction framework of the stochastic
Euclid-Mullin process.

At each step k of the ensemble sequence starting from n, the Euclid number
`genProd(n, k) + 1` has a set of prime factors. The selected prime `genSeq(n, k)`
is the smallest element. When this factor set has >= 2 elements with distinct
character values mod q, the mean character value over the factor set has norm
strictly < 1, producing spectral contraction.

## Main Definitions

* `genFactorSet n k` -- prime factors of genProd(n, k) + 1 as a Finset
* `genFactorSetMod q n k` -- factor set residues mod q in (ZMod q)
* `FactorDiversityAtStep q n k` -- genFactorSetMod has >= 2 distinct elements
* `InfinitelyManyDiverseSteps q n` -- FactorDiversityAtStep for infinitely many k

## Main Results

* `genFactorSet_nonempty` -- factor set is nonempty (for n >= 1)
* `genFactorSet_all_prime` -- every element of genFactorSet is prime
* `genSeq_mem_genFactorSet` -- genSeq(n, k) is in genFactorSet(n, k)
* `genFactorSetMod_card_ge_one` -- at least one residue class represented
* `factor_diversity_spectral_contraction` -- diversity implies mean char value norm < 1
* `diverse_steps_imply_vanishing` -- infinitely many diverse steps with uniform gap
                                     implies averaged character product vanishes
* `factor_diversity_landscape` -- summary conjunction

-/

noncomputable section

open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Part 1: Definitions

The factor set `genFactorSet n k` is simply the prime factorization of
`genProd(n, k) + 1`. The mod-q version `genFactorSetMod` maps these
prime factors into `ZMod q` via natural casting. -/

section Definitions

/-- Prime factors of genProd(n, k) + 1 as a Finset of natural numbers. -/
def genFactorSet (n k : ℕ) : Finset ℕ :=
  (genProd n k + 1).primeFactors

/-- Factor set residues mod q: the image of genFactorSet under casting to ZMod q. -/
def genFactorSetMod (q n k : ℕ) : Finset (ZMod q) :=
  (genFactorSet n k).image (fun (p : ℕ) => (p : ZMod q))

/-- Factor diversity at step k: the factor set mod q has at least 2 distinct
    residue classes. This is the ensemble-level version of the diversity
    condition needed for spectral contraction. -/
def FactorDiversityAtStep (q n k : ℕ) : Prop :=
  2 ≤ (genFactorSetMod q n k).card

/-- Infinitely many diverse steps: FactorDiversityAtStep holds for infinitely
    many values of k. -/
def InfinitelyManyDiverseSteps (q n : ℕ) : Prop :=
  ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ FactorDiversityAtStep q n k

end Definitions

/-! ## Part 2: Structural Properties

The factor set is nonempty because genProd(n, k) + 1 >= 2 (for n >= 1),
and every natural number >= 2 has at least one prime factor. Every element
of the factor set is prime (by definition of primeFactors). The selected
prime genSeq(n, k) = minFac(genProd(n, k) + 1) is always in the factor set. -/

section StructuralProperties

/-- genProd(n, k) + 1 is nonzero when n >= 1. -/
private theorem genProd_succ_ne_zero' {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    genProd n k + 1 ≠ 0 := by
  have := genProd_pos hn k; omega

/-- The factor set is nonempty when n >= 1: genProd(n, k) + 1 >= 2 has at
    least one prime factor. -/
theorem genFactorSet_nonempty {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    (genFactorSet n k).Nonempty :=
  ⟨genSeq n k, by
    simp only [genFactorSet]
    rw [Nat.mem_primeFactors]
    exact ⟨genSeq_prime hn k, genSeq_dvd_genProd_succ n k,
           genProd_succ_ne_zero' hn k⟩⟩

/-- Every element of the factor set is prime. -/
theorem genFactorSet_all_prime {n k p : ℕ} (hp : p ∈ genFactorSet n k) :
    Nat.Prime p := by
  simp only [genFactorSet] at hp
  exact (Nat.mem_primeFactors.mp hp).1

/-- Every element of the factor set divides genProd(n, k) + 1. -/
theorem genFactorSet_dvd {n k p : ℕ} (hp : p ∈ genFactorSet n k) :
    p ∣ genProd n k + 1 := by
  simp only [genFactorSet] at hp
  exact (Nat.mem_primeFactors.mp hp).2.1

/-- genSeq(n, k) is in the factor set of genProd(n, k) + 1. This is because
    genSeq = minFac(genProd + 1), which is a prime factor of genProd + 1. -/
theorem genSeq_mem_genFactorSet {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    genSeq n k ∈ genFactorSet n k := by
  simp only [genFactorSet]
  exact genSeq_mem_primeFactors hn k

/-- The factor set mod q has at least one element when n >= 1. -/
theorem genFactorSetMod_card_ge_one {n : ℕ} (hn : 1 ≤ n) (k q : ℕ) :
    1 ≤ (genFactorSetMod q n k).card := by
  rw [Finset.one_le_card]
  exact ⟨(genSeq n k : ZMod q), Finset.mem_image.mpr
    ⟨genSeq n k, genSeq_mem_genFactorSet hn k, rfl⟩⟩

/-- The factor set has cardinality equal to genEuclidOmega. -/
theorem genFactorSet_card_eq_omega (n k : ℕ) :
    (genFactorSet n k).card = genEuclidOmega n k := by
  rfl

/-- The factor set mod q has cardinality equal to genBagDiversity. -/
theorem genFactorSetMod_card_eq_diversity (q n k : ℕ) :
    (genFactorSetMod q n k).card = genBagDiversity q n k := by
  simp only [genFactorSetMod, genBagDiversity, genFactorSet]

/-- Factor diversity at step k is equivalent to genBagDiversity >= 2. -/
theorem factorDiversityAtStep_iff_diversity_ge_two (q n k : ℕ) :
    FactorDiversityAtStep q n k ↔ 2 ≤ genBagDiversity q n k := by
  simp only [FactorDiversityAtStep, genFactorSetMod_card_eq_diversity]

end StructuralProperties

/-! ## Part 3: Connection to Spectral Contraction

When the factor set mod q has >= 2 distinct residue classes AND a nontrivial
character chi separates two of them, the mean character value over the
factor set (viewed as elements of (ZMod q)^times) has norm strictly < 1.

This bridges the ensemble-level diversity condition to the spectral
contraction framework from VanishingNoise.

We state the spectral contraction in terms of abstract groups G, since
the key mechanism (strict triangle inequality for unit-modulus character values)
is purely group-theoretic. -/

section SpectralContraction

/-- If a Finset S in a finite abelian group has >= 2 elements with distinct
    chi-values, then the mean character value over S has norm < 1.

    This wraps meanCharValue_norm_lt_one_of_distinct from VanishingNoiseB.lean.
    The ensemble application: S is the factor set mod q lifted to units of
    (ZMod q)^times, and chi is a Dirichlet character. -/
theorem factor_diversity_spectral_contraction
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (chi : G →* ℂˣ) (S : Finset G)
    (hcard : 2 ≤ S.card)
    (hdist : ∃ s ∈ S, ∃ t ∈ S, (chi s : ℂ) ≠ (chi t : ℂ)) :
    ‖meanCharValue chi S‖ < 1 :=
  meanCharValue_norm_lt_one_of_distinct chi S hcard hdist

/-- The spectral gap at a diverse step is positive: if we have a Finset S
    with >= 2 elements and distinct chi-values, then 1 - ||meanCharValue|| > 0. -/
theorem spectral_gap_pos_of_diverse
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (chi : G →* ℂˣ) (S : Finset G)
    (hcard : 2 ≤ S.card)
    (hdist : ∃ s ∈ S, ∃ t ∈ S, (chi s : ℂ) ≠ (chi t : ℂ)) :
    0 < 1 - ‖meanCharValue chi S‖ := by
  linarith [factor_diversity_spectral_contraction chi S hcard hdist]

end SpectralContraction

/-! ## Part 4: From Infinitely Many Diverse Steps to Vanishing

If infinitely many steps have factor diversity (>= 2 distinct residue classes
with distinct chi-values), and the spectral gap at each diverse step is
bounded below by some delta > 0, then the sum of gaps diverges, which by
sparse_product_contraction implies the averaged character product tends to 0. -/

section DiverseStepsVanishing

/-- If a real-valued function f(k) >= delta > 0 at infinitely many k,
    and f(k) >= 0 everywhere, then sum f is not summable.

    This is the key lemma connecting "infinitely often >= delta" to
    non-summability (which feeds sparse_product_contraction). -/
private theorem not_summable_of_io_ge_delta
    (f : ℕ → ℝ) (hf_nonneg : ∀ k, 0 ≤ f k)
    (δ : ℝ) (hδ : 0 < δ)
    (hio : ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ δ ≤ f k) :
    ¬Summable f := by
  intro hsum
  have htend := hsum.tendsto_atTop_zero
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N, hN⟩ := htend δ hδ
  obtain ⟨k, hk_ge, hk_val⟩ := hio N
  have habs := hN k hk_ge
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hf_nonneg k)] at habs
  linarith

/-- If infinitely many steps have spectral gap >= delta > 0 and all steps
    have gap in [0, 1], then the gap sum diverges. -/
theorem diverse_steps_gap_not_summable
    (gap : ℕ → ℝ)
    (hgap_nonneg : ∀ k, 0 ≤ gap k)
    (δ : ℝ) (hδ : 0 < δ)
    (hio : ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ δ ≤ gap k) :
    ¬Summable gap :=
  not_summable_of_io_ge_delta gap hgap_nonneg δ hδ hio

/-- Main vanishing theorem: if a sequence of Finsets S(k) satisfies:
    (1) all S(k) are nonempty,
    (2) there exists delta > 0 such that infinitely many steps have gap >= delta,
    then the averaged character product tends to 0.

    This composes diverse_steps_gap_not_summable with
    sparse_avgCharProduct_tendsto_zero from VanishingNoiseC. -/
theorem diverse_steps_imply_vanishing
    {G : Type*} [CommGroup G] [Fintype G]
    (chi : G →* ℂˣ) (S : ℕ → Finset G)
    (hne : ∀ k, (S k).Nonempty)
    (δ : ℝ) (hδ : 0 < δ)
    (hio : ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ δ ≤ 1 - ‖meanCharValue chi (S k)‖) :
    Filter.Tendsto (fun N => ‖avgCharProduct chi S N‖)
      Filter.atTop (nhds 0) := by
  apply sparse_avgCharProduct_tendsto_zero chi S hne
  apply not_summable_of_io_ge_delta _ _ δ hδ hio
  intro k
  have hle := meanCharValue_norm_le_one chi (S k) (hne k)
  linarith

end DiverseStepsVanishing

/-! ## Part 5: Ensemble Factor Diversity Consequences

We tie together the structural properties with the vanishing framework.
The key results: factor diversity implies the existence of distinct
residue classes in the factor set, which is the precondition for
spectral contraction. -/

section EnsembleConsequences

/-- Factor diversity implies omega >= 2: if the factor set has >= 2
    residue classes mod q, then genProd(n,k)+1 has >= 2 distinct prime factors. -/
theorem factor_diversity_implies_omega_ge_two
    {q k : ℕ} (n : ℕ) (hdiv : FactorDiversityAtStep q n k) :
    2 ≤ genEuclidOmega n k := by
  have hle := genBagDiversity_le_omega q n k
  have hdiv' := (factorDiversityAtStep_iff_diversity_ge_two q n k).mp hdiv
  omega

/-- genSeq is the minimum element of genFactorSet: every prime factor of
    genProd(n, k) + 1 is at least as large as genSeq(n, k) = minFac(genProd(n, k) + 1). -/
theorem genSeq_is_min_of_genFactorSet (n k : ℕ)
    {p : ℕ} (hp : p ∈ genFactorSet n k) : genSeq n k ≤ p := by
  simp only [genFactorSet] at hp
  exact Nat.minFac_le_of_dvd
    (Nat.mem_primeFactors.mp hp).1.two_le
    (Nat.mem_primeFactors.mp hp).2.1

/-- Factor diversity at step k means there exist at least 2 prime factors
    with distinct residues mod q. -/
theorem factor_diversity_has_distinct_residues
    {q k : ℕ} (n : ℕ) (hdiv : FactorDiversityAtStep q n k) :
    ∃ p₁ ∈ genFactorSet n k, ∃ p₂ ∈ genFactorSet n k,
      (p₁ : ZMod q) ≠ (p₂ : ZMod q) := by
  simp only [FactorDiversityAtStep, genFactorSetMod] at hdiv
  letI : DecidableEq (ZMod q) := inferInstance
  have hge : 1 < ((genFactorSet n k).image (fun (p : ℕ) => (p : ZMod q))).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hge
  rw [Finset.mem_image] at ha hb
  obtain ⟨p₁, hp₁, rfl⟩ := ha
  obtain ⟨p₂, hp₂, rfl⟩ := hb
  exact ⟨p₁, hp₁, p₂, hp₂, hab⟩

/-- The factor set is a subset of the range [1, genProd(n,k)+1]: every
    prime factor p satisfies p <= genProd(n,k) + 1. -/
theorem genFactorSet_le_succ {n k p : ℕ} (hp : p ∈ genFactorSet n k) :
    p ≤ genProd n k + 1 := by
  exact Nat.le_of_dvd (by omega) (genFactorSet_dvd hp)

end EnsembleConsequences

/-! ## Part 6: Landscape -/

section Landscape

/-- **Factor Diversity Landscape**: Summary of the factor diversity formalization.

    1. genFactorSet is nonempty for n >= 1 (at least genSeq is present)
    2. Every element of genFactorSet is prime
    3. genSeq is the minimum element of genFactorSet
    4. genFactorSetMod has card >= 1 (at least one residue class)
    5. Factor diversity implies omega >= 2 (at least 2 distinct prime factors)
    6. Factor diversity implies distinct residues exist
    7. Diverse steps with uniform gap imply vanishing -/
theorem factor_diversity_landscape {n : ℕ} (hn : 1 ≤ n) (q : ℕ) :
    -- 1. Factor set nonempty
    (∀ k, (genFactorSet n k).Nonempty)
    ∧
    -- 2. All elements are prime
    (∀ k p, p ∈ genFactorSet n k → Nat.Prime p)
    ∧
    -- 3. genSeq is minimum
    (∀ k p, p ∈ genFactorSet n k → genSeq n k ≤ p)
    ∧
    -- 4. At least one residue class
    (∀ k, 1 ≤ (genFactorSetMod q n k).card)
    ∧
    -- 5. Factor diversity implies omega >= 2
    (∀ k, FactorDiversityAtStep q n k → 2 ≤ genEuclidOmega n k)
    ∧
    -- 6. Factor diversity implies distinct residues
    (∀ k, FactorDiversityAtStep q n k →
      ∃ p₁ ∈ genFactorSet n k, ∃ p₂ ∈ genFactorSet n k,
        (p₁ : ZMod q) ≠ (p₂ : ZMod q))
    ∧
    -- 7. Diverse steps with gap imply vanishing (abstract version)
    (∀ {G : Type*} [CommGroup G] [Fintype G]
      (chi : G →* ℂˣ) (S : ℕ → Finset G)
      (_ : ∀ k, (S k).Nonempty)
      (δ : ℝ) (_ : 0 < δ)
      (_ : ∀ K, ∃ k, K ≤ k ∧ δ ≤ 1 - ‖meanCharValue chi (S k)‖),
      Filter.Tendsto (fun N => ‖avgCharProduct chi S N‖)
        Filter.atTop (nhds 0)) :=
  ⟨fun k => genFactorSet_nonempty hn k,
   fun _ _ hp => genFactorSet_all_prime hp,
   fun _ _ hp => genSeq_is_min_of_genFactorSet _ _ hp,
   fun k => genFactorSetMod_card_ge_one hn k q,
   fun _ hd => factor_diversity_implies_omega_ge_two n hd,
   fun _ hd => factor_diversity_has_distinct_residues n hd,
   fun chi S hne δ hδ hio => diverse_steps_imply_vanishing chi S hne δ hδ hio⟩

end Landscape

end
