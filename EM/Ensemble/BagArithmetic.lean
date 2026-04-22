import EM.Ensemble.FirstMoment

/-!
# Bag Arithmetic: Prime Factor Structure of Euclid Numbers

This file formalizes "bag-level" quantities for the generalized Euclid-Mullin sequence.
At each step k, the Euclid number `genProd(s, k) + 1` has a set of prime factors
(the "bag"), and the selected prime `genSeq(s, k)` is the smallest element of this bag.

## Main Definitions

* `genEuclidOmega s k` -- number of distinct prime factors of genProd(s,k)+1
* `genBagDiversity q s k` -- number of distinct residue classes mod q among factors
* `genFactorsInClass q a s k` -- prime factors of genProd(s,k)+1 in residue class a mod q
* `genEuclidCofactor s k` -- the cofactor (genProd(s,k)+1) / genSeq(s,k)

## Main Results

* `genEuclidOmega_pos` -- omega >= 1 (the Euclid number has at least one prime factor)
* `genBagDiversity_le_omega` -- diversity <= omega (image card <= source card)
* `genBagDiversity_le_q` -- diversity <= q (at most q residue classes mod q)
* `genSeq_mem_primeFactors` -- genSeq is in the prime factorization
* `genSeq_in_bag` -- genSeq is in its own residue class factor set
* `genFactorsInClass_subset` -- class factors are a subset of all factors
* `genEuclidCofactor_mul` -- genProd(s,k)+1 = genSeq(s,k) * genEuclidCofactor(s,k)
* `genEuclidCofactor_pos` -- cofactor >= 1
* `two_not_mem_primeFactors_of_pos` -- 2 not in bag for k >= 1, s >= 1
* `bag_arithmetic_landscape` -- summary conjunction
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Definitions -/

section BagDefinitions

/-- Number of distinct prime factors of genProd(s, k) + 1. -/
def genEuclidOmega (s k : ℕ) : ℕ := (genProd s k + 1).primeFactors.card

/-- Residue diversity: number of distinct residue classes mod q among prime factors
    of genProd(s, k) + 1. -/
def genBagDiversity (q s k : ℕ) : ℕ :=
  ((genProd s k + 1).primeFactors.image (fun (p : ℕ) => (p : ZMod q))).card

/-- Prime factors of genProd(s, k) + 1 that lie in residue class a mod q. -/
def genFactorsInClass (q : ℕ) (a : ZMod q) (s k : ℕ) : Finset ℕ :=
  (genProd s k + 1).primeFactors.filter (fun (p : ℕ) => (p : ZMod q) = a)

/-- The cofactor: (genProd(s,k)+1) / genSeq(s,k).
    Since genSeq divides genProd+1, this is exact division. -/
def genEuclidCofactor (s k : ℕ) : ℕ := (genProd s k + 1) / genSeq s k

end BagDefinitions

/-! ## Elementary Properties -/

section BagProperties

/-- The Euclid number genProd(s,k)+1 is at least 2 when s >= 1. -/
private theorem genProd_succ_ge_two {s : ℕ} (hs : 1 ≤ s) (k : ℕ) :
    2 ≤ genProd s k + 1 := by
  have := genProd_pos hs k; omega

/-- The Euclid number genProd(s,k)+1 is nonzero when s >= 1. -/
private theorem genProd_succ_ne_zero {s : ℕ} (hs : 1 ≤ s) (k : ℕ) :
    genProd s k + 1 ≠ 0 := by
  have := genProd_pos hs k; omega

/-- genEuclidOmega(s, k) >= 1: the Euclid number has at least one prime factor. -/
theorem genEuclidOmega_pos {s : ℕ} (hs : 1 ≤ s) (k : ℕ) : 1 ≤ genEuclidOmega s k := by
  simp only [genEuclidOmega]
  rw [Finset.one_le_card]
  exact ⟨genSeq s k, by
    rw [Nat.mem_primeFactors]
    exact ⟨genSeq_prime hs k, genSeq_dvd_genProd_succ s k, genProd_succ_ne_zero hs k⟩⟩

/-- Residue diversity is at most omega (image card <= source card). -/
theorem genBagDiversity_le_omega (q s k : ℕ) :
    genBagDiversity q s k ≤ genEuclidOmega s k := by
  unfold genBagDiversity genEuclidOmega
  exact Finset.card_image_le

/-- Residue diversity is at most q (at most q residue classes mod q). -/
theorem genBagDiversity_le_q {q : ℕ} (hq : 1 ≤ q) (s k : ℕ) :
    genBagDiversity q s k ≤ q := by
  unfold genBagDiversity
  have : NeZero q := ⟨by omega⟩
  calc ((genProd s k + 1).primeFactors.image (fun (p : ℕ) => (p : ZMod q))).card
      ≤ Fintype.card (ZMod q) := Finset.card_le_univ _
    _ = q := ZMod.card q

/-- genSeq(s, k) is a member of the prime factorization of genProd(s, k) + 1. -/
theorem genSeq_mem_primeFactors {s : ℕ} (hs : 1 ≤ s) (k : ℕ) :
    genSeq s k ∈ (genProd s k + 1).primeFactors := by
  rw [Nat.mem_primeFactors]
  exact ⟨genSeq_prime hs k, genSeq_dvd_genProd_succ s k, genProd_succ_ne_zero hs k⟩

/-- genSeq(s, k) belongs to the factor set in its own residue class. -/
theorem genSeq_in_bag {s : ℕ} (hs : 1 ≤ s) (q : ℕ) (k : ℕ) :
    genSeq s k ∈ genFactorsInClass q ((genSeq s k : ℕ) : ZMod q) s k := by
  simp only [genFactorsInClass, Finset.mem_filter]
  exact ⟨genSeq_mem_primeFactors hs k, trivial⟩

/-- The class factor set is a subset of all prime factors. -/
theorem genFactorsInClass_subset (q : ℕ) (a : ZMod q) (s k : ℕ) :
    genFactorsInClass q a s k ⊆ (genProd s k + 1).primeFactors :=
  Finset.filter_subset _ _

/-- The cofactor satisfies genProd(s,k)+1 = genSeq(s,k) * genEuclidCofactor(s,k). -/
theorem genEuclidCofactor_mul (s k : ℕ) :
    genProd s k + 1 = genSeq s k * genEuclidCofactor s k := by
  simp only [genEuclidCofactor]
  rw [mul_comm]
  exact (Nat.div_mul_cancel (genSeq_dvd_genProd_succ s k)).symm

/-- The cofactor is at least 1 when s >= 1. -/
theorem genEuclidCofactor_pos {s : ℕ} (hs : 1 ≤ s) (k : ℕ) :
    1 ≤ genEuclidCofactor s k := by
  simp only [genEuclidCofactor]
  exact Nat.div_pos
    (Nat.le_of_dvd (by have := genProd_pos hs k; omega) (genSeq_dvd_genProd_succ s k))
    (genSeq_prime hs k).pos

/-- For k >= 1 and s >= 1, genProd(s,k)+1 is odd (2 does not divide it). -/
theorem genProd_succ_not_dvd_two {s : ℕ} (hs : 1 ≤ s) {k : ℕ} (hk : 1 ≤ k) :
    ¬ (2 ∣ genProd s k + 1) := by
  intro ⟨r, hr⟩
  exact genProd_succ_odd hs hk (even_iff_two_dvd.mpr ⟨r, hr⟩)

/-- For k >= 1 and s >= 1, 2 is not in the prime factorization of genProd(s,k)+1. -/
theorem two_not_mem_primeFactors_of_pos {s : ℕ} (hs : 1 ≤ s) {k : ℕ} (hk : 1 ≤ k) :
    2 ∉ (genProd s k + 1).primeFactors := by
  rw [Nat.mem_primeFactors]
  push Not
  intro _ h2
  exact absurd h2 (genProd_succ_not_dvd_two hs hk)

/-- All prime factors of genProd(s,k)+1 are odd for k >= 1, s >= 1. -/
theorem primeFactors_odd_of_pos {s : ℕ} (hs : 1 ≤ s) {k : ℕ} (hk : 1 ≤ k)
    {p : ℕ} (hp : p ∈ (genProd s k + 1).primeFactors) : p ≠ 2 := by
  intro h2
  exact absurd (h2 ▸ hp) (two_not_mem_primeFactors_of_pos hs hk)

/-- All prime factors of genProd(s,k)+1 are at least 3 for k >= 1, s >= 1. -/
theorem primeFactors_ge_three_of_pos {s : ℕ} (hs : 1 ≤ s) {k : ℕ} (hk : 1 ≤ k)
    {p : ℕ} (hp : p ∈ (genProd s k + 1).primeFactors) : 3 ≤ p := by
  have hp_prime := (Nat.mem_primeFactors.mp hp).1
  have hp_ge2 := hp_prime.two_le
  have hp_ne2 := primeFactors_odd_of_pos hs hk hp
  omega

end BagProperties

/-! ## Class Factor Cardinality -/

section ClassCardinality

/-- The class containing genSeq has at least one element. -/
theorem genFactorsInClass_nonempty {s : ℕ} (hs : 1 ≤ s) (q : ℕ) (k : ℕ) :
    (genFactorsInClass q ((genSeq s k : ℕ) : ZMod q) s k).Nonempty :=
  ⟨genSeq s k, genSeq_in_bag hs q k⟩

/-- The number of distinct primes in the genSeq residue class is at least 1. -/
theorem genFactorsInClass_card_pos {s : ℕ} (hs : 1 ≤ s) (q : ℕ) (k : ℕ) :
    1 ≤ (genFactorsInClass q ((genSeq s k : ℕ) : ZMod q) s k).card :=
  Finset.one_le_card.mpr (genFactorsInClass_nonempty hs q k)

/-- Sum of class cardinalities equals omega (partition by residue class mod q). -/
theorem genFactorsInClass_card_sum {s k q : ℕ} (hq : 1 ≤ q) :
    haveI : NeZero q := ⟨by omega⟩
    ∑ a : ZMod q,
      (genFactorsInClass q a s k).card = genEuclidOmega s k := by
  haveI : NeZero q := ⟨by omega⟩
  simp only [genEuclidOmega, genFactorsInClass]
  exact (Finset.card_eq_sum_card_fiberwise
    (f := fun (p : ℕ) => (p : ZMod q))
    (s := (genProd s k + 1).primeFactors)
    (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)).symm

end ClassCardinality

/-! ## Cofactor Structure -/

section CofactorStructure

/-- Every prime factor of the cofactor is also a prime factor of genProd(s,k)+1. -/
theorem cofactor_primeFactors_subset {s : ℕ} (hs : 1 ≤ s) (k : ℕ) :
    (genEuclidCofactor s k).primeFactors ⊆ (genProd s k + 1).primeFactors := by
  intro p hp
  rw [Nat.mem_primeFactors] at hp
  rw [Nat.mem_primeFactors]
  refine ⟨hp.1, dvd_trans hp.2.1 ?_, genProd_succ_ne_zero hs k⟩
  exact ⟨genSeq s k, by rw [mul_comm]; exact genEuclidCofactor_mul s k⟩

/-- The cofactor has at most as many distinct prime factors as genProd(s,k)+1. -/
theorem cofactor_omega_le {s : ℕ} (hs : 1 ≤ s) (k : ℕ) :
    (genEuclidCofactor s k).primeFactors.card ≤ genEuclidOmega s k := by
  simp only [genEuclidOmega]
  exact Finset.card_le_card (cofactor_primeFactors_subset hs k)

end CofactorStructure

/-! ## Landscape -/

/-- Summary of bag arithmetic properties. -/
theorem bag_arithmetic_landscape {s : ℕ} (hs : 1 ≤ s) (q : ℕ) (hq : 1 ≤ q) (k : ℕ) :
    genEuclidOmega s k ≥ 1 ∧
    genBagDiversity q s k ≤ genEuclidOmega s k ∧
    genSeq s k ∈ (genProd s k + 1).primeFactors ∧
    genProd s k + 1 = genSeq s k * genEuclidCofactor s k ∧
    genEuclidCofactor s k ≥ 1 ∧
    genBagDiversity q s k ≤ q :=
  ⟨genEuclidOmega_pos hs k,
   genBagDiversity_le_omega q s k,
   genSeq_mem_primeFactors hs k,
   genEuclidCofactor_mul s k,
   genEuclidCofactor_pos hs k,
   genBagDiversity_le_q hq s k⟩

end
