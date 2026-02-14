import EM.Probability.TransitionKernel

/-!
# Path Measure Infrastructure: Reachable Set Finsets and Branching

## Overview

This file bridges the set-theoretic reachable set infrastructure in `EpsilonRandomMC.lean`
(where `reachableAt q acc n` and `reachableEver q acc` are `Set (ZMod q)`) to the
computable `Finset` world. Since `ZMod q` is `Fintype`, every subset is finite and can
be converted to a `Finset`.

## Key Results

### Part 1: Reachable Set as Finset
* `reachableAtFinset` -- `reachableAt q acc n` as a `Finset (ZMod q)`
* `mem_reachableAtFinset_iff` -- membership equivalence
* `reachableEverFinset` -- `reachableEver q acc` as a `Finset (ZMod q)`
* `mem_reachableEverFinset_iff` -- membership equivalence
* `reachableAtFinset_card_le` -- |R_n| <= q
* `reachableEverFinset_card_le` -- |R_inf| <= q

### Part 2: Cardinality and Properness
* `reachableAtFinset_nonempty` -- R_n is nonempty
* `reachableEverFinset_nonempty` -- R_inf is nonempty
* `reachableEver_card_lt_of_proper` -- R_inf proper implies |R_inf| < q
* `reachableEver_compl_nonempty` -- R_inf proper implies complement nonempty

### Part 3: Branching Distinctness
* `branching_distinct_of_unit` -- unit walk position + distinct factor residues
  give distinct next positions
* `factorResidueFinset` -- prime factors of P+1 as Finset of ZMod q residues
* `factorResidueFinset_nonempty` -- nonempty for P >= 1
* `minFac_in_factorResidueFinset` -- minFac residue is in the factor set

### Part 4: Landscape
* `path_measure_landscape` -- summary conjunction
-/

noncomputable section

open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Part 1: Reachable Set as Finset -/

section ReachableFinset

variable (q : ℕ) [Fact (Nat.Prime q)]

/-- The reachable set at step n as a `Finset (ZMod q)`.
    Since `ZMod q` is `Fintype`, every set is finite. -/
noncomputable def reachableAtFinset (acc n : ℕ) : Finset (ZMod q) :=
  (reachableAt q acc n).toFinset

/-- Membership in `reachableAtFinset` is equivalent to membership in `reachableAt`. -/
theorem mem_reachableAtFinset_iff {acc n : ℕ} {a : ZMod q} :
    a ∈ reachableAtFinset q acc n ↔ a ∈ reachableAt q acc n := by
  simp [reachableAtFinset, Set.mem_toFinset]

/-- The ever-reachable set as a `Finset (ZMod q)`. -/
noncomputable def reachableEverFinset (acc : ℕ) : Finset (ZMod q) :=
  (reachableEver q acc).toFinset

/-- Membership in `reachableEverFinset` is equivalent to membership in `reachableEver`. -/
theorem mem_reachableEverFinset_iff {acc : ℕ} {a : ZMod q} :
    a ∈ reachableEverFinset q acc ↔ a ∈ reachableEver q acc := by
  simp [reachableEverFinset, Set.mem_toFinset]

/-- The cardinality of the reachable set at step n is at most q. -/
theorem reachableAtFinset_card_le (acc n : ℕ) :
    (reachableAtFinset q acc n).card ≤ q := by
  calc (reachableAtFinset q acc n).card
      ≤ Fintype.card (ZMod q) := Finset.card_le_univ _
    _ = q := ZMod.card q

/-- The cardinality of the ever-reachable set is at most q. -/
theorem reachableEverFinset_card_le (acc : ℕ) :
    (reachableEverFinset q acc).card ≤ q := by
  calc (reachableEverFinset q acc).card
      ≤ Fintype.card (ZMod q) := Finset.card_le_univ _
    _ = q := ZMod.card q

/-- The reachable set at step n is nonempty as a Finset. -/
theorem reachableAtFinset_nonempty (acc n : ℕ) :
    (reachableAtFinset q acc n).Nonempty := by
  obtain ⟨a, ha⟩ := reachableAt_nonempty q acc n
  exact ⟨a, (mem_reachableAtFinset_iff q).mpr ha⟩

/-- The ever-reachable set is nonempty as a Finset. -/
theorem reachableEverFinset_nonempty (acc : ℕ) :
    (reachableEverFinset q acc).Nonempty := by
  obtain ⟨a, ha⟩ := reachableEver_nonempty q acc
  exact ⟨a, (mem_reachableEverFinset_iff q).mpr ha⟩

/-- R_n as Finset is a subset of R_inf as Finset. -/
theorem reachableAtFinset_subset_reachableEverFinset (acc n : ℕ) :
    reachableAtFinset q acc n ⊆ reachableEverFinset q acc := by
  intro a ha
  rw [mem_reachableEverFinset_iff]
  exact reachableAt_subset_reachableEver q acc n ((mem_reachableAtFinset_iff q).mp ha)

end ReachableFinset

/-! ## Part 2: Cardinality and Properness -/

section Properness

variable (q : ℕ) [Fact (Nat.Prime q)]

/-- If R_inf is proper (not all of ZMod q), then its Finset cardinality is strictly less than q. -/
theorem reachableEver_card_lt_of_proper {acc : ℕ}
    (h : reachableEver q acc ≠ Set.univ) :
    (reachableEverFinset q acc).card < q := by
  have hlt : (reachableEverFinset q acc).card < Fintype.card (ZMod q) := by
    rw [Finset.card_lt_iff_ne_univ]
    intro heq
    apply h
    ext x
    simp only [Set.mem_univ, iff_true]
    have : x ∈ reachableEverFinset q acc := by rw [heq]; exact Finset.mem_univ x
    exact (mem_reachableEverFinset_iff q).mp this
  rwa [ZMod.card q] at hlt

/-- If R_inf is proper, the complement of R_inf as a Finset is nonempty. -/
theorem reachableEver_compl_nonempty {acc : ℕ}
    (h : reachableEver q acc ≠ Set.univ) :
    (reachableEverFinset q acc)ᶜ.Nonempty := by
  have hne : reachableEverFinset q acc ≠ Finset.univ := by
    intro heq
    apply h
    ext x
    simp only [Set.mem_univ, iff_true]
    have : x ∈ reachableEverFinset q acc := by rw [heq]; exact Finset.mem_univ x
    exact (mem_reachableEverFinset_iff q).mp this
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  apply hne
  ext x
  simp only [Finset.mem_univ, iff_true]
  by_contra hx
  have hmem : x ∈ (reachableEverFinset q acc)ᶜ := Finset.mem_compl.mpr hx
  rw [hempty] at hmem
  simp at hmem

/-- The starting accumulator is in the ever-reachable Finset. -/
theorem acc_mem_reachableEverFinset (acc : ℕ) :
    (acc : ZMod q) ∈ reachableEverFinset q acc :=
  (mem_reachableEverFinset_iff q).mpr (acc_mem_reachableEver q acc)

end Properness

/-! ## Part 3: Branching Distinctness

When the walk position P is a unit mod q, left multiplication by P is injective
on ZMod q. Therefore, if two prime factors p1, p2 of P+1 give distinct residues
mod q, then the resulting walk positions P*p1 and P*p2 are also distinct mod q.
This is the mechanism by which composite Euclid numbers cause the reachable set to grow. -/

section BranchingDistinctness

variable {q : ℕ} [Fact (Nat.Prime q)]

/-- If the walk position P is a unit mod q, and two prime factors of P+1 have
    distinct residues mod q, then they produce distinct walk positions P*p1 and P*p2
    at the next step.

    This is the key injectivity lemma for reachable set growth at composite steps. -/
theorem branching_distinct_of_unit
    {P p₁ p₂ : ℕ}
    (hunit : IsUnit ((P : ℕ) : ZMod q))
    (hdist : (p₁ : ZMod q) ≠ (p₂ : ZMod q)) :
    ((P * p₁ : ℕ) : ZMod q) ≠ ((P * p₂ : ℕ) : ZMod q) := by
  intro heq
  apply hdist
  simp only [Nat.cast_mul] at heq
  exact hunit.mul_left_cancel heq

/-- Variant: branching distinctness for the mixed walk using the walk's own position. -/
theorem branching_distinct_of_walk_unit
    {acc : ℕ} {σ : MixedSelection} {n : ℕ}
    {p₁ p₂ : ℕ}
    (hunit : IsUnit ((mixedWalkProd acc σ n : ℕ) : ZMod q))
    (hdist : (p₁ : ZMod q) ≠ (p₂ : ZMod q)) :
    ((mixedWalkProd acc σ n * p₁ : ℕ) : ZMod q) ≠
    ((mixedWalkProd acc σ n * p₂ : ℕ) : ZMod q) :=
  branching_distinct_of_unit hunit hdist

end BranchingDistinctness

/-! ## Part 4: Factor Residue Finset

The prime factors of P+1, viewed as residues mod q, form a natural Finset.
This bridges between the number-theoretic factorization and the walk dynamics mod q. -/

section FactorResidues

variable (q : ℕ) [Fact (Nat.Prime q)]

/-- The prime factors of P+1 as a Finset of residues in ZMod q.
    This is the image of `(P+1).primeFactors` under the natural cast to ZMod q. -/
noncomputable def factorResidueFinset (P : ℕ) : Finset (ZMod q) :=
  ((P + 1).primeFactors).image (fun (p : ℕ) => (p : ZMod q))

/-- The factor residue Finset is nonempty when P >= 1 (since P+1 >= 2 has prime factors). -/
theorem factorResidueFinset_nonempty {P : ℕ} (hP : 1 ≤ P) :
    (factorResidueFinset q P).Nonempty := by
  apply Finset.Nonempty.image
  exact Nat.nonempty_primeFactors.mpr (show 1 < P + 1 by omega)

/-- minFac(P+1) mod q is in the factor residue Finset when P >= 1. -/
theorem minFac_in_factorResidueFinset {P : ℕ} (hP : 1 ≤ P) :
    ((P + 1).minFac : ZMod q) ∈ factorResidueFinset q P := by
  apply Finset.mem_image.mpr
  exact ⟨(P + 1).minFac,
    Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (show P + 1 ≠ 1 by omega),
      Nat.minFac_dvd _, show P + 1 ≠ 0 by omega⟩,
    rfl⟩

/-- The cardinality of the factor residue Finset is at most the number of
    distinct prime factors (omega function), since it is an image of primeFactors. -/
theorem factorResidueFinset_card_le_omega (P : ℕ) :
    (factorResidueFinset q P).card ≤ (P + 1).primeFactors.card := by
  exact Finset.card_image_le

/-- Every element of the factor residue Finset is the image of some prime factor of P+1. -/
theorem mem_factorResidueFinset_iff {P : ℕ} {a : ZMod q} :
    a ∈ factorResidueFinset q P ↔
    ∃ p ∈ (P + 1).primeFactors, (p : ZMod q) = a := by
  simp [factorResidueFinset, Finset.mem_image]

/-- The factor residue Finset has card at most q. -/
theorem factorResidueFinset_card_le_q (P : ℕ) :
    (factorResidueFinset q P).card ≤ q := by
  calc (factorResidueFinset q P).card
      ≤ Fintype.card (ZMod q) := Finset.card_le_univ _
    _ = q := ZMod.card q

/-- The factor residue Finset subsumes factorSetModQ: every residue from
    factorSetModQ (which excludes factors equal to q) is also in
    factorResidueFinset (which includes all factor residues). -/
theorem factorResidueFinset_subset_image (P : ℕ) :
    factorSetModQ q P ⊆ factorResidueFinset q P := by
  intro a ha
  rw [factorSetModQ] at ha
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
  rw [Finset.mem_filter] at hp
  apply Finset.mem_image.mpr
  exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp.2.1, hp.2.2.1, show P + 1 ≠ 0 by omega⟩, rfl⟩

end FactorResidues

/-! ## Part 5: Reachable Finset Growth Infrastructure

Tools for tracking how the reachable Finset grows step by step. -/

section Growth

variable (q : ℕ) [Fact (Nat.Prime q)]

/-- If a position is reachable at step n, it is in the reachable Finset at step n. -/
theorem reachableAt_to_finset {acc n : ℕ} {a : ZMod q}
    (ha : a ∈ reachableAt q acc n) :
    a ∈ reachableAtFinset q acc n :=
  (mem_reachableAtFinset_iff q).mpr ha

/-- If a position is in the ever-reachable set, it is in the ever-reachable Finset. -/
theorem reachableEver_to_finset {acc : ℕ} {a : ZMod q}
    (ha : a ∈ reachableEver q acc) :
    a ∈ reachableEverFinset q acc :=
  (mem_reachableEverFinset_iff q).mpr ha

/-- Growth at factor step: if sigma reaches P at step n and p | P+1 is prime,
    then P*p mod q is in the ever-reachable Finset. -/
theorem reachableEverFinset_from_factor {acc : ℕ} {n : ℕ}
    {σ : MixedSelection} (hv : ValidMixedSelection acc σ)
    {p : ℕ} (hp : p.Prime) (hdvd : p ∣ mixedWalkProd acc σ n + 1) :
    (mixedWalkProd acc σ n * p : ZMod q) ∈ reachableEverFinset q acc :=
  reachableEver_to_finset q (reachableEver_from_factor hv hp hdvd)

/-- At step 0, the reachable Finset is exactly {acc mod q}. -/
theorem reachableAtFinset_zero (acc : ℕ) :
    reachableAtFinset q acc 0 = {(acc : ZMod q)} := by
  ext a
  rw [mem_reachableAtFinset_iff]
  rw [reachableAt_zero]
  simp [Set.mem_singleton_iff, Finset.mem_singleton]

/-- At step 0, the reachable Finset has card 1. -/
theorem reachableAtFinset_zero_card (acc : ℕ) :
    (reachableAtFinset q acc 0).card = 1 := by
  rw [reachableAtFinset_zero]
  exact Finset.card_singleton _

end Growth

/-! ## Part 6: Landscape -/

section Landscape

variable (q : ℕ) [Fact (Nat.Prime q)]

/-- Summary of path measure infrastructure:
    1. Reachable sets convert to Finsets with card <= q
    2. Proper R_inf has nonempty complement
    3. Branching with unit walk position and distinct factor residues gives distinct positions
    4. Factor residues form a Finset bridging factorization to walk dynamics
    5. R_0 has card 1 (just the starting accumulator) -/
theorem path_measure_landscape (acc : ℕ) :
    -- (1) Reachable Finset card <= q
    (∀ n, (reachableAtFinset q acc n).card ≤ q) ∧
    (reachableEverFinset q acc).card ≤ q ∧
    -- (2) Nonemptiness
    (∀ n, (reachableAtFinset q acc n).Nonempty) ∧
    (reachableEverFinset q acc).Nonempty ∧
    -- (3) R_n ⊆ R_inf (Finset version)
    (∀ n, reachableAtFinset q acc n ⊆ reachableEverFinset q acc) ∧
    -- (4) Starting position in R_inf
    ((acc : ZMod q) ∈ reachableEverFinset q acc) ∧
    -- (5) R_0 has card 1
    ((reachableAtFinset q acc 0).card = 1) :=
  ⟨fun n => reachableAtFinset_card_le q acc n,
   reachableEverFinset_card_le q acc,
   fun n => reachableAtFinset_nonempty q acc n,
   reachableEverFinset_nonempty q acc,
   fun n => reachableAtFinset_subset_reachableEverFinset q acc n,
   acc_mem_reachableEverFinset q acc,
   reachableAtFinset_zero_card q acc⟩

end Landscape

end
