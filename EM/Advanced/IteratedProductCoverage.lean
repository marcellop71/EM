/-
Copyright (c) 2025 Mullin's Conjecture Project. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Combinatorics.Additive.CauchyDavenport
import EM.Advanced.VanishingNoise

/-!
# Iterated Product Coverage via Cauchy-Davenport

This file proves that iterated products of sufficiently large subsets of a finite
commutative group eventually cover the entire group. The key tool is the
Cauchy-Davenport theorem, which at each step gives
`|A * B| >= min(minOrder G, |A| + |B| - 1)`.

For a cyclic group of prime order p (e.g. `(ZMod p)×`), `minOrder = p = |G|`,
so each multiplication step with a set of size >= 2 increases the product set
by at least 1 element, and after at most `|G| - 1` such steps the product
covers all of G.

## Main results

* `iteratedMulFinset_card_growth` -- iterated Cauchy-Davenport card lower bound
* `iteratedMulFinset_eq_univ` -- product = univ after enough large steps
* `iterated_product_coverage_landscape` -- summary conjunction

## Connection to existing infrastructure

This provides a DETERMINISTIC coverage result complementing the PROBABILISTIC
path existence in `VanishingNoise.lean` (via vanishing Fourier sums). The
Cauchy-Davenport approach is more elementary and gives explicit diameter bounds.
-/

open Finset Function Monoid
open scoped Pointwise

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

namespace IteratedProduct

/-! ### Part 1: Iterated product definition -/

/-- Iterated product of finsets: `iteratedMulFinset S 0 = {1}`,
    `iteratedMulFinset S (k+1) = (iteratedMulFinset S k) * S k`. -/
def iteratedMulFinset (S : ℕ → Finset G) : ℕ → Finset G
  | 0 => {1}
  | n + 1 => (iteratedMulFinset S n) * S n

omit [Fintype G] in
theorem iteratedMulFinset_zero (S : ℕ → Finset G) :
    iteratedMulFinset S 0 = {1} := rfl

omit [Fintype G] in
theorem iteratedMulFinset_succ (S : ℕ → Finset G) (n : ℕ) :
    iteratedMulFinset S (n + 1) = (iteratedMulFinset S n) * S n := rfl

omit [Fintype G] in
theorem iteratedMulFinset_nonempty (S : ℕ → Finset G) (hS : ∀ k, (S k).Nonempty) :
    ∀ n, (iteratedMulFinset S n).Nonempty
  | 0 => singleton_nonempty 1
  | n + 1 => (iteratedMulFinset_nonempty S hS n).mul (hS n)

omit [Fintype G] in
theorem one_mem_iteratedMulFinset_zero (S : ℕ → Finset G) :
    (1 : G) ∈ iteratedMulFinset S 0 :=
  Finset.mem_singleton_self 1

/-! ### Part 2: Monotonicity of iterated product -/

omit [Fintype G] in
/-- If `1 ∈ S n`, then the iterated product grows. -/
theorem iteratedMulFinset_subset_succ (S : ℕ → Finset G) (n : ℕ)
    (h1 : (1 : G) ∈ S n) :
    iteratedMulFinset S n ⊆ iteratedMulFinset S (n + 1) := by
  intro g hg
  simp only [iteratedMulFinset_succ, mem_mul]
  exact ⟨g, hg, 1, h1, mul_one g⟩

/-! ### Part 3: Card growth via Cauchy-Davenport -/

/-- When `minOrder G = |G|`, the Cauchy-Davenport bound simplifies:
    `|A * B| >= min(|G|, |A| + |B| - 1)`. -/
theorem cd_card_bound (hmo : minOrder G = Fintype.card G)
    (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty) :
    min (Fintype.card G) (A.card + B.card - 1) ≤ (A * B).card := by
  have h := cauchy_davenport_minOrder_mul hA hB
  rw [hmo] at h
  simp only [min_le_iff, Nat.cast_le] at h ⊢
  exact h

/-! ### Part 4: Iterated Cauchy-Davenport card growth -/

/-- Iterated Cauchy-Davenport: the card of the iterated product is at least
    `min(|G|, 1 + ∑_{k<n} (|S k| - 1))` when `minOrder G = |G|`. -/
theorem iteratedMulFinset_card_growth (hmo : minOrder G = Fintype.card G)
    (S : ℕ → Finset G) (hS : ∀ k, (S k).Nonempty) :
    ∀ n, min (Fintype.card G) (1 + ∑ k ∈ Finset.range n, ((S k).card - 1)) ≤
      (iteratedMulFinset S n).card := by
  intro n
  induction n with
  | zero =>
    simp [iteratedMulFinset_zero, Finset.card_singleton]
  | succ n ih =>
    have hne_prod := iteratedMulFinset_nonempty S hS n
    have hne_S := hS n
    have hScard := hne_S.card_pos
    have hcd := cd_card_bound hmo (iteratedMulFinset S n) (S n) hne_prod hne_S
    rw [iteratedMulFinset_succ, Finset.sum_range_succ]
    -- After rewrite, goal is:
    -- min(|G|, 1 + (∑_{k<n} (|S k| - 1) + (|S n| - 1))) ≤ |(P_n * S n)|
    -- Strategy: show LHS ≤ min(|G|, |P_n| + |S n| - 1) ≤ |(P_n * S n)|
    -- Strategy: show LHS ≤ min(|G|, |P_n| + |S n| - 1) ≤ RHS
    -- From ih: min(|G|, 1 + ∑_{k<n}) ≤ |P_n|
    -- Case 1: 1 + ∑ ≤ |G|, so (1 + ∑) ≤ |P_n|
    --   Then (1 + ∑) + c ≤ |P_n| + c = |P_n| + |S n| - 1
    --   So min(|G|, (1+∑)+c) ≤ min(|G|, |P_n|+|S n|-1) ≤ RHS
    -- Case 2: |G| < 1 + ∑
    --   Then min(|G|, anything ≥ |G|) = |G|
    --   And |G| ≤ |P_n| + |S n| - 1 (from min(|G|,·) ≤ |P_n| and |S n| ≥ 1)
    --   So min(|G|, |P_n|+|S n|-1) = |G|, done.
    by_cases h : 1 + ∑ k ∈ Finset.range n, ((S k).card - 1) ≤ Fintype.card G
    · -- Case 1
      have h1sm_le : 1 + ∑ k ∈ Finset.range n, ((S k).card - 1) ≤
          (iteratedMulFinset S n).card := by
        rwa [min_eq_right h] at ih
      -- Now: 1 + (∑ + c) = (1+∑) + c ≤ |P_n| + c = |P_n| + |S n| - 1
      have hle : 1 + (∑ k ∈ Finset.range n, ((S k).card - 1) + ((S n).card - 1)) ≤
          (iteratedMulFinset S n).card + (S n).card - 1 := by omega
      exact le_trans (min_le_min_left _ hle) hcd
    · -- Case 2: |G| < 1 + ∑
      push_neg at h
      have hG_le : Fintype.card G ≤
          1 + (∑ k ∈ Finset.range n, ((S k).card - 1) + ((S n).card - 1)) := by omega
      rw [min_eq_left hG_le]
      -- Need: |G| ≤ |(P_n * S n)|
      -- From ih: |G| ≤ min(|G|, 1+∑) ≤ |P_n| ... no, min(|G|, 1+∑) ≤ |P_n|
      -- Since |G| < 1+∑, min(|G|, 1+∑) = |G|, so |G| ≤ |P_n|
      have hG_P : Fintype.card G ≤ (iteratedMulFinset S n).card := by
        have := ih; rw [min_eq_left (le_of_lt h)] at this; exact this
      -- |P_n| ≤ |G| by card_le_univ, so |P_n| = |G|
      have hP_univ := Finset.card_le_univ (iteratedMulFinset S n)
      have hPeq : (iteratedMulFinset S n).card = Fintype.card G := le_antisymm hP_univ hG_P
      -- So P_n = univ, hence P_n * S n = univ
      have hP_is_univ : iteratedMulFinset S n = Finset.univ := by
        rwa [← Finset.card_eq_iff_eq_univ]
      rw [hP_is_univ]
      -- |univ * S n| ≥ |S n| ≥ 1, and also ≥ |univ| = |G| by card_le_card_mul_left
      have : (Finset.univ : Finset G).card ≤ (Finset.univ * S n).card :=
        Finset.card_le_card_mul_right hne_S
      rwa [Finset.card_univ] at this

/-! ### Part 5: The product equals univ after enough steps -/

omit [CommGroup G] [DecidableEq G] in
private theorem finset_eq_univ_of_card_ge (A : Finset G) (h : Fintype.card G ≤ A.card) :
    A = Finset.univ := by
  rw [← Finset.card_eq_iff_eq_univ]
  exact le_antisymm (Finset.card_le_univ A) h

/-- If `minOrder G = |G|` and each set has card >= 2, then after `D >= |G| - 1` steps
    the iterated product equals `Finset.univ`. -/
theorem iteratedMulFinset_eq_univ (hmo : minOrder G = Fintype.card G)
    (hcard_pos : 0 < Fintype.card G)
    (S : ℕ → Finset G) (hS : ∀ k, (S k).Nonempty)
    (hS2 : ∀ k, 2 ≤ (S k).card)
    {D : ℕ} (hD : Fintype.card G - 1 ≤ D) :
    iteratedMulFinset S D = Finset.univ := by
  apply finset_eq_univ_of_card_ge
  have hgrowth := iteratedMulFinset_card_growth hmo S hS D
  suffices h : Fintype.card G ≤ 1 + ∑ k ∈ Finset.range D, ((S k).card - 1) by
    rw [min_eq_left h] at hgrowth; exact hgrowth
  have hsum : D ≤ ∑ k ∈ Finset.range D, ((S k).card - 1) := by
    calc D = ∑ _k ∈ Finset.range D, 1 := by simp
      _ ≤ ∑ k ∈ Finset.range D, ((S k).card - 1) := by
          apply Finset.sum_le_sum; intro k _; have := hS2 k; omega
  omega

/-! ### Part 6: Element membership and diameter -/

/-- Any target element is reached after `|G| - 1` steps. -/
theorem target_reached (hmo : minOrder G = Fintype.card G)
    (hcard_pos : 0 < Fintype.card G)
    (S : ℕ → Finset G) (hS : ∀ k, (S k).Nonempty) (hS2 : ∀ k, 2 ≤ (S k).card)
    (a : G) :
    a ∈ iteratedMulFinset S (Fintype.card G - 1) := by
  rw [iteratedMulFinset_eq_univ hmo hcard_pos S hS hS2 le_rfl]
  exact Finset.mem_univ a

/-- The diameter of a group under iterated multiplication by sets of size >= 2
    is at most `|G| - 1`. -/
theorem iterated_product_diameter (hmo : minOrder G = Fintype.card G)
    (hcard_pos : 0 < Fintype.card G)
    (S : ℕ → Finset G) (hS : ∀ k, (S k).Nonempty) (hS2 : ∀ k, 2 ≤ (S k).card) :
    iteratedMulFinset S (Fintype.card G - 1) = Finset.univ :=
  iteratedMulFinset_eq_univ hmo hcard_pos S hS hS2 le_rfl

/-! ### Part 7: Connection to factor bags -/

section Application
open Mullin MullinGroup

/-- The iterated product of factor unit sets covers (ZMod q)x when each factor set
    has size >= 2 and enough steps are taken. This is an open hypothesis connecting
    the abstract coverage lemma to EM-specific factor sets. -/
def FactorBagCoverage (q : ℕ) : Prop :=
  ∀ [Fact (Nat.Prime q)], ∀ (S : ℕ → Finset (ZMod q)ˣ),
    (∀ k, (S k).Nonempty) →
    (∀ k, 2 ≤ (S k).card) →
    ∀ a : (ZMod q)ˣ, a ∈ iteratedMulFinset S (Fintype.card (ZMod q)ˣ - 1)

end Application

/-! ### Part 8: Instantiation for units of ZMod p (safe prime case) -/

section PrimeCyclic

/-- For prime p where p-1 is also prime (safe prime), `(ZMod p)x` has prime order,
    so `minOrder = p-1 = |G|` and the coverage theorem applies. -/
theorem minOrder_units_zmod_safe_prime
    {p : ℕ} [Fact (Nat.Prime p)] (hp_sub : Nat.Prime (p - 1)) :
    minOrder (ZMod p)ˣ = Fintype.card (ZMod p)ˣ := by
  have hp := Fact.out (self := ‹Fact (Nat.Prime p)›)
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hp]
  -- (ZMod p)× has order p-1 which is prime.
  -- Every nontrivial element has order p-1 by Lagrange.
  -- So minOrder = p-1.
  apply le_antisymm
  · -- minOrder ≤ p-1: there exists a nontrivial element of finite order
    have hp2 : 2 ≤ p - 1 := hp_sub.two_le
    have : Nontrivial (ZMod p)ˣ := by
      rw [← Fintype.one_lt_card_iff_nontrivial, hcard]; omega
    obtain ⟨a, ha⟩ := exists_ne (1 : (ZMod p)ˣ)
    have h1 : minOrder (ZMod p)ˣ ≤ orderOf a :=
      minOrder_le_orderOf ha (isOfFinOrder_of_finite a)
    have h2 : orderOf a ≤ Fintype.card (ZMod p)ˣ := by
      rw [← Nat.card_eq_fintype_card]; exact orderOf_le_card
    exact h1.trans (WithTop.coe_le_coe.mpr h2)
  · -- p-1 ≤ minOrder: every nontrivial element has order = p-1
    rw [le_minOrder]
    intro a ha ha'
    have hdvd : orderOf a ∣ Fintype.card (ZMod p)ˣ := orderOf_dvd_card
    rw [hcard] at hdvd
    rcases hp_sub.eq_one_or_self_of_dvd _ hdvd with h1 | heq
    · exact absurd (orderOf_eq_one_iff.mp h1) ha
    · rw [heq, hcard]

/-- For safe primes (p and p-1 both prime), the iterated product of sets of size >= 2
    in (ZMod p)x covers the group after p-2 steps. -/
theorem safe_prime_coverage {p : ℕ} [hp : Fact (Nat.Prime p)]
    (hp_sub : Nat.Prime (p - 1))
    (S : ℕ → Finset (ZMod p)ˣ) (hS : ∀ k, (S k).Nonempty) (hS2 : ∀ k, 2 ≤ (S k).card)
    (a : (ZMod p)ˣ) :
    a ∈ iteratedMulFinset S (Fintype.card (ZMod p)ˣ - 1) := by
  have hmo := minOrder_units_zmod_safe_prime hp_sub
  have hcard_pos : 0 < Fintype.card (ZMod p)ˣ := Fintype.card_pos
  exact target_reached hmo hcard_pos S hS hS2 a

end PrimeCyclic

/-! ### Part 9: General minOrder criterion -/

/-- For ANY finite commutative group where minOrder = card, iterated products of
    sets with card >= 2 cover the entire group. This is a purely group-theoretic
    statement with no number-theoretic content. -/
theorem general_coverage_criterion
    (hmo : minOrder G = Fintype.card G)
    (S : ℕ → Finset G) (hS : ∀ k, (S k).Nonempty) (hS2 : ∀ k, 2 ≤ (S k).card)
    (a : G) :
    a ∈ iteratedMulFinset S (Fintype.card G - 1) := by
  have hcard_pos : 0 < Fintype.card G := Fintype.card_pos
  exact target_reached hmo hcard_pos S hS hS2 a

/-! ### Part 10: Landscape theorem -/

/-- Summary of iterated product coverage results. -/
theorem iterated_product_coverage_landscape
    (hmo : minOrder G = Fintype.card G) (hcard_pos : 0 < Fintype.card G) :
    -- (1) Card growth: iterated Cauchy-Davenport bound
    (∀ (S : ℕ → Finset G), (∀ k, (S k).Nonempty) →
      ∀ n, min (Fintype.card G) (1 + ∑ k ∈ Finset.range n, ((S k).card - 1)) ≤
        (iteratedMulFinset S n).card) ∧
    -- (2) Full coverage: product = univ after |G| - 1 steps with sets of size >= 2
    (∀ (S : ℕ → Finset G), (∀ k, (S k).Nonempty) → (∀ k, 2 ≤ (S k).card) →
      iteratedMulFinset S (Fintype.card G - 1) = Finset.univ) ∧
    -- (3) Element reached: any target is in the product
    (∀ (S : ℕ → Finset G), (∀ k, (S k).Nonempty) → (∀ k, 2 ≤ (S k).card) →
      ∀ a : G, a ∈ iteratedMulFinset S (Fintype.card G - 1)) :=
  ⟨fun S hS => iteratedMulFinset_card_growth hmo S hS,
   fun S hS hS2 => iterated_product_diameter hmo hcard_pos S hS hS2,
   fun S hS hS2 a => target_reached hmo hcard_pos S hS hS2 a⟩

/-! ### Part 11: minOrder of (ZMod q)x equals 2 for primes q >= 3

The element -1 in (ZMod q)x has order 2 (since (-1)^2 = 1 and -1 != 1 for q >= 3).
Since 2 is the smallest prime, minOrder <= 2. Also minOrder >= 2 (since every nontrivial
element has order >= 2). So minOrder = 2.

This means the Cauchy-Davenport bound via minOrder gives only
  |A * B| >= min(2, |A| + |B| - 1) = 2
which is vacuous -- any product of nonempty sets has cardinality >= 2 when |A|, |B| >= 2.
-/

section MinOrderUnits

/-- orderOf (-1 : (ZMod q)x) = 2 for prime q >= 3. -/
private theorem orderOf_neg_one_units_zmod {q : ℕ} [Fact (Nat.Prime q)] (hq : 3 ≤ q) :
    orderOf (-1 : (ZMod q)ˣ) = 2 := by
  have hq2 : q ≠ 2 := by omega
  rw [← orderOf_units, Units.coe_neg_one, orderOf_neg_one,
    ZMod.ringChar_zmod_n q, if_neg hq2]

/-- -1 is not the identity in (ZMod q)x for q >= 3. -/
private theorem neg_one_ne_one_units_zmod {q : ℕ} [Fact (Nat.Prime q)] (hq : 3 ≤ q) :
    (-1 : (ZMod q)ˣ) ≠ 1 := by
  intro h
  have : orderOf (-1 : (ZMod q)ˣ) = 2 := orderOf_neg_one_units_zmod hq
  rw [h, orderOf_one] at this
  omega

/-- The minimum order of (ZMod q)x equals 2 for all primes q >= 3.

This is because -1 has order 2 (giving minOrder <= 2) and every nontrivial
element has order >= 2 (giving minOrder >= 2). -/
theorem minOrder_units_zmod_eq_two {q : ℕ} [Fact (Nat.Prime q)] (hq : 3 ≤ q) :
    minOrder (ZMod q)ˣ = 2 := by
  apply le_antisymm
  · -- minOrder <= orderOf(-1) = 2
    have hne : (-1 : (ZMod q)ˣ) ≠ 1 := neg_one_ne_one_units_zmod hq
    have hfin : IsOfFinOrder (-1 : (ZMod q)ˣ) := isOfFinOrder_of_finite _
    have h := minOrder_le_orderOf hne hfin
    rw [orderOf_neg_one_units_zmod hq] at h
    exact h
  · -- 2 <= minOrder: every nontrivial element has order >= 2
    rw [le_minOrder]
    intro a ha ha'
    have h1 : orderOf a ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
    have hpos : 0 < orderOf a := IsOfFinOrder.orderOf_pos ha'
    exact_mod_cast (show 2 ≤ orderOf a by omega)

/-! ### Part 12: Cauchy-Davenport bound is trivial for (ZMod q)x

Since minOrder = 2, the Cauchy-Davenport theorem gives only
  |A * B| >= min(2, |A| + |B| - 1)
which equals 2 whenever |A|, |B| >= 2. This provides NO growth information
beyond what is already trivially true.
-/

/-- The Cauchy-Davenport bound via minOrder gives at most 2 for (ZMod q)x. -/
theorem cd_bound_trivial {q : ℕ} [Fact (Nat.Prime q)] (hq : 3 ≤ q)
    (A B : Finset (ZMod q)ˣ) :
    min (minOrder (ZMod q)ˣ) (A.card + B.card - 1) ≤ 2 := by
  rw [minOrder_units_zmod_eq_two hq]
  exact min_le_left 2 _

/-! ### Part 13: Safe prime characterization

If q and q-1 are both prime, then q = 3. This is because q >= 3 (prime and >= 2)
implies q is odd, so q-1 is even, and the only even prime is 2, forcing q-1 = 2
and q = 3. This means `safe_prime_coverage` (Part 8) applies ONLY to q = 3.
-/

/-- If q is prime and q-1 is also prime, then q = 3.

Proof: q prime and q >= 3 implies q is odd, so q-1 is even.
Since q-1 is prime and even, q-1 = 2, hence q = 3. -/
theorem prime_sub_one_prime_implies_eq_three {q : ℕ} (hq : Nat.Prime q) (hq1 : Nat.Prime (q - 1)) :
    q = 3 := by
  -- q = 2 is impossible since q - 1 = 1 is not prime
  have hq_ne2 : q ≠ 2 := by intro h; rw [h] at hq1; exact Nat.not_prime_one hq1
  -- q is odd (prime and not 2), so 2 | (q - 1)
  have h2dvd : 2 ∣ q - 1 := by
    have : 2 ∣ q ↔ q = 2 := by
      constructor
      · intro h; rcases hq.eq_one_or_self_of_dvd 2 h with h | h <;> omega
      · intro h; rw [h]
    omega
  -- q - 1 is prime and 2 | (q - 1), so q - 1 = 2
  rcases hq1.eq_one_or_self_of_dvd 2 h2dvd with h | h <;> omega

/-! ### Part 14: Dead End #137 — Cauchy-Davenport via minOrder is vacuous

**Dead End #137**: The Cauchy-Davenport approach via `minOrder` is vacuous for
`(ZMod q)x` when `q >= 5`.

**Why**: `minOrder (ZMod q)x = 2` for ALL primes `q >= 3`. The Cauchy-Davenport
theorem gives `|A * B| >= min(minOrder, |A| + |B| - 1) = min(2, |A| + |B| - 1) = 2`
whenever `|A|, |B| >= 2`. This is trivially true and provides no growth information.

**The safe prime case**: `safe_prime_coverage` (Part 8) requires `minOrder = |G|`, which
holds only when `|G| = q - 1` is prime. Since `q` and `q - 1` being both prime forces
`q = 3`, the coverage result is nontrivial ONLY for `q = 3` (where `|G| = 2`).
For `q = 3`, the group has order 2, so one step trivially suffices.

**What would fix this**: Kneser's theorem (not in Mathlib) gives
`|A * B| >= |A| + |B| - |H|` where `H = {g : g * (A * B) = A * B}` is the stabilizer.
When `A * B != G`, the stabilizer `H` is a proper subgroup, so `|H|` divides `|G|`
and is at most `|G|/2`. For non-full products, Kneser gives genuine growth.
-/

/-- Dead End #137 landscape: Cauchy-Davenport via minOrder is vacuous for (ZMod q)x.
    (1) minOrder = 2 for all primes q >= 3
    (2) The safe prime condition (q-1 prime) forces q = 3
    (3) The CD bound gives only min(2, |A|+|B|-1) which is at most 2
-/
theorem iterated_product_dead_end_landscape {q : ℕ} [Fact (Nat.Prime q)] (hq : 3 ≤ q) :
    -- (1) minOrder = 2
    minOrder (ZMod q)ˣ = 2 ∧
    -- (2) safe_prime_coverage applies only when q-1 is prime, forcing q = 3
    (Nat.Prime (q - 1) → q = 3) ∧
    -- (3) The CD bound is at most 2
    (∀ (A B : Finset (ZMod q)ˣ),
      min (minOrder (ZMod q)ˣ) (A.card + B.card - 1) ≤ 2) :=
  ⟨minOrder_units_zmod_eq_two hq,
   prime_sub_one_prime_implies_eq_three (Fact.out),
   fun A B => cd_bound_trivial hq A B⟩

end MinOrderUnits

end IteratedProduct
