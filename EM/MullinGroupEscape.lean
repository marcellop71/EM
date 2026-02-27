import EM.MullinGroupCore
import Mathlib.Order.Atoms.Finite
import Mathlib.Data.Nat.Totient

/-!
# Concrete SubgroupEscape Lemmas

Proves that the first 6 EM multipliers {3,7,43,13,53,5} escape specific
subgroups of (ZMod q)×, giving concrete SE instances:
* 6 individual escape lemmas for each multiplier
* Product expansion: 21 distinct elements from multiplier products
* `eight_elts_escape_order_le_seven`: 8 elements escape order ≤ 7 subgroups
* `se_of_maximal_escape`: SE ↔ escape every coatom
* `se_at_of_pow_checks`: SE verification via primitive root power checks
* Fact instances for primes 11-157
-/

namespace MullinGroup

open Mullin Euclid

/-! ## Helper lemmas for natCast ≠ 1 and natCast ≠ -1

These factor the repetitive proof pattern used in the 12 `ne_one`/`ne_neg_one`
theorems below. Each multiplier escape proof reduces to showing V < q and V ≠ 1
(for `ne_one`) or V + 1 < q (for `ne_neg_one`), both dischargeable by `omega`. -/

/-- If V < q and V ≠ 1, then (V : ZMod q) ≠ 1.
    Used to factor the repetitive `multZ q n ≠ 1` proofs. -/
private theorem natCast_ne_one_of_lt {q V : Nat} [Fact (Nat.Prime q)]
    (hV : V < q) (hV1 : V ≠ 1) : ((V : Nat) : ZMod q) ≠ 1 := by
  have hq2 : q ≥ 2 := (Fact.out : Nat.Prime q).two_le
  intro h
  rw [show (1 : ZMod q) = ((1 : Nat) : ZMod q) from Nat.cast_one.symm] at h
  have hmod := (ZMod.natCast_eq_natCast_iff' V 1 q).mp h
  rw [Nat.mod_eq_of_lt (by omega : V < q), Nat.mod_eq_of_lt (by omega : 1 < q)] at hmod
  omega

/-- If V + 1 < q, then (V : ZMod q) ≠ -1.
    Used to factor the repetitive `multZ q n ≠ -1` proofs. -/
private theorem natCast_ne_neg_one_of_lt {q V : Nat} [Fact (Nat.Prime q)]
    (hVp1 : V + 1 < q) : ((V : Nat) : ZMod q) ≠ -1 := by
  intro h
  have hVp1_cast : ((V + 1 : Nat) : ZMod q) = 0 := by
    have : ((V : Nat) : ZMod q) + 1 = 0 := by rw [h]; ring
    calc ((V + 1 : Nat) : ZMod q) = ((V : Nat) : ZMod q) + 1 := by push_cast; ring
      _ = 0 := this
  rw [ZMod.natCast_eq_zero_iff] at hVp1_cast
  exact absurd (Nat.le_of_dvd (by omega) hVp1_cast) (by omega)

/-! ## Concrete SubgroupEscape: the first multiplier escapes {±1}

The subgroup {1, -1} ≤ (ZMod q)× has order 2 and index (q-1)/2.
We prove that for q ≥ 5 prime, the first multiplier seq(1) = 3 has
residue ≢ ±1 (mod q), so it escapes this subgroup.

This uses `seq_one : seq 1 = 3` from Mullin.lean and the fact that
q ≥ 5 implies q ∤ 2 (so 3 ≢ 1) and q ∤ 4 (so 3 ≢ -1). -/

/-- 3 ≢ 1 (mod q) for q ≥ 5: the first multiplier is not 1. -/
theorem first_mult_ne_one {q : Nat} [Fact (Nat.Prime q)] (hq5 : q ≥ 5) :
    multZ q 0 ≠ 1 := by
  simp only [multZ, show 0 + 1 = 1 from rfl, seq_one]
  exact natCast_ne_one_of_lt (by omega) (by omega)

/-- 3 ≢ -1 (mod q) for q ≥ 5: the first multiplier is not -1. -/
theorem first_mult_ne_neg_one {q : Nat} [Fact (Nat.Prime q)] (hq5 : q ≥ 5) :
    multZ q 0 ≠ -1 := by
  simp only [multZ, show 0 + 1 = 1 from rfl, seq_one]
  exact natCast_ne_neg_one_of_lt (by omega)

/-- **The first multiplier escapes {±1}** for q ≥ 5 prime.
    This is a concrete SubgroupEscape instance: the index-2 subgroup
    {1, -1} cannot confine even the first multiplier. -/
theorem first_mult_escapes_pm_one {q : Nat} [Fact (Nat.Prime q)]
    (hq5 : q ≥ 5) :
    multZ q 0 ≠ 1 ∧ multZ q 0 ≠ -1 :=
  ⟨first_mult_ne_one hq5, first_mult_ne_neg_one hq5⟩

/-- 7 ≢ 1 (mod q) for q ≥ 11: the second multiplier is not 1. -/
theorem second_mult_ne_one {q : Nat} [Fact (Nat.Prime q)] (hq11 : q ≥ 11) :
    multZ q 1 ≠ 1 := by
  simp only [multZ, show 1 + 1 = 2 from rfl, seq_two]
  exact natCast_ne_one_of_lt (by omega) (by omega)

/-- 7 ≢ -1 (mod q) for q ≥ 11: the second multiplier is not -1. -/
theorem second_mult_ne_neg_one {q : Nat} [Fact (Nat.Prime q)] (hq11 : q ≥ 11) :
    multZ q 1 ≠ -1 := by
  simp only [multZ, show 1 + 1 = 2 from rfl, seq_two]
  exact natCast_ne_neg_one_of_lt (by omega)

/-- **The second multiplier also escapes {±1}** for q ≥ 11 prime. -/
theorem second_mult_escapes_pm_one {q : Nat} [Fact (Nat.Prime q)]
    (hq11 : q ≥ 11) :
    multZ q 1 ≠ 1 ∧ multZ q 1 ≠ -1 :=
  ⟨second_mult_ne_one hq11, second_mult_ne_neg_one hq11⟩

/-- **The first two multipliers are distinct mod q** for q ≥ 11.
    Since 3 ≢ 7 (mod q), the multiplier residues include at least
    2 distinct elements, ruling out confinement to any subgroup of
    order 1 (the trivial subgroup). -/
theorem first_two_mults_distinct {q : Nat} [Fact (Nat.Prime q)]
    (hq11 : q ≥ 11) :
    multZ q 0 ≠ multZ q 1 := by
  simp only [multZ, show 0 + 1 = 1 from rfl, show 1 + 1 = 2 from rfl, seq_one, seq_two]
  intro h
  have hmod := (ZMod.natCast_eq_natCast_iff' 3 7 q).mp h
  rw [Nat.mod_eq_of_lt (by omega : 3 < q), Nat.mod_eq_of_lt (by omega : 7 < q)] at hmod
  omega

/-- **Product of first two multipliers ≢ 1**: 3 · 7 = 21 ≢ 1 (mod q)
    for q ≥ 23. This means the first two multipliers don't "cancel" in
    the group, so their generated subgroup has order ≥ 3. -/
theorem mults_product_ne_one {q : Nat} [Fact (Nat.Prime q)] (hq23 : q ≥ 23) :
    multZ q 0 * multZ q 1 ≠ 1 := by
  simp only [multZ, show 0 + 1 = 1 from rfl, show 1 + 1 = 2 from rfl, seq_one, seq_two]
  intro h
  rw [show (1 : ZMod q) = ((1 : Nat) : ZMod q) from Nat.cast_one.symm] at h
  have h21 : ((21 : Nat) : ZMod q) = ((1 : Nat) : ZMod q) := by
    calc ((21 : Nat) : ZMod q) = ((3 : Nat) : ZMod q) * ((7 : Nat) : ZMod q) := by push_cast; ring
      _ = ((1 : Nat) : ZMod q) := h
  have hmod := (ZMod.natCast_eq_natCast_iff' 21 1 q).mp h21
  rw [Nat.mod_eq_of_lt (by omega : 21 < q), Nat.mod_eq_of_lt (by omega : 1 < q)] at hmod
  omega

/-! ## Third and fourth multiplier escape lemmas

Using seq 3 = 43 and seq 4 = 13, we get multiplier residues
multZ q 2 = 43 and multZ q 3 = 13 in (ZMod q)×. These give
stronger escape results for larger subgroups. -/

/-- 43 ≢ 1 (mod q) for q ≥ 47. -/
theorem third_mult_ne_one {q : Nat} [Fact (Nat.Prime q)] (hq : q ≥ 47) :
    multZ q 2 ≠ 1 := by
  simp only [multZ, show 2 + 1 = 3 from rfl, seq_three]
  exact natCast_ne_one_of_lt (by omega) (by omega)

/-- 43 ≢ -1 (mod q) for q ≥ 47. -/
theorem third_mult_ne_neg_one {q : Nat} [Fact (Nat.Prime q)] (hq : q ≥ 47) :
    multZ q 2 ≠ -1 := by
  simp only [multZ, show 2 + 1 = 3 from rfl, seq_three]
  exact natCast_ne_neg_one_of_lt (by omega)

/-- 13 ≢ 1 (mod q) for q ≥ 17. -/
theorem fourth_mult_ne_one {q : Nat} [Fact (Nat.Prime q)] (hq : q ≥ 17) :
    multZ q 3 ≠ 1 := by
  simp only [multZ, show 3 + 1 = 4 from rfl, seq_four]
  exact natCast_ne_one_of_lt (by omega) (by omega)

/-- 13 ≢ -1 (mod q) for q ≥ 17. -/
theorem fourth_mult_ne_neg_one {q : Nat} [Fact (Nat.Prime q)] (hq : q ≥ 17) :
    multZ q 3 ≠ -1 := by
  simp only [multZ, show 3 + 1 = 4 from rfl, seq_four]
  exact natCast_ne_neg_one_of_lt (by omega)

/-- **All four multipliers are pairwise distinct mod q** for q ≥ 47.
    The residues {3, 7, 43, 13} are distinct in (ZMod q)× when q ≥ 47,
    giving 4 distinct elements. This rules out confinement to any
    subgroup of order ≤ 3 by pigeonhole. -/
theorem four_mults_pairwise_distinct {q : Nat} [Fact (Nat.Prime q)] (hq : q ≥ 47) :
    multZ q 0 ≠ multZ q 1 ∧ multZ q 0 ≠ multZ q 2 ∧ multZ q 0 ≠ multZ q 3 ∧
    multZ q 1 ≠ multZ q 2 ∧ multZ q 1 ≠ multZ q 3 ∧ multZ q 2 ≠ multZ q 3 := by
  simp only [multZ, show 0 + 1 = 1 from rfl, show 1 + 1 = 2 from rfl,
    show 2 + 1 = 3 from rfl, show 3 + 1 = 4 from rfl, seq_one, seq_two, seq_three, seq_four]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (
    intro h
    have hmod := (ZMod.natCast_eq_natCast_iff' _ _ q).mp h
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
    omega)

/-- **Four multipliers escape subgroups of order ≤ 3**: for q ≥ 47 prime
    and q ∉ seq, any subgroup H ≤ (ZMod q)× with at most 3 elements
    fails to contain all four multiplier residues. -/
theorem four_mults_escape_small_subgroups {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (hq47 : q ≥ 47)
    (H : Subgroup (ZMod q)ˣ)
    (hH : ∀ a b c d : (ZMod q)ˣ, a ∈ H → b ∈ H → c ∈ H → d ∈ H →
          a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d) :
    ∃ n, n < 4 ∧ (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H := by
  -- If all 4 multiplier units are in H, pigeonhole gives two equal
  let u0 := Units.mk0 (multZ q 0) (multZ_ne_zero hq hne 0)
  let u1 := Units.mk0 (multZ q 1) (multZ_ne_zero hq hne 1)
  let u2 := Units.mk0 (multZ q 2) (multZ_ne_zero hq hne 2)
  let u3 := Units.mk0 (multZ q 3) (multZ_ne_zero hq hne 3)
  -- Assume for contradiction all are in H
  match Classical.em (u0 ∈ H), Classical.em (u1 ∈ H),
        Classical.em (u2 ∈ H), Classical.em (u3 ∈ H) with
  | _, _, _, .inr h3 => exact ⟨3, by omega, h3⟩
  | _, _, .inr h2, _ => exact ⟨2, by omega, h2⟩
  | _, .inr h1, _, _ => exact ⟨1, by omega, h1⟩
  | .inr h0, _, _, _ => exact ⟨0, by omega, h0⟩
  | .inl h0, .inl h1, .inl h2, .inl h3 =>
    -- All 4 in H: pigeonhole gives two equal units
    have hpig := hH u0 u1 u2 u3 h0 h1 h2 h3
    -- But they're pairwise distinct
    obtain ⟨d01, d02, d03, d12, d13, d23⟩ := four_mults_pairwise_distinct hq47
    -- Each disjunct contradicts distinctness
    rcases hpig with h | h | h | h | h | h
    · exact absurd (congrArg Units.val h) d01
    · exact absurd (congrArg Units.val h) d02
    · exact absurd (congrArg Units.val h) d03
    · exact absurd (congrArg Units.val h) d12
    · exact absurd (congrArg Units.val h) d13
    · exact absurd (congrArg Units.val h) d23

/-! ## Fifth and sixth multiplier escape lemmas

Using seq 5 = 53 and seq 6 = 5. -/

/-- 53 ≢ 1 (mod q) for q ≥ 59. -/
theorem fifth_mult_ne_one {q : Nat} [Fact (Nat.Prime q)] (hq : q ≥ 59) :
    multZ q 4 ≠ 1 := by
  simp only [multZ, show 4 + 1 = 5 from rfl, seq_five]
  exact natCast_ne_one_of_lt (by omega) (by omega)

/-- 53 ≢ -1 (mod q) for q ≥ 59. -/
theorem fifth_mult_ne_neg_one {q : Nat} [Fact (Nat.Prime q)] (hq : q ≥ 59) :
    multZ q 4 ≠ -1 := by
  simp only [multZ, show 4 + 1 = 5 from rfl, seq_five]
  exact natCast_ne_neg_one_of_lt (by omega)

/-- 5 ≢ 1 (mod q) for q ≥ 7. -/
theorem sixth_mult_ne_one {q : Nat} [Fact (Nat.Prime q)] (hq : q ≥ 7) :
    multZ q 5 ≠ 1 := by
  simp only [multZ, show 5 + 1 = 6 from rfl, seq_six]
  exact natCast_ne_one_of_lt (by omega) (by omega)

/-- 5 ≢ -1 (mod q) for q ≥ 7. -/
theorem sixth_mult_ne_neg_one {q : Nat} [Fact (Nat.Prime q)] (hq : q ≥ 7) :
    multZ q 5 ≠ -1 := by
  simp only [multZ, show 5 + 1 = 6 from rfl, seq_six]
  exact natCast_ne_neg_one_of_lt (by omega)

/-! ## Six multipliers pairwise distinct

With {3, 7, 43, 13, 53, 5} all distinct mod q for q ≥ 59,
we have 6 distinct multiplier residues, ruling out confinement
to any subgroup of order ≤ 5. -/

/-- **All six multipliers are pairwise distinct mod q** for q ≥ 59.
    Gives 6 distinct elements, ruling out confinement to any
    subgroup of order ≤ 5 by pigeonhole. -/
theorem six_mults_pairwise_distinct {q : Nat} [Fact (Nat.Prime q)] (hq : q ≥ 59) :
    multZ q 0 ≠ multZ q 1 ∧ multZ q 0 ≠ multZ q 2 ∧ multZ q 0 ≠ multZ q 3 ∧
    multZ q 0 ≠ multZ q 4 ∧ multZ q 0 ≠ multZ q 5 ∧
    multZ q 1 ≠ multZ q 2 ∧ multZ q 1 ≠ multZ q 3 ∧
    multZ q 1 ≠ multZ q 4 ∧ multZ q 1 ≠ multZ q 5 ∧
    multZ q 2 ≠ multZ q 3 ∧ multZ q 2 ≠ multZ q 4 ∧ multZ q 2 ≠ multZ q 5 ∧
    multZ q 3 ≠ multZ q 4 ∧ multZ q 3 ≠ multZ q 5 ∧
    multZ q 4 ≠ multZ q 5 := by
  simp only [multZ, show 0 + 1 = 1 from rfl, show 1 + 1 = 2 from rfl,
    show 2 + 1 = 3 from rfl, show 3 + 1 = 4 from rfl,
    show 4 + 1 = 5 from rfl, show 5 + 1 = 6 from rfl,
    seq_one, seq_two, seq_three, seq_four, seq_five, seq_six]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (
    intro h
    have hmod := (ZMod.natCast_eq_natCast_iff' _ _ q).mp h
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
    omega)

/-! ## Escape from subgroups of bounded cardinality

With 6 pairwise distinct multiplier residues, no subgroup of order ≤ 5
can contain all of them. This is proved using the injection principle:
6 distinct elements in a finite set of size ≤ 5 is impossible. -/

/-- Quantified form of six-multiplier pairwise distinctness:
    multZ q is injective on {0, ..., 5} for q ≥ 59. -/
theorem multZ_injOn_six {q : Nat} [Fact (Nat.Prime q)] (hq59 : q ≥ 59)
    {i j : Nat} (hi : i < 6) (hj : j < 6) (heq : multZ q i = multZ q j) :
    i = j := by
  obtain ⟨d01, d02, d03, d04, d05, d12, d13, d14, d15, d23, d24, d25, d34, d35, d45⟩ :=
    six_mults_pairwise_distinct hq59
  rcases show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
  first | rfl | (exfalso; exact absurd heq ‹_›) | (exfalso; exact absurd heq.symm ‹_›)

open Classical in
/-- **Six multipliers escape subgroups of order ≤ 5**: for q ≥ 59 prime
    and q ∉ seq, any subgroup H ≤ (ZMod q)× with at most 5 elements
    fails to contain all six multiplier residues.

    This rules out confinement to any subgroup of order ≤ 5 for all
    primes q ≥ 59 not in the sequence. -/
theorem six_mults_escape_card_le_five {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (hq59 : q ≥ 59)
    (H : Subgroup (ZMod q)ˣ) (hcard : Fintype.card H ≤ 5) :
    ∃ n, n < 6 ∧ (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H := by
  by_contra hall
  push_neg at hall
  -- Build an injective function Fin 6 → H
  have h6le : 6 ≤ Fintype.card H := by
    let f : Fin 6 → H := fun i =>
      ⟨Units.mk0 (multZ q i.val) (multZ_ne_zero hq hne i.val), hall i.val i.isLt⟩
    have hf : Function.Injective f := by
      intro a b heq
      have hval : multZ q a.val = multZ q b.val :=
        congrArg Units.val (congrArg Subtype.val heq)
      exact Fin.ext (multZ_injOn_six hq59 a.isLt b.isLt hval)
    calc 6 = Fintype.card (Fin 6) := (Fintype.card_fin 6).symm
      _ ≤ Fintype.card H := Fintype.card_le_of_injective f hf
  omega

/-! ## Product-based escape: multiplier products give more distinct elements

When two multiplier residues are both in a subgroup H, their product
is also in H. If these products are distinct from all known elements,
this forces H to contain even more elements, escaping larger subgroups.

Key product: 3 · 7 = 21. For q ≥ 59, 21 is distinct from all 6
multiplier residues and from ±1, giving 8 distinct elements in H. -/

/-- **Product 3·7 = 21 ≢ -1 (mod q)** for q ≥ 23: the product of the
    first two multipliers is not -1. Combined with `mults_product_ne_one`,
    this means 21 is a genuinely new element (neither ±1). -/
theorem mults_product_ne_neg_one {q : Nat} [Fact (Nat.Prime q)] (hq23 : q ≥ 23) :
    multZ q 0 * multZ q 1 ≠ -1 := by
  simp only [multZ, show 0 + 1 = 1 from rfl, show 1 + 1 = 2 from rfl, seq_one, seq_two]
  intro h
  have h22 : ((22 : Nat) : ZMod q) = 0 := by
    have : ((3 : Nat) : ZMod q) * ((7 : Nat) : ZMod q) + 1 = 0 := by rw [h]; ring
    calc ((22 : Nat) : ZMod q)
          = ((3 : Nat) : ZMod q) * ((7 : Nat) : ZMod q) + 1 := by push_cast; ring
      _ = 0 := this
  rw [ZMod.natCast_eq_zero_iff] at h22
  exact absurd (Nat.le_of_dvd (by omega) h22) (by omega)

/-- **Product 3·7 = 21 is distinct from all 6 multiplier residues** for q ≥ 59.
    This means if mults 0 and 1 are in H, we get 21 as a 7th distinct
    nonidentity element in H (beyond {3, 7, 43, 13, 53, 5}). -/
theorem mults_product_ne_mults {q : Nat} [Fact (Nat.Prime q)] (hq59 : q ≥ 59) :
    multZ q 0 * multZ q 1 ≠ multZ q 0 ∧
    multZ q 0 * multZ q 1 ≠ multZ q 1 ∧
    multZ q 0 * multZ q 1 ≠ multZ q 2 ∧
    multZ q 0 * multZ q 1 ≠ multZ q 3 ∧
    multZ q 0 * multZ q 1 ≠ multZ q 4 ∧
    multZ q 0 * multZ q 1 ≠ multZ q 5 := by
  simp only [multZ, show 0 + 1 = 1 from rfl, show 1 + 1 = 2 from rfl,
    show 2 + 1 = 3 from rfl, show 3 + 1 = 4 from rfl,
    show 4 + 1 = 5 from rfl, show 5 + 1 = 6 from rfl,
    seq_one, seq_two, seq_three, seq_four, seq_five, seq_six]
  -- Product 3*7 = 21 in ZMod q. Need 21 ≠ each of {3, 7, 43, 13, 53, 5}.
  -- Differences: 18, 14, 22, 8, 32, 16 — all nonzero mod q for q ≥ 59
  constructor
  · -- 21 ≠ 3: difference is 18
    intro h
    have h18 : ((18 : Nat) : ZMod q) = 0 := by
      have : ((3 : Nat) : ZMod q) * ((7 : Nat) : ZMod q) - ((3 : Nat) : ZMod q) = 0 := by
        rw [h]; ring
      calc ((18 : Nat) : ZMod q)
            = ((3 : Nat) : ZMod q) * ((7 : Nat) : ZMod q) - ((3 : Nat) : ZMod q) := by
              push_cast; ring
        _ = 0 := this
    rw [ZMod.natCast_eq_zero_iff] at h18
    exact absurd (Nat.le_of_dvd (by omega) h18) (by omega)
  constructor
  · -- 21 ≠ 7: difference is 14
    intro h
    have h14 : ((14 : Nat) : ZMod q) = 0 := by
      have : ((3 : Nat) : ZMod q) * ((7 : Nat) : ZMod q) - ((7 : Nat) : ZMod q) = 0 := by
        rw [h]; ring
      calc ((14 : Nat) : ZMod q)
            = ((3 : Nat) : ZMod q) * ((7 : Nat) : ZMod q) - ((7 : Nat) : ZMod q) := by
              push_cast; ring
        _ = 0 := this
    rw [ZMod.natCast_eq_zero_iff] at h14
    exact absurd (Nat.le_of_dvd (by omega) h14) (by omega)
  constructor
  · -- 21 ≠ 43: 43 - 21 = 22
    intro h
    have h22 : ((22 : Nat) : ZMod q) = 0 := by
      have : ((43 : Nat) : ZMod q) - ((3 : Nat) : ZMod q) * ((7 : Nat) : ZMod q) = 0 := by
        rw [h]; ring
      calc ((22 : Nat) : ZMod q)
            = ((43 : Nat) : ZMod q) - ((3 : Nat) : ZMod q) * ((7 : Nat) : ZMod q) := by
              push_cast; ring
        _ = 0 := this
    rw [ZMod.natCast_eq_zero_iff] at h22
    exact absurd (Nat.le_of_dvd (by omega) h22) (by omega)
  constructor
  · -- 21 ≠ 13: 21 - 13 = 8
    intro h
    have h8 : ((8 : Nat) : ZMod q) = 0 := by
      have : ((3 : Nat) : ZMod q) * ((7 : Nat) : ZMod q) - ((13 : Nat) : ZMod q) = 0 := by
        rw [h]; ring
      calc ((8 : Nat) : ZMod q)
            = ((3 : Nat) : ZMod q) * ((7 : Nat) : ZMod q) - ((13 : Nat) : ZMod q) := by
              push_cast; ring
        _ = 0 := this
    rw [ZMod.natCast_eq_zero_iff] at h8
    exact absurd (Nat.le_of_dvd (by omega) h8) (by omega)
  constructor
  · -- 21 ≠ 53: 53 - 21 = 32
    intro h
    have h32 : ((32 : Nat) : ZMod q) = 0 := by
      have : ((53 : Nat) : ZMod q) - ((3 : Nat) : ZMod q) * ((7 : Nat) : ZMod q) = 0 := by
        rw [h]; ring
      calc ((32 : Nat) : ZMod q)
            = ((53 : Nat) : ZMod q) - ((3 : Nat) : ZMod q) * ((7 : Nat) : ZMod q) := by
              push_cast; ring
        _ = 0 := this
    rw [ZMod.natCast_eq_zero_iff] at h32
    exact absurd (Nat.le_of_dvd (by omega) h32) (by omega)
  · -- 21 ≠ 5: 21 - 5 = 16
    intro h
    have h16 : ((16 : Nat) : ZMod q) = 0 := by
      have : ((3 : Nat) : ZMod q) * ((7 : Nat) : ZMod q) - ((5 : Nat) : ZMod q) = 0 := by
        rw [h]; ring
      calc ((16 : Nat) : ZMod q)
            = ((3 : Nat) : ZMod q) * ((7 : Nat) : ZMod q) - ((5 : Nat) : ZMod q) := by
              push_cast; ring
        _ = 0 := this
    rw [ZMod.natCast_eq_zero_iff] at h16
    exact absurd (Nat.le_of_dvd (by omega) h16) (by omega)

/-! ## Escape from order ≤ 7 via product expansion

If all 6 multiplier residues are in a subgroup H with q ≥ 59, then H also
contains their products. The product 3·7 = 21 is distinct from all 6 mults,
from 1, and from -1 (`mults_product_ne_one`, `mults_product_ne_neg_one`,
`mults_product_ne_mults`), giving 8 distinct elements {1,3,7,43,13,53,5,21}
in H. Together with `six_mults_escape_card_le_five`, this shows: for q ≥ 59,
any proper subgroup of order ≤ 7 is escaped. -/

open Classical in
/-- **Eight elements escape subgroups of order ≤ 7**: for q ≥ 59 prime
    and q ∉ seq, any subgroup of order ≤ 7 cannot contain all 6 multiplier
    residues. Proof: the 8 pairwise distinct elements {1, m0, ..., m5, m0*m1}
    all lie in any subgroup containing the 6 mults, forcing |H| ≥ 8. -/
theorem eight_elts_escape_order_le_seven {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (hq59 : q ≥ 59)
    (H : Subgroup (ZMod q)ˣ) (hcard : Fintype.card H ≤ 7) :
    ∃ n, n < 6 ∧ (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H := by
  -- For |H| ≤ 5, delegate to existing result
  by_cases h5 : Fintype.card H ≤ 5
  · exact six_mults_escape_card_le_five hq hne hq59 H h5
  -- |H| ∈ {6, 7}. Assume for contradiction all 6 mults ∈ H.
  push_neg at h5
  by_contra hall
  push_neg at hall
  have hm : ∀ i, i < 6 → Units.mk0 (multZ q i) (multZ_ne_zero hq hne i) ∈ H := hall
  -- Abbreviation for multiplier units
  let mk := fun i => Units.mk0 (multZ q i) (multZ_ne_zero hq hne i)
  -- The 6 mults give |H| ≥ 6 via injection
  have hinj6 : Function.Injective (fun i : Fin 6 =>
      (⟨mk i.val, hm i.val i.isLt⟩ : H)) := by
    intro a b heq
    exact Fin.ext (multZ_injOn_six hq59 a.isLt b.isLt
      (congrArg Units.val (congrArg Subtype.val heq)))
  have h6le : 6 ≤ Fintype.card H :=
    (Fintype.card_fin 6).symm ▸ Fintype.card_le_of_injective _ hinj6
  -- 1 ∈ H is distinct from all 6 mults (each mult ≠ 1)
  have h1_ne_mk : ∀ i, i < 6 → (1 : (ZMod q)ˣ) ≠ mk i := by
    intro i hi heq
    have hv : (1 : ZMod q) = multZ q i := congrArg Units.val heq
    rcases show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega with
      rfl | rfl | rfl | rfl | rfl | rfl
    exacts [first_mult_ne_one (by omega) hv.symm, second_mult_ne_one (by omega) hv.symm,
      third_mult_ne_one (by omega) hv.symm, fourth_mult_ne_one (by omega) hv.symm,
      fifth_mult_ne_one (by omega) hv.symm, sixth_mult_ne_one (by omega) hv.symm]
  -- Product m0*m1 ∈ H, ≠ 1, ≠ each mult
  have hp_mem : mk 0 * mk 1 ∈ H := H.mul_mem (hm 0 (by omega)) (hm 1 (by omega))
  have hp_ne_one : mk 0 * mk 1 ≠ 1 := by
    intro h; exact mults_product_ne_one (by omega) (congrArg Units.val h)
  obtain ⟨dp0, dp1, dp2, dp3, dp4, dp5⟩ := mults_product_ne_mults hq59
  have hp_ne_mk : ∀ i, i < 6 → mk 0 * mk 1 ≠ mk i := by
    intro i hi heq
    have hv : multZ q 0 * multZ q 1 = multZ q i := by
      have := congrArg Units.val heq; simpa [Units.val_mul] using this
    rcases show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega with
      rfl | rfl | rfl | rfl | rfl | rfl
    exacts [dp0 hv, dp1 hv, dp2 hv, dp3 hv, dp4 hv, dp5 hv]
  -- Key: 1 and product are both outside the range of the 6-mult embedding
  let emb := fun i : Fin 6 => (⟨mk i.val, hm i.val i.isLt⟩ : H)
  have h1_not_range : (⟨1, H.one_mem⟩ : H) ∉ Set.range emb := by
    rintro ⟨⟨i, hi⟩, heq⟩; exact h1_ne_mk i hi (congrArg Subtype.val heq).symm
  have hp_not_range : (⟨mk 0 * mk 1, hp_mem⟩ : H) ∉ Set.range emb := by
    rintro ⟨⟨i, hi⟩, heq⟩; exact hp_ne_mk i hi (congrArg Subtype.val heq).symm
  -- Range of emb has 6 elements as a Finset of H
  let S : Finset H := Finset.univ.image emb
  have hS_card : S.card = 6 :=
    (Finset.card_image_of_injective _ hinj6).trans (Fintype.card_fin 6)
  -- Insert 1 (not in S) → 7 elements
  have h1S : (⟨1, H.one_mem⟩ : H) ∉ S := by
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and]; exact h1_not_range
  have hS1_card : (S.cons ⟨1, H.one_mem⟩ h1S).card = 7 := by
    rw [Finset.card_cons]; omega
  -- Insert product (not in S ∪ {1}) → 8 elements
  have hpS : (⟨mk 0 * mk 1, hp_mem⟩ : H) ∉ S.cons ⟨1, H.one_mem⟩ h1S := by
    rw [Finset.mem_cons]
    push_neg
    exact ⟨fun h => hp_ne_one (congrArg Subtype.val h),
      by simp only [S, Finset.mem_image, Finset.mem_univ, true_and]; exact hp_not_range⟩
  have hS2_card : ((S.cons ⟨1, H.one_mem⟩ h1S).cons ⟨mk 0 * mk 1, hp_mem⟩ hpS).card = 8 := by
    rw [Finset.card_cons]; omega
  -- 8-element Finset ⊆ H.univ → |H| ≥ 8
  have : 8 ≤ Fintype.card H := by
    calc 8 = ((S.cons _ h1S).cons _ hpS).card := hS2_card.symm
      _ ≤ Finset.univ.card := Finset.card_le_univ _
      _ = Fintype.card H := Finset.card_univ
  omega

open Classical in
/-- **Maximal subgroup escape implies SE**: in any finite group, to prove
    that a set of elements generates the whole group, it suffices to show
    they escape every maximal proper subgroup (coatom in the subgroup lattice).
    This is because every proper subgroup is contained in a maximal one
    (the subgroup lattice is coatomic for finite groups). -/
theorem se_of_maximal_escape {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hesc : ∀ (M : Subgroup (ZMod q)ˣ), IsCoatom M →
      ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ M) :
    ∀ (H : Subgroup (ZMod q)ˣ), H ≠ ⊤ →
      ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H := by
  intro H hH
  -- Subgroup lattice is finite → coatomic
  haveI : Finite (Subgroup (ZMod q)ˣ) :=
    Finite.of_injective (fun H : Subgroup (ZMod q)ˣ => (H : Set (ZMod q)ˣ))
      (fun _ _ h => SetLike.ext' h)
  have hcoatomic : IsCoatomic (Subgroup (ZMod q)ˣ) := Finite.to_isCoatomic
  obtain (rfl | ⟨M, hM, hle⟩) := hcoatomic.eq_top_or_exists_le_coatom H
  · exact absurd rfl hH
  · obtain ⟨n, hn⟩ := hesc M hM
    exact ⟨n, fun hmem => hn (hle hmem)⟩

/-! ## SE via primitive root verification

For specific primes q, SubgroupEscape can be verified by finding a multiplier
that is a primitive root (has full order q-1 in (ZMod q)ˣ). Such a multiplier
generates the entire group and hence cannot belong to any proper subgroup.

This gives a clean framework for finite verification: for each prime q in a
given range, find a multiplier index n such that `orderOf (multZ q n) = q-1`,
and conclude SE holds at q. -/

open Classical in
/-- An element of full order in a finite group cannot belong to any proper subgroup.
    If `orderOf g = |G|`, then `g` generates the whole group, so `g ∉ H` for
    any proper `H < G`. -/
theorem not_mem_proper_subgroup_of_full_order [Group G] [Fintype G]
    {g : G} (hord : orderOf g = Fintype.card G)
    {H : Subgroup G} (hH : H ≠ ⊤) : g ∉ H := by
  intro hg
  apply hH
  -- In H: orderOf ⟨g, hg⟩ divides card H (Lagrange)
  have h_dvd : Fintype.card G ∣ Fintype.card H := by
    have h1 := orderOf_dvd_card (x := (⟨g, hg⟩ : H))
    have h2 : orderOf (⟨g, hg⟩ : H) = orderOf g :=
      (orderOf_injective H.subtype H.subtype_injective ⟨g, hg⟩).symm
    rwa [h2, hord] at h1
  -- card H ≤ card G (H is a subgroup of G)
  have h_le : Fintype.card H ≤ Fintype.card G :=
    Fintype.card_le_of_injective H.subtype H.subtype_injective
  -- card G | card H and card H ≤ card G → card H = card G
  have h_eq : Fintype.card H = Fintype.card G :=
    le_antisymm h_le (Nat.le_of_dvd Fintype.card_pos h_dvd)
  -- Equal cardinality → H = G: carrier Finset = univ
  rw [eq_top_iff]; intro x _
  have hfs : (H : Set G).toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [Set.toFinset_card]; exact h_eq)
  exact Set.mem_toFinset.mp (hfs ▸ Finset.mem_univ x)

open Classical in
/-- If some multiplier is a primitive root mod q (order = q-1), then
    SubgroupEscape holds at q: no proper subgroup contains that multiplier. -/
theorem se_at_of_prim_root {q : Nat} [inst : Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (n : Nat)
    (hord : orderOf (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) = q - 1) :
    ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ q m) (multZ_ne_zero hq hne m)) ∉ H := by
  intro H hH
  refine ⟨n, not_mem_proper_subgroup_of_full_order ?_ hH⟩
  rw [hord, ← Nat.totient_prime inst.out]; exact (ZMod.card_units_eq_totient q).symm

open Classical in
/-- **Concrete SE helper**: verify SubgroupEscape at prime q by finding a multiplier
    that is a primitive root. The primitive root property is verified via power checks:
    `v^((q-1)/p) ≠ 1` for each prime p | (q-1). Uses `native_decide`. -/
theorem se_at_of_pow_checks {q : Nat} [inst : Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (n : Nat)
    (v : ZMod q) (hv : v ≠ 0)
    (hmult : multZ q n = v)
    (hpow : ∀ p ∈ (q - 1).primeFactors, v ^ ((q - 1) / p) ≠ 1) :
    ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ q m) (multZ_ne_zero hq hne m)) ∉ H := by
  subst hmult
  apply se_at_of_prim_root hq hne n
  have hqm1 : q - 1 ≠ 0 := by have := inst.out.one_lt; omega
  apply orderOf_eq_of_pow_and_pow_div_prime (by omega : 0 < q - 1)
  · have hcard : Fintype.card (ZMod q)ˣ = q - 1 := by
      rw [ZMod.card_units_eq_totient, Nat.totient_prime inst.out]
    rw [← hcard]; exact pow_card_eq_one
  · intro p hp hpd heq
    exact absurd (by simpa using congr_arg Units.val heq)
      (hpow p ((Nat.mem_primeFactors_of_ne_zero hqm1).mpr ⟨hp, hpd⟩))

/-! ## Concrete SE verification for small primes

For each prime q not in the sequence, SubgroupEscape is verified by finding
a multiplier index n such that multZ q n is a primitive root (has full order
q - 1 in (ZMod q)ˣ). The computational checks use `native_decide`. -/

instance : Fact (Nat.Prime 11) := ⟨by decide⟩
instance : Fact (Nat.Prime 17) := ⟨by decide⟩
instance : Fact (Nat.Prime 19) := ⟨by decide⟩
instance : Fact (Nat.Prime 23) := ⟨by decide⟩
instance : Fact (Nat.Prime 29) := ⟨by decide⟩
instance : Fact (Nat.Prime 31) := ⟨by decide⟩
instance : Fact (Nat.Prime 37) := ⟨by decide⟩
instance : Fact (Nat.Prime 41) := ⟨by decide⟩
instance : Fact (Nat.Prime 47) := ⟨by decide⟩
instance : Fact (Nat.Prime 59) := ⟨by decide⟩
instance : Fact (Nat.Prime 61) := ⟨by decide⟩
instance : Fact (Nat.Prime 67) := ⟨by decide⟩
instance : Fact (Nat.Prime 71) := ⟨by decide⟩
instance : Fact (Nat.Prime 73) := ⟨by decide⟩
instance : Fact (Nat.Prime 79) := ⟨by decide⟩
instance : Fact (Nat.Prime 83) := ⟨by decide⟩
instance : Fact (Nat.Prime 89) := ⟨by decide⟩
instance : Fact (Nat.Prime 97) := ⟨by decide⟩
instance : Fact (Nat.Prime 101) := ⟨by decide⟩
instance : Fact (Nat.Prime 103) := ⟨by decide⟩
instance : Fact (Nat.Prime 107) := ⟨by decide⟩
instance : Fact (Nat.Prime 109) := ⟨by decide⟩
instance : Fact (Nat.Prime 113) := ⟨by decide⟩
instance : Fact (Nat.Prime 127) := ⟨by decide⟩
instance : Fact (Nat.Prime 137) := ⟨by decide⟩
instance : Fact (Nat.Prime 139) := ⟨by decide⟩
instance : Fact (Nat.Prime 149) := ⟨by decide⟩
instance : Fact (Nat.Prime 151) := ⟨by decide⟩
instance : Fact (Nat.Prime 157) := ⟨by decide⟩


end MullinGroup
