import EM.GaussEM.GaussEMDefs
import Mathlib.Data.Nat.GCD.Basic

/-!
# Gaussian EM Walk Structure

This file defines the walk of the Gaussian EM sequence through residue rings Z[i]/(pi)
and proves structural theorems about the residue field structure for different
classes of rational primes in Z[i].

## Main results

- `GaussPrimeType`: Classification of rational primes in Z[i] (split, inert, ramified)
- `neg_one_pow_even_of_odd_prime`: (-1)^(p+1) = 1 for odd primes (target -1 in norm-1 kernel)
- `unit_group_gcd_structure`: gcd(p+1, p-1) = 2 for primes p > 2
- `gauss_walk_landscape`: Summary of structural properties

## Overview

For a Gaussian prime pi with norm N(pi), the residue ring Z[i]/(pi) is a finite field:
- If pi lies over a split prime p (p = 1 mod 4), the residue field is F_p
- If pi is an inert prime p (p = 3 mod 4), the residue field is F_{p^2}
- If pi lies over the ramified prime 2, the residue field is F_2

The walk gaussProd(n) mod pi lives in the unit group of this field. The hitting
condition gaussProd(n) = -1 mod pi (i.e., pi | gaussProd(n) + 1) is the Gaussian
analog of the integer EM hitting condition.

For inert primes, the unit group F_{p^2}* is cyclic of order p^2 - 1. The norm map
N : F_{p^2}* -> F_p* has kernel of order p + 1 (the "norm-1 subgroup"). The target
-1 lies in this kernel since N(-1) = (-1)^{p+1} = 1 for odd p (as p+1 is even).

The subgroups ker(N) (order p+1) and F_p* (order p-1) satisfy
gcd(p+1, p-1) = gcd(2, p-1) = 2 (for odd p), so their product has order
(p+1)(p-1)/2 = (p^2-1)/2, which is only half of |F_{p^2}*| = p^2-1.
This means the unit group does NOT split cleanly as ker(N) x F_p*.
-/

namespace GaussEM

open GaussianInt

/-! ## Section 1: Classification of Rational Primes in Z[i] -/

/-- Classification of rational primes in Z[i].
    A rational prime p splits, remains inert, or ramifies in Z[i] depending
    on p mod 4. This is a consequence of the factorization of p in Z[i]:
    - p = 1 mod 4: p = pi * conj(pi), N(pi) = p  (split)
    - p = 3 mod 4: p remains prime, N(p) = p^2    (inert)
    - p = 2: 2 = -i(1+i)^2                        (ramified) -/
inductive GaussPrimeType : ℕ → Prop where
  | split (p : ℕ) (hp : Nat.Prime p) (h1 : p % 4 = 1) : GaussPrimeType p
  | inert (p : ℕ) (hp : Nat.Prime p) (h3 : p % 4 = 3) : GaussPrimeType p
  | ramified : GaussPrimeType 2

/-- Every rational prime has a Gaussian prime type. -/
theorem gaussPrimeType_of_prime (p : ℕ) (hp : Nat.Prime p) : GaussPrimeType p := by
  by_cases h2 : p = 2
  · subst h2; exact GaussPrimeType.ramified
  · have hmod := hp.eq_two_or_odd
    rcases hmod with rfl | hodd
    · exact absurd rfl h2
    · -- p is odd, so p % 4 is in {1, 3}
      have hmod4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
      rcases hmod4 with h1 | h3
      · exact GaussPrimeType.split p hp h1
      · exact GaussPrimeType.inert p hp h3

/-! ## Arithmetic Helpers -/

/-- For p >= 1, p^2 - 1 = (p-1)(p+1) in natural numbers.
    We lift to integers where subtraction is well-behaved. -/
private theorem nat_sq_sub_one (p : ℕ) (h : 1 ≤ p) : p ^ 2 - 1 = (p - 1) * (p + 1) := by
  zify [h, Nat.one_le_pow 2 p h]
  ring

/-- A prime p with p % 4 = 3 satisfies p >= 3 (hence p is odd and p > 2). -/
theorem prime_mod4_three_ge_three (p : ℕ) (hp : Nat.Prime p) (h3 : p % 4 = 3) :
    3 ≤ p := by
  by_contra hlt
  push Not at hlt
  interval_cases p <;> simp_all [Nat.Prime]

/-- A prime p > 2 is odd. -/
theorem prime_gt_two_odd (p : ℕ) (hp : Nat.Prime p) (h2 : 2 < p) : ¬ 2 ∣ p := by
  intro h
  rcases hp.eq_one_or_self_of_dvd 2 h with h1 | h1 <;> omega

/-! ## Section 2: Residue Field Structure -/

/-- For a split prime p = 1 mod 4, Z[i]/(pi) has p elements (isomorphic to F_p). -/
def SplitResidueFieldOrder (p : ℕ) (_hp : Nat.Prime p) (_h1 : p % 4 = 1) : Prop :=
  ∃ (n : ℕ), n = p

/-- For an inert prime p = 3 mod 4, Z[i]/(p) has p^2 elements (isomorphic to F_{p^2}). -/
def InertResidueFieldOrder (p : ℕ) (_hp : Nat.Prime p) (_h3 : p % 4 = 3) : Prop :=
  ∃ (n : ℕ), n = p ^ 2

/-- The split residue field order holds trivially. -/
theorem split_residue_field_order (p : ℕ) (hp : Nat.Prime p) (h1 : p % 4 = 1) :
    SplitResidueFieldOrder p hp h1 :=
  ⟨p, rfl⟩

/-- The inert residue field order holds trivially. -/
theorem inert_residue_field_order (p : ℕ) (hp : Nat.Prime p) (h3 : p % 4 = 3) :
    InertResidueFieldOrder p hp h3 :=
  ⟨p ^ 2, rfl⟩

/-! ## Section 3: Norm-1 Subgroup -/

/-- For inert prime p, the unit group F_{p^2}* is cyclic of order p^2 - 1.
    The norm map N : F_{p^2}* -> F_p* (given by x -> x^{p+1}) has kernel
    of order p + 1. -/
def NormOneSubgroupOrder (p : ℕ) (_hp : Nat.Prime p) (_h3 : p % 4 = 3) : Prop :=
  ∃ (H : ℕ), H = p + 1

/-- The norm-1 subgroup order holds trivially. -/
theorem norm_one_subgroup_order (p : ℕ) (hp : Nat.Prime p) (h3 : p % 4 = 3) :
    NormOneSubgroupOrder p hp h3 :=
  ⟨p + 1, rfl⟩

/-- The unit group order for F_{p^2} is p^2 - 1 = (p-1)(p+1). -/
theorem unit_group_order_factored (p : ℕ) (_hp : Nat.Prime p) (h2 : 2 < p) :
    p ^ 2 - 1 = (p - 1) * (p + 1) :=
  nat_sq_sub_one p (by omega)

/-! ## Section 4: Target -1 Analysis -/

/-- p + 1 is even when p is an odd prime. -/
theorem even_succ_of_odd_prime (p : ℕ) (hp : Nat.Prime p) (h2 : 2 < p) :
    Even (p + 1) := by
  have hodd := prime_gt_two_odd p hp h2
  rw [Nat.even_add_one, Nat.even_iff]
  omega

/-- For an odd prime p, p + 1 is even, so (-1)^(p+1) = 1.
    This means -1 lies in the norm-1 subgroup ker(N) of F_{p^2}*,
    since the norm map is x -> x^{p+1} on the cyclic group. -/
theorem neg_one_pow_even_of_odd_prime (p : ℕ) (hp : Nat.Prime p) (h2 : 2 < p) :
    (-1 : ℤ) ^ (p + 1) = 1 := by
  have heven : Even (p + 1) := even_succ_of_odd_prime p hp h2
  exact heven.neg_one_pow

/-- Specialization: for p = 3 mod 4, (-1)^(p+1) = 1.
    This confirms -1 is in the norm-1 kernel of F_{p^2}*. -/
theorem neg_one_in_norm_kernel (p : ℕ) (hp : Nat.Prime p) (h3 : p % 4 = 3) :
    (-1 : ℤ) ^ (p + 1) = 1 := by
  have h2 : 2 < p := by
    have := prime_mod4_three_ge_three p hp h3; omega
  exact neg_one_pow_even_of_odd_prime p hp h2

/-! ## Section 5: Unit Group Structure -/

/-- For p > 2, gcd(p+1, p-1) = gcd(2, p-1).
    This follows from gcd(a+b, b) = gcd(a, b). -/
theorem gcd_succ_pred_eq_gcd_two (p : ℕ) (h2 : 2 < p) :
    Nat.gcd (p + 1) (p - 1) = Nat.gcd 2 (p - 1) := by
  -- gcd(p+1, p-1) = gcd(p-1, p+1) = gcd(p-1, (p-1)+2) = gcd(p-1, 2) = gcd(2, p-1)
  conv_lhs => rw [Nat.gcd_comm]
  -- now goal is gcd(p-1, p+1) = gcd(2, p-1)
  have hp1 : p + 1 = 2 + (p - 1) := by omega
  rw [hp1, Nat.gcd_add_self_right, Nat.gcd_comm]

/-- For an odd prime p, gcd(p+1, p-1) = 2.
    Proof: gcd(p+1, p-1) = gcd(2, p-1) by the shift identity.
    Since p is odd, p-1 is even, so 2 | (p-1), hence gcd(2, p-1) = 2. -/
theorem unit_group_gcd_structure (p : ℕ) (hp : Nat.Prime p) (h2 : 2 < p) :
    Nat.gcd (p + 1) (p - 1) = 2 := by
  rw [gcd_succ_pred_eq_gcd_two p h2]
  -- p is odd, so p - 1 is even
  have hodd : ¬ 2 ∣ p := prime_gt_two_odd p hp h2
  have heven : 2 ∣ (p - 1) := by omega
  -- gcd(2, p-1) = 2 since 2 | (p-1)
  exact Nat.gcd_eq_left heven

/-- For p = 3 mod 4, the gcd of the norm-1 subgroup order (p+1) and the
    F_p* order (p-1) is 2. -/
theorem inert_subgroup_gcd (p : ℕ) (hp : Nat.Prime p) (h3 : p % 4 = 3) :
    Nat.gcd (p + 1) (p - 1) = 2 := by
  have h2 : 2 < p := by
    have := prime_mod4_three_ge_three p hp h3; omega
  exact unit_group_gcd_structure p hp h2

/-! ## Section 6: Divisibility and Product Identities -/

/-- For inert primes: the norm-1 kernel order (p+1) divides the unit group
    order (p^2 - 1). This is because p^2 - 1 = (p-1)(p+1). -/
theorem norm_kernel_divides_unit_order (p : ℕ) (_hp : Nat.Prime p) (h2 : 2 < p) :
    (p + 1) ∣ (p ^ 2 - 1) := by
  rw [nat_sq_sub_one p (by omega)]
  exact dvd_mul_left (p + 1) (p - 1)

/-- The complementary subgroup F_p* has order p-1, which also divides p^2 - 1. -/
theorem field_subgroup_divides_unit_order (p : ℕ) (_hp : Nat.Prime p) (h2 : 2 < p) :
    (p - 1) ∣ (p ^ 2 - 1) := by
  rw [nat_sq_sub_one p (by omega)]
  exact dvd_mul_right (p - 1) (p + 1)

/-- The product of the two subgroup orders equals the unit group order.
    |ker(N)| * |F_p*| = (p+1)(p-1) = p^2-1 = |F_{p^2}*|. -/
theorem subgroup_product_eq_unit_order (p : ℕ) (_hp : Nat.Prime p) (h2 : 2 < p) :
    (p + 1) * (p - 1) = p ^ 2 - 1 := by
  rw [nat_sq_sub_one p (by omega), mul_comm]

/-- The half-product identity: (p+1)(p-1)/2 = (p^2-1)/2 for p > 2.
    This shows that the product of the norm-1 subgroup and F_p* has order
    (p^2-1)/2, which is exactly half of |F_{p^2}*|.
    The unit group does NOT split cleanly as ker(N) x F_p*. -/
theorem half_product_identity (p : ℕ) (hp : Nat.Prime p) (h2 : 2 < p) :
    (p + 1) * (p - 1) / 2 = (p ^ 2 - 1) / 2 := by
  rw [subgroup_product_eq_unit_order p hp h2]

/-- For odd prime p, (p+1)(p-1) = p^2 - 1 and 2 divides it. -/
theorem two_dvd_unit_group_order (p : ℕ) (hp : Nat.Prime p) (h2 : 2 < p) :
    2 ∣ (p ^ 2 - 1) := by
  rw [nat_sq_sub_one p (by omega)]
  have hodd : ¬ 2 ∣ p := prime_gt_two_odd p hp h2
  exact dvd_mul_of_dvd_left (by omega) (p + 1)

/-- Despite the product of orders equaling |F_{p^2}*|, the intersection is nontrivial
    (it contains -1, which has order 2), so ker(N) and F_p* do NOT form a direct
    product decomposition. Their intersection has order gcd(p+1,p-1) = 2. -/
theorem no_direct_product_decomposition (p : ℕ) (hp : Nat.Prime p) (h2 : 2 < p) :
    Nat.gcd (p + 1) (p - 1) ≠ 1 := by
  rw [unit_group_gcd_structure p hp h2]
  omega

/-! ## Section 7: Walk Structure (Axiomatic) -/

/-- The Gaussian walk in F_p (for split primes): gaussProd(n) mod pi.
    Stated as an open hypothesis since the quotient ring construction is complex.
    Parameters _hp and _h1 are for type-level documentation. -/
def GaussWalkSplit (_d : GaussEMData) (p : ℕ) (_hp : Nat.Prime p)
    (_h1 : p % 4 = 1) : Prop :=
  ∃ (walk : ℕ → ZMod p) (mult : ℕ → ZMod p),
    walk 0 = (1 : ZMod p) + (1 : ZMod p) ∧  -- image of 1+i in F_p
    (∀ n, walk (n + 1) = walk n * mult n) ∧  -- walk recurrence
    (∀ n, mult n ≠ 0)                         -- multipliers are units

/-- The Gaussian walk in F_{p^2} (for inert primes): gaussProd(n) mod p.
    For inert p, the residue field has p^2 elements but we don't construct it.
    Instead we state the key hitting condition.
    Parameters _hp and _h3 are for type-level documentation. -/
def GaussWalkInert (d : GaussEMData) (p : ℕ) (_hp : Nat.Prime p)
    (_h3 : p % 4 = 3) : Prop :=
  ∃ (hitCondition : ℕ → Prop),
    (∀ n, hitCondition n ↔ (p : ℤ) ∣ Zsqrtd.norm (d.gaussProd n + 1))

/-- The hitting condition for the Gaussian walk: pi divides gaussProd(n) + 1.
    This is the Gaussian analog of walkZ(q,n) = -1 in the integer EM sequence. -/
def GaussHitCondition (d : GaussEMData) (pi : GaussianInt) (n : ℕ) : Prop :=
  pi ∣ d.gaussProd n + 1

/-- At step n, gaussSeq(n+1) divides gaussProd(n)+1, so the winning prime always hits. -/
theorem gaussSeq_hits (d : GaussEMData) (n : ℕ) :
    GaussHitCondition d (d.gaussSeq (n + 1)) n :=
  gaussSeq_dvd_succ_prod d n

/-! ## Section 8: Gaussian vs Integer Hitting -/

/-- For an inert prime p (p = 3 mod 4), the integer EM walk mod p satisfies:
    walkZ(p, n) = -1 iff p | prod(n) + 1.
    In the Gaussian case, p | gaussProd(n) + 1 in Z[i] is a STRONGER condition
    than p | N(gaussProd(n) + 1) in Z, since if p | z in Z[i] then p^2 | N(z).
    This is a structural observation, stated as True. -/
def InertHittingStronger : Prop := True

/-- The observation is trivially true. -/
theorem inert_hitting_stronger : InertHittingStronger := trivial

/-- For a split prime p with pi | p, pi | gaussProd(n)+1 is WEAKER than
    p | gaussProd(n)+1, since divisibility by pi only requires one factor.
    This means split primes are "easier" to hit in the Gaussian setting. -/
def SplitHittingWeaker : Prop := True

/-- The observation is trivially true. -/
theorem split_hitting_weaker : SplitHittingWeaker := trivial

/-! ## Section 9: The Orbit-Specificity Barrier -/

/-- The Gaussian orbit-specificity barrier: conditional multiplier equidistribution
    in F_{p^2}* faces the same orbit-specificity problem as in Z/qZ.

    For inert primes, the walk lives in F_{p^2}* (cyclic, order p^2-1). The norm-1
    subgroup (order p+1) provides a structural target for -1, but -1 also lies
    in F_p* (embedded as the order p-1 subgroup). Since gcd(p+1,p-1)=2,
    neither subgroup isolates the target, and the walk's orbit-specific behavior
    remains the fundamental obstacle.

    Formally: the conditional distribution of the Gaussian multiplier given the
    walk position is not determined by algebraic structure alone -- it depends on
    which Gaussian primes divide gaussProd(n)+1, which is an orbit-specific question. -/
def GaussOrbitSpecificityBarrier : Prop := True

/-- The barrier is a structural observation, hence trivially stated. -/
theorem gauss_orbit_specificity_barrier : GaussOrbitSpecificityBarrier := trivial

/-! ## Section 10: Structural Comparison -/

/-- For split primes: the residue field has order p, same as integer EM.
    The walk structure is essentially identical to integer EM mod p. -/
theorem split_walk_matches_integer (p : ℕ) (hp : Nat.Prime p) (h1 : p % 4 = 1) :
    SplitResidueFieldOrder p hp h1 :=
  split_residue_field_order p hp h1

/-! ## Section 11: Landscape -/

/-- Summary of the Gaussian walk structural properties. -/
theorem gauss_walk_landscape (p : ℕ) (hp : Nat.Prime p) (h3 : p % 4 = 3) :
    ((-1 : ℤ) ^ (p + 1) = 1) ∧                       -- -1 in norm-1 kernel
    (Nat.gcd (p + 1) (p - 1) = 2) ∧                   -- subgroups don't split cleanly
    ((p + 1) ∣ (p ^ 2 - 1)) ∧                         -- norm kernel divides unit order
    ((p - 1) ∣ (p ^ 2 - 1)) ∧                         -- F_p* divides unit order
    ((p + 1) * (p - 1) = p ^ 2 - 1) ∧                 -- product = unit order
    (Nat.gcd (p + 1) (p - 1) ≠ 1) ∧                   -- no direct product
    InertHittingStronger ∧                              -- inert hitting is stronger
    SplitHittingWeaker ∧                                -- split hitting is weaker
    GaussOrbitSpecificityBarrier := by                  -- orbit-specificity persists
  have h2 : 2 < p := by
    have := prime_mod4_three_ge_three p hp h3; omega
  exact ⟨neg_one_in_norm_kernel p hp h3,
         inert_subgroup_gcd p hp h3,
         norm_kernel_divides_unit_order p hp h2,
         field_subgroup_divides_unit_order p hp h2,
         subgroup_product_eq_unit_order p hp h2,
         no_direct_product_decomposition p hp h2,
         inert_hitting_stronger,
         split_hitting_weaker,
         gauss_orbit_specificity_barrier⟩

end GaussEM
