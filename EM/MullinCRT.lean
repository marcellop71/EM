import EM.MullinGroupCore

open Mullin Euclid MullinGroup

namespace MullinCRT

/-! ## CRT Multiplier Invariance

This section proves that the smallest prime factor of P+1 depends only
on the residues of P modulo primes r different from q, provided q does
not divide P+1.

**Theorem A (CRT Multiplier Invariance):** If P and P' agree modulo every
prime r distinct from q, and q divides neither P+1 nor P'+1, then
`Nat.minFac(P+1) = Nat.minFac(P'+1)`.

The proof proceeds by symmetric minimality: the key lemma shows that
congruence mod r preserves divisibility of P+1 by r, so the sets of
prime divisors of P+1 and P'+1 agree (excluding q, which divides neither).
Since minFac selects the minimum of this set, equality follows.

This result formalizes the observation that the CRT structure of the
Euclid-Mullin sequence's multipliers is determined by the "other" prime
residues -- the residue mod q is irrelevant when q does not divide the
Euclid number.
-/

/-- If P and P' have the same remainder mod r, then r divides P+1
    if and only if r divides P'+1. -/
theorem dvd_succ_iff_of_mod_eq {P P' r : Nat} (hmod : P % r = P' % r) :
    r ∣ P + 1 ↔ r ∣ P' + 1 := by
  have key : (P + 1) % r = (P' + 1) % r := by
    have h1 : (P + 1) % r = (P % r + 1 % r) % r := Nat.add_mod P 1 r
    have h2 : (P' + 1) % r = (P' % r + 1 % r) % r := Nat.add_mod P' 1 r
    rw [h1, h2, hmod]
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, key]

/-- **CRT Multiplier Invariance (Theorem A):**
    If P, P' are naturals with P+1 >= 2 and P'+1 >= 2, q is prime,
    P and P' agree mod every prime r != q, and q divides neither P+1
    nor P'+1, then `Nat.minFac(P+1) = Nat.minFac(P'+1)`.

    The proof uses symmetric minimality: let m = minFac(P+1). Then m
    is prime, m | P+1, and m != q (since q does not divide P+1). By
    the key lemma (congruence mod m preserves divisibility), m | P'+1.
    By minimality of minFac, minFac(P'+1) <= m. The symmetric argument
    gives minFac(P+1) <= minFac(P'+1), so equality holds. -/
theorem crt_multiplier_invariance
    {P P' q : Nat}
    (hP : 2 ≤ P + 1) (hP' : 2 ≤ P' + 1)
    (_hq_prime : Nat.Prime q)
    (hcrt : ∀ r, Nat.Prime r → r ≠ q → P % r = P' % r)
    (hq_ndvd : ¬ (q ∣ P + 1))
    (hq_ndvd' : ¬ (q ∣ P' + 1)) :
    Nat.minFac (P + 1) = Nat.minFac (P' + 1) := by
  -- Let m = minFac(P+1), m' = minFac(P'+1)
  set m := Nat.minFac (P + 1)
  set m' := Nat.minFac (P' + 1)
  -- m is prime and divides P+1
  have hm_prime : Nat.Prime m := Nat.minFac_prime (by omega)
  have hm_dvd : m ∣ P + 1 := Nat.minFac_dvd (P + 1)
  -- m' is prime and divides P'+1
  have hm'_prime : Nat.Prime m' := Nat.minFac_prime (by omega)
  have hm'_dvd : m' ∣ P' + 1 := Nat.minFac_dvd (P' + 1)
  -- m != q (since q does not divide P+1 but m does)
  have hm_ne_q : m ≠ q := by
    intro heq; rw [heq] at hm_dvd; exact hq_ndvd hm_dvd
  -- m' != q (since q does not divide P'+1 but m' does)
  have hm'_ne_q : m' ≠ q := by
    intro heq; rw [heq] at hm'_dvd; exact hq_ndvd' hm'_dvd
  -- By CRT alignment: P % m = P' % m and P % m' = P' % m'
  have hmod_m : P % m = P' % m := hcrt m hm_prime hm_ne_q
  have hmod_m' : P % m' = P' % m' := hcrt m' hm'_prime hm'_ne_q
  -- Key lemma: m | P'+1 (from m | P+1 and congruence)
  have hm_dvd' : m ∣ P' + 1 :=
    (dvd_succ_iff_of_mod_eq hmod_m).mp hm_dvd
  -- Key lemma: m' | P+1 (from m' | P'+1 and congruence, reverse)
  have hm'_dvd' : m' ∣ P + 1 :=
    (dvd_succ_iff_of_mod_eq hmod_m').mpr hm'_dvd
  -- Minimality: m' <= m and m <= m'
  have h1 : m' ≤ m := Nat.minFac_le_of_dvd hm_prime.two_le hm_dvd'
  have h2 : m ≤ m' := Nat.minFac_le_of_dvd hm'_prime.two_le hm'_dvd'
  omega

/-! ## Walk Translation Corollary

When two products P, P' satisfy the CRT alignment condition and neither
is divisible by q after adding 1, the EM-like "next prime" operation
produces the same result. This connects the abstract CRT invariance to
the multiplicative walk structure.
-/

/-- Walk positions at consecutive steps are related multiplicatively:
    walkZ q (n+k) = walkZ q n * (product of multipliers from n to n+k-1).
    This is immediate from iterating `walkZ_succ`. -/
theorem walkZ_multi_step (q : Nat) (n k : Nat) :
    walkZ q (n + k) = walkZ q n *
      (Finset.range k).prod (fun i => multZ q (n + i)) := by
  induction k with
  | zero => simp [mul_one]
  | succ k ih =>
    rw [Nat.add_succ, walkZ_succ, ih, Finset.prod_range_succ, mul_assoc]

/-- Auxiliary: the product of multiplier units equals the ZMod product
    lifted to units. -/
theorem multZ_unit_prod_eq (q : Nat) [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (n k : Nat) :
    ((Finset.range k).prod (fun i => Units.mk0 (multZ q (n + i))
      (multZ_ne_zero hq hne (n + i))) : (ZMod q)ˣ).val =
    (Finset.range k).prod (fun i => multZ q (n + i)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Units.val_mul, ih,
        Units.val_mk0]

/-- The product of multiplier units from step n to n+k-1 equals the
    ratio walkZ(n)⁻¹ · walkZ(n+k) in units. When the walk returns,
    this product is 1. -/
theorem multZ_unit_prod_eq_one (q : Nat) [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) {n k : Nat}
    (hret : walkZ q n = walkZ q (n + k)) :
    (Finset.range k).prod (fun i => Units.mk0 (multZ q (n + i))
      (multZ_ne_zero hq hne (n + i))) = 1 := by
  -- From walkZ_multi_step: walkZ q (n+k) = walkZ q n * ∏ multZ
  have hmulti := walkZ_multi_step q n k
  -- Since walkZ q n = walkZ q (n+k), cancel to get ∏ multZ = 1
  have hwne : walkZ q n ≠ 0 := walkZ_ne_zero hq hne n
  have hprod_eq : (Finset.range k).prod (fun i => multZ q (n + i)) = 1 := by
    have : walkZ q n * (Finset.range k).prod (fun i => multZ q (n + i)) =
           walkZ q n * 1 := by rw [mul_one]; rw [← hmulti]; exact hret.symm
    exact mul_left_cancel₀ hwne this
  -- Lift to units: unit-valued product has same val as ZMod product
  ext
  rw [multZ_unit_prod_eq q hq hne n k, hprod_eq, Units.val_one]

/-- **Return product character constraint**: when the walk returns to
    the same position after k steps, applying any group homomorphism
    χ : (ZMod q)ˣ →* M to the product of multiplier units gives 1.

    This follows from `walkZ_multi_step` (w(n+k) = w(n) · ∏ m(j)) and
    the fact that w(n) = w(n+k) implies ∏ m(j) = 1 in (ZMod q)ˣ, so
    applying the homomorphism χ gives χ(∏ m(j)) = ∏ χ(m(j)) = χ(1) = 1. -/
theorem return_product_char_one {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {M : Type*} [CommMonoid M]
    (χ : (ZMod q)ˣ →* M)
    {n k : Nat} (hret : walkZ q n = walkZ q (n + k)) :
    (Finset.range k).prod (fun i =>
      χ (Units.mk0 (multZ q (n + i)) (multZ_ne_zero hq hne (n + i)))) = 1 := by
  have hone := multZ_unit_prod_eq_one q hq hne hret
  calc (Finset.range k).prod (fun i =>
        χ (Units.mk0 (multZ q (n + i)) (multZ_ne_zero hq hne (n + i))))
      = χ ((Finset.range k).prod (fun i =>
          Units.mk0 (multZ q (n + i)) (multZ_ne_zero hq hne (n + i)))) := by
        rw [map_prod]
    _ = χ 1 := by rw [hone]
    _ = 1 := map_one χ

end MullinCRT
