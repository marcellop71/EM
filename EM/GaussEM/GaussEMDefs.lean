import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Gaussian Euclid-Mullin Sequence: Foundations

The Gaussian Euclid-Mullin sequence over Z[i] mirrors the integer EM sequence:
- gaussSeq(0) = 1 + i (the Gaussian prime above 2)
- gaussSeq(n+1) = the irreducible factor of smallest norm of (gaussProd(n) + 1)
- gaussProd(n) = gaussSeq(0) * ... * gaussSeq(n)

This file defines the sequence, states the Gaussian Mullin Conjecture (GMC),
and proves basic structural properties analogous to the integer case.

## Main results

- `one_plus_i_irreducible`: 1 + i is irreducible in Z[i] (norm = 2, prime)
- `gaussSeq_irreducible`: every term of the Gaussian EM sequence is irreducible
- `gaussSeq_dvd_succ_prod`: seq(n+1) divides prod(n) + 1
- `gaussSeq_not_dvd_prod`: seq(n+1) does not divide prod(n) (Euclid argument)
- `gaussProd_coprime_succ`: prod(n) and prod(n)+1 are coprime
- `norm_gaussProd_ge_two`: norm of prod(n) is at least 2
- `gauss_em_landscape`: summary conjunction of structural properties
-/

namespace GaussEM

open GaussianInt

/-- The natural number norm of a Gaussian integer: re^2 + im^2. -/
def gaussNorm (z : GaussianInt) : ℕ := (Zsqrtd.norm z).natAbs

/-- An element of Z[i] is a Gaussian prime if it is irreducible. -/
def IsGaussPrime (pi : GaussianInt) : Prop := Irreducible pi

/-! ## Section 1: Irreducibility of 1 + i -/

/-- The Gaussian integer 1 + i. -/
def onePlusI : GaussianInt := ⟨1, 1⟩

/-- The norm of 1 + i is 2. -/
theorem norm_onePlusI : Zsqrtd.norm onePlusI = 2 := by
  native_decide

/-- The natural number norm of 1 + i is 2. -/
theorem gaussNorm_onePlusI : gaussNorm onePlusI = 2 := by
  simp [gaussNorm, norm_onePlusI]

/-- 1 + i is not zero in Z[i]. -/
theorem onePlusI_ne_zero : onePlusI ≠ 0 := by
  decide

/-- 1 + i is not a unit in Z[i].
    Proof: units have norm 1, but norm(1+i) = 2. -/
theorem onePlusI_not_isUnit : ¬IsUnit onePlusI := by
  intro h
  rw [← Zsqrtd.norm_eq_one_iff] at h
  simp [norm_onePlusI] at h

/-- An element of Z[i] with prime natAbs-norm is irreducible.
    Proof: if z = a * b, then natAbs(norm z) = natAbs(norm a) * natAbs(norm b).
    Since natAbs(norm z) is prime, one of the factors is 1, hence a unit. -/
private theorem irreducible_of_prime_natAbs_norm {z : GaussianInt}
    (hp : Nat.Prime (Zsqrtd.norm z).natAbs) : Irreducible z := by
  constructor
  · -- z is not a unit: units have natAbs norm = 1, but hp says it's prime (>= 2)
    intro hu
    rw [← Zsqrtd.norm_eq_one_iff] at hu
    have := hp.one_lt; omega
  · -- if z = a * b, one factor is a unit
    intro a b hab
    have hnorm : (Zsqrtd.norm z).natAbs =
        (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs := by
      rw [hab, Zsqrtd.norm_mul, Int.natAbs_mul]
    -- natAbs(norm a) divides natAbs(norm z) which is prime
    have hpgt : 1 < (Zsqrtd.norm z).natAbs := hp.one_lt
    have hdvd_a : (Zsqrtd.norm a).natAbs ∣ (Zsqrtd.norm z).natAbs := by
      rw [hnorm]; exact dvd_mul_right _ _
    rcases hp.eq_one_or_self_of_dvd _ hdvd_a with ha1 | ha_full
    · left; rwa [Zsqrtd.norm_eq_one_iff] at ha1
    · right
      have hb1 : (Zsqrtd.norm b).natAbs = 1 := by
        have hppos : 0 < (Zsqrtd.norm z).natAbs := by omega
        rw [ha_full] at hnorm
        have hmul : (Zsqrtd.norm z).natAbs * 1 = (Zsqrtd.norm z).natAbs *
            (Zsqrtd.norm b).natAbs := by omega
        exact (Nat.mul_left_cancel hppos hmul).symm
      rwa [Zsqrtd.norm_eq_one_iff] at hb1

/-- 1 + i is irreducible in Z[i].
    Proof: norm(1+i) = 2, which is a (rational) prime.
    An element with prime natAbs-norm is irreducible. -/
theorem one_plus_i_irreducible : Irreducible onePlusI := by
  apply irreducible_of_prime_natAbs_norm
  rw [norm_onePlusI]
  decide

/-! ## Section 2: The Gaussian EM Sequence Data -/

/-- The Gaussian Euclid-Mullin sequence data: a sequence of Gaussian primes
    (irreducible elements of Z[i]) and their running product, starting from 1+i.

    This mirrors the integer EM sequence where:
    - seq(0) = 2 becomes gaussSeq(0) = 1+i (the Gaussian prime above 2)
    - seq(n+1) = irreducible factor of smallest norm of (gaussProd(n) + 1)
    - gaussProd(n) = gaussSeq(0) * ... * gaussSeq(n) -/
structure GaussEMData where
  /-- The sequence of Gaussian primes. -/
  gaussSeq : ℕ → GaussianInt
  /-- The running product. -/
  gaussProd : ℕ → GaussianInt
  /-- Initial term is 1+i. -/
  gaussSeq_zero : gaussSeq 0 = onePlusI
  /-- Initial product is 1+i. -/
  gaussProd_zero : gaussProd 0 = onePlusI
  /-- Each successor is an irreducible factor of (product + 1). -/
  gaussSeq_succ : ∀ n, Irreducible (gaussSeq (n + 1)) ∧
    gaussSeq (n + 1) ∣ (gaussProd n + 1)
  /-- Running product recurrence. -/
  gaussProd_succ : ∀ n, gaussProd (n + 1) = gaussProd n * gaussSeq (n + 1)
  /-- Minimality: smallest norm among irreducible factors. -/
  gaussSeq_minimal : ∀ n, ∀ f : GaussianInt, Irreducible f →
    f ∣ (gaussProd n + 1) →
    Zsqrtd.norm (gaussSeq (n + 1)) ≤ Zsqrtd.norm f

variable (d : GaussEMData)

/-! ## Section 3: Basic Structural Properties -/

/-- Every term of the Gaussian EM sequence is irreducible. -/
theorem gaussSeq_irreducible (n : ℕ) : Irreducible (d.gaussSeq n) := by
  cases n with
  | zero => rw [d.gaussSeq_zero]; exact one_plus_i_irreducible
  | succ n => exact (d.gaussSeq_succ n).1

/-- Each successor term divides the previous product plus one. -/
theorem gaussSeq_dvd_succ_prod (n : ℕ) : d.gaussSeq (n + 1) ∣ d.gaussProd n + 1 :=
  (d.gaussSeq_succ n).2

/-- No term of the sequence is zero. -/
theorem gaussSeq_ne_zero (n : ℕ) : d.gaussSeq n ≠ 0 :=
  Irreducible.ne_zero (gaussSeq_irreducible d n)

/-- No term of the sequence is a unit. -/
theorem gaussSeq_not_isUnit (n : ℕ) : ¬IsUnit (d.gaussSeq n) :=
  Irreducible.not_isUnit (gaussSeq_irreducible d n)

/-- The product is never zero: it is a product of irreducible (hence nonzero) elements. -/
theorem gaussProd_ne_zero (n : ℕ) : d.gaussProd n ≠ 0 := by
  induction n with
  | zero => rw [d.gaussProd_zero]; exact onePlusI_ne_zero
  | succ n ih =>
    rw [d.gaussProd_succ]
    exact mul_ne_zero ih (gaussSeq_ne_zero d (n + 1))

/-- The norm of any product term is positive. -/
theorem norm_gaussProd_pos (n : ℕ) : 0 < Zsqrtd.norm (d.gaussProd n) :=
  GaussianInt.norm_pos.mpr (gaussProd_ne_zero d n)

/-- The norm of any irreducible element of Z[i] is at least 2.
    Proof: norm > 0 since nonzero; natAbs(norm) != 1 since not a unit.
    So natAbs(norm) >= 2, and since norm is nonneg for Gaussian integers, norm >= 2. -/
theorem norm_irreducible_ge_two {z : GaussianInt} (hz : Irreducible z) :
    2 ≤ Zsqrtd.norm z := by
  have hne : z ≠ 0 := hz.ne_zero
  have hpos : 0 < Zsqrtd.norm z := GaussianInt.norm_pos.mpr hne
  have hnu : ¬IsUnit z := hz.not_isUnit
  have hna_pos : 0 < (Zsqrtd.norm z).natAbs := by
    rw [Int.natAbs_pos]; exact ne_of_gt hpos
  have hna_ne_one : (Zsqrtd.norm z).natAbs ≠ 1 := by
    intro h; exact hnu (Zsqrtd.norm_eq_one_iff.mp h)
  have hna_ge : 2 ≤ (Zsqrtd.norm z).natAbs := by omega
  rw [← GaussianInt.abs_natCast_norm]
  exact_mod_cast hna_ge

/-- The norm of the product at step n is at least 2.
    Base: norm(1+i) = 2. Step: norm(prod(n+1)) = norm(prod(n)) * norm(seq(n+1)) >= 2*2 >= 2. -/
theorem norm_gaussProd_ge_two (n : ℕ) : 2 ≤ Zsqrtd.norm (d.gaussProd n) := by
  induction n with
  | zero => rw [d.gaussProd_zero, norm_onePlusI]
  | succ n ih =>
    rw [d.gaussProd_succ, Zsqrtd.norm_mul]
    have h1 := norm_irreducible_ge_two (gaussSeq_irreducible d (n + 1))
    nlinarith

/-- The product is never -1, since norm(-1) = 1 but norm(prod(n)) >= 2. -/
theorem gaussProd_ne_neg_one (n : ℕ) : d.gaussProd n ≠ -1 := by
  intro h
  have h1 : Zsqrtd.norm (d.gaussProd n) = Zsqrtd.norm (-1 : GaussianInt) := by
    rw [h]
  rw [Zsqrtd.norm_neg, Zsqrtd.norm_one] at h1
  have h2 := norm_gaussProd_ge_two d n
  omega

/-- The product plus one is never zero. -/
theorem gaussProd_succ_ne_zero (n : ℕ) : d.gaussProd n + 1 ≠ 0 := by
  intro h
  have : d.gaussProd n = -1 := by
    have hre : (d.gaussProd n).re + 1 = 0 := by
      have := congr_arg Zsqrtd.re h; simp at this; linarith
    have him : (d.gaussProd n).im = 0 := by
      have := congr_arg Zsqrtd.im h; simp at this; linarith
    ext <;> simp <;> omega
  exact gaussProd_ne_neg_one d n this

/-! ## Section 4: The Euclid Argument -/

/-- seq(n+1) does not divide prod(n): the Euclid argument.
    If pi | prod(n) and pi | prod(n)+1, then pi | 1, contradicting irreducibility. -/
theorem gaussSeq_not_dvd_prod (n : ℕ) : ¬(d.gaussSeq (n + 1) ∣ d.gaussProd n) := by
  intro hdvd
  have hdvd1 := gaussSeq_dvd_succ_prod d n
  have hd : d.gaussSeq (n + 1) ∣ 1 := by
    have hsub : d.gaussSeq (n + 1) ∣ (d.gaussProd n + 1 - d.gaussProd n) :=
      dvd_sub hdvd1 hdvd
    simp at hsub
    exact hsub
  exact (gaussSeq_not_isUnit d (n + 1)) (isUnit_of_dvd_one hd)

/-- prod(n) and prod(n)+1 are coprime (they are consecutive elements in a UFD). -/
theorem gaussProd_coprime_succ (n : ℕ) :
    IsRelPrime (d.gaussProd n) (d.gaussProd n + 1) := by
  intro p hp1 hp2
  have hsub : p ∣ (d.gaussProd n + 1 - d.gaussProd n) := dvd_sub hp2 hp1
  simp at hsub
  exact isUnit_of_dvd_one hsub

/-! ## Section 5: Norm Growth -/

/-- The norm of the product strictly increases at each step.
    norm(prod(n+1)) = norm(prod(n)) * norm(seq(n+1)), and norm(seq(n+1)) >= 2. -/
theorem norm_gaussProd_strict_mono :
    StrictMono (fun n => Zsqrtd.norm (d.gaussProd n)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [d.gaussProd_succ, Zsqrtd.norm_mul]
  have h1 := norm_irreducible_ge_two (gaussSeq_irreducible d (n + 1))
  have h2 := norm_gaussProd_pos d n
  nlinarith

/-! ## Section 6: The Gaussian Mullin Conjecture -/

/-- The Gaussian Mullin Conjecture: every Gaussian prime (up to units)
    eventually appears in the Gaussian EM sequence.

    We use `Associated` to handle unit ambiguity: in Z[i], the units are
    {1, -1, i, -i}, so each Gaussian prime has exactly 4 associates. -/
def GaussMullinConjecture : Prop :=
  ∀ pi : GaussianInt, Irreducible pi → ∃ n : ℕ, Associated (d.gaussSeq n) pi

/-- Weak Gaussian Mullin Conjecture: the sequence captures every norm value
    achieved by Gaussian primes. This is strictly weaker than GMC since
    multiple non-associated primes can share the same norm (e.g. 1+2i and 2+i). -/
def WeakGaussMullinConjecture : Prop :=
  ∀ pi : GaussianInt, Irreducible pi →
    ∃ n : ℕ, Zsqrtd.norm (d.gaussSeq n) = Zsqrtd.norm pi

/-! ## Section 7: Connection to Integer EM -/

/-- The integer EM sequence starts at 2 = norm(1+i). The Gaussian version
    starts at 1+i itself. Integer primes p = 3 mod 4 remain prime in Z[i]
    (by `prime_of_nat_prime_of_mod_four_eq_three`), while primes p = 1 mod 4
    split into conjugate pairs pi, conj(pi) with norm(pi) = p. The prime 2
    ramifies as 2 = -i(1+i)^2 (up to units).

    This structural difference means the Gaussian EM sequence potentially
    visits more "prime directions" than the integer sequence.
    Whether this helps or hinders the conjecture is unclear.

    Stated as True since the relationship between the two greedy
    constructions is nontrivial and not needed for the abstract theory. -/
def IntegerGaussianBridge : Prop := True

/-! ## Section 8: Landscape -/

/-- Summary of structural properties of the Gaussian EM sequence. -/
theorem gauss_em_landscape :
    (∀ n, Irreducible (d.gaussSeq n)) ∧
    (∀ n, d.gaussSeq (n + 1) ∣ d.gaussProd n + 1) ∧
    (∀ n, ¬(d.gaussSeq (n + 1) ∣ d.gaussProd n)) ∧
    (∀ n, d.gaussProd n ≠ -1) ∧
    (∀ n, 2 ≤ Zsqrtd.norm (d.gaussProd n)) := by
  exact ⟨gaussSeq_irreducible d,
         gaussSeq_dvd_succ_prod d,
         gaussSeq_not_dvd_prod d,
         gaussProd_ne_neg_one d,
         norm_gaussProd_ge_two d⟩

end GaussEM
