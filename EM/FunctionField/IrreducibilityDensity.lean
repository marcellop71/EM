import EM.FunctionField.Finiteness
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Irreducibility Density for Polynomials over Finite Fields

We prove that the number of monic irreducible polynomials of degree d over F_p
is at most p^d / d, giving an irreducibility density bound of at most 1/d that
tends to 0 as d grows.

## Main results

- `monic_irreducible_dvd_X_pow_sub_X` : every monic irreducible of degree d divides X^(p^d) - X
- `ff_irreducible_count_le` : at most p^d / d monic irreducibles of degree d

## Proof strategy

Part 1 uses AdjoinRoot: for monic irreducible Q of degree d, AdjoinRoot Q is a finite
field with p^d elements. The root alpha = AdjoinRoot.root Q satisfies alpha^(p^d) = alpha
by the Frobenius endomorphism. Since Q = minpoly(ZMod p, alpha), minpoly.dvd gives
Q | X^(p^d) - X.

Part 2 derives the count bound: distinct monic irreducibles are coprime in a UFD,
so their product divides X^(p^d) - X, giving d * count <= p^d.
-/

namespace FunctionFieldAnalog

open Polynomial Classical Filter

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## Part 1: Irreducible divides X^(p^d) - X -/

/-- Every monic irreducible polynomial Q of degree d over ZMod p divides X^(p^d) - X.

    Proof: In AdjoinRoot Q, the element alpha = root Q has minimal polynomial Q
    (since Q is monic). AdjoinRoot Q is a finite field with p^d elements, so by
    Frobenius alpha^(p^d) = alpha. Therefore aeval alpha (X^(p^d) - X) = 0, and
    by minpoly.dvd we get Q | X^(p^d) - X. -/
theorem monic_irreducible_dvd_X_pow_sub_X {d : ℕ} (_hd : d ≠ 0)
    {Q : Polynomial (ZMod p)} (hm : Q.Monic) (hirr : Irreducible Q) (hdeg : Q.natDegree = d) :
    Q ∣ (X ^ p ^ d - X : Polynomial (ZMod p)) := by
  -- Set up AdjoinRoot Q as a field
  haveI : Fact (Irreducible Q) := ⟨hirr⟩
  -- AdjoinRoot Q is a finite module over ZMod p (from Q monic)
  haveI : Module.Finite (ZMod p) (AdjoinRoot Q) := hm.finite_adjoinRoot
  -- Therefore AdjoinRoot Q is finite
  haveI : Finite (AdjoinRoot Q) := Module.finite_of_finite (ZMod p)
  haveI : Fintype (AdjoinRoot Q) := Fintype.ofFinite _
  -- The root alpha in AdjoinRoot Q
  set α := AdjoinRoot.root Q with hα_def
  -- Q = minpoly (ZMod p) alpha (since Q is monic)
  have hminpoly : minpoly (ZMod p) α = Q := by
    rw [hα_def, show AdjoinRoot.root Q = (AdjoinRoot.powerBasis hm.ne_zero).gen from rfl]
    exact AdjoinRoot.minpoly_powerBasis_gen_of_monic hm
  -- Card of AdjoinRoot Q = p^d
  have hcard : Fintype.card (AdjoinRoot Q) = p ^ d := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
    congr 1
    rw [(AdjoinRoot.powerBasis hm.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
    exact hdeg
  -- Frobenius: alpha^(p^d) = alpha (since card = p^d)
  have hfrob : α ^ (p ^ d) = α := by
    have h := FiniteField.pow_card α
    rwa [hcard] at h
  -- Therefore aeval alpha (X^(p^d) - X) = 0
  have heval : Polynomial.aeval α (X ^ (p ^ d) - X : (ZMod p)[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X]
    rw [hfrob, sub_self]
  -- By minpoly.dvd, minpoly | X^(p^d) - X
  have hdvd := minpoly.dvd (ZMod p) α heval
  rwa [hminpoly] at hdvd

/-! ## Part 2: Irreducible count bound -/

/-- Distinct monic irreducible polynomials over a field are coprime. -/
private theorem monic_irreducible_isCoprime
    {Q₁ Q₂ : Polynomial (ZMod p)} (hm₁ : Q₁.Monic) (hm₂ : Q₂.Monic)
    (hirr₁ : Irreducible Q₁) (hirr₂ : Irreducible Q₂) (hne : Q₁ ≠ Q₂) :
    IsCoprime Q₁ Q₂ := by
  rw [hirr₁.coprime_iff_not_dvd]
  intro hdvd
  exact hne (eq_of_monic_of_associated hm₁ hm₂ (hirr₁.associated_of_dvd hirr₂ hdvd))

/-- Fintype instance for monic irreducible degree-d polynomials. -/
noncomputable instance monicIrreducibleFintype (d : ℕ) :
    Fintype {Q : Polynomial (ZMod p) | Q.Monic ∧ Irreducible Q ∧ Q.natDegree = d} := by
  apply Set.Finite.fintype
  apply Set.Finite.subset (monic_natDegree_finite (ZMod p) d)
  intro Q ⟨hm, _, hd'⟩; exact ⟨hm, hd'⟩

/-- The number of monic irreducible polynomials of degree d over F_p
    is at most p^d / d. -/
theorem ff_irreducible_count_le (d : ℕ) (hd : 0 < d) :
    Fintype.card {Q : Polynomial (ZMod p) | Q.Monic ∧ Irreducible Q ∧ Q.natDegree = d}
      ≤ p ^ d / d := by
  -- Build a Finset S from the set
  have hfin : Set.Finite {Q : Polynomial (ZMod p) | Q.Monic ∧ Irreducible Q ∧ Q.natDegree = d} := by
    apply Set.Finite.subset (monic_natDegree_finite (ZMod p) d)
    intro Q ⟨hm, _, hd'⟩; exact ⟨hm, hd'⟩
  set S := hfin.toFinset with hS_def
  -- Card equality
  have hcard_eq : Fintype.card
      {Q : Polynomial (ZMod p) | Q.Monic ∧ Irreducible Q ∧ Q.natDegree = d} = S.card := by
    rw [hS_def]; exact hfin.card_toFinset.symm
  rw [hcard_eq]
  -- Properties of elements in S
  have hS_mem : ∀ Q ∈ S, Q.Monic ∧ Irreducible Q ∧ Q.natDegree = d := by
    intro Q hQ
    rwa [hS_def, Set.Finite.mem_toFinset] at hQ
  -- Product of S divides X^(p^d) - X
  have hprod_dvd : (∏ Q ∈ S, Q) ∣ (X ^ p ^ d - X : Polynomial (ZMod p)) := by
    apply Finset.prod_dvd_of_coprime
    · intro Q₁ hQ₁ Q₂ hQ₂ hne
      exact monic_irreducible_isCoprime p
        (hS_mem Q₁ hQ₁).1 (hS_mem Q₂ hQ₂).1
        (hS_mem Q₁ hQ₁).2.1 (hS_mem Q₂ hQ₂).2.1 hne
    · intro Q hQ
      exact monic_irreducible_dvd_X_pow_sub_X p hd.ne'
        (hS_mem Q hQ).1 (hS_mem Q hQ).2.1 (hS_mem Q hQ).2.2
  -- Degree of product = S.card * d
  have hprod_deg : (∏ Q ∈ S, Q).natDegree = S.card * d := by
    rw [Polynomial.natDegree_prod _ _ (fun Q hQ => (hS_mem Q hQ).2.1.ne_zero)]
    exact Finset.sum_const_nat (fun Q hQ => (hS_mem Q hQ).2.2)
  -- Degree of X^(p^d) - X = p^d
  have hxpd_ne : (X ^ p ^ d - X : Polynomial (ZMod p)) ≠ 0 :=
    FiniteField.X_pow_card_pow_sub_X_ne_zero (ZMod p) hd.ne' hp.out.one_lt
  have hxpd_deg : (X ^ p ^ d - X : Polynomial (ZMod p)).natDegree = p ^ d :=
    FiniteField.X_pow_card_pow_sub_X_natDegree_eq (ZMod p) hd.ne' hp.out.one_lt
  -- Degree of product ≤ degree of X^(p^d) - X
  have hdeg_le : (∏ Q ∈ S, Q).natDegree ≤ (X ^ p ^ d - X : Polynomial (ZMod p)).natDegree :=
    Polynomial.natDegree_le_of_dvd hprod_dvd hxpd_ne
  -- S.card * d ≤ p^d
  rw [hprod_deg, hxpd_deg] at hdeg_le
  exact Nat.le_div_iff_mul_le hd |>.mpr (by linarith)

/-- The irreducible count bound can be relaxed: for any K ≤ d with K > 0,
    the count of monic irreducibles of degree d is at most p^d / K.
    This follows from ff_irreducible_count_le and monotonicity of Nat.div
    in the denominator. -/
theorem ff_irreducible_count_le_div (d K : ℕ) (hd : 0 < d) (hK : K ≤ d) (hK0 : 0 < K) :
    Fintype.card {Q : Polynomial (ZMod p) | Q.Monic ∧ Irreducible Q ∧ Q.natDegree = d}
      ≤ p ^ d / K := by
  have h1 := ff_irreducible_count_le p d hd
  have h2 : p ^ d / d ≤ p ^ d / K := Nat.div_le_div_left hK hK0
  exact le_trans h1 h2

/-- For d ≥ 2, the number of monic irreducible polynomials of degree d over F_p
    is strictly less than the total number of monic polynomials of degree d (= p^d).
    This means "most" monic polynomials of degree ≥ 2 are reducible. -/
theorem ff_most_monic_are_reducible (d : ℕ) (hd : 2 ≤ d) :
    Fintype.card {Q : Polynomial (ZMod p) | Q.Monic ∧ Irreducible Q ∧ Q.natDegree = d}
      < p ^ d := by
  have hd_pos : 0 < d := by omega
  have hpd_pos : 0 < p ^ d := pos_of_gt (Nat.one_lt_pow hd_pos.ne' hp.out.one_lt)
  calc Fintype.card {Q : Polynomial (ZMod p) | Q.Monic ∧ Irreducible Q ∧ Q.natDegree = d}
      ≤ p ^ d / d := ff_irreducible_count_le p d hd_pos
    _ < p ^ d := Nat.div_lt_self hpd_pos (by omega)

end FunctionFieldAnalog
