import EM.FunctionField.CompositeFloors
import EM.FunctionField.FrobeniusOrbit
import Mathlib.FieldTheory.Finite.Extension

/-!
# The rule `minFac (N + 1)` over `𝔽_p[X]` as a statement about a fibre

A polynomial `N ∈ 𝔽_p[X]` is a self-map `x ↦ N(x)` of the affine line. The roots of `N` are
its fibre over `0`; the roots of `N + 1` are its fibre over `-1`. The map commutes with
Frobenius and `-1` is Frobenius-fixed, so Frobenius permutes the fibre over `-1`; its orbits
are the irreducible factors of `N + 1`, and the orbit length is the degree. The factor of
least degree is the point of the fibre defined over the smallest field.

This file records that frame (`docs/analysis/fibre_rule_2026-11-15.md`).

## Main results

* `exists_irreducible_dvd_iff` — `N + 1` has an irreducible factor of degree dividing `d`
  iff `-1` is a value of `N` on `𝔽_{p^d}`.
* `ffSeq_natDegree_le_of_value`, `exists_value_ffSeq` — along a sequence, the degree of the
  next term is the least `m ≠ 0` such that `-1` is a value of the running product on
  `𝔽_{p^m}`.
* `prod_add_C` — `∏_{c ∈ 𝔽_p} (N + c) = N^p - N`.
* `exists_dvd_add_C_iff` — an irreducible `f` with root `β` divides some `N + c`,
  `c ∈ 𝔽_p`, iff `N(β)` is Frobenius-fixed, i.e. `N` is constant on the roots of `f`.
* `cofactor_mul_euclid_succ` — the composite stage: if `P_n + 1 = π·c`, then
  `c · (P_{n+1} + 1) = P_n² + P_n + c`. With `c = 1` this is the prime stage, a composition
  of maps (`CompositeFloors.ffProd_succ_of_irreducible`).
* `aeval_quadratic_of_root`, `dvd_euclid_succ_iff`, `isSquare_disc_of_root` — at a root `β`
  of the next Euclid polynomial, `y = P_n(β)` solves `y² + y + c(β) = 0`; so `1 - 4·c(β)` is
  a square in `𝔽_p(β)`. This is the function-field twin of
  `QuadraticStep.isSquare_disc_of_dvd`.
-/

namespace FunctionFieldAnalog

namespace FibreRule

open Polynomial FrobeniusOrbit

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## Roots and divisibility -/

/-- An irreducible polynomial divides every polynomial vanishing at one of its roots. -/
theorem dvd_of_aeval_eq_zero {f g : (ZMod p)[X]} (hf : Irreducible f) {β : Lp p}
    (hβ : aeval β f = 0) (hg : aeval β g = 0) : f ∣ g := by
  have hint : IsIntegral (ZMod p) β := Algebra.IsIntegral.isIntegral β
  have hassoc : Associated (minpoly (ZMod p) β) f :=
    (minpoly.irreducible hint).associated_of_dvd hf (minpoly.dvd _ _ hβ)
  exact hassoc.symm.dvd.trans (minpoly.dvd _ _ hg)

/-- A root of a factor of `N + 1` lies in the fibre of `N` over `-1`. -/
theorem aeval_eq_neg_one_of_dvd {f N : (ZMod p)[X]} {β : Lp p} (hβ : aeval β f = 0)
    (h : f ∣ N + 1) : aeval β N = -1 := by
  obtain ⟨g, hg⟩ := h
  have := congrArg (aeval β) hg
  rw [map_mul, hβ, zero_mul, map_add, map_one] at this
  exact eq_neg_of_add_eq_zero_left this

/-! ## The value-set form of the rule -/

/-- **Value-set form.** `N + 1` has an irreducible factor of degree dividing `d` iff `-1` is
    a value of `N` on `𝔽_{p^d}` (the fixed points of `x ↦ x^{p^d}` in `𝔽̄_p`). -/
theorem exists_irreducible_dvd_iff (N : (ZMod p)[X]) (d : ℕ) :
    (∃ f : (ZMod p)[X], f.Monic ∧ Irreducible f ∧ f ∣ N + 1 ∧ f.natDegree ∣ d) ↔
      ∃ β : Lp p, β ^ p ^ d = β ∧ aeval β N = -1 := by
  constructor
  · rintro ⟨f, -, hf, hdvd, hd⟩
    obtain ⟨β, hβ⟩ := exists_aeval_eq_zero p hf
    refine ⟨β, ?_, aeval_eq_neg_one_of_dvd p hβ hdvd⟩
    obtain ⟨m, rfl⟩ := hd
    have := (isPeriodicPt_natDegree p hf hβ).mul_const m
    rw [← φ_iterate]
    exact this
  · rintro ⟨β, hfix, hval⟩
    have hint : IsIntegral (ZMod p) β := Algebra.IsIntegral.isIntegral β
    refine ⟨minpoly (ZMod p) β, minpoly.monic hint, minpoly.irreducible hint, ?_, ?_⟩
    · apply minpoly.dvd
      rw [map_add, map_one, hval, neg_add_cancel]
    · apply (minpoly.irreducible hint).natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
      apply minpoly.dvd
      rw [map_sub, map_pow, aeval_X, Nat.card_eq_fintype_card, ZMod.card, hfix, sub_self]

/-- The next term has degree at most `m` as soon as `-1` is a value of the running product
    on `𝔽_{p^m}`. -/
theorem ffSeq_natDegree_le_of_value (d : FFEMData p) (n m : ℕ) (hm : m ≠ 0) {β : Lp p}
    (hfix : β ^ p ^ m = β) (hval : aeval β (d.ffProd n) = -1) :
    (d.ffSeq (n + 1)).natDegree ≤ m := by
  obtain ⟨f, hmon, hirr, hdvd, hdeg⟩ :=
    (exists_irreducible_dvd_iff p _ m).mpr ⟨β, hfix, hval⟩
  exact (d.ffSeq_minimal n f hmon hirr hdvd).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdeg)

/-- The next term is the minimal polynomial of a point of the fibre over `-1` defined over
    `𝔽_{p^m}`, `m` its degree. -/
theorem exists_value_ffSeq (d : FFEMData p) (n : ℕ) :
    ∃ β : Lp p, aeval β (d.ffSeq (n + 1)) = 0 ∧
      β ^ p ^ (d.ffSeq (n + 1)).natDegree = β ∧ aeval β (d.ffProd n) = -1 := by
  obtain ⟨_, hirr, hdvd⟩ := d.ffSeq_succ n
  obtain ⟨β, hβ⟩ := exists_aeval_eq_zero p hirr
  exact ⟨β, hβ, pow_p_pow_natDegree_eq_self p hirr hβ, aeval_eq_neg_one_of_dvd p hβ hdvd⟩

/-! ## The fibres over all of `𝔽_p` -/

/-- `∏_{a ∈ 𝔽_p} (X - a) = X^p - X`. -/
theorem prod_X_sub_C : ∏ a : ZMod p, (X - C a) = (X ^ p - X : (ZMod p)[X]) := by
  have hmon : (X ^ p - X : (ZMod p)[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hp.out.one_lt)
  have hroots : (X ^ p - X : (ZMod p)[X]).roots = Finset.univ.val := by
    have := FiniteField.roots_X_pow_card_sub_X (ZMod p)
    rwa [ZMod.card] at this
  have hcard : Multiset.card (X ^ p - X : (ZMod p)[X]).roots =
      (X ^ p - X : (ZMod p)[X]).natDegree := by
    rw [hroots, FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp.out.one_lt]
    simp [ZMod.card]
  have := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon hcard
  rw [hroots] at this
  exact this

/-- **The fibres over `𝔽_p`.** `∏_{c ∈ 𝔽_p} (N + c) = N^p - N`. -/
theorem prod_add_C (N : (ZMod p)[X]) : ∏ c : ZMod p, (N + C c) = N ^ p - N := by
  have h := congrArg (fun q : (ZMod p)[X] => q.comp N) (prod_X_sub_C p)
  simp only [prod_comp, sub_comp, X_comp, C_comp, pow_comp] at h
  rw [← h]
  exact Fintype.prod_equiv (Equiv.neg (ZMod p)) _ _ (fun c => by
    simp [sub_neg_eq_add])

/-- **Levels.** An irreducible `f` with root `β` divides `N + c` for some constant `c` iff
    `N(β)` is fixed by Frobenius, i.e. `N(β) ∈ 𝔽_p`. -/
theorem exists_dvd_add_C_iff {f N : (ZMod p)[X]} (hf : Irreducible f) {β : Lp p}
    (hβ : aeval β f = 0) : (∃ c : ZMod p, f ∣ N + C c) ↔ aeval β N ^ p = aeval β N := by
  constructor
  · rintro ⟨c, g, hg⟩
    have := congrArg (aeval β) hg
    rw [map_mul, hβ, zero_mul, map_add, aeval_C] at this
    have hv : aeval β N = algebraMap (ZMod p) (Lp p) (-c) := by
      rw [map_neg]
      exact eq_neg_of_add_eq_zero_left this
    rw [hv, ← map_pow, ZMod.pow_card]
  · intro h
    have hroot : aeval β (∏ c : ZMod p, (N + C c)) = 0 := by
      rw [prod_add_C, map_sub, map_pow, h, sub_self]
    have hdvd := dvd_of_aeval_eq_zero p hf hβ hroot
    obtain ⟨c, -, hc⟩ := (hf.prime.dvd_finsetProd_iff _).mp hdvd
    exact ⟨c, hc⟩

/-! ## The two kinds of stage -/

/-- **Composite stage.** If `P_n + 1 = π·c` with `π` the chosen factor, then
    `c · (P_{n+1} + 1) = P_n² + P_n + c`. -/
theorem cofactor_mul_euclid_succ (d : FFEMData p) (n : ℕ) {c : (ZMod p)[X]}
    (hc : d.ffProd n + 1 = d.ffSeq (n + 1) * c) :
    c * (d.ffProd (n + 1) + 1) = d.ffProd n ^ 2 + d.ffProd n + c := by
  rw [d.ffProd_succ]
  linear_combination (-(d.ffProd n)) * hc

/-- At a root `β` of the next Euclid polynomial, `y = P_n(β)` solves `y² + y + c(β) = 0`. -/
theorem aeval_quadratic_of_root (d : FFEMData p) (n : ℕ) {c : (ZMod p)[X]}
    (hc : d.ffProd n + 1 = d.ffSeq (n + 1) * c) {β : Lp p}
    (hβ : aeval β (d.ffProd (n + 1) + 1) = 0) :
    aeval β (d.ffProd n) ^ 2 + aeval β (d.ffProd n) + aeval β c = 0 := by
  have := congrArg (aeval β) (cofactor_mul_euclid_succ p d n hc)
  rw [map_mul, hβ, mul_zero] at this
  simpa using this.symm

/-- Away from the cofactor, the quadratic relation characterises the next Euclid
    polynomial: an irreducible `f` with root `β`, `c(β) ≠ 0`, divides `P_{n+1} + 1` iff
    `P_n(β)² + P_n(β) + c(β) = 0`. -/
theorem dvd_euclid_succ_iff (d : FFEMData p) (n : ℕ) {c : (ZMod p)[X]}
    (hc : d.ffProd n + 1 = d.ffSeq (n + 1) * c) {f : (ZMod p)[X]} (hf : Irreducible f)
    {β : Lp p} (hβ : aeval β f = 0) (hcβ : aeval β c ≠ 0) :
    f ∣ d.ffProd (n + 1) + 1 ↔
      aeval β (d.ffProd n) ^ 2 + aeval β (d.ffProd n) + aeval β c = 0 := by
  constructor
  · rintro ⟨g, hg⟩
    exact aeval_quadratic_of_root p d n hc (by rw [hg, map_mul, hβ, zero_mul])
  · intro h
    apply dvd_of_aeval_eq_zero p hf hβ
    have := congrArg (aeval β) (cofactor_mul_euclid_succ p d n hc)
    rw [map_mul] at this
    have h0 : aeval β c * aeval β (d.ffProd (n + 1) + 1) = 0 := by
      rw [this]
      simpa using h
    exact (mul_eq_zero.mp h0).resolve_left hcβ

/-- **Splitting law.** At a root `β` of the next Euclid polynomial the discriminant
    `1 - 4·c(β)` of `y² + y + c(β)` is a square. -/
theorem isSquare_disc_of_root (d : FFEMData p) (n : ℕ) {c : (ZMod p)[X]}
    (hc : d.ffProd n + 1 = d.ffSeq (n + 1) * c) {β : Lp p}
    (hβ : aeval β (d.ffProd (n + 1) + 1) = 0) : IsSquare (1 - 4 * aeval β c) :=
  ⟨2 * aeval β (d.ffProd n) + 1, by
    linear_combination (-4 : Lp p) * aeval_quadratic_of_root p d n hc hβ⟩

end FibreRule

end FunctionFieldAnalog
