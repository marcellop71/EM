import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.RingTheory.AdjoinRoot

/-!
# Frobenius orbits and irreducibility over `𝔽_p`

The tool behind `EM/FunctionField/StableTower.lean`, stated once for every prime `p`.

Let `L = 𝔽̄_p` and `φ : L → L` the Frobenius `x ↦ x^p`.  For `β ∈ L` algebraic over `𝔽_p`:

* the `minimalPeriod` of `β` under `φ` is at most the degree of its minimal polynomial
  (`minimalPeriod_le_natDegree_minpoly`): the iterates `φ^[i] β`, `i < minimalPeriod`, are
  distinct roots of the minimal polynomial;
* hence a monic `f ∈ 𝔽_p[X]` with a root `β` and `deg f = minimalPeriod φ β` is irreducible
  (`irreducible_of_natDegree_eq_minimalPeriod`);
* conversely a root `β` of an irreducible `f` of degree `d` satisfies `β^{p^d} = β`
  (`pow_p_pow_natDegree_eq_self`), because `𝔽_p[X]/(f)` is a field with `p^d` elements.

Together: for irreducible `f` of degree `d` with root `β`, `minimalPeriod φ β ∣ d` and
`minimalPeriod φ β ≤ d`.  A consequence used repeatedly: if `ω = P(β)` for a polynomial `P`
over `𝔽_p`, then `minimalPeriod φ ω ∣ d` (`minimalPeriod_aeval_dvd_natDegree`).

We also record the period of a primitive cube root of unity for `p ≡ 2 (mod 3)`
(`phi3_root_minimalPeriod`): it is `2`, since `ω^p = ω²`.  This is the mechanism behind the
even-degree exclusion of `EM/FunctionField/AutonomousDegrees.lean`.
-/

namespace FunctionFieldAnalog

namespace FrobeniusOrbit

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- The algebraic closure of `𝔽_p`. -/
abbrev Lp : Type := AlgebraicClosure (ZMod p)

/-- Frobenius `x ↦ x^p` on `Lp p`. -/
noncomputable abbrev φ : Lp p →+* Lp p := frobenius (Lp p) p

theorem φ_apply (x : Lp p) : φ p x = x ^ p := frobenius_def p x

theorem φ_iterate (i : ℕ) (x : Lp p) : (⇑(φ p))^[i] x = x ^ p ^ i := by
  induction i generalizing x with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', ih, φ_apply, ← pow_mul, ← pow_succ]

theorem φ_comp_algebraMap : (φ p).comp (algebraMap (ZMod p) (Lp p)) = algebraMap (ZMod p) (Lp p) := by
  ext c
  simp only [RingHom.comp_apply, φ_apply, ← map_pow, ZMod.pow_card]

/-- Frobenius commutes with evaluation of `𝔽_p`-polynomials. -/
theorem aeval_iterate (f : (ZMod p)[X]) (x : Lp p) (i : ℕ) :
    aeval ((⇑(φ p))^[i] x) f = (⇑(φ p))^[i] (aeval x f) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', aeval_def, ← φ_comp_algebraMap,
      ← hom_eval₂, ← aeval_def, ih]

theorem aeval_iterate_root {f : (ZMod p)[X]} {x : Lp p} (hx : aeval x f = 0) (i : ℕ) :
    aeval ((⇑(φ p))^[i] x) f = 0 := by
  rw [aeval_iterate, hx, Function.iterate_fixed (map_zero _)]

/-! ## 1. Period bounds the degree -/

theorem minimalPeriod_le_natDegree_minpoly {β : Lp p} (hint : IsIntegral (ZMod p) β) :
    Function.minimalPeriod (⇑(φ p)) β ≤ (minpoly (ZMod p) β).natDegree := by
  classical
  set P : (Lp p)[X] := (minpoly (ZMod p) β).map (algebraMap (ZMod p) (Lp p)) with hP
  have hP0 : P ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap (ZMod p) (Lp p)).injective).mpr (minpoly.ne_zero hint)
  have hmem : ∀ i, (⇑(φ p))^[i] β ∈ P.roots := fun i => by
    rw [mem_roots hP0, IsRoot, hP, eval_map, ← aeval_def]
    exact aeval_iterate_root p (minpoly.aeval _ _) i
  set N := Function.minimalPeriod (⇑(φ p)) β
  have hinj : Set.InjOn (fun i => (⇑(φ p))^[i] β) (Finset.range N : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hi hj).mp hij
  calc N = (Finset.range N).card := (Finset.card_range _).symm
    _ = ((Finset.range N).image (fun i => (⇑(φ p))^[i] β)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ P.roots.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        exact Multiset.mem_toFinset.mpr (hmem i)
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' _
    _ = (minpoly (ZMod p) β).natDegree := natDegree_map _

/-- A monic polynomial with a root whose Frobenius period equals the degree is irreducible. -/
theorem irreducible_of_natDegree_eq_minimalPeriod {f : (ZMod p)[X]} (hf : f.Monic) {β : Lp p}
    (hβ : aeval β f = 0) (hdeg : f.natDegree = Function.minimalPeriod (⇑(φ p)) β) :
    Irreducible f := by
  have hint : IsIntegral (ZMod p) β := ⟨f, hf, by rw [← aeval_def]; exact hβ⟩
  have hdvd : minpoly (ZMod p) β ∣ f := minpoly.dvd _ _ hβ
  have hle : f.natDegree ≤ (minpoly (ZMod p) β).natDegree := by
    rw [hdeg]; exact minimalPeriod_le_natDegree_minpoly p hint
  have heq : f = minpoly (ZMod p) β :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hf hdvd hle
  rw [heq]; exact minpoly.irreducible hint

/-! ## 2. A root of an irreducible of degree `d` lies in `𝔽_{p^d}` -/

theorem pow_p_pow_natDegree_eq_self {f : (ZMod p)[X]} (hf : Irreducible f) {β : Lp p}
    (hβ : aeval β f = 0) : β ^ p ^ f.natDegree = β := by
  classical
  have : Fact (Irreducible f) := ⟨hf⟩
  have hf0 : f ≠ 0 := hf.ne_zero
  let pb := AdjoinRoot.powerBasis hf0
  let _ : Fintype (AdjoinRoot f) := Module.fintypeOfFintype pb.basis
  have hcard : Fintype.card (AdjoinRoot f) = p ^ f.natDegree := by
    rw [Module.card_fintype pb.basis, ZMod.card, Fintype.card_fin, AdjoinRoot.powerBasis_dim]
  have hroot : AdjoinRoot.root f ^ p ^ f.natDegree = AdjoinRoot.root f := by
    rw [← hcard]; exact FiniteField.pow_card _
  have hev : f.eval₂ (algebraMap (ZMod p) (Lp p)) β = 0 := by rwa [← aeval_def]
  have := congrArg (AdjoinRoot.lift (algebraMap (ZMod p) (Lp p)) β hev) hroot
  rwa [map_pow, AdjoinRoot.lift_root] at this

theorem isPeriodicPt_natDegree {f : (ZMod p)[X]} (hf : Irreducible f) {β : Lp p}
    (hβ : aeval β f = 0) : Function.IsPeriodicPt (⇑(φ p)) f.natDegree β := by
  show (⇑(φ p))^[f.natDegree] β = β
  rw [φ_iterate]; exact pow_p_pow_natDegree_eq_self p hf hβ

/-- If `ω = P(β)` with `β` a root of the irreducible `f`, the period of `ω` divides `deg f`. -/
theorem minimalPeriod_aeval_dvd_natDegree {f : (ZMod p)[X]} (hf : Irreducible f) {β : Lp p}
    (hβ : aeval β f = 0) (P : (ZMod p)[X]) :
    Function.minimalPeriod (⇑(φ p)) (aeval β P) ∣ f.natDegree := by
  apply Function.IsPeriodicPt.minimalPeriod_dvd
  show (⇑(φ p))^[f.natDegree] (aeval β P) = aeval β P
  rw [← aeval_iterate, show (⇑(φ p))^[f.natDegree] β = β from isPeriodicPt_natDegree p hf hβ]

/-- Every nonconstant polynomial over `𝔽_p` has a root in `𝔽̄_p`. -/
theorem exists_root_of_natDegree_pos {f : (ZMod p)[X]} (hf : 0 < f.natDegree) :
    ∃ β : Lp p, aeval β f = 0 := by
  have hdeg : (f.map (algebraMap (ZMod p) (Lp p))).degree ≠ 0 := by
    rw [degree_map]
    exact (natDegree_pos_iff_degree_pos.mp hf).ne'
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_root _ hdeg
  exact ⟨β, by rwa [IsRoot, eval_map, ← aeval_def] at hβ⟩

/-- Every irreducible polynomial over `𝔽_p` has a root in `𝔽̄_p`. -/
theorem exists_aeval_eq_zero {f : (ZMod p)[X]} (hf : Irreducible f) : ∃ β : Lp p, aeval β f = 0 :=
  exists_root_of_natDegree_pos p hf.natDegree_pos

/-! ## 3. Primitive cube roots of unity have period 2 when `p ≡ 2 (mod 3)` -/

theorem phi3_root_minimalPeriod (hp3 : p % 3 = 2) {ω : Lp p} (hω : ω ^ 2 + ω + 1 = 0) :
    Function.minimalPeriod (⇑(φ p)) ω = 2 := by
  have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω0 : ω ≠ 0 := by rintro rfl; norm_num at hω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    have h : ((3 : ℕ) : Lp p) = 0 := by exact_mod_cast (by linear_combination hω : (3 : Lp p) = 0)
    rw [CharP.cast_eq_zero_iff (Lp p) p] at h
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_three).mp h
    omega
  -- `ω^p = ω²` since `p = 3k + 2` and `ω³ = 1`
  have hpow : ω ^ p = ω ^ 2 := by
    have hk : p = 3 * (p / 3) + 2 := by omega
    have hcast : ω ^ p = ω ^ (3 * (p / 3) + 2) := congrArg (fun n : ℕ => ω ^ n) hk
    rw [hcast, pow_add, pow_mul, h3, one_pow, one_mul]
  have hfix : ¬ Function.IsFixedPt (⇑(φ p)) ω := by
    intro h
    have h' : ω ^ p = ω := h
    rw [hpow] at h'
    have : ω * (ω - 1) = 0 := by linear_combination h'
    rcases mul_eq_zero.mp this with h0 | h1
    · exact hω0 h0
    · exact hω1 (sub_eq_zero.mp h1)
  have hper : Function.IsPeriodicPt (⇑(φ p)) 2 ω := by
    show (⇑(φ p))^[2] ω = ω
    rw [φ_iterate, pow_two, pow_mul, hpow, ← pow_mul, show 2 * p = p * 2 by ring, pow_mul, hpow,
      ← pow_mul]
    linear_combination ω * h3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Function.minimalPeriod_eq_prime_iff.mpr ⟨hper, hfix⟩

/-- **Even-degree exclusion.**  For `p ≡ 2 (mod 3)`, every irreducible factor of `Φ₃(P)`,
`P ∈ 𝔽_p[X]`, has even degree. -/
theorem even_natDegree_of_dvd_phi3 (hp3 : p % 3 = 2) {f P : (ZMod p)[X]} (hf : Irreducible f)
    (hdvd : f ∣ P ^ 2 + P + 1) : Even f.natDegree := by
  obtain ⟨β, hβ⟩ := exists_aeval_eq_zero p hf
  obtain ⟨g, hg⟩ := hdvd
  have hω : (aeval β P) ^ 2 + aeval β P + 1 = 0 := by
    have := congrArg (aeval β) hg
    rwa [map_mul, hβ, zero_mul, map_add, map_add, map_pow, map_one] at this
  rw [even_iff_two_dvd, ← phi3_root_minimalPeriod p hp3 hω]
  exact minimalPeriod_aeval_dvd_natDegree p hf hβ P

end FrobeniusOrbit

end FunctionFieldAnalog
