import EM.FunctionField.StochasticMC
import EM.FunctionField.WeakMC
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Finiteness of Irreducible Polynomials per Degree

Over any finite commutative ring R, there are finitely many monic polynomials
of each degree d: each is determined by its d lower-order coefficients
(the leading coefficient is fixed at 1 by the monic constraint), giving
an injection into `Fin (d+1) -> R` which is Fintype. The irreducible ones
form a subset, hence are also finite.

This proves `FFFiniteIrreduciblesPerDegree` unconditionally, eliminating
an open hypothesis from the entire FF-MC chain.

## Main results

- `monic_natDegree_finite` : for Fintype R, {Q : R[X] | Q.Monic /\ Q.natDegree = d} is finite
- `ffFiniteIrreduciblesPerDegree_proved` : FFFiniteIrreduciblesPerDegree (unconditional)
-/

namespace FunctionFieldAnalog

open Polynomial Classical

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- The coefficient map from monic degree-d polynomials to `Fin (d+1) -> R` is injective.
    Two monic polynomials of the same degree with identical coefficients at all positions
    0, 1, ..., d are equal, since higher coefficients are determined (0 above degree d). -/
private theorem coeff_injection (R : Type*) [CommRing R] (d : ℕ) :
    Function.Injective (fun (Q : {Q : Polynomial R | Q.Monic ∧ Q.natDegree = d}) (i : Fin (d + 1)) =>
      Q.val.coeff i.val) := by
  intro ⟨P, hPm, hPd⟩ ⟨Q, hQm, hQd⟩ heq
  simp only at heq
  apply Subtype.ext
  apply Polynomial.ext
  intro n
  by_cases hn : n < d + 1
  · exact congr_fun heq ⟨n, hn⟩
  · push_neg at hn
    -- n ≥ d + 1, so n > natDegree for both P and Q
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < n)]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < n)]

/-- Over any finite commutative ring, there are finitely many monic polynomials
    of each given degree. Proof: inject into `Fin (d+1) -> R` via the coefficient map. -/
theorem monic_natDegree_finite (R : Type*) [CommRing R] [Fintype R] (d : ℕ) :
    Set.Finite {Q : Polynomial R | Q.Monic ∧ Q.natDegree = d} := by
  have hinj := coeff_injection R d
  have : Finite {Q : Polynomial R | Q.Monic ∧ Q.natDegree = d} :=
    Finite.of_injective _ hinj
  exact Set.toFinite _

/-- **FFFiniteIrreduciblesPerDegree proved unconditionally.**
    The set of monic irreducible polynomials of degree d over F_p is finite,
    as a subset of the finite set of all monic polynomials of degree d. -/
theorem ffFiniteIrreduciblesPerDegree_proved :
    FFFiniteIrreduciblesPerDegree (p := p) := by
  intro d
  apply Set.Finite.subset (monic_natDegree_finite (ZMod p) d)
  intro Q ⟨hm, _, hd⟩
  exact ⟨hm, hd⟩

/-! ## Unconditional Wrappers

Now that `FFFiniteIrreduciblesPerDegree` is proved, we provide unconditional
versions of the most important downstream theorems that previously required
it as a hypothesis.
-/

/-! ### From StochasticMC.lean -/

/-- **Captured degree grows unconditionally.**
    Previously conditional on `FFFiniteIrreduciblesPerDegree`.
    Now supplied by `ffFiniteIrreduciblesPerDegree_proved`. -/
theorem ffCapturedDegreeGrows_unconditional :
    FFCapturedDegreeGrows (p := p) :=
  ff_capture_degree_grows_of_finiteness ffFiniteIrreduciblesPerDegree_proved

/-- **Finitely many small selections, unconditionally.**
    For any valid mixed selection, only finitely many steps select an
    irreducible of degree at most D. -/
theorem ff_finitely_many_small_selections_unconditional
    {start : Polynomial (ZMod p)} {σ : FFMixedSelection p}
    (hv : FFMixedSelectionValid p start σ) (D : ℕ) :
    Set.Finite {n : ℕ | (σ.sel n).natDegree ≤ D} :=
  ff_finitely_many_small_selections ffFiniteIrreduciblesPerDegree_proved hv D

/-! ### From Bootstrap.lean -/

/-- **FFDynamicalHitting alone implies FF-MC.**
    Previously required both `FFDynamicalHitting` and `FFFiniteIrreduciblesPerDegree`.
    Now finiteness is supplied unconditionally. -/
theorem ff_dh_implies_ffmc_unconditional
    (hdh : FFDynamicalHitting (p := p)) :
    FFMullinConjecture p :=
  ff_dh_implies_ffmc hdh ffFiniteIrreduciblesPerDegree_proved

/-- **Sieve gap unconditional.** Given FFMCBelow, the sieve gap holds
    without needing finiteness as a hypothesis. -/
theorem ff_sieve_gap_unconditional (d : FFEMData p) {d0 : ℕ}
    (hbelow : FFMCBelow d d0) :
    ∃ N0, ∀ n, N0 ≤ n →
      ∀ P : Polynomial (ZMod p), P.Monic → Irreducible P →
        P.natDegree < d0 → ∃ j, j ≤ n ∧ d.ffSeq j = P :=
  ff_sieve_gap d ffFiniteIrreduciblesPerDegree_proved hbelow

/-! ### From WeakMC.lean -/

/-- **Degree escape unconditional (Tendsto form).** deg(ffSeq(n)) -> infinity. -/
theorem ffSeq_degree_tendsto_atTop_unconditional (d_data : FFEMData p) :
    Filter.Tendsto (fun n => (d_data.ffSeq n).natDegree)
      Filter.atTop Filter.atTop :=
  ffSeq_degree_tendsto_atTop ffFiniteIrreduciblesPerDegree_proved d_data

/-- **Capture count stabilizes unconditionally.** -/
theorem captureCount_eventually_constant_unconditional
    (d_data : FFEMData p) (deg : ℕ) :
    ∃ N₀ C, ∀ N, N₀ ≤ N → captureCount d_data deg N = C :=
  captureCount_eventually_constant ffFiniteIrreduciblesPerDegree_proved d_data deg

/-- **Weak MC landscape unconditional.** -/
theorem ff_weak_mc_landscape_unconditional :
    -- (1) Degree escape (PROVED)
    (∀ d_data : FFEMData p,
      Filter.Tendsto (fun n => (d_data.ffSeq n).natDegree)
        Filter.atTop Filter.atTop) ∧
    -- (2) Capture count stabilizes (PROVED)
    (∀ d_data : FFEMData p, ∀ deg,
      ∃ N₀ C, ∀ N, N₀ ≤ N → captureCount d_data deg N = C) ∧
    -- (3) FFMissingFinite (trivial from finiteness)
    FFMissingFinite p ∧
    -- (4) FFCaptureExhaustive iff FFMullinConjecture
    (FFCaptureExhaustive p ↔ FFMullinConjecture p) ∧
    -- (5) FFDH -> FF-MC (from Bootstrap, unconditional finiteness)
    (FFDynamicalHitting (p := p) → FFMullinConjecture p) ∧
    -- (6) Weil -> FFDirichletEquidist
    (WeilBound p → FFDirichletEquidist p) :=
  ff_weak_mc_landscape p ffFiniteIrreduciblesPerDegree_proved

/-! ### Existence of monic irreducible polynomials of every degree -/

/-- For every d >= 1, there exists a monic irreducible polynomial of degree d over F_p.
    Proof: GaloisField p d is a degree-d extension of ZMod p. By the primitive element
    theorem (for finite fields), there exists alpha generating the extension. Its minimal
    polynomial over ZMod p is monic, irreducible, and has degree equal to the extension
    degree, which is d. -/
theorem ffExistsIrreducibleOfDegree (d : ℕ) (hd : 0 < d) :
    ∃ Q : Polynomial (ZMod p), Q.Monic ∧ Irreducible Q ∧ Q.natDegree = d := by
  -- GaloisField p d is a finite field with p^d elements, degree d over ZMod p
  haveI : Fact (Nat.Prime p) := hp
  -- Get a primitive element alpha such that (ZMod p)(alpha) = GaloisField p d
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_top (ZMod p) (GaloisField p d)
  -- The minimal polynomial of alpha over ZMod p
  let Q := minpoly (ZMod p) α
  -- alpha is integral over ZMod p (finite extension)
  have hint : IsIntegral (ZMod p) α := IsIntegral.of_finite (ZMod p) α
  -- Q is monic
  have hmonic : Q.Monic := minpoly.monic hint
  -- Q is irreducible
  have hirr : Irreducible Q := minpoly.irreducible hint
  -- Q has degree d: primitive element iff minpoly degree = finrank
  have hdeg : Q.natDegree = d := by
    rw [(Field.primitive_element_iff_minpoly_natDegree_eq (ZMod p) α).mp hα]
    exact GaloisField.finrank p hd.ne'
  exact ⟨Q, hmonic, hirr, hdeg⟩

/-! ### From MultiplierCCSB.lean -/

/-- **MultCCSB landscape unconditional in finiteness.**
    The four routes to FF-MC now only need FFMultCCSBImpliesFFDH
    (not finiteness, which is proved). -/
theorem ff_mc_mult_ccsb_landscape_unconditional
    (hbridge : FFMultCCSBImpliesFFDH p) :
    -- Route 1: MultCCSB => FF-MC
    (FFMultiplierCCSB p → FFMullinConjecture p) ∧
    -- Route 2: Weil + SBN => FF-MC
    (WeilBound p → SelectionBiasNeutral p → FFMullinConjecture p) ∧
    -- Route 3: Weil + ConditionalCharEquidist => FF-MC
    (WeilBound p → ConditionalCharEquidist p → FFMullinConjecture p) ∧
    -- Route 4: FFDSLAnalog + bridge => FF-MC
    (FFDSLImpliesFFDH p → FFDSLAnalog p → FFMullinConjecture p) :=
  ff_mc_mult_ccsb_landscape p hbridge ffFiniteIrreduciblesPerDegree_proved

end FunctionFieldAnalog
