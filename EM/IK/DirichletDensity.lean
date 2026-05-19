import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting

/-!
# Dirichlet density: unconditional divergence of ∑ 1/p in invertible residue classes

This file proves, **unconditionally**, the "Dirichlet density" statement that for every
modulus `q ≥ 2` and every invertible residue class `a : ZMod q`, the sum of reciprocals
of the primes `p ≡ a (mod q)` diverges:

  `¬ Summable (fun n => if (Nat.Prime n ∧ (n : ZMod q) = a) then (1 : ℝ) / n else 0)`.

This is Dirichlet's classical argument (Dirichlet 1837; [IK] §2.3): for a non-principal
character `χ` the prime sum `G_χ(σ) = ∑_p χ(p) p^{-σ}` stays bounded as `σ → 1⁺` because
`exp` of the corresponding log-Euler sum is the L-function `L(σ,χ)`, which is continuous
and non-vanishing on the closed segment `[1,2]` (non-vanishing at `σ = 1` is Mathlib's
`DirichletCharacter.LFunction_ne_zero_of_one_le_re`); meanwhile the principal-character
prime sum diverges as `σ → 1⁺` (by `Nat.Primes.not_summable_one_div`), so by character
orthogonality the class-restricted sum `∑_{p ≡ a} p^{-σ}` is unbounded, contradicting
summability of `∑_{p ≡ a} 1/p`.

The branch-of-logarithm issue in "log L(σ,χ) is bounded" is handled via the covering-map
structure of `exp : ℂ → ℂ∖{0}` (`Complex.isCoveringMap_exp`): the prime log sum
`H_χ(σ) = ∑_p -log(1 - χ(p) p^{-σ})` is a continuous lift of `σ ↦ L(σ,χ)` on `(1,2]`, and
so is the path-lift `Γ` of `σ ↦ L(σ,χ)` along `[1,2]` starting at `H_χ(2)`; by uniqueness
of lifts on a preconnected set they agree, and `Γ` is bounded by compactness.

Part 9 upgrades the conclusion from *divergence* to *density*: the same three inputs pin
the ratio `(∑_{p ≡ a} p^{-σ}) / (∑_{p ∤ q} p^{-σ}) → 1/φ(q)` as `σ → 1⁺`, which is
Dirichlet's theorem in its density form.  Natural density (`π(x;q,a) ~ π(x)/φ(q)`) is
NOT proved here and is not reachable from this machinery: it needs PNT in arithmetic
progressions, carried by this project as the open `IK.WeightedPNTinAP` and recorded
infeasible from the existing infrastructure in Session 156.

## Main results (all PROVED, no hypotheses beyond `2 ≤ q`, `IsUnit a`)

* `nonPrincipalPrimeSumBounded` -- (core) for `χ ≠ 1`, `‖∑_p χ(p) p^{-σ}‖` is uniformly
  bounded on `1 < σ ≤ 2` (Stage B; unconditional).
* `prime_reciprocal_class_divergent` -- the headline divergence statement above.
* `tendsto_classPrimeSum_div_unitPrimeSum` -- **Dirichlet density `1/φ(q)`** of a single
  invertible class (Part 9).
* `tendsto_setPrimeSum_div_unitPrimeSum` -- Dirichlet density `|A|/φ(q)` of a `Finset` of
  invertible classes; this is the form applications consume, since a congruence condition
  unfolds by CRT into membership of a fixed `Finset` of unit classes.
* `tendsto_classPrimeSum_atTop` -- coherence: the density statement subsumes Part 8.

## Supporting statements

* `NonPrincipalPrimeSumBounded q` -- Prop-packaging of the core bound (kept as a named
  Prop so downstream files can also consume the Stage-A reduction in isolation).
* `prime_reciprocal_class_divergent_of_bounded` -- Stage A: the core bound implies the
  divergence statement (orthogonality + principal-character divergence + comparison).
* `exp_primeLogSum` -- `exp H_χ(σ) = L(σ,χ)` for `σ > 1` (Euler product, from Mathlib).
* `norm_primeTailSum_le` -- the prime-power tail `H_χ - G_χ` is uniformly bounded on
  `σ ≥ 1` by `∑_p p^{-2}`.
* `exists_lt_unitPrimeSum` -- `∑_{p ∤ q} p^{-σ}` exceeds any bound for suitable
  `σ ∈ (1,2]`.
* `re_charSum_split` -- the orthogonality sum splits as principal part plus non-principal
  remainder (shared by the divergence and density arguments).
* `unitPrimeSum_antitone` / `tendsto_unitPrimeSum_atTop` -- antitonicity in `σ` upgrades
  `exists_lt_unitPrimeSum` to a genuine limit; this is the only new ingredient in Part 9.
* `exists_nonprincipal_bound` -- the two-sided uniform error bound
  `|φ(q)·∑_{p ≡ a} p^{-σ} − ∑_{p ∤ q} p^{-σ}| ≤ Mtot` on `(1,2]`, uniform in the class.

The bridge to the repo's `PrimeReciprocalClassDivergent` / `ForbiddenClassDivergent` /
`PSCD` Props lives in `EM/Ensemble/UnconditionalPSCD.lean` (this file deliberately does
not import the ensemble framework).

## References

- [IK] H. Iwaniec, E. Kowalski, *Analytic Number Theory*, 2004, §2.3
-/

namespace IK
namespace DirichletDensity

open Complex Set

open scoped Classical

variable {q : ℕ}

/-! ## The prime sums attached to a Dirichlet character -/

/-- The prime sum `G_χ(σ) = ∑_p χ(p) p^{-σ}` (over all primes, as a complex number). -/
noncomputable def primeSum (χ : DirichletCharacter ℂ q) (σ : ℝ) : ℂ :=
  ∑' p : Nat.Primes, χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))

/-- The prime log sum `H_χ(σ) = ∑_p -log(1 - χ(p) p^{-σ})`, i.e. the logarithm of the
Euler product of `L(σ,χ)`. -/
noncomputable def primeLogSum (χ : DirichletCharacter ℂ q) (σ : ℝ) : ℂ :=
  ∑' p : Nat.Primes, -Complex.log (1 - χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ)))

/-- The prime-power tail `H_χ(σ) - G_χ(σ)` term by term. -/
noncomputable def primeTailSum (χ : DirichletCharacter ℂ q) (σ : ℝ) : ℂ :=
  ∑' p : Nat.Primes,
    (-Complex.log (1 - χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))) - χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ)))

/-- The uniform tail constant `∑_p p^{-2} < ∞`. -/
noncomputable def tailConst : ℝ := ∑' p : Nat.Primes, (p : ℝ) ^ (-2 : ℝ)

lemma norm_term_le (χ : DirichletCharacter ℂ q) (σ : ℝ) (p : Nat.Primes) :
    ‖χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))‖ ≤ (p : ℝ) ^ (-σ) := by
  rw [norm_mul]
  have h2 : ‖((p : ℕ) : ℂ) ^ (-(σ : ℂ))‖ = (p : ℝ) ^ (-σ) := by
    rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
    simp
  calc ‖χ ((p : ℕ) : ZMod q)‖ * ‖((p : ℕ) : ℂ) ^ (-(σ : ℂ))‖
      ≤ 1 * ((p : ℝ) ^ (-σ)) := by
        rw [h2]
        exact mul_le_mul_of_nonneg_right (χ.norm_le_one _) (Real.rpow_nonneg (by positivity) _)
    _ = (p : ℝ) ^ (-σ) := one_mul _

lemma summable_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => (p : ℝ) ^ (-σ)) :=
  Nat.Primes.summable_rpow.mpr (by linarith)

lemma summable_term (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))) :=
  Summable.of_norm_bounded (summable_rpow_neg hσ) (norm_term_le χ σ)

/-- Basic size estimate on the character-twisted prime term: for `σ ≥ 1` it has norm
at most `1/2`. -/
lemma norm_term_le_half (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 ≤ σ) (p : Nat.Primes) :
    ‖χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))‖ ≤ 1 / 2 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
  have h1 : (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : (p : ℝ) ^ (-1 : ℝ) ≤ 1 / 2 := by
    rw [Real.rpow_neg_one]
    rw [inv_eq_one_div]
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp2
  exact (norm_term_le χ σ p).trans (h1.trans h2)

/-- Term-wise tail bound: `‖-log(1-z) - z‖ ≤ p^{-2}` for `z = χ(p) p^{-σ}`, `σ ≥ 1`. -/
lemma norm_tail_term_le (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 ≤ σ) (p : Nat.Primes) :
    ‖-Complex.log (1 - χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))) - χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))‖
      ≤ (p : ℝ) ^ (-2 : ℝ) := by
  set z := χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ)) with hz_def
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
  have hz_half : ‖z‖ ≤ 1 / 2 := norm_term_le_half χ hσ p
  have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hz_half (by norm_num)
  have harg : (1 - z).arg ≠ Real.pi := by
    rw [sub_eq_add_neg]
    exact Complex.slitPlane_arg_ne_pi
      (Complex.mem_slitPlane_of_norm_lt_one (by rwa [norm_neg]))
  have hlog : -Complex.log (1 - z) = Complex.log (1 - z)⁻¹ := (Complex.log_inv _ harg).symm
  have hbound : ‖Complex.log (1 - z)⁻¹ - z‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 :=
    Complex.norm_log_one_sub_inv_sub_self_le hz1
  have hinv2 : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hz_sq : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖z‖ ^ 2 := sq_nonneg _
    nlinarith
  have hzn : ‖z‖ ^ 2 ≤ ((p : ℝ) ^ (-σ)) ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) (norm_term_le χ σ p)
  have hrw : ((p : ℝ) ^ (-σ)) ^ 2 = (p : ℝ) ^ (-σ * 2) := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ (-σ)) 2, ← Real.rpow_mul (by positivity)]
    norm_num
  have hfinal : (p : ℝ) ^ (-σ * 2) ≤ (p : ℝ) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  calc ‖-Complex.log (1 - z) - z‖
      = ‖Complex.log (1 - z)⁻¹ - z‖ := by rw [hlog]
    _ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := hbound
    _ ≤ ‖z‖ ^ 2 := hz_sq
    _ ≤ ((p : ℝ) ^ (-σ)) ^ 2 := hzn
    _ = (p : ℝ) ^ (-σ * 2) := hrw
    _ ≤ (p : ℝ) ^ (-2 : ℝ) := hfinal

lemma summable_sq : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-2 : ℝ)) :=
  Nat.Primes.summable_rpow.mpr (by norm_num)

lemma summable_tail_term (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 ≤ σ) :
    Summable (fun p : Nat.Primes =>
      -Complex.log (1 - χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))) -
        χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))) :=
  Summable.of_norm_bounded summable_sq (norm_tail_term_le χ hσ)

lemma norm_primeTailSum_le (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 ≤ σ) :
    ‖primeTailSum χ σ‖ ≤ tailConst := by
  rw [primeTailSum, tailConst]
  calc ‖∑' p : Nat.Primes, (-Complex.log (1 - χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))) -
          χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ)))‖
      ≤ ∑' p : Nat.Primes, ‖-Complex.log (1 - χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))) -
          χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))‖ :=
        norm_tsum_le_tsum_norm ((summable_tail_term χ hσ).norm)
    _ ≤ ∑' p : Nat.Primes, (p : ℝ) ^ (-2 : ℝ) :=
        Summable.tsum_le_tsum (norm_tail_term_le χ hσ) ((summable_tail_term χ hσ).norm)
          summable_sq

/-- Splitting of the log sum: `H_χ(σ) = G_χ(σ) + tail` for `σ > 1`. -/
lemma primeLogSum_eq (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) :
    primeLogSum χ σ = primeSum χ σ + primeTailSum χ σ := by
  rw [primeLogSum, primeSum, primeTailSum,
    ← (summable_term χ hσ).tsum_add (summable_tail_term χ hσ.le)]
  exact tsum_congr fun p => by ring

/-! ## The Euler product identity `exp H_χ(σ) = L(σ,χ)` -/

/-- For real `σ > 1`, `exp` of the prime log sum is the Dirichlet L-function. -/
lemma exp_primeLogSum [NeZero q] (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) :
    Complex.exp (primeLogSum χ σ) = DirichletCharacter.LFunction χ (σ : ℂ) := by
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs, primeLogSum]
  exact DirichletCharacter.LSeries_eulerProduct_exp_log χ hs

/-! ## Continuity of the prime sums on `σ > 1` -/

lemma continuous_term (χ : DirichletCharacter ℂ q) (p : Nat.Primes) :
    Continuous (fun σ : ℝ => χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))) := by
  apply continuous_const.mul
  apply Continuous.const_cpow (Complex.continuous_ofReal.neg)
  exact Or.inl (by exact_mod_cast p.prop.ne_zero)

lemma continuousAt_primeSum (χ : DirichletCharacter ℂ q) {σ₀ : ℝ} (hσ₀ : 1 < σ₀) :
    ContinuousAt (primeSum χ) σ₀ := by
  set a := (1 + σ₀) / 2 with ha_def
  have ha1 : 1 < a := by rw [ha_def]; linarith
  have haσ : a < σ₀ := by rw [ha_def]; linarith
  have hcont : ContinuousOn (primeSum χ) (Ici a) := by
    apply continuousOn_tsum (u := fun p : Nat.Primes => (p : ℝ) ^ (-a))
      (fun p => (continuous_term χ p).continuousOn) (summable_rpow_neg ha1)
    intro p σ hσ
    refine (norm_term_le χ σ p).trans ?_
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      have := p.prop.two_le
      exact_mod_cast le_trans (by norm_num) this
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by exact neg_le_neg hσ)
  exact hcont.continuousAt (Ici_mem_nhds haσ)

lemma continuousAt_primeTailSum (χ : DirichletCharacter ℂ q) {σ₀ : ℝ} (hσ₀ : 1 < σ₀) :
    ContinuousAt (primeTailSum χ) σ₀ := by
  have hcont : ContinuousOn (primeTailSum χ) (Ici 1) := by
    apply continuousOn_tsum (u := fun p : Nat.Primes => (p : ℝ) ^ (-2 : ℝ))
      ?_ summable_sq (fun p σ hσ => norm_tail_term_le χ hσ p)
    intro p σ hσ
    apply ContinuousAt.continuousWithinAt
    have hterm : ContinuousAt (fun σ : ℝ => χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))) σ :=
      (continuous_term χ p).continuousAt
    have hne : (1 - χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))) ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      have hhalf : ‖χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))‖ ≤ 1 / 2 := norm_term_le_half χ hσ p
      have hre : |(χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))).re| ≤ 1 / 2 :=
        le_trans (Complex.abs_re_le_norm _) hhalf
      have : (1 - χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))).re =
          1 - (χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))).re := by
        simp [Complex.sub_re]
      rw [this]
      have := abs_le.mp hre
      linarith [this.2]
    have hlog : ContinuousAt (fun σ : ℝ =>
        Complex.log (1 - χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ)))) σ :=
      ContinuousAt.clog (continuousAt_const.sub hterm) hne
    exact (hlog.neg).sub hterm
  exact hcont.continuousAt (Ici_mem_nhds hσ₀)

lemma continuousAt_primeLogSum (χ : DirichletCharacter ℂ q) {σ₀ : ℝ} (hσ₀ : 1 < σ₀) :
    ContinuousAt (primeLogSum χ) σ₀ := by
  have heq : ∀ᶠ σ in nhds σ₀, primeSum χ σ + primeTailSum χ σ = primeLogSum χ σ := by
    filter_upwards [Ioi_mem_nhds hσ₀] with σ hσ
    exact (primeLogSum_eq χ hσ).symm
  exact ContinuousAt.congr ((continuousAt_primeSum χ hσ₀).add (continuousAt_primeTailSum χ hσ₀))
    heq

/-! ## Stage B: the core boundedness theorem for non-principal characters -/

/-- **(core)** Boundedness of the non-principal prime sums on `(1,2]`, as a named Prop. -/
def NonPrincipalPrimeSumBounded (q : ℕ) : Prop :=
  ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
    ∃ M : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖primeSum χ σ‖ ≤ M

/-- **Stage B (PROVED)**: for a non-principal Dirichlet character `χ` mod `q`, the prime sum
`G_χ(σ) = ∑_p χ(p) p^{-σ}` is uniformly bounded for `σ ∈ (1,2]`.

Proof: `exp H_χ(σ) = L(σ,χ)`, which is continuous and non-vanishing on `[1,2]`
(non-vanishing at `1` is the deep input, from Mathlib's `Nonvanishing` file). Lift the
path `σ ↦ L(σ,χ)`, `σ ∈ [1,2]`, through the covering `exp : ℂ → ℂ∖{0}`, starting at
`H_χ(2)`; by uniqueness of lifts on the preconnected set `(1,2]`, the lift agrees with
`H_χ` there, and it is bounded by compactness of `[1,2]`. Finally
`G_χ = H_χ - tail` with the tail uniformly bounded. -/
theorem primeSum_bounded_of_ne_one [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    ∃ M : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖primeSum χ σ‖ ≤ M := by
  -- The L-function restricted to the real axis.
  set LC : ℝ → ℂ := fun σ => DirichletCharacter.LFunction χ (σ : ℂ) with hLC_def
  have hLC_cont : Continuous LC :=
    (DirichletCharacter.differentiable_LFunction hχ).continuous.comp Complex.continuous_ofReal
  have hLC_ne : ∀ σ : ℝ, 1 ≤ σ → LC σ ≠ 0 := by
    intro σ hσ
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using hσ)
  -- The path `t ↦ L(2 - t, χ)` in `ℂ∖{0}`, `t ∈ [0,1]`.
  have hmem : ∀ t : unitInterval, (1 : ℝ) ≤ 2 - (t : ℝ) := fun t => by
    have := t.2.2; linarith
  set γ : C(unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun t => ⟨LC (2 - (t : ℝ)), hLC_ne _ (hmem t)⟩, by
      apply Continuous.subtype_mk
      exact hLC_cont.comp (continuous_const.sub continuous_subtype_val)⟩ with hγ_def
  set e : ℂ := primeLogSum χ 2 with he_def
  have hγ0 : γ 0 = ⟨Complex.exp e, Complex.exp_ne_zero e⟩ := by
    apply Subtype.ext
    show LC (2 - ((0 : unitInterval) : ℝ)) = Complex.exp e
    have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
    rw [h0, sub_zero, he_def, exp_primeLogSum χ (by norm_num : (1:ℝ) < 2)]
  -- Lift the path through the covering `exp`.
  obtain ⟨Γ, hΓ, hΓ0⟩ := Complex.isCoveringMap_exp.exists_path_lifts γ e hγ0
  -- Transport the lift back to the real parameter `σ = 2 - t`.
  set Γ' : ℝ → ℂ := fun σ => Γ (Set.projIcc 0 1 zero_le_one (2 - σ)) with hΓ'_def
  have hΓ'_cont : Continuous Γ' :=
    Γ.continuous.comp (continuous_projIcc.comp (continuous_const.sub continuous_id))
  have hΓ'_exp : ∀ σ ∈ Icc (1 : ℝ) 2, Complex.exp (Γ' σ) = LC σ := by
    intro σ hσ
    have hmemσ : 2 - σ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    have hproj : Set.projIcc 0 1 zero_le_one (2 - σ) = ⟨2 - σ, hmemσ⟩ :=
      Set.projIcc_of_mem zero_le_one hmemσ
    have happ := congrFun hΓ (Set.projIcc 0 1 zero_le_one (2 - σ))
    have hval : Complex.exp (Γ (Set.projIcc 0 1 zero_le_one (2 - σ))) =
        LC (2 - ((Set.projIcc 0 1 zero_le_one (2 - σ) : unitInterval) : ℝ)) :=
      congrArg Subtype.val happ
    rw [hΓ'_def]
    simp only []
    rw [hval, hproj]
    norm_num
  have hΓ'_2 : Γ' 2 = e := by
    rw [hΓ'_def]
    simp only []
    have h20 : (2 : ℝ) - 2 = 0 := by norm_num
    rw [h20, Set.projIcc_left]
    exact hΓ0
  -- The two lifts agree on `(1,2]` by uniqueness of lifts.
  have hHcont : ContinuousOn (primeLogSum χ) (Ioc (1 : ℝ) 2) := fun σ hσ =>
    (continuousAt_primeLogSum χ hσ.1).continuousWithinAt
  have heqOn : Set.EqOn (primeLogSum χ) Γ' (Ioc (1 : ℝ) 2) := by
    apply Complex.isCoveringMap_exp.eqOn_of_comp_eqOn isPreconnected_Ioc hHcont
      hΓ'_cont.continuousOn ?_ (right_mem_Ioc.mpr one_lt_two) (by rw [hΓ'_2])
    intro σ hσ
    apply Subtype.ext
    show Complex.exp (primeLogSum χ σ) = Complex.exp (Γ' σ)
    rw [exp_primeLogSum χ hσ.1, hΓ'_exp σ ⟨hσ.1.le, hσ.2⟩]
  -- Conclude by compactness.
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hΓ'_cont.continuousOn
  refine ⟨M₀ + tailConst, fun σ h1 h2 => ?_⟩
  have hH : ‖primeLogSum χ σ‖ ≤ M₀ := by
    rw [heqOn ⟨h1, h2⟩]
    exact hM₀ σ ⟨h1.le, h2⟩
  have hsplit : primeSum χ σ = primeLogSum χ σ - primeTailSum χ σ := by
    rw [primeLogSum_eq χ h1]; ring
  calc ‖primeSum χ σ‖ = ‖primeLogSum χ σ - primeTailSum χ σ‖ := by rw [hsplit]
    _ ≤ ‖primeLogSum χ σ‖ + ‖primeTailSum χ σ‖ := norm_sub_le _ _
    _ ≤ M₀ + tailConst := add_le_add hH (norm_primeTailSum_le χ h1.le)

/-- The core Prop holds unconditionally. -/
theorem nonPrincipalPrimeSumBounded (q : ℕ) [NeZero q] : NonPrincipalPrimeSumBounded q :=
  fun _ hχ => primeSum_bounded_of_ne_one hχ

/-! ## Stage A: orthogonality and the class-restricted prime sums -/

/-- Summand of the class-restricted prime sum. -/
noncomputable def classTerm (a : ZMod q) (σ : ℝ) (p : Nat.Primes) : ℝ :=
  if ((p : ℕ) : ZMod q) = a then (p : ℝ) ^ (-σ) else 0

/-- The class-restricted prime sum `∑_{p ≡ a (q)} p^{-σ}` (a real number). -/
noncomputable def classPrimeSum (a : ZMod q) (σ : ℝ) : ℝ :=
  ∑' p : Nat.Primes, classTerm a σ p

/-- Summand of the prime sum over `p ∤ q`. -/
noncomputable def unitTerm (q : ℕ) (σ : ℝ) (p : Nat.Primes) : ℝ :=
  if IsUnit ((p : ℕ) : ZMod q) then (p : ℝ) ^ (-σ) else 0

/-- The prime sum over primes not dividing `q`: `∑_{p ∤ q} p^{-σ}` (a real number). -/
noncomputable def unitPrimeSum (q : ℕ) (σ : ℝ) : ℝ :=
  ∑' p : Nat.Primes, unitTerm q σ p

lemma classTerm_nonneg (a : ZMod q) (σ : ℝ) (p : Nat.Primes) : 0 ≤ classTerm a σ p := by
  rw [classTerm]
  split_ifs
  · positivity
  · exact le_rfl

lemma classTerm_le (a : ZMod q) (σ : ℝ) (p : Nat.Primes) : classTerm a σ p ≤ (p : ℝ) ^ (-σ) := by
  rw [classTerm]
  split_ifs
  · exact le_rfl
  · positivity

lemma unitTerm_nonneg (q : ℕ) (σ : ℝ) (p : Nat.Primes) : 0 ≤ unitTerm q σ p := by
  rw [unitTerm]
  split_ifs
  · positivity
  · exact le_rfl

lemma unitTerm_le (q : ℕ) (σ : ℝ) (p : Nat.Primes) : unitTerm q σ p ≤ (p : ℝ) ^ (-σ) := by
  rw [unitTerm]
  split_ifs
  · exact le_rfl
  · positivity

lemma summable_classTerm (a : ZMod q) {σ : ℝ} (hσ : 1 < σ) : Summable (classTerm a σ) :=
  Summable.of_nonneg_of_le (classTerm_nonneg a σ) (classTerm_le a σ) (summable_rpow_neg hσ)

lemma summable_unitTerm (q : ℕ) {σ : ℝ} (hσ : 1 < σ) : Summable (unitTerm q σ) :=
  Summable.of_nonneg_of_le (unitTerm_nonneg q σ) (unitTerm_le q σ) (summable_rpow_neg hσ)

/-- Cast identity for the prime power. -/
lemma term_cast (p : Nat.Primes) (σ : ℝ) :
    (p : ℂ) ^ (-(σ : ℂ)) = (((p : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ (p : ℝ)) (-σ), Complex.ofReal_neg]
  norm_cast

/-- **Orthogonality**: `φ(q) · ∑_{p ≡ a} p^{-σ} = Re ∑_χ χ(a⁻¹) G_χ(σ)` for a unit
class `a` and `σ > 1`. -/
lemma totient_mul_classPrimeSum [NeZero q] {a : ZMod q} (ha : IsUnit a) {σ : ℝ}
    (hσ : 1 < σ) :
    (q.totient : ℝ) * classPrimeSum a σ =
      (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * primeSum χ σ).re := by
  have hsum : ∀ χ : DirichletCharacter ℂ q,
      Summable (fun p : Nat.Primes => χ a⁻¹ * (χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ)))) :=
    fun χ => (summable_term χ hσ).mul_left _
  have hsum' : Summable (fun p : Nat.Primes => ((classTerm a σ p : ℝ) : ℂ)) :=
    summable_ofReal.mpr (summable_classTerm a hσ)
  have step1 : ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * primeSum χ σ =
      ∑ χ : DirichletCharacter ℂ q,
        ∑' p : Nat.Primes, χ a⁻¹ * (χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))) := by
    apply Finset.sum_congr rfl
    intro χ _
    rw [primeSum, tsum_mul_left]
  have step2 : ∑ χ : DirichletCharacter ℂ q,
      ∑' p : Nat.Primes, χ a⁻¹ * (χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))) =
      ∑' p : Nat.Primes, ∑ χ : DirichletCharacter ℂ q,
        χ a⁻¹ * (χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))) :=
    (Summable.tsum_finsetSum (fun χ _ => hsum χ)).symm
  have step3 : ∀ p : Nat.Primes,
      ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ))) =
      (q.totient : ℂ) * ((classTerm a σ p : ℝ) : ℂ) := by
    intro p
    have horth := DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha (((p : ℕ) : ZMod q))
    calc ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (χ (p : ℕ) * (p : ℂ) ^ (-(σ : ℂ)))
        = (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ (p : ℕ)) * (p : ℂ) ^ (-(σ : ℂ)) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun χ _ => by ring
      _ = (if a = ((p : ℕ) : ZMod q) then (q.totient : ℂ) else 0) * (p : ℂ) ^ (-(σ : ℂ)) := by
          rw [horth]
      _ = (q.totient : ℂ) * ((classTerm a σ p : ℝ) : ℂ) := by
          rw [classTerm]
          rcases eq_or_ne (((p : ℕ) : ZMod q)) a with h | h
          · rw [if_pos h.symm, if_pos h, term_cast]
          · rw [if_neg (Ne.symm h), if_neg h, zero_mul, Complex.ofReal_zero, mul_zero]
  have step4 : (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * primeSum χ σ) =
      (((q.totient : ℝ)) : ℂ) * ∑' p : Nat.Primes, ((classTerm a σ p : ℝ) : ℂ) := by
    rw [step1, step2, tsum_congr step3, tsum_mul_left]
    norm_cast
  rw [step4, Complex.re_ofReal_mul]
  congr 1
  rw [Complex.re_tsum hsum', classPrimeSum]
  exact tsum_congr fun p => (Complex.ofReal_re _).symm

/-- **Splitting off the principal character**: the real part of the orthogonality sum is
the prime sum over `p ∤ q` plus the non-principal contribution.

Extracted from `re_charSum_ge` so that the density argument of Part 9 can use the
*two-sided* estimate rather than just the lower bound. -/
lemma re_charSum_split [NeZero q] {a : ZMod q} (ha : IsUnit a) {σ : ℝ} (hσ : 1 < σ) :
    (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * primeSum χ σ).re =
      unitPrimeSum q σ +
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          χ a⁻¹ * primeSum χ σ).re := by
  have ha_inv : IsUnit (a⁻¹ : ZMod q) :=
    IsUnit.of_mul_eq_one a (ZMod.inv_mul_of_unit a ha)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ q)),
    Complex.add_re]
  congr 1
  -- the principal term is exactly the prime sum over `p ∤ q`
  rw [MulChar.one_apply ha_inv, one_mul, primeSum,
    Complex.re_tsum (summable_term (1 : DirichletCharacter ℂ q) hσ), unitPrimeSum]
  apply tsum_congr
  intro p
  rw [unitTerm]
  rcases em (IsUnit ((p : ℕ) : ZMod q)) with h | h
  · rw [if_pos h, MulChar.one_apply h, one_mul, term_cast, Complex.ofReal_re]
  · rw [if_neg h, MulChar.map_nonunit _ h, zero_mul, Complex.zero_re]

/-- Lower bound: the character sum's real part dominates the principal part minus the
non-principal contributions. -/
lemma re_charSum_ge [NeZero q] {a : ZMod q} (ha : IsUnit a) {σ : ℝ} (hσ : 1 < σ)
    (M : DirichletCharacter ℂ q → ℝ)
    (hM : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖primeSum χ σ‖ ≤ M χ) :
    unitPrimeSum q σ - ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), M χ ≤
      (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * primeSum χ σ).re := by
  rw [re_charSum_split ha hσ]
  -- non-principal terms
  have hrest : -(∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), M χ) ≤
      (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), χ a⁻¹ * primeSum χ σ).re := by
    rw [Complex.re_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro χ hχ
    have hχ1 : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
    have h1 : |(χ a⁻¹ * primeSum χ σ).re| ≤ ‖χ a⁻¹ * primeSum χ σ‖ :=
      Complex.abs_re_le_norm _
    have h2 : ‖χ a⁻¹ * primeSum χ σ‖ ≤ M χ := by
      rw [norm_mul]
      calc ‖χ a⁻¹‖ * ‖primeSum χ σ‖ ≤ 1 * ‖primeSum χ σ‖ :=
            mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)
        _ = ‖primeSum χ σ‖ := one_mul _
        _ ≤ M χ := hM χ hχ1
    have := abs_le.mp h1
    linarith [this.1]
  linarith [hrest]

/-! ## Divergence of the principal part as `σ → 1⁺` -/

set_option maxHeartbeats 1000000 in
/-- The prime sum over `p ∤ q` exceeds any given bound for suitable `σ ∈ (1,2]`. -/
lemma exists_lt_unitPrimeSum (q : ℕ) [NeZero q] (B : ℝ) :
    ∃ σ : ℝ, 1 < σ ∧ σ ≤ 2 ∧ B < unitPrimeSum q σ := by
  set K := (q.primeFactors.card : ℝ) with hK_def
  -- A finite set of primes with reciprocal sum exceeding `B + K`.
  have hex : ∃ F : Finset Nat.Primes, B + K < ∑ p ∈ F, (1 / (p : ℝ)) := by
    by_contra hcon
    push Not at hcon
    exact Nat.Primes.not_summable_one_div
      (summable_of_sum_le (fun p => by positivity) hcon)
  obtain ⟨F, hF⟩ := hex
  set P : Nat.Primes → Prop := fun p => (p : ℕ) ∣ q with hP_def
  set F' : Finset Nat.Primes := F.filter (fun p => ¬ P p) with hF'_def
  set D : Finset Nat.Primes := F.filter (fun p => P p) with hD_def
  -- The primes dividing `q` contribute at most `K`.
  have hD_le : ∑ p ∈ D, (1 / (p : ℝ)) ≤ K := by
    have hcard : D.card ≤ q.primeFactors.card := by
      apply Finset.card_le_card_of_injOn (fun p : Nat.Primes => (p : ℕ))
      · intro p hp
        rw [Finset.mem_coe, hD_def, Finset.mem_filter] at hp
        exact Nat.mem_primeFactors.mpr ⟨p.prop, hp.2, NeZero.ne q⟩
      · intro p _ p' _ h
        exact Subtype.ext h
    calc ∑ p ∈ D, (1 / (p : ℝ)) ≤ ∑ _p ∈ D, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro p _
          have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
            have := p.prop.two_le
            exact_mod_cast le_trans (by norm_num) this
          rw [div_le_one (by linarith)]
          exact hp1
      _ = D.card := by simp
      _ ≤ K := by rw [hK_def]; exact_mod_cast hcard
  have hsplit : ∑ p ∈ F', (1 / (p : ℝ)) + ∑ p ∈ D, (1 / (p : ℝ)) = ∑ p ∈ F, (1 / (p : ℝ)) := by
    rw [hF'_def, hD_def, add_comm]
    exact Finset.sum_filter_add_sum_filter_not F P _
  have hF' : B < ∑ p ∈ F', (1 / (p : ℝ)) := by linarith
  -- The finite sum `σ ↦ ∑_{p ∈ F'} p^{-σ}` is continuous and exceeds `B` at `σ = 1`.
  set ψ : ℝ → ℝ := fun σ => ∑ p ∈ F', (p : ℝ) ^ (-σ) with hψ_def
  have hψ_cont : Continuous ψ := by
    apply continuous_finsetSum
    intro p _
    have hp0 : (p : ℝ) ≠ 0 := by
      have := p.prop.pos
      positivity
    exact (Real.continuous_const_rpow hp0).comp continuous_neg
  have hψ1 : ψ 1 = ∑ p ∈ F', (1 / (p : ℝ)) := by
    rw [hψ_def]
    apply Finset.sum_congr rfl
    intro p _
    rw [Real.rpow_neg_one, inv_eq_one_div]
  have hψ1B : B < ψ 1 := by rw [hψ1]; exact hF'
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hψ_cont.continuousAt (ψ 1 - B)
    (by linarith)
  set σ := 1 + min (δ / 2) 1 with hσ_def
  have hσ1 : 1 < σ := by
    rw [hσ_def]
    have : (0 : ℝ) < min (δ / 2) 1 := lt_min (by linarith) one_pos
    linarith
  have hσ2 : σ ≤ 2 := by
    rw [hσ_def]
    have : min (δ / 2) 1 ≤ 1 := min_le_right _ _
    linarith
  have hσδ : dist σ 1 < δ := by
    rw [hσ_def, Real.dist_eq]
    have h1 : (0 : ℝ) < min (δ / 2) 1 := lt_min (by linarith) one_pos
    have h2 : min (δ / 2) 1 ≤ δ / 2 := min_le_left _ _
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hψσ : B < ψ σ := by
    have := hδ hσδ
    rw [Real.dist_eq] at this
    have h1 := abs_lt.mp this
    linarith [h1.1]
  -- Compare with the full prime sum.
  refine ⟨σ, hσ1, hσ2, lt_of_lt_of_le hψσ ?_⟩
  have hψ_eq : ψ σ = ∑ p ∈ F', unitTerm q σ p := by
    rw [hψ_def]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hF'_def, Finset.mem_filter] at hp
    rw [unitTerm, if_pos ((ZMod.isUnit_prime_iff_not_dvd p.prop).mpr hp.2)]
  rw [hψ_eq, unitPrimeSum]
  exact Summable.sum_le_tsum F' (fun p _ => unitTerm_nonneg q σ p) (summable_unitTerm q hσ1)

/-! ## Stage A conclusion: divergence of the class-restricted reciprocal sum -/

/-- **Stage A**: the core bound implies divergence of `∑_{p ≡ a} 1/p` for every unit
class `a` mod `q ≥ 2`. Stated with the core bound as an explicit hypothesis so that the
reduction is usable independently of Stage B. -/
theorem prime_reciprocal_class_divergent_of_bounded {q : ℕ} (hq : 2 ≤ q) {a : ZMod q}
    (ha : IsUnit a) (hcore : NonPrincipalPrimeSumBounded q) :
    ¬Summable (fun n : ℕ => if (Nat.Prime n ∧ (n : ZMod q) = a) then (1 : ℝ) / n else 0) := by
  have : NeZero q := ⟨by omega⟩
  intro hS
  set g : ℕ → ℝ := fun n => if (Nat.Prime n ∧ (n : ZMod q) = a) then (1 : ℝ) / n else 0
    with hg_def
  have hg0 : ∀ n, 0 ≤ g n := by
    intro n
    simp only [hg_def]
    split_ifs
    · positivity
    · exact le_refl 0
  set S := ∑' n, g n with hS_def
  -- Choose uniform bounds for the non-principal prime sums.
  set M : DirichletCharacter ℂ q → ℝ := fun χ =>
    if h : χ ≠ 1 then (hcore χ h).choose else 0 with hM_def
  have hM : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖primeSum χ σ‖ ≤ M χ := by
    intro χ hχ σ h1 h2
    simp only [hM_def]
    rw [dif_pos hχ]
    exact (hcore χ hχ).choose_spec σ h1 h2
  set Mtot := ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), M χ with hMtot_def
  -- The class prime sum is dominated by `S`, uniformly in `σ ∈ (1,2]`.
  have hclass_le : ∀ σ : ℝ, 1 < σ → classPrimeSum a σ ≤ S := by
    intro σ hσ
    have hle : ∀ p : Nat.Primes, classTerm a σ p ≤ g (p : ℕ) := by
      intro p
      rw [classTerm]
      rcases em (((p : ℕ) : ZMod q) = a) with h | h
      · rw [if_pos h]
        simp only [hg_def]
        rw [if_pos ⟨p.prop, h⟩]
        have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
          have := p.prop.two_le
          exact_mod_cast le_trans (by norm_num) this
        calc (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
          _ = 1 / (p : ℝ) := by rw [Real.rpow_neg_one, inv_eq_one_div]
      · rw [if_neg h]
        exact hg0 _
    have hsub : Summable (fun p : Nat.Primes => g (p : ℕ)) := hS.subtype _
    calc classPrimeSum a σ
        ≤ ∑' p : Nat.Primes, g (p : ℕ) :=
          Summable.tsum_le_tsum hle (summable_classTerm a hσ) hsub
      _ ≤ ∑' n, g n := Summable.tsum_subtype_le g {n | n.Prime} hg0 hS
      _ = S := hS_def.symm
  -- The key uniform bound on `(1,2]`.
  have key : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → unitPrimeSum q σ ≤ (q.totient : ℝ) * S + Mtot := by
    intro σ h1 h2
    have h3 := totient_mul_classPrimeSum ha h1
    have h4 := re_charSum_ge ha h1 M (fun χ hχ => hM χ hχ σ h1 h2)
    have h5 := hclass_le σ h1
    have h6 : (q.totient : ℝ) * classPrimeSum a σ ≤ (q.totient : ℝ) * S :=
      mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg _)
    -- h4 : unitPrimeSum - Mtot ≤ re; h3 : totient * classPrimeSum = re
    rw [← h3] at h4
    rw [← hMtot_def] at h4
    linarith
  obtain ⟨σ, h1, h2, h3⟩ := exists_lt_unitPrimeSum q ((q.totient : ℝ) * S + Mtot)
  exact absurd (key σ h1 h2) (not_le.mpr h3)

/-- **MAIN THEOREM (unconditional)**: for `q ≥ 2` and a unit class `a : ZMod q`, the sum of
reciprocals of the primes `p ≡ a (mod q)` diverges. This is the statement of the repo's
`PrimeReciprocalClassDivergent q a` (see `EM/Ensemble/UnconditionalPSCD.lean` for the
bridge). -/
theorem prime_reciprocal_class_divergent {q : ℕ} (hq : 2 ≤ q) {a : ZMod q} (ha : IsUnit a) :
    ¬Summable (fun n : ℕ => if (Nat.Prime n ∧ (n : ZMod q) = a) then (1 : ℝ) / n else 0) :=
  haveI : NeZero q := ⟨by omega⟩
  prime_reciprocal_class_divergent_of_bounded hq ha (nonPrincipalPrimeSumBounded q)

/-! ## Part 9: Dirichlet density

The divergence statement above throws away most of what orthogonality gives.  The same
three inputs — orthogonality (`totient_mul_classPrimeSum`), boundedness of the
non-principal prime sums (`primeSum_bounded_of_ne_one`), and unboundedness of the
principal part (`exists_lt_unitPrimeSum`) — pin the *ratio*

  `(∑_{p ≡ a} p^{-σ}) / (∑_{p ∤ q} p^{-σ}) → 1/φ(q)`  as `σ → 1⁺`,

which is Dirichlet's theorem in its **density** form.

Two things make this the right form to state.  First, it is genuinely what the argument
proves: the error `|φ(q)·∑_{p ≡ a} p^{-σ} − ∑_{p ∤ q} p^{-σ}|` is bounded uniformly on
`(1,2]`, and the denominator blows up, so the ratio is pinned.  Second, *natural* density
(`π(x;q,a) ~ π(x)/φ(q)`) is not available: it needs PNT in arithmetic progressions, which
Mathlib does not have and which this project carries as the open hypothesis
`IK.WeightedPNTinAP` (recorded infeasible from the existing infrastructure in Session
156).  Dirichlet density is the strongest form reachable unconditionally here.

The new ingredient beyond Parts 1–8 is that `unitPrimeSum q` is **antitone** in `σ`, which
upgrades `exists_lt_unitPrimeSum` (unbounded *somewhere* on `(1,2]`) to a genuine limit
`unitPrimeSum q σ → ∞` as `σ → 1⁺`. -/

/-! ### Monotonicity of the principal part -/

lemma unitTerm_antitone (q : ℕ) {σ₁ σ₂ : ℝ} (h : σ₁ ≤ σ₂) (p : Nat.Primes) :
    unitTerm q σ₂ p ≤ unitTerm q σ₁ p := by
  rw [unitTerm, unitTerm]
  split_ifs with _hu
  · refine Real.rpow_le_rpow_of_exponent_le ?_ (by linarith)
    exact_mod_cast p.prop.one_lt.le
  · exact le_rfl

lemma unitPrimeSum_antitone (q : ℕ) {σ₁ σ₂ : ℝ} (h1 : 1 < σ₁) (h : σ₁ ≤ σ₂) :
    unitPrimeSum q σ₂ ≤ unitPrimeSum q σ₁ :=
  Summable.tsum_le_tsum (unitTerm_antitone q h)
    (summable_unitTerm q (lt_of_lt_of_le h1 h)) (summable_unitTerm q h1)

/-- **The principal part diverges as `σ → 1⁺`.**  `exists_lt_unitPrimeSum` gives a large
value at *some* `σ ∈ (1,2]`; antitonicity propagates it to the whole interval `(1,σ]`,
which is a neighbourhood of `1` within `(1,∞)`. -/
theorem tendsto_unitPrimeSum_atTop (q : ℕ) [NeZero q] :
    Filter.Tendsto (unitPrimeSum q) (nhdsWithin 1 (Set.Ioi 1)) Filter.atTop := by
  refine Filter.tendsto_atTop.mpr fun B => ?_
  obtain ⟨σ₀, h1, _h2, h3⟩ := exists_lt_unitPrimeSum q B
  filter_upwards [Ioc_mem_nhdsGT h1] with σ hσ
  exact le_trans h3.le (unitPrimeSum_antitone q hσ.1 hσ.2)

/-! ### The uniform error bound -/

/-- The non-principal contribution is bounded by the sum of the individual bounds. -/
lemma abs_re_nonprincipal_le [NeZero q] (a : ZMod q) {σ : ℝ}
    (M : DirichletCharacter ℂ q → ℝ)
    (hM : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖primeSum χ σ‖ ≤ M χ) :
    |(∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), χ a⁻¹ * primeSum χ σ).re| ≤
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), M χ := by
  set E := Finset.univ.erase (1 : DirichletCharacter ℂ q) with hE
  calc |(∑ χ ∈ E, χ a⁻¹ * primeSum χ σ).re|
      ≤ ‖∑ χ ∈ E, χ a⁻¹ * primeSum χ σ‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ χ ∈ E, ‖χ a⁻¹ * primeSum χ σ‖ := norm_sum_le _ _
    _ ≤ ∑ χ ∈ E, M χ := by
        refine Finset.sum_le_sum fun χ hχ => ?_
        have hχ1 : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
        rw [norm_mul]
        calc ‖χ a⁻¹‖ * ‖primeSum χ σ‖ ≤ 1 * ‖primeSum χ σ‖ :=
              mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)
          _ = ‖primeSum χ σ‖ := one_mul _
          _ ≤ M χ := hM χ hχ1

/-- **The uniform error bound.**  There is a single constant `Mtot`, depending only on `q`,
with `|φ(q)·∑_{p ≡ a} p^{-σ} − ∑_{p ∤ q} p^{-σ}| ≤ Mtot` for *every* unit class `a` and
every `σ ∈ (1,2]`.  This is orthogonality plus Stage B, kept two-sided. -/
lemma exists_nonprincipal_bound (q : ℕ) [NeZero q] :
    ∃ Mtot : ℝ, 0 ≤ Mtot ∧ ∀ a : ZMod q, IsUnit a → ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      |(q.totient : ℝ) * classPrimeSum a σ - unitPrimeSum q σ| ≤ Mtot := by
  set M : DirichletCharacter ℂ q → ℝ := fun χ =>
    if h : χ ≠ 1 then (nonPrincipalPrimeSumBounded q χ h).choose else 0 with hM_def
  have hM : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖primeSum χ σ‖ ≤ M χ := by
    intro χ hχ σ h1 h2
    simp only [hM_def]
    rw [dif_pos hχ]
    exact (nonPrincipalPrimeSumBounded q χ hχ).choose_spec σ h1 h2
  refine ⟨∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), M χ, ?_, ?_⟩
  · refine Finset.sum_nonneg fun χ hχ => ?_
    have hχ1 : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
    exact le_trans (norm_nonneg _) (hM χ hχ1 2 (by norm_num) le_rfl)
  · intro a ha σ h1 h2
    rw [totient_mul_classPrimeSum ha h1, re_charSum_split ha h1]
    have hcancel : unitPrimeSum q σ +
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          χ a⁻¹ * primeSum χ σ).re - unitPrimeSum q σ =
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          χ a⁻¹ * primeSum χ σ).re := by ring
    rw [hcancel]
    exact abs_re_nonprincipal_le a M (fun χ hχ => hM χ hχ σ h1 h2)

/-! ### The density theorem -/

/-- **Dirichlet density, per class (unconditional).**  For `q ≥ 2` and an invertible
residue class `a` mod `q`,

  `(∑_{p ≡ a (q)} p^{-σ}) / (∑_{p ∤ q} p^{-σ}) → 1/φ(q)`  as `σ → 1⁺`.

This is the density strengthening of `prime_reciprocal_class_divergent`: that theorem
says the numerator is unbounded, this one says it carries exactly a `1/φ(q)` share of
the total.  Same three inputs, no new analytic content. -/
theorem tendsto_classPrimeSum_div_unitPrimeSum {q : ℕ} (hq : 2 ≤ q) {a : ZMod q}
    (ha : IsUnit a) :
    Filter.Tendsto (fun σ : ℝ => classPrimeSum a σ / unitPrimeSum q σ)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 / (q.totient : ℝ))) := by
  have : NeZero q := ⟨by omega⟩
  obtain ⟨Mtot, _hMtot0, hMtot⟩ := exists_nonprincipal_bound q
  have hT : (0 : ℝ) < (q.totient : ℝ) := by
    have : 0 < q.totient := Nat.totient_pos.mpr (by omega)
    exact_mod_cast this
  have hU : Filter.Tendsto (unitPrimeSum q) (nhdsWithin 1 (Set.Ioi 1)) Filter.atTop :=
    tendsto_unitPrimeSum_atTop q
  -- the error bound tends to `0`
  have hbound : Filter.Tendsto
      (fun σ : ℝ => Mtot / ((q.totient : ℝ) * unitPrimeSum q σ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds (Filter.Tendsto.const_mul_atTop hT hU)
  -- hence the difference from `1/φ(q)` tends to `0`
  have hdiff : Filter.Tendsto
      (fun σ : ℝ => classPrimeSum a σ / unitPrimeSum q σ - 1 / (q.totient : ℝ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [Ioc_mem_nhdsGT (by norm_num : (1 : ℝ) < 2),
      hU.eventually_gt_atTop 0] with σ hσ hUpos
    have hTU : 0 < (q.totient : ℝ) * unitPrimeSum q σ := mul_pos hT hUpos
    have hkey : classPrimeSum a σ / unitPrimeSum q σ - 1 / (q.totient : ℝ) =
        ((q.totient : ℝ) * classPrimeSum a σ - unitPrimeSum q σ) /
          ((q.totient : ℝ) * unitPrimeSum q σ) := by
      field_simp
    rw [Real.norm_eq_abs, hkey, abs_div, abs_of_pos hTU]
    gcongr
    exact hMtot a ha σ hσ.1 hσ.2
  simpa using hdiff.add_const (1 / (q.totient : ℝ))

/-- **Coherence with Part 8**: the density theorem subsumes the divergence theorem.
Since the ratio tends to the *positive* constant `1/φ(q)` and the denominator tends to
`∞`, the class sum itself tends to `∞` — which is the content extracted, in summability
form, by `prime_reciprocal_class_divergent`. -/
theorem tendsto_classPrimeSum_atTop {q : ℕ} (hq : 2 ≤ q) {a : ZMod q} (ha : IsUnit a) :
    Filter.Tendsto (fun σ : ℝ => classPrimeSum a σ) (nhdsWithin 1 (Set.Ioi 1))
      Filter.atTop := by
  have : NeZero q := ⟨by omega⟩
  have hT : (0 : ℝ) < 1 / (q.totient : ℝ) := by
    have : 0 < q.totient := Nat.totient_pos.mpr (by omega)
    have : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast this
    positivity
  have hU : Filter.Tendsto (unitPrimeSum q) (nhdsWithin 1 (Set.Ioi 1)) Filter.atTop :=
    tendsto_unitPrimeSum_atTop q
  have hmul :=
    Filter.Tendsto.pos_mul_atTop hT (tendsto_classPrimeSum_div_unitPrimeSum hq ha) hU
  refine hmul.congr' ?_
  filter_upwards [hU.eventually_gt_atTop 0] with σ hUpos
  field_simp

/-! ### Unions of classes

The form the applications consume: a set of prime residue classes has Dirichlet density
equal to its share of `(ZMod q)ˣ`.  A condition such as "`minFac (2·q₁⋯q_k + 1) = ℓ`"
unfolds, by CRT, to membership of a fixed `Finset` of unit classes. -/

/-- Summand of the prime sum restricted to a set of residue classes. -/
noncomputable def memTerm (A : Finset (ZMod q)) (σ : ℝ) (p : Nat.Primes) : ℝ :=
  if ((p : ℕ) : ZMod q) ∈ A then (p : ℝ) ^ (-σ) else 0

/-- The prime sum over the classes in `A`: `∑_{p mod q ∈ A} p^{-σ}`. -/
noncomputable def setPrimeSum (A : Finset (ZMod q)) (σ : ℝ) : ℝ :=
  ∑' p : Nat.Primes, memTerm A σ p

lemma memTerm_nonneg (A : Finset (ZMod q)) (σ : ℝ) (p : Nat.Primes) :
    0 ≤ memTerm A σ p := by
  rw [memTerm]; split_ifs
  · positivity
  · exact le_rfl

lemma memTerm_le (A : Finset (ZMod q)) (σ : ℝ) (p : Nat.Primes) :
    memTerm A σ p ≤ (p : ℝ) ^ (-σ) := by
  rw [memTerm]; split_ifs
  · exact le_rfl
  · positivity

lemma summable_memTerm (A : Finset (ZMod q)) {σ : ℝ} (hσ : 1 < σ) :
    Summable (memTerm A σ) :=
  Summable.of_nonneg_of_le (memTerm_nonneg A σ) (memTerm_le A σ) (summable_rpow_neg hσ)

/-- The classes partition the restricted prime sum. -/
lemma setPrimeSum_eq_sum (A : Finset (ZMod q)) {σ : ℝ} (hσ : 1 < σ) :
    setPrimeSum A σ = ∑ a ∈ A, classPrimeSum a σ := by
  have hpt : ∀ p : Nat.Primes, memTerm A σ p = ∑ a ∈ A, classTerm a σ p := by
    intro p
    simp only [memTerm, classTerm]
    exact (Finset.sum_ite_eq A (((p : ℕ) : ZMod q)) (fun _ => (p : ℝ) ^ (-σ))).symm
  rw [setPrimeSum, tsum_congr hpt]
  exact Summable.tsum_finsetSum (fun a _ => summable_classTerm a hσ)

/-- **Dirichlet density of a union of classes (unconditional).**  If every class in `A`
is invertible mod `q`, then

  `(∑_{p mod q ∈ A} p^{-σ}) / (∑_{p ∤ q} p^{-σ}) → |A|/φ(q)`  as `σ → 1⁺`. -/
theorem tendsto_setPrimeSum_div_unitPrimeSum {q : ℕ} (hq : 2 ≤ q) {A : Finset (ZMod q)}
    (hA : ∀ a ∈ A, IsUnit a) :
    Filter.Tendsto (fun σ : ℝ => setPrimeSum A σ / unitPrimeSum q σ)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds ((A.card : ℝ) / (q.totient : ℝ))) := by
  have hsum : Filter.Tendsto
      (fun σ : ℝ => ∑ a ∈ A, classPrimeSum a σ / unitPrimeSum q σ)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (∑ _a ∈ A, 1 / (q.totient : ℝ))) :=
    tendsto_finsetSum _ fun a ha => tendsto_classPrimeSum_div_unitPrimeSum hq (hA a ha)
  have hlim : (∑ _a ∈ A, 1 / (q.totient : ℝ)) = (A.card : ℝ) / (q.totient : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hlim] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [setPrimeSum_eq_sum A hσ, Finset.sum_div]

/-! ## Part 10: The modulus-free normalization

`unitPrimeSum q` omits the primes dividing `q`, so it depends on the modulus and
densities computed at different moduli cannot be compared directly.  Applications need
exactly that comparison (a condition read mod `3` against a class read mod `Q`), so we
record the modulus-free denominator `primeZetaSum σ = ∑_p p^{-σ}` and show it gives the
same densities: the two differ by the finitely many primes dividing `q`, a bounded
amount, against a denominator that blows up. -/

/-- The prime zeta sum `∑_p p^{-σ}`: the modulus-free denominator for Dirichlet density. -/
noncomputable def primeZetaSum (σ : ℝ) : ℝ := ∑' p : Nat.Primes, (p : ℝ) ^ (-σ)

/-- Summand of the prime sum over the primes that are *not* units mod `q` — by
`ZMod.isUnit_prime_iff_not_dvd`, exactly the prime factors of `q`. -/
noncomputable def nonUnitTerm (q : ℕ) (σ : ℝ) (p : Nat.Primes) : ℝ :=
  if IsUnit ((p : ℕ) : ZMod q) then 0 else (p : ℝ) ^ (-σ)

/-- The prime sum over `p ∣ q`. -/
noncomputable def nonUnitPrimeSum (q : ℕ) (σ : ℝ) : ℝ := ∑' p : Nat.Primes, nonUnitTerm q σ p

lemma nonUnitTerm_nonneg (q : ℕ) (σ : ℝ) (p : Nat.Primes) : 0 ≤ nonUnitTerm q σ p := by
  rw [nonUnitTerm]; split_ifs
  · exact le_rfl
  · positivity

lemma nonUnitTerm_le (q : ℕ) (σ : ℝ) (p : Nat.Primes) : nonUnitTerm q σ p ≤ (p : ℝ) ^ (-σ) := by
  rw [nonUnitTerm]; split_ifs
  · positivity
  · exact le_rfl

lemma summable_nonUnitTerm (q : ℕ) {σ : ℝ} (hσ : 1 < σ) : Summable (nonUnitTerm q σ) :=
  Summable.of_nonneg_of_le (nonUnitTerm_nonneg q σ) (nonUnitTerm_le q σ) (summable_rpow_neg hσ)

lemma nonUnitPrimeSum_nonneg (q : ℕ) (σ : ℝ) : 0 ≤ nonUnitPrimeSum q σ :=
  tsum_nonneg fun p => nonUnitTerm_nonneg q σ p

lemma unitTerm_add_nonUnitTerm (q : ℕ) (σ : ℝ) (p : Nat.Primes) :
    unitTerm q σ p + nonUnitTerm q σ p = (p : ℝ) ^ (-σ) := by
  rw [unitTerm, nonUnitTerm]
  split_ifs
  · exact add_zero _
  · exact zero_add _

lemma primeZetaSum_eq_add (q : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    primeZetaSum σ = unitPrimeSum q σ + nonUnitPrimeSum q σ := by
  rw [unitPrimeSum, nonUnitPrimeSum,
    ← Summable.tsum_add (summable_unitTerm q hσ) (summable_nonUnitTerm q hσ), primeZetaSum]
  exact tsum_congr fun p => (unitTerm_add_nonUnitTerm q σ p).symm

/-- The prime factors of `q`, as a `Finset` of `Nat.Primes`. -/
noncomputable def primeFactorsP (q : ℕ) : Finset Nat.Primes :=
  q.primeFactors.attach.image
    (fun p : {x : ℕ // x ∈ q.primeFactors} =>
      (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))

lemma mem_primeFactorsP {q : ℕ} {p : Nat.Primes} (hq : q ≠ 0) (hdvd : (p : ℕ) ∣ q) :
    p ∈ primeFactorsP q := by
  exact Finset.mem_image.mpr ⟨⟨(p : ℕ), Nat.mem_primeFactors.mpr ⟨p.prop, hdvd, hq⟩⟩,
    Finset.mem_attach _ _, Subtype.ext rfl⟩

/-- **The non-unit part is bounded**, uniformly in `σ`: it is supported on the finitely
many prime factors of `q`, each contributing at most `1`. -/
lemma nonUnitPrimeSum_le (q : ℕ) (hq : q ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    nonUnitPrimeSum q σ ≤ ((primeFactorsP q).card : ℝ) := by
  have hz : ∀ p ∉ primeFactorsP q, nonUnitTerm q σ p = 0 := by
    intro p hp
    rw [nonUnitTerm]
    split_ifs with h
    · rfl
    · exfalso
      have hd : (p : ℕ) ∣ q := by
        by_contra hnd
        exact h ((ZMod.isUnit_prime_iff_not_dvd p.prop).mpr hnd)
      exact hp (mem_primeFactorsP hq hd)
  have hle : ∀ p ∈ primeFactorsP q, nonUnitTerm q σ p ≤ 1 := by
    intro p _
    rw [nonUnitTerm]
    split_ifs
    · exact zero_le_one
    · exact Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast p.prop.one_lt.le) (by linarith)
  rw [nonUnitPrimeSum, tsum_eq_sum hz]
  simpa using Finset.sum_le_card_nsmul _ _ 1 hle

/-- The modulus-free denominator also blows up as `σ → 1⁺`. -/
theorem tendsto_primeZetaSum_atTop :
    Filter.Tendsto primeZetaSum (nhdsWithin 1 (Set.Ioi 1)) Filter.atTop := by
  refine Filter.tendsto_atTop_mono' _ ?_ (tendsto_unitPrimeSum_atTop 2)
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [primeZetaSum_eq_add 2 hσ]
  have : 0 ≤ nonUnitPrimeSum 2 σ :=
    tsum_nonneg fun p => nonUnitTerm_nonneg 2 σ p
  linarith

/-- **The two normalizations agree**: `∑_{p ∤ q} p^{-σ}` and `∑_p p^{-σ}` have ratio
tending to `1`, so Dirichlet densities may be computed against either. -/
theorem tendsto_unitPrimeSum_div_primeZetaSum (q : ℕ) (hq : q ≠ 0) :
    Filter.Tendsto (fun σ : ℝ => unitPrimeSum q σ / primeZetaSum σ)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  have hz := tendsto_primeZetaSum_atTop
  have hnu : Filter.Tendsto (fun σ : ℝ => nonUnitPrimeSum q σ / primeZetaSum σ)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    refine squeeze_zero_norm' ?_
      (Filter.Tendsto.div_atTop (f := fun _ : ℝ => ((primeFactorsP q).card : ℝ))
        tendsto_const_nhds hz)
    filter_upwards [self_mem_nhdsWithin, hz.eventually_gt_atTop 0] with σ hσ hzpos
    rw [Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (nonUnitPrimeSum_nonneg q σ) hzpos.le)]
    gcongr
    exact nonUnitPrimeSum_le q hq hσ
  have hsub : Filter.Tendsto (fun σ : ℝ => 1 - nonUnitPrimeSum q σ / primeZetaSum σ)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by simpa using hnu.const_sub 1
  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hz.eventually_gt_atTop 0] with σ hσ hzpos
  rw [primeZetaSum_eq_add q hσ] at hzpos ⊢
  have hne : unitPrimeSum q σ + nonUnitPrimeSum q σ ≠ 0 := hzpos.ne'
  field_simp
  ring

/-- **Dirichlet density against the modulus-free denominator.** -/
theorem tendsto_classPrimeSum_div_primeZetaSum {q : ℕ} (hq : 2 ≤ q) {a : ZMod q}
    (ha : IsUnit a) :
    Filter.Tendsto (fun σ : ℝ => classPrimeSum a σ / primeZetaSum σ)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 / (q.totient : ℝ))) := by
  have : NeZero q := ⟨by omega⟩
  have hmul : Filter.Tendsto (fun σ : ℝ =>
      classPrimeSum a σ / unitPrimeSum q σ * (unitPrimeSum q σ / primeZetaSum σ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 / (q.totient : ℝ))) := by
    simpa using (tendsto_classPrimeSum_div_unitPrimeSum hq ha).mul
      (tendsto_unitPrimeSum_div_primeZetaSum q (by omega))
  refine hmul.congr' ?_
  filter_upwards [(tendsto_unitPrimeSum_atTop q).eventually_gt_atTop 0,
    tendsto_primeZetaSum_atTop.eventually_gt_atTop 0] with σ hUpos hzpos
  field_simp

/-- **Dirichlet density of a union of classes, modulus-free denominator.**  This is the
form the applications consume. -/
theorem tendsto_setPrimeSum_div_primeZetaSum {q : ℕ} (hq : 2 ≤ q) {A : Finset (ZMod q)}
    (hA : ∀ a ∈ A, IsUnit a) :
    Filter.Tendsto (fun σ : ℝ => setPrimeSum A σ / primeZetaSum σ)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds ((A.card : ℝ) / (q.totient : ℝ))) := by
  have : NeZero q := ⟨by omega⟩
  have hmul : Filter.Tendsto (fun σ : ℝ =>
      setPrimeSum A σ / unitPrimeSum q σ * (unitPrimeSum q σ / primeZetaSum σ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds ((A.card : ℝ) / (q.totient : ℝ))) := by
    simpa using (tendsto_setPrimeSum_div_unitPrimeSum hq hA).mul
      (tendsto_unitPrimeSum_div_primeZetaSum q (by omega))
  refine hmul.congr' ?_
  filter_upwards [(tendsto_unitPrimeSum_atTop q).eventually_gt_atTop 0,
    tendsto_primeZetaSum_atTop.eventually_gt_atTop 0] with σ hUpos hzpos
  field_simp

end DirichletDensity
end IK
