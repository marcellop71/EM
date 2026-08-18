import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.ZMod.QuotientRing

/-!
# The ambient profinite ensemble: a probability space of seeds

This file builds the sample space on which the population statements of the
seed-average programme can be phrased *measure-theoretically* rather than as
counting statements about finite windows.  It is **packaging only**: every
theorem below is a repackaging of a finite counting fact, and no new
mathematics is introduced.  That is deliberate — the packaging carries no
analytic risk precisely because it proves nothing new.

## The space

```
Ω := Π (r : Nat.Primes), ZMod r
```

with the product of the uniform measures, `μ := Measure.infinitePi localUniform`
(Mathlib's `MeasureTheory.Measure.infinitePi`, which needs only that each factor
is a probability measure — no Polish/standard-Borel hypothesis, and no bespoke
Carathéodory extension here).

**Why `Π ZMod r` and not `Ẑ = Π ℤ_p`.**  The programme only ever conditions a
seed on `m mod M` with `M` **squarefree**: the modulus of the selection law is
`SelectionLaw.modulus q Y = ∏ r ∈ bandUpTo q Y, r`, a product of *distinct*
band primes.  A single `ZMod r` per prime therefore records everything any
statement in the programme can see; the extra `r`-adic depth of `ℤ_r` is dead
weight.  Including *every* prime as a coordinate — the prime `q` under study
included — is exactly what makes the `q`-coordinate a free, independent
coordinate, which is the CRT freedom that
`EM/Population/SelectionLaw.lean` exploits by *excluding* `q` from its modulus.

## Scope caveats — as important as the mathematics

* **`ℕ` is `μ`-null.**  The embedding `iota : ℕ → Ω` (coordinatewise reduction)
  has countable range, and `μ` gives every singleton measure `0`; so the image
  of `ℕ` in `Ω` is a `μ`-null set.  Consequently **"`μ`-a.e. seed" is not
  "almost all integer seeds"**: a `μ`-null set can have upper natural density
  `1` in `ℕ`, and a `μ`-full set can meet `ℕ` in a set of density `0`.  Any
  transfer between the two must go through the *finite* residue-class
  statements (`measure_residue_classes` together with a genuine equidistribution
  input), never through "a.e." alone.
* **This is a statement about a random model.**  It says **nothing** about the
  orbit of the seed `2`, i.e. nothing about Mullin's conjecture proper.  The
  orbit-specificity obstructions (dead ends #90 and #117) are untouched, and
  nothing here should be read as progress against them.
* **Not dead end #101, not #155.**  #101 is the (dead) proposal to house *the
  Euler–Mullin walk* in `Ẑ`; #155 is a Loeb-measure receptacle.  Here the
  profinite object is the *sample space of a population statement* and carries
  no walk and no orbit claim.

## Main results

* `localUniform_apply_finset` — the local uniform measure of a finset `S` of
  residues mod `r` is `#S / r`.
* `measure_cylinder` — **equality**: an event depending only on the coordinates
  in a finite set `P` of primes has measure `#B / ∏_{r ∈ P} r`, where `B` is the
  set of good tuples.
* `measure_residue_classes` — **equality**: for `M = ∏_{r ∈ P} r` (squarefree)
  and `T : Finset (ZMod M)`, the `M`-periodic event `redMod P x ∈ T` has measure
  `#T / M`.  This is the lemma the rest of the programme consumes: *the measure
  of an `M`-periodic event is its period fraction*.
* `redMod_iota` — compatibility: the CRT reduction of an embedded integer is its
  residue mod `M`.
-/

noncomputable section

open MeasureTheory Finset
open scoped ENNReal

namespace ProfiniteEnsemble

/-! ### The space and the measure -/

/-- Each prime, viewed as a natural number, is nonzero; needed for `ZMod r` to be a
nonempty `Fintype`. -/
instance instNeZeroPrimeVal (r : Nat.Primes) : NeZero ((r : ℕ)) := ⟨r.2.ne_zero⟩

/-- The ambient sample space: one `ZMod r` coordinate for **every** prime `r`. -/
abbrev Ω : Type := ∀ r : Nat.Primes, ZMod ((r : ℕ))

/-- The uniform probability measure on the residues mod `r`. -/
def localUniform (r : Nat.Primes) : Measure (ZMod ((r : ℕ))) :=
  (PMF.uniformOfFintype (ZMod ((r : ℕ)))).toMeasure

instance instIsProbabilityMeasureLocalUniform (r : Nat.Primes) :
    IsProbabilityMeasure (localUniform r) :=
  PMF.toMeasure.isProbabilityMeasure _

/-- The ambient measure: the product of the local uniform measures.  Built with
Mathlib's `Measure.infinitePi`, which requires only that every factor is a
probability measure. -/
def μ : Measure Ω := Measure.infinitePi localUniform

instance instIsProbabilityMeasureMu : IsProbabilityMeasure μ := by
  unfold μ; infer_instance

/-! ### The local uniform measure of a finset of residues -/

/-- The uniform measure of a finset `S` of residues mod `r` is `#S / r`. -/
theorem localUniform_apply_finset (r : Nat.Primes) (S : Finset (ZMod ((r : ℕ)))) :
    localUniform r (↑S : Set (ZMod ((r : ℕ)))) = (S.card : ℝ≥0∞) / ((r : ℕ) : ℝ≥0∞) := by
  rw [localUniform, PMF.toMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, ZMod.card, Finset.sum_const, nsmul_eq_mul]
  rw [div_eq_mul_inv]

/-- The uniform measure of a singleton residue class is `1 / r`. -/
theorem localUniform_apply_singleton (r : Nat.Primes) (b : ZMod ((r : ℕ))) :
    localUniform r {b} = ((r : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [localUniform, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b),
    PMF.uniformOfFintype_apply, ZMod.card]

/-! ### The cylinder-count lemma -/

/-- The modulus attached to a finite set of primes: `∏_{r ∈ P} r`.  It is
squarefree by construction (a product of *distinct* primes). -/
def emModulus (P : Finset Nat.Primes) : ℕ := ∏ r ∈ P, ((r : ℕ))

theorem emModulus_eq_prod_attach (P : Finset Nat.Primes) :
    emModulus P = ∏ i : P, ((i : Nat.Primes) : ℕ) := by
  rw [emModulus, ← Finset.prod_attach P (fun r : Nat.Primes => ((r : ℕ)))]
  rfl

theorem emModulus_pos (P : Finset Nat.Primes) : 0 < emModulus P :=
  Finset.prod_pos fun r _ => r.2.pos

private theorem prod_local_inv (P : Finset Nat.Primes) :
    ∏ i : P, (((i : Nat.Primes) : ℕ) : ℝ≥0∞)⁻¹ = ((emModulus P : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [emModulus_eq_prod_attach]
  rw [Nat.cast_prod]
  rw [ENNReal.prod_inv_distrib]
  intro i _ j _ _
  right
  exact ENNReal.natCast_ne_top _

/-- The measure of a finite-dimensional cylinder: an event that depends only on the
coordinates at the primes in `P` has measure `#B / ∏_{r ∈ P} r`, where `B` is the
finset of admissible tuples.  This is an **equality**. -/
theorem measure_cylinder (P : Finset Nat.Primes)
    (B : Finset (∀ r : P, ZMod ((r : Nat.Primes) : ℕ))) :
    μ {x : Ω | P.restrict x ∈ B} = (B.card : ℝ≥0∞) / ((emModulus P : ℕ) : ℝ≥0∞) := by
  classical
  have hset : {x : Ω | P.restrict x ∈ B}
      = (P.restrict : Ω → ∀ r : P, ZMod ((r : Nat.Primes) : ℕ)) ⁻¹' (↑B) := rfl
  have hmB : MeasurableSet (↑B : Set (∀ r : P, ZMod ((r : Nat.Primes) : ℕ))) :=
    B.measurableSet
  rw [hset, ← Measure.map_apply (Finset.measurable_restrict P) hmB, μ,
    Measure.infinitePi_map_restrict]
  -- Value on singletons.
  have hsingle : ∀ b : (∀ r : P, ZMod ((r : Nat.Primes) : ℕ)),
      Measure.pi (fun i : P => localUniform (i : Nat.Primes)) {b}
        = ((emModulus P : ℕ) : ℝ≥0∞)⁻¹ := by
    intro b
    rw [← Set.univ_pi_singleton b, Measure.pi_pi]
    simp only [localUniform_apply_singleton]
    exact prod_local_inv P
  -- Decompose `B` into its singletons.
  have hunion : (↑B : Set (∀ r : P, ZMod ((r : Nat.Primes) : ℕ))) = ⋃ b ∈ B, ({b} : Set _) :=
    (Set.biUnion_of_singleton (↑B : Set (∀ r : P, ZMod ((r : Nat.Primes) : ℕ)))).symm
  rw [hunion, measure_biUnion_finset]
  · simp only [hsingle, Finset.sum_const, nsmul_eq_mul]
    rw [div_eq_mul_inv]
  · intro a _ b _ hab
    simpa using hab
  · intro b _
    exact measurableSet_singleton b

/-! ### The CRT bridge -/

private theorem primes_pairwise_coprime (P : Finset Nat.Primes) :
    Pairwise (Function.onFun Nat.Coprime (fun i : P => ((i : Nat.Primes) : ℕ))) := by
  intro i j hij
  have hne : ((i : Nat.Primes) : ℕ) ≠ ((j : Nat.Primes) : ℕ) := by
    intro h
    exact hij (Subtype.ext (Subtype.ext h))
  exact (Nat.coprime_primes (i : Nat.Primes).2 (j : Nat.Primes).2).2 hne

/-- The Chinese remainder isomorphism `ZMod (∏_{r ∈ P} r) ≃+* Π_{r ∈ P} ZMod r`,
available because the primes in `P` are distinct, hence pairwise coprime. -/
def crtEquiv (P : Finset Nat.Primes) :
    ZMod (emModulus P) ≃+* (∀ i : P, ZMod ((i : Nat.Primes) : ℕ)) :=
  (ZMod.ringEquivCongr (emModulus_eq_prod_attach P)).trans
    (ZMod.prodEquivPi (fun i : P => ((i : Nat.Primes) : ℕ)) (primes_pairwise_coprime P))

/-- Reduction of a profinite seed modulo `M = ∏_{r ∈ P} r`, via CRT. -/
def redMod (P : Finset Nat.Primes) (x : Ω) : ZMod (emModulus P) :=
  (crtEquiv P).symm (P.restrict x)

/-- The coordinatewise reduction map embedding the integers into the profinite space. -/
def iota (m : ℕ) : Ω := fun r => (m : ZMod ((r : ℕ)))

/-- Compatibility: the CRT reduction of an embedded integer is its residue mod `M`. -/
theorem redMod_iota (P : Finset Nat.Primes) (m : ℕ) :
    redMod P (iota m) = (m : ZMod (emModulus P)) := by
  rw [redMod, RingEquiv.symm_apply_eq]
  have h : (crtEquiv P) (m : ZMod (emModulus P))
      = ((m : ℕ) : ∀ i : P, ZMod ((i : Nat.Primes) : ℕ)) := map_natCast _ m
  rw [h]
  funext i
  simp [iota, Finset.restrict]

/-- **The residue-class measure lemma.**  For `M = ∏_{r ∈ P} r` squarefree and any
finset `T` of residues mod `M`, the `M`-periodic event `{x | redMod P x ∈ T}` has
measure exactly `#T / M`.  This is an **equality**. -/
theorem measure_residue_classes (P : Finset Nat.Primes)
    (T : Finset (ZMod (emModulus P))) :
    μ {x : Ω | redMod P x ∈ T} = (T.card : ℝ≥0∞) / ((emModulus P : ℕ) : ℝ≥0∞) := by
  classical
  have hset : {x : Ω | redMod P x ∈ T}
      = {x : Ω | P.restrict x ∈ T.map (crtEquiv P).toEquiv.toEmbedding} := by
    ext x
    simp only [Set.mem_ofPred_eq, redMod, Finset.mem_map_equiv]
    rfl
  rw [hset, measure_cylinder, Finset.card_map]

/-- The whole space has measure one (sanity check, and the `IsProbabilityMeasure`
instance in usable form). -/
theorem measure_univ_eq_one : μ (Set.univ : Set Ω) = 1 := measure_univ

/-! ### The scope caveat, proved: the integers are a null set

The docstring's warning is not rhetorical.  We prove here that `μ` has no atoms
and that the image of `ℕ` under `iota` is `μ`-null.  Hence **`μ`-almost every
seed** is a statement about a random model that, taken alone, says *nothing*
about any particular integer seed, and in particular nothing about the orbit of
`2`.  Transfer to the integers must go through `measure_residue_classes` plus a
genuine equidistribution input, never through "a.e." alone. -/

/-- A single point of `Ω` is contained in the one-coordinate cylinder over any prime
`r`, so its measure is at most `1 / r`. -/
theorem measure_singleton_le (r : Nat.Primes) (x : Ω) :
    μ ({x} : Set Ω) ≤ ((r : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  set P : Finset Nat.Primes := {r} with hP
  have hsub : ({x} : Set Ω)
      ⊆ {y : Ω | P.restrict y ∈ ({P.restrict x} : Finset (∀ i : P, ZMod ((i : Nat.Primes) : ℕ)))} := by
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    simp
  refine (measure_mono hsub).trans_eq ?_
  rw [measure_cylinder]
  have hM : emModulus P = ((r : ℕ)) := by
    rw [emModulus, hP, Finset.prod_singleton]
  rw [hM, Finset.card_singleton, Nat.cast_one, one_div]

/-- `μ` has no atoms: every singleton is null.  (Take primes `r → ∞` in
`measure_singleton_le`.) -/
theorem measure_singleton_eq_zero (x : Ω) : μ ({x} : Set Ω) = 0 := by
  by_contra h
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt h
  obtain ⟨p, hpn, hp⟩ := Nat.exists_infinite_primes n
  have hle : μ ({x} : Set Ω) ≤ ((p : ℕ) : ℝ≥0∞)⁻¹ :=
    measure_singleton_le ⟨p, hp⟩ x
  have hmono : ((p : ℕ) : ℝ≥0∞)⁻¹ ≤ ((n : ℕ) : ℝ≥0∞)⁻¹ :=
    ENNReal.inv_le_inv.2 (Nat.cast_le.2 hpn)
  exact absurd (hle.trans hmono) (not_le.2 hn)

/-- **The integers are `μ`-null.**  `iota '' ℕ` is countable and `μ` has no atoms,
so the whole of `ℕ`, embedded in `Ω`, is invisible to `μ`.  This is why
"`μ`-a.e. seed" is *not* "almost all integer seeds": a `μ`-null set may have
upper natural density `1` in `ℕ`. -/
theorem measure_range_iota_eq_zero : μ (Set.range iota) = 0 := by
  rw [← Set.iUnion_singleton_eq_range]
  exact measure_iUnion_null fun m => measure_singleton_eq_zero (iota m)

end ProfiniteEnsemble
