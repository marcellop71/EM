import EM.LargeSieveSpectral
import EM.MullinCRT

/-!
# CME Decomposition: Structural Decorrelation and EM-Dirichlet

This file decomposes CME (Conditional Multiplier Equidistribution) into:

- **Part A (Structural Decorrelation — PROVED)**: the minFac operation is
  q-blind (`crt_multiplier_invariance` in MullinCRT.lean).
- **Part B (EM-Dirichlet — OPEN)**: EM primes are equidistributed in residue
  classes, identical to `DecorrelationHypothesis`.

The direction CME → EM-Dirichlet is proved (`cme_implies_dec`). The reverse
direction EM-Dirichlet → CME is an open hypothesis (`EMDImpliesCME`):
structural/functional independence (minFac doesn't use P(n) mod q) does NOT
automatically imply statistical independence of counting densities for a
deterministic sequence.

If `EMDImpliesCME` held, we'd get `Dec → CME → CCSB → MC` with zero
open bridges (currently `decorrelation_mc'` needs the open `PEDImpliesComplexCSB`).

## Main Results

* `EMDirichlet`                            : alias for `DecorrelationHypothesis`
* `emd_eq_dec`                             : `EMDirichlet = DecorrelationHypothesis` (rfl)
* `emd_implies_ped`                        : EMD → PED (PROVED)
* `structural_decorrelation_statement`     : restatement of `crt_multiplier_invariance`
* `EMDImpliesCME`                          : open hypothesis (EMD → CME)
* `cme_implies_emd`                        : CME → EMD (PROVED)
* `emd_cme_implies_mc`                     : EMDImpliesCME → EMD → MC (PROVED)
* `emd_cme_implies_ccsb`                   : EMDImpliesCME → EMD → CCSB (PROVED)
* `deathSet`                               : union of coordinate hyperplanes in a product
* `surjective_subgroup_coset_meets_target` : surjective subgroup coset hits target
* `surjective_subgroup_coset_meets_death`  : surjective subgroup coset meets death set
-/

open Mullin Euclid MullinGroup RotorRouter

open scoped BigOperators

/-! ## S90. EM-Dirichlet Alias and Structural Decorrelation -/

/-- **EM-Dirichlet**: EM primes are equidistributed in residue classes mod q.
    In character sum form: ∑ χ(em(n) mod q) = o(N) for nontrivial χ.

    Identical to `DecorrelationHypothesis` (EquidistSelfCorrecting.lean).
    The name emphasizes the analogy with Dirichlet's theorem on primes in
    arithmetic progressions: EM-Dirichlet asks whether the specific
    subsequence of primes selected by the EM mechanism inherits the
    equidistribution that the full set of primes enjoys. -/
def EMDirichlet : Prop := DecorrelationHypothesis

/-- `EMDirichlet` is definitionally equal to `DecorrelationHypothesis`. -/
theorem emd_eq_dec : EMDirichlet = DecorrelationHypothesis := rfl

/-- EM-Dirichlet implies PositiveEscapeDensity, via `decorrelation_implies_ped`. -/
theorem emd_implies_ped (h : EMDirichlet) : PositiveEscapeDensity :=
  decorrelation_implies_ped h

/-- **Structural Decorrelation (Part A — PROVED).**

    For prime q, if P and P' agree modulo every prime r ≠ q, q divides
    neither P+1 nor P'+1, and both P+1 ≥ 2, then
    `Nat.minFac(P+1) = Nat.minFac(P'+1)`.

    This means the minFac operation is **q-blind**: it does not depend on
    the walk position P mod q. The multiplier em(n+1) mod q is determined
    entirely by {P(n) mod r : r prime, r ≠ q}.

    This is a direct restatement of `MullinCRT.crt_multiplier_invariance`. -/
theorem structural_decorrelation_statement
    {P P' q : Nat}
    (hP : 2 ≤ P + 1) (hP' : 2 ≤ P' + 1)
    (hq_prime : Nat.Prime q)
    (hcrt : ∀ r, Nat.Prime r → r ≠ q → P % r = P' % r)
    (hq_ndvd : ¬ (q ∣ P + 1))
    (hq_ndvd' : ¬ (q ∣ P' + 1)) :
    Nat.minFac (P + 1) = Nat.minFac (P' + 1) :=
  MullinCRT.crt_multiplier_invariance hP hP' hq_prime hcrt hq_ndvd hq_ndvd'

/-! ## S91. CME Decomposition -/

/-- **EMDImpliesCME**: the open hypothesis that unconditional multiplier
    equidistribution (EM-Dirichlet) implies conditional multiplier
    equidistribution (CME).

    **Why this is plausible:** Structural decorrelation
    (`crt_multiplier_invariance`) shows the minFac mechanism is q-blind:
    em(n+1) mod q does not depend on P(n) mod q. This makes EMDImpliesCME
    the natural expectation.

    **Why this is NOT proved:** Functional independence of the mechanism
    does not imply statistical independence of the trajectory. The step
    from "the function doesn't use q-residues" to "counting densities in
    q-fibers match unconditional densities" requires dynamical input
    (e.g., weak mixing in CRT space). Trajectory correlations in CRT
    space can break conditional = unconditional even when the mechanism
    is q-blind.

    **Value:** If proved, gives `Dec → CME → CCSB → MC` with zero open
    bridges, avoiding the open `PEDImpliesComplexCSB`. -/
def EMDImpliesCME : Prop := EMDirichlet → ConditionalMultiplierEquidist

/-- CME implies EM-Dirichlet. Unfolds `EMDirichlet` and applies `cme_implies_dec`. -/
theorem cme_implies_emd (hcme : ConditionalMultiplierEquidist) : EMDirichlet :=
  cme_implies_dec hcme

/-- **EMDImpliesCME + EMDirichlet → MC**: if the open bridge holds, then
    EM-Dirichlet alone implies Mullin's Conjecture, via the proved chain
    CME → CCSB → MC.

    Compare with `decorrelation_mc'` which needs the open `PEDImpliesComplexCSB`.
    Both routes from Dec to MC need one open hypothesis beyond Dec itself:
    - This route: `EMDImpliesCME` (structural → statistical independence)
    - The other: `PEDImpliesComplexCSB` (block-rotation cancellation) -/
theorem emd_cme_implies_mc (h : EMDImpliesCME) (hemd : EMDirichlet) :
    MullinConjecture :=
  cme_implies_mc (h hemd)

/-- EMDImpliesCME + EMDirichlet → CCSB: the intermediate stop before MC. -/
theorem emd_cme_implies_ccsb (h : EMDImpliesCME) (hemd : EMDirichlet) :
    ComplexCharSumBound :=
  cme_implies_ccsb (h hemd)

/-! ## S92. Surjection Lemma

Standalone algebraic result: in a product of groups, if a subgroup surjects
onto each factor, every coset meets the "death set" (union of hyperplanes
where at least one coordinate equals its target value).

This constrains the walk's reachable set in the product group: avoidance
of all death values simultaneously is not an algebraic necessity, only a
dynamical possibility. -/

/-- The **death set** in a product group: the set of elements g : ∀ i, C i
    such that at least one coordinate equals its target value.

    An element g is in `deathSet f` iff ∃ i, g i = f i. For the EM walk
    in ∏ (ZMod qᵢ)ˣ, the target f i = -1 (the walk position where q
    divides P(n)+1). -/
def deathSet {ι : Type*} {C : ι → Type*} (f : ∀ i, C i) : Set (∀ i, C i) :=
  {g | ∃ i, g i = f i}

/-- **Surjective subgroup hits target in any coordinate of any coset.**

    If Λ ≤ ∏ Cᵢ is a subgroup and the projection πᵢ(Λ) = Cᵢ (surjection
    onto factor i), then for any g : ∏ Cᵢ, the coset g * Λ contains an
    element whose i-th coordinate equals f i.

    Proof: πᵢ surjects, so ∃ λ ∈ Λ with λ i = g⁻¹ i * f i.
    Then (g * λ) i = g i * λ i = g i * (g⁻¹ i * f i) = f i. -/
theorem surjective_subgroup_coset_meets_target
    {ι : Type*} {C : ι → Type*} [∀ i, Group (C i)]
    (Λ : Subgroup (∀ i, C i))
    (f : ∀ i, C i) (g : ∀ i, C i)
    (i : ι)
    (hsurj : Function.Surjective (fun (l : Λ) => (l : ∀ i, C i) i)) :
    ∃ l : Λ, (g * (l : ∀ i, C i)) i = f i := by
  -- Need l with (g * l) i = f i, i.e., l i = g⁻¹ i * f i
  obtain ⟨⟨l, hl⟩, hproj⟩ := hsurj (g⁻¹ i * f i)
  refine ⟨⟨l, hl⟩, ?_⟩
  show (g * l) i = f i
  simp only [Pi.mul_apply, Pi.inv_apply] at hproj ⊢
  rw [hproj, ← mul_assoc, mul_inv_cancel, one_mul]

/-- **Every coset of a surjective subgroup meets the death set.**

    If Λ ≤ ∏ Cᵢ surjects onto each factor (via projections), then for
    any g, the coset g · Λ meets `deathSet f`.

    Proof: pick any index i, apply `surjective_subgroup_coset_meets_target`. -/
theorem surjective_subgroup_coset_meets_death
    {ι : Type*} [Inhabited ι] {C : ι → Type*} [∀ i, Group (C i)]
    (Λ : Subgroup (∀ i, C i))
    (f : ∀ i, C i) (g : ∀ i, C i)
    (hsurj : ∀ i, Function.Surjective (fun (l : Λ) => (l : ∀ i, C i) i)) :
    ∃ l : Λ, (g * (l : ∀ i, C i)) ∈ deathSet f := by
  obtain ⟨l, hl⟩ := surjective_subgroup_coset_meets_target Λ f g default (hsurj default)
  exact ⟨l, default, hl⟩

/-- **Algebraic non-necessity of simultaneous avoidance.**

    For the EM walk in ∏ (ZMod qᵢ)ˣ with death targets f i = -1:
    if the multiplier subgroup surjects onto each factor, then every
    coset meets the death set. In particular, permanent avoidance of
    all death values simultaneously is not forced by the group structure
    — it can only be a dynamical property of the specific trajectory.

    This instantiates the surjection lemma with `C i = (ZMod (q i))ˣ`
    and `f i = -1`. -/
theorem walk_reachable_meets_death_algebraic
    {ι : Type*} [Inhabited ι] (q : ι → ℕ)
    [∀ i, Fact (Nat.Prime (q i))] [∀ i, NeZero (q i)]
    (Λ : Subgroup (∀ i, (ZMod (q i))ˣ))
    (g : ∀ i, (ZMod (q i))ˣ)
    (hsurj : ∀ i, Function.Surjective (fun (l : Λ) => (l : ∀ i, (ZMod (q i))ˣ) i)) :
    ∃ l : Λ, (g * (l : ∀ i, (ZMod (q i))ˣ)) ∈ deathSet (fun _ => -1) :=
  surjective_subgroup_coset_meets_death Λ (fun _ => -1) g hsurj
