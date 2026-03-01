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
* `visit_count_sum_eq`                     : ∑_a V(a,N) = N (partition identity, PROVED)
* `emd_vcb_implies_cme`                    : EMD + VCB → CME (PROVED)
* `emd_vcb_implies_mc`                     : EMD + VCB → MC (PROVED)
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

    **Factoring (PROVED, see `emd_vcb_implies_cme` below):**
    EMDImpliesCME factors as EMD + VCB → CME, where VCB = Vanishing
    Conditional Bias (fiber sums proportional to visit counts). The
    genuine gap is thus: "does EMD alone imply VCB?" Since VCB is
    equivalent to CME for fixed q (Dead End #93), this gap is inherent.

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

/-! ## S91b. EMD + VCB → CME: Factoring EMDImpliesCME

The open hypothesis `EMDImpliesCME` can be **factored** through VCB:
  EMD + VCB → CME.

The argument: VCB says F(a,N) ≈ μ(N)·V(a,N) for a common μ(N).
Summing over fibers: S(N) ≈ μ(N)·N (since ∑_a V(a,N) = N).
EMD gives ‖S(N)‖ = o(N), so |μ(N)| = o(1).
Then ‖F(a,N)‖ ≤ |μ(N)|·V(a,N) + o(N) = o(1)·N + o(N) = o(N), which is CME.

This shows EMDImpliesCME splits as (EMD → VCB) + (VCB itself). Since
VCB is strictly between CME and Dec in the hierarchy, this clarifies
exactly where the gap lies: the open content is "VCB from EMD alone."

### Key Results
* `visit_count_sum_eq`    — ∑_a V(a,N) = N (partition identity)
* `emd_vcb_implies_cme`   — EMD + VCB → CME (PROVED)
* `emd_vcb_implies_mc`    — EMD + VCB → MC (PROVED)
-/

open Classical in
/-- **Visit count partition identity**: the total number of steps equals the
    sum of visit counts over all walk positions. Every index n < N falls
    into exactly one fiber {n : w(n) = a}, so
    ∑_a |{n < N : w(n) = a}| = N. -/
theorem visit_count_sum_eq (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (N : Nat) :
    ∑ a : (ZMod q)ˣ,
      ((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card = N := by
  have := Finset.card_eq_sum_card_fiberwise (s := Finset.range N) (t := Finset.univ)
    (f := emWalkUnit q hq hne) (fun _ _ => Finset.mem_univ _)
  simp only [Finset.card_range] at this
  exact this.symm

open Classical in
/-- **EMD + VCB → CME**: unconditional multiplier equidistribution combined
    with vanishing conditional bias implies conditional multiplier
    equidistribution.

    **Proof**: fix q, χ ≠ 1, a, ε > 0. Apply VCB with tolerance ε' = ε/(2(C+1))
    to get μ(N) with ‖F(a,N) - μ·V(a,N)‖ ≤ ε'·N. Summing over all C = φ(q)
    fibers and using ∑_a V(a,N) = N gives ‖S(N) - μ·N‖ ≤ C·ε'·N. EMD gives
    ‖S(N)‖ ≤ δ·N with δ = ε/2, so ‖μ‖ ≤ δ + C·ε'. Then
    ‖F(a,N)‖ ≤ ε'·N + (δ + C·ε')·N = (ε' + δ + C·ε')·N = ε·N.

    **Value**: factors `EMDImpliesCME` into two pieces: the gap between EMD
    and CME is precisely VCB. Since VCB is implied by CME (`cme_implies_vcb`)
    and implies MC with PED (`vcb_ped_implies_mc`), this pinpoints the
    EMD-CME gap as "does EMD alone imply the proportionality F(a) ∝ V(a)?" -/
theorem emd_vcb_implies_cme (hemd : EMDirichlet) (hvcb : VanishingConditionalBias) :
    ConditionalMultiplierEquidist := by
  intro q inst hq hne χ hχ a ε hε
  haveI : Fact (Nat.Prime q) := inst
  -- C = number of walk positions = φ(q)
  set C := Fintype.card (ZMod q)ˣ with hC_def
  have hC_pos : (0 : ℝ) < C := by
    exact Nat.cast_pos.mpr Fintype.card_pos
  -- Set tolerances: ε' for VCB, δ for EMD
  -- Need: ε' + δ + C·ε' = ε, i.e., (C+1)·ε' + δ = ε
  -- Choose δ = ε/2, ε' = ε/(2·(C+1))
  set δ := ε / 2 with hδ_def
  have hδ_pos : 0 < δ := div_pos hε two_pos
  have hC1_pos : (0 : ℝ) < C + 1 := by linarith
  set ε' := ε / (2 * (C + 1)) with hε'_def
  have hε'_pos : 0 < ε' := div_pos hε (mul_pos two_pos hC1_pos)
  -- Apply VCB with tolerance ε'
  obtain ⟨N₀_vcb, hN₀_vcb⟩ := hvcb q hq hne χ hχ ε' hε'_pos
  -- Apply EMD with tolerance δ
  obtain ⟨N₀_emd, hN₀_emd⟩ := hemd q hq hne χ hχ δ hδ_pos
  -- Take N₀ = max(N₀_vcb, N₀_emd, 1) to ensure N > 0
  set N₀ := max (max N₀_vcb N₀_emd) 1
  refine ⟨N₀, fun N hN => ?_⟩
  -- N ≥ 1, so N > 0
  have hN_pos : (0 : ℝ) < N := by
    have : 1 ≤ N := le_trans (le_max_right _ _) hN
    exact Nat.cast_pos.mpr (by omega)
  have hN_vcb : N ≥ N₀_vcb := le_trans (le_max_left _ _ |>.trans (le_max_left _ _)) hN
  have hN_emd : N ≥ N₀_emd := le_trans (le_max_right _ _ |>.trans (le_max_left _ _)) hN
  -- VCB gives μ(N) such that ‖F(a,N) - μ·V(a,N)‖ ≤ ε'·N for all a
  obtain ⟨μ, hμ⟩ := hN₀_vcb N hN_vcb
  -- EMD gives ‖S(N)‖ ≤ δ·N
  have hemd_bound := hN₀_emd N hN_emd
  -- Visit count partition: ∑_a V(a,N) = N
  have hV_sum : (∑ a' : (ZMod q)ˣ,
      (((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a')).card : ℝ)) = N := by
    have := visit_count_sum_eq q hq hne N
    exact_mod_cast this
  -- S(N) = ∑_a F(a,N) by fiber decomposition
  have hS_decomp : ∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ) =
      ∑ a' : (ZMod q)ˣ, fiberMultCharSum q hq hne χ a' N :=
    mult_char_sum_eq_fiber_sum q hq hne χ N
  -- Step 1: Bound ‖S(N) - μ·N‖
  -- S(N) - μ·N = ∑_a (F(a) - μ·V(a)) because ∑_a μ·V(a) = μ·N
  have hSN_minus_muN :
      ‖∑ a' : (ZMod q)ˣ, fiberMultCharSum q hq hne χ a' N -
        μ * N‖ ≤ C * (ε' * N) := by
    -- Rewrite μ·N as μ·∑_a V(a)
    have hV_C : (N : ℂ) = ∑ a' : (ZMod q)ˣ,
        (((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a')).card : ℂ) := by
      have := visit_count_sum_eq q hq hne N
      exact_mod_cast this.symm
    have key : ∑ a' : (ZMod q)ˣ, fiberMultCharSum q hq hne χ a' N - μ * N =
        ∑ a' : (ZMod q)ˣ, (fiberMultCharSum q hq hne χ a' N -
          μ * ((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a')).card) := by
      rw [hV_C, Finset.mul_sum]
      simp only [Finset.sum_sub_distrib]
    rw [key]
    calc ‖∑ a' : (ZMod q)ˣ, (fiberMultCharSum q hq hne χ a' N -
            μ * ((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a')).card)‖
        ≤ ∑ a' : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a' N -
            μ * ((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a')).card‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _a' : (ZMod q)ˣ, ε' * N := by
          apply Finset.sum_le_sum; intro a' _; exact hμ a'
      _ = C * (ε' * N) := by
          rw [Finset.sum_const, nsmul_eq_mul, hC_def, Finset.card_univ]
  -- Step 2: Bound ‖μ‖
  -- ‖μ·N‖ ≤ ‖S(N)‖ + ‖S(N) - μ·N‖ ≤ δ·N + C·ε'·N
  have hmu_bound : ‖μ‖ * N ≤ (δ + C * ε') * N := by
    have h1 : ‖μ * N‖ ≤ ‖∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ)‖ +
        ‖∑ a' : (ZMod q)ˣ, fiberMultCharSum q hq hne χ a' N - μ * N‖ := by
      rw [hS_decomp]
      calc ‖μ * ↑N‖
          = ‖∑ a' : (ZMod q)ˣ, fiberMultCharSum q hq hne χ a' N -
              (∑ a' : (ZMod q)ˣ, fiberMultCharSum q hq hne χ a' N - μ * ↑N)‖ := by
            ring_nf
          _ ≤ ‖∑ a' : (ZMod q)ˣ, fiberMultCharSum q hq hne χ a' N‖ +
              ‖∑ a' : (ZMod q)ˣ, fiberMultCharSum q hq hne χ a' N - μ * ↑N‖ :=
            norm_sub_le _ _
    have h2 : ‖μ * ↑N‖ = ‖μ‖ * N := by
      rw [norm_mul, Complex.norm_natCast]
    linarith [hemd_bound, hSN_minus_muN]
  have hmu_norm : ‖μ‖ ≤ δ + C * ε' := by
    by_cases hN_zero : (N : ℝ) = 0
    · linarith [hN_pos]
    · exact le_of_mul_le_mul_right hmu_bound hN_pos
  -- Step 3: Bound ‖F(a,N)‖
  -- ‖F(a,N)‖ ≤ ‖F(a) - μ·V(a)‖ + ‖μ‖·V(a) ≤ ε'·N + (δ + C·ε')·N
  have hVa_le_N : (((Finset.range N).filter
      (fun n => emWalkUnit q hq hne n = a)).card : ℝ) ≤ N := by
    have h := Finset.card_filter_le (Finset.range N) (fun n => emWalkUnit q hq hne n = a)
    rw [Finset.card_range] at h
    exact_mod_cast h
  calc ‖fiberMultCharSum q hq hne χ a N‖
      = ‖(fiberMultCharSum q hq hne χ a N -
          μ * ((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card) +
          μ * ((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card‖ := by
        ring_nf
      _ ≤ ‖fiberMultCharSum q hq hne χ a N -
          μ * ((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card‖ +
          ‖μ * ((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card‖ :=
        norm_add_le _ _
      _ ≤ ε' * N + ‖μ‖ * N := by
          have h1 := hμ a
          have h2 : ‖μ * (((Finset.range N).filter
              (fun n => emWalkUnit q hq hne n = a)).card : ℂ)‖ ≤ ‖μ‖ * N := by
            rw [norm_mul, Complex.norm_natCast]
            exact mul_le_mul_of_nonneg_left hVa_le_N (norm_nonneg _)
          linarith
      _ ≤ ε' * N + (δ + C * ε') * N := by
          linarith [mul_le_mul_of_nonneg_right hmu_norm (le_of_lt hN_pos)]
      _ = (ε' + δ + C * ε') * N := by ring
      _ = ε * N := by
          -- ε' + δ + C·ε' = (1+C)·ε' + δ = (1+C)·ε/(2(C+1)) + ε/2 = ε/2 + ε/2 = ε
          rw [hε'_def, hδ_def]
          have hC1_ne : (C + 1 : ℝ) ≠ 0 := ne_of_gt hC1_pos
          field_simp
          ring

/-- **EMD + VCB → MC**: unconditional multiplier equidistribution combined
    with vanishing conditional bias implies Mullin's Conjecture.

    Chain: EMD + VCB → CME → CCSB → MC. -/
theorem emd_vcb_implies_mc (hemd : EMDirichlet) (hvcb : VanishingConditionalBias) :
    MullinConjecture :=
  cme_implies_mc (emd_vcb_implies_cme hemd hvcb)

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
