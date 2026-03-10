import EM.CMEReduction
import EM.MullinCRT
import EM.CRTPointwiseTransfer

/-!
# Adelic Decomposition of CME

## The orbit-specificity barrier

Every approach so far works at a fixed prime q and tries to prove something
about the q-coordinate of the walk. The orbit-specificity barrier keeps
appearing because a statement that holds for *almost all* starting points
can't be pinned to the specific orbit n=2 at a specific prime q.

## The adelic insight

The EM process doesn't privilege any prime q — it treats all primes
simultaneously. At each step, the race across all coordinates of
∏_p (Z/pZ)× is run and the winner (smallest prime factor) is selected.
The process is intrinsically adelic.

CRT multiplier invariance (`crt_multiplier_invariance`) shows that
`minFac(P+1) mod q` depends only on the residues of P at primes ≠ q.
This means the multiplier at q is determined by the *non-q coordinates*
of the walk.

## Decomposition of CME

We decompose `ConditionalMultiplierEquidist` into two independent conditions:

1. **`MultiplierMarginalEquidist` (MME)**: The multiplier character sums
   vanish unconditionally — the multiplier has no preferred direction.

2. **`MultWalkIndependence` (MWI)**: The multiplier at q is asymptotically
   independent of the walk position at q — knowledge of where you are
   doesn't predict the next step's direction.

**Main result**: MWI + MME ⟺ CME (Theorems `mwi_mme_implies_cme` and
`cme_implies_mwi`, `cme_implies_mme`).

This decomposition separates:
- The *analytic* content (MME): follows from population equidistribution
  via standard analytic number theory
- The *structural* content (MWI): follows from CRT multiplier invariance +
  cross-prime decorrelation

## Why cross-prime decorrelation gives MWI

The argument:
1. `crt_multiplier_invariance` (proved): mult_q(n) depends only on
   P₂(n) mod r for primes r ≠ q
2. Cross-prime decorrelation (new hypothesis): the walk positions at
   different primes are asymptotically independent
3. Therefore: conditioning on walk_q(n) = a doesn't change the
   distribution of the non-q coordinates
4. Therefore: mult_q(n) is independent of walk_q(n), i.e., MWI

## Connection to the profinite / condensed perspective

The walk lives in Ẑ× = ∏_p (Z/pZ)×. The empirical measure
μ_N = (1/N) ∑ δ_{P₂(n)} converges to Haar measure on Ẑ× iff CCSB holds
for all q simultaneously (Weyl criterion for compact abelian groups,
since the continuous characters of Ẑ× are exactly the Dirichlet characters).

The `CrossPrimeDecorrelation` hypothesis asserts that the convergence is
independent across different primes — the joint measure factors as a
product of marginals. This is the natural "all primes at once" formulation.
-/

open Mullin Euclid MullinGroup

/-! ## Definitions -/

/-- **Multiplier Marginal Equidistribution**: for each prime q, the
    unconditional multiplier character sums vanish. This is strictly
    weaker than CCSB (which is about walk character sums) and captures
    the analytic content of the equidistribution. -/
def MultiplierMarginalEquidist : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ‖∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ)‖ ≤ ε * N

/-- **Multiplier-Walk Independence**: the multiplier at q is asymptotically
    independent of the walk position at q. Formally: the conditional
    character sum is bounded by the unconditional one plus o(N).

    This captures the structural content of CME: knowledge of the walk
    position doesn't help predict the multiplier's character value.

    **Why it should hold**: By CRT multiplier invariance, the multiplier
    at q depends only on non-q coordinates. By cross-prime decorrelation,
    the q-coordinate is independent of non-q coordinates. Therefore the
    multiplier is independent of the walk position. -/
def MultWalkIndependence : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1) (a : (ZMod q)ˣ),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ‖∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
      (χ (emMultUnit q hq hne n) : ℂ)‖ ≤
    ‖∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ)‖ + ε * ↑N

/-- **Adelic Equidistribution**: the conjunction of multiplier marginal
    equidistribution and multiplier-walk independence. Equivalent to CME
    but decomposed into analytic and structural components. -/
def AdelicEquidist : Prop :=
  MultiplierMarginalEquidist ∧ MultWalkIndependence

/-- **Cross-Prime Decorrelation**: for distinct primes q, r, the walk
    positions at q and r are asymptotically independent. In character-sum
    form: for non-trivial characters χ_q, χ_r, the product character
    sum ∑ χ_q(walk_q(n)) · χ_r(walk_r(n)) = o(N).

    This is the "all primes at once" hypothesis. Combined with CRT
    multiplier invariance, it implies MultWalkIndependence. -/
def CrossPrimeDecorrelation : Prop :=
  ∀ (q r : Nat) [Fact (Nat.Prime q)] [Fact (Nat.Prime r)]
    (hq : IsPrime q) (hne_q : ∀ k, seq k ≠ q)
    (hr : IsPrime r) (hne_r : ∀ k, seq k ≠ r)
    (_hqr : q ≠ r)
    (χ_q : (ZMod q)ˣ →* ℂˣ) (χ_r : (ZMod r)ˣ →* ℂˣ)
    (_hχ_q : χ_q ≠ 1) (_hχ_r : χ_r ≠ 1),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ‖∑ n ∈ Finset.range N,
      (χ_q (emWalkUnit q hq hne_q n) : ℂ) *
      (χ_r (emWalkUnit r hr hne_r n) : ℂ)‖ ≤ ε * ↑N

/-! ## Main results -/

/-- **MWI + MME ⟹ CME**: The adelic decomposition implies conditional
    multiplier equidistribution.

    Proof: Given χ ≠ 1 and walk position a, by MWI the conditional sum
    is bounded by the unconditional sum plus ε/2·N. By MME the
    unconditional sum is at most ε/2·N. Together: at most ε·N. -/
theorem mwi_mme_implies_cme
    (hmwi : MultWalkIndependence)
    (hmme : MultiplierMarginalEquidist) :
    ConditionalMultiplierEquidist := by
  intro q inst hq hne χ hχ a ε hε
  -- Apply MWI with ε/2
  obtain ⟨N₁, hN₁⟩ := hmwi q hq hne χ hχ a (ε / 2) (by linarith)
  -- Apply MME with ε/2
  obtain ⟨N₂, hN₂⟩ := hmme q hq hne χ hχ (ε / 2) (by linarith)
  use max N₁ N₂
  intro N hN
  have hN₁' : N ≥ N₁ := le_of_max_le_left hN
  have hN₂' : N ≥ N₂ := le_of_max_le_right hN
  -- The conditional sum is bounded by |unconditional| + ε/2 · N
  have h1 := hN₁ N hN₁'
  -- The unconditional sum is bounded by ε/2 · N
  have h2 := hN₂ N hN₂'
  -- Combine: |conditional| ≤ |unconditional| + ε/2·N ≤ ε/2·N + ε/2·N = ε·N
  calc ‖∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
        (χ (emMultUnit q hq hne n) : ℂ)‖
      ≤ ‖∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ)‖ + ε / 2 * ↑N := h1
    _ ≤ ε / 2 * ↑N + ε / 2 * ↑N := by linarith
    _ = ε * ↑N := by ring

/-- **CME ⟹ MWI**: Conditional multiplier equidistribution implies
    multiplier-walk independence (trivially: the conditional sum is
    already small, so it's bounded by anything non-negative plus ε·N). -/
theorem cme_implies_mwi (hcme : ConditionalMultiplierEquidist) :
    MultWalkIndependence := by
  intro q inst hq hne χ hχ a ε hε
  obtain ⟨N₀, hN₀⟩ := hcme q hq hne χ hχ a ε hε
  exact ⟨N₀, fun N hN => by
    have h := hN₀ N hN
    have h2 := norm_nonneg (∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ))
    linarith⟩

/-- **CME ⟹ MME**: Conditional multiplier equidistribution implies
    multiplier marginal equidistribution. Proof: the unconditional sum
    decomposes as ∑_a (conditional sum at a), and each piece is o(N). -/
theorem cme_implies_mme (hcme : ConditionalMultiplierEquidist) :
    MultiplierMarginalEquidist := by
  intro q inst hq hne χ hχ ε hε
  haveI : Fact (Nat.Prime q) := inst
  -- Number of walk positions: Fintype.card (ZMod q)ˣ
  set C := Fintype.card (ZMod q)ˣ with hC_def
  have hC_pos : (0 : ℝ) < C := Nat.cast_pos.mpr Fintype.card_pos
  -- Set ε' = ε / C so that C · ε' = ε
  set ε' := ε / C with hε'_def
  have hε'_pos : 0 < ε' := div_pos hε hC_pos
  -- For each walk position a, CME gives N₀(a) such that the conditional sum ≤ ε' * N
  have hcme_a : ∀ a : (ZMod q)ˣ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
        (χ (emMultUnit q hq hne n) : ℂ)‖ ≤ ε' * N :=
    fun a => hcme q hq hne χ hχ a ε' hε'_pos
  -- Choose N₀(a) for each a
  choose N₀_fn hN₀_fn using hcme_a
  -- Take the maximum N₀ over all a
  set N₀ := Finset.univ.sup N₀_fn with hN₀_def
  refine ⟨N₀, fun N hN => ?_⟩
  -- Step 1: Partition the sum by walk position using sum_fiberwise
  have hdecomp : ∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ) =
      ∑ a : (ZMod q)ˣ, ∑ n ∈ (Finset.range N).filter
        (fun n => emWalkUnit q hq hne n = a),
        (χ (emMultUnit q hq hne n) : ℂ) := by
    rw [← Finset.sum_fiberwise (Finset.range N) (emWalkUnit q hq hne)
      (fun n => (χ (emMultUnit q hq hne n) : ℂ))]
  rw [hdecomp]
  -- Step 2: Triangle inequality + CME bound at each fiber + count fibers
  calc ‖∑ a : (ZMod q)ˣ, ∑ n ∈ (Finset.range N).filter
        (fun n => emWalkUnit q hq hne n = a),
        (χ (emMultUnit q hq hne n) : ℂ)‖
      ≤ ∑ a : (ZMod q)ˣ, ‖∑ n ∈ (Finset.range N).filter
        (fun n => emWalkUnit q hq hne n = a),
        (χ (emMultUnit q hq hne n) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _a : (ZMod q)ˣ, ε' * N := by
        apply Finset.sum_le_sum
        intro a _
        apply hN₀_fn a N
        exact le_trans (Finset.le_sup (Finset.mem_univ a)) hN
    _ = C * (ε' * N) := by
        rw [Finset.sum_const, nsmul_eq_mul, hC_def, Finset.card_univ]
    _ = ε * N := by
        rw [hε'_def]
        field_simp

/-- **Adelic Equidistribution ⟹ CME** -/
theorem adelic_implies_cme (h : AdelicEquidist) :
    ConditionalMultiplierEquidist :=
  mwi_mme_implies_cme h.2 h.1

/-- **Adelic Equidistribution ⟹ CCSB** -/
theorem adelic_implies_ccsb (h : AdelicEquidist) :
    ComplexCharSumBound :=
  cme_implies_ccsb (adelic_implies_cme h)

/-- **Adelic Equidistribution ⟹ MC**: the adelic decomposition gives
    Mullin's Conjecture via CME → CCSB → MC. -/
theorem adelic_implies_mc (h : AdelicEquidist) :
    MullinConjecture :=
  cme_implies_mc (adelic_implies_cme h)

/-- **CME ⟹ Adelic Equidistribution**: the decomposition is an
    equivalence. -/
theorem cme_implies_adelic (hcme : ConditionalMultiplierEquidist) :
    AdelicEquidist :=
  ⟨cme_implies_mme hcme, cme_implies_mwi hcme⟩

/-! ## CME ↔ Adelic Equivalence -/

/-- **CME ↔ AdelicEquidist**: full equivalence between conditional multiplier
    equidistribution and the adelic decomposition. -/
theorem cme_iff_adelic : ConditionalMultiplierEquidist ↔ AdelicEquidist :=
  ⟨cme_implies_adelic, adelic_implies_cme⟩

/-! ## CRT Multiplier-Walk Fiber Independence

The key structural observation is that `mult_q(n) = minFac(P(n)+1) mod q`
depends only on the non-q coordinates of the walk (by CRT multiplier
invariance). If we can show that the non-q coordinates are asymptotically
independent of the q-coordinate, then `mult_q` is independent of `walk_q`,
giving MWI.

We formalize this via `CRTMultiplierFiber`: the mixed character sum
∑ χ(mult_q(n)) · ψ(walk_q(n)) = o(N) for nontrivial χ, ψ at the same
prime q. This says mult_q and walk_q are independent at the character level.

The reduction CRTMultiplierFiber + MME → MWI uses character orthogonality to
express the indicator 1_{walk(n)=a} via Fourier inversion on (Z/qZ)×,
then applies the triangle inequality. This is **PROVED** as
`crt_fiber_implies_mwi_proved` using `char_indicator_expansion` and
`MulChar.equivToUnitHom` to bridge between DirichletCharacter and unit hom types.

The reduction CPD → CRTMultiplierFiber would require expressing
"mult_q depends only on non-q coordinates" in character-sum form and
composing with cross-prime decorrelation. This is stated as an open Prop
`CPDImpliesCRTFiber`.
-/

/-- **CRT Multiplier-Walk Fiber Independence**: for nontrivial characters
    χ, ψ at the same prime q, the mixed character sum
    ∑ χ(mult(n)) · ψ(walk(n)) = o(N). This says: the multiplier at q is
    statistically independent of the walk at q at the character level.

    **Why it should hold**: By CRT multiplier invariance, mult_q depends
    only on non-q coordinates of the walk. By cross-prime decorrelation,
    these non-q coordinates are independent of walk_q. Therefore any
    character of mult_q is independent of any character of walk_q. -/
def CRTMultiplierFiber : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1)
    (ψ : (ZMod q)ˣ →* ℂˣ) (_hψ : ψ ≠ 1),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : Nat, ∀ N ≥ N₀,
    ‖∑ n ∈ Finset.range N,
      (χ (emMultUnit q hq hne n) : ℂ) * (ψ (emWalkUnit q hq hne n) : ℂ)‖ ≤ ε * N

/-! ## Fourier inversion bridge: CRTMultiplierFiber + MME → MWI (PROVED)

The key identity uses character orthogonality (Fourier inversion on (Z/qZ)×):
  1_{walk(n)=a} = (1/(q-1)) · ∑_ψ ψ(a⁻¹) · ψ(walk(n))
so the conditional sum becomes:
  ∑_{walk(n)=a} χ(mult(n)) = (1/(q-1)) · ∑_ψ ψ(a⁻¹) · ∑_n χ(mult(n))·ψ(walk(n))
The trivial character ψ=1 gives (1/(q-1)) · ∑ χ(mult(n)) (bounded by MME).
Each nontrivial ψ gives a cross term bounded by CRTMultiplierFiber.
Triangle inequality over (q-2) nontrivial characters gives MWI.

We use `MulChar.equivToUnitHom` to bridge between `DirichletCharacter ℂ q`
(which is `Fintype` and has `char_indicator_expansion`) and `(ZMod q)ˣ →* ℂˣ`
(used in our hypothesis definitions).
-/

section FourierInversionBridge

open Finset DirichletCharacter

/-- The conditional character sum at fiber a equals the Fourier inversion
    expansion using DirichletCharacters. This is the key identity:
    ∑_{walk(n)=a} χ(mult(n)) = (1/(q-1)) · ∑_ψ ψ(↑a⁻¹) · ∑_n χ(mult(n))·ψ(↑walk(n))
    where the outer sum is over all DirichletCharacters ψ mod q. -/
private theorem conditional_sum_fourier_expansion
    {q : Nat} [inst : Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (a : (ZMod q)ˣ) (N : Nat) :
    (q : ℂ) - 1 ≠ 0 →
    ∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
      (χ (emMultUnit q hq hne n) : ℂ) =
    (1 / ((q : ℂ) - 1)) * ∑ ψ : DirichletCharacter ℂ q,
      ψ (↑a⁻¹ : ZMod q) * ∑ n ∈ Finset.range N,
        (χ (emMultUnit q hq hne n) : ℂ) * ψ (↑(emWalkUnit q hq hne n) : ZMod q) := by
  intro hq1
  -- RHS: swap sums, apply orthogonality
  have hkey : ∑ ψ : DirichletCharacter ℂ q,
      ψ (↑a⁻¹ : ZMod q) * ∑ n ∈ Finset.range N,
        (χ (emMultUnit q hq hne n) : ℂ) * ψ (↑(emWalkUnit q hq hne n) : ZMod q) =
    ((q : ℂ) - 1) * ∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
      (χ (emMultUnit q hq hne n) : ℂ) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    -- Now: ∑_n ∑_ψ ψ(↑a⁻¹) * (χ(mult(n)) * ψ(↑walk(n)))
    -- Rearrange each summand: ψ(a⁻¹) * (χ(m) * ψ(w)) = χ(m) * (ψ(a⁻¹) * ψ(w))
    conv_lhs =>
      arg 2; ext n; arg 2; ext ψ
      rw [show ψ (↑a⁻¹ : ZMod q) * ((χ (emMultUnit q hq hne n) : ℂ) *
          ψ (↑(emWalkUnit q hq hne n) : ZMod q)) =
        (χ (emMultUnit q hq hne n) : ℂ) *
          (ψ (↑a⁻¹ : ZMod q) * ψ (↑(emWalkUnit q hq hne n) : ZMod q)) by ring]
    -- Factor χ(mult(n)) out of the inner sum
    simp_rw [← Finset.mul_sum]
    -- Apply char_indicator_expansion: ∑_ψ ψ(↑a⁻¹) · ψ(↑walk(n)) = (q-1)·[walk(n)=a]
    simp_rw [char_indicator_expansion a (emWalkUnit q hq hne _)]
    -- Now have: ∑_n χ(mult(n)) * (if walk(n)=a then q-1 else 0)
    -- Transform: f(n) * (if p then c else 0) = if p then f(n) * c else 0
    simp_rw [mul_ite, mul_zero]
    -- Now: ∑_n if walk(n)=a then χ(mult(n)) * (q-1) else 0
    rw [← Finset.sum_filter]
    -- Now: ∑_{walk(n)=a} χ(mult(n)) * (q-1) = (q-1) * ∑_{walk(n)=a} χ(mult(n))
    conv_lhs => arg 2; ext; rw [mul_comm]
    rw [← Finset.mul_sum]
  rw [hkey, one_div, ← mul_assoc, inv_mul_cancel₀ hq1, one_mul]

/-- **CRTFiberImpliesMWI PROVED**: CRT multiplier-walk fiber independence plus
    multiplier marginal equidistribution implies multiplier-walk independence.

    Uses Fourier inversion on (Z/qZ)× via `char_indicator_expansion` and
    `MulChar.equivToUnitHom` to bridge character types. -/
theorem crt_fiber_implies_mwi_proved
    (hfiber : CRTMultiplierFiber)
    (hmme : MultiplierMarginalEquidist) :
    MultWalkIndependence := by
  intro q inst hq hne χ hχ a ε hε
  haveI : Fact (Nat.Prime q) := inst
  -- Constants
  set C := Fintype.card (DirichletCharacter ℂ q) with hC_def
  have hC_pos : (0 : ℝ) < C := Nat.cast_pos.mpr Fintype.card_pos
  have hq_pos : (0 : ℝ) < (q : ℝ) - 1 := by
    have : 1 < q := inst.out.one_lt
    exact sub_pos.mpr (by exact_mod_cast this)
  have hq1 : (q : ℂ) - 1 ≠ 0 := by
    exact_mod_cast ne_of_gt hq_pos
  -- Number of nontrivial characters = C - 1
  -- ε-budget: ε_mme for the trivial character, ε_fiber for each nontrivial one
  -- Total bound: (1/(q-1)) · (ε_mme · N + (C-1) · ε_fiber · N)
  -- We want this ≤ ‖uncond‖ + ε · N, so set ε_mme and ε_fiber appropriately
  set ε' := ε * ((q : ℝ) - 1) / C with hε'_def
  have hε' : 0 < ε' := by positivity
  -- From MME: ‖∑ χ(mult)‖ ≤ ε' · N for large N
  obtain ⟨N₁, hN₁⟩ := hmme q hq hne χ hχ ε' hε'
  -- For each nontrivial ψ_D : DirichletCharacter, convert to unit hom and apply CRTFiber
  -- The number of nontrivial DirichletCharacters is finite, so take max N₀ over all
  have hfin : ∀ ψ_D : DirichletCharacter ℂ q, ψ_D ≠ 1 →
      ∃ N₀ : Nat, ∀ N ≥ N₀,
        ‖∑ n ∈ Finset.range N,
          (χ (emMultUnit q hq hne n) : ℂ) * ψ_D (↑(emWalkUnit q hq hne n) : ZMod q)‖ ≤ ε' * N := by
    intro ψ_D hψ_D
    -- Convert ψ_D to unit hom
    set ψ_U := ψ_D.toUnitHom with hψ_U_def
    have hψ_U : ψ_U ≠ 1 := by
      intro heq
      apply hψ_D
      -- heq : toUnitHom ψ_D = 1
      -- Need: ψ_D = 1
      -- Strategy: use MulChar.equivToUnitHom (an Equiv) which is injective
      -- equivToUnitHom ψ_D = toUnitHom ψ_D = ψ_U = 1
      -- equivToUnitHom 1 = toUnitHom 1 = 1 (need to prove this)
      apply (MulChar.equivToUnitHom (R := ZMod q) (R' := ℂ)).injective
      -- Goal: equivToUnitHom ψ_D = equivToUnitHom 1
      rw [show MulChar.equivToUnitHom ψ_D = ψ_U from by
        rw [hψ_U_def]; rfl]
      rw [heq]
      -- Goal: 1 = equivToUnitHom 1, i.e., (1 : (ZMod q)ˣ →* ℂˣ) = toUnitHom 1
      -- toUnitHom 1 = Units.map (1 : MulChar). Both send u ↦ 1.
      symm; ext u
      simp [MulChar.equivToUnitHom, MulChar.toUnitHom, Units.coe_map, MulChar.one_apply_coe]
    -- The sum ∑ χ(mult) · ψ_D(↑walk) = ∑ χ(mult) · (ψ_U(walk) : ℂ)
    have hsum_eq : ∀ N, ∑ n ∈ Finset.range N,
        (χ (emMultUnit q hq hne n) : ℂ) * ψ_D (↑(emWalkUnit q hq hne n) : ZMod q) =
      ∑ n ∈ Finset.range N,
        (χ (emMultUnit q hq hne n) : ℂ) * (ψ_U (emWalkUnit q hq hne n) : ℂ) := by
      intro N
      apply Finset.sum_congr rfl
      intro n _
      simp only [hψ_U_def, MulChar.coe_toUnitHom]
    obtain ⟨N₀, hN₀⟩ := hfiber q hq hne χ hχ ψ_U hψ_U ε' hε'
    exact ⟨N₀, fun N hN => by rw [hsum_eq]; exact hN₀ N hN⟩
  -- Choose N₀(ψ_D) for each nontrivial ψ_D, take max
  -- Use Classical.choice to get the function
  open Classical in
  have hchoice : ∀ ψ_D : DirichletCharacter ℂ q,
      ∃ N₀ : Nat, ∀ N ≥ N₀,
        ‖∑ n ∈ Finset.range N,
          (χ (emMultUnit q hq hne n) : ℂ) * ψ_D (↑(emWalkUnit q hq hne n) : ZMod q)‖ ≤ ε' * N := by
    intro ψ_D
    by_cases hψ : ψ_D = 1
    · -- Trivial character: ψ_D = 1, so ψ_D(x) = 1 for units, sum = ∑ χ(mult)
      subst hψ
      refine ⟨N₁, fun N hN => ?_⟩
      have hsimp : ∀ n, (1 : DirichletCharacter ℂ q)
          (↑(emWalkUnit q hq hne n) : ZMod q) = 1 :=
        fun n => MulChar.one_apply_coe _
      simp_rw [hsimp, mul_one]
      exact hN₁ N hN
    · exact hfin ψ_D hψ
  choose N₀_fn hN₀_fn using hchoice
  set N₀ := max N₁ (Finset.univ.sup N₀_fn)
  refine ⟨N₀, fun N hN => ?_⟩
  -- Step 1: Express conditional sum via Fourier expansion
  rw [conditional_sum_fourier_expansion hq hne χ a N hq1]
  -- Step 2: Bound using triangle inequality
  -- ‖(1/(q-1)) · ∑_ψ ...‖ ≤ (1/(q-1)) · ∑_ψ ‖...‖
  -- Factor: ‖(1/(q-1)) · S‖ = (1/(q-1)) · ‖S‖ since 1/(q-1) > 0
  have hfactor : ‖(1 / ((q : ℂ) - 1))‖ = 1 / ((q : ℝ) - 1) := by
    rw [norm_div, norm_one]
    congr 1
    rw [show (q : ℂ) - 1 = ((q : ℝ) - 1 : ℝ) from by push_cast; ring]
    rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt hq_pos)]
  rw [norm_mul, hfactor]
  have hfactor_pos : (0 : ℝ) < 1 / ((q : ℝ) - 1) := by positivity
  -- Step 2a: triangle inequality for the outer sum
  have htri : ‖∑ ψ : DirichletCharacter ℂ q,
      ψ (↑a⁻¹ : ZMod q) * ∑ n ∈ Finset.range N,
        (χ (emMultUnit q hq hne n) : ℂ) * ψ (↑(emWalkUnit q hq hne n) : ZMod q)‖ ≤
    ∑ ψ : DirichletCharacter ℂ q,
      ‖∑ n ∈ Finset.range N,
        (χ (emMultUnit q hq hne n) : ℂ) * ψ (↑(emWalkUnit q hq hne n) : ZMod q)‖ := by
    calc _ ≤ ∑ ψ : DirichletCharacter ℂ q,
          ‖ψ (↑a⁻¹ : ZMod q) * ∑ n ∈ Finset.range N,
            (χ (emMultUnit q hq hne n) : ℂ) * ψ (↑(emWalkUnit q hq hne n) : ZMod q)‖ :=
        norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro ψ _
        rw [norm_mul]
        have hψ_norm : ‖ψ (↑a⁻¹ : ZMod q)‖ ≤ 1 := by
          -- Use walkTelescope_char_norm_one with ψ.toUnitHom
          have h1 := walkTelescope_char_norm_one ψ.toUnitHom a⁻¹
          rw [MulChar.coe_toUnitHom] at h1
          linarith
        calc ‖ψ (↑a⁻¹ : ZMod q)‖ * _ ≤ 1 * _ :=
              mul_le_mul_of_nonneg_right hψ_norm (norm_nonneg _)
          _ = _ := one_mul _
  -- Step 2b: each term bounded by ε' * N
  have hterm_bound : ∑ ψ : DirichletCharacter ℂ q,
      ‖∑ n ∈ Finset.range N,
        (χ (emMultUnit q hq hne n) : ℂ) * ψ (↑(emWalkUnit q hq hne n) : ZMod q)‖ ≤
    C * (ε' * N) := by
    calc _ ≤ ∑ _ψ : DirichletCharacter ℂ q, ε' * N := by
          apply Finset.sum_le_sum
          intro ψ _
          exact hN₀_fn ψ N (le_trans (le_trans
            (Finset.le_sup (Finset.mem_univ ψ)) (le_max_right _ _)) hN)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hC_def, Finset.card_univ]
  -- Step 2c: combine
  have hcombine : 1 / ((q : ℝ) - 1) * (C * (ε' * ↑N)) = ε * ↑N := by
    rw [hε'_def]; field_simp
  have hfinal : 1 / ((q : ℝ) - 1) * ‖∑ ψ : DirichletCharacter ℂ q,
        ψ (↑a⁻¹ : ZMod q) * ∑ n ∈ Finset.range N,
          (χ (emMultUnit q hq hne n) : ℂ) * ψ (↑(emWalkUnit q hq hne n) : ZMod q)‖
    ≤ ε * ↑N := by
    have h1 : ‖∑ ψ : DirichletCharacter ℂ q,
        ψ (↑a⁻¹ : ZMod q) * ∑ n ∈ Finset.range N,
          (χ (emMultUnit q hq hne n) : ℂ) * ψ (↑(emWalkUnit q hq hne n) : ZMod q)‖ ≤
      (C : ℝ) * (ε' * ↑N) := le_trans htri hterm_bound
    calc 1 / ((q : ℝ) - 1) * ‖∑ ψ : DirichletCharacter ℂ q,
          ψ (↑a⁻¹ : ZMod q) * ∑ n ∈ Finset.range N,
            (χ (emMultUnit q hq hne n) : ℂ) * ψ (↑(emWalkUnit q hq hne n) : ZMod q)‖
      ≤ 1 / ((q : ℝ) - 1) * ((C : ℝ) * (ε' * ↑N)) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hfactor_pos)
      _ = ε * ↑N := hcombine
  linarith [norm_nonneg (∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ))]

end FourierInversionBridge

/-- **CPDImpliesCRTFiber**: Cross-prime decorrelation implies CRT
    multiplier-walk fiber independence.

    The mathematical argument: CRT multiplier invariance shows mult_q(n)
    is a function of the non-q coordinates {walk_r(n) : r ≠ q}. Therefore
    χ(mult_q(n)) can be expanded in characters of the non-q coordinates.
    The mixed sum ∑ χ(mult_q(n))·ψ(walk_q(n)) then becomes a sum of
    cross-prime character products, each bounded by CPD.

    This is left as an open Prop because expressing "mult_q is a function
    of non-q coordinates" in character-sum form requires a finite Fourier
    expansion argument. -/
def CPDImpliesCRTFiber : Prop :=
  CrossPrimeDecorrelation → CRTMultiplierFiber

/-! ## Reductions via CRT fiber independence -/

/-- **CRTMultiplierFiber + MME → CME**: CRT fiber independence plus MME gives
    full CME, via the PROVED Fourier inversion bridge. -/
theorem crt_fiber_mme_implies_cme
    (hfiber : CRTMultiplierFiber)
    (hmme : MultiplierMarginalEquidist) :
    ConditionalMultiplierEquidist :=
  mwi_mme_implies_cme (crt_fiber_implies_mwi_proved hfiber hmme) hmme

/-- **CRTMultiplierFiber + MME → MC**: CRT fiber independence plus MME gives
    Mullin's Conjecture. -/
theorem crt_fiber_mme_implies_mc
    (hfiber : CRTMultiplierFiber)
    (hmme : MultiplierMarginalEquidist) :
    MullinConjecture :=
  cme_implies_mc (crt_fiber_mme_implies_cme hfiber hmme)

/-- **CPD + MME → MC**: if CPDImpliesCRTFiber holds, then cross-prime
    decorrelation plus MME gives Mullin's Conjecture. -/
theorem cpd_mme_implies_mc
    (hcpd_bridge : CPDImpliesCRTFiber)
    (hcpd : CrossPrimeDecorrelation)
    (hmme : MultiplierMarginalEquidist) :
    MullinConjecture :=
  crt_fiber_mme_implies_mc (hcpd_bridge hcpd) hmme

/-! ## Route landscape -/

/-- **All routes to MC with adelic decomposition**: witnesses that the
    adelic route (MWI + MME) joins the existing landscape. -/
theorem all_routes_to_mc_adelic :
    -- Route 1: Adelic (MWI + MME)
    (AdelicEquidist → MullinConjecture) ∧
    -- Route 2: DSL (PE → CME)
    (DeterministicStabilityLemma → PopulationEquidist → MullinConjecture) ∧
    -- Route 3: CRT bridge (PCE → OCE)
    (CRTPointwiseTransferBridge → PopulationConditionalEquidist → MullinConjecture) :=
  ⟨adelic_implies_mc,
   fun hdsl hpe => cme_implies_mc (hdsl hpe),
   fun hbridge hpce => oce_implies_mc (hbridge hpce)⟩

/-- **Enhanced landscape with full equivalences and the CPD route**.
    Witnesses all known routes to MC through the adelic framework:
    - CME ↔ AdelicEquidist (full equivalence, no open Props)
    - AdelicEquidist → MC (direct)
    - MWI + MME → MC (decomposition route)
    - CRTMultiplierFiber + MME → CME (PROVED via Fourier inversion)
    - CPD + MME → MC (conditional on CPDImpliesCRTFiber only) -/
theorem adelic_landscape :
    -- Equivalence: CME ↔ AdelicEquidist
    (ConditionalMultiplierEquidist ↔ AdelicEquidist) ∧
    -- Route 1: Adelic → MC
    (AdelicEquidist → MullinConjecture) ∧
    -- Route 2: MWI + MME → MC (decomposition)
    (MultWalkIndependence → MultiplierMarginalEquidist → MullinConjecture) ∧
    -- Route 3: CRT fiber + MME → CME (PROVED, no open Props)
    (CRTMultiplierFiber → MultiplierMarginalEquidist →
      ConditionalMultiplierEquidist) ∧
    -- Route 4: CPD + MME → MC (conditional on CPDImpliesCRTFiber only)
    (CPDImpliesCRTFiber → CrossPrimeDecorrelation →
      MultiplierMarginalEquidist → MullinConjecture) :=
  ⟨cme_iff_adelic,
   adelic_implies_mc,
   fun hmwi hmme => adelic_implies_mc ⟨hmme, hmwi⟩,
   fun hfiber hmme => crt_fiber_mme_implies_cme hfiber hmme,
   fun hcpd_br hcpd hmme => cpd_mme_implies_mc hcpd_br hcpd hmme⟩

/-! ## Walk-multiplier autocorrelation equivalence

The walk lag-1 autocorrelation ∑ χ(w(n))·conj(χ(w(n+1))) equals the
conjugate of the multiplier character sum by `walk_shift_one_correlation`
(from EquidistSelfCorrecting.lean). Since conjugation preserves norms,
MME is equivalent to vanishing walk lag-1 autocorrelation.
-/

/-- **MME ↔ walk autocorrelation**: multiplier marginal equidistribution is
    equivalent to vanishing walk lag-1 autocorrelation.
    Uses `walk_shift_one_correlation`: ∑ χ(w(n))·conj(χ(w(n+1))) = conj(∑ χ(m(n))).
    Since ‖conj(z)‖ = ‖z‖, the norms are equal. -/
theorem mme_iff_walk_autocorrelation :
    MultiplierMarginalEquidist ↔
    (∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
      (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
    ∀ (ε : ℝ) (_hε : 0 < ε),
    ∃ N₀ : Nat, ∀ N ≥ N₀,
      ‖∑ n ∈ Finset.range N,
        ((χ (emWalkUnit q hq hne n) : ℂ) *
         starRingEnd ℂ (χ (emWalkUnit q hq hne (n + 1)) : ℂ))‖ ≤ ε * N) := by
  constructor
  · -- Forward: MME → walk autocorrelation
    intro hmme q inst hq hne χ hχ ε hε
    obtain ⟨N₀, hN₀⟩ := hmme q hq hne χ hχ ε hε
    exact ⟨N₀, fun N hN => by
      rw [walk_shift_one_correlation q hq hne χ N, RCLike.norm_conj]
      exact hN₀ N hN⟩
  · -- Backward: walk autocorrelation → MME
    intro hauto q inst hq hne χ hχ ε hε
    obtain ⟨N₀, hN₀⟩ := hauto q hq hne χ hχ ε hε
    exact ⟨N₀, fun N hN => by
      have h := hN₀ N hN
      rw [walk_shift_one_correlation q hq hne χ N, RCLike.norm_conj] at h
      exact h⟩

/-- **CCSB ∧ MME landscape**: CME decomposes into CCSB (walk equidist) and MME
    (multiplier equidist): CCSB ∧ MME sits between CCSB alone and CME. -/
theorem ccsb_mme_landscape :
    (ConditionalMultiplierEquidist → ComplexCharSumBound ∧ MultiplierMarginalEquidist) ∧
    (ComplexCharSumBound ∧ MultiplierMarginalEquidist →
      MultWalkIndependence → ConditionalMultiplierEquidist) :=
  ⟨fun h => ⟨cme_implies_ccsb h, cme_implies_mme h⟩,
   fun ⟨_, hmme⟩ hmwi => mwi_mme_implies_cme hmwi hmme⟩

/-! ## The pre-collapse measure

The user's proposal defines the EM distribution ν_N^(q) as the empirical
measure of the walk on (Z/qZ)× up to the time q enters the sequence.
For the purpose of proving MC at q, we are in the regime where q has not
yet appeared, so this IS the walk measure.

The joint measure ν_N = ⊗_q ν_N^(q) factoring as a product is exactly
`CrossPrimeDecorrelation`. The Weyl criterion for the compact group
Ẑ× = ∏_p (Z/pZ)× says: the walk equidistributes in Ẑ× iff for every
non-trivial continuous character (= Dirichlet character of some modulus),
the Cesàro mean vanishes. This is CCSB for all q simultaneously.

The profinite structure gives a potential proof strategy:
1. At each finite level Q, the walk equidistributes in ∏_{p≤Q} (Z/pZ)×
   (from SubgroupEscape + PRE)
2. If this equidistribution is uniform in Q, the full profinite limit holds
3. This uniformity is exactly what cross-prime decorrelation provides
-/
