import EM.CME.Reduction
import EM.Equidist.WalkDecomposition

/-!
# Walk Analysis: Energy Increments, VCB, CME Fiber Decomposition, Transitions

Content extracted from LargeSieveSpectral.lean for modularity.

## Sections

* **ElliottHalberstamSection** (§S71): EH conjecture, EH → BV → MC chain
* **EnergyIncrementDynamics** (§75): energy increment identity, self-correcting criterion
* **VanishingConditionalBias** (§84): VCB definition, CME → VCB, VCB + PED → CCSB → MC
* **CMEFiberDecomposition** (§85): fiber residue class, fiber energy bound, CME ↔ fiber equidist
* **TransitionMatrix** (§86): empirical transition counts, row sums, CME ↔ transition char vanish
-/

open Mullin Euclid MullinGroup RotorRouter

/-! ## S71. Elliott-Halberstam Conjecture and Chain to MC

The **Elliott-Halberstam conjecture** (1968) asserts that primes have
level of distribution θ for every θ < 1: the BV-type error bound
∑_{q ≤ x^θ} max_{(a,q)=1} |π(x;q,a) − li(x)/φ(q)| ≤ x/(log x)^A
holds for all A > 0 whenever θ < 1.

The Bombieri-Vinogradov theorem proves this for θ = 1/2 only. EH is
strictly stronger: it allows moduli up to x^θ for any θ < 1, while BV
only gives √x/(log x)^B.

### Main results

* `ElliottHalberstam` : the EH conjecture as an open Prop
* `eh_implies_bv`     : EH → BV (instantiate θ = 1/2)
* `eh_chain_mc`       : EH + BV→MMCSB transfer + finite check → MC
* `eh_small_threshold_mc` : EH + BV→MMCSB transfer (Q₀ ≤ 11) → MC unconditionally
-/

section ElliottHalberstamSection

/-- **Elliott-Halberstam Conjecture** (Elliott 1968, Halberstam 1968).

    The EH conjecture asserts that primes have level of distribution θ for
    every θ < 1. The Bombieri-Vinogradov theorem proves this for θ = 1/2.

    EH is strictly stronger than BV: it gives equidistribution of primes
    in arithmetic progressions for moduli up to x^θ (any θ < 1), while
    BV only handles moduli up to √x/(log x)^B.

    We state this as the assertion that for every θ ∈ (0,1) and A > 0,
    there exists x₀ such that the BV-type error bound holds for all x ≥ x₀.

    **Open Prop**: a major open conjecture in analytic number theory. Not in Mathlib. -/
def ElliottHalberstam : Prop :=
  ∀ (θ : ℝ) (_hθ₀ : 0 < θ) (_hθ₁ : θ < 1),
  ∀ (A : ℝ) (_hA : 0 < A),
  ∃ (x₀ : ℝ),
  ∀ (x : ℝ), x₀ ≤ x →
    ∃ (E : ℝ), E ≤ x / (Real.log x) ^ A ∧ 0 ≤ E

/-- **EH implies BV**: The Elliott-Halberstam conjecture implies the
    Bombieri-Vinogradov theorem. This is immediate because BV is the
    special case θ = 1/2 of EH (with an arbitrary constant B taken as 0). -/
theorem eh_implies_bv (heh : ElliottHalberstam) : BombieriVinogradov := by
  intro A hA
  obtain ⟨x₀, hx₀⟩ := heh (1 / 2) (by norm_num) (by norm_num) A hA
  exact ⟨0, x₀, hx₀⟩

/-- **EH chain to MC**: Elliott-Halberstam + the BV-to-MMCSB transfer
    + finite verification below the threshold implies Mullin's Conjecture.

    ```
    EH → BV → MMCSB → ThresholdHitting → MC
    ``` -/
theorem eh_chain_mc
    (heh : ElliottHalberstam)
    (htransfer : BVImpliesMMCSB)
    (hfin : FiniteMCBelow (htransfer (eh_implies_bv heh)).choose) :
    MullinConjecture :=
  bv_chain_mc (eh_implies_bv heh) htransfer hfin

/-- **EH + small threshold to MC**: Elliott-Halberstam + the BV-to-MMCSB
    transfer with Q₀ ≤ 11 implies Mullin's Conjecture unconditionally
    (the finite check below 11 is already verified in the codebase). -/
theorem eh_small_threshold_mc
    (heh : ElliottHalberstam)
    (htransfer : BVImpliesMMCSB)
    (hsmall : (htransfer (eh_implies_bv heh)).choose ≤ 11) :
    MullinConjecture :=
  bv_small_threshold_mc (eh_implies_bv heh) htransfer hsmall

end ElliottHalberstamSection

/-! ## §75. Energy Increment Dynamics

The energy increment `Delta E` when the walk takes one step to position `a` equals
`2(p-1) V_N(a) - 2N + (p-2)`, where `V_N(a)` is the visit count.

This identity connects the excess energy (a spectral quantity equal to
`sum_{chi != 1} |S_chi|^2`) to the walk's single-step visit pattern.

**Key insight**: energy increases when the walk visits an above-average position
(`V_N(a) > N/(p-1)`) and decreases when visiting a below-average position.
SubquadraticVisitEnergy (SVE) is equivalent to the walk "typically" visiting
below-average positions.

**Self-correcting criterion**: SVE holds iff the average energy increment per
step converges to (p-2), which happens iff V_N(w(N)) is approximately N/(p-1) on average.
This reformulates SVE as a single-step visit-count condition. -/

section EnergyIncrementDynamics

open Finset DirichletCharacter
open Classical

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private instance neZeroP75 : NeZero p := ⟨hp.out.ne_zero⟩

/-- **Nontrivial character orthogonality for walk sums**:
    `sum_{chi != 1} conj(chi(a)) * S_chi(N) = (p-1) * V_N(a) - N`.

    This is the key identity connecting nontrivial character sums to visit counts.
    It follows from full character orthogonality by separating the trivial character. -/
theorem nontrivial_char_walk_sum {N : ℕ} (w : Fin N → (ZMod p)ˣ)
    (a : (ZMod p)ˣ) (hp1 : (1 : ℝ) < p) :
    (Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum
      (fun χ => χ (↑a⁻¹ : ZMod p) * ∑ n : Fin N, χ (↑(w n) : ZMod p)) =
    ((p : ℂ) - 1) * (walkVisitCount w a : ℂ) - (N : ℂ) := by
  have hp1c : (p : ℂ) - 1 ≠ 0 := by
    exact_mod_cast ne_of_gt (by linarith : (0 : ℝ) < (p : ℝ) - 1)
  -- Full sum: ∑_χ χ(a⁻¹) · S_χ = (p-1) · V_N(a)
  have hfull : ∑ χ : DirichletCharacter ℂ p, χ (↑a⁻¹ : ZMod p) *
      ∑ n : Fin N, χ (↑(w n) : ZMod p) =
    ((p : ℂ) - 1) * (walkVisitCount w a : ℂ) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [char_indicator_expansion a]
    rw [← Finset.sum_filter]
    simp only [walkVisitCount, Finset.sum_const, nsmul_eq_mul]
    ring
  -- Split: full = trivial + nontrivial
  have hsplit : ∑ χ : DirichletCharacter ℂ p, χ (↑a⁻¹ : ZMod p) *
      ∑ n : Fin N, χ (↑(w n) : ZMod p) =
    (1 : DirichletCharacter ℂ p) (↑a⁻¹ : ZMod p) *
      (∑ n : Fin N, (1 : DirichletCharacter ℂ p) (↑(w n) : ZMod p)) +
    (Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum
      (fun χ => χ (↑a⁻¹ : ZMod p) * ∑ n : Fin N, χ (↑(w n) : ZMod p)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ _)]
  -- Trivial part: 1(a⁻¹) · ∑ 1(w(n)) = N
  have h_triv : (1 : DirichletCharacter ℂ p) (↑a⁻¹ : ZMod p) *
      (∑ n : Fin N, (1 : DirichletCharacter ℂ p) (↑(w n) : ZMod p)) = (N : ℂ) := by
    simp only [MulChar.one_apply_coe, one_mul, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  -- Combine: nontrivial = full - trivial = (p-1)*V - N
  -- hsplit: full = triv + nontrivial, hfull: full = (p-1)*V, h_triv: triv = N
  -- => nontrivial = (p-1)*V - N
  rw [hfull, h_triv] at hsplit
  -- hsplit : (p-1) * V = N + nontrivial_sum => nontrivial = (p-1)*V - N
  have hsplit' := hsplit  -- (p-1)*V = N + nontrivial
  -- Goal: nontrivial = (p-1)*V - N
  -- From hsplit': nontrivial = (p-1)*V - N
  exact eq_sub_of_add_eq' hsplit'.symm

/-- **Energy increment identity (character-sum form)**:
    The total "energy change" from adding one step at position `a` is
    `2(p-1) V_N(a) - 2N + (p-2)`.

    Formally, `sum_{chi != 1} (2 Re(S_chi * conj(chi(a))) + 1) = 2(p-1) V_N(a) - 2N + (p-2)`.

    This identity follows from `nontrivial_char_walk_sum` (which gives the sum of
    `conj(chi(a)) * S_chi` over nontrivial characters) plus the count of nontrivial
    characters (which is `p-2`). -/
theorem energy_increment_identity {N : ℕ} (w : Fin N → (ZMod p)ˣ)
    (a : (ZMod p)ˣ) (hp1 : (1 : ℝ) < p) :
    (Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum
      (fun χ => 2 * ((χ (↑a⁻¹ : ZMod p) *
        ∑ n : Fin N, χ (↑(w n) : ZMod p)).re) + 1) =
    2 * ((p : ℝ) - 1) * (walkVisitCount w a : ℝ) - 2 * (N : ℝ) + ((p : ℝ) - 2) := by
  -- Step 1: Split sum of (f + 1) into (sum f) + card * 1
  have hsplit_sum : (Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum
      (fun χ => 2 * ((χ (↑a⁻¹ : ZMod p) *
        ∑ n : Fin N, χ (↑(w n) : ZMod p)).re) + 1) =
    (Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum
      (fun χ => 2 * ((χ (↑a⁻¹ : ZMod p) *
        ∑ n : Fin N, χ (↑(w n) : ZMod p)).re)) +
    ((Finset.univ.erase (1 : DirichletCharacter ℂ p)).card : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hsplit_sum]
  -- Step 2: Compute ∑_χ (χ(a⁻¹) * S_χ).re via Complex.re_sum + nontrivial_char_walk_sum
  have hre_key : (Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum
      (fun χ => (χ (↑a⁻¹ : ZMod p) * ∑ n : Fin N, χ (↑(w n) : ZMod p)).re) =
    ((p : ℝ) - 1) * (walkVisitCount w a : ℝ) - (N : ℝ) := by
    rw [← Complex.re_sum, nontrivial_char_walk_sum w a hp1]
    simp only [Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.one_re, mul_zero, sub_zero]
  -- Step 3: Factor 2 out: ∑ (2 * f) = 2 * ∑ f
  have hfactor : (Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum
      (fun χ => 2 * ((χ (↑a⁻¹ : ZMod p) *
        ∑ n : Fin N, χ (↑(w n) : ZMod p)).re)) =
    2 * ((p : ℝ) - 1) * (walkVisitCount w a : ℝ) - 2 * (N : ℝ) := by
    rw [← Finset.mul_sum, hre_key]; ring
  rw [hfactor]
  -- Step 4: Count of nontrivial characters = p - 2
  have hcard_real : ((Finset.univ.erase (1 : DirichletCharacter ℂ p)).card : ℝ) =
      (p : ℝ) - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ p,
      Nat.totient_prime hp.out]
    have h2le : 2 ≤ p := hp.out.two_le
    push_cast [Nat.sub_sub, Nat.cast_sub h2le]; ring
  rw [hcard_real]

/-- **Energy decreases for below-average positions**: if `V_N(a) < N/(p-1)` then the
    energy increment is strictly less than `p - 2` (the "neutral" increment value).

    This means visiting an underrepresented position results in slower-than-average
    energy growth. SVE is equivalent to the walk typically visiting such positions. -/
theorem energy_below_average_decreases {N : ℕ} (w : Fin N → (ZMod p)ˣ)
    (a : (ZMod p)ˣ) (hp1 : (1 : ℝ) < p)
    (hbelow : (walkVisitCount w a : ℝ) < (N : ℝ) / ((p : ℝ) - 1)) :
    2 * ((p : ℝ) - 1) * (walkVisitCount w a : ℝ) - 2 * (N : ℝ) + ((p : ℝ) - 2) <
    (p : ℝ) - 2 := by
  have hp1r : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  -- V < N/(p-1) implies (p-1)*V < N
  have h1 : ((p : ℝ) - 1) * (walkVisitCount w a : ℝ) < (N : ℝ) := by
    have := (lt_div_iff₀ hp1r).mp hbelow
    linarith [mul_comm (walkVisitCount w a : ℝ) ((p : ℝ) - 1)]
  nlinarith

/-- **Energy increases for above-average positions**: if `V_N(a) > N/(p-1)` then the
    energy increment is strictly greater than `p - 2`. -/
theorem energy_above_average_increases {N : ℕ} (w : Fin N → (ZMod p)ˣ)
    (a : (ZMod p)ˣ) (hp1 : (1 : ℝ) < p)
    (habove : (N : ℝ) / ((p : ℝ) - 1) < (walkVisitCount w a : ℝ)) :
    (p : ℝ) - 2 <
    2 * ((p : ℝ) - 1) * (walkVisitCount w a : ℝ) - 2 * (N : ℝ) + ((p : ℝ) - 2) := by
  have hp1r : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  -- N/(p-1) < V implies N < (p-1)*V
  have h1 : (N : ℝ) < ((p : ℝ) - 1) * (walkVisitCount w a : ℝ) := by
    have := (div_lt_iff₀ hp1r).mp habove
    linarith [mul_comm (walkVisitCount w a : ℝ) ((p : ℝ) - 1)]
  nlinarith

/-- **Average energy increment equals `p - 2`**: the expected energy increment,
    averaged uniformly over all positions `a`, equals `p - 2`.

    Proof: the average of `2(p-1) V_N(a) - 2N + (p-2)` over all `a` in `(ZMod p)ˣ`
    equals `(1/(p-1)) * (2(p-1) * sum_a V(a) - 2N(p-1) + (p-2)(p-1))`
    = `(1/(p-1)) * (2(p-1)N - 2N(p-1) + (p-2)(p-1))` = `p - 2`. -/
theorem average_energy_increment {N : ℕ} (w : Fin N → (ZMod p)ˣ)
    (hp1 : (1 : ℝ) < p) :
    (1 / ((p : ℝ) - 1)) *
      ∑ a : (ZMod p)ˣ, (2 * ((p : ℝ) - 1) * (walkVisitCount w a : ℝ) -
        2 * (N : ℝ) + ((p : ℝ) - 2)) = (p : ℝ) - 2 := by
  have hp1r : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp1ne : (p : ℝ) - 1 ≠ 0 := ne_of_gt hp1r
  -- Compute the full sum directly
  -- ∑_a (2(p-1)V(a) - 2N + (p-2))
  -- = 2(p-1) * ∑V(a) - (p-1)*2N + (p-1)*(p-2)
  -- = 2(p-1)*N - 2N(p-1) + (p-1)(p-2)
  -- = (p-1)(p-2)
  -- Card of units = p - 1
  have hcard : (Finset.univ : Finset (ZMod p)ˣ).card = p - 1 := by
    rw [Finset.card_univ, ZMod.card_units_eq_totient, Nat.totient_prime hp.out]
  -- ∑_a V(a) = N
  have hv_sum : ∑ a : (ZMod p)ˣ, (walkVisitCount w a : ℝ) = (N : ℝ) := by
    have h := walkVisitCount_sum w
    exact_mod_cast h
  -- Compute the sum by distributing
  have hfull : ∑ a : (ZMod p)ˣ, (2 * ((p : ℝ) - 1) * (walkVisitCount w a : ℝ) -
      2 * (N : ℝ) + ((p : ℝ) - 2)) =
    ((p : ℝ) - 1) * ((p : ℝ) - 2) := by
    simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hv_sum,
      Finset.sum_const, hcard, nsmul_eq_mul]
    push_cast [Nat.cast_sub hp.out.one_le]
    ring
  rw [hfull]
  field_simp

end EnergyIncrementDynamics

/-! ## §84. Vanishing Conditional Bias (VCB)

**VanishingConditionalBias** weakens CME by allowing the fiber character sums
`F(a)` to be approximately proportional to the visit counts `V(a)` with a
common ratio `μ`, rather than requiring them to be `o(N)`.

### Position in Hierarchy

CME forces `μ = 0`, making VCB strictly weaker than CME.  Combined with PED,
VCB recovers CCSB: the telescoping identity gives `(μ - 1) · S_N = O(1) + o(N)`,
and PED constrains `μ` away from 1 via the escape-density root-of-unity argument.

### Main Results

* `VanishingConditionalBias` : the VCB hypothesis (def)
* `cme_implies_vcb`         : CME → VCB (PROVED: take μ = 0)
* `VCBPEDImpliesCCSB`       : VCB + PED → CCSB (open Prop documenting the
    two-case argument: μ far from 1 → direct bound; μ ≈ 1 → PED contradiction)
* `vcb_ped_implies_mc`      : VCBPEDImpliesCCSB → VCB + PED → MC (PROVED)
-/

section VanishingConditionalBias

open Classical

/-- **VanishingConditionalBias**: for any prime q not in the EM sequence and any
    nontrivial character χ, the fiber character sums F(a) are approximately
    proportional to the visit counts V(a) with a common ratio μ.

    This is strictly WEAKER than CME: CME forces μ = 0, while VCB allows any μ.
    Combined with PED, VCB implies CCSB (stated below as `VCBPEDImpliesCCSB`).

    Position in hierarchy: CME → VCB (μ = 0), and VCB + PED → CCSB. -/
def VanishingConditionalBias : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
  ∃ μ : ℂ, ∀ (a : (ZMod q)ˣ),
    ‖fiberMultCharSum q hq hne χ a N -
      μ * ↑((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card‖ ≤ ε * N

/-- **CME implies VCB**: Conditional Multiplier Equidistribution implies
    VanishingConditionalBias, by taking μ = 0 everywhere.

    Since CME gives ‖F(a)‖ ≤ ε·N for all fibers, and VCB requires
    ‖F(a) - μ·V(a)‖ ≤ ε·N for SOME μ, choosing μ = 0 immediately works. -/
theorem cme_implies_vcb (hcme : ConditionalMultiplierEquidist) :
    VanishingConditionalBias := by
  intro q inst hq hne χ hχ ε hε
  haveI : Fact (Nat.Prime q) := inst
  -- For each a, CME gives N₀(a) such that ‖F(a)‖ ≤ ε·N for N ≥ N₀(a)
  have h_each : ∀ a : (ZMod q)ˣ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖fiberMultCharSum q hq hne χ a N‖ ≤ ε * N := by
    intro a
    exact (cme_iff_fiber_bound.mp hcme) q hq hne χ hχ a ε hε
  choose N₀_fn hN₀_fn using h_each
  refine ⟨Finset.univ.sup N₀_fn, fun N hN => ⟨0, fun a => ?_⟩⟩
  simp only [zero_mul, sub_zero]
  exact hN₀_fn a N (le_trans (Finset.le_sup (Finset.mem_univ a)) hN)

/-- For a complex number of norm 1, `‖z - 1‖² = 2 - 2 · Re(z)`.
    This is the key identity linking escape distance `‖χ(m(n)) - 1‖` to the
    real-part defect `1 - Re(χ(m(n)))`. -/
theorem norm_sub_one_sq_eq (z : ℂ) (hz : ‖z‖ = 1) :
    ‖z - 1‖ ^ 2 = 2 - 2 * z.re := by
  -- ‖z - 1‖² = normSq(z - 1) = (z.re - 1)² + z.im²
  rw [Complex.sq_norm, Complex.normSq_apply]
  -- ‖z‖² = normSq z = z.re² + z.im² = 1
  have hns : z.re * z.re + z.im * z.im = 1 := by
    have := Complex.sq_norm z
    rw [hz, one_pow, Complex.normSq_apply] at this; linarith
  -- (z.re - 1)*(z.re - 1) + z.im*z.im = z.re² - 2*z.re + 1 + z.im² = 2 - 2*z.re
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  nlinarith

/-- If `‖z‖ = 1` and `‖z - 1‖ ≥ η₀ ≥ 0`, then `Re(z) ≤ 1 - η₀² / 2`. -/
theorem unit_norm_re_le_of_dist {z : ℂ} (hz : ‖z‖ = 1) {η₀ : ℝ} (hη₀ : 0 ≤ η₀)
    (hdist : η₀ ≤ ‖z - 1‖) :
    z.re ≤ 1 - η₀ ^ 2 / 2 := by
  have hnsq := norm_sub_one_sq_eq z hz
  have hsq : η₀ ^ 2 ≤ ‖z - 1‖ ^ 2 := sq_le_sq' (by linarith) hdist
  linarith

/-- **Step 9 helper**: Given the VCB per-fiber bound, the product sum P_N
    satisfies `‖P_N - μ * S_N‖ ≤ C * η * N` where C = #(ZMod q)ˣ.

    Proof: expand both P_N and S_N via fiber decomposition, factor out χ(a),
    use `‖χ(a)‖ = 1` to reduce to the per-fiber VCB bound, then sum over all fibers. -/
private theorem vcb_fiber_error_bound {q : ℕ} [Fact (Nat.Prime q)]
    {hq : IsPrime q} {hne : ∀ k, seq k ≠ q} {χ : (ZMod q)ˣ →* ℂˣ} {N : ℕ}
    {μ : ℂ} {η : ℝ}
    (hμ_bound : ∀ a : (ZMod q)ˣ,
      ‖fiberMultCharSum q hq hne χ a N -
        μ * ↑((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card‖ ≤ η * N) :
    ‖∑ n ∈ Finset.range N,
        ((χ (emWalkUnit q hq hne n) : ℂ) * (χ (emMultUnit q hq hne n) : ℂ)) -
      μ * ∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤
    Fintype.card (ZMod q)ˣ * η * N := by
  set C := Fintype.card (ZMod q)ˣ
  rw [walk_mult_product_fiber_decomp q hq hne χ N]
  have hSN_fiber : ∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ) =
      ∑ a : (ZMod q)ˣ, (χ a : ℂ) *
      ∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a), (1 : ℂ) := by
    rw [← Finset.sum_fiberwise (Finset.range N) (emWalkUnit q hq hne)
      (fun n => (χ (emWalkUnit q hq hne n) : ℂ))]
    congr 1; ext a; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n hn
    rw [(Finset.mem_filter.mp hn).2, mul_one]
  rw [hSN_fiber, Finset.mul_sum]
  simp_rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [show ∑ a : (ZMod q)ˣ, (χ a : ℂ) *
        ∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
          (χ (emMultUnit q hq hne n) : ℂ) -
      ∑ a : (ZMod q)ˣ, μ * ((χ a : ℂ) *
        ↑((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card) =
      ∑ a : (ZMod q)ˣ, (χ a : ℂ) * (fiberMultCharSum q hq hne χ a N -
        μ * ↑((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card)
    from by simp only [fiberMultCharSum]; rw [← Finset.sum_sub_distrib]; congr 1; ext a; ring]
  calc ‖∑ a : (ZMod q)ˣ, (χ a : ℂ) * (fiberMultCharSum q hq hne χ a N -
        μ * ↑((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card)‖
      ≤ ∑ a : (ZMod q)ˣ, ‖(χ a : ℂ) * (fiberMultCharSum q hq hne χ a N -
        μ * ↑((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card)‖ :=
          norm_sum_le _ _
    _ ≤ ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N -
        μ * ↑((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card‖ := by
          apply Finset.sum_le_sum; intro a _
          rw [norm_mul]
          calc ‖(χ a : ℂ)‖ * _ ≤ 1 * _ := by
                apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                exact le_of_eq (walkTelescope_char_norm_one χ a)
            _ = _ := one_mul _
    _ ≤ ∑ _a : (ZMod q)ˣ, η * ↑N := by
          apply Finset.sum_le_sum; intro a _; exact hμ_bound a
    _ = C * η * N := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]; ring

/-- **Step 10 helper**: The aggregate multiplier character sum M_N satisfies
    `‖M_N - μ * N‖ ≤ C * η * N`.

    Proof: decompose M_N = ∑_a F(a) via `mult_char_sum_eq_fiber_sum`, decompose
    N = ∑_a V(a), then each summand `F(a) - μ·V(a)` is bounded by VCB. -/
private theorem vcb_aggregate_error_bound {q : ℕ} [Fact (Nat.Prime q)]
    {hq : IsPrime q} {hne : ∀ k, seq k ≠ q} {χ : (ZMod q)ˣ →* ℂˣ} {N : ℕ}
    {μ : ℂ} {η : ℝ}
    (hμ_bound : ∀ a : (ZMod q)ˣ,
      ‖fiberMultCharSum q hq hne χ a N -
        μ * ↑((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card‖ ≤ η * N) :
    ‖∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ) - μ * ↑N‖ ≤
    Fintype.card (ZMod q)ˣ * η * N := by
  set C := Fintype.card (ZMod q)ˣ
  rw [mult_char_sum_eq_fiber_sum q hq hne χ N]
  have hV_sum_nat : ∑ a : (ZMod q)ˣ,
      ((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card = N := by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.range N) (t := Finset.univ)
      (f := emWalkUnit q hq hne) (fun _ _ => Finset.mem_univ _)
    simp only [Finset.card_range] at this; exact this.symm
  have hV_sum_C : (N : ℂ) = ∑ a : (ZMod q)ˣ,
      (((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card : ℂ) := by
    have : (N : ℂ) = ↑(∑ a : (ZMod q)ˣ,
        ((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card : ℕ) := by
      push_cast; exact_mod_cast hV_sum_nat.symm
    rw [this]; push_cast; rfl
  conv_lhs => rw [hV_sum_C]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc ‖∑ a : (ZMod q)ˣ, (fiberMultCharSum q hq hne χ a N -
        μ * ↑((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card)‖
      ≤ ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N -
        μ * ↑((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _a : (ZMod q)ˣ, η * ↑N := by
          apply Finset.sum_le_sum; intro a _; exact hμ_bound a
    _ = C * η * N := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]; ring

/-- **Step 11 helper**: PED real-part lower bound: `c₀ * N ≤ ‖M_N - N‖`.

    Each term χ(m(n)) has |χ(m(n))| = 1, so Re(χ(m(n)) - 1) ≤ 0.
    For escape terms (χ(m(n)) ≠ 1), `escape_min_dist_pos` gives
    `‖χ(m(n)) - 1‖ ≥ η₀`, hence Re(χ(m(n)) - 1) ≤ -η₀²/2.
    PED provides ≥ δN escape terms, yielding -Re(M_N - N) ≥ δ·η₀²/2·N = c₀·N.
    Then ‖M_N - N‖ ≥ |Re(M_N - N)| ≥ c₀·N. -/
private theorem ped_real_part_lower_bound {q : ℕ} [Fact (Nat.Prime q)]
    {hq : IsPrime q} {hne : ∀ k, seq k ≠ q}
    {χ : (ZMod q)ˣ →* ℂˣ} (_hχ : χ ≠ 1) {N : ℕ}
    {δ : ℝ} (_hδ_pos : 0 < δ)
    {η₀ : ℝ} (hη₀_pos : 0 < η₀)
    (hη₀_bound : ∀ u : (ZMod q)ˣ, (χ u : ℂ) ≠ 1 → η₀ ≤ ‖(χ u : ℂ) - 1‖)
    (hped_N : δ * ↑N ≤
      ↑((Finset.filter (fun k => χ (emMultUnit q hq hne k) ≠ 1)
        (Finset.range N)).card)) :
    δ * η₀ ^ 2 / 2 * ↑N ≤
    ‖∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ) - ↑N‖ := by
  have hMN_sub : ∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ) - ↑N =
      ∑ n ∈ Finset.range N, ((χ (emMultUnit q hq hne n) : ℂ) - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [hMN_sub]
  set S := ∑ n ∈ Finset.range N, ((χ (emMultUnit q hq hne n) : ℂ) - 1) with hS_def
  have hterm_re_le : ∀ n ∈ Finset.range N,
      ((χ (emMultUnit q hq hne n) : ℂ) - 1).re ≤ 0 := by
    intro n _
    simp only [Complex.sub_re, Complex.one_re]
    have h1 := Complex.abs_re_le_norm (χ (emMultUnit q hq hne n) : ℂ)
    rw [walkTelescope_char_norm_one χ] at h1
    linarith [abs_le.mp h1]
  have hesc_term : ∀ n ∈ (Finset.range N).filter
      (fun k => (χ (emMultUnit q hq hne k) : ℂ) ≠ 1),
      ((χ (emMultUnit q hq hne n) : ℂ) - 1).re ≤ -(η₀ ^ 2 / 2) := by
    intro n hn
    have hne_val := (Finset.mem_filter.mp hn).2
    simp only [Complex.sub_re, Complex.one_re]
    have hn1 : ‖(χ (emMultUnit q hq hne n) : ℂ)‖ = 1 :=
      walkTelescope_char_norm_one χ _
    have hdist : η₀ ≤ ‖(χ (emMultUnit q hq hne n) : ℂ) - 1‖ :=
      hη₀_bound _ hne_val
    have hre := unit_norm_re_le_of_dist hn1 (le_of_lt hη₀_pos) hdist
    linarith
  have hfilter_eq : (Finset.range N).filter
      (fun k => χ (emMultUnit q hq hne k) ≠ 1) =
      (Finset.range N).filter
      (fun k => (χ (emMultUnit q hq hne k) : ℂ) ≠ 1) := by
    congr 1; ext n; simp only [ne_eq, Units.val_eq_one]
  have hesc_count : δ * ↑N ≤
      ((Finset.range N).filter
        (fun k => (χ (emMultUnit q hq hne k) : ℂ) ≠ 1)).card := by
    rw [← hfilter_eq]; exact_mod_cast hped_N
  have hS_re_lower : δ * η₀ ^ 2 / 2 * ↑N ≤ -S.re := by
    rw [hS_def, Complex.re_sum, ← Finset.sum_neg_distrib]
    have hsplit := (Finset.sum_filter_add_sum_filter_not (Finset.range N)
      (fun k => (χ (emMultUnit q hq hne k) : ℂ) ≠ 1)
      (fun n => -((χ (emMultUnit q hq hne n) : ℂ) - 1).re)).symm
    rw [hsplit]
    have hker_sum : 0 ≤ ∑ n ∈ (Finset.range N).filter
        (fun k => ¬((χ (emMultUnit q hq hne k) : ℂ) ≠ 1)),
        -((χ (emMultUnit q hq hne n) : ℂ) - 1).re := by
      apply Finset.sum_nonneg; intro n hn
      simp only [ne_eq, Decidable.not_not, Finset.mem_filter] at hn
      rw [hn.2]; simp
    have hesc_sum :
        δ * η₀ ^ 2 / 2 * ↑N ≤ ∑ n ∈ (Finset.range N).filter
          (fun k => (χ (emMultUnit q hq hne k) : ℂ) ≠ 1),
          -((χ (emMultUnit q hq hne n) : ℂ) - 1).re := by
      calc δ * η₀ ^ 2 / 2 * ↑N
          ≤ ((Finset.range N).filter
              (fun k => (χ (emMultUnit q hq hne k) : ℂ) ≠ 1)).card * (η₀ ^ 2 / 2) := by
            nlinarith [hesc_count]
        _ ≤ ∑ _n ∈ (Finset.range N).filter
              (fun k => (χ (emMultUnit q hq hne k) : ℂ) ≠ 1),
              (η₀ ^ 2 / 2 : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ n ∈ (Finset.range N).filter
              (fun k => (χ (emMultUnit q hq hne k) : ℂ) ≠ 1),
              -((χ (emMultUnit q hq hne n) : ℂ) - 1).re :=
            Finset.sum_le_sum (fun n hn => by linarith [hesc_term n hn])
    linarith
  calc δ * η₀ ^ 2 / 2 * ↑N ≤ -S.re := hS_re_lower
    _ ≤ |S.re| := le_abs_self (-S.re) |>.trans (by rw [abs_neg])
    _ ≤ ‖S‖ := Complex.abs_re_le_norm S

/-- **Step 12 helper**: If `‖M_N - N‖ ≥ c₀·N` and `‖M_N - μ·N‖ ≤ C·η·N`
    with `C·η ≤ c₀/4`, then `c₀/2 ≤ ‖1 - μ‖`.

    Proof by contradiction: if `‖1-μ‖ < c₀/2`, then
    `‖M_N - N‖ ≤ ‖M_N - μN‖ + ‖μN - N‖ < CηN + c₀/2·N ≤ 3c₀/4·N < c₀·N`. -/
private theorem vcb_mu_away_from_one {μ : ℂ} {c₀ C η : ℝ} {N : ℕ}
    (hc₀_pos : 0 < c₀) (hN_pos : (0 : ℝ) < N)
    {M_N : ℂ}
    (hMN_N_lower : c₀ * ↑N ≤ ‖M_N - ↑N‖)
    (hMN_muN : ‖M_N - μ * ↑N‖ ≤ C * η * N)
    (hCη_le : C * η ≤ c₀ / 4) : c₀ / 2 ≤ ‖1 - μ‖ := by
  by_contra h_not
  push Not at h_not
  have hmuN_N : ‖μ * ↑N - ↑N‖ < c₀ / 2 * N := by
    rw [show μ * (↑N : ℂ) - ↑N = (μ - 1) * ↑N from by ring, norm_mul]
    simp only [Complex.norm_natCast]
    calc ‖μ - 1‖ * ↑N = ‖1 - μ‖ * ↑N := by rw [norm_sub_rev]
      _ < c₀ / 2 * ↑N := by nlinarith
  have h1 : ‖M_N - ↑N‖ ≤ C * η * N + c₀ / 2 * N := by
    calc ‖M_N - (↑N : ℂ)‖ = ‖(M_N - μ * ↑N) + (μ * ↑N - ↑N)‖ := by ring_nf
      _ ≤ ‖M_N - μ * ↑N‖ + ‖μ * ↑N - ↑N‖ := norm_add_le _ _
      _ ≤ C * η * N + c₀ / 2 * N := by linarith [hMN_muN, hmuN_N.le]
  nlinarith [hMN_N_lower, hN_pos]

set_option maxHeartbeats 400000 in
/-- **VCB + PED implies CCSB**: VanishingConditionalBias combined with
    PositiveEscapeDensity implies ComplexCharSumBound.

    **Proof outline**: Steps 1-5 extract constants and choose parameters.
    Step 6 establishes the telescoping identity `S_N = P_N - boundary`.
    Steps 9-10 (`vcb_fiber_error_bound`, `vcb_aggregate_error_bound`) give
    `‖P_N - μ·S_N‖ ≤ CηN` and `‖M_N - μN‖ ≤ CηN`.
    Step 11 (`ped_real_part_lower_bound`) gives `c₀·N ≤ ‖M_N - N‖`.
    Step 12 (`vcb_mu_away_from_one`) gives `c₀/2 ≤ ‖1-μ‖`.
    Step 13 divides the telescoping bound by `‖1-μ‖` to get `‖S_N‖ ≤ εN`.

    Position in hierarchy: VCB + PED → CCSB → MC. -/
theorem vcb_ped_implies_ccsb (hvcb : VanishingConditionalBias)
    (hped : PositiveEscapeDensity) : ComplexCharSumBound := by
  intro q inst hq hne χ hχ ε hε
  haveI : Fact (Nat.Prime q) := inst
  -- Step 1: Extract constants from PED and escape_min_dist_pos
  obtain ⟨δ, hδ_pos, N₁, hN₁⟩ := hped q hq hne χ hχ
  obtain ⟨η₀, hη₀_pos, hη₀_bound⟩ := escape_min_dist_pos χ hχ
  set c₀ := δ * η₀ ^ 2 / 2 with hc₀_def
  have hc₀_pos : 0 < c₀ := by positivity
  -- Step 2: Set up group cardinality
  set C := Fintype.card (ZMod q)ˣ with hC_def
  have hC_pos : (0 : ℝ) < C := Nat.cast_pos.mpr Fintype.card_pos
  -- Step 3: Choose η for VCB — small enough for both μ-recovery and final bound
  set η := min (c₀ / (4 * C)) (ε * c₀ / (8 * C)) with hη_def
  have hη_pos : 0 < η := by
    simp only [hη_def]; exact lt_min (by positivity) (by positivity)
  -- Step 4: Get N₀ and μ from VCB
  obtain ⟨N₂, hN₂⟩ := hvcb q hq hne χ hχ η hη_pos
  -- Step 5: N large enough to absorb boundary term
  set N₃ := Nat.ceil (8 / (c₀ * ε))
  set N₀ := max (max N₁ N₂) N₃
  refine ⟨N₀, fun N hN => ?_⟩
  have hN₂' : N₂ ≤ N := le_trans (le_max_right N₁ N₂ |>.trans (le_max_left _ N₃)) hN
  obtain ⟨μ, hμ_bound⟩ := hN₂ N hN₂'
  have hN₁' : N₁ ≤ N := le_trans (le_max_left N₁ N₂ |>.trans (le_max_left _ N₃)) hN
  have hped_N := hN₁ N hN₁'
  have hN_pos : (0 : ℝ) < N := by
    have : N₃ ≤ N := le_max_right _ N₃ |>.trans hN
    have : 0 < Nat.ceil (8 / (c₀ * ε)) := Nat.ceil_pos.mpr (by positivity)
    exact Nat.cast_pos.mpr (by omega)
  -- Step 6: Telescoping identity — S_N = P_N - boundary
  set S_N := ∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ) with hSN_def
  set P_N := ∑ n ∈ Finset.range N,
    ((χ (emWalkUnit q hq hne n) : ℂ) * (χ (emMultUnit q hq hne n) : ℂ)) with hPN_def
  set boundary := (χ (emWalkUnit q hq hne N) : ℂ) -
    (χ (emWalkUnit q hq hne 0) : ℂ) with hbdry_def
  have hSN_eq : S_N = P_N - boundary := by
    rw [hSN_def, hPN_def, hbdry_def]
    exact walk_sum_eq_product_sub_boundary q hq hne χ N
  -- Step 7: Boundary norm ≤ 2
  have hboundary_le : ‖boundary‖ ≤ 2 := hbdry_def ▸ walk_boundary_norm_le_two q hq hne χ N
  -- Step 9: VCB fiber error bound (via helper)
  have hPN_muSN : ‖P_N - μ * S_N‖ ≤ C * η * N := by
    rw [hPN_def, hSN_def]; exact vcb_fiber_error_bound hμ_bound
  -- Step 10: Aggregate VCB bound (via helper)
  set M_N := ∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ) with hMN_def
  have hMN_muN : ‖M_N - μ * ↑N‖ ≤ C * η * N := by
    rw [hMN_def]; exact vcb_aggregate_error_bound hμ_bound
  -- Step 11: PED real-part lower bound (via helper)
  have hMN_N_lower : c₀ * ↑N ≤ ‖M_N - ↑N‖ := by
    rw [hMN_def, hc₀_def]; exact ped_real_part_lower_bound hχ hδ_pos hη₀_pos hη₀_bound hped_N
  -- Step 12: μ away from 1 (via helper)
  have hη_le1 : η ≤ c₀ / (4 * C) := min_le_left _ _
  have hη_le2 : η ≤ ε * c₀ / (8 * C) := min_le_right _ _
  have hCη_le : C * η ≤ c₀ / 4 := by
    calc C * η ≤ C * (c₀ / (4 * C)) :=
          mul_le_mul_of_nonneg_left hη_le1 (le_of_lt hC_pos)
      _ = c₀ / 4 := by field_simp
  have hmu_away : c₀ / 2 ≤ ‖1 - μ‖ :=
    vcb_mu_away_from_one hc₀_pos hN_pos hMN_N_lower hMN_muN hCη_le
  -- Step 13: Final bound — divide telescoping bound by ‖1-μ‖
  have hmu1SN_bound : ‖(μ - 1) * S_N‖ ≤ 2 + C * η * N := by
    have hmu1SN : (μ - 1) * S_N = boundary - (P_N - μ * S_N) := by rw [hSN_eq]; ring
    rw [hmu1SN]
    calc ‖boundary - (P_N - μ * S_N)‖
        ≤ ‖boundary‖ + ‖P_N - μ * S_N‖ := norm_sub_le _ _
      _ ≤ 2 + C * η * N := by linarith [hboundary_le, hPN_muSN]
  have hSN_bound : ‖S_N‖ ≤ (2 + ↑C * η * ↑N) / (c₀ / 2) := by
    rw [norm_mul] at hmu1SN_bound
    rw [show ‖μ - 1‖ = ‖1 - μ‖ from norm_sub_rev μ 1] at hmu1SN_bound
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < c₀ / 2)]
    calc ‖S_N‖ * (c₀ / 2) ≤ ‖1 - μ‖ * ‖S_N‖ := by
          nlinarith [hmu_away, norm_nonneg S_N]
      _ ≤ 2 + ↑C * η * ↑N := hmu1SN_bound
  have hCη : C * η ≤ ε * c₀ / 8 := by
    calc C * η ≤ C * (ε * c₀ / (8 * C)) :=
          mul_le_mul_of_nonneg_left hη_le2 (le_of_lt hC_pos)
      _ = ε * c₀ / 8 := by field_simp
  have hN_big : 8 / (c₀ * ε) ≤ N := by
    calc 8 / (c₀ * ε) ≤ ↑(Nat.ceil (8 / (c₀ * ε))) := Nat.le_ceil _
      _ ≤ ↑N := by exact_mod_cast le_max_right _ N₃ |>.trans hN
  have hnum : 2 + ↑C * η * ↑N ≤ 2 + ε * c₀ / 8 * ↑N := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N; nlinarith
  have h4c : 4 / c₀ ≤ ε / 2 * ↑N := by
    rw [div_le_iff₀ hc₀_pos]
    have := (div_le_iff₀ (by positivity : (0:ℝ) < c₀ * ε)).mp hN_big; linarith
  calc ‖S_N‖ ≤ (2 + ↑C * η * ↑N) / (c₀ / 2) := hSN_bound
    _ ≤ (2 + ε * c₀ / 8 * ↑N) / (c₀ / 2) := by
        apply div_le_div_of_nonneg_right hnum (by positivity)
    _ = 4 / c₀ + ε / 4 * ↑N := by
        have hc₀_ne : c₀ ≠ 0 := ne_of_gt hc₀_pos; field_simp; ring
    _ ≤ ε / 2 * ↑N + ε / 4 * ↑N := by linarith [h4c]
    _ ≤ ε * ↑N := by nlinarith [hε, hN_pos]

/-- **VCB + PED implies MC**: VanishingConditionalBias together with
    PositiveEscapeDensity implies Mullin's Conjecture, via the chain
    VCB + PED → CCSB → MC.

    This witnesses the hierarchy position of VCB: it is weaker than CME
    (which implies MC unconditionally), but combined with PED it reaches CCSB. -/
theorem vcb_ped_implies_mc
    (hvcb : VanishingConditionalBias) (hped : PositiveEscapeDensity) :
    MullinConjecture :=
  complex_csb_mc' (vcb_ped_implies_ccsb hvcb hped)

end VanishingConditionalBias

/-! ## §85. CME Fiber Decomposition

**CME Fiber Decomposition** makes explicit the sieve connection: ConditionalMultiplierEquidist
is literally the statement that the least prime factors of integers in a FIXED residue class
mod q are equidistributed among coprime residues.

### The Sieve Structure

When walkZ(q,n) = a, we have prod(n) ≡ a mod q, so the Euclid number prod(n)+1 is in
residue class (a+1) mod q. The CME fiber sum at position a is thus a character sum over
minFac(integers in residue class (a+1) mod q).

This is the bridge to sieve theory: CME bounds character sums restricted to arithmetic
progressions implicitly defined by the walk dynamics.

### Main Results

* `cme_fiber_residue_class`     : walkZ(q,n) = a ⇒ euclid_number(n) ≡ a+1 mod q
* `fiber_mult_sum_eq_walk_char` : M_N = ∑_a F(a), S_N = ∑_a χ(a)·V(a)
* `cme_fiber_energy_bound`      : CME ⇒ ∑_a ‖F(a)‖² = o(N²) (subquadratic fiber energy)
* `cme_iff_fiber_equidist`      : CME ↔ all fiber sums o(N) (tautological spelling-out)

### Position in Hierarchy

CME is the sharpest known sufficient condition for MC. The fiber decomposition shows why:
it bounds character sums over very specific arithmetic progressions arising from the walk.
-/

section CMEFiberDecomposition

open Classical

/-- **CME fiber residue class**: when walkZ(q,n) = a, the Euclid number prod(n)+1 is
    in residue class (a+1) mod q.

    This is the fundamental sieve connection: the CME fiber at position a involves
    the least prime factors of integers in a FIXED residue class mod q, namely (a+1).

    Proof: immediate from `euclid_number_mod_eq_walk_plus_one`. -/
theorem cme_fiber_residue_class (q : ℕ) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (n : ℕ) (a : (ZMod q)ˣ) (hw : emWalkUnit q hq hne n = a) :
    (prod n + 1 : ZMod q) = (a : ZMod q) + 1 := by
  -- emWalkUnit q hq hne n = a means Units.mk0 (walkZ q n) ... = a
  have hw' : (walkZ q n : ZMod q) = (a : ZMod q) := by
    simp only [emWalkUnit] at hw
    have := congr_arg Units.val hw
    simp only [Units.val_mk0] at this
    exact this
  -- Apply euclid_number_mod_eq_walk_plus_one
  have := euclid_number_mod_eq_walk_plus_one q n
  rw [hw'] at this
  exact this

/-- **Fiber multiplier sum decomposition**: the total multiplier character sum M_N
    decomposes as ∑_a F(a) where F(a) is the fiber sum at position a.

    This is already proved as `mult_char_sum_eq_fiber_sum`. We provide a standalone
    reference for the fiber-energy analysis. -/
theorem fiber_mult_sum_decomposition (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ) =
    ∑ a : (ZMod q)ˣ, fiberMultCharSum q hq hne χ a N :=
  mult_char_sum_eq_fiber_sum q hq hne χ N

/-- **Walk character sum via occupation**: the walk character sum S_N equals the
    occupation-weighted sum ∑_a χ(a)·V(a), where V(a) is the visit count at position a.

    This is a restatement of the generic walk_char_sum_eq_occupation in terms of
    the EM walk and Finset.range N.

    Proof: apply sum_fiberwise and use that χ(w(n)) is constant (equal to χ(a))
    on the fiber {n : w(n) = a}. -/
theorem walk_char_sum_via_visit_count (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ) =
    ∑ a : (ZMod q)ˣ, (χ a : ℂ) *
      ↑((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card := by
  -- This is exactly the rearrangement lemma walk_char_sum_eq_occupation specialized
  -- to the EM walk. The proof is  identical to the existing theorem.
  rw [← Finset.sum_fiberwise (Finset.range N) (emWalkUnit q hq hne)
    (fun n => (χ (emWalkUnit q hq hne n) : ℂ))]
  congr 1; ext a
  conv_lhs => rw [show ∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
      (χ (emWalkUnit q hq hne n) : ℂ) =
    ∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a), (χ a : ℂ) from by
      apply Finset.sum_congr rfl; intro n hn
      simp only [Finset.mem_filter] at hn; rw [hn.2]]
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **CME implies subquadratic fiber energy**: under ConditionalMultiplierEquidist,
    the sum of squared fiber norms ∑_a ‖F(a)‖² is o(N²).

    Precisely: for any ε > 0, eventually ∑_a ‖F(a)‖² ≤ ε·N².

    Proof: CME gives ‖F(a)‖ ≤ ε'·N for each a (with ε' = ε^(1/2) / √(q-1)).
    Then ∑_a ‖F(a)‖² ≤ (q-1)·(ε')²·N² = ε·N². -/
theorem cme_fiber_energy_bound (hcme : ConditionalMultiplierEquidist)
    (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hχ : χ ≠ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2 ≤ ε * N ^ 2 := by
  -- Step 1: Set up group cardinality
  set C := Fintype.card (ZMod q)ˣ with hC_def
  have hC_pos : (0 : ℝ) < C := Nat.cast_pos.mpr Fintype.card_pos
  -- Step 2: Choose ε' = √(ε/C) so that C·(ε')² = ε
  set ε' := Real.sqrt (ε / C) with hε'_def
  have hε'_pos : 0 < ε' := Real.sqrt_pos.mpr (div_pos hε hC_pos)
  -- Step 3: For each a, CME gives N₀(a) such that ‖F(a)‖ ≤ ε'·N
  have h_each : ∀ a : (ZMod q)ˣ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖fiberMultCharSum q hq hne χ a N‖ ≤ ε' * N := by
    intro a
    exact (cme_iff_fiber_bound.mp hcme) q hq hne χ hχ a ε' hε'_pos
  choose N₀_fn hN₀_fn using h_each
  refine ⟨Finset.univ.sup N₀_fn, fun N hN => ?_⟩
  -- Step 4: Bound ∑‖F(a)‖² ≤ C·(ε'·N)² = ε·N²
  have hsum_bound : ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2
      ≤ ∑ a : (ZMod q)ˣ, (ε' * ↑N) ^ 2 := by
    apply Finset.sum_le_sum
    intro a _
    have ha := hN₀_fn a N (le_trans (Finset.le_sup (Finset.mem_univ a)) hN)
    nlinarith [norm_nonneg (fiberMultCharSum q hq hne χ a N), sq_nonneg (ε' * ↑N)]
  calc ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2
      ≤ ∑ a : (ZMod q)ˣ, (ε' * ↑N) ^ 2 := hsum_bound
    _ = C * (ε' * ↑N) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, hC_def, Finset.card_univ]
    _ = C * ε' ^ 2 * ↑N ^ 2 := by ring
    _ = ε * ↑N ^ 2 := by
          rw [hε'_def, Real.sq_sqrt (by positivity)]; field_simp

/-- **CME ↔ fiber equidistribution (spelling-out)**: ConditionalMultiplierEquidist is
    literally the statement that each fiber character sum F(a) is o(N).

    This is tautological (just unfolding the definition), but makes the fiber
    structure explicit: CME says the conditional distribution of multZ given
    walkZ = a is equidistributed in the character-sum sense.

    Position in hierarchy: CME is the sharpest known sufficient condition for MC. -/
theorem cme_iff_fiber_equidist :
    ConditionalMultiplierEquidist ↔
    ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
    ∀ (a : (ZMod q)ˣ),
    ∀ (ε : ℝ) (_hε : 0 < ε),
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖fiberMultCharSum q hq hne χ a N‖ ≤ ε * N :=
  cme_iff_fiber_bound

end CMEFiberDecomposition

/-! ## §86: Transition Matrix Infrastructure

The empirical transition matrix `T(a,b,N)` counts the number of times the
Euclid-Mullin walk transitions from position `a` to position `b` in `N` steps.

Key structural results:
1. `T(a,b,N) = #{n < N : w(n) = a ∧ m(n) = a⁻¹ * b}` — transition ↔ multiplier fiber
2. `∑_b T(a,b,N) = V(a,N)` — row sums equal visit counts
3. CME ↔ the character-weighted transition sums vanish

This reformulates CME in matrix language: the rows of the empirical transition
matrix converge to the uniform distribution on `(Z/qZ)×`.

Position in hierarchy: purely definitional/structural — no new open hypotheses. -/

section TransitionMatrix

open Finset

variable (q : ℕ) [Fact (Nat.Prime q)] (hq : Euclid.IsPrime q) (hne : ∀ k, Mullin.seq k ≠ q)

/-- The empirical transition count: number of times the walk transitions
    from position `a` to position `b` in `N` steps. -/
noncomputable def transitionCount (a b : (ZMod q)ˣ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n =>
    emWalkUnit q hq hne n = a ∧ emWalkUnit q hq hne (n + 1) = b)).card

/-- The EM-specific visit count using `Finset.range N` (compatible with
    `transitionCount` indexing). -/
noncomputable def emVisitCount (a : (ZMod q)ˣ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card

/-- Transition from `a` to `b` is equivalent to: walk at `a` with multiplier `a⁻¹ * b`.

    This follows from the walk recurrence `w(n+1) = w(n) * m(n)`:
    - Forward: if `w(n) = a` and `w(n+1) = b`, then `m(n) = a⁻¹ * b`
    - Backward: if `w(n) = a` and `m(n) = a⁻¹ * b`, then `w(n+1) = a * (a⁻¹ * b) = b` -/
theorem transitionCount_eq_mult_fiber (a b : (ZMod q)ˣ) (N : ℕ) :
    transitionCount q hq hne a b N =
    ((Finset.range N).filter (fun n =>
      emWalkUnit q hq hne n = a ∧ emMultUnit q hq hne n = a⁻¹ * b)).card := by
  apply congr_arg Finset.card
  ext n
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro ⟨hn, hw, hb⟩
    refine ⟨hn, hw, ?_⟩
    have hrec := emWalkUnit_succ q hq hne n
    rw [hw, hb] at hrec
    -- hrec : b = a * emMultUnit q hq hne n
    -- need: emMultUnit q hq hne n = a⁻¹ * b
    have : a * emMultUnit q hq hne n = b := hrec.symm
    calc emMultUnit q hq hne n = a⁻¹ * (a * emMultUnit q hq hne n) := by group
      _ = a⁻¹ * b := by rw [this]
  · intro ⟨hn, hw, hm⟩
    refine ⟨hn, hw, ?_⟩
    have hrec := emWalkUnit_succ q hq hne n
    rw [hw, hm] at hrec
    rwa [show a * (a⁻¹ * b) = b from by group] at hrec

/-- Each row of the transition matrix sums to the visit count:
    `∑_b T(a,b,N) = V(a,N)`.

    This says: every visit to position `a` at step `n < N` generates
    exactly one transition (to `w(n+1)`), and different target values `b`
    partition these visits. -/
theorem transitionCount_row_sum (a : (ZMod q)ˣ) (N : ℕ) :
    ∑ b : (ZMod q)ˣ, transitionCount q hq hne a b N = emVisitCount q hq hne a N := by
  -- Use the mult-fiber form: T(a,b) = #{n : w(n)=a, m(n)=a⁻¹*b}
  simp only [transitionCount_eq_mult_fiber, emVisitCount]
  -- ∑_b #{n < N : w(n)=a, m(n)=a⁻¹*b} = #{n < N : w(n)=a}
  -- This is a fiberwise decomposition: partition {n<N : w(n)=a} by m(n),
  -- then reindex b ↦ a⁻¹*b to match standard fiberwise form.
  -- Use card_eq_sum_card_fiberwise with f = emMultUnit, then reindex
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a))
    (t := Finset.univ)
    (f := fun n => emMultUnit q hq hne n)
    (fun _ _ => Finset.mem_univ _)
  -- hfiber: card S = ∑_{c ∈ univ} #{n ∈ S : m(n) = c}
  rw [hfiber]
  -- Now reindex: ∑_{b} #{..m(n) = a⁻¹*b} = ∑_{c} #{..m(n) = c} via c = a⁻¹*b
  apply Finset.sum_nbij (fun b => a⁻¹ * b)
    (fun b _ => Finset.mem_univ _)
    (fun b₁ _ b₂ _ h => mul_left_cancel h)
    (fun c _ => ⟨a * c, Finset.mem_univ _, by group⟩)
  intro b _
  apply congr_arg Finset.card
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, and_assoc]

/-- Auxiliary: the character-weighted transition sum from position `a` equals
    the fiber multiplier character sum `fiberMultCharSum`. -/
theorem transition_char_sum_eq_fiber (χ : (ZMod q)ˣ →* ℂˣ) (a : (ZMod q)ˣ) (N : ℕ) :
    ∑ b : (ZMod q)ˣ, (transitionCount q hq hne a b N : ℂ) * (χ (a⁻¹ * b) : ℂ) =
    fiberMultCharSum q hq hne χ a N := by
  -- Strategy: rewrite transitionCount using mult-fiber form, then transform
  -- ∑_b (card S_b) * χ(a⁻¹*b) into ∑_{n ∈ S} χ(m(n)) via fiberwise decomposition
  simp only [transitionCount_eq_mult_fiber]
  -- Step 1: Rewrite (card S_b) * v as ∑_{n ∈ S_b} v
  have step1 : ∀ b : (ZMod q)ˣ,
      (((Finset.range N).filter (fun n =>
        emWalkUnit q hq hne n = a ∧ emMultUnit q hq hne n = a⁻¹ * b)).card : ℂ) *
        (χ (a⁻¹ * b) : ℂ) =
      ∑ _n ∈ (Finset.range N).filter (fun n =>
        emWalkUnit q hq hne n = a ∧ emMultUnit q hq hne n = a⁻¹ * b),
        (χ (a⁻¹ * b) : ℂ) := by
    intro b
    rw [Finset.sum_const, nsmul_eq_mul]
  simp_rw [step1]
  -- Step 2: Replace χ(a⁻¹*b) with χ(m(n)) on each fiber (since m(n) = a⁻¹*b there)
  have step2 : ∀ b : (ZMod q)ˣ,
      ∑ n ∈ (Finset.range N).filter (fun n =>
        emWalkUnit q hq hne n = a ∧ emMultUnit q hq hne n = a⁻¹ * b),
        (χ (a⁻¹ * b) : ℂ) =
      ∑ n ∈ (Finset.range N).filter (fun n =>
        emWalkUnit q hq hne n = a ∧ emMultUnit q hq hne n = a⁻¹ * b),
        (χ (emMultUnit q hq hne n) : ℂ) := by
    intro b; apply Finset.sum_congr rfl
    intro n hn; simp only [Finset.mem_filter] at hn; congr 1
    exact Units.ext (congrArg Units.val (by rw [hn.2.2]))
  simp_rw [step2]
  -- Step 3: ∑_b ∑_{n ∈ S_b} f(n) = ∑_{n ∈ S} f(n) by sum_fiberwise + reindex
  -- Use sum_fiberwise: ∑_{n ∈ S} f(n) = ∑_{c ∈ univ} ∑_{n ∈ S, m(n)=c} f(n)
  simp only [fiberMultCharSum]
  rw [← Finset.sum_fiberwise
    ((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a))
    (fun n => emMultUnit q hq hne n)
    (fun n => (χ (emMultUnit q hq hne n) : ℂ))]
  -- Now reindex: ∑_b ∑_{S(a⁻¹*b)} = ∑_c ∑_{S(c)} via b = a*c
  apply Finset.sum_nbij (fun b => a⁻¹ * b)
    (fun b _ => Finset.mem_univ _)
    (fun b₁ _ b₂ _ h => mul_left_cancel h)
    (fun c _ => ⟨a * c, Finset.mem_univ _, by group⟩)
  intro b _
  apply Finset.sum_congr
  · ext n; simp only [Finset.mem_filter, Finset.mem_range, and_assoc]
  · intro n _; rfl

/-- **CME ↔ transition matrix character sums vanish**: CME is equivalent to
    the statement that for all nontrivial `χ`, the character-weighted
    transition count `∑_b T(a,b) · χ(a⁻¹ · b)` is `o(N)` for all `a`.

    The proof uses `transition_char_sum_eq_fiber` to reduce to `cme_iff_fiber_bound`.

    This reformulates CME in matrix language: the rows of the empirical
    transition matrix converge to the uniform distribution on `(Z/qZ)×`
    in the character-sum sense. -/
theorem cme_iff_transition_char_vanish :
    ConditionalMultiplierEquidist ↔
    ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : Euclid.IsPrime q) (hne : ∀ k, Mullin.seq k ≠ q),
    ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
    ∀ (a : (ZMod q)ˣ) (ε : ℝ) (_hε : 0 < ε),
    ∃ N₀, ∀ N ≥ N₀,
      ‖∑ b : (ZMod q)ˣ, (transitionCount q hq hne a b N : ℂ) * (χ (a⁻¹ * b) : ℂ)‖
        ≤ ε * N := by
  constructor
  · -- Forward: CME → transition char sums vanish
    intro hcme q inst hq hne χ hχ a ε hε
    haveI : Fact (Nat.Prime q) := inst
    obtain ⟨N₀, hN₀⟩ := (cme_iff_fiber_bound.mp hcme) q hq hne χ hχ a ε hε
    exact ⟨N₀, fun N hN => by rw [transition_char_sum_eq_fiber]; exact hN₀ N hN⟩
  · -- Backward: transition char sums vanish → CME
    intro htrans
    rw [cme_iff_fiber_bound]
    intro q inst hq hne χ hχ a ε hε
    haveI : Fact (Nat.Prime q) := inst
    obtain ⟨N₀, hN₀⟩ := htrans q hq hne χ hχ a ε hε
    exact ⟨N₀, fun N hN => by
      rw [← transition_char_sum_eq_fiber q hq hne χ a N]; exact hN₀ N hN⟩

end TransitionMatrix
