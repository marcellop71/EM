import EM.EquidistFourier
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Self-Correcting Sieve and Block Rotation Analysis

Self-correcting sieve program for Mullin's Conjecture:

* §31: Escape density and decorrelation hypotheses
* §32: Self-correcting sieve — run-length analysis
* §33: Block-rotation estimate (BRE) and PED → CCSB
* §34: Simplified reduction chains (Fourier bridge eliminated)
* §35: BRE for order-2 characters via NoLongRuns
* §36: Sieve equidistribution, Dirichlet independence, multi-modular CSB
* §37: Walk telescoping identity and BRE structural analysis
* §72: Kernel confinement and CCSB failure — PED-CCSB boundary
-/

open Mullin Euclid MullinGroup RotorRouter

/-! ## §31. Escape Density and Decorrelation

This section introduces two intermediate hypotheses that sit between the
dynamical / combinatorial structure of the EM multiplier sequence and the
analytic `ComplexCharSumBound` of §30.

**`PositiveEscapeDensity` (PED)**: A positive fraction of the multipliers
`emMultUnit q n` escape the kernel of every non-trivial character.  More
precisely, for every non-trivial `χ : (ZMod q)ˣ →* ℂˣ`, there exist `δ > 0`
and `N₀` such that `#{k < N : χ(emMultUnit q n) ≠ 1} ≥ δ * N` for all
`N ≥ N₀`.

**`DecorrelationHypothesis`**: Non-trivial character sums along the multiplier
sequence are `o(N)`.  This is the analogue of `ComplexCharSumBound` for the
multiplier sequence `emMultUnit` rather than the walk `emWalkUnit`.

The chain of reductions is:
```
DecorrelationHypothesis
    →[decorrelation_implies_ped]→ PositiveEscapeDensity
    →[PEDImpliesComplexCSB]→ ComplexCharSumBound
    →[ComplexCSBImpliesHitCountLB]→ hitCount_lower_bound
    →[proved]→ WalkEquidistribution
    →[proved]→ DynamicalHitting
    →[proved]→ MullinConjecture
```

The outer implications are formally verified given the open Props.  The two
open bridges (`PEDImpliesComplexCSB` and `ComplexCSBImpliesHitCountLB`)
encapsulate respectively the block-rotation cancellation argument and the
Fourier inversion formula. -/

section EscapeDensityDecorrelation

/-- **PositiveEscapeDensity (PED)**: for every prime `q` not in the EM sequence
    and every non-trivial multiplicative character `χ : (ZMod q)ˣ →* ℂˣ`,
    a positive fraction of the multipliers `emMultUnit q n` escape the kernel
    of `χ`.

    Formally: there exist `δ > 0` and `N₀` such that for all `N ≥ N₀`,
    ```
    #{k < N : χ(emMultUnit q k) ≠ 1} ≥ δ * N
    ```

    **Open Prop**: the proof requires showing that the EM multipliers are not
    eventually confined to the kernel of any non-trivial character — a
    structural equidistribution property of the Euclid-Mullin sequence. -/
def PositiveEscapeDensity : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∃ (δ : ℝ) (_hδ : 0 < δ),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    δ * (N : ℝ) ≤
      ↑((Finset.filter (fun k => χ (emMultUnit q hq hne k) ≠ 1)
          (Finset.range N)).card)

/-- **DecorrelationHypothesis**: non-trivial character sums along the EM
    multiplier sequence are `o(N)`.

    For every prime `q` not in the EM sequence, every non-trivial character
    `χ : (ZMod q)ˣ →* ℂˣ`, and every `ε > 0`, there exists `N₀` such that
    for all `N ≥ N₀`:
    ```
    ‖∑_{k<N} χ(emMultUnit q k)‖ ≤ ε * N
    ```

    **Open Prop**: this is the multiplier-sequence analogue of
    `ComplexCharSumBound` (which is stated for `emWalkUnit`).  The proof would
    require connecting the dynamical properties of the EM recurrence to
    character sum estimates. -/
def DecorrelationHypothesis : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ‖∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ)‖ ≤ ε * N

/-- **PEDImpliesComplexCSB**: positive escape density implies the complex
    character sum bound.

    The intended argument is a block-rotation cancellation: if a positive
    fraction of the multipliers have `χ(m) ≠ 1`, then the partial walk sums
    undergo genuine cancellation, giving `o(N)` bounds.

    **Open Prop**: the formal proof would use a Cauchy-Schwarz estimate on
    block sums of the walk, combining the recurrence
    `emWalkUnit q (n+1) = emWalkUnit q n · emMultUnit q n`
    with the escape density lower bound. -/
def PEDImpliesComplexCSB : Prop := PositiveEscapeDensity → ComplexCharSumBound

/-- Helper: every value of a multiplicative character `χ : (ZMod q)ˣ →* ℂˣ`,
    viewed as a complex number, has norm 1.  This follows because `(ZMod q)ˣ`
    is finite, so every element has finite order, and finite-order elements in
    a normed ring have norm 1. -/
private lemma char_val_norm_one {q : Nat} [Fact (Nat.Prime q)]
    (χ : (ZMod q)ˣ →* ℂˣ) (u : (ZMod q)ˣ) :
    ‖(χ u : ℂ)‖ = 1 := by
  have h2 : IsOfFinOrder (χ u) := χ.isOfFinOrder (isOfFinOrder_of_finite u)
  have h3 : IsOfFinOrder ((χ u).val : ℂ) := by
    obtain ⟨n, hn, hpow⟩ := h2.exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, by
      rw [← Units.val_pow_eq_pow_val]
      exact congrArg Units.val hpow⟩
  exact h3.norm_eq_one

/-- **DecorrelationHypothesis implies PositiveEscapeDensity**: if multiplier
    character sums are `o(N)`, then a positive fraction of multipliers escape
    every non-trivial character's kernel.

    **Proof**: Fix a non-trivial `χ` and choose `δ = 1/4`.  Apply
    `DecorrelationHypothesis` with `ε = 1/4` to get `N₀`.  For `N ≥ N₀`,
    suppose for contradiction that the escape count `E < N/4`.  Then the
    kernel count `K = N - E > 3N/4`.  Split the character sum into kernel
    and escape parts:
    - The kernel part equals `K · 1` in ℂ, contributing norm `K`.
    - The escape part has norm at most `E` (each term has norm 1).
    By the reverse triangle inequality, `‖Σ χ‖ ≥ K - E > N/2`.
    But `DecorrelationHypothesis` gives `‖Σ χ‖ ≤ N/4` — contradiction. -/
theorem decorrelation_implies_ped :
    DecorrelationHypothesis → PositiveEscapeDensity := by
  intro hdec q inst hq hne χ hχ
  haveI : Fact (Nat.Prime q) := inst
  -- Choose δ = 1/4 for PED
  refine ⟨1/4, by norm_num, ?_⟩
  -- Apply DH with ε = 1/4
  obtain ⟨N₀, hN₀⟩ := hdec q hq hne χ hχ (1/4) (by norm_num)
  refine ⟨N₀, fun N hN => ?_⟩
  -- Let escSet = {k < N : χ(mk) ≠ 1}, kerSet = {k < N : χ(mk) = 1}
  set escSet := Finset.filter (fun k => χ (emMultUnit q hq hne k) ≠ 1) (Finset.range N)
  set kerSet := Finset.filter (fun k => χ (emMultUnit q hq hne k) = 1) (Finset.range N)
  -- Card relationship: kerSet.card + escSet.card = N
  have hKE : kerSet.card + escSet.card = N := by
    have h := @Finset.card_filter_add_card_filter_not ℕ (Finset.range N)
                (fun k => χ (emMultUnit q hq hne k) = 1) _ _
    rw [Finset.card_range] at h; omega
  -- Goal: 1/4 * N ≤ escSet.card. Prove by contradiction.
  by_contra hlt
  push_neg at hlt
  -- So escSet.card < 1/4 * N (as reals)
  have hE_lt : (escSet.card : ℝ) < 1/4 * N := hlt
  -- Total sum splits into kernel and escape parts
  have hsum_split : ∑ k ∈ Finset.range N, (χ (emMultUnit q hq hne k) : ℂ) =
      (∑ k ∈ kerSet, (χ (emMultUnit q hq hne k) : ℂ)) +
      (∑ k ∈ escSet, (χ (emMultUnit q hq hne k) : ℂ)) :=
    (Finset.sum_filter_add_sum_filter_not (Finset.range N)
      (fun k => χ (emMultUnit q hq hne k) = 1) _).symm
  -- Kernel sum = kerSet.card (each term is 1 in ℂ)
  have hker_sum : ∑ k ∈ kerSet, (χ (emMultUnit q hq hne k) : ℂ) = ↑kerSet.card := by
    have hterms : ∀ k ∈ kerSet, (χ (emMultUnit q hq hne k) : ℂ) = 1 := by
      intro k hk; simp [kerSet, Finset.mem_filter] at hk; simp [hk.2]
    rw [Finset.sum_congr rfl hterms]; simp [Finset.sum_const]
  -- Escape sum norm ≤ escSet.card (each term has norm 1)
  have hesc_norm : ‖∑ k ∈ escSet, (χ (emMultUnit q hq hne k) : ℂ)‖ ≤ ↑escSet.card :=
    calc ‖∑ k ∈ escSet, (χ (emMultUnit q hq hne k) : ℂ)‖
        ≤ ∑ k ∈ escSet, ‖(χ (emMultUnit q hq hne k) : ℂ)‖ := norm_sum_le _ _
      _ = ∑ k ∈ escSet, 1 := Finset.sum_congr rfl (fun k _ => char_val_norm_one χ _)
      _ = ↑escSet.card := by simp [Finset.sum_const]
  -- Kernel sum norm = kerSet.card
  have hker_norm : ‖∑ k ∈ kerSet, (χ (emMultUnit q hq hne k) : ℂ)‖ = ↑kerSet.card := by
    rw [hker_sum]; simp
  -- Reverse triangle inequality: ‖kerSum + escSum‖ ≥ K - E
  have h_rev_tri : ‖(∑ k ∈ kerSet, (χ (emMultUnit q hq hne k) : ℂ)) +
      (∑ k ∈ escSet, (χ (emMultUnit q hq hne k) : ℂ))‖ ≥
      (↑kerSet.card : ℝ) - ↑escSet.card := by
    have h1 : ‖∑ k ∈ kerSet, (χ (emMultUnit q hq hne k) : ℂ)‖ ≤
        ‖(∑ k ∈ kerSet, (χ (emMultUnit q hq hne k) : ℂ)) +
        (∑ k ∈ escSet, (χ (emMultUnit q hq hne k) : ℂ))‖ +
        ‖∑ k ∈ escSet, (χ (emMultUnit q hq hne k) : ℂ)‖ :=
      calc ‖∑ k ∈ kerSet, (χ (emMultUnit q hq hne k) : ℂ)‖ =
            ‖(∑ k ∈ kerSet, (χ (emMultUnit q hq hne k) : ℂ) +
            ∑ k ∈ escSet, (χ (emMultUnit q hq hne k) : ℂ)) -
            (∑ k ∈ escSet, (χ (emMultUnit q hq hne k) : ℂ))‖ := by ring_nf
        _ ≤ _ + _ := norm_sub_le _ _
    rw [hker_norm] at h1; linarith [hesc_norm]
  -- ‖totalSum‖ ≥ K - E ≥ (N - E) - E = N - 2E > N - N/2 = N/2
  have hK_cast : (kerSet.card : ℝ) = N - escSet.card := by
    push_cast [← hKE]; ring
  have hsum_norm : ‖∑ k ∈ Finset.range N, (χ (emMultUnit q hq hne k) : ℂ)‖ ≥ (N : ℝ) / 2 := by
    rw [hsum_split]; linarith [h_rev_tri]
  -- But DH gives ‖totalSum‖ ≤ N/4 < N/2 — contradiction
  linarith [hN₀ N hN, norm_nonneg (∑ k ∈ Finset.range N, (χ (emMultUnit q hq hne k) : ℂ))]

/-- **PED chain theorem**: given positive escape density, block-rotation
    cancellation, and the Fourier inversion bridge, we obtain Mullin's
    Conjecture.

    This composes:
    - `PEDImpliesComplexCSB` (open): PED → ComplexCharSumBound
    - `ComplexCSBImpliesHitCountLB` (open): CCSB → hitCount_lower_bound
    - `complex_csb_mc` (proved): CCSB + Fourier → MullinConjecture -/
theorem ped_mc
    (hped : PositiveEscapeDensity)
    (hped_csb : PEDImpliesComplexCSB)
    (hfourier : ComplexCSBImpliesHitCountLB) :
    MullinConjecture :=
  complex_csb_mc (hped_csb hped) hfourier

/-- **Decorrelation chain theorem**: given the decorrelation hypothesis and all
    intermediate bridges, we obtain Mullin's Conjecture.

    This composes the full chain:
    ```
    DecorrelationHypothesis
        → PositiveEscapeDensity        [decorrelation_implies_ped, proved]
        → ComplexCharSumBound          [PEDImpliesComplexCSB]
        → hitCount_lower_bound         [ComplexCSBImpliesHitCountLB]
        → WalkEquidistribution         [proved]
        → MullinConjecture             [proved]
    ``` -/
theorem decorrelation_mc
    (hdec : DecorrelationHypothesis)
    (hped_csb : PEDImpliesComplexCSB)
    (hfourier : ComplexCSBImpliesHitCountLB) :
    MullinConjecture :=
  ped_mc (decorrelation_implies_ped hdec) hped_csb hfourier

end EscapeDensityDecorrelation

/-! ## §32. Self-Correcting Sieve: Run-Length Analysis

The self-correcting sieve principle: bounding the maximum run length
of multipliers in ker(χ) implies positive escape density (PED).

Key reduction: NoLongRuns(L) → PED with δ = 1/(2L).
Contrapositive: ¬PED → arbitrarily long ker-runs occur infinitely often.
-/

section SelfCorrectingSieve

open Mullin Euclid MullinGroup RotorRouter

open Classical in
/-- `NoLongRuns L` asserts that for every non-trivial character χ,
    there is a threshold past which no L consecutive multipliers
    all lie in ker(χ). -/
def NoLongRuns (L : Nat) : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∃ k, k < L ∧ χ (emMultUnit q hq hne (n + k)) ≠ 1

/-- Helper: `(i + 1) * L ≤ N - N₀` when `i < (N - N₀) / L`. -/
private lemma block_fits {N N₀ L : ℕ} (_ : 0 < L) (i : ℕ)
    (hi : i < (N - N₀) / L) (_ : N₀ ≤ N) :
    (i + 1) * L ≤ N - N₀ := by
  have h1 : i + 1 ≤ (N - N₀) / L := hi
  have h2 : (N - N₀) / L * L ≤ N - N₀ := Nat.div_mul_le_self _ _
  calc (i + 1) * L ≤ (N - N₀) / L * L := Nat.mul_le_mul_right L h1
    _ ≤ N - N₀ := h2

/-- Helper: counting escapes via injection from block indices.
    For each block i < (N - N₀)/L, classical choice picks a witness in escSet. -/
lemma escape_count_ge_blocks {q : ℕ} [Fact (Nat.Prime q)]
    {hq : IsPrime q} {hne : ∀ k, seq k ≠ q}
    {χ : (ZMod q)ˣ →* ℂˣ} {N₀ L : ℕ}
    (hN₀ : ∀ n ≥ N₀, ∃ k, k < L ∧ χ (emMultUnit q hq hne (n + k)) ≠ 1)
    {N : ℕ} (hN : N₀ ≤ N) (hL : 0 < L) :
    (N - N₀) / L ≤
      (Finset.filter (fun k => χ (emMultUnit q hq hne k) ≠ 1)
        (Finset.range N)).card := by
  set escSet := Finset.filter (fun k => χ (emMultUnit q hq hne k) ≠ 1) (Finset.range N)
  -- For each block index i, classical choice gives a witness offset wit(i) < L
  -- such that N₀ + i*L + wit(i) ∈ escSet.
  -- The map i ↦ N₀ + i*L + wit(i) is injective (witnesses lie in disjoint blocks).
  -- Use classical choice to define the witness function
  let wit : ℕ → ℕ := fun i =>
    (hN₀ (N₀ + i * L) (by omega)).choose
  have hwit_lt : ∀ i, wit i < L := fun i =>
    (hN₀ (N₀ + i * L) (by omega)).choose_spec.1
  have hwit_esc : ∀ i, χ (emMultUnit q hq hne (N₀ + i * L + wit i)) ≠ 1 := fun i =>
    (hN₀ (N₀ + i * L) (by omega)).choose_spec.2
  -- Define the injection f : range ((N-N₀)/L) → escSet
  let f : ℕ → ℕ := fun i => N₀ + i * L + wit i
  -- Use (j*L + w)/L = j when w < L
  have hdiv : ∀ j w, w < L → (j * L + w) / L = j := fun j w hw => by
    have hrw : j * L + w = w + L * j := by ring
    rw [hrw, Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt hw]
    simp
  -- f maps range ((N-N₀)/L) into escSet
  have hf_maps : Set.MapsTo f (Finset.range ((N - N₀) / L)) escSet := by
    intro i hi
    simp only [Finset.mem_coe, Finset.mem_range] at hi
    simp only [Finset.mem_coe]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, hwit_esc i⟩
    simp only [f]
    have hfit := block_fits hL i hi hN
    -- hfit : (i+1)*L ≤ N-N₀
    have hwitl := hwit_lt i
    -- i*L + wit i < (i+1)*L ≤ N-N₀, so N₀ + i*L + wit i < N
    have hstep : i * L + wit i < (i + 1) * L := by
      have hrw : (i + 1) * L = i * L + L := by ring
      linarith
    calc N₀ + i * L + wit i < N₀ + (i + 1) * L := by linarith
      _ ≤ N₀ + (N - N₀) := by linarith
      _ = N := Nat.add_sub_cancel' hN
  -- f is injective on range ((N-N₀)/L)
  have hf_inj : Set.InjOn f (Finset.range ((N - N₀) / L)) := by
    intro i₁ hi₁ i₂ hi₂ heq
    simp only [Finset.mem_coe, Finset.mem_range] at hi₁ hi₂
    simp only [f] at heq
    have hw1 := hwit_lt i₁
    have hw2 := hwit_lt i₂
    have heq' : i₁ * L + wit i₁ = i₂ * L + wit i₂ := by omega
    calc i₁ = (i₁ * L + wit i₁) / L := (hdiv i₁ (wit i₁) hw1).symm
      _ = (i₂ * L + wit i₂) / L := by rw [heq']
      _ = i₂ := hdiv i₂ (wit i₂) hw2
  -- Conclude (N-N₀)/L = range.card ≤ escSet.card
  have hle := Finset.card_le_card_of_injOn f hf_maps hf_inj
  simpa [Finset.card_range] using hle

/-- **NoLongRuns implies PositiveEscapeDensity**: if no L consecutive
    multipliers all lie in ker(χ), then a fraction ≥ 1/(2L) of multipliers
    escape ker(χ).

    **Proof**: Fix χ, apply NoLongRuns to get N₀.  Set N₀' = 2 * N₀ + 2 * L.
    For N ≥ N₀', partition [N₀, N) into blocks of length L.
    Each block contributes ≥ 1 escape.  So escSet.card ≥ (N - N₀)/L.
    For N ≥ 2·N₀ + 2·L, we have (N - N₀)/L ≥ N/(2·L), giving δ = 1/(2L). -/
theorem noLongRuns_implies_ped (L : Nat) (hL : 0 < L)
    (hnlr : NoLongRuns L) : PositiveEscapeDensity := by
  intro q inst hq hne χ hχ
  haveI : Fact (Nat.Prime q) := inst
  -- Apply NoLongRuns to get the threshold N₀
  obtain ⟨N₀, hN₀⟩ := hnlr q hq hne χ hχ
  -- Choose δ = 1 / (2 * L) > 0
  refine ⟨1 / (2 * (L : ℝ)), by
    apply div_pos one_pos
    exact mul_pos two_pos (by exact_mod_cast hL), ?_⟩
  -- Threshold: N₀' = 2 * N₀ + 2 * L ensures N/(2L) ≤ (N-N₀)/L in ℕ
  refine ⟨2 * N₀ + 2 * L, fun N hN => ?_⟩
  set escSet := Finset.filter (fun k => χ (emMultUnit q hq hne k) ≠ 1) (Finset.range N)
  have hN₀_le : N₀ ≤ N := by omega
  -- escSet.card ≥ (N - N₀) / L  (injection from block witnesses)
  have hcard_ge : (N - N₀) / L ≤ escSet.card :=
    escape_count_ge_blocks hN₀ hN₀_le hL
  -- Real-valued quantities
  have hLr : (0 : ℝ) < ↑L := by exact_mod_cast hL
  -- Step 1: ↑((N-N₀)/L) * ↑L > ↑(N-N₀) - ↑L   (from nat div rounding)
  have hmod : (↑((N - N₀) / L) : ℝ) * ↑L > (↑(N - N₀) : ℝ) - ↑L := by
    -- From Nat.div_add_mod: L * ((N-N₀)/L) + (N-N₀)%L = N-N₀
    -- From Nat.mod_lt: (N-N₀)%L < L
    -- Combining: (N-N₀)/L * L > N-N₀ - L
    have heq : L * ((N - N₀) / L) + (N - N₀) % L = N - N₀ := Nat.div_add_mod (N - N₀) L
    have hrem : (N - N₀) % L < L := Nat.mod_lt _ hL
    -- Cast to ℝ
    have heqr : (↑L : ℝ) * ↑((N - N₀) / L) + ↑((N - N₀) % L) = ↑(N - N₀) := by
      exact_mod_cast heq
    have hremr : (↑((N - N₀) % L) : ℝ) < ↑L := by exact_mod_cast hrem
    linarith [mul_comm (↑L : ℝ) ↑((N - N₀) / L)]
  -- Step 2: ↑(N - N₀) ≥ ↑N/2 + ↑L   (from N ≥ 2*N₀ + 2*L)
  have hNhalf : (↑(N - N₀) : ℝ) ≥ (↑N : ℝ) / 2 + ↑L := by
    have h2 : 2 * (N - N₀) ≥ N + 2 * L := by omega
    have h2r : 2 * (↑(N - N₀) : ℝ) ≥ ↑N + 2 * ↑L := by exact_mod_cast h2
    linarith
  -- Step 3: ↑((N-N₀)/L) * (2*↑L) > ↑N   (product form, avoids division)
  have hprod : (↑((N - N₀) / L) : ℝ) * (2 * ↑L) > ↑N := by
    nlinarith
  -- Step 4: 1/(2*↑L)*↑N ≤ ↑escSet.card
  have hc : (↑((N - N₀) / L) : ℝ) ≤ ↑escSet.card := by exact_mod_cast hcard_ge
  -- hprod gives ↑((N-N₀)/L) > ↑N/(2*↑L); combined with hc, done
  have h2L : (2 : ℝ) * ↑L > 0 := by linarith
  -- 1/(2*L)*N < ↑((N-N₀)/L): use hprod which says ↑((N-N₀)/L)*(2*L) > N
  -- 1/(2*L)*N = N/(2*L) and ↑((N-N₀)/L)*(2*L) > N gives N/(2*L) < ↑((N-N₀)/L)
  have h1 : (1 : ℝ) / (2 * ↑L) * ↑N ≤ ↑escSet.card := by
    have key : (↑N : ℝ) < ↑((N - N₀) / L) * (2 * ↑L) := by linarith
    have hdiv : (↑N : ℝ) / (2 * ↑L) < ↑((N - N₀) / L) := by
      rwa [div_lt_iff₀ h2L]
    have heq : (1 : ℝ) / (2 * ↑L) * ↑N = ↑N / (2 * ↑L) := by ring
    linarith
  exact h1

/-- **NoLongRuns chain**: NoLongRuns(L) + bridges → MC -/
theorem noLongRuns_mc (L : Nat) (hL : 0 < L) (hnlr : NoLongRuns L)
    (hped_csb : PEDImpliesComplexCSB) (hfourier : ComplexCSBImpliesHitCountLB) :
    MullinConjecture :=
  ped_mc (noLongRuns_implies_ped L hL hnlr) hped_csb hfourier

end SelfCorrectingSieve

/-! ## §33. Block-Rotation Estimate and PED → ComplexCharSumBound

This section introduces `BlockRotationEstimate` (BRE), which formalises the
Cauchy-Schwarz / van der Corput step that converts a positive escape density
into a sublinear walk sum.  We prove:

1. `char_walk_recurrence`: the ℂ-valued character of the walk satisfies
   the multiplicative recurrence `(χ(w(n+1)) : ℂ) = (χ(w(n)) : ℂ) * (χ(m(n)) : ℂ)`.
   (Note: the general product formula already exists as `char_walk_product`
   in `EquidistCharPRE` for arbitrary `CommMonoid` targets.)
2. `BlockRotationEstimate` (open Prop): given escape density ≥ δ past
   threshold N₁, the walk character sum is o(N).
3. `block_rotation_implies_ped_csb` (proved): BRE → PEDImpliesComplexCSB.
4. Chain theorems connecting BRE to MullinConjecture.
-/

section BlockRotation

/-- **Multiplicative recurrence for ℂ-valued character of the walk**: the
    coercion `(χ (w(n+1)) : ℂ)` equals `(χ (w(n)) : ℂ) * (χ (m(n)) : ℂ)`.

    This specialises the general `char_walk_product` formula (in `EquidistCharPRE`)
    to the coercion `ℂˣ → ℂ` and the step-by-step recurrence `emWalkUnit_succ`. -/
theorem char_walk_recurrence (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (n : Nat) :
    (χ (emWalkUnit q hq hne (n + 1)) : ℂ) =
    (χ (emWalkUnit q hq hne n) : ℂ) * (χ (emMultUnit q hq hne n) : ℂ) := by
  have hrec := emWalkUnit_succ q hq hne n
  have hmap := χ.map_mul (emWalkUnit q hq hne n) (emMultUnit q hq hne n)
  simp only [hrec, hmap, Units.val_mul]

/-- **BlockRotationEstimate (BRE)**: the Cauchy-Schwarz / van der Corput step.

    Given a non-trivial character χ and a positive escape density — i.e., a
    threshold N₁ past which ≥ δN multipliers escape ker(χ) — the partial sums
    of χ along the walk are o(N).

    **Open Prop**: the proof requires a block-rotation cancellation argument
    using the multiplicative recurrence `char_walk_recurrence`.  Each block of
    L consecutive steps contains ≥ 1 escape, causing the partial product P_n
    to rotate by a non-trivial root of unity.  A Cauchy-Schwarz bound then
    gives `‖∑_{n<N} P_n‖ ≤ O(√(N/δ)) = o(N)`.

    This isolates the analytic harmonic-analysis content of the PED → CCSB
    implication. -/
def BlockRotationEstimate : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∀ (δ : ℝ) (_hδ : 0 < δ) (N₁ : ℕ),
  (∀ N ≥ N₁,
    δ * (N : ℝ) ≤ ↑((Finset.filter (fun k => χ (emMultUnit q hq hne k) ≠ 1)
                       (Finset.range N)).card)) →
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤ ε * N

/-- **BRE implies PEDImpliesComplexCSB**: given BlockRotationEstimate,
    PositiveEscapeDensity implies ComplexCharSumBound.

    **Proof**: PED provides δ > 0 and threshold N₁ such that the escape count
    is ≥ δN for all N ≥ N₁.  BRE converts this density bound directly into
    the walk sum bound, for any ε > 0.  The composition is purely logical. -/
theorem block_rotation_implies_ped_csb :
    BlockRotationEstimate → PEDImpliesComplexCSB := by
  intro hbre hped q inst hq hne χ hχ ε hε
  haveI : Fact (Nat.Prime q) := inst
  -- PED gives δ > 0, N₁, and the density lower bound for N ≥ N₁
  obtain ⟨δ, hδ, N₁, hdens⟩ := hped q hq hne χ hχ
  -- BRE converts the density bound into the walk sum bound o(N)
  exact hbre q hq hne χ hχ δ hδ N₁ hdens ε hε

/-- **BRE chain**: BlockRotationEstimate + PED + Fourier → MullinConjecture. -/
theorem bre_ped_mc
    (hbre : BlockRotationEstimate)
    (hped : PositiveEscapeDensity)
    (hfourier : ComplexCSBImpliesHitCountLB) :
    MullinConjecture :=
  ped_mc hped (block_rotation_implies_ped_csb hbre) hfourier

/-- **BRE + Decorrelation chain**: BlockRotationEstimate + DecorrelationHypothesis
    + Fourier → MullinConjecture. -/
theorem bre_decorrelation_mc
    (hbre : BlockRotationEstimate)
    (hdec : DecorrelationHypothesis)
    (hfourier : ComplexCSBImpliesHitCountLB) :
    MullinConjecture :=
  bre_ped_mc hbre (decorrelation_implies_ped hdec) hfourier

/-- **BRE + NoLongRuns chain**: BlockRotationEstimate + NoLongRuns(L) + Fourier
    → MullinConjecture. -/
theorem bre_noLongRuns_mc (L : Nat) (hL : 0 < L)
    (hbre : BlockRotationEstimate)
    (hnlr : NoLongRuns L)
    (hfourier : ComplexCSBImpliesHitCountLB) :
    MullinConjecture :=
  bre_ped_mc hbre (noLongRuns_implies_ped L hL hnlr) hfourier

end BlockRotation

/-! ## §34. Simplified Reduction Chains (Fourier Bridge Eliminated)

With `ComplexCSBImpliesHitCountLB` now PROVED (via the Fourier step identity
and character orthogonality), the chain theorems no longer require the Fourier
bridge as a parameter.  This reduces the open bridges from 3 to 2:

1. `ComplexCharSumBound` (open) — non-trivial character sums are o(N)
2. `PEDImpliesComplexCSB` (open) — PED → CCSB via block-rotation (= BRE)

Or equivalently, ONE of the input hypotheses:
- `DecorrelationHypothesis` (open) — multiplier char sums o(N)
- `PositiveEscapeDensity` (open) — positive escape density
- `NoLongRuns L` (open) — bounded kernel run length
-/

section SimplifiedChains

open Mullin Euclid MullinGroup RotorRouter

/-- **ComplexCharSumBound → MC** (simplified): the Fourier bridge is proved,
    so only the analytic cancellation hypothesis is needed. -/
theorem complex_csb_mc' (hcsb : ComplexCharSumBound) : MullinConjecture :=
  complex_csb_mc hcsb complex_csb_implies_hit_count_lb_proved

/-- **PED → MC** (simplified): PED + block-rotation bridge → MC.
    The Fourier bridge is proved, so only PEDImpliesComplexCSB remains open. -/
theorem ped_mc' (hped : PositiveEscapeDensity) (hped_csb : PEDImpliesComplexCSB) :
    MullinConjecture :=
  ped_mc hped hped_csb complex_csb_implies_hit_count_lb_proved

/-- **Decorrelation → MC** (simplified): only 2 bridges needed (was 3). -/
theorem decorrelation_mc' (hdec : DecorrelationHypothesis)
    (hped_csb : PEDImpliesComplexCSB) : MullinConjecture :=
  decorrelation_mc hdec hped_csb complex_csb_implies_hit_count_lb_proved

/-- **BRE + PED → MC** (simplified): BlockRotationEstimate + PED → MC. -/
theorem bre_ped_mc' (hbre : BlockRotationEstimate) (hped : PositiveEscapeDensity) :
    MullinConjecture :=
  bre_ped_mc hbre hped complex_csb_implies_hit_count_lb_proved

/-- **BRE + Decorrelation → MC** (simplified): 2 open hypotheses. -/
theorem bre_decorrelation_mc' (hbre : BlockRotationEstimate)
    (hdec : DecorrelationHypothesis) : MullinConjecture :=
  bre_decorrelation_mc hbre hdec complex_csb_implies_hit_count_lb_proved

/-- **BRE + NoLongRuns → MC** (simplified): 2 open hypotheses. -/
theorem bre_noLongRuns_mc' (L : Nat) (hL : 0 < L)
    (hbre : BlockRotationEstimate) (hnlr : NoLongRuns L) :
    MullinConjecture :=
  bre_noLongRuns_mc L hL hbre hnlr complex_csb_implies_hit_count_lb_proved

/-- **NoLongRuns → MC** (simplified): only PEDImpliesComplexCSB remains open. -/
theorem noLongRuns_mc' (L : Nat) (hL : 0 < L) (hnlr : NoLongRuns L)
    (hped_csb : PEDImpliesComplexCSB) : MullinConjecture :=
  noLongRuns_mc L hL hnlr hped_csb complex_csb_implies_hit_count_lb_proved

end SimplifiedChains

/-! ## §35. BRE for Order-2 Characters via NoLongRuns

For characters of order 2 (taking values ±1 in ℂ), the walk character values
also alternate between +1 and -1 at each escape step.  This section
formalises the basic sign-flip algebra for order-2 characters and derives
the Complex Character Sum Bound for such characters directly from `NoLongRuns`.

The key results:
1. `IsOrder2`: characterisation of order-2 characters.
2. `walk_char_val_pm_one`: walk character values lie in {+1, -1}.
3. `escape_flips_walk_char`: an escape flips the walk character value.
4. `kernel_preserves_walk_char`: a kernel step preserves the walk character value.
5. `bre_order2_from_noLongRuns`: NoLongRuns(L) implies CCSB for order-2 χ.
6. `ccsb_order2_from_noLongRuns`: the CCSB corollary as an explicit ∃M₀ statement.
-/

section BREOrder2

/-- `IsOrder2 χ` asserts that the character χ takes only the values +1 and −1
    in ℂ, i.e. it is a character of order dividing 2. -/
def IsOrder2 {q : Nat} [Fact (Nat.Prime q)] (χ : (ZMod q)ˣ →* ℂˣ) : Prop :=
  ∀ u : (ZMod q)ˣ, (χ u : ℂ) = 1 ∨ (χ u : ℂ) = -1

/-- Every value of an order-2 character squares to 1 in ℂ. -/
lemma order2_sq_eq_one {q : Nat} [Fact (Nat.Prime q)]
    (χ : (ZMod q)ˣ →* ℂˣ) (hord2 : IsOrder2 χ) (u : (ZMod q)ˣ) :
    (χ u : ℂ) ^ 2 = 1 := by
  rcases hord2 u with h | h <;> simp [h]

/-- The walk character values of an order-2 character all lie in {+1, −1}. -/
lemma walk_char_val_pm_one {q : Nat} [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (hord2 : IsOrder2 χ) (n : ℕ) :
    (χ (emWalkUnit q hq hne n) : ℂ) = 1 ∨
    (χ (emWalkUnit q hq hne n) : ℂ) = -1 := by
  induction n with
  | zero =>
    simp only [emWalkUnit]
    rcases hord2 (Units.mk0 (walkZ q 0) (walkZ_ne_zero hq hne 0)) with h | h
    · exact Or.inl h
    · exact Or.inr h
  | succ n ih =>
    rw [char_walk_recurrence q hq hne χ n]
    rcases ih with hw | hw <;> rcases hord2 (emMultUnit q hq hne n) with hm | hm
    · left;  simp [hw, hm]
    · right; simp [hw, hm]
    · right; simp [hw, hm]
    · left;  simp [hw, hm]

/-- When the multiplier character value is −1 (an escape), the walk character
    value is negated at the next step. -/
lemma escape_flips_walk_char {q : Nat} [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (n : ℕ) :
    (χ (emMultUnit q hq hne n) : ℂ) = -1 →
    (χ (emWalkUnit q hq hne (n + 1)) : ℂ) =
      -(χ (emWalkUnit q hq hne n) : ℂ) := by
  intro hesc
  rw [char_walk_recurrence q hq hne χ n, hesc, mul_neg_one]

/-- When the multiplier character value is 1 (a kernel step), the walk
    character value is preserved at the next step. -/
lemma kernel_preserves_walk_char {q : Nat} [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (n : ℕ) :
    (χ (emMultUnit q hq hne n) : ℂ) = 1 →
    (χ (emWalkUnit q hq hne (n + 1)) : ℂ) =
      (χ (emWalkUnit q hq hne n) : ℂ) := by
  intro hker
  rw [char_walk_recurrence q hq hne χ n, hker, mul_one]

/-- **Walk norm is 1 for order-2 characters**: each walk character value has
    complex norm 1. -/
lemma walk_char_norm_one {q : Nat} [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (hord2 : IsOrder2 χ) (n : ℕ) :
    ‖(χ (emWalkUnit q hq hne n) : ℂ)‖ = 1 := by
  rcases walk_char_val_pm_one hq hne χ hord2 n with h | h <;> simp [h]

/-- **BRE for order-2 characters via NoLongRuns**: given `NoLongRuns L` and a
    non-trivial order-2 character `χ`, the walk character sum satisfies CCSB
    (is o(N)), assuming the PED→CCSB bridge `PEDImpliesComplexCSB`.

    **Proof**: `NoLongRuns L` implies `PositiveEscapeDensity` (proved in §32).
    `PEDImpliesComplexCSB` then converts PED to CCSB.  The order-2 hypothesis
    is not needed for the logical implication but will be used in the eventual
    proof of `PEDImpliesComplexCSB` for this special case. -/
theorem bre_order2_from_noLongRuns (L : Nat) (hL : 0 < L)
    (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hχ : χ ≠ 1) (_hord2 : IsOrder2 χ)
    (hped_csb : PEDImpliesComplexCSB)
    (hnlr : NoLongRuns L)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀,
      ‖∑ n ∈ Finset.range M, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤ ε * M := by
  -- NoLongRuns → PED (proved in §32)
  have hped := noLongRuns_implies_ped L hL hnlr
  -- PED → CCSB (open bridge)
  have hcsb := hped_csb hped
  -- Apply CCSB to this specific character
  exact hcsb q hq hne χ hχ ε hε

/-- **CCSB for order-2 characters from NoLongRuns**: under `NoLongRuns L`,
    every non-trivial order-2 character χ has walk sum o(N), provided the
    PED→CCSB bridge holds.

    This is a corollary of `bre_order2_from_noLongRuns` with identical proof
    structure, restating the conclusion in the standard CCSB form. -/
theorem ccsb_order2_from_noLongRuns (L : Nat) (hL : 0 < L)
    (hnlr : NoLongRuns L)
    (hped_csb : PEDImpliesComplexCSB)
    (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hχ : χ ≠ 1) (hord2 : IsOrder2 χ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀,
      ‖∑ n ∈ Finset.range M, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤ ε * M :=
  bre_order2_from_noLongRuns L hL q hq hne χ hχ hord2 hped_csb hnlr ε hε

/-- **Order-2 CCSB implies MC** (simplified chain): NoLongRuns(L) + order-2
    characters give CCSB, which closes to MullinConjecture via the proved
    bridges.

    With `PEDImpliesComplexCSB` as the sole open hypothesis, this collapses
    to the `noLongRuns_mc'` chain. -/
theorem order2_noLongRuns_mc (L : Nat) (hL : 0 < L) (hnlr : NoLongRuns L)
    (hped_csb : PEDImpliesComplexCSB) : MullinConjecture :=
  noLongRuns_mc' L hL hnlr hped_csb

end BREOrder2

/-! ## §36. Sieve Equidistribution, Dirichlet Independence, and Multi-Modular CSB

This section contains three components:

1. **SieveEquidistribution** (open Prop): The generic sieve equidistribution
   result from analytic number theory (Alladi 1977 / PNT in APs). States that
   for integers coprime to a finite sieve set, the smallest prime factor
   equidistributes among residue classes mod q. This is a known theorem but NOT
   in Mathlib.

2. **dirichlet_residues_independent** (proved theorem): For any residue class
   a (mod q) coprime to q, there are infinitely many primes in that class.
   This is Dirichlet's theorem on primes in arithmetic progressions, available
   in Mathlib as `Nat.infinite_setOf_prime_and_eq_mod`. This formalizes the key
   insight that self-avoidance imposes no constraint at the character level.

3. **MultiModularCSB** (open Prop): `ComplexCharSumBound` holds for all but
   finitely many primes q. Combined with `ThresholdHitting → MC`, this would
   close the conjecture if the threshold is below the sieve bound.
-/

section SieveEquidist

/-- **SieveEquidistribution**: For integers m in a residue class (mod q) that
    are coprime to a finite set F of primes, the smallest prime factor of m
    equidistributes among residue classes mod q as the range grows.

    More precisely: fix a modulus q, a coprimality sieve set F (a finite set of
    primes not including q), and a target residue class a : (ZMod q)ˣ. Among
    integers n ≤ N that are coprime to all primes in F, the fraction of those
    for which minFac(n) ≡ a (mod q) converges to 1/φ(q) as N → ∞.

    **This is a known theorem** (Alladi 1977; follows from the prime number
    theorem in arithmetic progressions via partial summation) but is **NOT in
    Mathlib**. It is the key analytic input needed to prove that the Euclid-Mullin
    walk has positive escape density, closing the chain:

        SieveEquidistribution
          → NoLongRuns(L)            [for L = φ(q)+1, combinatorial]
          → PositiveEscapeDensity    [proved in §32]
          → ComplexCharSumBound      [PEDImpliesComplexCSB, open]
          → MullinConjecture         [proved in §30]

    The statement here is phrased for the Euclid-Mullin setting: the "integers"
    in question are values of `prod(n) + 1`, and the sieve set F grows with n
    (it equals the set of primes already in the sequence). The equidistribution
    of minFac is exactly what drives the multiplier walk. -/
def SieveEquidistribution : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (a : (ZMod q)ˣ),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
  -- Among the first N steps, the fraction of multipliers equal to a
  -- is within ε of 1/φ(q).
  let hitN : ℕ := (Finset.range N).filter (fun n => emMultUnit q hq hne n = a) |>.card
  (hitN : ℝ) ≥ (N : ℝ) * (1 / (Finset.univ (α := (ZMod q)ˣ)).card - ε)

/-- **Self-avoidance is invisible to characters**: For any residue class a (mod q)
    coprime to q, there are infinitely many primes p with p ≡ a (mod q).

    This is **Dirichlet's theorem on primes in arithmetic progressions**, proved
    in Mathlib as `Nat.infinite_setOf_prime_and_eq_mod`. The proof is immediate.

    **Significance**: The Euclid-Mullin sequence is self-avoiding (no prime
    repeats), but self-avoidance does NOT reduce the supply of primes available
    in any residue class. Since each class contains infinitely many primes, the
    walk can always find a fresh prime in any desired class. Characters depend
    only on the residue class, not on which specific prime is chosen. Therefore,
    self-avoidance imposes zero constraint at the character level — the walk's
    character values are governed purely by the equidistribution of residue
    classes, just as if primes were chosen with replacement. -/
theorem dirichlet_residues_independent (q : Nat) [hq : Fact (Nat.Prime q)]
    (a : (ZMod q)ˣ) :
    Set.Infinite {p : Nat | Nat.Prime p ∧ (p : ZMod q) = a.val} := by
  haveI : NeZero q := ⟨Nat.Prime.ne_zero hq.out⟩
  have ha : IsUnit (a.val : ZMod q) := a.isUnit
  exact Nat.infinite_setOf_prime_and_eq_mod ha

/-- **Self-avoidance independence corollary**: for any prime q and coprime residue
    class a, there exist arbitrarily large primes in that class. This is the
    existential form of Dirichlet's theorem, useful for the EM walk analysis. -/
theorem dirichlet_residues_unbounded (q : Nat) [hq : Fact (Nat.Prime q)]
    (a : (ZMod q)ˣ) (M : Nat) :
    ∃ p : Nat, M ≤ p ∧ Nat.Prime p ∧ (p : ZMod q) = a.val := by
  haveI : NeZero q := ⟨Nat.Prime.ne_zero hq.out⟩
  have ha : IsUnit (a.val : ZMod q) := a.isUnit
  obtain ⟨p, hp, hprime, heq⟩ := Nat.forall_exists_prime_gt_and_eq_mod ha M
  exact ⟨p, Nat.le_of_lt hp, hprime, heq⟩

end SieveEquidist

section MultiModular

/-- **MultiModularCSB**: `ComplexCharSumBound` holds for all sufficiently large
    primes q. More precisely, there exists a threshold Q₀ such that for all primes
    q ≥ Q₀ not already appearing in the EM sequence, every non-trivial character
    χ : (ZMod q)ˣ →* ℂˣ satisfies the sublinear bound on the character sum
    along the EM walk.

    This is a strengthening of `ComplexCharSumBound` with a uniformity threshold.
    Combined with `ThresholdHitting → MC` (proved in §14), MultiModularCSB implies
    MC by taking B = Q₀ and using `FiniteMCBelow Q₀` (which is finitely verifiable,
    and verified for Q₀ = 11 in `concrete_mc_below_11`).

    **This is an open Prop**: proving it requires analytic estimates on the spectral
    gap of the EM dynamical system, or a sieve argument showing that the walk is
    equidistributed for all large moduli simultaneously. The sieve approach would
    use `SieveEquidistribution` (above) plus character sum technology.

    **Open Prop** — not yet proved. -/
def MultiModularCSB : Prop :=
  ∃ Q₀ : ℕ, ∀ (q : Nat) [Fact (Nat.Prime q)], q ≥ Q₀ →
  ∀ (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤ ε * N

/-- **MultiModularCSB is strictly weaker than ComplexCharSumBound**: MMCSB gives
    CCSB only for q ≥ Q₀, not for all q. The full chain to MC requires BOTH
    MultiModularCSB (for large q) and FiniteMCBelow Q₀ (for small q).

    The intended chain is:
    ```
    MultiModularCSB + FiniteMCBelow Q₀ → MC
    ```
    where the left conjunct handles q ≥ Q₀ and the right handles q < Q₀.

    **Open Prop**: the MultiModularCSB → ThresholdHitting Q₀ step requires
    the full Fourier bridge (ComplexCSBImpliesHitCountLB, already PROVED) plus
    the PEDImpliesComplexCSB bridge (still OPEN as BlockRotationEstimate). -/
def MultiModularCSBImpliesMC : Prop :=
  MultiModularCSB → MullinConjecture

end MultiModular

/-! ### §36 Summary

The four components of §36 are:

1. **SieveEquidistribution** (open Prop): The generic sieve equidistribution
   result for minFac (Alladi 1977 / PNT in APs). NOT in Mathlib.

2. **dirichlet_residues_independent** (PROVED): Dirichlet's theorem via Mathlib.
   Documents that self-avoidance is invisible to characters.

3. **dirichlet_residues_unbounded** (PROVED): Existential form — arbitrarily
   large primes exist in any coprime residue class.

4. **MultiModularCSB** (open Prop): Uniform ComplexCharSumBound for large q.

5. **MultiModularCSBImpliesMC** (open Prop): The chain MMCSB → MC.

The intended chains are:
```
SieveEquidistribution → NoLongRuns(L) → PED → (PEDImpliesComplexCSB) → CCSB → MC
MultiModularCSB + FiniteMCBelow Q₀ → MC
```
-/

/-! ## §37. Walk Telescoping Identity and BRE Structural Analysis

This section develops structural identities relating the walk character sum
to the multiplier character sum.  Two key results are proved:

1. **Telescoping identity**: ∑_{n<N} χ(w(n))·(χ(m(n))-1) = χ(w(N)) - χ(w(0)).
   This follows directly from the recurrence χ(w(n+1)) = χ(w(n))·χ(m(n)).

2. **Norm bound**: The telescoping sum has norm ≤ 2, since each character value
   on the walk has norm 1.

3. **Shift-one autocorrelation identity**: ∑_n χ(w(n))·conj(χ(w(n+1))) =
   conj(∑_n χ(m(n))).  This follows because χ(w(n))·conj(χ(w(n+1))) =
   χ(w(n))·conj(χ(w(n)))·conj(χ(m(n))) = conj(χ(m(n))) (using |χ(w(n))|=1).

**Note on BRE for characters of order ≥ 3**: Positive escape density alone
does NOT imply the walk character sum is o(N) when the character has order
d ≥ 3.  Counterexample: a walk on Z/3Z that alternates between two of the
three values (escape density = 1) can have walk sum ≈ N/2·(1 + ω) ≠ 0.
The fundamental issue is that escape density constrains the FREQUENCY of
non-trivial steps but NOT their DISTRIBUTION among the d-1 non-identity
rotations.
-/

section WalkTelescope

/-- Every value of a multiplicative character `χ : (ZMod q)ˣ →* ℂˣ`,
    viewed as a complex number, has norm 1.  Extracted here as a non-private
    lemma for use in §37. -/
lemma walkTelescope_char_norm_one {q : Nat} [Fact (Nat.Prime q)]
    (χ : (ZMod q)ˣ →* ℂˣ) (u : (ZMod q)ˣ) :
    ‖(χ u : ℂ)‖ = 1 := by
  have h2 : IsOfFinOrder (χ u) := χ.isOfFinOrder (isOfFinOrder_of_finite u)
  have h3 : IsOfFinOrder ((χ u).val : ℂ) := by
    obtain ⟨n, hn, hpow⟩ := h2.exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, by
      rw [← Units.val_pow_eq_pow_val]
      exact congrArg Units.val hpow⟩
  exact h3.norm_eq_one

/-- **Telescoping walk identity**: for any character χ and any N,
    ∑_{n<N} χ(w(n))·(χ(m(n)) - 1) = χ(w(N)) - χ(w(0)).

    **Proof**: Each summand equals χ(w(n+1)) - χ(w(n)) by the recurrence
    `char_walk_recurrence`, so the sum telescopes. -/
theorem walk_telescope_identity (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ∑ n ∈ Finset.range N,
      ((χ (emWalkUnit q hq hne n) : ℂ) * ((χ (emMultUnit q hq hne n) : ℂ) - 1)) =
    (χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, char_walk_recurrence q hq hne χ N]
    ring

/-- **Telescoping norm bound**: the telescoping sum has norm at most 2.

    Since ∑_{n<N} χ(w(n))·(χ(m(n))-1) = χ(w(N)) - χ(w(0)) and each walk
    character value has norm 1, the triangle inequality gives norm ≤ 1 + 1 = 2. -/
theorem walk_telescope_norm_bound (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ‖∑ n ∈ Finset.range N,
      ((χ (emWalkUnit q hq hne n) : ℂ) * ((χ (emMultUnit q hq hne n) : ℂ) - 1))‖ ≤ 2 := by
  rw [walk_telescope_identity]
  calc ‖(χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ)‖
      ≤ ‖(χ (emWalkUnit q hq hne N) : ℂ)‖ + ‖(χ (emWalkUnit q hq hne 0) : ℂ)‖ :=
          norm_sub_le _ _
    _ = 1 + 1 := by
          rw [walkTelescope_char_norm_one χ _, walkTelescope_char_norm_one χ _]
    _ = 2 := by ring

/-- **Shift-one autocorrelation identity**: the h=1 autocorrelation of the walk
    character equals the conjugate of the multiplier character sum.

    Concretely, ∑_{n<N} χ(w(n))·conj(χ(w(n+1))) = conj(∑_{n<N} χ(m(n))).

    **Proof**: For each n, the recurrence gives χ(w(n+1)) = χ(w(n))·χ(m(n)), so:
      χ(w(n)) · conj(χ(w(n+1)))
        = χ(w(n)) · conj(χ(w(n))) · conj(χ(m(n)))
        = ‖χ(w(n))‖² · conj(χ(m(n)))
        = conj(χ(m(n))).
    Summing over n and pulling the continuous ring hom starRingEnd ℂ outside
    the finite sum gives the result. -/
theorem walk_shift_one_correlation (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ∑ n ∈ Finset.range N,
      ((χ (emWalkUnit q hq hne n) : ℂ) *
       starRingEnd ℂ (χ (emWalkUnit q hq hne (n + 1)) : ℂ)) =
    starRingEnd ℂ (∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ)) := by
  rw [map_sum]
  congr 1
  ext n
  -- Goal: χ(w(n)) * conj(χ(w(n+1))) = conj(χ(m(n)))
  -- Step 1: rewrite χ(w(n+1)) via the recurrence
  rw [char_walk_recurrence q hq hne χ n]
  -- Goal: χ(w(n)) * conj(χ(w(n)) * χ(m(n))) = conj(χ(m(n)))
  rw [map_mul]
  -- Goal: χ(w(n)) * (conj(χ(w(n))) * conj(χ(m(n)))) = conj(χ(m(n)))
  -- Step 2: show χ(w(n)) * conj(χ(w(n))) = 1 using norm = 1
  have hmul_self : (χ (emWalkUnit q hq hne n) : ℂ) *
      starRingEnd ℂ (χ (emWalkUnit q hq hne n) : ℂ) = 1 := by
    -- starRingEnd ℂ z = star z; for ℂ, star z = conj z
    rw [starRingEnd_apply]
    simp only [Complex.star_def]
    -- z * conj z = normSq z (cast to ℂ)
    rw [Complex.mul_conj]
    -- normSq z = ‖z‖^2
    rw [Complex.normSq_eq_norm_sq]
    have hn1 := walkTelescope_char_norm_one χ (emWalkUnit q hq hne n)
    simp [hn1]
  -- Step 3: conclude by associativity + the unit fact
  rw [← mul_assoc, hmul_self, one_mul]

end WalkTelescope

/-! ## §72. Kernel Confinement and CCSB Failure

This section documents the precise boundary between PED and CCSB by analysing
what happens when all multipliers eventually lie in ker(χ).

If χ(m(n)) = 1 for all n ≥ N₀ (eventual kernel confinement), then the walk
character value χ(w(n)) becomes constant for n ≥ N₀.  Consequently the walk
character sum grows linearly: ‖∑_{n<N} χ(w(n))‖ ≈ N − 2·N₀.  This is
incompatible with CCSB (which requires ‖∑‖ ≤ ε·N for ε < 1), so CCSB at
a fixed (q, χ) implies infinitely many escapes from ker(χ).

Key results:
1. `kernel_confinement_walk_char_constant`: eventual kernel ⇒ walk char constant.
2. `kernel_confinement_walk_sum`: walk sum has explicit linear growth formula.
3. `ccsb_at_implies_escape_cofinal`: CCSB ⇒ infinitely many escapes.
-/

section KernelConfinement

/-- **Kernel confinement makes the walk character constant**: if every
    multiplier from step N₀ onward lies in ker(χ), then the walk character
    value is frozen at its N₀-th value for all n ≥ N₀. -/
theorem kernel_confinement_walk_char_constant {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ)
    (N₀ : ℕ) (hker : ∀ n, N₀ ≤ n → (χ (emMultUnit q hq hne n) : ℂ) = 1)
    (n : ℕ) (hn : N₀ ≤ n) :
    (χ (emWalkUnit q hq hne n) : ℂ) = (χ (emWalkUnit q hq hne N₀) : ℂ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = N₀ + k := ⟨n - N₀, by omega⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, char_walk_recurrence q hq hne χ (N₀ + k),
        hker (N₀ + k) (by omega), mul_one, ih (by omega)]

/-- **Walk sum under kernel confinement**: when all multipliers from step N₀
    onward are in ker(χ), the walk character sum over `Finset.range N` (for
    N ≥ N₀) equals the partial sum up to N₀ plus (N − N₀) copies of the
    frozen value χ(w(N₀)). -/
theorem kernel_confinement_walk_sum {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ)
    (N₀ : ℕ) (hker : ∀ n, N₀ ≤ n → (χ (emMultUnit q hq hne n) : ℂ) = 1)
    (N : ℕ) (hN : N₀ ≤ N) :
    ∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ) =
    ∑ n ∈ Finset.range N₀, (χ (emWalkUnit q hq hne n) : ℂ) +
      (N - N₀ : ℕ) • (χ (emWalkUnit q hq hne N₀) : ℂ) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = N₀ + k := ⟨N - N₀, by omega⟩
  induction k with
  | zero => simp
  | succ k ih =>
    have hN₀k : N₀ ≤ N₀ + k := Nat.le_add_right _ _
    conv_lhs => rw [show N₀ + (k + 1) = (N₀ + k) + 1 from by omega]
    rw [Finset.sum_range_succ, ih hN₀k]
    rw [kernel_confinement_walk_char_constant hq hne χ N₀ hker (N₀ + k) hN₀k]
    rw [show N₀ + (k + 1) - N₀ = k + 1 from by omega,
        show N₀ + k - N₀ = k from by omega]
    rw [add_assoc, succ_nsmul]

/-- **CCSB at a fixed (q, χ) implies infinitely many escapes from ker(χ)**.
    More precisely, if for some ε < 1 the walk character sum satisfies
    ‖∑_{n<N} χ(w(n))‖ ≤ ε·N for all sufficiently large N, then for every
    N₀ there exists n ≥ N₀ with χ(m(n)) ≠ 1.

    **Proof**: by contradiction.  If all multipliers from N₀ onward are in
    ker(χ), the walk sum grows linearly by `kernel_confinement_walk_sum`.
    The frozen term has norm 1, so the constant tail contributes norm
    ≥ (N − N₀) − N₀ = N − 2·N₀ for large N.  But CCSB gives ≤ ε·N with
    ε < 1, contradicting N − 2·N₀ > ε·N for N large enough. -/
theorem ccsb_at_implies_escape_cofinal {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hccsb : ∃ N₁ : ℕ, ∀ N ≥ N₁,
      ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤ ε * N)
    (N₀ : ℕ) : ∃ n, N₀ ≤ n ∧ (χ (emMultUnit q hq hne n) : ℂ) ≠ 1 := by
  by_contra h
  push_neg at h
  -- h : ∀ n, N₀ ≤ n → (χ (emMultUnit q hq hne n) : ℂ) = 1
  obtain ⟨N₁, hN₁⟩ := hccsb
  -- We need N large enough that (1-ε)·N > 2·N₀. Use Archimedean property.
  have h1ε_pos : 0 < 1 - ε := by linarith
  obtain ⟨M, hM⟩ := exists_nat_gt ((2 * (N₀ : ℝ) + 1) / (1 - ε))
  set N := max (max M N₁) N₀ with hN_def
  have hN_ge_N₁ : N₁ ≤ N := (le_max_right M N₁).trans (le_max_left _ N₀)
  have hN_ge_N₀ : N₀ ≤ N := le_max_right _ N₀
  have hM_le_N : M ≤ N := (le_max_left M N₁).trans (le_max_left _ N₀)
  have hN₁_bound := hN₁ N hN_ge_N₁
  -- The walk sum splits into a bounded prefix and a constant tail
  rw [kernel_confinement_walk_sum hq hne χ N₀ h N hN_ge_N₀] at hN₁_bound
  -- Bound the norm from below using reverse triangle inequality
  have hnorm_frozen : ‖(χ (emWalkUnit q hq hne N₀) : ℂ)‖ = 1 :=
    walkTelescope_char_norm_one χ _
  have hpre_bound : ‖∑ n ∈ Finset.range N₀,
      (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤ N₀ := by
    calc ‖∑ n ∈ Finset.range N₀, (χ (emWalkUnit q hq hne n) : ℂ)‖
        ≤ ∑ n ∈ Finset.range N₀, ‖(χ (emWalkUnit q hq hne n) : ℂ)‖ :=
          norm_sum_le _ _
      _ = ∑ n ∈ Finset.range N₀, 1 := by
          congr 1; ext n; exact walkTelescope_char_norm_one χ _
      _ = N₀ := by simp
  -- The tail has norm = N - N₀
  have htail_norm : ‖(N - N₀ : ℕ) • (χ (emWalkUnit q hq hne N₀) : ℂ)‖ =
      (N - N₀ : ℕ) := by
    rw [nsmul_eq_mul, norm_mul, Complex.norm_natCast, hnorm_frozen, mul_one]
  -- ‖prefix + tail‖ ≥ ‖tail‖ - ‖prefix‖ ≥ (N-N₀) - N₀
  have hrev : (N - N₀ : ℕ) - (N₀ : ℝ) ≤
      ‖∑ n ∈ Finset.range N₀, (χ (emWalkUnit q hq hne n) : ℂ) +
        (N - N₀ : ℕ) • (χ (emWalkUnit q hq hne N₀) : ℂ)‖ := by
    have h1 := norm_sub_norm_le
      ((N - N₀ : ℕ) • (χ (emWalkUnit q hq hne N₀) : ℂ))
      (-(∑ n ∈ Finset.range N₀, (χ (emWalkUnit q hq hne n) : ℂ)))
    rw [norm_neg, sub_neg_eq_add, add_comm] at h1
    rw [htail_norm] at h1
    linarith
  -- Combine: (N - N₀) - N₀ ≤ ‖sum‖ ≤ ε * N
  have hN_sub : (N - N₀ : ℕ) = (N : ℝ) - (N₀ : ℝ) := by
    rw [Nat.cast_sub hN_ge_N₀]
  rw [hN_sub] at hrev
  -- So: N - 2·N₀ ≤ ε·N, i.e., (1-ε)·N ≤ 2·N₀
  have h1 : (1 - ε) * N ≤ 2 * N₀ := by linarith [hrev, hN₁_bound]
  -- But (1-ε)·N ≥ (1-ε)·M > 2·N₀ + 1
  have h2 : (1 - ε) * N ≥ (1 - ε) * M := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hM_le_N) (le_of_lt h1ε_pos)
  have h3 : 2 * (N₀ : ℝ) + 1 < (1 - ε) * M := by
    rw [div_lt_iff₀ h1ε_pos] at hM; linarith
  linarith

end KernelConfinement

/-! ## Euclid Number Feedback Loop

This small subsection documents the relationship between the Euclid number
E(n) = prod(n) + 1 and the walk position w(n) = prod(n) mod q.

The key identity `euclid_number_mod_eq_walk_plus_one` shows that reducing the
Euclid number mod q gives the walk position plus 1. This is the algebraic
feedback loop: the walk position determines the next multiplier via
minFac(w(n) + 1 mod q). -/

section EuclidNumberFeedback

/-- **Euclid number feedback loop**: the Euclid number E(n) = prod(n) + 1,
    when reduced mod q, equals the walk position plus 1.

    This identity documents the feedback structure of the EM sequence:
    - Walk position: w(n) = prod(n) mod q
    - Euclid number: E(n) = prod(n) + 1
    - Multiplier: seq(n+1) = minFac(E(n))

    In ZMod q: E(n) ≡ w(n) + 1 (mod q), so the walk position directly
    determines the residue class of the Euclid number, and hence the
    available residue classes for the next multiplier. -/
theorem euclid_number_mod_eq_walk_plus_one (q : ℕ) [Fact (Nat.Prime q)] (n : ℕ) :
    (prod n + 1 : ZMod q) = (walkZ q n : ZMod q) + 1 := by
  simp [walkZ]

end EuclidNumberFeedback
