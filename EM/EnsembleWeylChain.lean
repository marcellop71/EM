import EM.EnsemblePT

/-!
# Generalized MC & Weyl Hitting Chain

This file contains the generalized Mullin Conjecture framework and the
JSE → MC chain via the Weyl test function argument.

## Main Results

### Definitions
* `GenMullinConjecture`              -- every prime in generalized EM from n
* `GenHittingImpliesGenMC`           -- cofinal hitting → gen MC (PROVED)
* `PerChiCancellationBridge`         -- per-chi SD → per-chi cancellation (PROVED)
* `WeylHittingBridge`                -- walk char cancellation → cofinal hitting (PROVED)

### Proved Theorems
* `gen_captures_target`              -- generalized captures_target (PROVED)
* `gen_hitting_implies_gen_mc_proved` -- cofinal walk hitting → gen MC (PROVED)
* `gen_mc_two_implies_mc`            -- GenMC(2) → MC (PROVED)
* `per_chi_cancellation_bridge_proved` -- PerChiCancellationBridge (PROVED)
* `weyl_hitting_bridge_proved`       -- WeylHittingBridge (PROVED)
* `jse_implies_nontrivial_cancellation` -- JSE + PCB → nontrivial cancellation (PROVED)
* `cancel_weyl_implies_mc`           -- walk cancellation → MC for n=2 (PROVED)
* `jse_transfer_implies_mc`          -- JSE + MultCancelToWalkCancel → MC (PROVED)

### Open Hypotheses (in other files)
* `JointStepEquidist` (EnsemblePT.lean)
* `MultCancelToWalkCancel` (EnsembleDecorrelation.lean)
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Section 4: Generalized MC from Walk Hitting -/

section GenMC

/-- **Generalized Mullin Conjecture for starting point n**: every prime
    appears in the generalized EM sequence from n. -/
def GenMullinConjecture (n : Nat) : Prop :=
  ∀ q : Nat, Nat.Prime q → ∃ k : Nat, genSeq n k = q

/-- **Walk hitting (cofinal) implies generalized MC.**
    If the generalized walk hits -1 mod q cofinally for every prime q
    (meaning for every N, there exists k >= N with q | genProd n k + 1),
    then every prime q appears in the generalized EM sequence from n.

    This is the generalized analogue of `conjectureA_implies_mullin`.
    The cofinal hitting hypothesis is necessary: a single hit might occur
    before all smaller primes have appeared, preventing the captures_target
    argument. With cofinal hitting, we can choose a hit past the "sieve gap"
    (after all smaller primes have appeared), making the argument work.

    **Status**: PROVED (gen_hitting_implies_gen_mc_proved). -/
def GenHittingImpliesGenMC : Prop :=
  ∀ (n : Nat), Squarefree n → 1 ≤ n →
    (∀ q : Nat, Nat.Prime q → ∀ N : Nat, ∃ k : Nat, N ≤ k ∧ genWalkZ n q k = -1) →
    GenMullinConjecture n

/-- Helper: if every prime below q appears in genSeq n, there exists a
    uniform bound N such that they all appear by step N.
    This is the generalized analogue of `exists_bound`. -/
private theorem gen_exists_bound (n : Nat) (q : Nat)
    (h : ∀ p, Nat.Prime p → p < q → ∃ k, genSeq n k = p) :
    ∃ N, ∀ p, Nat.Prime p → p < q → ∃ m, m < N ∧ genSeq n m = p := by
  induction q with
  | zero => exact ⟨0, fun p _ hp => absurd hp (by omega)⟩
  | succ q' ih =>
    have h' : ∀ p, Nat.Prime p → p < q' → ∃ k, genSeq n k = p :=
      fun p hp hpq => h p hp (by omega)
    obtain ⟨N', hN'⟩ := ih h'
    if hprime : Nat.Prime q' then
      obtain ⟨m, hm⟩ := h q' hprime (by omega)
      refine ⟨Nat.max N' (m + 1), fun p hp hpq => ?_⟩
      match Nat.lt_or_ge p q' with
      | .inl hlt =>
        obtain ⟨j, hj, hjseq⟩ := hN' p hp hlt
        exact ⟨j, lt_of_lt_of_le hj (Nat.le_max_left N' (m + 1)), hjseq⟩
      | .inr hge =>
        have : p = q' := by omega
        subst this
        exact ⟨m, lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_max_right N' (m + 1)), hm⟩
    else
      refine ⟨N', fun p hp hpq => ?_⟩
      match Nat.lt_or_ge p q' with
      | .inl hlt => exact hN' p hp hlt
      | .inr hge =>
        exfalso
        have : p = q' := by omega
        subst this
        exact hprime hp

/-- **Generalized captures_target**: if q divides genProd n k + 1 and all
    primes p < q have appeared in genSeq n at steps < k, then genSeq n k = q.

    This parallels `captures_target` from MullinConjectures.lean. The proof:
    - genSeq n k = Nat.minFac(genProd n k + 1) <= q (minimality of minFac)
    - If genSeq n k < q, it appeared at some earlier step j < k (by hypothesis)
    - Then genSeq n j divides genProd n k (via genSeq_dvd_genProd_later)
    - But genSeq n k = genSeq n j also divides genProd n k + 1
    - A prime dividing both genProd n k and genProd n k + 1 divides 1: contradiction -/
theorem gen_captures_target {n : Nat} (hn : Squarefree n)
    {q : Nat} (hq : Nat.Prime q) {k : Nat}
    (hdvd : q ∣ genProd n k + 1)
    (hall : ∀ p, Nat.Prime p → p < q → ∃ j, j < k ∧ genSeq n j = p) :
    genSeq n k = q := by
  have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero (Squarefree.ne_zero hn)
  -- genSeq n k = Nat.minFac(genProd n k + 1), so genSeq n k divides genProd n k + 1
  -- Upper bound: genSeq n k <= q
  have hpn : 2 ≤ genProd n k + 1 := by have := genProd_pos hn_pos k; omega
  have hle : genSeq n k ≤ q := by
    rw [genSeq_def]
    exact Nat.minFac_le_of_dvd hq.two_le hdvd
  -- genSeq n k is prime
  have hprime_s := genSeq_prime hn_pos k
  -- Lower bound: q <= genSeq n k
  have hge : q ≤ genSeq n k := by
    match Nat.lt_or_ge (genSeq n k) q with
    | .inr hge => exact hge
    | .inl hlt =>
      exfalso
      -- genSeq n k < q and is prime, so by hall it appeared at some step j < k
      obtain ⟨j, hjk, hseqj⟩ := hall (genSeq n k) hprime_s hlt
      -- genSeq n j = genSeq n k, so genSeq n j divides genProd n k
      have h_dvd_prod : genSeq n j ∣ genProd n k := by
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hjk)
        rw [hd]; exact genSeq_dvd_genProd_later n j d
      -- genSeq n k divides genProd n k (substituting genSeq n j = genSeq n k)
      rw [hseqj] at h_dvd_prod
      -- genSeq n k divides genProd n k + 1
      have h_dvd_succ := genSeq_dvd_genProd_succ n k
      -- A number >= 2 can't divide both a and a+1
      exact not_dvd_consec hprime_s.two_le h_dvd_prod h_dvd_succ
  omega

/-- **Cofinal walk hitting implies generalized MC.** PROVED.

    The proof follows the same pattern as `conjectureA_implies_mullin`:
    strong induction on q, collecting witnesses into a uniform bound,
    choosing a hit past the bound, and applying gen_captures_target. -/
theorem gen_hitting_implies_gen_mc_proved : GenHittingImpliesGenMC := by
  intro n hn hn_pos hhit
  -- Prove ∀ q, Nat.Prime q → ∃ k, genSeq n k = q by strong induction on q
  unfold GenMullinConjecture
  suffices ∀ B q, q ≤ B → Nat.Prime q → ∃ k, genSeq n k = q by
    intro q hq; exact this q q (Nat.le_refl q) hq
  intro B
  induction B with
  | zero => intro q hle hq; exact absurd hq.two_le (by omega)
  | succ B ih =>
    intro q hle hq
    match Nat.lt_or_ge q (B + 1) with
    | .inl hlt => exact ih q (by omega) hq
    | .inr _ =>
      -- q = B + 1. By IH, every prime p < q appears in genSeq n.
      have appears : ∀ p, Nat.Prime p → p < q → ∃ k, genSeq n k = p :=
        fun p hp hpq => ih p (by omega) hp
      -- Collect witnesses into a uniform bound N
      obtain ⟨N, hN⟩ := gen_exists_bound n q appears
      -- By cofinal hitting, get k >= N with q | genProd n k + 1
      obtain ⟨k, hk_ge, hhit_k⟩ := hhit q hq N
      rw [genWalkZ_eq_neg_one_iff] at hhit_k
      -- All primes < q appeared at steps < k (since k >= N >= each witness)
      have hall : ∀ p, Nat.Prime p → p < q → ∃ j, j < k ∧ genSeq n j = p := by
        intro p hp hpq
        obtain ⟨m, hm, hseqm⟩ := hN p hp hpq
        exact ⟨m, by omega, hseqm⟩
      -- gen_captures_target: genSeq n k = q. Done!
      exact ⟨k, gen_captures_target hn hq hhit_k hall⟩

/-- **Standard EM is a special case of generalized EM.**
    GenMullinConjecture 2 is equivalent to MullinConjecture
    (modulo the index shift genSeq 2 k = seq (k+1)). -/
theorem gen_mc_two_implies_mc
    (h : GenMullinConjecture 2) : MullinConjecture := by
  intro q hq
  obtain ⟨k, hk⟩ := h q (IsPrime.toNatPrime hq)
  exact ⟨k + 1, by rwa [← genSeq_two_eq_seq_succ]⟩

end GenMC

/-! ## Section 4b: JSE → GenMC Master Chain

The full chain from JointStepEquidist to GenMullinConjecture requires two bridges:

1. **Per-chi cancellation bridge**: JSE gives per-chi decorrelation for nontrivial
   characters (PROVED: `joint_step_equidist_implies_step_decorrelation`). The
   existing `sd_implies_cancellation` works with *universal* StepDecorrelation
   (quantified over ALL chi, including trivial), but JSE only gives decorrelation
   for nontrivial chi. A per-chi version of the variance-concentration-cancellation
   chain is needed. This is mathematically straightforward (identical proofs
   restricted to one chi) and captured by `PerChiCancellationBridge` (PROVED).

2. **Weyl hitting bridge**: Character cancellation for all nontrivial chi implies
   equidistribution of the walk (Weyl criterion), hence cofinal hitting of -1.
   This is captured by `WeylHittingBridge`.

Together: JSE + PerChiCancellationBridge (PROVED) + WeylHittingBridge → GenMC for all
squarefree n ≥ 1, completing the ensemble chain.
-/

section JSEToGenMC

/-- **Per-chi cancellation bridge**: per-chi step decorrelation implies
    per-chi character sum cancellation.

    This captures the mathematical content that the variance-concentration-cancellation
    chain (`decorrelation_implies_variance_proved`, `char_variance_implies_concentration_proved`,
    `char_concentration_implies_cancellation`) works per-chi, not just for universal SD.

    The proof is identical to the existing chain but with the SD hypothesis
    restricted to a single character χ. Specifically:
    - Per-chi SD → per-chi variance bound (C=2, by the same induction on K)
    - Per-chi variance → per-chi concentration (same Markov argument)
    - Per-chi concentration → per-chi cancellation (same squeeze argument)

    **Status**: PROVED (`per_chi_cancellation_bridge_proved`). -/
def PerChiCancellationBridge : Prop :=
  ∀ (q : Nat), Nat.Prime q →
  ∀ (χ : Nat → ℂ), (∀ a, Complex.normSq (χ a) ≤ 1) →
  -- Per-chi decorrelation hypothesis (not universal SD)
  (∀ j k : Nat, j < k →
    Filter.Tendsto
      (fun X : Nat =>
        |ensembleAvg X (fun n =>
            (χ (genSeq n j % q) * starRingEnd ℂ (χ (genSeq n k % q))).re)|)
      Filter.atTop (nhds 0)) →
  -- Conclusion: per-chi cancellation
  ∀ (ε : ℝ), 0 < ε →
    Filter.Tendsto
      (fun X : Nat =>
        (((Finset.Icc 1 X).filter
          (fun n => Squarefree n ∧
            ∀ K, genSeqCharEnergy n K q χ > (ε * K) ^ 2)).card : ℝ) /
        ((Finset.Icc 1 X).filter Squarefree).card)
      Filter.atTop (nhds 0)

/-- **PerChiCancellationBridge is PROVED.**

    The proof inlines the three-step chain (variance → concentration → cancellation)
    with the character χ fixed throughout. Each step is identical to its universal
    counterpart (`decorrelation_implies_variance_proved`,
    `char_variance_implies_concentration_proved`,
    `char_concentration_implies_cancellation`) but uses the per-chi decorrelation
    hypothesis instead of universal `StepDecorrelation`.

    **Step 1** (per-chi variance, C=2): By induction on K. Base: energy(0)=0≤0.
    Step: energy(K+1) = energy(K) + normSq(z_K) + 2·Re(S_K·conj(z_K)).
    The diagonal contributes ≤1. The cross-term is a sum of K terms, each
    with ensemble average → 0 by per-chi decorrelation. Choose X₀ so each
    cross-term average < 1/(2(K+1)), giving total cross ≤ 1.
    So E[energy(K+1)] ≤ 2K + 1 + 1 = 2(K+1).

    **Step 2** (per-chi concentration): Markov/Chebyshev. The variance bound
    gives density ≤ 2K/(εK)² = 2/(ε²K). Choose K₀ ≥ ⌈2/(ε²δ)⌉+1.

    **Step 3** (per-chi cancellation): The "∀ K" deviant set is a subset of
    the K₀-specific deviant set, so its density → 0 via Metric.tendsto_atTop. -/
theorem per_chi_cancellation_bridge_proved : PerChiCancellationBridge := by
  intro q hq χ hχ h_decorr ε hε
  -- ===== Step 1: Per-chi variance bound with C=2 (via extracted helper) =====
  have h_variance : ∀ K : Nat, ∃ X₀ : Nat, ∀ X ≥ X₀,
      ensembleAvg X (fun n => genSeqCharEnergy n K q χ) ≤ 2 * K :=
    variance_bound_induction q χ hχ (fun j K hjK => by
      have hε_cross : (0 : ℝ) < 1 / (2 * ((K : ℝ) + 1)) :=
        div_pos one_pos (mul_pos two_pos (Nat.cast_add_one_pos (n := K)))
      have h := h_decorr j K hjK
      rw [Metric.tendsto_atTop] at h
      obtain ⟨X₀, hX₀⟩ := h _ hε_cross
      refine ⟨X₀, fun X hX => ?_⟩
      have := hX₀ X hX
      rwa [Real.dist_eq, sub_zero, abs_abs] at this)
  -- ===== Step 2: Per-chi concentration =====
  -- For any δ > 0, ∃ K₀, ∀ K ≥ K₀, ∃ X₀, ∀ X ≥ X₀, density ≤ δ
  have h_concentration : ∀ (δ : ℝ), 0 < δ →
      ∃ K₀ : Nat, ∀ K ≥ K₀, ∃ X₀ : Nat, ∀ X ≥ X₀,
        (((Finset.Icc 1 X).filter
          (fun n => Squarefree n ∧
            genSeqCharEnergy n K q χ > (ε * ↑K) ^ 2)).card : ℝ) /
        ((Finset.Icc 1 X).filter Squarefree).card ≤ δ := by
    intro δ hδ
    -- Markov: density ≤ 2K/(εK)² = 2/(ε²K). Need K ≥ 2/(ε²δ).
    set K₀ := Nat.max 1 (Nat.ceil (2 / (ε ^ 2 * δ)) + 1)
    refine ⟨K₀, fun K hK => ?_⟩
    have hK_ge_one : K ≥ 1 := le_trans (Nat.le_max_left 1 _) hK
    have hK_pos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr (by omega)
    obtain ⟨X₀, hX₀⟩ := h_variance K
    refine ⟨X₀, fun X hX => ?_⟩
    have hεK_sq_pos : (0 : ℝ) < (ε * ↑K) ^ 2 := sq_pos_of_pos (mul_pos hε hK_pos)
    -- Apply Markov inequality
    have h_markov : (((Finset.Icc 1 X).filter
        (fun n => Squarefree n ∧
          genSeqCharEnergy n K q χ > (ε * ↑K) ^ 2)).card : ℝ) /
      ((Finset.Icc 1 X).filter Squarefree).card ≤
      2 * ↑K / (ε * ↑K) ^ 2 := by
      exact finset_markov_density
        (fun n hn => genSeqCharEnergy_nonneg _ _ _ _)
        hεK_sq_pos
        (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (le_of_lt hK_pos))
        (hX₀ X hX)
        _
        (fun n hn => by
          simp only [Finset.mem_filter] at hn ⊢
          exact ⟨hn.1, hn.2.1⟩)
        (fun n hn => by
          simp only [Finset.mem_filter] at hn
          exact le_of_lt hn.2.2)
    -- Simplify: 2K/(εK)² = 2/(ε²K)
    have h_simplify : 2 * ↑K / (ε * ↑K) ^ 2 = 2 / (ε ^ 2 * ↑K) := by
      rw [mul_pow]; field_simp
    rw [h_simplify] at h_markov
    -- Show 2/(ε²K) ≤ δ
    have h_bound : 2 / (ε ^ 2 * ↑K) ≤ δ := by
      rw [div_le_iff₀ (mul_pos (sq_pos_of_pos hε) hK_pos)]
      have hε2δ_pos : (0 : ℝ) < ε ^ 2 * δ := mul_pos (sq_pos_of_pos hε) hδ
      have hK_large : (K : ℝ) ≥ 2 / (ε ^ 2 * δ) := by
        have hK₀_large : (K₀ : ℝ) ≥ Nat.ceil (2 / (ε ^ 2 * δ)) + 1 := by
          exact_mod_cast Nat.le_max_right 1 _
        have : (K : ℝ) ≥ K₀ := by exact_mod_cast hK
        have hceil : (Nat.ceil (2 / (ε ^ 2 * δ)) : ℝ) ≥ 2 / (ε ^ 2 * δ) := Nat.le_ceil _
        linarith
      have hkey : ε ^ 2 * δ * ↑K ≥ 2 := by
        calc ε ^ 2 * δ * ↑K
            ≥ ε ^ 2 * δ * (2 / (ε ^ 2 * δ)) :=
              mul_le_mul_of_nonneg_left hK_large (le_of_lt hε2δ_pos)
          _ = 2 := by field_simp
      linarith
    linarith
  -- ===== Step 3: Per-chi cancellation (squeeze to zero) =====
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- Get K₀ from concentration with density target δ/2
  obtain ⟨K₀, hK₀⟩ := h_concentration (δ / 2) (by linarith)
  -- For K = K₀, get X₀
  obtain ⟨X₀, hX₀⟩ := hK₀ K₀ (le_refl _)
  refine ⟨X₀, fun X hX => ?_⟩
  -- The density of the K₀-specific set is ≤ δ/2
  have h_K₀_bound := hX₀ X hX
  -- The "∀ K" set is a subset of the K₀-specific set
  have h_card : ((Finset.Icc 1 X).filter
      (fun n => Squarefree n ∧
        ∀ K, genSeqCharEnergy n K q χ > (ε * K) ^ 2)).card ≤
    ((Finset.Icc 1 X).filter
      (fun n => Squarefree n ∧
        genSeqCharEnergy n K₀ q χ > (ε * K₀) ^ 2)).card := by
    apply Finset.card_le_card
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1, hn.2.2 K₀⟩
  -- So density of "∀ K" set ≤ density of K₀-specific set ≤ δ/2
  have h_density_bound : (((Finset.Icc 1 X).filter
      (fun n => Squarefree n ∧
        ∀ K, genSeqCharEnergy n K q χ > (ε * ↑K) ^ 2)).card : ℝ) /
    ((Finset.Icc 1 X).filter Squarefree).card ≤ δ / 2 :=
    le_trans (div_le_div_of_nonneg_right (by exact_mod_cast h_card) (Nat.cast_nonneg _))
      h_K₀_bound
  -- dist f(X) 0 = |f(X)| = f(X) (since f ≥ 0) ≤ δ/2 < δ
  rw [Real.dist_eq]
  have h_nn : 0 ≤ (((Finset.Icc 1 X).filter
      (fun n => Squarefree n ∧
        ∀ K, genSeqCharEnergy n K q χ > (ε * ↑K) ^ 2)).card : ℝ) /
    ((Finset.Icc 1 X).filter Squarefree).card :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- **Nontrivial character cancellation from JSE + PerChiCancellationBridge.**

    Under JSE, every nontrivial character χ mod q (chi(0)=0, ∑chi=0, normSq≤1)
    has its character sums cancel for almost all squarefree starting points.

    This composes:
    1. JSE → per-chi decorrelation (joint_step_equidist_implies_step_decorrelation, PROVED)
    2. Per-chi decorrelation → per-chi cancellation (PerChiCancellationBridge, PROVED)

    **Status**: PROVED (from JSE + PerChiCancellationBridge, both proved). -/
theorem jse_implies_nontrivial_cancellation
    (hjse : JointStepEquidist) (hbridge : PerChiCancellationBridge) :
    ∀ (q : Nat) (hq : Nat.Prime q),
    ∀ (χ : Nat → ℂ), (∀ a, Complex.normSq (χ a) ≤ 1) →
    (χ 0 = 0) →
    (letI : NeZero q := ⟨hq.ne_zero⟩; ∑ a : ZMod q, χ (ZMod.val a) = 0) →
    ∀ (ε : ℝ), 0 < ε →
      Filter.Tendsto
        (fun X : Nat =>
          (((Finset.Icc 1 X).filter
            (fun n => Squarefree n ∧
              ∀ K, genSeqCharEnergy n K q χ > (ε * K) ^ 2)).card : ℝ) /
          ((Finset.Icc 1 X).filter Squarefree).card)
        Filter.atTop (nhds 0) := by
  intro q hq χ hχ_bound hχ0 hχ_sum ε hε
  -- Step 1: JSE → per-chi decorrelation for this nontrivial χ
  have h_decorr : ∀ j k : Nat, j < k →
      Filter.Tendsto
        (fun X : Nat =>
          |ensembleAvg X (fun n =>
              (χ (genSeq n j % q) * starRingEnd ℂ (χ (genSeq n k % q))).re)|)
        Filter.atTop (nhds 0) :=
    joint_step_equidist_implies_step_decorrelation hjse q hq χ hχ0 hχ_sum
  -- Step 2: per-chi decorrelation → per-chi cancellation (PerChiCancellationBridge)
  exact hbridge q hq χ hχ_bound h_decorr ε hε

/-- **Weyl hitting bridge**: walk character cancellation (strong Weyl form)
    for primes not dividing the starting point implies either the prime
    appeared in the generalized sequence or the walk hits -1 cofinally.

    The mathematical content is the Weyl equidistribution criterion applied
    to the walk positions genProd n k mod q. The hypothesis uses genWalkCharEnergy
    (walk character energy) with the strong form: for all K >= K0, the energy
    is bounded by (eps*K)^2. The guard q does not divide n ensures the walk
    starts in (Z/qZ)x.

    **Status**: PROVED (weyl_hitting_bridge_proved). -/
def WeylHittingBridge : Prop :=
  ∀ (n : Nat), Squarefree n → 1 ≤ n →
  ∀ (q : Nat) (hq : Nat.Prime q),
  ¬ (q ∣ n) →
  (∀ (χ : Nat → ℂ), (∀ a, Complex.normSq (χ a) ≤ 1) →
    (χ 0 = 0) →
    (letI : NeZero q := ⟨hq.ne_zero⟩; ∑ a : ZMod q, χ (ZMod.val a) = 0) →
    ∀ (ε : ℝ), 0 < ε →
      ∃ K₀ : Nat, ∀ K : Nat, K₀ ≤ K → genWalkCharEnergy n K q χ ≤ (ε * K) ^ 2) →
  (∃ j : Nat, genSeq n j = q) ∨
  (∀ N : Nat, ∃ k : Nat, N ≤ k ∧ genWalkZ n q k = -1)

/-- If q is prime, does not divide n, and never appears as genSeq n j,
    then q does not divide genProd n k for any k. -/
private theorem genProd_not_dvd_of_not_appeared {n : Nat} {q : Nat} (hq : Nat.Prime q)
    (hndvd : ¬ (q ∣ n)) (hnot : ∀ j, genSeq n j ≠ q) (k : Nat) :
    ¬ (q ∣ genProd n k) := by
  induction k with
  | zero => simpa [genProd]
  | succ k ih =>
    rw [genProd_succ]; intro hdvd
    rcases hq.dvd_mul.mp hdvd with h1 | h2
    · exact ih h1
    · have hn_pos : 1 ≤ n := by
        by_contra h; push_neg at h; interval_cases n; exact hndvd (dvd_zero q)
      rcases (genSeq_prime hn_pos k).eq_one_or_self_of_dvd q h2 with h | h
      · exact absurd h (by have := hq.one_lt; omega)
      · exact absurd h.symm (hnot k)

/-- If no hits at -1 occur at steps >= N0, hits in any range are bounded
    by hits in range N0. -/
private theorem hit_filter_bounded {n q N₀ : Nat}
    (hno : ∀ k, N₀ ≤ k → genProd n k % q ≠ q - 1) (K : Nat) :
    ((Finset.range K).filter (fun k => genProd n k % q = q - 1)).card ≤
    ((Finset.range N₀).filter (fun k => genProd n k % q = q - 1)).card := by
  apply Finset.card_le_card; intro k hk
  simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
  exact ⟨by_contra fun h => hno k (by push_neg at h; exact h) hk.2, hk.2⟩

/-- The Weyl test function: centered indicator of -1 among units mod q. -/
private noncomputable def weylTestFn (q : Nat) : Nat → ℂ := fun x =>
  if x % q = 0 then (0 : ℂ)
  else if x % q = q - 1 then (((q : ℝ) - 2) / ((q : ℝ) - 1) : ℂ)
  else (((-1 : ℝ) / ((q : ℝ) - 1)) : ℂ)

private theorem weylTestFn_zero (q : Nat) : weylTestFn q 0 = 0 := by
  simp [weylTestFn]

private theorem weylTestFn_bound (q : Nat) (hq2 : 2 ≤ q) (a : Nat) :
    Complex.normSq (weylTestFn q a) ≤ 1 := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hqr_pos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  simp only [weylTestFn]
  split_ifs with h0 h1
  · simp [Complex.normSq]
  · rw [show (((q : ℝ) - 2) / ((q : ℝ) - 1) : ℂ) =
      Complex.ofReal (((q : ℝ) - 2) / ((q : ℝ) - 1)) from by push_cast; ring]
    rw [Complex.normSq_ofReal, div_mul_div_comm, div_le_one (by positivity)]
    exact mul_self_le_mul_self (by linarith) (by linarith)
  · rw [show (((-1 : ℝ) / ((q : ℝ) - 1)) : ℂ) =
      Complex.ofReal ((-1 : ℝ) / ((q : ℝ) - 1)) from by push_cast; ring]
    rw [Complex.normSq_ofReal, div_mul_div_comm, div_le_one (by positivity)]
    nlinarith

/-- The Weyl test function sums to zero over ZMod q.
    Sum = 0 (at val=0) + (q-2)/(q-1) (at val=q-1) + (q-2)*(-1/(q-1)) (rest) = 0. -/
private theorem weylTestFn_sum_zero (q : Nat) (hq : Nat.Prime q) :
    (letI : NeZero q := ⟨hq.ne_zero⟩; ∑ a : ZMod q, weylTestFn q (ZMod.val a) = 0) := by
  letI : NeZero q := ⟨hq.ne_zero⟩
  have hq2 := hq.two_le
  have hval_mod : ∀ a : ZMod q, ZMod.val a % q = ZMod.val a :=
    fun a => Nat.mod_eq_of_lt (ZMod.val_lt a)
  simp_rw [weylTestFn, hval_mod]
  -- Decompose: each summand = B·(if val≠0 then 1 else 0) + (A-B)·(if val=q-1 then 1 else 0)
  -- Sum = B·(q-1) + (A-B)·1 = A + (q-2)·B = 0.
  set A : ℂ := (((q : ℝ) - 2) / ((q : ℝ) - 1) : ℂ) with hAdef
  set B : ℂ := (((-1 : ℝ) / ((q : ℝ) - 1)) : ℂ) with hBdef
  have hdecomp : ∀ a : ZMod q,
      (if ZMod.val a = 0 then (0 : ℂ) else if ZMod.val a = q - 1 then A else B) =
      B * (if ZMod.val a = 0 then 0 else 1) + (A - B) * (if ZMod.val a = q - 1 then 1 else 0) := by
    intro a; split_ifs with h0 h1
    · exfalso; omega
    · simp
    · ring
    · ring
  simp_rw [hdecomp, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- Need: B·card{val≠0} + (A-B)·card{val=q-1} = 0 where card{val≠0}=q-1, card{val=q-1}=1
  have hval_inj : Function.Injective (fun a : ZMod q => ZMod.val a) := ZMod.val_injective q
  have hcard_ne0 : ((Finset.univ.filter (fun a : ZMod q => ¬ZMod.val a = 0)).card : ℂ) =
      (q : ℂ) - 1 := by
    have htotal : Finset.card (Finset.univ : Finset (ZMod q)) = q := ZMod.card q
    have hone : (Finset.univ.filter (fun a : ZMod q => ZMod.val a = 0)).card = 1 := by
      have : Finset.univ.filter (fun a : ZMod q => ZMod.val a = 0) = {0} := by
        ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h => hval_inj (by simp [h]), fun h => by simp [h]⟩
      rw [this, Finset.card_singleton]
    have hnat := Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (fun a : ZMod q => ZMod.val a = 0)
    rw [htotal, hone] at hnat
    rw [show (Finset.univ.filter (fun a : ZMod q => ¬ZMod.val a = 0)).card = q - 1 from by omega,
        Nat.cast_sub (by omega : 1 ≤ q)]; simp
  -- Second: card{a : ZMod q | val a = q-1}
  have hcard_qm1 : ((Finset.univ.filter (fun a : ZMod q => ZMod.val a = q - 1)).card : ℂ) = 1 := by
    have : Finset.univ.filter (fun a : ZMod q => ZMod.val a = q - 1) = {((q - 1 : Nat) : ZMod q)} := by
      ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; apply hval_inj; simp only; rw [h, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      · intro h; rw [h, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [this, Finset.card_singleton]; simp
  rw [hcard_ne0, hcard_qm1]
  rw [hAdef, hBdef]; push_cast; field_simp; ring

/-- **WeylHittingBridge is true.** PROVED.

    Proof by contradiction using the Weyl test function. If q never appeared
    and the walk stops hitting -1, the hit count is bounded. The test function's
    partial sum grows as K/(q-1), giving energy ~ K^2/(q-1)^2 which contradicts
    the hypothesis for eps = 1/(2(q-1)). -/
theorem weyl_hitting_bridge_proved : WeylHittingBridge := by
  intro n hn hn_pos q hq hndvd hcancel
  by_cases happeared : ∃ j, genSeq n j = q
  · exact Or.inl happeared
  · push_neg at happeared; right
    have hndvd_prod := fun k => genProd_not_dvd_of_not_appeared hq hndvd happeared k
    have hwalk_nz : ∀ k, genProd n k % q ≠ 0 :=
      fun k h => hndvd_prod k (Nat.dvd_of_mod_eq_zero h)
    by_contra hf; push_neg at hf
    obtain ⟨N₀, hN₀⟩ := hf
    have hno : ∀ k, N₀ ≤ k → genProd n k % q ≠ q - 1 := by
      intro k hk h; apply hN₀ k hk; rw [genWalkZ_eq_neg_one_iff]
      have hq2 := hq.two_le
      rw [Nat.dvd_iff_mod_eq_zero]
      conv_lhs => rw [show genProd n k + 1 = genProd n k + 1 from rfl]
      rw [Nat.add_mod, h]
      have : 1 % q = 1 := Nat.mod_eq_of_lt (by omega)
      rw [this, Nat.sub_add_cancel (by omega : 1 ≤ q), Nat.mod_self]
    set C := ((Finset.range N₀).filter (fun k => genProd n k % q = q - 1)).card
    have hbd := hit_filter_bounded hno
    -- Apply hypothesis with Weyl test function
    set χ := weylTestFn q
    have hχ_bound := weylTestFn_bound q hq.two_le
    have hχ0 := weylTestFn_zero q
    have hχ_sum := weylTestFn_sum_zero q hq
    have hqr_pos : (0 : ℝ) < (q : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.two_le
      linarith
    set ε := 1 / (2 * ((q : ℝ) - 1))
    have hε_pos : 0 < ε := div_pos one_pos (mul_pos two_pos hqr_pos)
    obtain ⟨K₀, hK₀⟩ := hcancel χ hχ_bound hχ0 hχ_sum ε hε_pos
    -- Choose K large enough
    set K := Nat.max K₀ (2 * C * q + 1)
    have hK_ge : K₀ ≤ K := Nat.le_max_left _ _
    have hK_big : 2 * C * q + 1 ≤ K := Nat.le_max_right _ _
    have hE := hK₀ K hK_ge
    -- Compute partial sum, show energy = (hitK - K/(q-1))², derive contradiction
    set hitK := ((Finset.range K).filter (fun k => genProd n k % q = q - 1)).card
    set A : ℂ := (((q : ℝ) - 2) / ((q : ℝ) - 1) : ℂ)
    set B : ℂ := (((-1 : ℝ) / ((q : ℝ) - 1)) : ℂ)
    -- Each summand: since walk is never 0 mod q, χ(genProd n k % q) is A or B
    have hterm : ∀ k, k ∈ Finset.range K →
        χ (genProd n k % q) = if genProd n k % q = q - 1 then A else B := by
      intro k _
      simp only [χ, weylTestFn]
      -- weylTestFn applies % q to its arg, giving (genProd n k % q) % q = genProd n k % q
      rw [Nat.mod_mod_of_dvd _ (dvd_refl q)]
      rw [if_neg (hwalk_nz k)]
    have hpartial : genWalkCharPartialSum n K q χ = ↑hitK * A + (↑K - ↑hitK) * B := by
      simp only [genWalkCharPartialSum]; rw [Finset.sum_congr rfl hterm]
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      -- Goal: ↑hitK * A + ↑compl * B = ↑hitK * A + (↑K - ↑hitK) * B
      -- where compl = filter (¬P).card
      -- We need: ↑compl = ↑K - ↑hitK
      have hle : hitK ≤ K := by
        have := Finset.card_filter_le (Finset.range K) (fun k => genProd n k % q = q - 1)
        rw [Finset.card_range] at this; exact this
      have hcomp := Finset.card_filter_add_card_filter_not
        (s := Finset.range K) (fun k => genProd n k % q = q - 1)
      rw [Finset.card_range] at hcomp
      -- hcomp: hitK + compl = K, so compl = K - hitK
      set compl := ((Finset.range K).filter (fun k => ¬genProd n k % q = q - 1)).card
      have hcompl_eq : compl = K - hitK := by omega
      rw [hcompl_eq, Nat.cast_sub hle]
    -- A and B simplify: hitK*A + (K-hitK)*B = (hitK - K/(q-1))
    have hAB_val : ↑hitK * A + (↑K - ↑hitK) * B =
        (↑(hitK : ℕ) - ↑(K : ℕ) / ((q : ℝ) - 1) : ℝ) := by
      simp only [A, B]; push_cast
      have hqc : ((-1 : ℂ) + (q : ℂ)) ≠ 0 := by
        rw [show (-1 : ℂ) + (q : ℂ) = ((q : ℤ) - 1 : ℤ) from by push_cast; ring]
        exact_mod_cast (show (q : ℤ) - 1 ≠ 0 from by have := hq.two_le; omega)
      set r := ((-1 : ℂ) + (↑↑q : ℂ))⁻¹
      have hqr1 : ((-1 : ℂ) + ↑↑q) * r = 1 := mul_inv_cancel₀ hqc
      linear_combination ↑↑hitK * hqr1
    -- So energy = normSq of a real number
    have henergy_eq : genWalkCharEnergy n K q χ =
        ((hitK : ℝ) - (K : ℝ) / ((q : ℝ) - 1)) ^ 2 := by
      simp only [genWalkCharEnergy]; rw [hpartial, hAB_val]
      rw [show ((↑hitK - ↑K / ((q : ℝ) - 1) : ℝ) : ℂ) =
        Complex.ofReal (↑hitK - ↑K / ((q : ℝ) - 1)) from by push_cast; ring]
      rw [Complex.normSq_ofReal]; ring
    -- Step 2: Energy lower bound
    -- hitK ≤ C (bounded by early hits)
    have hhit_le : hitK ≤ C := hbd K
    -- Energy ≥ (K/(q-1) - C)^2 when K/(q-1) ≥ C
    have hKr : (K : ℝ) / ((q : ℝ) - 1) ≥ (C : ℝ) := by
      rw [ge_iff_le, le_div_iff₀ hqr_pos]
      have hq2 := hq.two_le
      have : (q : ℝ) - 1 ≤ (q : ℝ) := by linarith
      calc (C : ℝ) * ((q : ℝ) - 1) ≤ (C : ℝ) * (q : ℝ) := by
            apply mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ (2 * C * q : ℕ) := by
            push_cast
            have : (0 : ℝ) ≤ (C : ℝ) * (q : ℝ) := mul_nonneg (Nat.cast_nonneg' C) (Nat.cast_nonneg' q)
            linarith
        _ ≤ (2 * C * q + 1 : ℕ) := by push_cast; linarith
        _ ≤ K := by exact_mod_cast hK_big
    have henergy_lb : ((K : ℝ) / ((q : ℝ) - 1) - (C : ℝ)) ^ 2 ≤ genWalkCharEnergy n K q χ := by
      rw [henergy_eq]
      have hhitR : (hitK : ℝ) ≤ (C : ℝ) := by exact_mod_cast hhit_le
      -- (K/(q-1) - C)^2 ≤ (hitK - K/(q-1))^2
      -- = (K/(q-1) - hitK)^2 (squaring removes sign)
      rw [show ((hitK : ℝ) - (K : ℝ) / ((q : ℝ) - 1)) ^ 2 =
        ((K : ℝ) / ((q : ℝ) - 1) - (hitK : ℝ)) ^ 2 from by ring]
      apply sq_le_sq'
      · -- -(K/(q-1) - hitK) ≤ K/(q-1) - C, i.e., C ≤ 2K/(q-1) - hitK
        -- True since C ≤ K/(q-1) and hitK ≤ K/(q-1)
        linarith
      · -- K/(q-1) - C ≤ K/(q-1) - hitK, i.e., hitK ≤ C
        linarith
    -- Step 3: Energy upper bound from hypothesis
    -- energy ≤ (ε * K)^2 = (K / (2*(q-1)))^2
    have hε_val : ε = 1 / (2 * ((q : ℝ) - 1)) := rfl
    have henergy_ub : genWalkCharEnergy n K q χ ≤ ((K : ℝ) / (2 * ((q : ℝ) - 1))) ^ 2 := by
      calc genWalkCharEnergy n K q χ ≤ (ε * K) ^ 2 := hE
        _ = ((K : ℝ) / (2 * ((q : ℝ) - 1))) ^ 2 := by rw [hε_val]; ring
    -- Combined: (K/(q-1) - C)^2 ≤ (K/(2(q-1)))^2
    have hcombined : ((K : ℝ) / ((q : ℝ) - 1) - (C : ℝ)) ^ 2 ≤
        ((K : ℝ) / (2 * ((q : ℝ) - 1))) ^ 2 := le_trans henergy_lb henergy_ub
    -- Since both sides ≥ 0, take square root: lhs ≤ rhs
    have hrhs_nn : (0 : ℝ) ≤ (K : ℝ) / (2 * ((q : ℝ) - 1)) := by positivity
    have hsqrt := (abs_le_of_sq_le_sq' hcombined hrhs_nn).2
    -- K/(q-1) - C ≤ K/(2(q-1)), so K/(2(q-1)) ≤ C
    -- From hsqrt: K/(q-1) - C ≤ K/(2(q-1))
    -- Hence: K/(q-1) - K/(2(q-1)) ≤ C
    -- K/(q-1) - K/(2(q-1)) = K * (1/(q-1) - 1/(2(q-1))) = K * 1/(2(q-1)) = K/(2(q-1))
    have hdiff : (K : ℝ) / ((q : ℝ) - 1) - (K : ℝ) / (2 * ((q : ℝ) - 1)) =
        (K : ℝ) / (2 * ((q : ℝ) - 1)) := by
      field_simp; ring
    have hKC : (K : ℝ) / (2 * ((q : ℝ) - 1)) ≤ (C : ℝ) := by linarith
    -- K ≤ 2*C*(q-1)
    have hK_le : (K : ℝ) ≤ 2 * (C : ℝ) * ((q : ℝ) - 1) := by
      have h2qr := show (0 : ℝ) < 2 * ((q : ℝ) - 1) from by positivity
      calc (K : ℝ) = (K : ℝ) / (2 * ((q : ℝ) - 1)) * (2 * ((q : ℝ) - 1)) :=
            (div_mul_cancel₀ _ (ne_of_gt h2qr)).symm
        _ ≤ (C : ℝ) * (2 * ((q : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_right hKC (le_of_lt h2qr)
        _ = 2 * (C : ℝ) * ((q : ℝ) - 1) := by ring
    -- But K ≥ 2*C*q + 1 > 2*C*(q-1) (since C ≥ 0)
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.two_le
    have hCnn : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg'  _
    have hKbig : (2 * C * q + 1 : ℕ) ≤ K := hK_big
    have : (K : ℝ) ≥ 2 * (C : ℝ) * (q : ℝ) + 1 := by exact_mod_cast hKbig
    -- K ≤ 2C(q-1) = 2Cq - 2C ≤ 2Cq < 2Cq + 1 ≤ K, contradiction
    nlinarith [mul_nonneg hCnn (by linarith : (0 : ℝ) ≤ (q : ℝ) - 1)]

/-- Helper: gen_exists_bound for odd primes only.
    Same as gen_exists_bound but with the extra 3 ≤ p condition. -/
private theorem gen_exists_bound_odd (q : Nat)
    (h : ∀ p, Nat.Prime p → 3 ≤ p → p < q → ∃ k, genSeq 2 k = p) :
    ∃ N, ∀ p, Nat.Prime p → 3 ≤ p → p < q → ∃ m, m < N ∧ genSeq 2 m = p := by
  induction q with
  | zero => exact ⟨0, fun p _ _ hp => absurd hp (by omega)⟩
  | succ q' ih =>
    have h' : ∀ p, Nat.Prime p → 3 ≤ p → p < q' → ∃ k, genSeq 2 k = p :=
      fun p hp hp3 hpq => h p hp hp3 (by omega)
    obtain ⟨N', hN'⟩ := ih h'
    if hprime : Nat.Prime q' then
      if hge3 : 3 ≤ q' then
        obtain ⟨m, hm⟩ := h q' hprime hge3 (by omega)
        refine ⟨Nat.max N' (m + 1), fun p hp hp3 hpq => ?_⟩
        match Nat.lt_or_ge p q' with
        | .inl hlt =>
          obtain ⟨j, hj, hjseq⟩ := hN' p hp hp3 hlt
          exact ⟨j, lt_of_lt_of_le hj (Nat.le_max_left _ _), hjseq⟩
        | .inr hge_p =>
          have : p = q' := by omega
          subst this
          exact ⟨m, lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_max_right _ _), hm⟩
      else
        refine ⟨N', fun p hp hp3 hpq => ?_⟩
        have : p < q' := by omega
        exact hN' p hp hp3 this
    else
      refine ⟨N', fun p hp hp3 hpq => ?_⟩
      match Nat.lt_or_ge p q' with
      | .inl hlt => exact hN' p hp hp3 hlt
      | .inr hge_p =>
        exfalso; have : p = q' := by omega
        subst this; exact hprime hp

/-- **Weyl + walk cancellation → MC for standard EM (n=2).**

    For the standard EM sequence (n=2), seq 0 = 2 handles q=2.
    For q >= 3, q does not divide 2, so WeylHittingBridge gives either
    appearance (genSeq 2 j = q, hence seq(j+1) = q) or cofinal hitting.
    Cofinal hitting gives appearance via the gen_captures_target induction
    (modified: all primes in the gen sequence from 2 are odd, so the induction
    only needs primes >= 3, which all don't divide 2).

    **Status**: PROVED (from weyl_hitting_bridge_proved). -/
theorem cancel_weyl_implies_mc
    -- Walk character cancellation for n=2 (strong Weyl form, for q coprime to 2):
    (hcancel : ∀ (q : Nat) (hq : Nat.Prime q), ¬ (q ∣ 2) →
      ∀ (χ : Nat → ℂ), (∀ a, Complex.normSq (χ a) ≤ 1) →
      (χ 0 = 0) →
      (letI : NeZero q := ⟨hq.ne_zero⟩; ∑ a : ZMod q, χ (ZMod.val a) = 0) →
      ∀ (ε : ℝ), 0 < ε →
        ∃ K₀ : Nat, ∀ K : Nat, K₀ ≤ K → genWalkCharEnergy 2 K q χ ≤ (ε * K) ^ 2) :
    MullinConjecture := by
  -- Strong induction: suffices to show MC for all primes q ≤ B
  suffices ∀ B q, IsPrime q → q ≤ B → ∃ k, seq k = q by
    intro q hq; exact this q q hq (le_refl q)
  intro B
  induction B with
  | zero => intro q hq hle; exact absurd (Nat.Prime.one_lt (IsPrime.toNatPrime hq)) (by omega)
  | succ B ih =>
    intro q hq hle
    match Nat.lt_or_ge q (B + 1) with
    | .inl hlt => exact ih q hq (by omega)
    | .inr hge =>
      -- q = B + 1
      have hqp := IsPrime.toNatPrime hq
      by_cases hq2 : q = 2
      · exact ⟨0, by subst hq2; rfl⟩
      · have hndvd : ¬ (q ∣ 2) := by
          intro h; have hle := Nat.le_of_dvd (by norm_num) h
          have hge := hqp.two_le; omega
        have h_weyl := weyl_hitting_bridge_proved 2 Nat.squarefree_two (by norm_num)
          q hqp hndvd (hcancel q hqp hndvd)
        rcases h_weyl with ⟨j, hj⟩ | h_cofinal
        · exact ⟨j + 1, by rwa [← genSeq_two_eq_seq_succ]⟩
        · -- Cofinal hitting. Extract appearance.
          suffices ∃ k, genSeq 2 k = q by
            obtain ⟨k, hk⟩ := this
            exact ⟨k + 1, by rwa [← genSeq_two_eq_seq_succ]⟩
          -- By IH, every odd prime p < q appears as genSeq 2 _
          have ih_odd : ∀ p, Nat.Prime p → 3 ≤ p → p < q → ∃ k, genSeq 2 k = p := by
            intro p hp hp3 hpq
            obtain ⟨m, hm⟩ := ih p hp.toIsPrime (by omega)
            -- seq m = p, and seq 0 = 2 ≠ p (since p ≥ 3), so m ≥ 1
            have hm_pos : 0 < m := by
              by_contra h_zero; push_neg at h_zero
              have : m = 0 := by omega
              subst this; change seq 0 = p at hm; rw [seq_zero] at hm; omega
            -- genSeq 2 (m-1) = seq m = p
            refine ⟨m - 1, ?_⟩
            rw [genSeq_two_eq_seq_succ, show m - 1 + 1 = m from by omega, hm]
          -- genSeq 2 k ≥ 3 always (genProd 2 k is even, so genProd 2 k + 1 is odd)
          have hgen_ge3 : ∀ k, 3 ≤ genSeq 2 k := by
            intro k
            have hprime := genSeq_prime (by norm_num : 1 ≤ 2) k
            have heven : 2 ∣ genProd 2 k := start_dvd_genProd 2 k
            have hodd : ¬ 2 ∣ genProd 2 k + 1 := by omega
            have h2ne : genSeq 2 k ≠ 2 := by
              intro heq; rw [genSeq_def] at heq
              have := Nat.minFac_dvd (genProd 2 k + 1)
              rw [heq] at this; exact hodd this
            have := hprime.two_le; omega
          -- Bound the odd prime witnesses
          obtain ⟨N, hN⟩ := gen_exists_bound_odd q ih_odd
          obtain ⟨k, hk_ge, hhit_k⟩ := h_cofinal N
          rw [genWalkZ_eq_neg_one_iff] at hhit_k
          -- Key: genSeq 2 k ≤ q (from minFac ≤ q since q | genProd 2 k + 1)
          have hle_q : genSeq 2 k ≤ q := by
            rw [genSeq_def]; exact Nat.minFac_le_of_dvd hqp.two_le hhit_k
          -- Key: genSeq 2 k ≥ q (all odd primes < q already taken at steps < k)
          have hge_q : q ≤ genSeq 2 k := by
            by_contra hlt; push_neg at hlt
            have hprime_s := genSeq_prime (by norm_num : 1 ≤ 2) k
            have hge3_k := hgen_ge3 k
            obtain ⟨j, hjk, hseqj⟩ := hN (genSeq 2 k) hprime_s hge3_k hlt
            have hinj := (genSeq_injective Nat.squarefree_two) hseqj
            -- j < N ≤ k and j = k: contradiction
            omega
          -- genSeq 2 k = q
          exact ⟨k, by omega⟩

/-- **Full JSE to MC chain (honest version with explicit gap).**

    This composes all links in the JSE → MC chain:
    - JSE → multiplier cancellation for a.a. squarefree n (PROVED)
    - MultCancelToWalkCancel → walk cancellation for all squarefree n (open)
    - cancel_weyl_implies_mc → MC (PROVED)

    The two open hypotheses are:
    1. JointStepEquidist (JSE) — hard, requires BV/Siegel-Walfisz infrastructure
    2. MultCancelToWalkCancel — hard, equivalent to CCSB/CME (Dead End #117)

    Note: JSE is included for documentation (it motivates why multiplier
    cancellation should hold) but is logically redundant here —
    MultCancelToWalkCancel alone suffices since it gives walk cancellation
    unconditionally. The density-based multiplier cancellation from JSE
    cannot be extracted to pointwise bounds for specific n=2, so the
    conditional form (multiplier→walk transfer) would require an additional
    pointwise hypothesis. The unconditional form avoids this subtlety.

    WeylHittingBridge and PerChiCancellationBridge are both PROVED. -/
theorem jse_transfer_implies_mc
    (_hjse : JointStepEquidist)
    (htransfer : MultCancelToWalkCancel) :
    MullinConjecture :=
  cancel_weyl_implies_mc (fun q hq hndvd χ hχb hχ0 hχs ε hε =>
    htransfer 2 Nat.squarefree_two (by norm_num) q hq hndvd χ hχb hχ0 hχs ε hε)

end JSEToGenMC

end
