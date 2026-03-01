import EM.EnsembleFirstMoment

/-!
# CRT Equidistribution of Generalized Accumulators

This file establishes the **CRT equidistribution framework** for averaging over
squarefree starting points. The key objects are:

1. **Counting functions**: `sqfreeAccumCount X k r a` counts squarefree n in [1,X]
   with genProd n k in a given residue class mod r.
2. **Squarefree residue equidistribution**: a standard ANT result that squarefree
   integers equidistribute in coprime residue classes.
3. **CRT propagation**: if genProd n k equidistributes mod r, then so does
   genProd n (k+1), by `crt_multiplier_invariance` and injectivity.
4. **Multiplier equidistribution**: genSeq n k equidistributes mod q when averaged
   over squarefree starting points.

## Mathematical Background

The generalized EM accumulator `genProd n k` satisfies:
- genProd n 0 = n
- genProd n (k+1) = genProd n k * genSeq n k
- genSeq n k = minFac(genProd n k + 1)

By `crt_multiplier_invariance` (PROVED in MullinCRT.lean), the multiplier
genSeq n k = minFac(genProd n k + 1) depends only on the residues of
genProd n k modulo primes r != q, not on its residue mod q. This CRT
independence is the structural basis for equidistribution propagation.

## Main Results

### Definitions
* `sqfreeAccumCount`       -- count of squarefree n with genProd n k in a residue class
* `sqfreeSeqCount`         -- count of squarefree n with genSeq n k in a residue class
* `sqfreeAccumDensity`     -- density of squarefree n with genProd n k in a residue class
* `sqfreeSeqDensity`       -- density of squarefree n with genSeq n k in a residue class
* `ensembleCharMean`       -- ensemble average of a character applied to genSeq residues

### Open Hypotheses
* `SquarefreeResidueEquidist`           -- squarefree integers equidistribute mod primes
* `CRTPropagationStep`                  -- equidist at step k implies equidist at step k+1
* `AccumulatorEquidistPropagation`      -- genProd n k equidistributes for all k
* `EnsembleMultiplierEquidist`          -- genSeq n k equidistributes for all k
* `AccumEquidistImpliesMultEquidist`    -- AEP implies EME (via PE)
### Proved Theorems
* `sqfreeAccumCount_le_sqfreeCount`     -- counting bound
* `sqfreeSeqCount_le_sqfreeCount`       -- counting bound
* `sqfreeAccumDensity_nonneg`           -- density is non-negative
* `sqfreeAccumDensity_le_one`           -- density is at most 1
* `sqfreeSeqDensity_nonneg`             -- density is non-negative
* `sqfreeSeqDensity_le_one`             -- density is at most 1
* `sqfreeResidueEquidist_implies_accumEquidist_zero` -- SRE implies base case k=0
* `sre_crt_implies_accum_equidist`      -- SRE + CRTPropStep => AEP (by induction)
* `sre_crt_bridge_implies_mult_equidist`-- SRE + CRTPropStep + bridge => EME
* `ensembleCharMean_eq_density_sum`     -- density decomposition identity
* `ensemble_mult_equidist_implies_char_mean_zero` -- EME => vanishing char means (PROVED)
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Counting Functions -/

section Counting

/-- Count of squarefree n in [1,X] with genProd n k in residue class a mod r.
    At k=0, genProd n 0 = n, so this counts squarefree n in [1,X] with n ≡ a (mod r). -/
def sqfreeAccumCount (X k r : Nat) (a : ZMod r) : Nat :=
  ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ (genProd n k : ZMod r) = a)).card

/-- Count of squarefree n in [1,X] with genSeq n k in residue class a mod q.
    This counts starting points whose k-th generalized EM prime falls in a given
    residue class. -/
def sqfreeSeqCount (X k q : Nat) (a : ZMod q) : Nat :=
  ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ (genSeq n k : ZMod q) = a)).card

/-- The density of squarefree n in [1,X] with genProd n k ≡ a (mod r). -/
def sqfreeAccumDensity (X k r : Nat) (a : ZMod r) : ℝ :=
  (sqfreeAccumCount X k r a : ℝ) / (sqfreeCount X : ℝ)

/-- The density of squarefree n in [1,X] with genSeq n k ≡ a (mod q). -/
def sqfreeSeqDensity (X k q : Nat) (a : ZMod q) : ℝ :=
  (sqfreeSeqCount X k q a : ℝ) / (sqfreeCount X : ℝ)

end Counting

/-! ## Basic Properties of Counting Functions -/

section CountingProps

/-- The accumulator count is bounded by the total squarefree count. -/
theorem sqfreeAccumCount_le_sqfreeCount (X k r : Nat) (a : ZMod r) :
    sqfreeAccumCount X k r a ≤ sqfreeCount X := by
  unfold sqfreeAccumCount sqfreeCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.1⟩

/-- The sequence count is bounded by the total squarefree count. -/
theorem sqfreeSeqCount_le_sqfreeCount (X k q : Nat) (a : ZMod q) :
    sqfreeSeqCount X k q a ≤ sqfreeCount X := by
  unfold sqfreeSeqCount sqfreeCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.1⟩

/-- The accumulator density is non-negative. -/
theorem sqfreeAccumDensity_nonneg (X k r : Nat) (a : ZMod r) :
    0 ≤ sqfreeAccumDensity X k r a := by
  unfold sqfreeAccumDensity
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The accumulator density is at most 1. -/
theorem sqfreeAccumDensity_le_one (X k r : Nat) (a : ZMod r) :
    sqfreeAccumDensity X k r a ≤ 1 := by
  unfold sqfreeAccumDensity
  by_cases h : sqfreeCount X = 0
  · simp [h]
  · rw [div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))]
    exact Nat.cast_le.mpr (sqfreeAccumCount_le_sqfreeCount X k r a)

/-- The sequence density is non-negative. -/
theorem sqfreeSeqDensity_nonneg (X k q : Nat) (a : ZMod q) :
    0 ≤ sqfreeSeqDensity X k q a := by
  unfold sqfreeSeqDensity
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The sequence density is at most 1. -/
theorem sqfreeSeqDensity_le_one (X k q : Nat) (a : ZMod q) :
    sqfreeSeqDensity X k q a ≤ 1 := by
  unfold sqfreeSeqDensity
  by_cases h : sqfreeCount X = 0
  · simp [h]
  · rw [div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))]
    exact Nat.cast_le.mpr (sqfreeSeqCount_le_sqfreeCount X k q a)

end CountingProps

/-! ## Squarefree Residue Equidistribution -/

section SquarefreeEquidist

/-- **Squarefree Residue Equidistribution**: for prime r and nonzero residue a,
    the density of squarefree n with n ≡ a (mod r) among all squarefree integers
    tends to 1/(r-1).

    This is a standard result in analytic number theory. The density of squarefree
    integers in the residue class a (mod r) is (6/pi^2) * (1/(r-1)) * (some local
    factor), but normalized by the total squarefree density (6/pi^2), the relative
    density is 1/(r-1) for nonzero residues mod a prime r.

    At k=0, genProd n 0 = n, so `sqfreeAccumCount X 0 r a` counts exactly the
    squarefree n in [1,X] with n ≡ a (mod r). This is the base case for the
    inductive equidistribution propagation.

    **Status**: open hypothesis (standard ANT, not in Mathlib). -/
def SquarefreeResidueEquidist : Prop :=
  ∀ (r : Nat), Nat.Prime r → ∀ (a : ZMod r), a ≠ 0 →
    Filter.Tendsto
      (fun X : Nat => sqfreeAccumDensity X 0 r a)
      Filter.atTop
      (nhds (1 / ((r : ℝ) - 1)))

end SquarefreeEquidist

/-! ## CRT Propagation -/

section CRTPropagation

/-- **Accumulator Equidistribution Propagation**: for each prime r, step k, and
    nonzero residue a mod r, the density of squarefree n with genProd n k ≡ a (mod r)
    tends to 1/(r-1).

    The base case (k=0) is `SquarefreeResidueEquidist`: genProd n 0 = n equidistributes.

    The inductive step uses `crt_multiplier_invariance`: genProd n (k+1) = genProd n k *
    genSeq n k, where genSeq n k = minFac(genProd n k + 1). The multiplier genSeq n k
    depends only on the residues of genProd n k mod primes other than r (by CRT
    invariance). As n varies over squarefree integers, the mod-r and non-mod-r
    coordinates of genProd n k are approximately independent (by CRT for squarefree
    numbers). So multiplying by the "r-independent" factor genSeq n k preserves
    equidistribution mod r.

    **Status**: open hypothesis, provable from SRE + CRT decorrelation + PE. -/
def AccumulatorEquidistPropagation : Prop :=
  ∀ (r : Nat), Nat.Prime r → ∀ (k : Nat), ∀ (a : ZMod r), a ≠ 0 →
    Filter.Tendsto
      (fun X : Nat => sqfreeAccumDensity X k r a)
      Filter.atTop
      (nhds (1 / ((r : ℝ) - 1)))

/-- **SRE implies the base case**: SquarefreeResidueEquidist gives
    AccumulatorEquidistPropagation at k = 0.

    At k=0, genProd n 0 = n, so the accumulator counting function coincides
    with the squarefree residue counting function, and the result is immediate. -/
theorem sqfreeResidueEquidist_implies_accumEquidist_zero
    (hsre : SquarefreeResidueEquidist) (r : Nat) (hr : Nat.Prime r)
    (a : ZMod r) (ha : a ≠ 0) :
    Filter.Tendsto
      (fun X : Nat => sqfreeAccumDensity X 0 r a)
      Filter.atTop
      (nhds (1 / ((r : ℝ) - 1))) :=
  hsre r hr a ha

/-- **CRT Propagation Step**: the inductive hypothesis that equidistribution at
    step k implies equidistribution at step k+1. This captures the key CRT argument:

    genProd n (k+1) = genProd n k * genSeq n k, where the multiplier genSeq n k
    depends on genProd n k only through its non-mod-r coordinates (by
    `crt_multiplier_invariance`). When genProd n k equidistributes mod r and
    independently in the other coordinates, the product equidistributes mod r.

    **Status**: open hypothesis (the main content of the CRT propagation). -/
def CRTPropagationStep : Prop :=
  ∀ (r : Nat), Nat.Prime r → ∀ (k : Nat),
    (∀ (a : ZMod r), a ≠ 0 →
      Filter.Tendsto
        (fun X : Nat => sqfreeAccumDensity X k r a)
        Filter.atTop
        (nhds (1 / ((r : ℝ) - 1)))) →
    (∀ (a : ZMod r), a ≠ 0 →
      Filter.Tendsto
        (fun X : Nat => sqfreeAccumDensity X (k + 1) r a)
        Filter.atTop
        (nhds (1 / ((r : ℝ) - 1))))

/-- **SRE + CRTPropagationStep → AccumulatorEquidistPropagation.**
    The base case is SRE (k=0), and the inductive step is CRTPropagationStep.
    Together they give equidistribution for all k by induction. -/
theorem sre_crt_implies_accum_equidist
    (hsre : SquarefreeResidueEquidist) (hcrt : CRTPropagationStep) :
    AccumulatorEquidistPropagation := by
  intro r hr k
  induction k with
  | zero => exact hsre r hr
  | succ k ih => exact hcrt r hr k ih

end CRTPropagation

/-! ## Ensemble Multiplier Equidistribution -/

section MultiplierEquidist

/-- **Ensemble Multiplier Equidistribution**: for each prime q, step k, and
    nonzero residue a mod q, the density of squarefree n with genSeq n k ≡ a (mod q)
    tends to 1/(q-1).

    This says that the k-th generalized EM prime equidistributes in coprime
    residue classes when averaged over squarefree starting points.

    The proof strategy: by AccumulatorEquidistPropagation, genProd n k
    equidistributes mod all primes. So genProd n k + 1 is approximately a
    random shifted squarefree number (by `genProd_succ_in_shifted_squarefree`),
    and minFac of such numbers equidistributes mod q (by PE).

    **Status**: open hypothesis, follows from AccumulatorEquidistPropagation + PE. -/
def EnsembleMultiplierEquidist : Prop :=
  ∀ (q : Nat), Nat.Prime q → ∀ (k : Nat), ∀ (a : ZMod q), a ≠ 0 →
    Filter.Tendsto
      (fun X : Nat => sqfreeSeqDensity X k q a)
      Filter.atTop
      (nhds (1 / ((q : ℝ) - 1)))

/-- **AccumulatorEquidistPropagation → EnsembleMultiplierEquidist** (modulo PE).

    The multiplier genSeq n k = minFac(genProd n k + 1). If genProd n k
    equidistributes mod all primes (from AEP), then genProd n k + 1 is a
    random-looking shifted squarefree number, and PE gives equidistribution
    of its minFac in coprime residue classes.

    We state this as an open hypothesis since the PE bridge requires the
    population equidistribution framework (from WeakErgodicity.lean).

    **Status**: open hypothesis. -/
def AccumEquidistImpliesMultEquidist : Prop :=
  AccumulatorEquidistPropagation → EnsembleMultiplierEquidist

/-- **Full chain**: SRE + CRTPropagationStep + AccumEquidistImpliesMultEquidist
    → EnsembleMultiplierEquidist. -/
theorem sre_crt_bridge_implies_mult_equidist
    (hsre : SquarefreeResidueEquidist)
    (hcrt : CRTPropagationStep)
    (hbridge : AccumEquidistImpliesMultEquidist) :
    EnsembleMultiplierEquidist :=
  hbridge (sre_crt_implies_accum_equidist hsre hcrt)

end MultiplierEquidist

/-! ## Connection to Character Sums and Step Decorrelation -/

section CharMean

/-- The ensemble average of a character applied to genSeq residues.
    For a function chi : ZMod q -> C representing a Dirichlet character,
    this averages chi(genSeq n k mod q) over squarefree n in [1,X]. -/
def ensembleCharMean (X k q : Nat) (chi : ZMod q → ℂ) : ℂ :=
  (∑ n ∈ (Finset.Icc 1 X).filter Squarefree, chi (genSeq n k : ZMod q)) /
    ((sqfreeCount X : ℝ) : ℂ)

/-- **Ensemble multiplier equidistribution implies vanishing character means**
    for nontrivial characters.

    If genSeq n k equidistributes mod q over squarefree starting points, then
    for any function chi : ZMod q -> C satisfying:
    (1) chi(0) = 0 (vanishes on the zero residue), and
    (2) ∑ a : ZMod q, chi(a) = 0 (character sum vanishes — nontriviality),
    the ensemble average of chi(genSeq n k) vanishes.

    The connection: if the density of {n : genSeq n k ≡ a (mod q)} → 1/(q-1)
    for each nonzero a, then by the density decomposition
    (`ensembleCharMean_eq_density_sum`):

    E_n[chi(genSeq n k)] = ∑_a density(a) * chi(a)

    The a = 0 term vanishes since chi(0) = 0. For a ≠ 0, density(a) → 1/(q-1)
    by EME, so the sum converges to (1/(q-1)) * ∑_{a≠0} chi(a). Since chi(0) = 0,
    ∑_{a≠0} chi(a) = ∑_a chi(a) = 0. Hence the limit is 0.

    Note: the trivial character (chi = 1 on nonzero residues) does NOT satisfy
    condition (2), so this statement correctly excludes it (the trivial character
    mean → 1, not 0).

    **Status**: PROVED (ensemble_mult_equidist_implies_char_mean_zero). -/
def EnsembleMultEquidistImpliesCharMeanZero : Prop :=
  EnsembleMultiplierEquidist →
    ∀ (q : Nat) (hq : Nat.Prime q), ∀ (k : Nat),
    ∀ (chi : ZMod q → ℂ),
      chi (0 : ZMod q) = 0 →
      (letI : NeZero q := ⟨hq.ne_zero⟩; ∑ a : ZMod q, chi a = 0) →
      Filter.Tendsto
        (fun X : Nat => ‖ensembleCharMean X k q chi‖)
        Filter.atTop
        (nhds 0)

/-- **Density decomposition**: the ensemble character mean decomposes as a
    weighted sum over residue classes.

    E_n[chi(genSeq n k)] = ∑_a density(genSeq n k ≡ a) * chi(a).

    This algebraic identity holds exactly (no limits needed) and connects
    counting functions to character averages.

    The proof works by partitioning the squarefree set S by residue class
    of genSeq n k mod q: each n falls into exactly one class, chi is
    constant on each class, so the sum factorizes. -/
theorem ensembleCharMean_eq_density_sum (X k q : Nat) [NeZero q]
    (chi : ZMod q → ℂ) :
    ensembleCharMean X k q chi =
      ∑ a : ZMod q,
        ((sqfreeSeqCount X k q a : ℝ) : ℂ) / ((sqfreeCount X : ℝ) : ℂ) * chi a := by
  unfold ensembleCharMean sqfreeSeqCount sqfreeCount
  set S := (Finset.Icc 1 X).filter Squarefree
  -- Decompose the sum over S by residue class of genSeq n k mod q
  have hdecomp : ∑ n ∈ S, chi (genSeq n k : ZMod q) =
      ∑ a : ZMod q, ∑ n ∈ S.filter (fun n => (genSeq n k : ZMod q) = a),
        chi (genSeq n k : ZMod q) := by
    rw [← Finset.sum_biUnion]
    · congr 1
      ext n
      simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter]
      constructor
      · intro hn
        exact ⟨(genSeq n k : ZMod q), trivial, hn, rfl⟩
      · intro ⟨_, _, hn, _⟩
        exact hn
    · intro a _ b _ hab
      simp only [Finset.disjoint_left, Finset.mem_filter]
      intro n ⟨_, ha'⟩ ⟨_, hb'⟩
      exact hab (ha'.symm.trans hb')
  -- Simplify each inner sum: chi(genSeq n k) = chi(a) on the a-fiber
  have hsimp : ∀ a : ZMod q,
      ∑ n ∈ S.filter (fun n => (genSeq n k : ZMod q) = a),
        chi (genSeq n k : ZMod q) =
      ↑(S.filter (fun n => (genSeq n k : ZMod q) = a)).card * chi a := by
    intro a
    have hsub : ∀ n ∈ S.filter (fun n => (genSeq n k : ZMod q) = a),
        chi (genSeq n k : ZMod q) = chi a := by
      intro n hn
      simp only [Finset.mem_filter] at hn
      rw [hn.2]
    rw [Finset.sum_congr rfl hsub, Finset.sum_const, nsmul_eq_mul]
  -- Rewrite using the fiber count
  have hcount : ∀ a : ZMod q,
      (S.filter (fun n => (genSeq n k : ZMod q) = a)).card =
      ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧
        (genSeq n k : ZMod q) = a)).card := by
    intro a; congr 1; ext n
    simp only [Finset.mem_filter, S, and_assoc]
  rw [hdecomp]
  -- Now LHS = (∑ a, card_a * chi a) / c, RHS = ∑ a, (card_a / c) * chi a
  simp_rw [hsimp, hcount]
  rw [Finset.sum_div]
  congr 1; ext a
  push_cast
  rw [div_mul_eq_mul_div]

/-- **Rewrite density_sum using sqfreeSeqDensity**: the ensemble character mean
    equals ∑_a (sqfreeSeqDensity X k q a : ℂ) * chi a. -/
private theorem ensembleCharMean_eq_ofReal_density_sum (X k q : Nat) [NeZero q]
    (chi : ZMod q → ℂ) :
    ensembleCharMean X k q chi =
      ∑ a : ZMod q,
        ((sqfreeSeqDensity X k q a : ℝ) : ℂ) * chi a := by
  rw [ensembleCharMean_eq_density_sum]
  congr 1; ext a
  simp only [sqfreeSeqDensity]
  rw [Complex.ofReal_div]

/-- **EME implies vanishing character means for nontrivial characters.** PROVED.

    Proof: By the density decomposition, ensembleCharMean X k q chi =
    ∑_a (density(a) : ℂ) * chi(a). The a = 0 term vanishes since chi(0) = 0.
    For a ≠ 0, density(a) → 1/(q-1) by EME. By `tendsto_finset_sum`, the sum
    converges to ∑_a limit(a) * chi(a). Since limit(0) * chi(0) = 0 and
    ∑_{a≠0} limit(a) * chi(a) = (1/(q-1)) * ∑_{a≠0} chi(a) = (1/(q-1)) * 0 = 0,
    the total limit is 0, and so ‖ensembleCharMean‖ → 0. -/
theorem ensemble_mult_equidist_implies_char_mean_zero :
    EnsembleMultEquidistImpliesCharMeanZero := by
  intro heme q hq k chi hchi0 hchisum
  haveI : NeZero q := ⟨hq.ne_zero⟩
  -- Set the common limit constant
  set c : ℂ := ((1 / ((q : ℝ) - 1) : ℝ) : ℂ)
  -- Define the limit value for each a : ZMod q as c * chi a
  -- Note: for a = 0, this gives c * chi 0 = c * 0 = 0 (by hchi0)
  -- For a ≠ 0, this is the genuine limit from EME
  set L : ZMod q → ℂ := fun a => c * chi a
  -- Step 1: show ∑ a, L a = 0
  have hLsum : ∑ a : ZMod q, L a = 0 := by
    simp only [L, ← Finset.mul_sum]
    rw [hchisum, mul_zero]
  -- Step 2: show each term converges
  have hterm : ∀ a : ZMod q,
      Filter.Tendsto
        (fun X : Nat => ((sqfreeSeqDensity X k q a : ℝ) : ℂ) * chi a)
        Filter.atTop (nhds (L a)) := by
    intro a
    by_cases ha : a = 0
    · -- a = 0: chi(0) = 0, so the term is always 0
      simp only [ha, hchi0, mul_zero, L]
      exact tendsto_const_nhds
    · -- a ≠ 0: density(a) → 1/(q-1) by EME
      simp only [L]
      have hd := heme q hq k a ha
      -- Lift ℝ tendsto to ℂ tendsto via continuous_ofReal
      have hd_C : Filter.Tendsto
          (fun X : Nat => ((sqfreeSeqDensity X k q a : ℝ) : ℂ))
          Filter.atTop (nhds c) := by
        exact (Complex.continuous_ofReal.tendsto _).comp hd
      exact Filter.Tendsto.mul hd_C tendsto_const_nhds
  -- Step 3: use tendsto_finset_sum to get ∑ converges to ∑ L
  have hsum_tends : Filter.Tendsto
      (fun X : Nat => ∑ a : ZMod q, ((sqfreeSeqDensity X k q a : ℝ) : ℂ) * chi a)
      Filter.atTop (nhds (∑ a : ZMod q, L a)) :=
    tendsto_finset_sum Finset.univ (fun a _ => hterm a)
  -- Step 4: combine: ensembleCharMean → 0
  rw [hLsum] at hsum_tends
  have hcm_tends : Filter.Tendsto
      (fun X : Nat => ensembleCharMean X k q chi)
      Filter.atTop (nhds 0) := by
    rw [show (fun X => ensembleCharMean X k q chi) =
        (fun X => ∑ a : ZMod q, ((sqfreeSeqDensity X k q a : ℝ) : ℂ) * chi a)
      from funext (fun X => ensembleCharMean_eq_ofReal_density_sum X k q chi)]
    exact hsum_tends
  -- Step 5: ‖ensembleCharMean‖ → 0
  exact tendsto_zero_iff_norm_tendsto_zero.mp hcm_tends

end CharMean

/-! ## Summary of Proof Chain

The CRT equidistribution framework establishes the following chain:

```
SquarefreeResidueEquidist (standard ANT)
  + CRTPropagationStep (CRT independence of multiplier from mod-r coordinate)
  → AccumulatorEquidistPropagation (genProd n k equidistributes mod r for all k)

AccumulatorEquidistPropagation
  + PE (population equidistribution of minFac)
  → EnsembleMultiplierEquidist (genSeq n k equidistributes mod q for all k)

EnsembleMultiplierEquidist
  + character orthogonality
  → vanishing character means (E_n[chi(genSeq n k)] → 0)
  → StepDecorrelation (from EnsembleDecorrelation.lean)
  → CharSumVarianceBound
  → EnsembleCharSumConcentration
```

The CRT propagation step is the key new ingredient: it uses
`crt_multiplier_invariance` (PROVED) to show that equidistribution is preserved
under the genProd → genProd * genSeq multiplication. The non-mod-r coordinates
of genProd n k vary as n varies (by `genSeq_injective`), making the multiplier
genSeq n k = minFac(genProd n k + 1) effectively independent of the mod-r
coordinate.
-/

end
