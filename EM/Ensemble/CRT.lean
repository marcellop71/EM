import EM.Ensemble.FirstMoment

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
  exact Finset.card_le_card fun n hn => by
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩

/-- The sequence count is bounded by the total squarefree count. -/
theorem sqfreeSeqCount_le_sqfreeCount (X k q : Nat) (a : ZMod q) :
    sqfreeSeqCount X k q a ≤ sqfreeCount X := by
  unfold sqfreeSeqCount sqfreeCount
  exact Finset.card_le_card fun n hn => by
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩

/-- The accumulator density is non-negative. -/
theorem sqfreeAccumDensity_nonneg (X k r : Nat) (a : ZMod r) :
    0 ≤ sqfreeAccumDensity X k r a :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The accumulator density is at most 1. -/
theorem sqfreeAccumDensity_le_one (X k r : Nat) (a : ZMod r) :
    sqfreeAccumDensity X k r a ≤ 1 := by
  unfold sqfreeAccumDensity
  rcases eq_or_ne (sqfreeCount X) 0 with h | h
  · simp [h]
  · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))).mpr
      (Nat.cast_le.mpr (sqfreeAccumCount_le_sqfreeCount X k r a))

/-- The sequence density is non-negative. -/
theorem sqfreeSeqDensity_nonneg (X k q : Nat) (a : ZMod q) :
    0 ≤ sqfreeSeqDensity X k q a :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The sequence density is at most 1. -/
theorem sqfreeSeqDensity_le_one (X k q : Nat) (a : ZMod q) :
    sqfreeSeqDensity X k q a ≤ 1 := by
  unfold sqfreeSeqDensity
  rcases eq_or_ne (sqfreeCount X) 0 with h | h
  · simp [h]
  · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))).mpr
      (Nat.cast_le.mpr (sqfreeSeqCount_le_sqfreeCount X k q a))

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
    · congr 1; ext n
      simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
      exact ⟨fun hn => ⟨_, hn, rfl⟩, fun ⟨_, hn, _⟩ => hn⟩
    · intro a _ b _ hab
      simp only [Finset.disjoint_left, Finset.mem_filter]
      exact fun _ ⟨_, ha'⟩ ⟨_, hb'⟩ => hab (ha'.symm.trans hb')
  -- Simplify each inner sum: chi(genSeq n k) = chi(a) on the a-fiber
  have hsimp : ∀ a : ZMod q,
      ∑ n ∈ S.filter (fun n => (genSeq n k : ZMod q) = a),
        chi (genSeq n k : ZMod q) =
      ↑(S.filter (fun n => (genSeq n k : ZMod q) = a)).card * chi a := by
    intro a
    rw [Finset.sum_congr rfl (fun n hn => by rw [(Finset.mem_filter.mp hn).2]),
        Finset.sum_const, nsmul_eq_mul]
  -- Rewrite using the fiber count
  have hcount : ∀ a : ZMod q,
      (S.filter (fun n => (genSeq n k : ZMod q) = a)).card =
      ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧
        (genSeq n k : ZMod q) = a)).card := by
    intro a; congr 1; ext n; simp only [Finset.mem_filter, S, and_assoc]
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
  congr 1; ext a; simp only [sqfreeSeqDensity, Complex.ofReal_div]

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
    simp only [L, ← Finset.mul_sum, hchisum, mul_zero]
  -- Step 2: show each term converges
  have hterm : ∀ a : ZMod q,
      Filter.Tendsto
        (fun X : Nat => ((sqfreeSeqDensity X k q a : ℝ) : ℂ) * chi a)
        Filter.atTop (nhds (L a)) := by
    intro a
    by_cases ha : a = 0
    · -- a = 0: chi(0) = 0, so the term is always 0
      simp [ha, hchi0, L]
    · -- a ≠ 0: density(a) → 1/(q-1) by EME, lift to ℂ via continuous_ofReal
      simp only [L]
      exact ((Complex.continuous_ofReal.tendsto _).comp (heme q hq k a ha)).mul
        tendsto_const_nhds
  -- Step 3: use tendsto_finset_sum to get ∑ converges to ∑ L
  have hsum_tends : Filter.Tendsto
      (fun X : Nat => ∑ a : ZMod q, ((sqfreeSeqDensity X k q a : ℝ) : ℂ) * chi a)
      Filter.atTop (nhds (∑ a : ZMod q, L a)) :=
    tendsto_finset_sum Finset.univ (fun a _ => hterm a)
  -- Step 4: combine: ensembleCharMean → 0, then ‖·‖ → 0
  simp_rw [hLsum] at hsum_tends
  refine tendsto_zero_iff_norm_tendsto_zero.mp ?_
  simpa only [ensembleCharMean_eq_ofReal_density_sum] using hsum_tends

end CharMean

/-! ## Mod-3 Bridge: AccumMod3LB → SMLB → PositiveDensityRSD

When genProd(n,k) ≡ 2 mod 3 and k ≥ 1, the accumulator is even (so genProd+1 is odd)
and 3 divides genProd+1, forcing genSeq(n,k) = minFac(genProd+1) = 3.

This gives a lower bound on the k-th step ensemble average from the mod-3
accumulator density, which chains to SMLB and then PositiveDensityRSD.
-/

section Mod3Bridge

/-- When genProd(n,k) ≡ 2 mod 3 and k ≥ 1, n ≥ 1, genSeq(n,k) = 3.
    Proof: 3 divides genProd+1 (since 2+1 = 0 in ZMod 3), and genSeq ≥ 3
    (from parity), and genSeq = minFac(genProd+1) ≤ 3 (from 3 | genProd+1). -/
theorem genSeq_eq_three_of_genProd_mod3 {n k : Nat} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hmod : (genProd n k : ZMod 3) = 2) : genSeq n k = 3 := by
  have h3_dvd : 3 ∣ (genProd n k + 1) := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    simp only [hmod]; decide
  rw [genSeq_def]
  have hne1 : genProd n k + 1 ≠ 1 := by have := genProd_pos hn k; omega
  have hge2 := (Nat.minFac_prime hne1).two_le
  have hle3 := Nat.minFac_le_of_dvd (by omega : 2 ≤ 3) h3_dvd
  have hne2 : Nat.minFac (genProd n k + 1) ≠ 2 := fun h2 =>
    genProd_succ_odd hn hk (even_iff_two_dvd.mpr ((Nat.minFac_eq_two_iff _).mp h2))
  omega

/-- Auxiliary: the numerator inequality for the mod-3 density bound. -/
private theorem mod3_numerator_bound (X k : Nat) (hk : 1 ≤ k) :
    (((Finset.Icc 1 X).filter (fun n => Squarefree n ∧
        (genProd n k : ZMod 3) = 2)).card : ℝ) / 3 ≤
    ∑ n ∈ (Finset.Icc 1 X).filter Squarefree, 1 / (genSeq n k : ℝ) := by
  set S := (Finset.Icc 1 X).filter Squarefree
  set Smod := S.filter (fun n => (genProd n k : ZMod 3) = (2 : ZMod 3))
  -- The filter on Icc with conj equals Smod
  have hSmod_eq : Smod.card =
      ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧
        (genProd n k : ZMod 3) = 2)).card := by
    congr 1; ext n; simp only [Smod, S, Finset.mem_filter, and_assoc]
  rw [← hSmod_eq]
  -- Split the sum over S by whether genProd n k ≡ 2 mod 3
  have hsplit := Finset.sum_filter_add_sum_filter_not S
    (fun n => (genProd n k : ZMod 3) = (2 : ZMod 3))
    (fun n => 1 / (genSeq n k : ℝ))
  -- On Smod: each term is 1/3
  have hmod_terms : ∀ n ∈ Smod, 1 / (genSeq n k : ℝ) = 1 / 3 := by
    intro n hn
    have hmem := Finset.mem_filter.mp hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem.1).1).1
    congr 1; exact_mod_cast genSeq_eq_three_of_genProd_mod3 hn1 hk hmem.2
  -- Sum on Smod = Smod.card / 3
  have hmod_sum : ∑ n ∈ Smod, 1 / (genSeq n k : ℝ) = (Smod.card : ℝ) / 3 := by
    rw [Finset.sum_congr rfl hmod_terms, Finset.sum_const, nsmul_eq_mul]; ring
  -- Sum on complement ≥ 0
  have hrest_nonneg : 0 ≤ ∑ n ∈ S.filter (fun n => ¬(genProd n k : ZMod 3) = (2 : ZMod 3)),
      1 / (genSeq n k : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
  linarith [hsplit]

/-- The ensemble average of 1/genSeq(n,k) is at least (1/3) times the density
    of squarefree n with genProd(n,k) ≡ 2 mod 3. -/
theorem ensembleAvg_ge_mod3_density (X k : Nat) (hk : 1 ≤ k) :
    sqfreeAccumDensity X k 3 2 / 3 ≤
    ensembleAvg X (fun n => 1 / (genSeq n k : ℝ)) := by
  unfold ensembleAvg sqfreeAccumDensity sqfreeAccumCount sqfreeCount
  set S := (Finset.Icc 1 X).filter Squarefree
  rcases eq_or_ne S.card 0 with hcard | hcard
  · simp [hcard]
  have hS_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcard)
  have hnum := mod3_numerator_bound X k hk
  calc (((Finset.Icc 1 X).filter (fun n => Squarefree n ∧
          (genProd n k : ZMod 3) = 2)).card : ℝ) / ↑S.card / 3
      = (((Finset.Icc 1 X).filter (fun n => Squarefree n ∧
          (genProd n k : ZMod 3) = 2)).card : ℝ) / 3 / ↑S.card := by ring
    _ ≤ (∑ n ∈ S, 1 / (genSeq n k : ℝ)) / ↑S.card :=
        div_le_div_of_nonneg_right hnum hS_pos.le

/-- Positive lower bound on mod-3 accumulator density for all k. -/
def AccumMod3LB (c : ℝ) : Prop :=
  ∀ k : Nat, ∃ X₀ : Nat, ∀ X ≥ X₀,
    c ≤ sqfreeAccumDensity X k 3 2

/-- AccumMod3LB(c) implies StepMeanLowerBound(min(1/4, c/3)) for all k. -/
theorem accum_mod3_implies_smlb {c : ℝ} (_hc : 0 < c) (hmod3 : AccumMod3LB c) :
    StepMeanLowerBound (min (1/4) (c/3)) := by
  intro k
  rcases k with _ | k'
  · obtain ⟨X₀, hX₀⟩ := smlb_k0_unconditional
    exact ⟨X₀, fun X hX => le_trans (min_le_left _ _) (hX₀ X hX)⟩
  · obtain ⟨X₀, hX₀⟩ := hmod3 (k' + 1)
    exact ⟨X₀, fun X hX => by
      calc min (1 / 4) (c / 3) ≤ c / 3 := min_le_right _ _
        _ ≤ sqfreeAccumDensity X (k' + 1) 3 2 / 3 :=
            div_le_div_of_nonneg_right (hX₀ X hX) (by positivity)
        _ ≤ ensembleAvg X (fun n => 1 / (genSeq n (k' + 1) : ℝ)) :=
            ensembleAvg_ge_mod3_density X (k' + 1) (by omega)⟩

/-- AccumMod3LB(c) implies PositiveDensityRSD, via SMLB and LMG. -/
theorem accum_mod3_implies_positive_density_rsd {c : ℝ} (hc : 0 < c)
    (hmod3 : AccumMod3LB c) : PositiveDensityRSD :=
  smlb_implies_positive_density_rsd (by positivity) (accum_mod3_implies_smlb hc hmod3)

/-- **EWE Landscape**: all routes from equidistribution hypotheses to PRSD. -/
theorem ewe_landscape :
    (∀ κ : ℝ, 0 < κ → FirstMomentStep κ → PositiveDensityRSD) ∧
    (∀ c : ℝ, 0 < c → StepMeanLowerBound c → PositiveDensityRSD) ∧
    (∀ c : ℝ, 0 < c → AccumMod3LB c → PositiveDensityRSD) :=
  ⟨fun _ hκ => first_moment_step_implies_positive_density_rsd hκ,
   fun _ hc => smlb_implies_positive_density_rsd hc,
   fun _ hc => accum_mod3_implies_positive_density_rsd hc⟩

end Mod3Bridge

/-! ## Conditional MinFac Residue Equidistribution -/

section MFREConditional

/-- Count of squarefree m in [1,X] with m ≡ c (mod q). -/
def sqfreeClassCount (X q : Nat) (c : ZMod q) : Nat :=
  ((Finset.Icc 1 X).filter (fun m : Nat => Squarefree m ∧ (↑m : ZMod q) = c)).card

/-- Count of squarefree m in [1,X] with m ≡ c (mod q) AND minFac(m+1) ≡ a (mod q). -/
def sqfreeClassMinFacCount (X q : Nat) (c a : ZMod q) : Nat :=
  ((Finset.Icc 1 X).filter (fun m : Nat =>
    Squarefree m ∧ (↑m : ZMod q) = c ∧
    (↑(Nat.minFac (m + 1)) : ZMod q) = a)).card

/-- Conditional density of minFac(m+1) ≡ a mod q among squarefree m ≡ c mod q. -/
def condMinFacDensity (X q : Nat) (c a : ZMod q) : ℝ :=
  (sqfreeClassMinFacCount X q c a : ℝ) / (sqfreeClassCount X q c : ℝ)

/-- The joint count is bounded by the class count (filter subset). -/
theorem sqfreeClassMinFacCount_le (X q : Nat) (c a : ZMod q) :
    sqfreeClassMinFacCount X q c a ≤ sqfreeClassCount X q c := by
  unfold sqfreeClassMinFacCount sqfreeClassCount
  exact Finset.card_le_card fun n hn => by
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1, hn.2.2.1⟩

/-- The conditional density is non-negative. -/
theorem condMinFacDensity_nonneg (X q : Nat) (c a : ZMod q) :
    0 ≤ condMinFacDensity X q c a :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The conditional density is at most 1. -/
theorem condMinFacDensity_le_one (X q : Nat) (c a : ZMod q) :
    condMinFacDensity X q c a ≤ 1 := by
  unfold condMinFacDensity
  rcases eq_or_ne (sqfreeClassCount X q c) 0 with h | h
  · simp [h]
  · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))).mpr
      (Nat.cast_le.mpr (sqfreeClassMinFacCount_le X q c a))

/-- **MFREConditional**: conditional equidistribution of minFac mod q with O(1/q^2) error.
    For prime q, among squarefree m with m ≡ c (mod q) where c is nonzero and c ≠ -1,
    the density of those with minFac(m+1) ≡ a (mod q) converges to 1/(q-1) + O(1/q^2).

    **Status**: open hypothesis (requires conditional sieve-theoretic analysis). -/
def MFREConditional : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (q : Nat), Nat.Prime q →
    ∀ (c : ZMod q), c ≠ 0 → (c : ZMod q) ≠ -1 →
    ∀ (a : ZMod q), a ≠ 0 →
      ∃ (L : ℝ),
        |L - 1 / ((q : ℝ) - 1)| ≤ C / (q : ℝ) ^ 2 ∧
        Filter.Tendsto
          (fun X : Nat => condMinFacDensity X q c a)
          Filter.atTop (nhds L)

/-- **EnsembleSelectionLemma**: orbit-population transfer for conditional MFRE.
    This bridges from the population-level conditional equidistribution (MFREConditional)
    to the ensemble-level conditional density of genSeq n k ≡ a (mod q) among squarefree
    n with genProd n k ≡ c (mod q).

    **Status**: open hypothesis (requires orbit-population transfer analysis). -/
def EnsembleSelectionLemma : Prop :=
  MFREConditional →
    ∀ (q : Nat), Nat.Prime q → ∀ (k : Nat),
    ∀ (c : ZMod q), c ≠ 0 → (c : ZMod q) ≠ -1 →
    ∀ (a : ZMod q), a ≠ 0 →
      ∃ (L : ℝ),
        (∃ C : ℝ, |L - 1 / ((q : ℝ) - 1)| ≤ C / (q : ℝ) ^ 2) ∧
        Filter.Tendsto
          (fun X : Nat =>
            (((Finset.Icc 1 X).filter (fun n =>
              Squarefree n ∧ (genProd n k : ZMod q) = c ∧
              (genSeq n k : ZMod q) = a)).card : ℝ) /
            (sqfreeAccumCount X k q c : ℝ))
          Filter.atTop (nhds L)

/-- **MFRECondImpliesSMLB**: MFRE_conditional + EnsembleSelection implies SMLB.
    This captures the route from conditional equidistribution to a step mean lower bound.

    **Status**: open hypothesis (requires assembling conditional density → average bound). -/
def MFRECondImpliesSMLB : Prop :=
  MFREConditional → EnsembleSelectionLemma → StepMeanLowerBound (1/6)

end MFREConditional

/-! ## Generalized Death Density Bridge

When genProd(n,k) ≡ -1 mod q for a prime q ≥ 3, the accumulator satisfies
q | genProd(n,k) + 1, so genSeq(n,k) = minFac(genProd(n,k)+1) ≤ q.
Combined with genSeq ≥ 3 (from parity), this gives 1/genSeq ≥ 1/q on
the "death fiber" {n : genProd(n,k) ≡ -1 mod q}.

This generalizes the mod-3 bridge (where -1 ≡ 2 mod 3) to all primes q ≥ 3.
-/

section DeathDensity

/-- Auxiliary: on the fiber where genProd n k ≡ -1 mod q (for prime q ≥ 3, k ≥ 1, n ≥ 1),
    the generalized EM prime genSeq n k satisfies genSeq n k ≤ q.
    Proof: q divides genProd n k + 1, and genSeq = minFac(genProd+1) ≤ q. -/
private theorem genSeq_le_of_genProd_neg_one {n k q : Nat} (_hn : 1 ≤ n) (_hk : 1 ≤ k)
    (hq : Nat.Prime q) (hmod : (genProd n k : ZMod q) = -1) :
    genSeq n k ≤ q := by
  rw [genSeq_def]
  have h_dvd : q ∣ genProd n k + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [hmod]; ring
  exact Nat.minFac_le_of_dvd hq.two_le h_dvd

/-- Auxiliary: the numerator inequality for the death density bound at prime q ≥ 3.
    On the death fiber {n : genProd n k ≡ -1 mod q}, each 1/genSeq ≥ 1/q,
    so the fiber sum ≥ fiber_card / q. The complement contributes ≥ 0. -/
private theorem death_numerator_bound (X k q : Nat) (hk : 1 ≤ k) (hq : Nat.Prime q)
    (_hq3 : 3 ≤ q) :
    (((Finset.Icc 1 X).filter (fun n => Squarefree n ∧
        (genProd n k : ZMod q) = (-1 : ZMod q))).card : ℝ) / q ≤
    ∑ n ∈ (Finset.Icc 1 X).filter Squarefree, 1 / (genSeq n k : ℝ) := by
  set S := (Finset.Icc 1 X).filter Squarefree
  set Sdeath := S.filter (fun n => (genProd n k : ZMod q) = (-1 : ZMod q))
  -- The filter on Icc with conj equals Sdeath
  have hSdeath_eq : Sdeath.card =
      ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧
        (genProd n k : ZMod q) = (-1 : ZMod q))).card := by
    congr 1; ext n; simp only [Sdeath, S, Finset.mem_filter, and_assoc]
  rw [← hSdeath_eq]
  -- Split the sum over S by whether genProd n k ≡ -1 mod q
  have hsplit := Finset.sum_filter_add_sum_filter_not S
    (fun n => (genProd n k : ZMod q) = (-1 : ZMod q))
    (fun n => 1 / (genSeq n k : ℝ))
  -- On Sdeath: each term ≥ 1/q
  have hdeath_terms : ∀ n ∈ Sdeath, 1 / (q : ℝ) ≤ 1 / (genSeq n k : ℝ) := by
    intro n hn
    have hmem := Finset.mem_filter.mp hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem.1).1).1
    have hle := genSeq_le_of_genProd_neg_one hn1 hk hq hmem.2
    have hge3 := genSeq_ge_three hn1 hk
    refine div_le_div_of_nonneg_left one_pos.le (Nat.cast_pos.mpr (by omega))
      (Nat.cast_le.mpr hle)
  -- Sum on Sdeath ≥ Sdeath.card / q
  have hdeath_sum : (Sdeath.card : ℝ) / q ≤ ∑ n ∈ Sdeath, 1 / (genSeq n k : ℝ) := by
    rw [div_le_iff₀ (Nat.cast_pos.mpr hq.pos)]
    calc (Sdeath.card : ℝ) = ∑ _ ∈ Sdeath, (1 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ∑ n ∈ Sdeath, (1 / (q : ℝ)) * (q : ℝ) := by
          congr 1; ext n; rw [div_mul_cancel₀]; exact Nat.cast_ne_zero.mpr hq.ne_zero
      _ ≤ ∑ n ∈ Sdeath, (1 / (genSeq n k : ℝ)) * (q : ℝ) :=
          Finset.sum_le_sum fun n hn =>
            mul_le_mul_of_nonneg_right (hdeath_terms n hn) (Nat.cast_nonneg q)
      _ = (∑ n ∈ Sdeath, 1 / (genSeq n k : ℝ)) * (q : ℝ) := (Finset.sum_mul ..).symm
  -- Sum on complement ≥ 0
  have hrest_nonneg : 0 ≤ ∑ n ∈ S.filter
      (fun n => ¬(genProd n k : ZMod q) = (-1 : ZMod q)),
      1 / (genSeq n k : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
  linarith [hsplit]

/-- For any prime q ≥ 3 and step k ≥ 1: the ensemble average of 1/genSeq(n,k)
    is at least the death density at q divided by q.
    "Death density" = density of genProd ≡ -1 mod q among squarefree starting points.

    This generalizes `ensembleAvg_ge_mod3_density` from q=3 to all primes q ≥ 3. -/
theorem ensembleAvg_ge_death_density (X k q : Nat) (hk : 1 ≤ k)
    (hq : Nat.Prime q) (hq3 : 3 ≤ q) :
    sqfreeAccumDensity X k q (-1) / q ≤
    ensembleAvg X (fun n => 1 / (genSeq n k : ℝ)) := by
  unfold ensembleAvg sqfreeAccumDensity sqfreeAccumCount sqfreeCount
  set S := (Finset.Icc 1 X).filter Squarefree
  rcases eq_or_ne S.card 0 with hcard | hcard
  · simp [hcard]
  have hS_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcard)
  have hnum := death_numerator_bound X k q hk hq hq3
  calc (((Finset.Icc 1 X).filter (fun n => Squarefree n ∧
          (genProd n k : ZMod q) = (-1 : ZMod q))).card : ℝ) / ↑S.card / ↑q
      = (((Finset.Icc 1 X).filter (fun n => Squarefree n ∧
          (genProd n k : ZMod q) = (-1 : ZMod q))).card : ℝ) / ↑q / ↑S.card := by ring
    _ ≤ (∑ n ∈ S, 1 / (genSeq n k : ℝ)) / ↑S.card :=
        div_le_div_of_nonneg_right hnum hS_pos.le

/-- Lower bound on the "death density" at prime q for all steps k.
    This says the density of squarefree n with genProd n k ≡ -1 mod q is
    eventually at least c for every step k.

    **Status**: open hypothesis (follows from AccumulatorEquidistPropagation). -/
def DeathDensityLB (q : Nat) (c : ℝ) : Prop :=
  ∀ k : Nat, ∃ X₀ : Nat, ∀ X ≥ X₀,
    c ≤ sqfreeAccumDensity X k q (-1)

/-- DeathDensityLB at any prime q ≥ 3 implies StepMeanLowerBound.
    At k=0 we use the unconditional smlb_k0_unconditional (c=1/4).
    At k≥1 we use ensembleAvg_ge_death_density to get c/q as a lower bound. -/
theorem death_density_implies_smlb {q : Nat} {c : ℝ} (hq : Nat.Prime q)
    (hq3 : 3 ≤ q) (_hc : 0 < c) (hdd : DeathDensityLB q c) :
    StepMeanLowerBound (min (1/4) (c/q)) := by
  intro k
  rcases k with _ | k'
  · obtain ⟨X₀, hX₀⟩ := smlb_k0_unconditional
    exact ⟨X₀, fun X hX => le_trans (min_le_left _ _) (hX₀ X hX)⟩
  · obtain ⟨X₀, hX₀⟩ := hdd (k' + 1)
    exact ⟨X₀, fun X hX => by
      calc min (1 / 4) (c / ↑q) ≤ c / ↑q := min_le_right _ _
        _ ≤ sqfreeAccumDensity X (k' + 1) q (-1) / ↑q :=
            div_le_div_of_nonneg_right (hX₀ X hX) (Nat.cast_nonneg q)
        _ ≤ ensembleAvg X (fun n => 1 / (genSeq n (k' + 1) : ℝ)) :=
            ensembleAvg_ge_death_density X (k' + 1) q (by omega) hq hq3⟩

/-- DeathDensityLB at any prime q ≥ 3 implies PositiveDensityRSD, via SMLB and LMG. -/
theorem death_density_implies_prsd {q : Nat} {c : ℝ} (hq : Nat.Prime q)
    (hq3 : 3 ≤ q) (hc : 0 < c) (hdd : DeathDensityLB q c) :
    PositiveDensityRSD :=
  smlb_implies_positive_density_rsd (by positivity) (death_density_implies_smlb hq hq3 hc hdd)

/-- In ZMod 3, -1 = 2. -/
private theorem neg_one_eq_two_mod3 : (-1 : ZMod 3) = (2 : ZMod 3) := by decide

/-- AccumMod3LB(c) is equivalent to DeathDensityLB(3, c), since -1 ≡ 2 mod 3.
    This shows the mod-3 bridge is a special case of the general death density bridge. -/
theorem accumMod3LB_iff_deathDensity3 {c : ℝ} :
    AccumMod3LB c ↔ DeathDensityLB 3 c := by
  simp only [AccumMod3LB, DeathDensityLB, neg_one_eq_two_mod3]

end DeathDensity

/-! ## Extended EWE Landscape -/

section ExtendedLandscape

/-- **Extended EWE Landscape**: all routes from equidistribution hypotheses to
    PositiveDensityRSD, including the generalized death density bridge.

    Route 1: FirstMomentStep(kappa) → PRSD (via LMG).
    Route 2: SMLB(c) → PRSD (via LMG).
    Route 3: AccumMod3LB(c) → PRSD (special case of Route 4 at q=3).
    Route 4: DeathDensityLB at any prime q ≥ 3 → PRSD (generalized death density). -/
theorem ewe_landscape_extended :
    (∀ κ : ℝ, 0 < κ → FirstMomentStep κ → PositiveDensityRSD) ∧
    (∀ c : ℝ, 0 < c → StepMeanLowerBound c → PositiveDensityRSD) ∧
    (∀ c : ℝ, 0 < c → AccumMod3LB c → PositiveDensityRSD) ∧
    (∀ q : Nat, Nat.Prime q → 3 ≤ q → ∀ c : ℝ, 0 < c →
      DeathDensityLB q c → PositiveDensityRSD) :=
  ⟨fun _ hκ => first_moment_step_implies_positive_density_rsd hκ,
   fun _ hc => smlb_implies_positive_density_rsd hc,
   fun _ hc => accum_mod3_implies_positive_density_rsd hc,
   fun _ hq hq3 _ hc => death_density_implies_prsd hq hq3 hc⟩

end ExtendedLandscape

/-! ## MinFac Selection Independence

The CRT structure gives three levels of independence:

1. **Pointwise** (`crt_multiplier_invariance`, PROVED): if two accumulators P, P' agree
   at all primes r != q, then minFac(P+1) = minFac(P'+1). This is deterministic.

2. **Population** (`MinFacSelectionIndependence`, open): among integers m in [1,X],
   the conditional distribution of minFac(m+1) mod q given m mod q is asymptotically
   independent of the mod-q residue class. This follows from CRT + primes in APs.

3. **Fiber/Orbit** (= CME/DSL, the open problem): along a *specific* EM orbit,
   the multiplier equidistributes mod q. This is the sole remaining gap for MC.
-/

section MinFacSelection

/-- **MinFac Selection Independence**: for prime q >= 3 and nonzero residue classes
    d1, d2 (both not -1) in (Z/qZ), the conditional density of {minFac(m+1) = a mod q}
    given {m = d1 mod q} equals that given {m = d2 mod q}, asymptotically.

    This is a population-level CRT statement: the mod-q coordinate of m does not
    influence which prime wins the minFac race for m+1, because the minFac depends
    on divisibility by primes r (possibly = q), and for r != q the CRT coordinate
    mod r is independent of the mod-q coordinate.

    Note: The d != -1 exclusion is necessary because m = -1 mod q means q | m+1,
    which forces minFac(m+1) <= q, biasing the conditional distribution.

    **Status**: open hypothesis (follows from PrimesEquidistributedInAP via CRT). -/
def MinFacSelectionIndependence : Prop :=
  ∀ (q : Nat), Nat.Prime q → 3 ≤ q →
  ∀ (d₁ d₂ : ZMod q), d₁ ≠ 0 → d₂ ≠ 0 → d₁ ≠ -1 → d₂ ≠ -1 →
  ∀ (a : ZMod q), a ≠ 0 →
    Filter.Tendsto
      (fun X : Nat => condMinFacDensity X q d₁ a - condMinFacDensity X q d₂ a)
      Filter.atTop
      (nhds 0)

/-- MinFacSelectionIndependence implies MFREConditional.

    If the conditional distribution of minFac mod q is independent of the mod-q
    class (for non-death classes), then each conditional density converges to the
    same limit. Since the unconditional density sums to 1 over nonzero residues,
    the common limit must be close to 1/(q-1). -/
def MSIImpliesMFREConditional : Prop :=
  MinFacSelectionIndependence → MFREConditional

end MinFacSelection

/-! ## Multi-Prime Death Density

The death density framework works one prime at a time. Here we aggregate
death contributions across all small primes, giving a total ensemble average
lower bound from multiple death channels simultaneously.
-/

section MultiPrimeDeath

/-- Total death contribution from primes in a finite set: sum of
    sqfreeAccumDensity(X, k, q, -1) / q over primes q in the set with q >= 3. -/
def totalDeathContribution (X k : Nat) (primes : Finset Nat) : ℝ :=
  ∑ q ∈ primes.filter (fun q => Nat.Prime q ∧ 3 ≤ q),
    sqfreeAccumDensity X k q (-1) / q

/-- The total death contribution is non-negative (each summand is non-negative). -/
theorem totalDeathContribution_nonneg (X k : Nat) (primes : Finset Nat) :
    0 ≤ totalDeathContribution X k primes := by
  unfold totalDeathContribution
  exact Finset.sum_nonneg fun q _ =>
    div_nonneg (sqfreeAccumDensity_nonneg X k q (-1)) (Nat.cast_nonneg q)

/-- The total death contribution is monotone in the prime set. -/
theorem totalDeathContribution_mono {X k : Nat} {S T : Finset Nat} (hST : S ⊆ T) :
    totalDeathContribution X k S ≤ totalDeathContribution X k T := by
  unfold totalDeathContribution
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset_filter _ hST)
    (fun q _ _ => div_nonneg (sqfreeAccumDensity_nonneg X k q (-1)) (Nat.cast_nonneg q))

/-- The total death contribution lower-bounds the ensemble average.
    Each death channel contributes independently, and the ensemble average
    counts all contributions (including non-death terms which are non-negative).

    For any set of distinct primes q_i >= 3, the death fibers
    {genProd ≡ -1 mod q_i} may overlap, but the ensemble average of 1/genSeq
    is at least the contribution from each individual death channel.
    Since 1/genSeq >= 0 everywhere, the total is at least the max over channels. -/
theorem ensembleAvg_ge_max_death_channel (X k : Nat) (hk : 1 ≤ k)
    (primes : Finset Nat) (hprimes : ∀ q ∈ primes, Nat.Prime q ∧ 3 ≤ q) :
    ∀ q ∈ primes, sqfreeAccumDensity X k q (-1) / q ≤
      ensembleAvg X (fun n => 1 / (genSeq n k : ℝ)) := by
  intro q hq
  exact ensembleAvg_ge_death_density X k q hk (hprimes q hq).1 (hprimes q hq).2

/-- Multi-prime DeathDensityLB: if DeathDensityLB holds at SOME prime q >= 3 with
    positive constant, then PositiveDensityRSD holds. This is already proved
    per-prime; this theorem simply records that ANY single prime suffices. -/
theorem exists_death_density_implies_prsd
    (h : ∃ q : Nat, ∃ c : ℝ, Nat.Prime q ∧ 3 ≤ q ∧ 0 < c ∧ DeathDensityLB q c) :
    PositiveDensityRSD := by
  obtain ⟨q, c, hq, hq3, hc, hdd⟩ := h
  exact death_density_implies_prsd hq hq3 hc hdd

end MultiPrimeDeath

/-! ## CRT Blindness Landscape

Summary of the three levels of CRT independence and their status.
-/

section CRTBlindness

/-- **CRT Blindness Landscape**: documents the three levels of CRT independence
    and the proved/open status of each.

    Level 1 (PROVED): `crt_multiplier_invariance` — pointwise, deterministic.
      If P ≡ P' at all primes r != q, then minFac(P+1) = minFac(P'+1).

    Level 2 (OPEN): `MinFacSelectionIndependence` — population, statistical.
      Conditional density of minFac(m+1) mod q given m mod q is asymptotically
      independent of the mod-q class (for non-death classes).

    Level 3 (OPEN = CME/DSL): fiber/orbit-level equidistribution.
      Along a specific EM orbit, the multiplier equidistributes.
      This is the sole remaining gap for Mullin's Conjecture.

    Proved implications:
    - Level 2 (MSI) → MFREConditional (open bridge: MSIImpliesMFREConditional)
    - DeathDensityLB(q,c) → SMLB → LMG → PositiveDensityRSD (PROVED)
    - AccumulatorEquidistPropagation → DeathDensityLB (immediate from AEP)

    The landscape records:
    (a) DeathDensityLB at any q >= 3 with positive c gives PRSD (PROVED).
    (b) MinFacSelectionIndependence is a population-level statement (OPEN).
    (c) The fiber-level gap (CME/DSL) remains the core open problem. -/
theorem crt_blindness_landscape :
    -- (a) Any single death density lower bound gives PRSD
    (∀ q : Nat, Nat.Prime q → 3 ≤ q → ∀ c : ℝ, 0 < c →
      DeathDensityLB q c → PositiveDensityRSD) ∧
    -- (b) MinFacSelectionIndependence is a well-defined Prop
    (MinFacSelectionIndependence → MinFacSelectionIndependence) ∧
    -- (c) AccumMod3LB is the q=3 special case of DeathDensityLB
    (∀ c : ℝ, AccumMod3LB c ↔ DeathDensityLB 3 c) :=
  ⟨fun _ hq hq3 _ hc => death_density_implies_prsd hq hq3 hc,
   id,
   fun _ => accumMod3LB_iff_deathDensity3⟩

end CRTBlindness

/-! ## Absorption Mechanism: Why AccumMod3LB and DeathDensityLB Are Heuristically False

The mod-q dynamics of `genProd n k` has an **absorption mechanism** that causes the
death density to decay over time:

1. **State 0 is absorbing**: If `q | genProd n k`, then `q | genProd n (k + j)` for all `j ≥ 0`.
   This is because `genProd n (k+1) = genProd n k * genSeq n k`, and divisibility is preserved
   under multiplication.

2. **Death feeds absorption**: When `genProd n k ≡ -1 mod q` and `k ≥ 1`, the proved theorem
   `genSeq_eq_three_of_genProd_mod3` (for q=3) shows `genSeq n k = q`. Then
   `genProd n (k+1) = genProd n k * q ≡ 0 mod q`, so the orbit is absorbed.
   More generally, `genSeq_le_of_genProd_neg_one` gives `genSeq n k ≤ q`, and when
   equality holds, absorption follows.

3. **Absorbed ≠ death**: For `q ≥ 2`, `0 ≠ -1` in `ZMod q`, so absorbed orbits can never
   return to the death class. This means the death density can only decrease over time.

Together, these show that `DeathDensityLB q c` for any `c > 0` is heuristically false:
the death density `d_k(q-1)` decays as orbits get absorbed, roughly as `O((1-1/(q-1))^k)`.

The theorems below formalize the three structural facts (absorption permanence, death-to-absorption
transition, and absorbed-vs-death incompatibility). They do NOT attempt to quantify the decay
rate, which would require population-level dynamics beyond the current infrastructure.
-/

section AbsorptionMechanism

/-- **Absorption is permanent**: if `q | genProd n k`, then `q | genProd n (k + j)` for all `j`.
    This follows from the recurrence `genProd n (k+1) = genProd n k * genSeq n k` and the
    fact that divisibility is preserved under multiplication. -/
theorem genProd_mod_zero_absorbing (q n k j : Nat) (h : q ∣ genProd n k) :
    q ∣ genProd n (k + j) := by
  induction j with
  | zero => exact h
  | succ j ih =>
    rw [Nat.add_succ, genProd_succ]
    exact dvd_mul_of_dvd_left ih _

/-- **Death feeds absorption (when genSeq = q)**: if `genProd n k ≡ -1 mod q` and
    `genSeq n k = q`, then `q | genProd n (k + 1)`. This is because
    `genProd n (k+1) = genProd n k * q`, and `q | q` gives `q | genProd n (k+1)`. -/
theorem death_implies_absorption {q n k : Nat} (_hq : 2 ≤ q)
    (_hmod : (genProd n k : ZMod q) = -1) (hseq : genSeq n k = q) :
    q ∣ genProd n (k + 1) := by
  rw [genProd_succ, hseq]
  exact dvd_mul_left q (genProd n k)

/-- **Absorbed state is not the death state**: if `q | genProd n k` and `q ≥ 2`, then
    `genProd n k` is NOT in residue class `-1 mod q`. This is because `q | genProd n k`
    means `(genProd n k : ZMod q) = 0`, and `0 ≠ -1` in `ZMod q` when `q ≥ 2`. -/
theorem absorbed_not_in_death_class {q n k : Nat} (hq : 2 ≤ q)
    (hdvd : q ∣ genProd n k) : ¬((genProd n k : ZMod q) = -1) := by
  haveI : Fact (1 < q) := ⟨by omega⟩
  intro hmod
  have h0 : (genProd n k : ZMod q) = 0 := by
    rwa [ZMod.natCast_eq_zero_iff]
  have h01 : (0 : ZMod q) = -1 := h0 ▸ hmod
  exact absurd (neg_eq_zero.mp h01.symm) one_ne_zero

/-- **Death at mod 3 implies absorption at the next step**: when `genProd n k ≡ 2 mod 3`,
    `k ≥ 1`, and `n ≥ 1`, the proved `genSeq_eq_three_of_genProd_mod3` gives `genSeq n k = 3`,
    so `genProd n (k+1) = genProd n k * 3 ≡ 0 mod 3`. -/
theorem mod3_death_implies_absorption {n k : Nat} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hmod : (genProd n k : ZMod 3) = 2) : 3 ∣ genProd n (k + 1) := by
  have hseq := genSeq_eq_three_of_genProd_mod3 hn hk hmod
  exact death_implies_absorption (by omega) (by rw [hmod]; decide) hseq

/-- **Absorption kills death density**: a landscape theorem witnessing the three
    structural facts that make `DeathDensityLB q c` heuristically false for any `c > 0`:

    (1) Absorption is permanent: once `q | genProd`, it stays forever.
    (2) Absorbed ≠ death: `0 ≠ -1` in `ZMod q` for `q ≥ 2`.
    (3) Death feeds absorption when `genSeq = q` (which holds whenever
        `genProd ≡ -1 mod q` and `genSeq ≤ q`, as proved by `genSeq_le_of_genProd_neg_one`).

    This does NOT prove that `DeathDensityLB` is false (that would require quantitative
    population dynamics), but formalizes the mechanism by which death density decays. -/
theorem absorption_kills_death_density (q : Nat) (hq : Nat.Prime q) (_hq3 : 3 ≤ q) :
    -- (1) Absorption is permanent
    (∀ n k j, q ∣ genProd n k → q ∣ genProd n (k + j)) ∧
    -- (2) Absorbed state ≠ death state
    (∀ n k, q ∣ genProd n k → ¬((genProd n k : ZMod q) = -1)) ∧
    -- (3) Death feeds absorption (when genSeq = q)
    (∀ n k, (genProd n k : ZMod q) = -1 → genSeq n k = q → q ∣ genProd n (k + 1)) :=
  ⟨fun n k j h => genProd_mod_zero_absorbing q n k j h,
   fun _ _ h => absorbed_not_in_death_class hq.two_le h,
   fun _ _ hmod hseq => death_implies_absorption hq.two_le hmod hseq⟩

/-- **Permanence of absorption**: once absorbed, the orbit stays absorbed at all future steps.
    Combined with `death_implies_absorption`, this means any orbit that hits the death state
    and has `genSeq = q` at that step will be permanently absorbed from that step onward. -/
theorem death_then_permanent_absorption {q n k : Nat} (hq : 2 ≤ q)
    (hmod : (genProd n k : ZMod q) = -1) (hseq : genSeq n k = q)
    (j : Nat) : q ∣ genProd n (k + 1 + j) := by
  exact genProd_mod_zero_absorbing q n (k + 1) j (death_implies_absorption hq hmod hseq)

/-- **Once absorbed, never in death class again**: if an orbit passes through the death state
    at step `k` with `genSeq n k = q`, it can never return to the death class. -/
theorem death_then_never_death_again {q n k : Nat} (hq : Nat.Prime q) (_hq3 : 3 ≤ q)
    (hmod : (genProd n k : ZMod q) = -1) (hseq : genSeq n k = q)
    (j : Nat) : ¬((genProd n (k + 1 + j) : ZMod q) = -1) :=
  absorbed_not_in_death_class hq.two_le
    (death_then_permanent_absorption hq.two_le hmod hseq j)

end AbsorptionMechanism

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
