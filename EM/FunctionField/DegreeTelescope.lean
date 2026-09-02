import EM.FunctionField.Analog
import EM.Population.DefectTelescope

/-!
# The Degree Telescope over `𝔽_p[t]`

`EM/Population/DefectTelescope.lean` builds, over `ℤ`, the identity

    log (prod (n+1)) = 2 * log (prod n) - defect n ,

telescopes it, and extracts the growth constant `C = lim log (prod N) / 2 ^ N`.  Two
things there are approximate, and both are artefacts of working with `log` of an integer:

* the defect can be slightly **negative** (a prime Euclid number has
  `seq (n+1) = prod n + 1 > prod n`), so one has to carry the error `log (1 + 1/prod n)`
  and correct the sequence before it is antitone;
* the defect is a **real** number, so nothing distinguishes "the selected factor is
  proper" from "the selected factor is almost everything".

Over `𝔽_p[t]` both disappear.  Degrees are additive on the nose, and
`deg (Prod n + 1) = deg (Prod n)` exactly (`ffProdPlusOne_natDegree`), so the defect

    ffDefect n := deg (ffProd n) - deg (ffSeq (n+1))

is a **nonnegative integer**, the recursion

    deg (ffProd (n+1)) = 2 * deg (ffProd n) - ffDefect n

is exact, and `deg (ffProd N) / 2 ^ N` is antitone with no correction at all.  This is the
sense in which the function field model is the right place to look at the growth axis:
the telescope is a clean identity rather than an identity plus an error term.

## Trial division, and what the model buys

Trial division works here too, and exactly.  If `ffProd n + 1` is reducible then the
cofactor also carries a monic irreducible factor, which minimality forces to be at least
as large as the selected one; so

    2 * deg (ffSeq (n+1)) ≤ deg (ffProd n)

(`two_mul_ffDeg'_le_of_not_irreducible`) with no error term — the integer statement needs
one.  Hence one reducible stage multiplies `ffNormDeg` by exactly `3/4`, giving the sharp

    deg (ffProd N) ≤ (3/4) ^ (#reducible stages below N) * 2 ^ N

(`ffDeg_le_pow_mul`; over `ℤ` the same bound carries a constant `log 2 + 1/3`).  The
growth constant is therefore a **complete invariant**:

    ffGrowthConstant = 0  ⟺  (C∞_FF),
    0 < ffGrowthConstant  ⟺  perpetual irreducibility from some stage

(`ffInfinitelyManyReducible_iff_ffGrowthConstant_eq_zero`,
`ffGrowthConstant_pos_iff_perpetual`), exactly as over `ℤ`.

So what the model buys is *cleanliness*: every statement of
`EM/Population/DefectTelescope.lean` holds here with the epsilons removed.  What it does
**not** buy is the question.  Both settings reduce (C∞) to a single real number, and in
both the number is defined from the orbit and cannot be evaluated by any finite
computation — a defect at stage `n` is discounted by `2 ^ -n`.  The density of
irreducibles of each degree, which over `𝔽_p[t]` is not merely known but exactly
computable, is a statement about the *population*; what is needed is the least-degree
irreducible factor of the *one* polynomial `ffProd n + 1`.  That is the orbit-specificity
barrier (`EM/Meta/BagInformation.lean`, Dead End #90), and this file is the sharpest form
of the evidence that it, and not the analytic input, is the obstruction: here every
analytic input is a theorem, and nothing moves.

**Update 2026-09-02 — for particular `p` the question does move, in both directions.**
Over `𝔽_5[t]` the seed-`X` sequence is perpetually irreducible from stage `0`
(`EM/FunctionField/StableTower.lean`, `tower_euclid_irreducible`): `ffDefect n = 0` for all `n`,
`ffGrowthConstant = 1`, `FFPerpetualIrreducibility d 0` holds, `(C∞)_FF` is *false*, and so is
`FFMullinConjecture 5` (`not_ffMullinConjecture_five`).  Over `𝔽_2[t]` the take-all map
`P ↦ P² + P` is additive and `(F+1)³P + 1 = (P⁴+P³+1)(P⁴+P³+P²+P+1)`, so no four consecutive
Euclid polynomials are irreducible and `(C∞)_FF` holds for every seed; for `p ≡ 1 (mod 3)` `Φ₃`
splits and no two consecutive ones are.  Both floors are theorems for every `FFEMData`
(`EM/FunctionField/CompositeFloors.lean`: `ffGrowthConstant_eq_zero_of_two`,
`ffGrowthConstant_eq_zero_of_one_mod_three`).  Which case a prime `p ≡ 2 (mod 3)` falls into is
decided by a finite check on the orbit of `−1/4` under `y ↦ y² + y` in `𝔽_p`.

## Contents

* `ffDeg`, `ffDefect`, `ffNormDeg` — the telescope's three sequences.
* `ffDeg_succ_add_ffDefect` — the exact recursion.
* `ffDefect_eq_zero_iff` — zero defect ⟺ the Euclid polynomial is irreducible.
* `ffNormDeg_eq_sub_sum`, `ffNormDeg_antitone` — the telescope, exact and antitone.
* `two_mul_ffDeg'_le_of_not_irreducible`, `ffDeg_le_pow_mul` — trial division and the
  damping bound.
* `ffInfinitelyManyReducible_iff_ffGrowthConstant_eq_zero`,
  `ffGrowthConstant_pos_iff_perpetual` — the complete invariant.
* `ffDefect_dichotomy`, `ff_degree_telescope_landscape`.
-/

noncomputable section

open Polynomial FunctionFieldAnalog Filter Topology

namespace FFDegreeTelescope

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ## Part 1: the three sequences -/

/-- The degree of the accumulator. -/
def ffDeg (d : FFEMData p) (n : ℕ) : ℕ := (d.ffProd n).natDegree

/-- The **defect**: how far the selected irreducible falls short of the maximal step
`ffSeq (n+1) = ffProd n + 1`.  Unlike the integer case this is an honest natural
number. -/
def ffDeg' (d : FFEMData p) (n : ℕ) : ℕ := (d.ffSeq (n + 1)).natDegree

/-- The normalised degree `deg (ffProd n) / 2 ^ n`. -/
def ffNormDeg (d : FFEMData p) (n : ℕ) : ℝ := (ffDeg d n : ℝ) / 2 ^ n

theorem ffDeg_zero (d : FFEMData p) : ffDeg d 0 = 1 := by
  unfold ffDeg
  rw [d.ffProd_zero]
  exact natDegree_X

theorem ffDeg_pos (d : FFEMData p) (n : ℕ) : 0 < ffDeg d n := by
  have hmono := ffProd_natDegree_strict_mono p d
  have : ffDeg d 0 ≤ ffDeg d n := hmono.monotone (Nat.zero_le n)
  rw [ffDeg_zero] at this
  omega

theorem ffProd_add_one_natDegree (d : FFEMData p) (n : ℕ) :
    (d.ffProd n + 1).natDegree = ffDeg d n :=
  ffProdPlusOne_natDegree p d n (ffDeg_pos d n)

theorem ffProd_add_one_ne_zero (d : FFEMData p) (n : ℕ) : d.ffProd n + 1 ≠ 0 := by
  intro h
  have := ffProd_add_one_natDegree d n
  rw [h, natDegree_zero] at this
  have := ffDeg_pos d n
  omega

/-- The selected irreducible cannot exceed the Euclid polynomial it divides. -/
theorem ffDeg'_le (d : FFEMData p) (n : ℕ) : ffDeg' d n ≤ ffDeg d n := by
  have hdvd : d.ffSeq (n + 1) ∣ d.ffProd n + 1 := (d.ffSeq_succ n).2.2
  have := natDegree_le_of_dvd hdvd (ffProd_add_one_ne_zero d n)
  rwa [ffProd_add_one_natDegree] at this

theorem ffDeg'_pos (d : FFEMData p) (n : ℕ) : 0 < ffDeg' d n :=
  Irreducible.natDegree_pos (d.ffSeq_succ n).2.1

/-- The **defect** at stage `n`, a natural number in `[0, ffDeg d n)`. -/
def ffDefect (d : FFEMData p) (n : ℕ) : ℕ := ffDeg d n - ffDeg' d n

theorem ffDeg_succ (d : FFEMData p) (n : ℕ) :
    ffDeg d (n + 1) = ffDeg d n + ffDeg' d n := by
  unfold ffDeg ffDeg'
  rw [d.ffProd_succ n]
  exact Monic.natDegree_mul (ffProd_monic p d n) (ffSeq_monic p d (n + 1))

/-- **The exact recursion.**  Every step is the maximal (doubling) step, less the defect —
with no error term, because `deg (ffProd n + 1) = deg (ffProd n)` on the nose. -/
theorem ffDeg_succ_add_ffDefect (d : FFEMData p) (n : ℕ) :
    ffDeg d (n + 1) + ffDefect d n = 2 * ffDeg d n := by
  have h := ffDeg_succ d n
  have hle := ffDeg'_le d n
  unfold ffDefect
  omega

theorem ffDefect_lt (d : FFEMData p) (n : ℕ) : ffDefect d n < ffDeg d n := by
  have h1 : 0 < (d.ffSeq (n + 1)).natDegree := ffDeg'_pos d n
  have h2 : (d.ffSeq (n + 1)).natDegree ≤ ffDeg d n := ffDeg'_le d n
  unfold ffDefect ffDeg'
  omega

/-! ## Part 2: zero defect is exactly irreducibility

Over `ℤ` the analogous statement is an approximation: a prime Euclid number gives
`log (seq (n+1)) = log (prod n + 1)`, not `log (prod n)`.  Here it is an equivalence. -/

/-- **Zero defect ⟺ the Euclid polynomial is irreducible.** -/
theorem ffDefect_eq_zero_iff (d : FFEMData p) (n : ℕ) :
    ffDefect d n = 0 ↔ Irreducible (d.ffProd n + 1) := by
  constructor
  · intro h
    have hle := ffDeg'_le d n
    have hdeg : ffDeg' d n = ffDeg d n := by unfold ffDefect at h; omega
    -- a monic divisor of the same degree is the whole thing
    obtain ⟨g, hg⟩ := (d.ffSeq_succ n).2.2
    have hmonic : (d.ffProd n + 1).Monic := by
      have h1 : (d.ffProd n).Monic := ffProd_monic p d n
      have h2 : (1 : Polynomial (ZMod p)).degree < (d.ffProd n).degree := by
        rw [degree_one, degree_eq_natDegree h1.ne_zero]
        exact_mod_cast ffDeg_pos d n
      exact h1.add_of_left h2
    have hgm : g.Monic := by
      refine Monic.of_mul_monic_left (ffSeq_monic p d (n + 1)) ?_
      rw [← hg]; exact hmonic
    have hgdeg : g.natDegree = 0 := by
      have := Monic.natDegree_mul (ffSeq_monic p d (n + 1)) hgm
      rw [← hg, ffProd_add_one_natDegree] at this
      unfold ffDeg' at hdeg
      omega
    have : g = 1 := eq_one_of_monic_natDegree_zero hgm hgdeg
    rw [hg, this, mul_one]
    exact (d.ffSeq_succ n).2.1
  · intro hirr
    -- the minimal-degree monic irreducible factor of an irreducible monic is itself
    have hmin := d.ffSeq_minimal n
    have hmonic : (d.ffProd n + 1).Monic := by
      have h1 : (d.ffProd n).Monic := ffProd_monic p d n
      have h2 : (1 : Polynomial (ZMod p)).degree < (d.ffProd n).degree := by
        rw [degree_one, degree_eq_natDegree h1.ne_zero]
        exact_mod_cast ffDeg_pos d n
      exact h1.add_of_left h2
    -- an irreducible divisor of an irreducible is an associate, hence of full degree
    obtain ⟨g, hg⟩ := (d.ffSeq_succ n).2.2
    have hu : IsUnit g := by
      rcases hirr.isUnit_or_isUnit hg with h1 | h1
      · exact absurd h1 (d.ffSeq_succ n).2.1.not_isUnit
      · exact h1
    have hg0 : g ≠ 0 := hu.ne_zero
    have hs0 : d.ffSeq (n + 1) ≠ 0 := (ffSeq_monic p d (n + 1)).ne_zero
    have hdeg := natDegree_mul hs0 hg0
    rw [← hg, ffProd_add_one_natDegree, natDegree_eq_zero_of_isUnit hu, add_zero] at hdeg
    unfold ffDefect ffDeg'
    omega

/-! ## Part 3: the telescope, exact and antitone -/

theorem ffNormDeg_succ (d : FFEMData p) (n : ℕ) :
    ffNormDeg d (n + 1) = ffNormDeg d n - (ffDefect d n : ℝ) / 2 ^ (n + 1) := by
  have h := ffDeg_succ_add_ffDefect d n
  have hR : (ffDeg d (n + 1) : ℝ) = 2 * (ffDeg d n : ℝ) - (ffDefect d n : ℝ) := by
    have hc : ((ffDeg d (n + 1) + ffDefect d n : ℕ) : ℝ) = ((2 * ffDeg d n : ℕ) : ℝ) :=
      congrArg (fun m : ℕ => (m : ℝ)) h
    push_cast at hc
    linarith
  have h2 : ((2 : ℝ)) ^ n ≠ 0 := by positivity
  unfold ffNormDeg
  rw [hR, pow_succ]
  field_simp

/-- **The telescoped identity**, exact: `deg (ffProd 0) = 1`, so the normalised degree is
`1` minus the `2 ^ -n`-weighted defect sum. -/
theorem ffNormDeg_eq_sub_sum (d : FFEMData p) (N : ℕ) :
    ffNormDeg d N = 1 - ∑ n ∈ Finset.range N, (ffDefect d n : ℝ) / 2 ^ (n + 1) := by
  induction N with
  | zero => simp [ffNormDeg, ffDeg_zero]
  | succ N ih => rw [ffNormDeg_succ, ih, Finset.sum_range_succ]; ring

theorem ffNormDeg_pos (d : FFEMData p) (n : ℕ) : 0 < ffNormDeg d n := by
  unfold ffNormDeg
  have := ffDeg_pos d n
  have : (0 : ℝ) < (ffDeg d n : ℝ) := by exact_mod_cast this
  positivity

/-- **Antitone with no correction term.**  This is the structural gain over `ℤ`: the
defect is genuinely nonnegative here. -/
theorem ffNormDeg_antitone (d : FFEMData p) : Antitone (ffNormDeg d) := by
  refine antitone_nat_of_succ_le (fun n => ?_)
  rw [ffNormDeg_succ]
  have : (0 : ℝ) ≤ (ffDefect d n : ℝ) / 2 ^ (n + 1) := by positivity
  linarith

theorem ffNormDeg_bddBelow (d : FFEMData p) : BddBelow (Set.range (ffNormDeg d)) := by
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  exact (ffNormDeg_pos d n).le

/-- **(G_FF): the function field growth constant.** -/
def ffGrowthConstant (d : FFEMData p) : ℝ := ⨅ n, ffNormDeg d n

theorem tendsto_ffNormDeg (d : FFEMData p) :
    Tendsto (ffNormDeg d) atTop (𝓝 (ffGrowthConstant d)) :=
  tendsto_atTop_ciInf (ffNormDeg_antitone d) (ffNormDeg_bddBelow d)

theorem ffGrowthConstant_nonneg (d : FFEMData p) : 0 ≤ ffGrowthConstant d :=
  ge_of_tendsto' (tendsto_ffNormDeg d) (fun n => (ffNormDeg_pos d n).le)

theorem ffGrowthConstant_le_one (d : FFEMData p) : ffGrowthConstant d ≤ 1 := by
  have h : ffGrowthConstant d ≤ ffNormDeg d 0 := ciInf_le (ffNormDeg_bddBelow d) 0
  simpa [ffNormDeg, ffDeg_zero] using h

/-! ## Part 4: `(G_FF)` implies the function field `(C∞)`

Over `ℤ` this implication runs through `Nat.log`-chasing.  Here it is immediate from
exactness: on the perpetually-irreducible branch the defect is identically zero, so the
normalised degree is eventually *constant*, and a positive constant at that. -/

/-- The function field analogue of `PerpetualPrimality`. -/
def FFPerpetualIrreducibility (d : FFEMData p) (N : ℕ) : Prop :=
  ∀ n, N ≤ n → Irreducible (d.ffProd n + 1)

/-- The function field analogue of (C∞). -/
def FFInfinitelyManyReducible (d : FFEMData p) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ ¬ Irreducible (d.ffProd n + 1)

theorem ffInfinitelyManyReducible_iff (d : FFEMData p) :
    FFInfinitelyManyReducible d ↔ ∀ N, ¬ FFPerpetualIrreducibility d N := by
  constructor
  · intro h N hpp
    obtain ⟨n, hn, hnot⟩ := h N
    exact hnot (hpp n hn)
  · intro h N
    by_contra hcon
    push Not at hcon
    exact h N (fun n hn => hcon n hn)

/-- On the perpetually-irreducible branch the normalised degree is eventually constant. -/
theorem ffNormDeg_eq_of_perpetual {d : FFEMData p} {N : ℕ}
    (hpp : FFPerpetualIrreducibility d N) {n : ℕ} (hn : N ≤ n) :
    ffNormDeg d n = ffNormDeg d N := by
  induction n with
  | zero =>
      have : N = 0 := Nat.le_zero.mp hn
      rw [this]
  | succ m ih =>
      rcases Nat.lt_or_ge N (m + 1) with hlt | hge
      · have hm : N ≤ m := by omega
        have hz : ffDefect d m = 0 := (ffDefect_eq_zero_iff d m).mpr (hpp m hm)
        rw [ffNormDeg_succ, hz]
        simpa using ih hm
      · have : N = m + 1 := by omega
        rw [this]

/-- **(G_FF) ⟹ (C∞_FF).**  If the accumulator's degree is `o(2 ^ N)` then the Euclid
polynomial is reducible infinitely often. -/
theorem ffInfinitelyManyReducible_of_ffGrowthConstant_eq_zero {d : FFEMData p}
    (h : ffGrowthConstant d = 0) : FFInfinitelyManyReducible d := by
  rw [ffInfinitelyManyReducible_iff]
  intro N hpp
  have hconst : Tendsto (ffNormDeg d) atTop (𝓝 (ffNormDeg d N)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (ffNormDeg_eq_of_perpetual hpp hn).symm
  have := tendsto_nhds_unique (tendsto_ffNormDeg d) hconst
  rw [h] at this
  exact absurd this.symm (ne_of_gt (ffNormDeg_pos d N))

/-! ## Part 4b: trial division, exactly

The integer telescope needs an error term for the corresponding statement; here it is a
clean inequality on natural numbers.  If `ffProd n + 1` is reducible, its least-degree
monic irreducible factor is matched by an irreducible factor of the cofactor, which
minimality forces to be at least as large.  So the selected degree is at most **half**:

    2 * ffDeg' n ≤ ffDeg n,   equivalently   ffDeg n ≤ 2 * ffDefect n .

Consequently one reducible stage multiplies `ffNormDeg` by exactly `3/4` — no correction
term, unlike the integer case — and the growth constant is again a *complete invariant*:
`ffGrowthConstant = 0 ⟺ (C∞_FF)`. -/

theorem one_le_ffDefect_of_not_irreducible {d : FFEMData p} {n : ℕ}
    (h : ¬ Irreducible (d.ffProd n + 1)) : 1 ≤ ffDefect d n := by
  have hne : ffDefect d n ≠ 0 := fun h0 => h ((ffDefect_eq_zero_iff d n).mp h0)
  omega

/-- **Trial division over `𝔽_p[t]`.**  A reducible Euclid polynomial has its least-degree
irreducible factor at most half its degree. -/
theorem two_mul_ffDeg'_le_of_not_irreducible {d : FFEMData p} {n : ℕ}
    (h : ¬ Irreducible (d.ffProd n + 1)) : 2 * ffDeg' d n ≤ ffDeg d n := by
  obtain ⟨g, hg⟩ := (d.ffSeq_succ n).2.2
  have hfirr : Irreducible (d.ffSeq (n + 1)) := (d.ffSeq_succ n).2.1
  have hgu : ¬ IsUnit g := by
    intro hu
    have hass : Associated (d.ffSeq (n + 1)) (d.ffSeq (n + 1) * g) :=
      associated_mul_unit_right _ _ hu
    exact h (hg ▸ hass.irreducible hfirr)
  obtain ⟨q, hqm, hqi, hqd⟩ := Polynomial.exists_monic_irreducible_factor g hgu
  have hg0 : g ≠ 0 := by
    intro h0
    exact ffProd_add_one_ne_zero d n (by rw [hg, h0, mul_zero])
  have hs0 : d.ffSeq (n + 1) ≠ 0 := (ffSeq_monic p d (n + 1)).ne_zero
  -- minimality: the selected degree is at most that of any monic irreducible factor
  have hmin := d.ffSeq_minimal n q hqm hqi (hqd.trans ⟨d.ffSeq (n + 1), by rw [hg]; ring⟩)
  have hqg : q.natDegree ≤ g.natDegree := natDegree_le_of_dvd hqd hg0
  have hsplit := natDegree_mul hs0 hg0
  rw [← hg, ffProd_add_one_natDegree] at hsplit
  unfold ffDeg'
  omega

/-- **A reducible stage contracts the telescope by exactly `3/4`.** -/
theorem ffNormDeg_succ_le_of_not_irreducible {d : FFEMData p} {n : ℕ}
    (h : ¬ Irreducible (d.ffProd n + 1)) :
    ffNormDeg d (n + 1) ≤ (3 / 4) * ffNormDeg d n := by
  have hle := two_mul_ffDeg'_le_of_not_irreducible h
  have hdef : ffDeg d n ≤ 2 * ffDefect d n := by
    have h2 := ffDeg'_le d n
    unfold ffDefect
    omega
  have hR : (ffDeg d n : ℝ) ≤ 2 * (ffDefect d n : ℝ) := by exact_mod_cast hdef
  have h2 : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have hquarter : (1 / 4) * ffNormDeg d n ≤ (ffDefect d n : ℝ) / 2 ^ (n + 1) := by
    rw [le_div_iff₀ h2, ffNormDeg]
    have hne : ((2 : ℝ)) ^ n ≠ 0 := by positivity
    have hid : (1 / 4 : ℝ) * ((ffDeg d n : ℝ) / 2 ^ n) * 2 ^ (n + 1)
        = (1 / 2) * (ffDeg d n : ℝ) := by
      rw [pow_succ]; field_simp; ring
    rw [hid]
    linarith
  rw [ffNormDeg_succ]
  linarith

open Classical in
/-- The number of reducible Euclid polynomials before stage `N`. -/
def ffReducibleCount (d : FFEMData p) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => ¬ Irreducible (d.ffProd n + 1))).card

open Classical in
theorem ffReducibleCount_succ_of_irreducible {d : FFEMData p} {N : ℕ}
    (h : Irreducible (d.ffProd N + 1)) :
    ffReducibleCount d (N + 1) = ffReducibleCount d N := by
  unfold ffReducibleCount
  rw [Finset.range_add_one, Finset.filter_insert, if_neg (by simpa using h)]

open Classical in
theorem ffReducibleCount_succ_of_not_irreducible {d : FFEMData p} {N : ℕ}
    (h : ¬ Irreducible (d.ffProd N + 1)) :
    ffReducibleCount d (N + 1) = ffReducibleCount d N + 1 := by
  unfold ffReducibleCount
  rw [Finset.range_add_one, Finset.filter_insert, if_pos h,
    Finset.card_insert_of_notMem (by simp)]

/-- **The damping bound over `𝔽_p[t]`, exact.**  Every reducible stage costs the
accumulator a factor `3/4`; since `deg (ffProd 0) = 1` there is no constant at all:

    deg (ffProd N) ≤ (3/4) ^ (#reducible stages below N) * 2 ^ N . -/
theorem ffNormDeg_le_pow (d : FFEMData p) (N : ℕ) :
    ffNormDeg d N ≤ (3 / 4 : ℝ) ^ ffReducibleCount d N := by
  induction N with
  | zero => simp [ffNormDeg, ffDeg_zero, ffReducibleCount]
  | succ N ih =>
      by_cases h : Irreducible (d.ffProd N + 1)
      · rw [ffReducibleCount_succ_of_irreducible h]
        exact le_trans (ffNormDeg_antitone d (Nat.le_succ N)) ih
      · rw [ffReducibleCount_succ_of_not_irreducible h, pow_succ]
        calc ffNormDeg d (N + 1) ≤ (3 / 4) * ffNormDeg d N :=
              ffNormDeg_succ_le_of_not_irreducible h
          _ ≤ (3 / 4) * (3 / 4 : ℝ) ^ ffReducibleCount d N := by
              exact mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = (3 / 4 : ℝ) ^ ffReducibleCount d N * (3 / 4) := by ring

theorem ffDeg_le_pow_mul (d : FFEMData p) (N : ℕ) :
    (ffDeg d N : ℝ) ≤ (3 / 4 : ℝ) ^ ffReducibleCount d N * 2 ^ N := by
  have h := ffNormDeg_le_pow d N
  have h2 : (0 : ℝ) < 2 ^ N := by positivity
  rw [ffNormDeg, div_le_iff₀ h2] at h
  exact h

/-- **(C∞_FF) ⟹ `ffGrowthConstant = 0`.**  Reducibility infinitely often contracts the
normalised degree geometrically. -/
theorem ffGrowthConstant_eq_zero_of_infinitelyManyReducible {d : FFEMData p}
    (h : FFInfinitelyManyReducible d) : ffGrowthConstant d = 0 := by
  by_contra hne
  have hpos : 0 < ffGrowthConstant d :=
    lt_of_le_of_ne (ffGrowthConstant_nonneg d) (Ne.symm hne)
  -- eventually `ffNormDeg < (7/6) * ffGrowthConstant`
  have hev : ∀ᶠ n in atTop, ffNormDeg d n < (7 / 6) * ffGrowthConstant d := by
    have hlt : ffGrowthConstant d < (7 / 6) * ffGrowthConstant d := by linarith
    simpa using (tendsto_ffNormDeg d).eventually (gt_mem_nhds hlt)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  obtain ⟨n, hn, hred⟩ := h N₀
  have h1 : ffGrowthConstant d ≤ ffNormDeg d (n + 1) :=
    ciInf_le (ffNormDeg_bddBelow d) (n + 1)
  have h2 := ffNormDeg_succ_le_of_not_irreducible hred
  have h3 := hN₀ n hn
  linarith

/-- **(C∞_FF) ⟺ `ffGrowthConstant = 0`**, the function field twin of
`DefectTelescope.infinitelyManyComposite_iff_growthConstant_eq_zero`. -/
theorem ffInfinitelyManyReducible_iff_ffGrowthConstant_eq_zero (d : FFEMData p) :
    FFInfinitelyManyReducible d ↔ ffGrowthConstant d = 0 :=
  ⟨ffGrowthConstant_eq_zero_of_infinitelyManyReducible,
    ffInfinitelyManyReducible_of_ffGrowthConstant_eq_zero⟩

/-- **A positive growth constant is exactly perpetual irreducibility.** -/
theorem ffGrowthConstant_pos_iff_perpetual (d : FFEMData p) :
    0 < ffGrowthConstant d ↔ ∃ N : ℕ, FFPerpetualIrreducibility d N := by
  constructor
  · intro hpos
    by_contra hcon
    push Not at hcon
    have : FFInfinitelyManyReducible d := (ffInfinitelyManyReducible_iff d).mpr hcon
    exact absurd ((ffInfinitelyManyReducible_iff_ffGrowthConstant_eq_zero d).mp this)
      (ne_of_gt hpos)
  · rintro ⟨N, hpp⟩
    rcases eq_or_lt_of_le (ffGrowthConstant_nonneg d) with h | h
    · have hred := (ffInfinitelyManyReducible_iff_ffGrowthConstant_eq_zero d).mpr h.symm
      obtain ⟨n, hn, hnot⟩ := hred N
      exact absurd (hpp n hn) hnot
    · exact h

/-! ## Part 5: the failure branch -/

/-- The telescope's terms tend to `0`. -/
theorem tendsto_ffDefect_div_two_pow (d : FFEMData p) :
    Tendsto (fun n : ℕ => (ffDefect d n : ℝ) / 2 ^ (n + 1)) atTop (𝓝 0) := by
  have hshift : Tendsto (fun n : ℕ => ffNormDeg d (n + 1)) atTop
      (𝓝 (ffGrowthConstant d)) := (tendsto_ffNormDeg d).comp (tendsto_add_atTop_nat 1)
  have h := (tendsto_ffNormDeg d).sub hshift
  simp only [sub_self] at h
  refine h.congr (fun n => ?_)
  rw [ffNormDeg_succ]; ring

theorem tendsto_ffDefect_div_two_pow' (d : FFEMData p) :
    Tendsto (fun n : ℕ => (ffDefect d n : ℝ) / 2 ^ n) atTop (𝓝 0) := by
  have h := (tendsto_ffDefect_div_two_pow d).const_mul (2 : ℝ)
  simp only [mul_zero] at h
  refine h.congr (fun n => ?_)
  have h2 : ((2 : ℝ)) ^ n ≠ 0 := by positivity
  field_simp
  ring

theorem ffDeg'_div_ffDeg_eq (d : FFEMData p) (n : ℕ) :
    (ffDeg' d n : ℝ) / (ffDeg d n : ℝ)
      = 1 - ((ffDefect d n : ℝ) / 2 ^ n) / ffNormDeg d n := by
  have hpos : (0 : ℝ) < (ffDeg d n : ℝ) := by exact_mod_cast ffDeg_pos d n
  have h2 : ((2 : ℝ)) ^ n ≠ 0 := by positivity
  have hsub : (ffDeg' d n : ℝ) = (ffDeg d n : ℝ) - (ffDefect d n : ℝ) := by
    have := ffDeg'_le d n
    unfold ffDefect
    push_cast [Nat.cast_sub this]
    ring
  rw [hsub, ffNormDeg]
  field_simp

/-- **The failure branch.**  A positive growth constant forces the selected irreducible to
have degree `(1 - o(1)) deg (ffProd n)` — the exact analogue of
`DefectTelescope.tendsto_log_seq_div_logProd_of_pos`. -/
theorem tendsto_ffDeg'_div_ffDeg_of_pos {d : FFEMData p} (h : 0 < ffGrowthConstant d) :
    Tendsto (fun n : ℕ => (ffDeg' d n : ℝ) / (ffDeg d n : ℝ)) atTop (𝓝 1) := by
  have hquot : Tendsto (fun n : ℕ => ((ffDefect d n : ℝ) / 2 ^ n) / ffNormDeg d n)
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => ((ffDefect d n : ℝ) / 2 ^ n) / ffNormDeg d n) atTop
        (𝓝 (0 / ffGrowthConstant d)) :=
      (tendsto_ffDefect_div_two_pow' d).div (tendsto_ffNormDeg d) (ne_of_gt h)
    simpa using h0
  have hc := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub hquot
  simp only [sub_zero] at hc
  exact hc.congr (fun n => (ffDeg'_div_ffDeg_eq d n).symm)

/-- **The dichotomy over `𝔽_p[t]`, sharp.**  Either the Euclid polynomial is reducible
infinitely often — and then the growth constant vanishes — or the sequence is eventually
perpetually irreducible, and then its least-degree irreducible factor has degree
`(1 - o(1)) deg (ffProd n)` and the growth constant is positive.  As over `ℤ`, the second
alternative is *not* wider than perpetual irreducibility: by trial division a factor of
more than half the degree is the whole polynomial. -/
theorem ffDefect_dichotomy (d : FFEMData p) :
    (FFInfinitelyManyReducible d ∧ ffGrowthConstant d = 0) ∨
      ((∃ N : ℕ, FFPerpetualIrreducibility d N) ∧ 0 < ffGrowthConstant d ∧
        Tendsto (fun n : ℕ => (ffDeg' d n : ℝ) / (ffDeg d n : ℝ)) atTop (𝓝 1)) := by
  rcases eq_or_lt_of_le (ffGrowthConstant_nonneg d) with h | h
  · exact Or.inl ⟨ffInfinitelyManyReducible_of_ffGrowthConstant_eq_zero h.symm, h.symm⟩
  · exact Or.inr ⟨(ffGrowthConstant_pos_iff_perpetual d).mp h, h,
      tendsto_ffDeg'_div_ffDeg_of_pos h⟩

/-! ## Landscape -/

/-- **The degree telescope over `𝔽_p[t]`.**  The whole of
`EM/Population/DefectTelescope.lean` transfers, and the two approximations of the integer
model — the negative-defect error term and the absence of an integrality gap — are
replaced by exact statements.  Neither gain reaches the tail, which is where the question
lives. -/
theorem ff_degree_telescope_landscape (d : FFEMData p) :
    -- the exact recursion and telescope
    (∀ n : ℕ, ffDeg d (n + 1) + ffDefect d n = 2 * ffDeg d n) ∧
    (∀ N : ℕ, ffNormDeg d N = 1 - ∑ n ∈ Finset.range N, (ffDefect d n : ℝ) / 2 ^ (n + 1)) ∧
    -- integrality: zero defect is exactly irreducibility
    (∀ n : ℕ, ffDefect d n = 0 ↔ Irreducible (d.ffProd n + 1)) ∧
    -- the growth constant exists, in `[0, 1]`
    Tendsto (ffNormDeg d) atTop (𝓝 (ffGrowthConstant d)) ∧
    0 ≤ ffGrowthConstant d ∧ ffGrowthConstant d ≤ 1 ∧
    -- trial division, exactly, and the damping bound it produces
    (∀ n : ℕ, ¬ Irreducible (d.ffProd n + 1) → 2 * ffDeg' d n ≤ ffDeg d n) ∧
    (∀ N : ℕ, (ffDeg d N : ℝ) ≤ (3 / 4 : ℝ) ^ ffReducibleCount d N * 2 ^ N) ∧
    -- (G_FF) is a complete invariant
    (FFInfinitelyManyReducible d ↔ ffGrowthConstant d = 0) ∧
    (0 < ffGrowthConstant d ↔ ∃ N : ℕ, FFPerpetualIrreducibility d N) ∧
    -- and the failure branch is the perpetual-irreducibility branch
    (0 < ffGrowthConstant d →
      Tendsto (fun n : ℕ => (ffDeg' d n : ℝ) / (ffDeg d n : ℝ)) atTop (𝓝 1)) :=
  ⟨ffDeg_succ_add_ffDefect d, ffNormDeg_eq_sub_sum d, ffDefect_eq_zero_iff d,
    tendsto_ffNormDeg d, ffGrowthConstant_nonneg d, ffGrowthConstant_le_one d,
    fun _ h => two_mul_ffDeg'_le_of_not_irreducible h, ffDeg_le_pow_mul d,
    ffInfinitelyManyReducible_iff_ffGrowthConstant_eq_zero d,
    ffGrowthConstant_pos_iff_perpetual d,
    fun h => tendsto_ffDeg'_div_ffDeg_of_pos h⟩

end FFDegreeTelescope

end
