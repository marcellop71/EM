import EM.Stochastic.EpsilonDegeneration
import EM.Stochastic.RandomFactorMC

/-!
# The Random Euclid–Mullin Process as a Theorem in its Own Right

## Overview

Euclid's argument does not say which prime factor of `P + 1` to take. Mullin's
first sequence takes the smallest; the second takes the largest and is known to
omit infinitely many primes (Cox–van der Poorten 1968, Booker 2012). The rule
with no bias at all takes a **uniformly random** prime factor. This file treats
the resulting **random Euclid–Mullin process** — from the standard start `2`,
and from arbitrary starts — as an object of study in itself, and sets up the
framework so that **any** selection rule (uniform, the `(1-ε)·minFac + ε·random`
mixture, or a rule skewed towards the least factor) is covered by the same
theorems.

## Selection kernels

A **selection kernel** is a function `w : ℕ → ℕ → ℝ`, `w P p` = probability of
choosing `p` at accumulator `P`, satisfying `IsKernel w`: non-negative, and
summing to `1` over the prime factors of `P + 1`. Every result below is stated
for an arbitrary kernel, specialised to:

* `uniformKernel` — the pure random rule (`= epsStepWeight 1`,
  `uniformKernel_eq_epsStepWeight_one`);
* `epsStepWeight ε` — the mixture, for `0 ≤ ε ≤ 1` (`isKernel_epsStepWeight`);
* any kernel with **full support**, `LowerBounded w λ`
  (`w P p ≥ λ / ω(P+1)` on the support): this is the only quantitative input
  the almost-sure theorems need, and it is what a min-skewed rule provides as
  long as no factor is starved.

The **failure weight** `failWeightK w q m n` is the exact probability that the
first `n` steps from `m` never select `q`; `failWeight ε q = failWeightK
(epsStepWeight ε) q` (`failWeight_eq_failWeightK`). Almost-sure capture is
`CapturesAS w q m := failWeightK w q m n → 0`.

## The random Mullin conjecture

* `RandomMC q := q = 2 ∨ CapturesAS uniformKernel q 2` and
  `RandomMullinConjecture := ∀ q prime, RandomMC q` — the conjecture in its own
  right: from `2`, the uniformly random Euclid process selects every prime almost
  surely.
* `RandomMCFrom m q := q ∣ m ∨ CapturesAS uniformKernel q m` — arbitrary start
  (`randomMCFrom_two_iff`).

## The three levels, and what is proved at each

For any kernel and any start `m ≥ 2` there is a strict hierarchy

  trapped   ⟺  `failWeightK ≡ 1`            (`failWeightK_eq_one_of_trapped`,
                                              `capturesAS_implies_reachable`)
  reachable ⟹  `failWeightK < 1` eventually  (`failWeightK_lt_one_of_reachable`)
  a.s.      ⟸  block-reachability + anatomy  (`capturesAS_of_blocks`)

with the first two unconditional. In particular almost-sure capture implies the
existential `PureRandomMC` (`randomMC_implies_pureRandomMC`), so the a.s.
conjecture is at least as strong as the (open) reachability conjecture, which is
itself equivalent to `MixedMC` (`pure_random_mc_iff_mixed_mc`).

## The general almost-sure engine

* `failWeightK_le_of_capture` — a valid path that first selects `q` at step `k`
  with weight `W` forces `failWeightK w q m N ≤ 1 - W` for `N > k`. (Any kernel.)
* `failWeightK_add_le` — block composition: if from every accumulator reachable
  in `a` `q`-avoiding steps the next `b` steps fail with weight `≤ C`, then
  `failWeightK m (a+b) ≤ failWeightK m a · C`.
* `failWeightK_le_prod_blocks` / `capturesAS_of_blocks` — iterating: block
  lengths `d j`, per-block capture weights `wt j`, `∑ wt = ∞` ⟹ a.s. capture.
  Block success at block `j` means: from every accumulator reachable
  `q`-avoiding at cumulative depth `D j`, there is a valid capturing path of
  length `≤ d j` and weight `≥ wt j`.

This isolates the two ingredients cleanly. **Reachability** (uniform block depth
along `q`-avoiding walks) is number theory of the factor tree; **anatomy** (the
weights `wt j`, i.e. `∏ 1/ω` along the path) is the distribution of `ω` on
Euclid numbers. Neither involves the kernel beyond `LowerBounded`.

## Two instances with unconditional reachability

* **`q = 3`, any start coprime to `3`, any lower-bounded kernel**
  (`three_capturesAS_of_omegaPair`): block depth `2` from
  `exists_three_opportunity_step`; anatomy `OmegaPairLB m v` —
  `v j ≤ 1 / (ω(P_{2j}+1)·ω(P_{2j+1}+1))` along `3`-avoiding walks — with
  `∑ v = ∞`. Specialisations: `three_random_almost_sure` (uniform, from `2`,
  i.e. `RandomMC 3` conditional on anatomy), `three_random_almost_sure_from`
  (uniform, any start), `three_eps_almost_sure_general` (the mixture, any
  `0 < ε ≤ 1`, any start — no parity, unlike `ThreeAlmostSure.lean`, at the
  cost of the pair-`ω` hypothesis).
* **`q = 2`, any odd start** (`two_capturesAS_of_omega_odd`): while `2` is
  avoided the accumulator stays odd, so `2 ∣ P + 1` at EVERY step — block depth
  `1`. Anatomy `OmegaLB m v` (`v j ≤ 1/ω(P_j+1)`) with `∑ v = ∞`.

## What is not here

For `q ≥ 5` from `2` the reachability input is open even in its existential form
(equivalent to `MixedMC q`), so no unconditional a.s. statement is possible yet;
`capturesAS_of_blocks` is the reduction. The anatomy hypotheses are stated
uniformly over `q`-avoiding walks (a single `v` for all of them); heuristically
`ω(P_k+1) ≍ √k` under the uniform rule (Golomb–Dickman: a random prime factor
has `log log` uniformly distributed), so `∑ 1/(ω_k ω_{k+1}) ≍ ∑ 1/k` diverges and
the hypotheses should hold, but no unconditional bound on `ω` of Euclid numbers
along walks is available.

## Contents

* Part 1: Kernels — `IsKernel`, `LowerBounded`, `uniformKernel`, `failWeightK`,
  bridge to `failWeight`
* Part 2: Basic properties — nonneg, `≤ 1`, antitone; `stepFailK`
* Part 3: Almost-sure capture and the random Mullin conjecture — `CapturesAS`,
  `RandomMC`, `RandomMullinConjecture`, `RandomMCFrom`
* Part 4: Trapped ⟺ failure weight `≡ 1` — `failWeightK_eq_one_of_trapped`,
  `capturesAS_implies_reachable`, `randomMC_implies_pureRandomMC`
* Part 5: Path weights and the capture upper bound — `pathWeightK`,
  `shiftSel`, `failWeightK_le_of_capture`, `failWeightK_lt_one_of_reachable`
* Part 6: Block composition — `failWeightK_add_le`, `failWeightK_le_prod_blocks`
* Part 7: The general almost-sure theorem — `capturesAS_of_blocks`
* Part 8: Extending a walk by one chosen factor — `spliceMinFac`
* Part 9: `q = 3` — `OmegaPairLB`, `three_capturesAS_of_omegaPair` and
  specialisations
* Part 10: `q = 2` from odd starts — `OmegaLB`, `two_capturesAS_of_omega_odd`
* Part 11: Landscape
-/

noncomputable section

open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Part 1: Selection Kernels -/

section Kernels

/-- A **selection kernel**: `w P p` is the probability of selecting `p` at
    accumulator `P`. Non-negative and summing to `1` over the prime factors of
    `P + 1` (for `P ≥ 1`, so that `P + 1 ≥ 2` has prime factors). -/
def IsKernel (w : ℕ → ℕ → ℝ) : Prop :=
  (∀ P p, 0 ≤ w P p) ∧ (∀ P, 1 ≤ P → ∑ p ∈ (P + 1).primeFactors, w P p = 1)

/-- **Full support with rate `λ`**: every prime factor of `P + 1` is selected
    with probability at least `λ / ω(P+1)`. The uniform kernel has `λ = 1`, the
    `ε`-mixture has `λ = ε`; a rule skewed towards the least factor qualifies
    as long as it does not starve any factor. This is the ONLY quantitative
    property of the kernel used by the almost-sure theorems. -/
def LowerBounded (w : ℕ → ℕ → ℝ) (lam : ℝ) : Prop :=
  ∀ P p, 1 ≤ P → p ∈ (P + 1).primeFactors →
    lam / ((P + 1).primeFactors.card : ℝ) ≤ w P p

/-- The **uniform kernel**: the pure random rule. -/
noncomputable def uniformKernel (P p : ℕ) : ℝ :=
  if p ∈ (P + 1).primeFactors then ((P + 1).primeFactors.card : ℝ)⁻¹ else 0

theorem uniformKernel_eq_epsStepWeight_one : uniformKernel = epsStepWeight 1 := by
  funext P p
  rw [epsStepWeight_one_eq_uniform]
  rfl

/-- The `ε`-mixture is a kernel for `0 ≤ ε ≤ 1`. -/
theorem isKernel_epsStepWeight {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    IsKernel (epsStepWeight ε) :=
  ⟨fun _ _ => epsStepWeight_nonneg hε0 hε1, fun _ hP => epsStepWeight_sum_one hP⟩

/-- The `ε`-mixture has full support with rate `ε`. -/
theorem lowerBounded_epsStepWeight {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    LowerBounded (epsStepWeight ε) ε :=
  fun _ _ _ hp => epsStepWeight_ge_eps_div_omega hε0 hε1 hp

theorem isKernel_uniformKernel : IsKernel uniformKernel := by
  rw [uniformKernel_eq_epsStepWeight_one]
  exact isKernel_epsStepWeight zero_le_one le_rfl

/-- The uniform kernel has full support with rate `1`. -/
theorem lowerBounded_uniformKernel : LowerBounded uniformKernel 1 := by
  rw [uniformKernel_eq_epsStepWeight_one]
  exact lowerBounded_epsStepWeight zero_le_one le_rfl

/-- **Failure weight under a kernel**: the exact probability that the first `n`
    steps from `m` never select `q`. -/
noncomputable def failWeightK (w : ℕ → ℕ → ℝ) (q : ℕ) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | m, n + 1 =>
      ∑ p ∈ (m + 1).primeFactors.erase q, w m p * failWeightK w q (m * p) n

@[simp] theorem failWeightK_zero (w : ℕ → ℕ → ℝ) (q m : ℕ) : failWeightK w q m 0 = 1 := rfl

theorem failWeightK_succ (w : ℕ → ℕ → ℝ) (q m n : ℕ) :
    failWeightK w q m (n + 1) =
      ∑ p ∈ (m + 1).primeFactors.erase q, w m p * failWeightK w q (m * p) n := rfl

/-- The `ε`-process failure weight of `ThreeAlmostSure.lean` is the kernel
    failure weight of `epsStepWeight ε`. -/
theorem failWeight_eq_failWeightK (ε : ℝ) (q : ℕ) :
    ∀ n m, failWeight ε q m n = failWeightK (epsStepWeight ε) q m n := by
  intro n
  induction n with
  | zero => intro m; rfl
  | succ n ih =>
    intro m
    rw [failWeight_succ, failWeightK_succ]
    exact Finset.sum_congr rfl (fun p _ => by rw [ih])

end Kernels

/-! ## Part 2: Basic Properties -/

section Basic

variable {w : ℕ → ℕ → ℝ}

/-- One-step avoid-`q` weight. -/
noncomputable def stepFailK (w : ℕ → ℕ → ℝ) (q m : ℕ) : ℝ :=
  ∑ p ∈ (m + 1).primeFactors.erase q, w m p

theorem stepFailK_le_one (hK : IsKernel w) {m : ℕ} (hm : 1 ≤ m) (q : ℕ) :
    stepFailK w q m ≤ 1 := by
  rw [stepFailK, ← hK.2 m hm]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    (fun _ _ _ => hK.1 _ _)

theorem stepFailK_eq_one_sub (hK : IsKernel w) {m : ℕ} (hm : 1 ≤ m) {q : ℕ}
    (hq : q ∈ (m + 1).primeFactors) : stepFailK w q m = 1 - w m q := by
  have h := Finset.add_sum_erase _ (w m) hq
  rw [hK.2 m hm] at h
  rw [stepFailK]; linarith

theorem failWeightK_nonneg (hK : IsKernel w) (q : ℕ) :
    ∀ n m, 0 ≤ failWeightK w q m n := by
  intro n
  induction n with
  | zero => intro m; simp
  | succ n ih =>
    intro m
    rw [failWeightK_succ]
    exact Finset.sum_nonneg (fun p _ => mul_nonneg (hK.1 _ _) (ih _))

theorem failWeightK_le_one (hK : IsKernel w) (q : ℕ) :
    ∀ n m, 1 ≤ m → failWeightK w q m n ≤ 1 := by
  intro n
  induction n with
  | zero => intro m _; simp
  | succ n ih =>
    intro m hm
    rw [failWeightK_succ]
    calc ∑ p ∈ (m + 1).primeFactors.erase q, w m p * failWeightK w q (m * p) n
        ≤ ∑ p ∈ (m + 1).primeFactors.erase q, w m p := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hp2 : 2 ≤ p :=
            (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).two_le
          calc w m p * failWeightK w q (m * p) n
              ≤ w m p * 1 := mul_le_mul_of_nonneg_left (ih (m * p) (by nlinarith)) (hK.1 _ _)
            _ = w m p := mul_one _
      _ ≤ 1 := stepFailK_le_one hK hm q

/-- Bound the failure weight after one more step by the one-step avoid weight. -/
theorem failWeightK_succ_le_stepFailK (hK : IsKernel w) (q m n : ℕ) (hm : 1 ≤ m) :
    failWeightK w q m (n + 1) ≤ stepFailK w q m := by
  rw [failWeightK_succ, stepFailK]
  refine Finset.sum_le_sum (fun p hp => ?_)
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).two_le
  calc w m p * failWeightK w q (m * p) n
      ≤ w m p * 1 :=
        mul_le_mul_of_nonneg_left (failWeightK_le_one hK q n (m * p) (by nlinarith)) (hK.1 _ _)
    _ = w m p := mul_one _

theorem failWeightK_succ_le (hK : IsKernel w) (q : ℕ) :
    ∀ n m, 1 ≤ m → failWeightK w q m (n + 1) ≤ failWeightK w q m n := by
  intro n
  induction n with
  | zero =>
    intro m hm
    rw [failWeightK_zero]
    exact failWeightK_le_one hK q 1 m hm
  | succ n ih =>
    intro m hm
    rw [failWeightK_succ, failWeightK_succ]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).two_le
    exact mul_le_mul_of_nonneg_left (ih (m * p) (by nlinarith)) (hK.1 _ _)

/-- The failure weight is antitone in the horizon, hence convergent; its limit
    is the probability that `q` is never selected. -/
theorem failWeightK_antitone (hK : IsKernel w) (q : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    Antitone (failWeightK w q m) :=
  antitone_nat_of_succ_le (fun n => failWeightK_succ_le hK q n m hm)

end Basic

/-! ## Part 3: Almost-Sure Capture and the Random Mullin Conjecture -/

section Conjectures

/-- **Almost-sure capture** of `q` from `m` under the kernel `w`: the failure
    weight tends to `0`. Since `failWeightK` is antitone, this is exactly "the
    process selects `q` with probability `1`". -/
def CapturesAS (w : ℕ → ℕ → ℝ) (q m : ℕ) : Prop :=
  Filter.Tendsto (failWeightK w q m) Filter.atTop (nhds 0)

/-- **Random Mullin conjecture at `q`**: from the standard start `2`, the
    uniformly random Euclid process selects `q` almost surely. The disjunct
    `q = 2` is the usual convention: `2` is the start and, all later
    accumulators being even, is never a factor of `P + 1`. -/
def RandomMC (q : ℕ) : Prop := q = 2 ∨ CapturesAS uniformKernel q 2

/-- **The random Mullin conjecture**: every prime is captured almost surely by
    the uniformly random Euclid process from `2`. -/
def RandomMullinConjecture : Prop := ∀ q, q.Prime → RandomMC q

/-- Random Mullin conjecture at `q` from an arbitrary start `m`: primes dividing
    `m` divide every accumulator, hence never `P + 1`, and count as present. -/
def RandomMCFrom (m q : ℕ) : Prop := q ∣ m ∨ CapturesAS uniformKernel q m

theorem randomMCFrom_two_iff {q : ℕ} (hq : q.Prime) : RandomMCFrom 2 q ↔ RandomMC q := by
  unfold RandomMCFrom RandomMC
  constructor
  · rintro (h | h)
    · left; exact ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h)
    · right; exact h
  · rintro (h | h)
    · left; rw [h]
    · right; exact h

theorem randomMC_two : RandomMC 2 := Or.inl rfl

end Conjectures

/-! ## Part 4: Trapped ⟺ Failure Weight ≡ 1

If `-1` is not tree-reachable mod `q` from `m`, no valid walk ever has
`q ∣ P + 1`, so no kernel whatsoever can select `q`: the failure weight is
identically `1`. Contrapositively, almost-sure capture — under ANY kernel —
implies reachability. This is the a.s. ⟹ existential direction; the
existential level is the (open) `MixedMC` / `PureRandomMC`. -/

section Trapped

variable {w : ℕ → ℕ → ℝ}

/-- If `q ∣ m + 1` then `-1` is reachable at step `0`. -/
private theorem reachable_of_dvd_succ {q m : ℕ} (hq : q.Prime) (h : q ∣ m + 1) :
    (-1 : ZMod q) ∈ reachableEver q m := by
  have hmod : (m : ZMod q) = -1 := by
    have hc0 : ((m + 1 : ℕ) : ZMod q) = 0 := by rwa [ZMod.natCast_eq_zero_iff]
    have hc1 : (m : ZMod q) + 1 = 0 := by push_cast at hc0; exact hc0
    exact eq_neg_of_add_eq_zero_left hc1
  have _ := hq
  apply reachableAt_subset_reachableEver q m 0
  rw [reachableAt_zero, ← hmod]
  exact Set.mem_singleton _

/-- **Trapped ⟹ failure weight ≡ 1**, for every kernel. -/
theorem failWeightK_eq_one_of_trapped (hK : IsKernel w) {q : ℕ} (hq : q.Prime) :
    ∀ n m, 1 ≤ m → (-1 : ZMod q) ∉ reachableEver q m → failWeightK w q m n = 1 := by
  intro n
  induction n with
  | zero => intro m _ _; rfl
  | succ n ih =>
    intro m hm htrap
    have hqnot : q ∉ (m + 1).primeFactors := by
      intro hmem
      exact htrap (reachable_of_dvd_succ hq (Nat.dvd_of_mem_primeFactors hmem))
    rw [failWeightK_succ, Finset.erase_eq_of_notMem hqnot]
    calc ∑ p ∈ (m + 1).primeFactors, w m p * failWeightK w q (m * p) n
        = ∑ p ∈ (m + 1).primeFactors, w m p := by
          refine Finset.sum_congr rfl (fun p hp => ?_)
          have hpp := Nat.prime_of_mem_primeFactors hp
          have hpd := Nat.dvd_of_mem_primeFactors hp
          have hmp : 1 ≤ m * p := by have := hpp.two_le; nlinarith
          rw [ih (m * p) hmp (trapped_hereditary htrap p hpp hpd), mul_one]
      _ = 1 := hK.2 m hm

/-- **Almost-sure capture implies reachability**, for every kernel: if the failure
    weight tends to `0` then `-1` is tree-reachable mod `q` from `m`. -/
theorem capturesAS_implies_reachable (hK : IsKernel w) {q : ℕ} (hq : q.Prime)
    {m : ℕ} (hm : 1 ≤ m) (h : CapturesAS w q m) :
    (-1 : ZMod q) ∈ reachableEver q m := by
  by_contra htrap
  have hconst : failWeightK w q m = fun _ => (1 : ℝ) :=
    funext (fun n => failWeightK_eq_one_of_trapped hK hq n m hm htrap)
  rw [CapturesAS, hconst] at h
  have := tendsto_nhds_unique h tendsto_const_nhds
  norm_num at this

/-- The a.s. random Mullin conjecture at `q` implies the existential one
    (`PureRandomMC q`, equivalent to `MixedMC q`). -/
theorem randomMC_implies_pureRandomMC {q : ℕ} (hq : q.Prime) (h : RandomMC q) :
    PureRandomMC q := by
  rcases h with h2 | hAS
  · intro _; left; exact h2
  · rcases Nat.lt_or_ge q 3 with hlt | hge
    · have : q = 2 := by have := hq.two_le; omega
      intro _; left; exact this
    · exact (pure_random_mc_iff_reachable hq hge).mpr
        (capturesAS_implies_reachable isKernel_uniformKernel hq (by norm_num) hAS)

end Trapped

/-! ## Part 5: Path Weights and the Capture Upper Bound

The general lemma behind every almost-sure statement: a valid path that FIRST
selects `q` at step `k` and has weight `W` is excluded from the failure weight,
so `failWeightK w q m N ≤ 1 - W` for every `N > k`. Nothing about the kernel is
used beyond `IsKernel`. -/

section PathWeight

variable {w : ℕ → ℕ → ℝ}

/-- The weight of the first `n` steps of the walk `σ` from `m` under `w`. -/
noncomputable def pathWeightK (w : ℕ → ℕ → ℝ) (m : ℕ) (σ : MixedSelection) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, w (mixedWalkProd m σ i) (mixedWalkFactor m σ i)

@[simp] theorem pathWeightK_zero (m : ℕ) (σ : MixedSelection) : pathWeightK w m σ 0 = 1 := by
  simp [pathWeightK]

theorem pathWeightK_one (m : ℕ) (σ : MixedSelection) :
    pathWeightK w m σ 1 = w m (mixedWalkFactor m σ 0) := by
  simp [pathWeightK, mixedWalkProd_zero]

/-- The shifted selection: `σ` restarted after its first step. -/
def shiftSel (σ : MixedSelection) : MixedSelection := fun i => σ (1 + i)

theorem shiftSel_walk (m : ℕ) (σ : MixedSelection) (k : ℕ) :
    mixedWalkProd (m * mixedWalkFactor m σ 0) (shiftSel σ) k = mixedWalkProd m σ (1 + k) := by
  have h1 : mixedWalkProd m σ 1 = m * mixedWalkFactor m σ 0 := by
    rw [mixedWalkProd_succ, mixedWalkProd_zero]
  rw [mixedWalkProd_tail_restart m σ 1 k, h1]
  rfl

theorem shiftSel_factor (m : ℕ) (σ : MixedSelection) (k : ℕ) :
    mixedWalkFactor (m * mixedWalkFactor m σ 0) (shiftSel σ) k = mixedWalkFactor m σ (1 + k) := by
  cases hσ : σ (1 + k) with
  | none =>
    rw [mixedWalkFactor_none_eq_minFac _ (shiftSel σ) k hσ,
      mixedWalkFactor_none_eq_minFac m σ (1 + k) hσ, shiftSel_walk]
  | some p =>
    rw [mixedWalkFactor_some_eq _ (shiftSel σ) k p hσ, mixedWalkFactor_some_eq m σ (1 + k) p hσ]

theorem shiftSel_valid {m : ℕ} {σ : MixedSelection} (hv : ValidMixedSelection m σ) :
    ValidMixedSelection (m * mixedWalkFactor m σ 0) (shiftSel σ) := by
  intro k
  have hspec := hv (1 + k)
  show match shiftSel σ k with
    | none => True
    | some p => p.Prime ∧ p ∣ (mixedWalkProd (m * mixedWalkFactor m σ 0) (shiftSel σ) k + 1)
  rw [shiftSel_walk]
  exact hspec

theorem shiftSel_consSel (f : ℕ) (τ : MixedSelection) : shiftSel (consSel f τ) = τ := by
  funext i
  show consSel f τ (1 + i) = τ i
  rw [Nat.add_comm]
  rfl

theorem pathWeightK_succ' (m : ℕ) (σ : MixedSelection) (n : ℕ) :
    pathWeightK w m σ (n + 1) =
      w m (mixedWalkFactor m σ 0) *
        pathWeightK w (m * mixedWalkFactor m σ 0) (shiftSel σ) n := by
  rw [pathWeightK, Finset.prod_range_succ', mixedWalkProd_zero, mul_comm]
  congr 1
  rw [pathWeightK]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [shiftSel_walk, shiftSel_factor, Nat.add_comm 1 i]

/-- The factor at each step of a valid walk from `m ≥ 2` is a prime factor of
    `P_i + 1`. -/
theorem mixedWalkFactor_mem_primeFactors {m : ℕ} (hm : 2 ≤ m) {σ : MixedSelection}
    (hv : ValidMixedSelection m σ) (i : ℕ) :
    mixedWalkFactor m σ i ∈ (mixedWalkProd m σ i + 1).primeFactors :=
  Nat.mem_primeFactors.mpr ⟨mixedWalkFactor_prime m σ hv i (mixedWalkProd_ge_two m hm σ hv i),
    mixedWalkFactor_dvd m σ hv i, by have := mixedWalkProd_ge_two m hm σ hv i; omega⟩

/-- Path weights are positive under a kernel with full support. -/
theorem pathWeightK_pos {lam : ℝ} (hLB : LowerBounded w lam) (hlam : 0 < lam)
    {m : ℕ} (hm : 2 ≤ m) {σ : MixedSelection} (hv : ValidMixedSelection m σ) (n : ℕ) :
    0 < pathWeightK w m σ n := by
  rw [pathWeightK]
  refine Finset.prod_pos (fun i _ => ?_)
  have hP := mixedWalkProd_ge_two m hm σ hv i
  refine lt_of_lt_of_le ?_ (hLB _ _ (by omega) (mixedWalkFactor_mem_primeFactors hm hv i))
  apply div_pos hlam
  exact Nat.cast_pos.mpr (Nat.nonempty_primeFactors.mpr (by omega)).card_pos

/-- **Capture upper bound.** If the valid path `σ` from `m ≥ 2` first selects
    `q` at step `k` (`q`-avoiding before), then for every horizon `N > k`,
    `failWeightK w q m N ≤ 1 - pathWeightK w m σ (k + 1)`. -/
theorem failWeightK_le_of_capture (hK : IsKernel w) (q : ℕ) :
    ∀ (k N m : ℕ) (σ : MixedSelection), 2 ≤ m → ValidMixedSelection m σ → k < N →
      (∀ i, i < k → mixedWalkFactor m σ i ≠ q) → mixedWalkFactor m σ k = q →
      failWeightK w q m N ≤ 1 - pathWeightK w m σ (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro N m σ hm hv hk _ hcap
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hmem : q ∈ (m + 1).primeFactors := by
      have := mixedWalkFactor_mem_primeFactors hm hv 0
      rwa [mixedWalkProd_zero, hcap] at this
    rw [pathWeightK_one, hcap]
    calc failWeightK w q m (n + 1)
        ≤ stepFailK w q m := failWeightK_succ_le_stepFailK hK q m n (by omega)
      _ = 1 - w m q := stepFailK_eq_one_sub hK (by omega) hmem
  | succ k ih =>
    intro N m σ hm hv hk havoid hcap
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    set f := mixedWalkFactor m σ 0 with hf
    have hf0 : f ≠ q := havoid 0 (by omega)
    have hfmem : f ∈ (m + 1).primeFactors := by
      have := mixedWalkFactor_mem_primeFactors hm hv 0
      rwa [mixedWalkProd_zero] at this
    have hfmem' : f ∈ (m + 1).primeFactors.erase q := Finset.mem_erase.mpr ⟨hf0, hfmem⟩
    have hfp : f.Prime := Nat.prime_of_mem_primeFactors hfmem
    have hmf : 2 ≤ m * f := by have := hfp.two_le; nlinarith
    -- Induction hypothesis on the shifted walk from the child `m·f`.
    have hchild := ih n (m * f) (shiftSel σ) hmf (shiftSel_valid hv) (by omega)
      (fun i hi => by rw [shiftSel_factor]; exact havoid (1 + i) (by omega))
      (by rw [shiftSel_factor, Nat.add_comm 1 k]; exact hcap)
    -- Split off the `f` branch; bound the rest by its total weight.
    have hsplit := Finset.add_sum_erase _
      (fun p => w m p * failWeightK w q (m * p) n) hfmem'
    have hrest : ∑ p ∈ ((m + 1).primeFactors.erase q).erase f,
        w m p * failWeightK w q (m * p) n
        ≤ ∑ p ∈ (m + 1).primeFactors.erase f, w m p := by
      calc ∑ p ∈ ((m + 1).primeFactors.erase q).erase f, w m p * failWeightK w q (m * p) n
          ≤ ∑ p ∈ ((m + 1).primeFactors.erase q).erase f, w m p := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors
              (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp))).two_le
            calc w m p * failWeightK w q (m * p) n
                ≤ w m p * 1 := mul_le_mul_of_nonneg_left
                  (failWeightK_le_one hK q n (m * p) (by nlinarith)) (hK.1 _ _)
              _ = w m p := mul_one _
        _ ≤ ∑ p ∈ (m + 1).primeFactors.erase f, w m p := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => hK.1 _ _)
            intro x hx
            exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hx,
              Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)⟩
    have htot : w m f + ∑ p ∈ (m + 1).primeFactors.erase f, w m p = 1 := by
      rw [Finset.add_sum_erase _ (w m) hfmem]
      exact hK.2 m (by omega)
    have hwf : 0 ≤ w m f := hK.1 _ _
    rw [failWeightK_succ, ← hsplit, pathWeightK_succ']
    have hmain : w m f * failWeightK w q (m * f) n
        ≤ w m f * (1 - pathWeightK w (m * f) (shiftSel σ) (k + 1)) :=
      mul_le_mul_of_nonneg_left hchild hwf
    linarith

/-- **Reachable ⟹ eventually `< 1`**, for any kernel with full support: if
    `-1` is tree-reachable mod `q` from `m ≥ 2`, some finite horizon already has
    failure weight `< 1`. Together with `failWeightK_eq_one_of_trapped` this
    gives the exact dichotomy at the existential level. -/
theorem failWeightK_lt_one_of_reachable (hK : IsKernel w) {lam : ℝ}
    (hLB : LowerBounded w lam) (hlam : 0 < lam) {q : ℕ} (hq : q.Prime)
    {m : ℕ} (hm : 2 ≤ m) (hreach : (-1 : ZMod q) ∈ reachableEver q m) :
    ∃ N, failWeightK w q m N < 1 := by
  rw [reachableEver, Set.mem_iUnion] at hreach
  obtain ⟨n, σ, hv, hmod⟩ := hreach
  have hdvd : q ∣ mixedWalkProd m σ n + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [hmod]; ring
  obtain ⟨σ', hv', k, hk⟩ := hit_implies_capture' hq m σ hv n hdvd
  -- take the FIRST capture index
  have hex : ∃ j, mixedWalkFactor m σ' j = q := ⟨k, hk⟩
  set j := Nat.find hex with hj
  have hjcap : mixedWalkFactor m σ' j = q := Nat.find_spec hex
  have hjmin : ∀ i, i < j → mixedWalkFactor m σ' i ≠ q :=
    fun i hi => Nat.find_min hex hi
  refine ⟨j + 1, lt_of_le_of_lt
    (failWeightK_le_of_capture hK q j (j + 1) m σ' hm hv' (by omega) hjmin hjcap) ?_⟩
  linarith [pathWeightK_pos hLB hlam hm hv' (j + 1)]

end PathWeight

/-! ## Part 6: Block Composition

`failWeightK m (a + b) ≤ failWeightK m a · C` as soon as every accumulator
reachable in `a` `q`-avoiding steps fails over the next `b` steps with weight
`≤ C`. Iterated over blocks this yields `∏ (1 - wt j)`. -/

section Blocks

variable {w : ℕ → ℕ → ℝ}

/-- **Block composition.** -/
theorem failWeightK_add_le (hK : IsKernel w) (q : ℕ) :
    ∀ (a b m : ℕ) (C : ℝ), 1 ≤ m → 0 ≤ C →
      (∀ σ : MixedSelection, ValidMixedSelection m σ →
        (∀ i, i < a → mixedWalkFactor m σ i ≠ q) →
        failWeightK w q (mixedWalkProd m σ a) b ≤ C) →
      failWeightK w q m (a + b) ≤ failWeightK w q m a * C := by
  intro a
  induction a with
  | zero =>
    intro b m C _ _ h
    have := h minFacMixed (minFacMixed_valid m) (fun i hi => absurd hi (by omega))
    rw [mixedWalkProd_zero] at this
    simpa using this
  | succ a ih =>
    intro b m C hm hC h
    have hstep : a + 1 + b = (a + b) + 1 := by ring
    rw [hstep, failWeightK_succ, failWeightK_succ, Finset.sum_mul]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hpq : p ≠ q := Finset.ne_of_mem_erase hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
    have hpd : p ∣ m + 1 := Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
    have hmp : 1 ≤ m * p := by have := hpp.two_le; nlinarith
    -- the block hypothesis at the child, by lifting walks through `consSel p`
    have hchild : ∀ τ : MixedSelection, ValidMixedSelection (m * p) τ →
        (∀ i, i < a → mixedWalkFactor (m * p) τ i ≠ q) →
        failWeightK w q (mixedWalkProd (m * p) τ a) b ≤ C := by
      intro τ hτ havoid
      have hσv : ValidMixedSelection m (consSel p τ) := consSel_valid hpp hpd hτ
      have hσavoid : ∀ i, i < a + 1 → mixedWalkFactor m (consSel p τ) i ≠ q := by
        intro i hi
        cases i with
        | zero => rw [consSel_factor_zero]; exact hpq
        | succ i => rw [consSel_factor_succ]; exact havoid i (by omega)
      have := h (consSel p τ) hσv hσavoid
      rwa [consSel_walk_succ] at this
    have := ih b (m * p) C hmp hC hchild
    calc w m p * failWeightK w q (m * p) (a + b)
        ≤ w m p * (failWeightK w q (m * p) a * C) := mul_le_mul_of_nonneg_left this (hK.1 _ _)
      _ = w m p * failWeightK w q (m * p) a * C := by ring

/-- Cumulative depth of the first `j` blocks. -/
def blockDepth (d : ℕ → ℕ) (j : ℕ) : ℕ := ∑ i ∈ Finset.range j, d i

@[simp] theorem blockDepth_zero (d : ℕ → ℕ) : blockDepth d 0 = 0 := by simp [blockDepth]

theorem blockDepth_succ (d : ℕ → ℕ) (j : ℕ) : blockDepth d (j + 1) = blockDepth d j + d j := by
  simp [blockDepth, Finset.sum_range_succ]

theorem le_blockDepth (d : ℕ → ℕ) (hd : ∀ j, 1 ≤ d j) (j : ℕ) : j ≤ blockDepth d j := by
  induction j with
  | zero => simp
  | succ j ih => rw [blockDepth_succ]; have := hd j; omega

theorem blockDepth_mono (d : ℕ → ℕ) : Monotone (blockDepth d) :=
  monotone_nat_of_le_succ (fun j => by rw [blockDepth_succ]; omega)

/-- **Iterated block bound.** If at every block `j`, from every accumulator
    reachable `q`-avoiding at depth `blockDepth d j`, the next `d j` steps fail
    with weight `≤ 1 - wt j`, then after `K` blocks the failure weight is at most
    `∏_{j<K} (1 - wt j)`. -/
theorem failWeightK_le_prod_blocks (hK : IsKernel w) (q : ℕ) {m : ℕ} (hm : 1 ≤ m)
    (d : ℕ → ℕ) (wt : ℕ → ℝ) (hwt : ∀ j, wt j ≤ 1)
    (hblock : ∀ j, ∀ σ : MixedSelection, ValidMixedSelection m σ →
      (∀ i, i < blockDepth d j → mixedWalkFactor m σ i ≠ q) →
      failWeightK w q (mixedWalkProd m σ (blockDepth d j)) (d j) ≤ 1 - wt j) :
    ∀ K, failWeightK w q m (blockDepth d K) ≤ ∏ j ∈ Finset.range K, (1 - wt j) := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    rw [blockDepth_succ, Finset.prod_range_succ]
    have hC : 0 ≤ 1 - wt K := by linarith [hwt K]
    calc failWeightK w q m (blockDepth d K + d K)
        ≤ failWeightK w q m (blockDepth d K) * (1 - wt K) :=
          failWeightK_add_le hK q (blockDepth d K) (d K) m (1 - wt K) hm hC (hblock K)
      _ ≤ (∏ j ∈ Finset.range K, (1 - wt j)) * (1 - wt K) :=
          mul_le_mul_of_nonneg_right ih hC

end Blocks

/-! ## Part 7: The General Almost-Sure Theorem -/

section GeneralAS

variable {w : ℕ → ℕ → ℝ}

/-- Block success in **path form**: from every accumulator reachable
    `q`-avoiding at depth `blockDepth d j`, there is a valid path that first
    selects `q` within `d j` steps, of weight at least `wt j`. -/
def BlockCapture (w : ℕ → ℕ → ℝ) (q m : ℕ) (d : ℕ → ℕ) (wt : ℕ → ℝ) : Prop :=
  ∀ j, ∀ σ : MixedSelection, ValidMixedSelection m σ →
    (∀ i, i < blockDepth d j → mixedWalkFactor m σ i ≠ q) →
    ∃ (τ : MixedSelection) (k : ℕ),
      ValidMixedSelection (mixedWalkProd m σ (blockDepth d j)) τ ∧ k < d j ∧
      (∀ i, i < k → mixedWalkFactor (mixedWalkProd m σ (blockDepth d j)) τ i ≠ q) ∧
      mixedWalkFactor (mixedWalkProd m σ (blockDepth d j)) τ k = q ∧
      wt j ≤ pathWeightK w (mixedWalkProd m σ (blockDepth d j)) τ (k + 1)

/-- Path-form block success gives the failure-weight form. -/
theorem blockCapture_bound (hK : IsKernel w) {q m : ℕ} (hm : 2 ≤ m) {d : ℕ → ℕ}
    {wt : ℕ → ℝ} (h : BlockCapture w q m d wt) (j : ℕ) (σ : MixedSelection)
    (hv : ValidMixedSelection m σ)
    (havoid : ∀ i, i < blockDepth d j → mixedWalkFactor m σ i ≠ q) :
    failWeightK w q (mixedWalkProd m σ (blockDepth d j)) (d j) ≤ 1 - wt j := by
  obtain ⟨τ, k, hτ, hk, hτavoid, hτcap, hwt⟩ := h j σ hv havoid
  have hP : 2 ≤ mixedWalkProd m σ (blockDepth d j) := mixedWalkProd_ge_two m hm σ hv _
  calc failWeightK w q (mixedWalkProd m σ (blockDepth d j)) (d j)
      ≤ failWeightK w q (mixedWalkProd m σ (blockDepth d j)) (k + 1) :=
        failWeightK_antitone hK q (by omega) (by omega : k + 1 ≤ d j)
    _ ≤ 1 - pathWeightK w (mixedWalkProd m σ (blockDepth d j)) τ (k + 1) :=
        failWeightK_le_of_capture hK q k (k + 1) _ τ hP hτ (by omega) hτavoid hτcap
    _ ≤ 1 - wt j := by linarith

/-- **The general almost-sure theorem.** For any kernel `w`, prime `q` and start
    `m ≥ 2`: if there are block lengths `d j ≥ 1` and per-block capture weights
    `wt j ∈ [0, 1]` with `∑ wt = ∞` such that `BlockCapture w q m d wt` holds,
    then `q` is captured almost surely from `m`.

    `BlockCapture` packages the two ingredients separately: REACHABILITY (a
    capturing path of bounded length from every `q`-avoiding accumulator at each
    block boundary) and ANATOMY (the weight of that path, i.e. `∏ 1/ω` along it,
    is at least `wt j`, with divergent sum). -/
theorem capturesAS_of_blocks (hK : IsKernel w) {q m : ℕ} (hm : 2 ≤ m)
    (d : ℕ → ℕ) (hd : ∀ j, 1 ≤ d j) (wt : ℕ → ℝ) (hwt0 : ∀ j, 0 ≤ wt j) (hwt1 : ∀ j, wt j ≤ 1)
    (hdiv : Filter.Tendsto (fun K => ∑ j ∈ Finset.range K, wt j) Filter.atTop Filter.atTop)
    (hblock : BlockCapture w q m d wt) :
    CapturesAS w q m := by
  have hm1 : 1 ≤ m := by omega
  -- along block boundaries
  have hbdry : ∀ K, failWeightK w q m (blockDepth d K) ≤ ∏ j ∈ Finset.range K, (1 - wt j) :=
    failWeightK_le_prod_blocks hK q hm1 d wt hwt1
      (fun j σ hv havoid => blockCapture_bound hK hm hblock j σ hv havoid)
  have hprod := prod_one_sub_tendsto_zero hwt0 hwt1 hdiv
  have hbdry_tendsto : Filter.Tendsto (fun K => failWeightK w q m (blockDepth d K))
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun K => failWeightK_nonneg hK q _ m) hbdry hprod
  -- transfer to all horizons via antitonicity: `g n` = last block boundary `≤ n`
  let g : ℕ → ℕ := fun n => Nat.findGreatest (fun K => blockDepth d K ≤ n) n
  have hg_le : ∀ n, blockDepth d (g n) ≤ n := fun n =>
    Nat.findGreatest_spec (P := fun K => blockDepth d K ≤ n) (Nat.zero_le n) (by simp)
  have hg_top : Filter.Tendsto g Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.mpr (fun K => ⟨blockDepth d K, fun n hn => ?_⟩)
    exact Nat.le_findGreatest (le_trans (le_blockDepth d hd K) hn) hn
  refine squeeze_zero (fun n => failWeightK_nonneg hK q n m) (fun n => ?_)
    (hbdry_tendsto.comp hg_top)
  exact failWeightK_antitone hK q hm1 (hg_le n)

end GeneralAS

/-! ## Part 8: Extending a Walk by One Chosen Factor

To instantiate anatomy hypotheses (which quantify over valid walks from the
root) at a specific child `P·f` of a reachable accumulator `P`, we need "follow
`σ` for `n` steps, then choose `f`" as a valid walk from the root. -/

section Splice

/-- Follow `σ` for `n` steps, choose `f` at step `n`, then minFac forever. -/
def spliceMinFac (σ : MixedSelection) (n f : ℕ) : MixedSelection :=
  fun i => if i < n then σ i else if i = n then some f else none

theorem spliceMinFac_walk_le (m : ℕ) (σ : MixedSelection) (n f : ℕ) {k : ℕ} (hk : k ≤ n) :
    mixedWalkProd m (spliceMinFac σ n f) k = mixedWalkProd m σ k :=
  mixedWalkProd_depends_on_prefix m _ σ k (fun i hi => by simp [spliceMinFac, show i < n by omega])

theorem spliceMinFac_factor_lt (m : ℕ) (σ : MixedSelection) (n f : ℕ) {k : ℕ} (hk : k < n) :
    mixedWalkFactor m (spliceMinFac σ n f) k = mixedWalkFactor m σ k :=
  mixedWalkFactor_depends_on_prefix m _ σ k (fun i hi => by simp [spliceMinFac, show i < n by omega])

theorem spliceMinFac_factor_at (m : ℕ) (σ : MixedSelection) (n f : ℕ) :
    mixedWalkFactor m (spliceMinFac σ n f) n = f :=
  mixedWalkFactor_some_eq m _ n f (by simp [spliceMinFac])

theorem spliceMinFac_walk_succ (m : ℕ) (σ : MixedSelection) (n f : ℕ) :
    mixedWalkProd m (spliceMinFac σ n f) (n + 1) = mixedWalkProd m σ n * f := by
  rw [mixedWalkProd_succ, spliceMinFac_walk_le m σ n f le_rfl, spliceMinFac_factor_at]

theorem spliceMinFac_valid {m : ℕ} {σ : MixedSelection} (hv : ValidMixedSelection m σ)
    {n f : ℕ} (hf : f.Prime) (hfd : f ∣ mixedWalkProd m σ n + 1) :
    ValidMixedSelection m (spliceMinFac σ n f) := by
  intro k
  rcases lt_trichotomy k n with hlt | heq | hgt
  · have hspec := hv k
    show match spliceMinFac σ n f k with
      | none => True
      | some p => p.Prime ∧ p ∣ (mixedWalkProd m (spliceMinFac σ n f) k + 1)
    have hσk : spliceMinFac σ n f k = σ k := by simp [spliceMinFac, hlt]
    rw [hσk, spliceMinFac_walk_le m σ n f (le_of_lt hlt)]
    exact hspec
  · subst heq
    show match spliceMinFac σ k f k with
      | none => True
      | some p => p.Prime ∧ p ∣ (mixedWalkProd m (spliceMinFac σ k f) k + 1)
    have hσk : spliceMinFac σ k f k = some f := by simp [spliceMinFac]
    rw [hσk, spliceMinFac_walk_le m σ k f le_rfl]
    exact ⟨hf, hfd⟩
  · show match spliceMinFac σ n f k with
      | none => True
      | some p => p.Prime ∧ p ∣ (mixedWalkProd m (spliceMinFac σ n f) k + 1)
    have hσk : spliceMinFac σ n f k = none := by
      simp [spliceMinFac, show ¬ k < n by omega, show k ≠ n by omega]
    rw [hσk]
    trivial

end Splice

/-! ## Part 9: `q = 3` — Any Start Coprime to 3, Any Lower-Bounded Kernel

Reachability is unconditional with block depth `2` (`exists_three_opportunity_step`).
The anatomy hypothesis controls the product of two consecutive `ω`'s, because
under a general kernel BOTH reaching an opportunity and taking it cost `≍ 1/ω`
(there is no minFac bonus at `ε = 1`, and no parity is assumed). -/

section Three

variable {w : ℕ → ℕ → ℝ}

/-- **Pair-`ω` anatomy hypothesis** for `q = 3` from `m`: `v j` is a lower bound
    for `1 / (ω(P_{2j}+1) · ω(P_{2j+1}+1))` along every valid walk from `m` that
    avoids `3` during its first `2j` steps. -/
def OmegaPairLB (m : ℕ) (v : ℕ → ℝ) : Prop :=
  (∀ j, 0 ≤ v j ∧ v j ≤ 1) ∧
  ∀ σ : MixedSelection, ValidMixedSelection m σ → ∀ j : ℕ,
    (∀ i, i < 2 * j → mixedWalkFactor m σ i ≠ 3) →
    v j * ((mixedWalkProd m σ (2 * j) + 1).primeFactors.card : ℝ)
        * ((mixedWalkProd m σ (2 * j + 1) + 1).primeFactors.card : ℝ) ≤ 1

/-- The accumulator stays coprime to `q` while `q` is avoided. -/
theorem mixedWalkProd_coprime_of_avoid {q m : ℕ} (hq : q.Prime) (hm : 2 ≤ m)
    (hcop : Nat.Coprime m q) {σ : MixedSelection} (hv : ValidMixedSelection m σ) :
    ∀ n, (∀ i, i < n → mixedWalkFactor m σ i ≠ q) → Nat.Coprime (mixedWalkProd m σ n) q := by
  intro n
  induction n with
  | zero => intro _; rw [mixedWalkProd_zero]; exact hcop
  | succ n ih =>
    intro havoid
    rw [mixedWalkProd_succ]
    have hf : (mixedWalkFactor m σ n).Prime :=
      mixedWalkFactor_prime m σ hv n (mixedWalkProd_ge_two m hm σ hv n)
    have hfq : mixedWalkFactor m σ n ≠ q := havoid n (by omega)
    exact ((ih (fun i hi => havoid i (by omega))).symm.mul_right
      ((Nat.coprime_primes hf hq).mpr hfq).symm).symm

/-- The `3`-block: from any accumulator `P ≥ 2` coprime to `3`, a valid path
    first selecting `3` within `2` steps, of weight `≥ lam² · v` whenever
    `v ≤ 1/(ω(P+1)·ω(P'+1))` for the relevant continuation `P'`. Packaged as
    the `BlockCapture` for `d ≡ 2`, `wt j = lam² · v j`. -/
theorem three_blockCapture {lam : ℝ} (hLB : LowerBounded w lam)
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) {m : ℕ} (hm : 2 ≤ m) (hcop : Nat.Coprime m 3)
    {v : ℕ → ℝ} (hv : OmegaPairLB m v) :
    BlockCapture w 3 m (fun _ => 2) (fun j => lam ^ 2 * v j) := by
  intro j σ hσ havoid
  have hD : blockDepth (fun _ => 2) j = 2 * j := by simp [blockDepth, mul_comm]
  rw [hD] at havoid ⊢
  set P := mixedWalkProd m σ (2 * j) with hP
  have hP2 : 2 ≤ P := mixedWalkProd_ge_two m hm σ hσ _
  have hPcop : Nat.Coprime P 3 := mixedWalkProd_coprime_of_avoid Nat.prime_three hm hcop hσ _ havoid
  have hω_pos : ∀ Q : ℕ, 1 ≤ Q → (0 : ℝ) < ((Q + 1).primeFactors.card : ℝ) := fun Q hQ =>
    Nat.cast_pos.mpr (Nat.nonempty_primeFactors.mpr (by omega)).card_pos
  have hω_ge1 : ∀ Q : ℕ, 1 ≤ Q → (1 : ℝ) ≤ ((Q + 1).primeFactors.card : ℝ) := fun Q hQ => by
    exact_mod_cast (Nat.nonempty_primeFactors.mpr (by omega : 1 < Q + 1)).card_pos
  have hv0 : 0 ≤ v j := (hv.1 j).1
  by_cases h3 : 3 ∣ P + 1
  · -- Case A: opportunity now. Path: choose 3, weight ≥ lam/ω(P+1) ≥ lam² v j.
    have h3mem : 3 ∈ (P + 1).primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, by omega⟩
    refine ⟨consSel 3 minFacMixed, 0, consSel_valid Nat.prime_three h3 (minFacMixed_valid _),
      by norm_num, fun i hi => absurd hi (by omega), consSel_factor_zero _ _ _, ?_⟩
    rw [pathWeightK_one, consSel_factor_zero]
    -- anatomy at the pair (P_{2j}, P_{2j+1}) of σ itself
    have hpair := hv.2 σ hσ j havoid
    rw [← hP] at hpair
    have hω1 := hω_ge1 (mixedWalkProd m σ (2 * j + 1))
      (by have := mixedWalkProd_ge_two m hm σ hσ (2 * j + 1); omega)
    have hωP := hω_pos P (by omega)
    have hvω : v j * ((P + 1).primeFactors.card : ℝ) ≤ 1 := by
      have h0 : 0 ≤ v j * ((P + 1).primeFactors.card : ℝ) := mul_nonneg hv0 hωP.le
      have := mul_le_mul_of_nonneg_left hω1 h0
      linarith
    have hl2 : lam ^ 2 * v j ≤ lam * v j := by
      have : lam ^ 2 ≤ lam := by nlinarith
      exact mul_le_mul_of_nonneg_right this hv0
    calc lam ^ 2 * v j ≤ lam * v j := hl2
      _ ≤ lam / ((P + 1).primeFactors.card : ℝ) := by
          rw [le_div_iff₀ hωP]
          calc lam * v j * ((P + 1).primeFactors.card : ℝ)
              = lam * (v j * ((P + 1).primeFactors.card : ℝ)) := by ring
            _ ≤ lam * 1 := mul_le_mul_of_nonneg_left hvω hlam0.le
            _ = lam := mul_one _
      _ ≤ w P 3 := hLB P 3 (by omega) h3mem
  · -- Case B: escape to a child with the opportunity, then take it.
    obtain ⟨f, hf, hfd, hf3, hfopp⟩ := exists_three_opportunity_step P hP2 hPcop h3
    have hfmem : f ∈ (P + 1).primeFactors := Nat.mem_primeFactors.mpr ⟨hf, hfd, by omega⟩
    have hPf1 : 1 ≤ P * f := by have := hf.two_le; nlinarith
    have h3mem : 3 ∈ (P * f + 1).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_three, hfopp, by omega⟩
    set τ : MixedSelection := consSel f (consSel 3 minFacMixed) with hτ
    have hτv : ValidMixedSelection P τ :=
      consSel_valid hf hfd (consSel_valid Nat.prime_three hfopp (minFacMixed_valid _))
    refine ⟨τ, 1, hτv, by norm_num, ?_, ?_, ?_⟩
    · intro i hi
      obtain rfl : i = 0 := by omega
      rw [hτ, consSel_factor_zero]; exact hf3
    · rw [hτ, consSel_factor_succ, consSel_factor_zero]
    · -- weight = w P f · w (P f) 3 ≥ lam/ω(P+1) · lam/ω(Pf+1) ≥ lam² v j
      have hw : pathWeightK w P τ 2 = w P f * w (P * f) 3 := by
        rw [pathWeightK_succ', hτ, consSel_factor_zero, shiftSel_consSel, pathWeightK_one,
          consSel_factor_zero]
      rw [hw]
      -- anatomy at the pair (P, P·f) via the spliced walk from the root
      set σ' := spliceMinFac σ (2 * j) f with hσ'
      have hσ'v : ValidMixedSelection m σ' := spliceMinFac_valid hσ hf (by rw [← hP]; exact hfd)
      have hσ'avoid : ∀ i, i < 2 * j → mixedWalkFactor m σ' i ≠ 3 := by
        intro i hi; rw [hσ', spliceMinFac_factor_lt m σ _ f hi]; exact havoid i hi
      have hpair := hv.2 σ' hσ'v j hσ'avoid
      rw [hσ', spliceMinFac_walk_le m σ _ f le_rfl, spliceMinFac_walk_succ, ← hP] at hpair
      have hωP := hω_pos P (by omega)
      have hωPf := hω_pos (P * f) hPf1
      have h1 : lam / ((P + 1).primeFactors.card : ℝ) ≤ w P f := hLB P f (by omega) hfmem
      have h2 : lam / ((P * f + 1).primeFactors.card : ℝ) ≤ w (P * f) 3 :=
        hLB (P * f) 3 hPf1 h3mem
      have hprod : lam ^ 2 * v j ≤
          (lam / ((P + 1).primeFactors.card : ℝ)) * (lam / ((P * f + 1).primeFactors.card : ℝ)) := by
        rw [div_mul_div_comm, le_div_iff₀ (mul_pos hωP hωPf)]
        calc lam ^ 2 * v j * (((P + 1).primeFactors.card : ℝ) * ((P * f + 1).primeFactors.card : ℝ))
            = lam ^ 2 * (v j * ((P + 1).primeFactors.card : ℝ)
                * ((P * f + 1).primeFactors.card : ℝ)) := by ring
          _ ≤ lam ^ 2 * 1 := mul_le_mul_of_nonneg_left hpair (by positivity)
          _ = lam * lam := by ring
      have hnn1 : 0 ≤ lam / ((P + 1).primeFactors.card : ℝ) := by positivity
      have hnn2 : 0 ≤ lam / ((P * f + 1).primeFactors.card : ℝ) := by positivity
      calc lam ^ 2 * v j
          ≤ (lam / ((P + 1).primeFactors.card : ℝ)) * (lam / ((P * f + 1).primeFactors.card : ℝ)) :=
            hprod
        _ ≤ w P f * w (P * f) 3 :=
            mul_le_mul h1 h2 hnn2 (le_trans hnn1 h1)

/-- **Almost-sure capture of `3`, any start coprime to `3`, any lower-bounded
    kernel** — conditional only on the pair-`ω` anatomy hypothesis. -/
theorem three_capturesAS_of_omegaPair (hK : IsKernel w) {lam : ℝ} (hLB : LowerBounded w lam)
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) {m : ℕ} (hm : 2 ≤ m) (hcop : Nat.Coprime m 3)
    {v : ℕ → ℝ} (hv : OmegaPairLB m v)
    (hdiv : Filter.Tendsto (fun K => ∑ j ∈ Finset.range K, v j) Filter.atTop Filter.atTop) :
    CapturesAS w 3 m := by
  have hl2 : 0 < lam ^ 2 := by positivity
  refine capturesAS_of_blocks hK hm (fun _ => 2) (fun _ => by norm_num)
    (fun j => lam ^ 2 * v j) (fun j => mul_nonneg hl2.le (hv.1 j).1)
    (fun j => by
      have := (hv.1 j).2
      have h1 : lam ^ 2 ≤ 1 := by nlinarith
      nlinarith [(hv.1 j).1]) ?_
    (three_blockCapture hLB hlam0 hlam1 hm hcop hv)
  have := hdiv.const_mul_atTop hl2
  simpa [Finset.mul_sum] using this

/-- **`RandomMC 3`, conditional on anatomy**: from the standard start `2`, the
    uniformly random Euclid process selects `3` almost surely provided
    `OmegaPairLB 2 v` with `∑ v = ∞`. Reachability is unconditional. -/
theorem three_random_almost_sure {v : ℕ → ℝ} (hv : OmegaPairLB 2 v)
    (hdiv : Filter.Tendsto (fun K => ∑ j ∈ Finset.range K, v j) Filter.atTop Filter.atTop) :
    RandomMC 3 :=
  Or.inr (three_capturesAS_of_omegaPair isKernel_uniformKernel lowerBounded_uniformKernel
    one_pos le_rfl (le_refl 2) (by decide) hv hdiv)

/-- Uniform rule, arbitrary start `m ≥ 2` coprime to `3`. -/
theorem three_random_almost_sure_from {m : ℕ} (hm : 2 ≤ m) (hcop : Nat.Coprime m 3)
    {v : ℕ → ℝ} (hv : OmegaPairLB m v)
    (hdiv : Filter.Tendsto (fun K => ∑ j ∈ Finset.range K, v j) Filter.atTop Filter.atTop) :
    RandomMCFrom m 3 :=
  Or.inr (three_capturesAS_of_omegaPair isKernel_uniformKernel lowerBounded_uniformKernel
    one_pos le_rfl hm hcop hv hdiv)

/-- The `(1-ε)·minFac + ε·random` mixture, any `0 < ε ≤ 1`, any start `m ≥ 2`
    coprime to `3` — no parity assumption (contrast
    `three_almost_sure_capture_of_omega_divergence`, which needs `m` even and
    `ε < 1` but only the single-`ω` hypothesis). Stated for the `failWeight` of
    `ThreeAlmostSure.lean` via the bridge. -/
theorem three_eps_almost_sure_general {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (hm : 2 ≤ m) (hcop : Nat.Coprime m 3) {v : ℕ → ℝ} (hv : OmegaPairLB m v)
    (hdiv : Filter.Tendsto (fun K => ∑ j ∈ Finset.range K, v j) Filter.atTop Filter.atTop) :
    Filter.Tendsto (failWeight ε 3 m) Filter.atTop (nhds 0) := by
  have h := three_capturesAS_of_omegaPair (isKernel_epsStepWeight hε0.le hε1)
    (lowerBounded_epsStepWeight hε0.le hε1) hε0 hε1 hm hcop hv hdiv
  rw [CapturesAS] at h
  have heq : failWeight ε 3 m = failWeightK (epsStepWeight ε) 3 m :=
    funext (fun n => failWeight_eq_failWeightK ε 3 n m)
  rw [heq]; exact h

end Three

/-! ## Part 10: `q = 2` from Odd Starts

A different-start instance where reachability is trivial: while `2` is
avoided every factor is odd, the accumulator stays odd, and `2 ∣ P + 1` at
every step. Block depth `1`; anatomy is the single-`ω` hypothesis. -/

section Two

variable {w : ℕ → ℕ → ℝ}

/-- **Single-`ω` anatomy hypothesis**: `v j ≤ 1/ω(P_j+1)` along every valid walk
    from `m` avoiding `q` during its first `j` steps. -/
def OmegaLB (q m : ℕ) (v : ℕ → ℝ) : Prop :=
  (∀ j, 0 ≤ v j ∧ v j ≤ 1) ∧
  ∀ σ : MixedSelection, ValidMixedSelection m σ → ∀ j : ℕ,
    (∀ i, i < j → mixedWalkFactor m σ i ≠ q) →
    v j * ((mixedWalkProd m σ j + 1).primeFactors.card : ℝ) ≤ 1

/-- The accumulator stays odd while `2` is avoided. -/
theorem mixedWalkProd_odd_of_avoid {m : ℕ} (hm : 2 ≤ m) (hodd : Odd m)
    {σ : MixedSelection} (hv : ValidMixedSelection m σ) :
    ∀ n, (∀ i, i < n → mixedWalkFactor m σ i ≠ 2) → Odd (mixedWalkProd m σ n) := by
  intro n havoid
  have hcop := mixedWalkProd_coprime_of_avoid Nat.prime_two hm
    (Nat.coprime_two_right.mpr hodd) hv n havoid
  exact Nat.coprime_two_right.mp hcop

theorem two_blockCapture {lam : ℝ} (hLB : LowerBounded w lam)
    (hlam0 : 0 < lam) {m : ℕ} (hm : 2 ≤ m) (hodd : Odd m)
    {v : ℕ → ℝ} (hv : OmegaLB 2 m v) :
    BlockCapture w 2 m (fun _ => 1) (fun j => lam * v j) := by
  intro j σ hσ havoid
  have hD : blockDepth (fun _ => 1) j = j := by simp [blockDepth]
  rw [hD] at havoid ⊢
  set P := mixedWalkProd m σ j with hP
  have hP2 : 2 ≤ P := mixedWalkProd_ge_two m hm σ hσ _
  have hPodd : Odd P := mixedWalkProd_odd_of_avoid hm hodd hσ j havoid
  have h2 : 2 ∣ P + 1 := by rcases hPodd with ⟨t, ht⟩; omega
  have h2mem : 2 ∈ (P + 1).primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, by omega⟩
  refine ⟨consSel 2 minFacMixed, 0, consSel_valid Nat.prime_two h2 (minFacMixed_valid _),
    by norm_num, fun i hi => absurd hi (by omega), consSel_factor_zero _ _ _, ?_⟩
  rw [pathWeightK_one, consSel_factor_zero]
  have hωP : (0 : ℝ) < ((P + 1).primeFactors.card : ℝ) :=
    Nat.cast_pos.mpr (Nat.nonempty_primeFactors.mpr (by omega)).card_pos
  have hpair := hv.2 σ hσ j havoid
  rw [← hP] at hpair
  calc lam * v j ≤ lam / ((P + 1).primeFactors.card : ℝ) := by
        rw [le_div_iff₀ hωP]
        calc lam * v j * ((P + 1).primeFactors.card : ℝ)
            = lam * (v j * ((P + 1).primeFactors.card : ℝ)) := by ring
          _ ≤ lam * 1 := mul_le_mul_of_nonneg_left hpair hlam0.le
          _ = lam := mul_one _
    _ ≤ w P 2 := hLB P 2 (by omega) h2mem

/-- **Almost-sure capture of `2` from any odd start `m ≥ 3`, any lower-bounded
    kernel** — conditional only on the single-`ω` anatomy hypothesis. -/
theorem two_capturesAS_of_omega_odd (hK : IsKernel w) {lam : ℝ} (hLB : LowerBounded w lam)
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) {m : ℕ} (hm : 2 ≤ m) (hodd : Odd m)
    {v : ℕ → ℝ} (hv : OmegaLB 2 m v)
    (hdiv : Filter.Tendsto (fun K => ∑ j ∈ Finset.range K, v j) Filter.atTop Filter.atTop) :
    CapturesAS w 2 m := by
  refine capturesAS_of_blocks hK hm (fun _ => 1) (fun _ => le_rfl)
    (fun j => lam * v j) (fun j => mul_nonneg hlam0.le (hv.1 j).1)
    (fun j => by have := (hv.1 j); nlinarith) ?_
    (two_blockCapture hLB hlam0 hm hodd hv)
  have := hdiv.const_mul_atTop hlam0
  simpa [Finset.mul_sum] using this

/-- Uniform rule: `RandomMCFrom m 2` for odd `m ≥ 3`, conditional on anatomy. -/
theorem two_random_almost_sure_from_odd {m : ℕ} (hm : 2 ≤ m) (hodd : Odd m)
    {v : ℕ → ℝ} (hv : OmegaLB 2 m v)
    (hdiv : Filter.Tendsto (fun K => ∑ j ∈ Finset.range K, v j) Filter.atTop Filter.atTop) :
    RandomMCFrom m 2 :=
  Or.inr (two_capturesAS_of_omega_odd isKernel_uniformKernel lowerBounded_uniformKernel
    one_pos le_rfl hm hodd hv hdiv)

end Two

/-! ## Part 11: Landscape -/

section Landscape

/-- **The random-variant landscape.**

    1. Endpoints: the uniform kernel is `epsStepWeight 1`, and `failWeight ε` is
       the kernel failure weight of `epsStepWeight ε`.
    2. Trapped ⟹ failure weight `≡ 1` (any kernel); a.s. capture ⟹ reachable.
    3. `RandomMC` implies the existential `PureRandomMC` (`= MixedMC`).
    4. Reachable ⟹ eventually `< 1` (any lower-bounded kernel).
    5. The general engine: block reachability + anatomy ⟹ a.s. capture.
    6. `q = 3`, any start coprime to `3`, any lower-bounded kernel: a.s. capture
       from `OmegaPairLB` + divergence.
    7. `q = 2`, any odd start: a.s. capture from `OmegaLB` + divergence.
    8. `RandomMC 2` unconditionally; `RandomMC 3` conditional on anatomy. -/
theorem random_variant_landscape :
    -- 1
    (uniformKernel = epsStepWeight 1 ∧
      ∀ ε q n m, failWeight ε q m n = failWeightK (epsStepWeight ε) q m n) ∧
    -- 2
    (∀ w, IsKernel w → ∀ q, q.Prime → ∀ m, 1 ≤ m →
      ((-1 : ZMod q) ∉ reachableEver q m → ∀ n, failWeightK w q m n = 1) ∧
      (CapturesAS w q m → (-1 : ZMod q) ∈ reachableEver q m)) ∧
    -- 3
    (∀ q, q.Prime → RandomMC q → PureRandomMC q) ∧
    -- 4
    (∀ w lam, IsKernel w → LowerBounded w lam → 0 < lam → ∀ q, q.Prime → ∀ m, 2 ≤ m →
      (-1 : ZMod q) ∈ reachableEver q m → ∃ N, failWeightK w q m N < 1) ∧
    -- 5
    (∀ w, IsKernel w → ∀ q m, 2 ≤ m → ∀ (d : ℕ → ℕ) (wt : ℕ → ℝ),
      (∀ j, 1 ≤ d j) → (∀ j, 0 ≤ wt j) → (∀ j, wt j ≤ 1) →
      Filter.Tendsto (fun K => ∑ j ∈ Finset.range K, wt j) Filter.atTop Filter.atTop →
      BlockCapture w q m d wt → CapturesAS w q m) ∧
    -- 6
    (∀ w lam, IsKernel w → LowerBounded w lam → 0 < lam → lam ≤ 1 →
      ∀ m, 2 ≤ m → Nat.Coprime m 3 → ∀ v : ℕ → ℝ, OmegaPairLB m v →
      Filter.Tendsto (fun K => ∑ j ∈ Finset.range K, v j) Filter.atTop Filter.atTop →
      CapturesAS w 3 m) ∧
    -- 7
    (∀ w lam, IsKernel w → LowerBounded w lam → 0 < lam → lam ≤ 1 →
      ∀ m, 2 ≤ m → Odd m → ∀ v : ℕ → ℝ, OmegaLB 2 m v →
      Filter.Tendsto (fun K => ∑ j ∈ Finset.range K, v j) Filter.atTop Filter.atTop →
      CapturesAS w 2 m) ∧
    -- 8
    (RandomMC 2 ∧ ∀ v : ℕ → ℝ, OmegaPairLB 2 v →
      Filter.Tendsto (fun K => ∑ j ∈ Finset.range K, v j) Filter.atTop Filter.atTop →
      RandomMC 3) :=
  ⟨⟨uniformKernel_eq_epsStepWeight_one, fun ε q n m => failWeight_eq_failWeightK ε q n m⟩,
   fun _ hK _ hq _ hm => ⟨fun htrap n => failWeightK_eq_one_of_trapped hK hq n _ hm htrap,
     fun h => capturesAS_implies_reachable hK hq hm h⟩,
   fun _ hq h => randomMC_implies_pureRandomMC hq h,
   fun _ _ hK hLB hlam _ hq _ hm hr => failWeightK_lt_one_of_reachable hK hLB hlam hq hm hr,
   fun _ hK _ _ hm d wt hd h0 h1 hdiv hb => capturesAS_of_blocks hK hm d hd wt h0 h1 hdiv hb,
   fun _ _ hK hLB h0 h1 _ hm hcop _ hv hdiv =>
     three_capturesAS_of_omegaPair hK hLB h0 h1 hm hcop hv hdiv,
   fun _ _ hK hLB h0 h1 _ hm hodd _ hv hdiv =>
     two_capturesAS_of_omega_odd hK hLB h0 h1 hm hodd hv hdiv,
   ⟨randomMC_two, fun _ hv hdiv => three_random_almost_sure hv hdiv⟩⟩

end Landscape
