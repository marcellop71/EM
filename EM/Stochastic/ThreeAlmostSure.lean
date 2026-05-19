import EM.Stochastic.MissedPrimes
import EM.Stochastic.TransitionKernel

/-!
# Almost-Sure Capture of 3 by the (1-ε) Process, from a Genuine Failure Weight

## Overview

Every earlier "almost-sure" statement in this development is finitary in the weak
sense: it exhibits ONE path with positive `pathWeightLB`. That is a lower bound on
a single cylinder and cannot express "the process fails with probability → 0",
which is an upper bound on the total weight of ALL failing paths.

This file introduces that missing object and uses it to close the reachability
side of almost-sure capture of `q = 3`.

**The failure weight.** `failWeight ε q m n` is the exact `ε`-process probability
that the first `n` steps from accumulator `m` never select `q`:

  `failWeight ε q m 0       = 1`
  `failWeight ε q m (n + 1) = ∑_{p ∣ m+1 prime, p ≠ q} epsStepWeight ε m p *
                                failWeight ε q (m·p) n`

built from the exact per-step kernel `epsStepWeight` of
`EM/Stochastic/TransitionKernel.lean` (NOT from the conservative lower bound
`stepWeightLB`). It is a finite sum over a finite tree — no measure theory on
infinite paths — yet it is a genuine probability: it is the measure of the
horizon-`n` cylinder set of failing paths. It is antitone in `n`
(`failWeight_antitone`), so it converges, and by continuity from above its limit
IS the probability that `q` is never selected: `failWeight ε q m n → 0` is the
finitary form of "the process captures `q` almost surely". (The identification of
the limit with a measure is not itself formalized — that would need the path
measure of `EM/Stochastic/PathMeasure.lean` — but no step below uses it.)

## The q = 3 theorem

Two unconditional structural facts drive everything:

* **Uniform block depth 1** (`exists_three_opportunity_step`,
  `EM/Stochastic/TreeSieveDecay.lean`): from EVERY accumulator `P ≥ 2` coprime to
  `3`, either `3 ∣ P+1` already, or some prime `f ∣ P+1`, `f ≠ 3`, has
  `3 ∣ P·f + 1`. No hypotheses, no threshold.

* **Parity makes the opportunity cheap** (`minFac_succ_eq_three`): if the
  accumulator `P` is EVEN and `3 ∣ P+1`, then `minFac(P+1) = 3`. So at an
  opportunity the *deterministic* branch already captures `3`, and
  `epsStepWeight ε P 3 ≥ 1 - ε` — a cost independent of `ω`.

Accumulators of the standard Euclid–Mullin process are even (the walk starts at
`2` and only multiplies), so parity is free there. This is the reason the residual
hypothesis is a divergence of `Σ 1/ω` rather than `Σ 1/(ω ω')`: only the
*reaching* of an opportunity costs `ε/ω`, never the *taking* of it. Since
`ω(P+1) ≈ log log P ≈ k` heuristically along a walk with doubly-exponential
growth, `Σ 1/ω` diverges (like `Σ 1/k`) while `Σ 1/(ω ω')` would not (like
`Σ 1/k²`). Parity is what makes the hypothesis credible rather than false.

**Main theorem** (`three_almost_sure_capture_of_omega_divergence`): let
`0 < ε < 1`, let `m ≥ 2` be even and coprime to `3`, and suppose there is a
sequence `v` with

* `OmegaBlockLB m v` — `v j ≤ 1/ω(P_{2j} + 1)` along every valid walk from `m`
  that has not yet selected `3` (an ANATOMY bound on Euclid numbers: nothing
  about reachability), and
* `∑_{j<K} v j → ∞`.

Then `failWeight ε 3 m n → 0`: the `(1-ε)·minFac + ε·random` process captures `3`
almost surely.

The reachability side is fully discharged; `OmegaBlockLB` + divergence is a
statement purely about `ω` of the Euclid numbers along walks. This is the exact
sense in which "the residual gap for `q = 3` is anatomy, not reachability".

## Scoping

`OmegaBlockLB` is UNIFORM over the (still very large) set of `3`-avoiding walks:
a single deterministic `v` must under-estimate `1/ω` along all of them. Only
walks that have not yet captured `3` are constrained — walks that already
captured contribute nothing to `failWeight` — but no genuinely path-dependent
(almost-sure-in-the-path) weakening is available in this finitary framework,
because `failWeight` aggregates all surviving branches at once. Weakening the
uniformity to an a.s.-in-the-path condition is the natural next step and would
need the branch-wise decomposition of `failWeight` rather than the crude
`sup`-style bound of Part 5.

The hypothesis is not vacuous in either direction: `v = 0` satisfies
`OmegaBlockLB` but has convergent partial sums, so divergence carries the whole
content; and heuristically `v j ≍ 1/j` is admissible, so the hypothesis should
be true — but the only unconditional bound available, `ω(N) ≤ log₂ N`, gives
`v j ≍ 2^{-j}` on doubly-exponentially growing accumulators, which is far too
weak. Establishing (or refuting) it is a question about the anatomy of Euclid
numbers, of the same flavour as the normal order of `ω`.

## Contents

* Part 1: Cons selections — `consSel` and its walk/validity lemmas
* Part 2: The failure weight — `failWeight`, `stepFail`, nonnegativity, `≤ 1`,
  antitonicity
* Part 3: Parity — `minFac_succ_eq_three`, `epsStepWeight_three_ge`,
  `minFac_captures_three` (unconditional: the pure minFac rule captures `3` at
  every even accumulator with `3 ∣ P+1`)
* Part 4: The anatomy hypothesis — `OmegaBlockLB`, `omegaBlockLB_le_one`,
  `omegaBlockLB_shift`
* Part 5: The two-step block bound — `failWeight_le_block_prod`
* Part 6: Divergence kills the product — `prod_one_sub_tendsto_zero`
* Part 7: Main theorem — `three_almost_sure_capture_of_omega_divergence`,
  `three_almost_sure_capture_from_two`
* Part 8: Landscape — `three_almost_sure_landscape`
-/

noncomputable section

open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Part 1: Cons Selections

`consSel f τ` prepends the choice `f` to the selection `τ`. It is the one-step
version of `spliceSelection`; we need it to transport a walk from a grandchild
`m·p·p'` back to a walk from `m`, which is how the anatomy hypothesis is
inherited by grandchildren in the block induction. -/

section ConsSel

/-- Prepend the choice `f` to the selection `τ`. -/
def consSel (f : ℕ) (τ : MixedSelection) : MixedSelection
  | 0 => some f
  | j + 1 => τ j

@[simp] theorem consSel_zero (f : ℕ) (τ : MixedSelection) : consSel f τ 0 = some f := rfl

@[simp] theorem consSel_succ (f : ℕ) (τ : MixedSelection) (j : ℕ) :
    consSel f τ (j + 1) = τ j := rfl

/-- The tail of `consSel f τ` is `τ`. -/
theorem consSel_tail (f : ℕ) (τ : MixedSelection) :
    (fun i => consSel f τ (1 + i)) = τ := by
  funext i
  rw [Nat.add_comm 1 i]
  rfl

/-- The walk of a cons selection, one step in, is the walk from the child. -/
theorem consSel_walk_succ (m f : ℕ) (τ : MixedSelection) (j : ℕ) :
    mixedWalkProd m (consSel f τ) (j + 1) = mixedWalkProd (m * f) τ j := by
  have h1 : mixedWalkProd m (consSel f τ) 1 = m * f := by
    rw [mixedWalkProd_succ, mixedWalkProd_zero,
      mixedWalkFactor_some_eq m (consSel f τ) 0 f rfl]
  have := mixedWalkProd_tail_restart m (consSel f τ) 1 j
  rw [h1, consSel_tail] at this
  rw [Nat.add_comm j 1]
  exact this

/-- A cons selection is valid when the prepended choice is a prime dividing
    `m + 1` and the tail is valid from the child `m·f`. -/
theorem consSel_valid {m f : ℕ} (hf : f.Prime) (hfd : f ∣ m + 1)
    {τ : MixedSelection} (hτ : ValidMixedSelection (m * f) τ) :
    ValidMixedSelection m (consSel f τ) := by
  intro k
  cases k with
  | zero =>
    show match consSel f τ 0 with
      | none => True
      | some p => p.Prime ∧ p ∣ (mixedWalkProd m (consSel f τ) 0 + 1)
    rw [consSel_zero, mixedWalkProd_zero]
    exact ⟨hf, hfd⟩
  | succ j =>
    have hspec := hτ j
    show match consSel f τ (j + 1) with
      | none => True
      | some p => p.Prime ∧ p ∣ (mixedWalkProd m (consSel f τ) (j + 1) + 1)
    rw [consSel_succ, consSel_walk_succ]
    exact hspec

/-- The first factor of a cons selection is the prepended choice. -/
theorem consSel_factor_zero (m f : ℕ) (τ : MixedSelection) :
    mixedWalkFactor m (consSel f τ) 0 = f :=
  mixedWalkFactor_some_eq m (consSel f τ) 0 f rfl

/-- Later factors of a cons selection are the factors of the walk from the child. -/
theorem consSel_factor_succ (m f : ℕ) (τ : MixedSelection) (j : ℕ) :
    mixedWalkFactor m (consSel f τ) (j + 1) = mixedWalkFactor (m * f) τ j := by
  cases hτj : τ j with
  | none =>
    rw [mixedWalkFactor_none_eq_minFac m (consSel f τ) (j + 1) (by rw [consSel_succ, hτj]),
      mixedWalkFactor_none_eq_minFac (m * f) τ j hτj, consSel_walk_succ]
  | some p =>
    rw [mixedWalkFactor_some_eq m (consSel f τ) (j + 1) p (by rw [consSel_succ, hτj]),
      mixedWalkFactor_some_eq (m * f) τ j p hτj]

end ConsSel

/-! ## Part 2: The Failure Weight

`failWeight ε q m n` is the exact probability, under the `ε`-process, that the
first `n` steps from `m` never select `q`. Unlike `pathWeightLB` (a lower bound on
ONE path) this is an upper bound on ALL failing paths, which is what an
almost-sure statement requires. -/

section FailWeight

/-- Total `ε`-process weight of the one-step choices that AVOID `q`. -/
noncomputable def stepFail (ε : ℝ) (q m : ℕ) : ℝ :=
  ∑ p ∈ (m + 1).primeFactors.erase q, epsStepWeight ε m p

/-- **Failure weight**: the exact `ε`-process probability that the first `n`
    steps of the mixed walk from accumulator `m` never select the prime `q`.
    A finite sum over the depth-`n` factor tree; no measure theory needed. -/
noncomputable def failWeight (ε : ℝ) (q : ℕ) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | m, n + 1 =>
      ∑ p ∈ (m + 1).primeFactors.erase q, epsStepWeight ε m p * failWeight ε q (m * p) n

@[simp] theorem failWeight_zero (ε : ℝ) (q m : ℕ) : failWeight ε q m 0 = 1 := rfl

theorem failWeight_succ (ε : ℝ) (q m n : ℕ) :
    failWeight ε q m (n + 1) =
      ∑ p ∈ (m + 1).primeFactors.erase q,
        epsStepWeight ε m p * failWeight ε q (m * p) n := rfl

theorem failWeight_one (ε : ℝ) (q m : ℕ) : failWeight ε q m 1 = stepFail ε q m := by
  rw [failWeight_succ, stepFail]
  exact Finset.sum_congr rfl (fun p _ => by rw [failWeight_zero, mul_one])

variable {ε : ℝ}

/-- The avoid-`q` step weight is non-negative. -/
theorem stepFail_nonneg (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (q m : ℕ) :
    0 ≤ stepFail ε q m :=
  Finset.sum_nonneg (fun _ _ => epsStepWeight_nonneg hε0 hε1)

/-- The avoid-`q` step weight is at most `1`: it is a sub-sum of a distribution. -/
theorem stepFail_le_one (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {m : ℕ} (hm : 1 ≤ m) (q : ℕ) :
    stepFail ε q m ≤ 1 := by
  rw [stepFail, ← epsStepWeight_sum_one (ε := ε) hm]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    (fun _ _ _ => epsStepWeight_nonneg hε0 hε1)

/-- If `q` is itself an available choice, the avoid-`q` weight loses exactly
    `epsStepWeight ε m q`. -/
theorem stepFail_eq_one_sub {m : ℕ} (hm : 1 ≤ m) {q : ℕ} (hq : q ∈ (m + 1).primeFactors) :
    stepFail ε q m = 1 - epsStepWeight ε m q := by
  have h := Finset.add_sum_erase _ (epsStepWeight ε m) hq
  rw [epsStepWeight_sum_one (ε := ε) hm] at h
  rw [stepFail]
  linarith

/-- The failure weight is non-negative. -/
theorem failWeight_nonneg (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (q : ℕ) :
    ∀ (n m : ℕ), 1 ≤ m → 0 ≤ failWeight ε q m n := by
  intro n
  induction n with
  | zero => intro m _; rw [failWeight_zero]; norm_num
  | succ n ih =>
    intro m hm
    rw [failWeight_succ]
    refine Finset.sum_nonneg (fun p hp => ?_)
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).two_le
    exact mul_nonneg (epsStepWeight_nonneg hε0 hε1) (ih (m * p) (by nlinarith))

/-- The failure weight is at most `1`: it is the measure of a set of paths. -/
theorem failWeight_le_one (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (q : ℕ) :
    ∀ (n m : ℕ), 1 ≤ m → failWeight ε q m n ≤ 1 := by
  intro n
  induction n with
  | zero => intro m _; rw [failWeight_zero]
  | succ n ih =>
    intro m hm
    rw [failWeight_succ]
    calc ∑ p ∈ (m + 1).primeFactors.erase q, epsStepWeight ε m p * failWeight ε q (m * p) n
        ≤ ∑ p ∈ (m + 1).primeFactors.erase q, epsStepWeight ε m p := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).two_le
          have hmp : 1 ≤ m * p := by nlinarith
          calc epsStepWeight ε m p * failWeight ε q (m * p) n
              ≤ epsStepWeight ε m p * 1 :=
                mul_le_mul_of_nonneg_left (ih (m * p) hmp) (epsStepWeight_nonneg hε0 hε1)
            _ = epsStepWeight ε m p := mul_one _
      _ ≤ 1 := stepFail_le_one hε0 hε1 hm q

/-- One more step can only decrease the failure weight. -/
theorem failWeight_succ_le (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (q : ℕ) :
    ∀ (n m : ℕ), 1 ≤ m → failWeight ε q m (n + 1) ≤ failWeight ε q m n := by
  intro n
  induction n with
  | zero =>
    intro m hm
    rw [failWeight_zero, failWeight_one]
    exact stepFail_le_one hε0 hε1 hm q
  | succ n ih =>
    intro m hm
    rw [failWeight_succ, failWeight_succ]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).two_le
    exact mul_le_mul_of_nonneg_left (ih (m * p) (by nlinarith))
      (epsStepWeight_nonneg hε0 hε1)

/-- The failure weight is antitone in the horizon, hence convergent; its limit is
    the probability that `q` is never selected. `failWeight ε q m n → 0` is the
    finitary form of "the process captures `q` almost surely". -/
theorem failWeight_antitone (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (q : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    Antitone (failWeight ε q m) :=
  antitone_nat_of_succ_le (fun n => failWeight_succ_le hε0 hε1 q n m hm)

end FailWeight

/-! ## Part 3: Parity Makes the Opportunity Cheap

The accumulator of the standard Euclid–Mullin process is even (it starts at `2`
and only ever gets multiplied). Then `P + 1` is odd, so as soon as `3 ∣ P + 1` the
smallest prime factor of `P + 1` IS `3`: the deterministic branch of the
`ε`-process captures `3` by itself, at weight `≥ 1 - ε` — no `ω` in sight. -/

section Parity

/-- **Parity forces minFac**: if `P` is even and `3 ∣ P + 1`, then
    `minFac (P + 1) = 3`. (`P + 1` is odd, so `2` is excluded, and `3` divides,
    so the least prime factor is at most `3`.) -/
theorem minFac_succ_eq_three {P : ℕ} (_hP : 1 ≤ P) (heven : Even P) (h3 : 3 ∣ P + 1) :
    (P + 1).minFac = 3 := by
  have hodd : ¬(2 ∣ P + 1) := by
    rcases heven with ⟨t, ht⟩
    omega
  have hprime : (P + 1).minFac.Prime := Nat.minFac_prime (by omega)
  have hle : (P + 1).minFac ≤ 3 := Nat.minFac_le_of_dvd (by norm_num) h3
  have hge : 2 ≤ (P + 1).minFac := hprime.two_le
  have hne2 : (P + 1).minFac ≠ 2 := by
    intro h
    exact hodd (h ▸ Nat.minFac_dvd (P + 1))
  omega

/-- **The pure minFac rule captures 3** at every even accumulator with
    `3 ∣ P + 1` — unconditional, no `ε` and no randomness. In particular the
    deterministic Euclid–Mullin walk (whose accumulators are all even, starting
    from `2`) captures `3` at its first `3`-opportunity. -/
theorem minFac_captures_three {P : ℕ} (hP : 1 ≤ P) (heven : Even P) (h3 : 3 ∣ P + 1) :
    mixedWalkFactor P minFacMixed 0 = 3 := by
  rw [mixedWalkFactor_none_eq_minFac P minFacMixed 0 rfl, mixedWalkProd_zero]
  exact minFac_succ_eq_three hP heven h3

/-- At an even accumulator with a `3`-opportunity, the `ε`-process selects `3`
    with probability at least `1 - ε`: the cost of TAKING an opportunity is
    independent of `ω`. -/
theorem epsStepWeight_three_ge {ε : ℝ} (hε0 : 0 ≤ ε) {P : ℕ} (hP : 1 ≤ P)
    (heven : Even P) (h3 : 3 ∣ P + 1) :
    1 - ε ≤ epsStepWeight ε P 3 := by
  have h := epsStepWeight_minFac_ge (ε := ε) hε0 hP
  rwa [minFac_succ_eq_three hP heven h3] at h

/-- `3` is an available choice at an accumulator with a `3`-opportunity. -/
theorem three_mem_primeFactors {P : ℕ} (hP : 1 ≤ P) (h3 : 3 ∣ P + 1) :
    3 ∈ (P + 1).primeFactors :=
  Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, by omega⟩

end Parity

/-! ## Part 4: The Anatomy Hypothesis

`OmegaBlockLB m v` says the deterministic sequence `v` is a lower bound for
`1/ω(P_{2j} + 1)` at every even step of every valid walk from `m`. It says
NOTHING about reachability — that side is closed unconditionally by
`exists_three_opportunity_step`. It is purely a statement about how many distinct
prime factors the Euclid numbers along a walk can have. -/

section OmegaHypothesis

/-- **Anatomy hypothesis**: `v j ≤ 1 / ω(P_{2j} + 1)` uniformly along all valid
    walks from `m`, at even steps (the block boundaries of Part 5).

    Heuristically `ω(P_k + 1) ≈ log log P_k ≈ k` along a walk, so `v j ≈ 1/(2j)`
    is admissible and `∑ v j` diverges. The trivial bound `ω(N) ≤ log₂ N` is NOT
    enough, since accumulators can grow doubly exponentially — this is a genuine
    hypothesis about the anatomy of Euclid numbers, not a theorem. -/
def OmegaBlockLB (m : ℕ) (v : ℕ → ℝ) : Prop :=
  (∀ j, 0 ≤ v j ∧ v j ≤ 1) ∧
  ∀ σ : MixedSelection, ValidMixedSelection m σ → ∀ j : ℕ,
    (∀ i, i < 2 * j → mixedWalkFactor m σ i ≠ 3) →
    v j * (((mixedWalkProd m σ (2 * j) + 1).primeFactors.card : ℝ)) ≤ 1

/-- Any admissible `v` is non-negative. -/
theorem omegaBlockLB_nonneg {m : ℕ} {v : ℕ → ℝ} (h : OmegaBlockLB m v) (j : ℕ) :
    0 ≤ v j := (h.1 j).1

/-- Any admissible `v` is bounded by `1` (as it must be: `ω ≥ 1`). -/
theorem omegaBlockLB_le_one {m : ℕ} {v : ℕ → ℝ} (h : OmegaBlockLB m v) (j : ℕ) :
    v j ≤ 1 := (h.1 j).2

/-- The value at the root: `v 0 ≤ 1 / ω(m + 1)`, in product form. The block
    condition at `j = 0` is unrestricted (there are no earlier steps to avoid
    `3` at), so any valid walk — e.g. the pure minFac walk — witnesses it. -/
theorem omegaBlockLB_root {m : ℕ} {v : ℕ → ℝ} (h : OmegaBlockLB m v) :
    v 0 * (((m + 1).primeFactors.card : ℝ)) ≤ 1 := by
  have := h.2 minFacMixed (minFacMixed_valid m) 0 (fun i hi => absurd hi (by omega))
  rwa [Nat.mul_zero, mixedWalkProd_zero] at this

/-- **Grandchild inheritance**: the hypothesis at `m` with `v` gives the
    hypothesis at a grandchild `m·p·p'` with `v` shifted by one block. Walks from
    the grandchild lift to walks from `m` by prepending the two choices. -/
theorem omegaBlockLB_shift {m : ℕ} {v : ℕ → ℝ} (h : OmegaBlockLB m v)
    {p p' : ℕ} (hp : p.Prime) (hpd : p ∣ m + 1) (hp3 : p ≠ 3)
    (hp' : p'.Prime) (hp'd : p' ∣ m * p + 1) (hp'3 : p' ≠ 3) :
    OmegaBlockLB (m * p * p') (fun j => v (j + 1)) := by
  refine ⟨fun j => h.1 (j + 1), fun τ hτ j havoid => ?_⟩
  set σ : MixedSelection := consSel p (consSel p' τ) with hσ
  have hvalid : ValidMixedSelection m σ :=
    consSel_valid hp hpd (consSel_valid hp' hp'd hτ)
  have hwalk : mixedWalkProd m σ (2 * (j + 1)) = mixedWalkProd (m * p * p') τ (2 * j) := by
    have h2 : 2 * (j + 1) = (2 * j + 1) + 1 := by ring
    rw [hσ, h2, consSel_walk_succ, consSel_walk_succ]
  -- The lifted walk avoids `3` below step `2(j+1)`: its first two factors are
  -- `p` and `p'`, and the rest are `τ`'s factors, which avoid `3` by assumption.
  have havoid' : ∀ i, i < 2 * (j + 1) → mixedWalkFactor m σ i ≠ 3 := by
    intro i hi
    match i with
    | 0 => rw [hσ, consSel_factor_zero]; exact hp3
    | 1 => rw [hσ, consSel_factor_succ, consSel_factor_zero]; exact hp'3
    | (k + 2) =>
      rw [hσ, show k + 2 = (k + 1) + 1 from rfl, consSel_factor_succ,
        consSel_factor_succ]
      exact havoid k (by omega)
  have := h.2 σ hvalid (j + 1) havoid'
  rwa [hwalk] at this

end OmegaHypothesis

/-! ## Part 5: The Two-Step Block Bound

The heart of the file. From any even accumulator `m ≥ 2` coprime to `3`, TWO
steps of the `ε`-process capture `3` with probability at least `(1-ε)·ε·v 0`:

* if `3 ∣ m + 1`, one step suffices and costs only `1 - ε` (Part 3);
* otherwise `exists_three_opportunity_step` gives a prime `f ∣ m+1`, `f ≠ 3`,
  with `3 ∣ m·f + 1`; selecting `f` costs `≥ ε/ω(m+1) ≥ ε·v 0`, and then the
  opportunity at the even accumulator `m·f` is taken at cost `≥ 1 - ε`.

Iterating over `K` blocks gives `failWeight ε 3 m (2K) ≤ ∏_{j<K} (1 - (1-ε)·ε·v j)`. -/

section BlockBound

variable {ε : ℝ}

/-- **Single block**: two steps of the `ε`-process from an even accumulator
    `m ≥ 2` coprime to `3` fail to select `3` with weight at most
    `1 - (1-ε)·ε·v 0`, where `v 0 ≤ 1/ω(m+1)`. -/
private theorem block_fail_bound (hε0 : 0 < ε) (hε1 : ε < 1) {m : ℕ} (hm : 2 ≤ m)
    (heven : Even m) (hcop : Nat.Coprime m 3) {v0 : ℝ} (_hv0 : 0 ≤ v0)
    (hv0ω : v0 * (((m + 1).primeFactors.card : ℝ)) ≤ 1) (hv0one : v0 ≤ 1) :
    ∑ p ∈ (m + 1).primeFactors.erase 3, epsStepWeight ε m p * stepFail ε 3 (m * p)
      ≤ 1 - (1 - ε) * ε * v0 := by
  have hε0' : (0 : ℝ) ≤ ε := le_of_lt hε0
  have hε1' : ε ≤ 1 := le_of_lt hε1
  have hm1 : 1 ≤ m := by omega
  by_cases h3 : 3 ∣ m + 1
  · -- Case A: the opportunity is already here; `minFac (m+1) = 3` takes it.
    have hbound : ∑ p ∈ (m + 1).primeFactors.erase 3,
        epsStepWeight ε m p * stepFail ε 3 (m * p) ≤ ε := by
      calc ∑ p ∈ (m + 1).primeFactors.erase 3,
              epsStepWeight ε m p * stepFail ε 3 (m * p)
          ≤ ∑ p ∈ (m + 1).primeFactors.erase 3, epsStepWeight ε m p := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            have hp2 : 2 ≤ p :=
              (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).two_le
            calc epsStepWeight ε m p * stepFail ε 3 (m * p)
                ≤ epsStepWeight ε m p * 1 :=
                  mul_le_mul_of_nonneg_left (stepFail_le_one hε0' hε1' (by nlinarith) 3)
                    (epsStepWeight_nonneg hε0' hε1')
              _ = epsStepWeight ε m p := mul_one _
        _ = 1 - epsStepWeight ε m 3 :=
            stepFail_eq_one_sub hm1 (three_mem_primeFactors hm1 h3) ▸ rfl
        _ ≤ ε := by linarith [epsStepWeight_three_ge (ε := ε) hε0' hm1 heven h3]
    -- `ε ≤ 1 - (1-ε)·ε·v0` because `(1-ε)² ≥ 0` and `v0 ≤ 1`.
    have hcnn : (0 : ℝ) ≤ (1 - ε) * ε := mul_nonneg (by linarith) hε0'
    have hshrink : (1 - ε) * ε * v0 ≤ (1 - ε) * ε * 1 :=
      mul_le_mul_of_nonneg_left hv0one hcnn
    nlinarith [sq_nonneg (1 - ε)]
  · -- Case B: escape to a child that has the opportunity, at cost `ε/ω(m+1)`.
    obtain ⟨f, hf, hfd, hf3, hfopp⟩ := exists_three_opportunity_step m hm hcop h3
    have hfmem : f ∈ (m + 1).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hf, hfd, by omega⟩
    have hfmem' : f ∈ (m + 1).primeFactors.erase 3 := Finset.mem_erase.mpr ⟨hf3, hfmem⟩
    have hmf1 : 1 ≤ m * f := by have := hf.two_le; nlinarith
    have hmfeven : Even (m * f) := heven.mul_right f
    -- The escape branch: after selecting `f`, the opportunity costs only `1 - ε`.
    have hchild : stepFail ε 3 (m * f) ≤ ε := by
      rw [stepFail_eq_one_sub hmf1 (three_mem_primeFactors hmf1 hfopp)]
      linarith [epsStepWeight_three_ge (ε := ε) hε0' hmf1 hmfeven hfopp]
    -- All other branches are bounded trivially.
    have hsplit := Finset.add_sum_erase _
      (fun p => epsStepWeight ε m p * stepFail ε 3 (m * p)) hfmem'
    have hrest : ∑ p ∈ ((m + 1).primeFactors.erase 3).erase f,
        epsStepWeight ε m p * stepFail ε 3 (m * p)
        ≤ ∑ p ∈ (m + 1).primeFactors.erase f, epsStepWeight ε m p := by
      calc ∑ p ∈ ((m + 1).primeFactors.erase 3).erase f,
              epsStepWeight ε m p * stepFail ε 3 (m * p)
          ≤ ∑ p ∈ ((m + 1).primeFactors.erase 3).erase f, epsStepWeight ε m p := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors
              (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp))).two_le
            calc epsStepWeight ε m p * stepFail ε 3 (m * p)
                ≤ epsStepWeight ε m p * 1 :=
                  mul_le_mul_of_nonneg_left (stepFail_le_one hε0' hε1' (by nlinarith) 3)
                    (epsStepWeight_nonneg hε0' hε1')
              _ = epsStepWeight ε m p := mul_one _
        _ ≤ ∑ p ∈ (m + 1).primeFactors.erase f, epsStepWeight ε m p := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_
              (fun _ _ _ => epsStepWeight_nonneg hε0' hε1')
            intro x hx
            exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hx,
              Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)⟩
    have hsum_erase_f : epsStepWeight ε m f
        + ∑ p ∈ (m + 1).primeFactors.erase f, epsStepWeight ε m p = 1 := by
      rw [Finset.add_sum_erase _ (epsStepWeight ε m) hfmem]
      exact epsStepWeight_sum_one hm1
    -- `epsStepWeight ε m f ≥ ε/ω(m+1) ≥ ε · v0`.
    have hωpos : (0 : ℝ) < ((m + 1).primeFactors.card : ℝ) := by
      have : (m + 1).primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
      exact_mod_cast this.card_pos
    have hfw : ε * v0 ≤ epsStepWeight ε m f := by
      refine le_trans ?_ (epsStepWeight_ge_eps_div_omega hε0' hε1' hfmem)
      rw [le_div_iff₀ hωpos]
      nlinarith
    have hfw_nonneg : 0 ≤ epsStepWeight ε m f := epsStepWeight_nonneg hε0' hε1'
    have hchild_nonneg : 0 ≤ stepFail ε 3 (m * f) := stepFail_nonneg hε0' hε1' 3 (m * f)
    calc ∑ p ∈ (m + 1).primeFactors.erase 3,
            epsStepWeight ε m p * stepFail ε 3 (m * p)
        = epsStepWeight ε m f * stepFail ε 3 (m * f)
          + ∑ p ∈ ((m + 1).primeFactors.erase 3).erase f,
              epsStepWeight ε m p * stepFail ε 3 (m * p) := hsplit.symm
      _ ≤ epsStepWeight ε m f * ε
          + ∑ p ∈ (m + 1).primeFactors.erase f, epsStepWeight ε m p := by
            exact add_le_add (mul_le_mul_of_nonneg_left hchild hfw_nonneg) hrest
      _ = 1 - epsStepWeight ε m f * (1 - ε) := by linarith
      _ ≤ 1 - (1 - ε) * ε * v0 := by nlinarith

/-- **Block product bound**: after `K` two-step blocks, the total weight of paths
    from `m` that never selected `3` is at most `∏_{j<K} (1 - (1-ε)·ε·v j)`. -/
theorem failWeight_le_block_prod (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ (K m : ℕ) (v : ℕ → ℝ), 2 ≤ m → Even m → Nat.Coprime m 3 → OmegaBlockLB m v →
      failWeight ε 3 m (2 * K) ≤ ∏ j ∈ Finset.range K, (1 - (1 - ε) * ε * v j) := by
  have hε0' : (0 : ℝ) ≤ ε := le_of_lt hε0
  have hε1' : ε ≤ 1 := le_of_lt hε1
  intro K
  induction K with
  | zero => intro m v _ _ _ _; simp
  | succ K ih =>
    intro m v hm heven hcop hv
    have hm1 : 1 ≤ m := by omega
    -- The common bound for all grandchildren, from the induction hypothesis.
    set C : ℝ := ∏ j ∈ Finset.range K, (1 - (1 - ε) * ε * v (j + 1)) with hC
    have hCnonneg : 0 ≤ C := by
      refine Finset.prod_nonneg (fun j _ => ?_)
      have h1 : v (j + 1) ≤ 1 := omegaBlockLB_le_one hv (j + 1)
      have h0 : 0 ≤ v (j + 1) := omegaBlockLB_nonneg hv (j + 1)
      have hcnn : (0 : ℝ) ≤ (1 - ε) * ε := mul_nonneg (by linarith) hε0'
      have hcle : (1 - ε) * ε ≤ 1 := by nlinarith [sq_nonneg (1 - ε)]
      have hshrink : (1 - ε) * ε * v (j + 1) ≤ (1 - ε) * ε * 1 :=
        mul_le_mul_of_nonneg_left h1 hcnn
      linarith
    -- Bound the inner (second) step of each block by `stepFail · C`.
    have hinner : ∀ p ∈ (m + 1).primeFactors.erase 3,
        failWeight ε 3 (m * p) (2 * K + 1) ≤ stepFail ε 3 (m * p) * C := by
      intro p hp
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
      have hp3 : p ≠ 3 := Finset.ne_of_mem_erase hp
      have hpd : p ∣ m + 1 := Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
      have hmp : 2 ≤ m * p := by have := hpprime.two_le; nlinarith
      rw [failWeight_succ, stepFail, Finset.sum_mul]
      refine Finset.sum_le_sum (fun p' hp' => ?_)
      have hp'prime : p'.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp')
      have hp'3 : p' ≠ 3 := Finset.ne_of_mem_erase hp'
      have hp'd : p' ∣ m * p + 1 := Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase hp')
      have hmpp : 2 ≤ m * p * p' := by have := hp'prime.two_le; nlinarith
      have hgc_even : Even (m * p * p') := (heven.mul_right p).mul_right p'
      have hgc_cop : Nat.Coprime (m * p * p') 3 := by
        have hpc : Nat.Coprime p 3 := (Nat.coprime_primes hpprime Nat.prime_three).mpr hp3
        have hp'c : Nat.Coprime p' 3 :=
          (Nat.coprime_primes hp'prime Nat.prime_three).mpr hp'3
        exact ((hcop.symm.mul_right hpc.symm).mul_right hp'c.symm).symm
      have hgc_omega : OmegaBlockLB (m * p * p') (fun j => v (j + 1)) :=
        omegaBlockLB_shift hv hpprime hpd hp3 hp'prime hp'd hp'3
      exact mul_le_mul_of_nonneg_left
        (ih (m * p * p') (fun j => v (j + 1)) hmpp hgc_even hgc_cop hgc_omega)
        (epsStepWeight_nonneg hε0' hε1')
    -- Assemble: outer step × (inner step × C) ≤ (block bound) × C.
    have hstep : 2 * (K + 1) = (2 * K + 1) + 1 := by ring
    rw [hstep, failWeight_succ]
    calc ∑ p ∈ (m + 1).primeFactors.erase 3,
            epsStepWeight ε m p * failWeight ε 3 (m * p) (2 * K + 1)
        ≤ ∑ p ∈ (m + 1).primeFactors.erase 3,
            epsStepWeight ε m p * (stepFail ε 3 (m * p) * C) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          exact mul_le_mul_of_nonneg_left (hinner p hp) (epsStepWeight_nonneg hε0' hε1')
      _ = (∑ p ∈ (m + 1).primeFactors.erase 3,
            epsStepWeight ε m p * stepFail ε 3 (m * p)) * C := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun p _ => by ring)
      _ ≤ (1 - (1 - ε) * ε * v 0) * C := by
          refine mul_le_mul_of_nonneg_right ?_ hCnonneg
          exact block_fail_bound hε0 hε1 hm heven hcop (omegaBlockLB_nonneg hv 0)
            (omegaBlockLB_root hv) (omegaBlockLB_le_one hv 0)
      _ = ∏ j ∈ Finset.range (K + 1), (1 - (1 - ε) * ε * v j) := by
          rw [Finset.prod_range_succ', hC]; ring

end BlockBound

/-! ## Part 6: Divergence Kills the Product

`∏_{k<K} (1 - x k) ≤ exp(-∑_{k<K} x k)`, so a divergent sum forces the product
to `0`. This is the strict generalization of `product_failure_tendsto_zero`
(`EM/Stochastic/GeometricCapture.lean`), which needs a UNIFORM `δ`; here the
per-block success probabilities are allowed to decay, as they must (they are
`≍ ε/ω(P_k+1)` and `ω` grows along the walk). -/

section DivergentProduct

/-- `∏_{k<K} (1 - x k) ≤ exp (-∑_{k<K} x k)` for `x k ∈ [0, 1]`. -/
theorem prod_one_sub_le_exp_neg_sum {x : ℕ → ℝ} (_hx0 : ∀ k, 0 ≤ x k) (hx1 : ∀ k, x k ≤ 1)
    (K : ℕ) :
    ∏ k ∈ Finset.range K, (1 - x k) ≤ Real.exp (-∑ k ∈ Finset.range K, x k) := by
  have hstep : ∀ k, (1 : ℝ) - x k ≤ Real.exp (-x k) := by
    intro k
    have := Real.add_one_le_exp (-x k)
    linarith
  calc ∏ k ∈ Finset.range K, (1 - x k)
      ≤ ∏ k ∈ Finset.range K, Real.exp (-x k) :=
        Finset.prod_le_prod (fun k _ => by linarith [hx1 k]) (fun k _ => hstep k)
    _ = Real.exp (∑ k ∈ Finset.range K, -x k) := (Real.exp_sum _ _).symm
    _ = Real.exp (-∑ k ∈ Finset.range K, x k) := by rw [Finset.sum_neg_distrib]

/-- **Divergence kills the product**: if `x k ∈ [0, 1]` and the partial sums of
    `x` diverge, then `∏_{k<K} (1 - x k) → 0`. -/
theorem prod_one_sub_tendsto_zero {x : ℕ → ℝ} (hx0 : ∀ k, 0 ≤ x k) (hx1 : ∀ k, x k ≤ 1)
    (hdiv : Filter.Tendsto (fun K => ∑ k ∈ Finset.range K, x k) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun K => ∏ k ∈ Finset.range K, (1 - x k)) Filter.atTop (nhds 0) := by
  apply squeeze_zero
  · intro K
    exact Finset.prod_nonneg (fun k _ => by linarith [hx1 k])
  · intro K; exact prod_one_sub_le_exp_neg_sum hx0 hx1 K
  · exact Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atBot_iff.mpr hdiv)

end DivergentProduct

/-! ## Part 7: Main Theorem -/

section Main

/-- **Almost-sure capture of 3, conditional only on anatomy.**

    Let `0 < ε < 1`, let `m ≥ 2` be EVEN and coprime to `3`, and suppose there is
    a sequence `v` satisfying the anatomy hypothesis `OmegaBlockLB m v`
    (`v j ≤ 1/ω(P_{2j}+1)` along every valid walk) with divergent partial sums.
    Then the failure weight tends to `0`: the `(1-ε)·minFac + ε·random` process
    captures `3` almost surely.

    Everything on the reachability side is unconditional — uniform block depth `1`
    (`exists_three_opportunity_step`) and the parity bonus (`minFac_succ_eq_three`,
    which makes taking an opportunity cost `1 - ε` rather than `ε/ω`). The only
    input is the divergence of `∑ 1/ω` along the walk. -/
theorem three_almost_sure_capture_of_omega_divergence
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {m : ℕ} (hm : 2 ≤ m) (heven : Even m)
    (hcop : Nat.Coprime m 3) {v : ℕ → ℝ} (hv : OmegaBlockLB m v)
    (hdiv : Filter.Tendsto (fun K => ∑ j ∈ Finset.range K, v j)
      Filter.atTop Filter.atTop) :
    Filter.Tendsto (failWeight ε 3 m) Filter.atTop (nhds 0) := by
  have hε0' : (0 : ℝ) ≤ ε := le_of_lt hε0
  have hε1' : ε ≤ 1 := le_of_lt hε1
  have hm1 : 1 ≤ m := by omega
  set c : ℝ := (1 - ε) * ε with hc
  have hcpos : 0 < c := by rw [hc]; nlinarith
  -- The block-success sequence `x j = c · v j` lies in `[0,1]` and has divergent sums.
  have hx0 : ∀ j, 0 ≤ c * v j := fun j => mul_nonneg hcpos.le (omegaBlockLB_nonneg hv j)
  have hx1 : ∀ j, c * v j ≤ 1 := by
    intro j
    have h1 : v j ≤ 1 := omegaBlockLB_le_one hv j
    have hc1 : c ≤ 1 := by rw [hc]; nlinarith
    nlinarith [omegaBlockLB_nonneg hv j]
  have hxdiv : Filter.Tendsto (fun K => ∑ j ∈ Finset.range K, c * v j)
      Filter.atTop Filter.atTop := by
    have := hdiv.const_mul_atTop hcpos
    simpa [Finset.mul_sum] using this
  have hprod := prod_one_sub_tendsto_zero hx0 hx1 hxdiv
  -- Along even horizons, the failure weight is dominated by the block product.
  have heven_bound : ∀ K, failWeight ε 3 m (2 * K)
      ≤ ∏ j ∈ Finset.range K, (1 - c * v j) := by
    intro K
    have := failWeight_le_block_prod hε0 hε1 K m v hm heven hcop hv
    simpa [hc, mul_assoc] using this
  have heven_tendsto : Filter.Tendsto (fun K => failWeight ε 3 m (2 * K))
      Filter.atTop (nhds 0) := by
    apply squeeze_zero
    · intro K; exact failWeight_nonneg hε0' hε1' 3 (2 * K) m hm1
    · exact heven_bound
    · exact hprod
  -- Antitonicity transfers the limit from the even subsequence to all horizons.
  have hhalf : Filter.Tendsto (fun n : ℕ => n / 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr (fun b => ⟨2 * b, fun a ha => by omega⟩)
  apply squeeze_zero (g := fun n : ℕ => failWeight ε 3 m (2 * (n / 2)))
  · intro n; exact failWeight_nonneg hε0' hε1' 3 n m hm1
  · intro n
    exact failWeight_antitone hε0' hε1' 3 hm1 (by omega : 2 * (n / 2) ≤ n)
  · exact heven_tendsto.comp hhalf

/-- The standard start: from `m = 2`, the accumulator is always even, so the
    parity bonus is free. Almost-sure capture of `3` by the `(1-ε)` process
    reduces to the anatomy hypothesis alone. -/
theorem three_almost_sure_capture_from_two
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {v : ℕ → ℝ} (hv : OmegaBlockLB 2 v)
    (hdiv : Filter.Tendsto (fun K => ∑ j ∈ Finset.range K, v j)
      Filter.atTop Filter.atTop) :
    Filter.Tendsto (failWeight ε 3 2) Filter.atTop (nhds 0) :=
  three_almost_sure_capture_of_omega_divergence hε0 hε1 (le_refl 2) (by decide)
    (by decide) hv hdiv

end Main

/-! ## Part 8: Landscape -/

section Landscape

/-- **Almost-sure capture of 3: the landscape.**

    1. The failure weight is a genuine probability: antitone in the horizon, so
       `→ 0` is exactly almost-sure capture.
    2. Unconditional: the pure minFac rule captures `3` at every even accumulator
       with a `3`-opportunity — taking an opportunity is `ω`-free.
    3. Unconditional: `3`-opportunities are at distance `≤ 1` from every
       accumulator (`exists_three_opportunity_step`).
    4. Conditional only on anatomy: `OmegaBlockLB` + divergence gives almost-sure
       capture of `3`. -/
theorem three_almost_sure_landscape {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    -- 1. The failure weight is antitone (so its limit is the a.s. criterion)
    (∀ m : ℕ, 1 ≤ m → Antitone (failWeight ε 3 m))
    ∧
    -- 2. Taking a 3-opportunity at an even accumulator is ω-free
    (∀ P : ℕ, 1 ≤ P → Even P → 3 ∣ P + 1 →
      mixedWalkFactor P minFacMixed 0 = 3 ∧ 1 - ε ≤ epsStepWeight ε P 3)
    ∧
    -- 3. 3-opportunities are at distance ≤ 1 from every accumulator
    (∀ P : ℕ, 2 ≤ P → Nat.Coprime P 3 →
      3 ∣ P + 1 ∨ ∃ f : ℕ, f.Prime ∧ f ∣ P + 1 ∧ f ≠ 3 ∧ 3 ∣ P * f + 1)
    ∧
    -- 4. Anatomy ⟹ almost-sure capture of 3
    (∀ (m : ℕ) (v : ℕ → ℝ), 2 ≤ m → Even m → Nat.Coprime m 3 → OmegaBlockLB m v →
      Filter.Tendsto (fun K => ∑ j ∈ Finset.range K, v j) Filter.atTop Filter.atTop →
      Filter.Tendsto (failWeight ε 3 m) Filter.atTop (nhds 0)) :=
  ⟨fun _ hm => failWeight_antitone (le_of_lt hε0) (le_of_lt hε1) 3 hm,
   fun _ hP heven h3 => ⟨minFac_captures_three hP heven h3,
     epsStepWeight_three_ge (le_of_lt hε0) hP heven h3⟩,
   fun P hP hcop => by
     by_cases h3 : 3 ∣ P + 1
     · exact Or.inl h3
     · exact Or.inr (exists_three_opportunity_step P hP hcop h3),
   fun m v hm heven hcop hv hdiv =>
     three_almost_sure_capture_of_omega_divergence hε0 hε1 hm heven hcop hv hdiv⟩

end Landscape
