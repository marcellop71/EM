import EM.Stochastic.ThreeAlmostSure
import EM.Stochastic.RandomFactorMC

/-!
# The ε-Family and its Deterministic Limit: what "degenerating to minFac" can and cannot buy

## The programme this file makes precise

Euclid's argument does not specify which prime factor of `P + 1` to take. The
classical choices are extremal:

* **min** (`ε = 0`) — Mullin's first sequence. Whether every prime occurs is OPEN.
* **max** — Mullin's second sequence. It omits `5, 11, 13, 17, 19, 23, 29, 31,
  37, 41, 47` (Cox–van der Poorten 1968) and in fact infinitely many primes
  (Booker 2012).
* **uniformly random** (`ε = 1`) — the rule with no bias at all.

The strategic hope is: if the random rule captures every prime, and the family
`(1-ε)·minFac + ε·random` interpolates continuously from random (`ε = 1`) down
to minFac (`ε = 0`), then a statement proved for all `ε > 0` might survive the
limit and settle Mullin's conjecture.

This file shows that hope is **exactly right in form and exactly quantified in
strength**. Both endpoints really are endpoints of one object
(`epsStepWeight_zero_minFac`, `epsStepWeight_one_eq_uniform`), the limit
`ε → 0` really does transfer — but only from bounds that are **uniform on a
finite horizon**, and the usable window is `N · ε < c`. Asymptotic
(almost-sure) statements at each fixed `ε > 0`, which is what every current
technique produces, fall outside that window and carry **no** information about
`ε = 0`.

## Why the max rule fails and why that is evidence for min

Worth recording, because it is the structural content of "max is bad, so maybe
min is fine". The Cox–van der Poorten/Booker argument assumes every prime
`≤ X` outside a known omitted set occurs, takes the **last** such prime `p` to
occur, at step `n`, and concludes that the prime factors of
`1 + q₁⋯q_{n-1}` lie in the omitted set together with `p` — because under the
**max** rule `p` is the LARGEST prime factor, so no factor can exceed `X`. That
closes the factorization and lets a Jacobi-symbol computation contradict itself.

Under the **min** rule the selected prime is the SMALLEST factor, so the
cofactor is unconstrained and may be divisible by arbitrarily large primes: the
factorization never closes and the whole argument collapses at its first step.
The min rule resembles the random rule precisely in the feature that defeats
the known obstruction. That is the honest form of "max fails ⇒ min is
plausible": not an analogy, but the observation that the sole known mechanism
for omission is available only to the extremal rule that closes cofactors.

## Main results

* `epsStepWeight_zero_minFac` / `epsStepWeight_one_eq_uniform` — the family's
  two endpoints: `ε = 0` is the deterministic minFac rule, `ε = 1` is the
  uniform random rule. The SAME `failWeight ε q m N` describes both.
* `failWeight_ge_one_sub_pow` — if the minFac walk avoids `q` for `N` steps then
  `(1-ε)^N ≤ failWeight ε q m N`: the deterministic orbit is itself a failing
  path, of weight at least `(1-ε)^N`.
* **`mullin_capture_of_failWeight_bound`** — the transfer. If for a SINGLE
  `ε` with `N · ε < c` one has `failWeight ε q 2 N ≤ 1 - c`, then
  `∃ n, seq n = q`: Mullin's conjecture holds at `q`.
* `horizon_ge_of_minFacAvoids` — sharpness: the same inequality read backwards.
  If the minFac walk misses `q` on `[0, N)` then any bound `failWeight ≤ 1 - c`
  forces `c ≤ N · ε`, i.e. `N ≥ c/ε`. The transfer window is exactly
  `N < c/ε`.
* `failWeight_le_of_minFacCaptures` and
  **`mullin_iff_exists_failWeight_bound`** — the converse, hence an EQUIVALENCE:
  Mullin's conjecture at `q` holds iff such an `(ε, N, c)` exists.

## The consequence for the programme

The equivalence is the point. Mullin's conjecture at `q` is not merely implied
by an ε-uniform finite-horizon capture bound — it **is** one. So the noisy
family is a faithful reformulation, not a weakening: nothing is bought for
free. What the family does buy is a precise target, `capture probability ≥ c
within fewer than c/ε steps`, and a precise diagnosis of why the natural
results do not reach it:

`failWeight_ge_one_sub_pow` shows that if `q` never occurs in the minFac
sequence then `failWeight ε q 2 N ≥ (1-ε)^N` for EVERY `ε` and `N`. Since
`(1-ε)^N → 0` as `N → ∞`, this is entirely compatible with almost-sure capture
at every fixed `ε > 0`. **Almost-sure capture for all `ε > 0` does not imply
Mullin's conjecture**, and no argument that only produces a horizon `N(ε)` with
no control as `ε → 0` ever will: one needs `N(ε) < c/ε`, whereas the process
requires `≈ 1/ε` steps merely to take its first random step.

This is also why `EM/Stochastic/ThreeAlmostSure.lean` — which needs `ε < 1` and
produces an asymptotic statement in `N` — settles nothing about `ε = 0`, and why
its quantifiers (fixed `q = 3`, varying start) are orthogonal to Mullin's
(fixed start `2`, varying `q`).

## Contents

* Part 1: The two endpoints of the family
* Part 2: The deterministic orbit as a failing path — `failWeight_ge_one_sub_pow`
* Part 3: Bernoulli, and the `ε = 0` collapse
* Part 4: The transfer theorem
* Part 5: Sharpness — the `N < c/ε` window
* Part 6: The converse and the equivalence
* Part 7: Landscape
-/

noncomputable section

open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Part 1: The Two Endpoints of the Family

`epsStepWeight ε P ·` is a probability distribution on the prime factors of
`P + 1` for every `ε ∈ [0, 1]` (`epsStepWeight_sum_one`). At `ε = 0` it is the
point mass at `minFac (P+1)` — the deterministic Euclid–Mullin rule. At `ε = 1`
it is the uniform distribution — the pure random rule. -/

section Endpoints

/-- **The `ε = 0` endpoint is the min rule**: all the mass sits on `minFac`. -/
theorem epsStepWeight_zero_minFac {P : ℕ} (hP : 1 ≤ P) :
    epsStepWeight 0 P (P + 1).minFac = 1 := by
  have hmem : (P + 1).minFac ∈ (P + 1).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd _, by omega⟩
  simp [epsStepWeight, hmem]

/-- **The `ε = 0` endpoint is the min rule**: every other factor has weight `0`. -/
theorem epsStepWeight_zero_of_ne_minFac {P p : ℕ} (h : p ≠ (P + 1).minFac) :
    epsStepWeight 0 P p = 0 := by
  simp [epsStepWeight, h]

/-- **The `ε = 1` endpoint is the pure random rule**: the uniform distribution
    on the prime factors of `P + 1`. Note the minFac branch collapses too —
    `(1 - 1) + 1/ω = 1/ω` — so no factor is privileged. -/
theorem epsStepWeight_one_eq_uniform (P p : ℕ) :
    epsStepWeight 1 P p =
      if p ∈ (P + 1).primeFactors then ((P + 1).primeFactors.card : ℝ)⁻¹ else 0 := by
  unfold epsStepWeight
  split_ifs with hmem hmin <;> simp [one_div]

end Endpoints

/-! ## Part 2: The Deterministic Orbit is Itself a Failing Path

The whole file turns on one observation: the minFac walk is one of the paths
`failWeight` sums over, and under the `ε`-process it retains weight at least
`(1-ε)^N`. So the deterministic orbit is never negligible at finite horizon —
it is negligible only in the limit `N → ∞`, which is exactly where asymptotic
statements live and exactly why they say nothing about `ε = 0`. -/

section MinFacPath

/-- The minFac walk from `m` does not select `q` during its first `N` steps. -/
def MinFacAvoids (q m N : ℕ) : Prop :=
  ∀ k, k < N → mixedWalkFactor m minFacMixed k ≠ q

/-- One step of the minFac walk, as a restart from the child. -/
theorem minFacMixed_walk_succ (m k : ℕ) :
    mixedWalkProd m minFacMixed (k + 1) =
      mixedWalkProd (m * (m + 1).minFac) minFacMixed k := by
  have h1 : mixedWalkProd m minFacMixed 1 = m * (m + 1).minFac := by
    rw [mixedWalkProd_succ, mixedWalkProd_zero,
      mixedWalkFactor_none_eq_minFac m minFacMixed 0 rfl, mixedWalkProd_zero]
  have h := mixedWalkProd_tail_restart m minFacMixed 1 k
  rw [h1] at h
  rw [Nat.add_comm k 1]
  exact h

/-- The factors of the minFac walk, as a restart from the child. -/
theorem minFacMixed_factor_succ (m k : ℕ) :
    mixedWalkFactor m minFacMixed (k + 1) =
      mixedWalkFactor (m * (m + 1).minFac) minFacMixed k := by
  rw [mixedWalkFactor_none_eq_minFac m minFacMixed (k + 1) rfl,
    mixedWalkFactor_none_eq_minFac (m * (m + 1).minFac) minFacMixed k rfl,
    minFacMixed_walk_succ]

/-- `MinFacAvoids` passes to the child of the minFac walk. -/
theorem minFacAvoids_child {q m N : ℕ} (h : MinFacAvoids q m (N + 1)) :
    MinFacAvoids q (m * (m + 1).minFac) N := by
  intro k hk
  have := h (k + 1) (by omega)
  rwa [minFacMixed_factor_succ] at this

/-- The head of `MinFacAvoids`: the first minFac step is not `q`. -/
theorem minFacAvoids_head {q m N : ℕ} (h : MinFacAvoids q m (N + 1)) :
    (m + 1).minFac ≠ q := by
  have := h 0 (by omega)
  rwa [mixedWalkFactor_none_eq_minFac m minFacMixed 0 rfl, mixedWalkProd_zero] at this

/-- **The deterministic orbit is a failing path of weight `≥ (1-ε)^N`.**

    If the minFac walk from `m` avoids `q` for `N` steps, then the total weight
    of `q`-avoiding paths is at least the weight of that single path, and each
    of its steps costs at least `1 - ε` (`epsStepWeight_minFac_ge`). -/
theorem failWeight_ge_one_sub_pow {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (q : ℕ) :
    ∀ (N m : ℕ), 1 ≤ m → MinFacAvoids q m N → (1 - ε) ^ N ≤ failWeight ε q m N := by
  intro N
  induction N with
  | zero => intro m _ _; simp
  | succ N ih =>
    intro m hm havoid
    have hmf : (m + 1).minFac ≠ q := minFacAvoids_head havoid
    have hmem : (m + 1).minFac ∈ (m + 1).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd _, by omega⟩
    have hmem' : (m + 1).minFac ∈ (m + 1).primeFactors.erase q :=
      Finset.mem_erase.mpr ⟨hmf, hmem⟩
    have hmchild : 1 ≤ m * (m + 1).minFac := by
      have := (Nat.minFac_prime (show m + 1 ≠ 1 by omega)).two_le
      nlinarith
    have hchild := ih (m * (m + 1).minFac) hmchild (minFacAvoids_child havoid)
    rw [failWeight_succ]
    calc (1 - ε) ^ (N + 1)
        = (1 - ε) * (1 - ε) ^ N := by ring
      _ ≤ epsStepWeight ε m (m + 1).minFac * failWeight ε q (m * (m + 1).minFac) N := by
          apply mul_le_mul (epsStepWeight_minFac_ge hε0 hm) hchild
            (pow_nonneg (by linarith) N) (le_trans (by linarith) (epsStepWeight_minFac_ge hε0 hm))
      _ ≤ ∑ p ∈ (m + 1).primeFactors.erase q,
            epsStepWeight ε m p * failWeight ε q (m * p) N := by
          refine Finset.single_le_sum (f := fun p =>
            epsStepWeight ε m p * failWeight ε q (m * p) N) (fun p hp => ?_) hmem'
          have hp2 : 2 ≤ p :=
            (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).two_le
          exact mul_nonneg (epsStepWeight_nonneg hε0 hε1)
            (failWeight_nonneg hε0 hε1 q N (m * p) (by nlinarith))

end MinFacPath

/-! ## Part 3: Bernoulli, and the `ε = 0` Collapse -/

section Bernoulli

/-- Bernoulli's inequality in the form used below. -/
theorem one_sub_mul_le_one_sub_pow {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (N : ℕ) :
    1 - N * ε ≤ (1 - ε) ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hnn : (0 : ℝ) ≤ 1 - ε := by linarith
    have hstep : (1 - N * ε) * (1 - ε) ≤ (1 - ε) ^ N * (1 - ε) :=
      mul_le_mul_of_nonneg_right ih hnn
    have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [pow_succ, hcast]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (mul_nonneg hε0 hε0)]

/-- **At `ε = 0` the failure weight is the indicator of the minFac walk missing
    `q`** — the `= 1` half. Immediate from `failWeight_ge_one_sub_pow` at
    `ε = 0` together with `failWeight ≤ 1`. -/
theorem failWeight_zero_eq_one {q m N : ℕ} (hm : 1 ≤ m) (h : MinFacAvoids q m N) :
    failWeight 0 q m N = 1 :=
  le_antisymm (failWeight_le_one le_rfl zero_le_one q N m hm)
    (by simpa using failWeight_ge_one_sub_pow (le_refl (0 : ℝ)) zero_le_one q N m hm h)

/-- One step of the failure weight at `ε = 0`: all mass follows `minFac`. -/
theorem failWeight_zero_step (q m n : ℕ) (hm : 1 ≤ m) :
    failWeight 0 q m (n + 1) =
      if (m + 1).minFac = q then 0
      else failWeight 0 q (m * (m + 1).minFac) n := by
  have hmem : (m + 1).minFac ∈ (m + 1).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd _, by omega⟩
  rw [failWeight_succ]
  split_ifs with hq
  · -- `minFac` is erased: every remaining factor has weight `0`.
    refine Finset.sum_eq_zero (fun p hp => ?_)
    have hpq : p ≠ q := Finset.ne_of_mem_erase hp
    rw [epsStepWeight_zero_of_ne_minFac (by rw [hq]; exact hpq), zero_mul]
  · -- `minFac` survives and carries all the mass.
    have hmem' : (m + 1).minFac ∈ (m + 1).primeFactors.erase q :=
      Finset.mem_erase.mpr ⟨hq, hmem⟩
    rw [Finset.sum_eq_single_of_mem _ hmem']
    · rw [epsStepWeight_zero_minFac hm, one_mul]
    · intro p _ hne
      rw [epsStepWeight_zero_of_ne_minFac hne, zero_mul]

/-- **At `ε = 0` the failure weight is the indicator** — the `= 0` half: if the
    minFac walk does select `q` inside the horizon, the failure weight vanishes. -/
theorem failWeight_zero_eq_zero {q m N : ℕ} (hm : 1 ≤ m)
    (k : ℕ) (hk : k < N) (hcap : mixedWalkFactor m minFacMixed k = q) :
    failWeight 0 q m N = 0 := by
  induction k generalizing m N with
  | zero =>
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    rw [mixedWalkFactor_none_eq_minFac m minFacMixed 0 rfl, mixedWalkProd_zero] at hcap
    rw [failWeight_zero_step q m n hm, if_pos hcap]
  | succ k ih =>
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hmchild : 1 ≤ m * (m + 1).minFac := by
      have := (Nat.minFac_prime (show m + 1 ≠ 1 by omega)).two_le
      nlinarith
    rw [minFacMixed_factor_succ] at hcap
    rw [failWeight_zero_step q m n hm]
    split_ifs with hq
    · rfl
    · exact ih hmchild (by omega) hcap

end Bernoulli

/-! ## Part 4: The Transfer Theorem

A capture bound at a SINGLE `ε` small relative to the horizon forces the
deterministic walk to capture. No topology and no limit: the deterministic
orbit's own weight `(1-ε)^N ≥ 1 - N·ε` is what does the work. -/

section Transfer

/-- **Transfer, walk form.** If the `ε`-process captures `q` from `m` within `N`
    steps with probability at least `c`, and `ε` is small relative to the
    horizon (`N · ε < c`), then the DETERMINISTIC minFac walk from `m` captures
    `q` within `N` steps.

    The hypothesis `N · ε < c` is what makes this a statement about `ε = 0`:
    it says the noise had no room to matter over the horizon considered. -/
theorem minFac_captures_of_failWeight_bound {ε c : ℝ} {q m N : ℕ}
    (hm : 1 ≤ m) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hsmall : (N : ℝ) * ε < c)
    (hbound : failWeight ε q m N ≤ 1 - c) :
    ∃ k, k < N ∧ mixedWalkFactor m minFacMixed k = q := by
  by_contra hcon
  push Not at hcon
  have havoid : MinFacAvoids q m N := fun k hk => hcon k hk
  have hlow : (1 - ε) ^ N ≤ failWeight ε q m N :=
    failWeight_ge_one_sub_pow hε0 hε1 q N m hm havoid
  have hbern : 1 - (N : ℝ) * ε ≤ (1 - ε) ^ N := one_sub_mul_le_one_sub_pow hε0 hε1 N
  linarith

/-- **Transfer, Mullin form.** A capture bound for the `ε`-process from the
    standard start `2`, at a single `ε` with `N · ε < c`, proves Mullin's
    conjecture at `q`.

    This is the exact content of "let the noise degenerate to the min rule":
    it works, and it needs an `ε`-uniform bound on a horizon `N < c/ε`. -/
theorem mullin_capture_of_failWeight_bound {ε c : ℝ} {q N : ℕ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hsmall : (N : ℝ) * ε < c)
    (hbound : failWeight ε q 2 N ≤ 1 - c) :
    ∃ n, seq n = q := by
  obtain ⟨k, _, hk⟩ :=
    minFac_captures_of_failWeight_bound (by omega) hε0 hε1 hsmall hbound
  exact ⟨k + 1, by rwa [mixedWalkFactor_two_minFac_eq_seq] at hk⟩

end Transfer

/-! ## Part 5: Sharpness — the Transfer Window is `N < c/ε`

The same inequality read backwards. It shows the transfer cannot be improved,
and it quantifies exactly how far the asymptotic results sit from being usable. -/

section Sharpness

/-- **Sharpness.** If the minFac walk misses `q` over `[0, N)`, then ANY capture
    bound `failWeight ε q m N ≤ 1 - c` forces `c ≤ N · ε`, i.e. `N ≥ c/ε`.

    So the window in which `mullin_capture_of_failWeight_bound` applies —
    `N < c/ε` — is exactly the window in which such a bound is unavailable
    unless Mullin's conjecture already holds at `q`. The noisy family is a
    faithful reformulation of the problem, not a relaxation of it. -/
theorem horizon_ge_of_minFacAvoids {ε c : ℝ} {q m N : ℕ}
    (hm : 1 ≤ m) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (havoid : MinFacAvoids q m N)
    (hbound : failWeight ε q m N ≤ 1 - c) :
    c ≤ (N : ℝ) * ε := by
  have hlow : (1 - ε) ^ N ≤ failWeight ε q m N :=
    failWeight_ge_one_sub_pow hε0 hε1 q N m hm havoid
  have hbern : 1 - (N : ℝ) * ε ≤ (1 - ε) ^ N := one_sub_mul_le_one_sub_pow hε0 hε1 N
  linarith

/-- **Why almost-sure capture at every `ε > 0` decides nothing.** If `q` never
    occurs in the Euclid–Mullin sequence, then for EVERY `ε ∈ [0,1]` and every
    horizon `N` the failure weight from the standard start is at least
    `(1-ε)^N`.

    Since `(1-ε)^N → 0` as `N → ∞`, this is perfectly compatible with
    `failWeight ε q 2 N → 0` — i.e. with almost-sure capture of `q` for every
    `ε > 0`. An asymptotic statement in `N`, at each fixed `ε`, therefore
    carries no information about the deterministic rule. Only a bound in the
    window `N < c/ε` does. -/
theorem failWeight_ge_of_mullin_fails {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {q : ℕ} (hmiss : ∀ n, seq n ≠ q) (N : ℕ) :
    (1 - ε) ^ N ≤ failWeight ε q 2 N := by
  refine failWeight_ge_one_sub_pow hε0 hε1 q N 2 (by omega) (fun k _ hk => ?_)
  rw [mixedWalkFactor_two_minFac_eq_seq] at hk
  exact hmiss (k + 1) hk

end Sharpness

/-! ## Part 6: The Converse, and the Equivalence

Mullin's conjecture at `q` does not merely follow from a bound in the transfer
window — it produces one. So the two are equivalent, and the ε-family is a
faithful reformulation of the problem rather than a relaxation of it. -/

section Converse

variable {ε : ℝ}

/-- One step of the failure weight is bounded by the one-step avoid weight. -/
private theorem failWeight_succ_le_stepFail (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (q m n : ℕ) (hm : 1 ≤ m) : failWeight ε q m (n + 1) ≤ stepFail ε q m := by
  rw [failWeight_succ, stepFail]
  refine Finset.sum_le_sum (fun p hp => ?_)
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).two_le
  calc epsStepWeight ε m p * failWeight ε q (m * p) n
      ≤ epsStepWeight ε m p * 1 :=
        mul_le_mul_of_nonneg_left (failWeight_le_one hε0 hε1 q n (m * p) (by nlinarith))
          (epsStepWeight_nonneg hε0 hε1)
    _ = epsStepWeight ε m p := mul_one _

/-- If the deterministic rule selects `q` immediately, the `ε`-process fails to
    capture it with weight at most `ε`. -/
private theorem failWeight_le_eps_of_head (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {q m n : ℕ} (hm : 1 ≤ m) (hq : (m + 1).minFac = q) :
    failWeight ε q m (n + 1) ≤ ε := by
  have hmem : q ∈ (m + 1).primeFactors := by
    rw [← hq]
    exact Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd _, by omega⟩
  have hmf : 1 - ε ≤ epsStepWeight ε m q := by
    rw [← hq]; exact epsStepWeight_minFac_ge hε0 hm
  calc failWeight ε q m (n + 1)
      ≤ stepFail ε q m := failWeight_succ_le_stepFail hε0 hε1 q m n hm
    _ = 1 - epsStepWeight ε m q := stepFail_eq_one_sub hm hmem
    _ ≤ ε := by linarith

/-- **Converse to `failWeight_ge_one_sub_pow`.** If the minFac walk from `m`
    selects `q` at step `k < N`, the `ε`-process fails to capture `q` within `N`
    steps with weight at most `1 - (1-ε)^(k+1)`: the deterministic capturing
    path is excluded from `failWeight`, and it carries weight `≥ (1-ε)^(k+1)`. -/
theorem failWeight_le_of_minFacCaptures (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (q : ℕ) :
    ∀ (k N m : ℕ), 1 ≤ m → k < N → mixedWalkFactor m minFacMixed k = q →
      failWeight ε q m N ≤ 1 - (1 - ε) ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro N m hm hk hcap
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    rw [mixedWalkFactor_none_eq_minFac m minFacMixed 0 rfl, mixedWalkProd_zero] at hcap
    have := failWeight_le_eps_of_head hε0 hε1 (n := n) hm hcap
    simpa using by linarith
  | succ k ih =>
    intro N m hm hk hcap
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hmemMF : (m + 1).minFac ∈ (m + 1).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd _, by omega⟩
    have hmchild : 1 ≤ m * (m + 1).minFac := by
      have := (Nat.minFac_prime (show m + 1 ≠ 1 by omega)).two_le
      nlinarith
    have hpow_le : (1 - ε) ^ (k + 2) ≤ 1 - ε := by
      calc (1 - ε) ^ (k + 2) = (1 - ε) * (1 - ε) ^ (k + 1) := by ring
        _ ≤ (1 - ε) * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (by linarith) (by linarith)) (by linarith)
        _ = 1 - ε := mul_one _
    rw [minFacMixed_factor_succ] at hcap
    by_cases hq : (m + 1).minFac = q
    · -- The deterministic rule already selects `q` at step 0.
      have := failWeight_le_eps_of_head hε0 hε1 (n := n) hm hq
      linarith
    · -- Descend through the minFac child, keeping its weight `≥ 1 - ε`.
      have hmem' : (m + 1).minFac ∈ (m + 1).primeFactors.erase q :=
        Finset.mem_erase.mpr ⟨hq, hmemMF⟩
      have hchild := ih n (m * (m + 1).minFac) hmchild (by omega) hcap
      have hmfw : 1 - ε ≤ epsStepWeight ε m (m + 1).minFac :=
        epsStepWeight_minFac_ge hε0 hm
      have hmfw_nn : 0 ≤ epsStepWeight ε m (m + 1).minFac := epsStepWeight_nonneg hε0 hε1
      -- rest of the branches, bounded by their total weight
      have hrest : ∑ p ∈ ((m + 1).primeFactors.erase q).erase (m + 1).minFac,
          epsStepWeight ε m p * failWeight ε q (m * p) n
          ≤ ∑ p ∈ (m + 1).primeFactors.erase (m + 1).minFac, epsStepWeight ε m p := by
        calc ∑ p ∈ ((m + 1).primeFactors.erase q).erase (m + 1).minFac,
                epsStepWeight ε m p * failWeight ε q (m * p) n
            ≤ ∑ p ∈ ((m + 1).primeFactors.erase q).erase (m + 1).minFac,
                epsStepWeight ε m p := by
              refine Finset.sum_le_sum (fun p hp => ?_)
              have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors
                (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp))).two_le
              calc epsStepWeight ε m p * failWeight ε q (m * p) n
                  ≤ epsStepWeight ε m p * 1 :=
                    mul_le_mul_of_nonneg_left
                      (failWeight_le_one hε0 hε1 q n (m * p) (by nlinarith))
                      (epsStepWeight_nonneg hε0 hε1)
                _ = epsStepWeight ε m p := mul_one _
          _ ≤ ∑ p ∈ (m + 1).primeFactors.erase (m + 1).minFac, epsStepWeight ε m p := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_
                (fun _ _ _ => epsStepWeight_nonneg hε0 hε1)
              intro x hx
              exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hx,
                Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)⟩
      have htot : epsStepWeight ε m (m + 1).minFac
          + ∑ p ∈ (m + 1).primeFactors.erase (m + 1).minFac, epsStepWeight ε m p = 1 := by
        rw [Finset.add_sum_erase _ (epsStepWeight ε m) hmemMF]
        exact epsStepWeight_sum_one hm
      have hsplit := Finset.add_sum_erase _
        (fun p => epsStepWeight ε m p * failWeight ε q (m * p) n) hmem'
      rw [failWeight_succ, ← hsplit]
      have hmain : epsStepWeight ε m (m + 1).minFac
          * failWeight ε q (m * (m + 1).minFac) n
          ≤ epsStepWeight ε m (m + 1).minFac * (1 - (1 - ε) ^ (k + 1)) :=
        mul_le_mul_of_nonneg_left hchild hmfw_nn
      have hkey : epsStepWeight ε m (m + 1).minFac * (1 - ε) ^ (k + 1)
          ≥ (1 - ε) * (1 - ε) ^ (k + 1) :=
        mul_le_mul_of_nonneg_right hmfw (pow_nonneg (by linarith) _)
      have hpow_eq : (1 - ε) * (1 - ε) ^ (k + 1) = (1 - ε) ^ (k + 1 + 1) := by ring
      nlinarith

/-- **Mullin's conjecture at `q` IS an `ε`-uniform finite-horizon capture bound.**

    For `q ≠ 2`: `q` occurs in the Euclid–Mullin sequence if and only if there
    are a noise level `ε`, a horizon `N` and a confidence `c > 0` with
    `N · ε < c` such that the `(1-ε)·minFac + ε·random` process captures `q`
    from the standard start within `N` steps with probability at least `c`.

    Read left to right this is `failWeight_le_of_minFacCaptures`; read right to
    left it is `mullin_capture_of_failWeight_bound`. The equivalence is the
    honest verdict on the interpolation programme: the noisy family neither
    weakens nor strengthens the problem — it relocates it into the window
    `N < c/ε`, where by `horizon_ge_of_minFacAvoids` no bound is available
    unless the conjecture already holds. -/
theorem mullin_iff_exists_failWeight_bound {q : ℕ} (hq2 : q ≠ 2) :
    (∃ n, seq n = q) ↔
      ∃ (ε c : ℝ) (N : ℕ), 0 < ε ∧ ε ≤ 1 ∧ 0 < c ∧
        (N : ℝ) * ε < c ∧ failWeight ε q 2 N ≤ 1 - c := by
  constructor
  · rintro ⟨n, hn⟩
    -- `q ≠ 2 = seq 0`, so the hit is at a positive index, i.e. a walk factor.
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
      cases n with
      | zero => exact absurd (by rw [seq_zero] at hn; exact hn.symm) hq2
      | succ k => exact ⟨k, rfl⟩
    have hcap : mixedWalkFactor 2 minFacMixed k = q := by
      rw [mixedWalkFactor_two_minFac_eq_seq]; exact hn
    set N := k + 1 with hN
    set d : ℝ := 2 * (N : ℝ) + 2 with hd_def
    have hd : (0 : ℝ) < d := by rw [hd_def]; positivity
    refine ⟨1 / d, 1 / 2, N, by positivity, ?_, by norm_num, ?_, ?_⟩
    · rw [div_le_one hd, hd_def]
      have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    · -- `N · ε = N/d < 1/2` since `d = 2N + 2`
      rw [mul_one_div, div_lt_iff₀ hd, hd_def]
      linarith
    · -- `failWeight ≤ 1 - (1-ε)^N ≤ 1 - 1/2` by Bernoulli
      have hε0 : (0 : ℝ) ≤ 1 / d := by positivity
      have hε1 : (1 : ℝ) / d ≤ 1 := by
        rw [div_le_one hd, hd_def]
        have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith
      have hNe : (N : ℝ) * (1 / d) < 1 / 2 := by
        rw [mul_one_div, div_lt_iff₀ hd, hd_def]; linarith
      have hbern := one_sub_mul_le_one_sub_pow hε0 hε1 N
      have hle := failWeight_le_of_minFacCaptures hε0 hε1 q k N 2 (by omega)
        (by omega) hcap
      linarith
  · rintro ⟨ε, c, N, hε0, hε1, _, hsmall, hbound⟩
    exact mullin_capture_of_failWeight_bound (le_of_lt hε0) hε1 hsmall hbound

end Converse

/-! ## Part 7: Landscape -/

section Landscape

/-- **The ε-family landscape.**

    1. The family has the two classical rules as its endpoints: `ε = 0` is
       minFac (all mass on `minFac`), `ε = 1` is the uniform random rule.
    2. The deterministic orbit is a failing path of weight `≥ (1-ε)^N`, so it is
       never negligible at finite horizon.
    3. Transfer: a capture bound at any single `ε` with `N · ε < c` proves
       Mullin's conjecture at `q`.
    4. Sharpness: outside that window — `N ≥ c/ε` — no such bound exists unless
       the conjecture already holds at `q`.
    5. Equivalence: for `q ≠ 2`, Mullin's conjecture at `q` IS the existence of
       such a bound. -/
theorem epsilon_degeneration_landscape :
    -- 1. endpoints
    (∀ P : ℕ, 1 ≤ P → epsStepWeight 0 P (P + 1).minFac = 1) ∧
    (∀ P p : ℕ, epsStepWeight 1 P p =
      if p ∈ (P + 1).primeFactors then ((P + 1).primeFactors.card : ℝ)⁻¹ else 0) ∧
    -- 2. the deterministic orbit is a failing path
    (∀ (ε : ℝ), 0 ≤ ε → ε ≤ 1 → ∀ q N m : ℕ, 1 ≤ m → MinFacAvoids q m N →
      (1 - ε) ^ N ≤ failWeight ε q m N) ∧
    -- 3. transfer
    (∀ (ε c : ℝ) (q N : ℕ), 0 ≤ ε → ε ≤ 1 → (N : ℝ) * ε < c →
      failWeight ε q 2 N ≤ 1 - c → ∃ n, seq n = q) ∧
    -- 4. sharpness
    (∀ (ε c : ℝ) (q m N : ℕ), 1 ≤ m → 0 ≤ ε → ε ≤ 1 → MinFacAvoids q m N →
      failWeight ε q m N ≤ 1 - c → c ≤ (N : ℝ) * ε) ∧
    -- 5. equivalence
    (∀ q : ℕ, q ≠ 2 → ((∃ n, seq n = q) ↔
      ∃ (ε c : ℝ) (N : ℕ), 0 < ε ∧ ε ≤ 1 ∧ 0 < c ∧
        (N : ℝ) * ε < c ∧ failWeight ε q 2 N ≤ 1 - c)) :=
  ⟨fun _ hP => epsStepWeight_zero_minFac hP,
   epsStepWeight_one_eq_uniform,
   fun _ hε0 hε1 q N m hm h => failWeight_ge_one_sub_pow hε0 hε1 q N m hm h,
   fun _ _ _ _ hε0 hε1 hs hb => mullin_capture_of_failWeight_bound hε0 hε1 hs hb,
   fun _ _ _ _ _ hm hε0 hε1 ha hb => horizon_ge_of_minFacAvoids hm hε0 hε1 ha hb,
   fun _ hq => mullin_iff_exists_failWeight_bound hq⟩

end Landscape
