import EM.Population.AutonomousBranch
import EM.Population.WeakMullin

/-!
# The Composite Floor Under Every Smallness Statement

`EM/Population/WeakMullin.lean` collects the natural weakenings of Mullin's conjecture
that speak about the *size* of the missing set:

* `MissingFinite` — only finitely many primes are missed;
* `WeakMullin` (WM) — `∑_{q missed} 1/q` converges;
* `ReciprocalDivergence` (RD) — `∑_k 1/seq k` diverges.

Together with `mc_implies_wm`, `missing_finite_implies_wm` and `wm_implies_rd` these
form a descending ladder `MC → MissingFinite? → WM → RD`, and every theorem in that
file is *downstream* of MC: nothing there is unconditional.

This file supplies the missing lower bound.  It shows that the **whole** ladder rests
on a single elementary statement about the anatomy of the Euclid numbers,

> **(C∞)** `prod n + 1` is composite for infinitely many `n`
> (`AutonomousBranch.InfinitelyManyComposite`),

which is open — and in fact on the strictly stronger *growth* statement (S) below.

## The mechanism

On the perpetual-primality branch (`AutonomousBranch.PerpetualPrimality N`) the least
factor of the Euclid candidate is the candidate itself, so `seq (n+1) = prod n + 1`.
The accumulator already grows geometrically for trivial reasons — every term is at
least `2`, so `2 ^ (n+1) ≤ prod n` — hence the selected primes are at least `2 ^ n`
from stage `N` on and `∑_k 1/seq k` **converges** by comparison with `∑ 2⁻ⁿ`.

That is `¬ RD`, and `wm_implies_rd` propagates it up the ladder: `¬ WM`,
`¬ MissingFinite`.  Contrapositively, each smallness statement forces (C∞).

Note how little is used.  The autonomous-map obstruction of
`EM/Population/AutonomousBranch.lean` derives `¬ MC` on this branch through Bertrand's
postulate (`eventually_prime_implies_not_mullin`), and the density-`1/2` failure through
`Φ₃` having no root mod `q ≡ 2 (mod 3)`.  Neither is needed here: geometric growth of
the accumulator alone kills the *reciprocal-sum* statements, which sit far below MC.
So `mullin_implies_infinitelyManyComposite` is recovered as a corollary of a strictly
weaker hypothesis, by a strictly more elementary route.

## The floor is really a growth statement

Perpetual primality is not what the convergence proof consumes.  It uses only that the
selected primes are eventually **large**, and "large" may be measured against any
benchmark whose reciprocals converge.  Hence

> **(S)** if `f n ≤ seq n` for all large `n` and `∑ 1/f n` converges, then
> `∑ 1/seq k` converges — so `RD`, `WM` and `MissingFinite` all fail
> (`summable_one_div_seq_of_lower_bound`).

Contrapositively (`exists_lt_of_reciprocalDivergence`), `RD` forces the selected primes
below *every* summable-reciprocal benchmark, infinitely often.  In arithmetic terms
(`exists_small_minFac_of_reciprocalDivergence`): for every fixed `c`,

    minFac (prod n + 1) < 2 ^ (n - c)   for infinitely many `n`.

This is strictly stronger than (C∞), which merely asks the least factor to be *proper*;
indeed (S) with `c = 0` gives (C∞) at once, since `2 ^ n < prod n + 1`
(`infinitelyManyComposite_of_reciprocalDivergence_via_growth`).  Perpetual primality is
recovered as the extreme case `f n = 2 ^ n`.

So what the smallness family needs is not that the Euclid numbers are sometimes
composite, but that they are sometimes **smooth relative to their own size**.

## Consequence for the programme

No statement in the family — convergence of `∑ 1/q` over the missing set, finiteness of
that set, its having relative density zero, or MC itself — can be proved without first
proving (C∞).  (C∞) is not a statement about the distribution of primes at all; it is a
statement about the anatomy of the numbers `prod n + 1`.  The family therefore does not
route around the anatomy axis identified in `EM/Meta/BagInformation.lean` — it lands on
it.

## Contents

* `two_pow_le_prod` — the unconditional geometric lower bound on the accumulator.
* `summable_one_div_seq_of_lower_bound`, `exists_lt_of_reciprocalDivergence`,
  `exists_small_minFac_of_reciprocalDivergence` — (S), the growth form of the floor.
* `summable_one_div_seq_of_perpetual` — perpetual primality makes `∑ 1/seq k` converge;
  now a corollary of (S).
* `infinitelyManyComposite_of_reciprocalDivergence` and its corollaries — the floor.
* `infinitelyManyComposite_of_small_minFac`,
  `infinitelyManyComposite_of_reciprocalDivergence_via_growth` — (S) ⟹ (C∞).
* `sum_inv_primes_below_le_tsum` — the reciprocal sum pays for every prime below the
  least missing prime; the one unconditional quantitative handle on that prime.
* `sq_lt_prod_succ_of_prime`, `two_pow_two_pow_primeEuclidCount_le_prod`,
  `primeEuclidCount_le_log_log` — primality squares the accumulator, hence is doubly
  logarithmically rare.
* `composite_floor_landscape`, `growth_floor_landscape`.
-/

noncomputable section

open Mullin Euclid MullinGroup AutonomousBranch

namespace CompositeFloor

/-! ## Part 1: the accumulator grows geometrically

This needs no hypothesis at all: each term of the sequence is prime, hence at least
`2`, and the accumulator is their product. -/

/-- **Geometric growth**: `2 ^ (n+1) ≤ prod n`, unconditionally. -/
theorem two_pow_le_prod (n : ℕ) : 2 ^ (n + 1) ≤ prod n := by
  induction n with
  | zero => rw [prod_zero]; norm_num
  | succ n ih =>
      have h2 : 2 ≤ seq (n + 1) := (seq_isPrime (n + 1)).1
      calc 2 ^ (n + 1 + 1) = 2 ^ (n + 1) * 2 := by ring
        _ ≤ prod n * seq (n + 1) := Nat.mul_le_mul ih h2
        _ = prod (n + 1) := (prod_succ n).symm

/-! ## Part 2: the reciprocal sum converges as soon as the selected primes are large

The convergence argument below is usually stated on the perpetual-primality branch, where
the selected prime *is* the Euclid candidate and therefore inherits the accumulator's
geometric growth.  But primality is not what the proof consumes.  All it uses is that
`seq n` is eventually **large**, and "large" may be read against any benchmark whose
reciprocals converge.

So the real floor under the smallness family is not (C∞) — the statement that the least
prime factor of `prod n + 1` is sometimes a *proper* factor — but the strictly stronger
growth statement (S): that the least prime factor is sometimes *small*.  Perpetual
primality is recovered as the extreme special case, where the benchmark is `2 ^ n`.

`exists_lt_of_reciprocalDivergence` is the contrapositive and the sharp form: divergence
of `∑ 1/seq k` forces the selected primes below **every** summable-reciprocal benchmark,
infinitely often. -/

/-- **Comparison.**  If the reciprocals of the selected primes are eventually dominated by
a summable benchmark, then `∑ 1/seq k` converges. -/
theorem summable_one_div_seq_of_le {g : ℕ → ℝ} (hg : Summable g) {N : ℕ}
    (hle : ∀ n, N ≤ n → (1 : ℝ) / seq n ≤ g n) :
    Summable (fun k : ℕ => (1 : ℝ) / seq k) := by
  rw [← summable_nat_add_iff N]
  exact Summable.of_nonneg_of_le
    (fun k => div_nonneg zero_le_one (Nat.cast_nonneg _))
    (fun k => hle _ (Nat.le_add_left N k))
    ((summable_nat_add_iff N).mpr hg)

/-- **(S), the growth form of the floor.**  If the selected primes eventually dominate a
benchmark `f` whose reciprocals are summable, then `∑ 1/seq k` converges — so
`ReciprocalDivergence`, `WeakMullin` and `MissingFinite` all fail. -/
theorem summable_one_div_seq_of_lower_bound {f : ℕ → ℝ} (hf0 : ∀ n, 0 < f n)
    (hf : Summable fun n => (1 : ℝ) / f n) {N : ℕ} (hgrow : ∀ n, N ≤ n → f n ≤ seq n) :
    Summable (fun k : ℕ => (1 : ℝ) / seq k) :=
  summable_one_div_seq_of_le hf (fun n hn => one_div_le_one_div_of_le (hf0 n) (hgrow n hn))

/-- **The floor, read as a growth statement.**  If `∑ 1/seq k` diverges then the selected
primes drop below *every* benchmark with summable reciprocals, infinitely often.

This is strictly stronger than (C∞): (C∞) only says the least prime factor of
`prod n + 1` is a proper factor infinitely often, whereas this says it is *small*
infinitely often, against an arbitrarily generous notion of small. -/
theorem exists_lt_of_reciprocalDivergence (h : ReciprocalDivergence) {f : ℕ → ℝ}
    (hf0 : ∀ n, 0 < f n) (hf : Summable fun n => (1 : ℝ) / f n) (N : ℕ) :
    ∃ n, N ≤ n ∧ (seq n : ℝ) < f n := by
  by_contra hcon
  push Not at hcon
  exact h (summable_one_div_seq_of_lower_bound hf0 hf hcon)

/-- The geometric instance of (S): factors of size `c * b ^ n` with `b > 1` already make
the reciprocal sum converge. -/
theorem summable_one_div_seq_of_geometric {c b : ℝ} (hc : 0 < c) (hb : 1 < b) {N : ℕ}
    (hgrow : ∀ n, N ≤ n → c * b ^ n ≤ seq n) :
    Summable (fun k : ℕ => (1 : ℝ) / seq k) := by
  have hb0 : (0 : ℝ) < b := lt_trans one_pos hb
  refine summable_one_div_seq_of_lower_bound (f := fun n => c * b ^ n)
    (fun n => by positivity) ?_ hgrow
  have : (fun n : ℕ => (1 : ℝ) / (c * b ^ n)) = fun n : ℕ => c⁻¹ * (b⁻¹) ^ n := by
    funext n; rw [one_div, mul_inv, inv_pow]
  rw [this]
  exact (summable_geometric_of_lt_one (by positivity)
    (by rw [inv_lt_one_iff₀]; exact Or.inr hb)).mul_left _

/-- **The geometric contrapositive.**  Divergence of `∑ 1/seq k` forces the selected
primes below any fixed geometric benchmark infinitely often. -/
theorem exists_lt_geometric_of_reciprocalDivergence (h : ReciprocalDivergence)
    {c b : ℝ} (hc : 0 < c) (hb : 1 < b) (N : ℕ) :
    ∃ n, N ≤ n ∧ (seq n : ℝ) < c * b ^ n := by
  by_contra hcon
  push Not at hcon
  exact h (summable_one_div_seq_of_geometric hc hb hcon)

/-- **(S) in the shape of the handoff.**  `RD` forces the least prime factor of the Euclid
number `prod n + 1` below `2 ^ (n - c)` infinitely often, for every fixed `c` — a purely
arithmetic statement about the anatomy of `prod n + 1`, with no primality in it. -/
theorem exists_small_minFac_of_reciprocalDivergence (h : ReciprocalDivergence) (c N : ℕ) :
    ∃ n, N ≤ n ∧ 2 ^ c * minFac (prod n + 1) < 2 ^ n := by
  obtain ⟨m, hm, hlt⟩ := exists_lt_geometric_of_reciprocalDivergence h
    (c := ((2 : ℝ) ^ (c + 1))⁻¹) (b := 2) (by positivity) one_lt_two (N + 1)
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine ⟨k, by omega, ?_⟩
  rw [seq_succ] at hlt
  have hid : (2 : ℝ) ^ c * (((2 : ℝ) ^ (c + 1))⁻¹ * 2 ^ (k + 1)) = 2 ^ k := by
    have h2c : (2 : ℝ) ^ c ≠ 0 := by positivity
    field_simp
    ring
  have hmul := mul_lt_mul_of_pos_left hlt (show (0 : ℝ) < 2 ^ c by positivity)
  rw [hid] at hmul
  exact_mod_cast hmul

/-- Under perpetual primality from `N`, the reciprocal sum of the sequence converges.  Now
a corollary of (S): the branch is just the case where the benchmark is `2 ^ n`. -/
theorem summable_one_div_seq_of_perpetual {N : ℕ} (hpp : PerpetualPrimality N) :
    Summable (fun k : ℕ => (1 : ℝ) / seq k) := by
  refine summable_one_div_seq_of_geometric (c := 1) (b := 2) one_pos one_lt_two
    (N := N + 1) (fun n hn => ?_)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : N ≤ m := by omega
  have hs : seq (m + 1) = prod m + 1 := perpetual_seq_succ hpp hm
  have hpow : (2 : ℕ) ^ (m + 1) ≤ prod m := two_pow_le_prod m
  have hpowR : (2 : ℝ) ^ (m + 1) ≤ ((prod m : ℕ) : ℝ) := by exact_mod_cast hpow
  rw [hs]; push_cast; linarith

/-! ## Part 3: the floor

Each smallness statement forces infinitely many composite Euclid candidates. -/

/-- **The floor.**  Divergence of `∑ 1/seq k` forces (C∞). -/
theorem infinitelyManyComposite_of_reciprocalDivergence (h : ReciprocalDivergence) :
    InfinitelyManyComposite :=
  infinitelyManyComposite_iff_no_perpetual_primality.mpr
    fun _ hpp => h (summable_one_div_seq_of_perpetual hpp)

/-- **Weak Mullin forces (C∞).** -/
theorem infinitelyManyComposite_of_weakMullin (h : WeakMullin) :
    InfinitelyManyComposite :=
  infinitelyManyComposite_of_reciprocalDivergence (wm_implies_rd h)

/-- **A finite missing set forces (C∞).** -/
theorem infinitelyManyComposite_of_missingFinite (h : MissingFinite) :
    InfinitelyManyComposite :=
  infinitelyManyComposite_of_weakMullin (missing_finite_implies_wm h)

/-- **Mullin's conjecture forces (C∞)** — re-proved through the reciprocal sum rather
than through Bertrand's postulate, and hence from a strictly weaker hypothesis.  Compare
`AutonomousBranch.mullin_implies_infinitelyManyComposite`. -/
theorem infinitelyManyComposite_of_mullin (hmc : MullinConjecture) :
    InfinitelyManyComposite :=
  infinitelyManyComposite_of_reciprocalDivergence (mc_implies_rd hmc)

/-! ### The floor, sharpened: (S) sits strictly below (C∞)

Each smallness statement forces not merely a *proper* factor infinitely often, but a
*small* one — below `2 ^ (n - c)` for every fixed `c`.  And (S) implies (C∞) for a
trivial reason: `prod n + 1 > 2 ^ n`, so a factor below `2 ^ n` cannot be the Euclid
number itself.  So the floor genuinely descends. -/

/-- **Weak Mullin forces a small factor.** -/
theorem exists_small_minFac_of_weakMullin (h : WeakMullin) (c N : ℕ) :
    ∃ n, N ≤ n ∧ 2 ^ c * minFac (prod n + 1) < 2 ^ n :=
  exists_small_minFac_of_reciprocalDivergence (wm_implies_rd h) c N

/-- **A finite missing set forces a small factor.** -/
theorem exists_small_minFac_of_missingFinite (h : MissingFinite) (c N : ℕ) :
    ∃ n, N ≤ n ∧ 2 ^ c * minFac (prod n + 1) < 2 ^ n :=
  exists_small_minFac_of_weakMullin (missing_finite_implies_wm h) c N

/-- **Mullin's conjecture forces a small factor.** -/
theorem exists_small_minFac_of_mullin (hmc : MullinConjecture) (c N : ℕ) :
    ∃ n, N ≤ n ∧ 2 ^ c * minFac (prod n + 1) < 2 ^ n :=
  exists_small_minFac_of_reciprocalDivergence (mc_implies_rd hmc) c N

/-- **(S) ⟹ (C∞).**  A factor strictly below the Euclid number is a proper factor, so the
candidate is composite. -/
theorem infinitelyManyComposite_of_small_minFac
    (h : ∀ N : ℕ, ∃ n, N ≤ n ∧ minFac (prod n + 1) < prod n + 1) :
    InfinitelyManyComposite := by
  intro N
  obtain ⟨n, hn, hlt⟩ := h N
  exact ⟨n, hn, fun hp => by
    rw [AutonomousBranch.euclid_minFac_self_of_prime hp] at hlt; omega⟩

/-- **The floor re-derived through (S)**, with no reference to the perpetual-primality
branch: `RD` forces a factor below `2 ^ n`, and `2 ^ n < prod n + 1`, so that factor is
proper.  Compare `infinitelyManyComposite_of_reciprocalDivergence`, which routes through
the branch instead. -/
theorem infinitelyManyComposite_of_reciprocalDivergence_via_growth
    (h : ReciprocalDivergence) : InfinitelyManyComposite := by
  refine infinitelyManyComposite_of_small_minFac (fun N => ?_)
  obtain ⟨n, hn, hsmall⟩ := exists_small_minFac_of_reciprocalDivergence h 0 N
  refine ⟨n, hn, ?_⟩
  have hpow : 2 ^ (n + 1) ≤ prod n := two_pow_le_prod n
  have : (2 : ℕ) ^ n ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [pow_zero, one_mul] at hsmall
  omega

/-! ### The branch, read forwards

On the perpetual-primality branch every smallness statement fails outright. -/

/-- Perpetual primality refutes `ReciprocalDivergence`. -/
theorem not_reciprocalDivergence_of_perpetual {N : ℕ} (hpp : PerpetualPrimality N) :
    ¬ ReciprocalDivergence :=
  fun h => h (summable_one_div_seq_of_perpetual hpp)

/-- Perpetual primality refutes `WeakMullin`: the missing set is then reciprocal-thick. -/
theorem not_weakMullin_of_perpetual {N : ℕ} (hpp : PerpetualPrimality N) :
    ¬ WeakMullin :=
  fun h => not_reciprocalDivergence_of_perpetual hpp (wm_implies_rd h)

/-- Perpetual primality refutes `MissingFinite`. -/
theorem not_missingFinite_of_perpetual {N : ℕ} (hpp : PerpetualPrimality N) :
    ¬ MissingFinite :=
  fun h => not_weakMullin_of_perpetual hpp (missing_finite_implies_wm h)

/-! ## Part 5: primality of a Euclid number is self-limiting

The reason `prod n + 1` is generally *not* prime is not that primes are scarce in general.
It is that this sequence penalises primality, and does so at a doubly exponential rate.

Compare the two branches of one step.  If `prod n + 1` is composite, its least factor is a
proper factor and the accumulator grows by that factor:
`prod (n+1) = prod n * minFac (prod n + 1)`.  If `prod n + 1` is *prime*, the least factor
is the whole Euclid number, so

    prod (n+1) = prod n * (prod n + 1) > (prod n) ^ 2 ,

and the accumulator **squares**.  Each prime Euclid number therefore doubles
`log (prod n)`, and the next candidate — whose primality has probability of order
`1 / log` — is twice as unlikely to be prime.  Primality is not merely rare here; it
consumes the resource that makes it possible.

This is enough for an unconditional bound.  If `m` of the first `N` Euclid numbers are
prime, the accumulator has been squared `m` times, so

    2 ^ 2 ^ m ≤ prod N ,        i.e.   m ≤ log₂ log₂ (prod N) .

Prime Euclid numbers are at most **doubly logarithmically** many in the size of the
accumulator.  Nothing is assumed: the composite steps only help, since they enlarge the
accumulator too. -/

/-- **A prime Euclid number squares the accumulator.**  The least factor is the whole
Euclid number, so the multiplier is `prod n + 1` rather than a proper factor. -/
theorem sq_lt_prod_succ_of_prime {n : ℕ} (h : Nat.Prime (prod n + 1)) :
    prod n * prod n < prod (n + 1) := by
  have hseq : seq (n + 1) = prod n + 1 := by
    rw [seq_succ]; exact AutonomousBranch.euclid_minFac_self_of_prime h
  have h2 := prod_ge_two n
  rw [prod_succ, hseq]
  nlinarith

/-- The accumulator never shrinks. -/
theorem prod_le_prod_succ (n : ℕ) : prod n ≤ prod (n + 1) := by
  have h2 : 2 ≤ seq (n + 1) := (seq_isPrime (n + 1)).1
  calc prod n = prod n * 1 := (Nat.mul_one _).symm
    _ ≤ prod n * seq (n + 1) := Nat.mul_le_mul_left _ (by omega)
    _ = prod (n + 1) := (prod_succ n).symm

/-- The number of prime Euclid numbers before stage `N`. -/
def primeEuclidCount (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => Nat.Prime (prod n + 1))).card

theorem primeEuclidCount_succ_of_prime {N : ℕ} (h : Nat.Prime (prod N + 1)) :
    primeEuclidCount (N + 1) = primeEuclidCount N + 1 := by
  classical
  unfold primeEuclidCount
  rw [Finset.range_add_one, Finset.filter_insert, if_pos h,
    Finset.card_insert_of_notMem (by simp)]

theorem primeEuclidCount_succ_of_not_prime {N : ℕ} (h : ¬ Nat.Prime (prod N + 1)) :
    primeEuclidCount (N + 1) = primeEuclidCount N := by
  classical
  unfold primeEuclidCount
  rw [Finset.range_add_one, Finset.filter_insert, if_neg h]

/-- **Primality is self-limiting.**  `m` prime Euclid numbers before stage `N` force the
accumulator past a tower `2 ^ 2 ^ m`.  Unconditional. -/
theorem two_pow_two_pow_primeEuclidCount_le_prod (N : ℕ) :
    2 ^ 2 ^ primeEuclidCount N ≤ prod N := by
  induction N with
  | zero => simp [primeEuclidCount, prod_zero]
  | succ N ih =>
      by_cases h : Nat.Prime (prod N + 1)
      · rw [primeEuclidCount_succ_of_prime h, pow_succ, pow_mul]
        have hsq : (2 ^ 2 ^ primeEuclidCount N) ^ 2 ≤ prod N * prod N := by
          rw [sq]; exact Nat.mul_le_mul ih ih
        exact le_of_lt (lt_of_le_of_lt hsq (sq_lt_prod_succ_of_prime h))
      · rw [primeEuclidCount_succ_of_not_prime h]
        exact ih.trans (prod_le_prod_succ N)

/-- **Prime Euclid numbers are doubly logarithmically rare.** -/
theorem primeEuclidCount_le_log_log (N : ℕ) :
    primeEuclidCount N ≤ Nat.log 2 (Nat.log 2 (prod N)) := by
  have hp : prod N ≠ 0 := by have := prod_ge_two N; omega
  have h1 : 2 ^ 2 ^ primeEuclidCount N ≤ prod N :=
    two_pow_two_pow_primeEuclidCount_le_prod N
  have h2 : 2 ^ primeEuclidCount N ≤ Nat.log 2 (prod N) :=
    (Nat.le_log_iff_pow_le (by norm_num) hp).mpr h1
  have hlog : Nat.log 2 (prod N) ≠ 0 := by
    have : 1 ≤ 2 ^ primeEuclidCount N := Nat.one_le_two_pow
    omega
  exact (Nat.le_log_iff_pow_le (by norm_num) hlog).mpr h2

/-! ### (C∞) is a growth statement about the accumulator

The self-limiting bound converts the primality question into a question about how fast
`prod` grows.  Splitting the first `N` stages into prime and composite ones,

    N = primeEuclidCount N + compositeEuclidCount N ≤ compositeEuclidCount N + log₂ log₂ (prod N),

so a composite Euclid number exists past any stage as soon as `N` outruns
`log₂ log₂ (prod N)`.  In other words **(C∞) follows from any bound saying the accumulator
grows strictly slower than the maximal tower rate.**

That reformulation is honest about its own difficulty.  The accumulator obeys the
unconditional ceiling `prod N + 1 ≤ 3 ^ 2 ^ N` (`prod_add_one_le_three_pow`), because the
selected factor never exceeds the Euclid number itself; so `log₂ log₂ (prod N) ≤ N + O(1)`
and the inequality above is vacuous *unless* one can beat the ceiling by an unbounded
margin.  Beating it is exactly what perpetual primality forbids.  The reformulation is
therefore equivalent in strength to (C∞) rather than weaker — but it locates the
difficulty in the *growth* of the accumulator rather than in the primality of any
individual term, which is a different kind of question to attack. -/

/-- The number of composite Euclid numbers before stage `N`. -/
def compositeEuclidCount (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => ¬ Nat.Prime (prod n + 1))).card

theorem primeEuclidCount_add_compositeEuclidCount (N : ℕ) :
    primeEuclidCount N + compositeEuclidCount N = N := by
  classical
  simpa [primeEuclidCount, compositeEuclidCount] using
    Finset.card_filter_add_card_filter_not (s := Finset.range N)
      (fun n => Nat.Prime (prod n + 1))

theorem compositeEuclidCount_succ_of_not_prime {N : ℕ} (h : ¬ Nat.Prime (prod N + 1)) :
    compositeEuclidCount (N + 1) = compositeEuclidCount N + 1 := by
  classical
  unfold compositeEuclidCount
  rw [Finset.range_add_one, Finset.filter_insert, if_pos h,
    Finset.card_insert_of_notMem (by simp)]

theorem compositeEuclidCount_succ_of_prime {N : ℕ} (h : Nat.Prime (prod N + 1)) :
    compositeEuclidCount (N + 1) = compositeEuclidCount N := by
  classical
  unfold compositeEuclidCount
  rw [Finset.range_add_one, Finset.filter_insert, if_neg (by simpa using h)]

theorem compositeEuclidCount_mono : Monotone compositeEuclidCount := by
  classical
  intro m n hmn
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hmn))

/-- **(C∞) makes the composite count unbounded.** -/
theorem exists_le_compositeEuclidCount (h : InfinitelyManyComposite) (M : ℕ) :
    ∃ N, M ≤ compositeEuclidCount N := by
  induction M with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ M ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨n, hn, hnp⟩ := h N
      refine ⟨n + 1, ?_⟩
      have h1 : compositeEuclidCount N ≤ compositeEuclidCount n := compositeEuclidCount_mono hn
      have h2 := compositeEuclidCount_succ_of_not_prime hnp
      omega

/-- **Composites are as plentiful as the accumulator's growth allows.** -/
theorem le_compositeEuclidCount_add_log_log (N : ℕ) :
    N ≤ compositeEuclidCount N + Nat.log 2 (Nat.log 2 (prod N)) := by
  have h := primeEuclidCount_add_compositeEuclidCount N
  have hp := primeEuclidCount_le_log_log N
  omega

/-- **The unconditional tower ceiling.**  The selected factor never exceeds the Euclid
number, so the accumulator can at most square at each step. -/
theorem prod_add_one_le_three_pow (N : ℕ) : prod N + 1 ≤ 3 ^ 2 ^ N := by
  induction N with
  | zero => simp [prod_zero]
  | succ N ih =>
      have hge : 2 ≤ prod N + 1 := by have := prod_ge_two N; omega
      have hseq : seq (N + 1) ≤ prod N + 1 := by
        rw [seq_succ]
        exact Nat.le_of_dvd (by omega) (minFac_dvd (prod N + 1) hge)
      have hstep : prod (N + 1) + 1 ≤ (prod N + 1) * (prod N + 1) := by
        rw [prod_succ]
        nlinarith [Nat.mul_le_mul_left (prod N) hseq, prod_ge_two N]
      calc prod (N + 1) + 1 ≤ (prod N + 1) * (prod N + 1) := hstep
        _ ≤ (3 ^ 2 ^ N) * (3 ^ 2 ^ N) := Nat.mul_le_mul ih ih
        _ = 3 ^ 2 ^ (N + 1) := by rw [← pow_add, ← two_mul, ← pow_succ']

/-- **A sub-tower growth bound gives (C∞).**  If `N` outruns `log₂ log₂ (prod N)` by an
arbitrarily large margin, then composite Euclid numbers occur past every stage. -/
theorem infinitelyManyComposite_of_subtower_growth
    (h : ∀ B : ℕ, ∃ N : ℕ, Nat.log 2 (Nat.log 2 (prod N)) + B ≤ N) :
    InfinitelyManyComposite := by
  classical
  intro M
  obtain ⟨N, hN⟩ := h (M + 1)
  have hcount : M + 1 ≤ compositeEuclidCount N := by
    have := le_compositeEuclidCount_add_log_log N
    omega
  -- more than `M` composite stages below `N`, so one of them is at least `M`
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.range N).filter (fun n => ¬ Nat.Prime (prod n + 1)) ⊆
      Finset.range M := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [Finset.mem_range]
    by_contra hge
    exact hn.2 (hcon n (by omega))
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  simp only [compositeEuclidCount] at hcount
  omega

/-! ## Part 4: the reciprocal sum pays for the prefix

Every prime below the least missing prime has been selected, so it contributes to
`∑ 1/seq k`.  This is the only unconditional quantitative link between the sequence's
reciprocal sum and the location of the first gap, and it runs opposite to
`wm_implies_rd`: there, thinness of the missing set forces the sum to diverge; here, a
*convergent* sum caps how far the first gap can be. -/

/-- If every prime below `q` has been selected and the reciprocal sum converges, then
that sum dominates `∑_{p < q} 1/p`. -/
theorem sum_inv_primes_below_le_tsum {q : ℕ}
    (hbelow : ∀ p, Nat.Prime p → p < q → p ∈ Set.range seq)
    (hsum : Summable (fun k : ℕ => (1 : ℝ) / seq k)) :
    ∑ p ∈ (Finset.range q).filter (fun p => Nat.Prime p), (1 : ℝ) / p
      ≤ ∑' k, (1 : ℝ) / seq k := by
  classical
  have hmem : ∀ p ∈ (Finset.range q).filter (fun p => Nat.Prime p), ∃ k, seq k = p := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    exact hbelow p hp.2 hp.1
  choose! idx hidx using hmem
  have hinj : ∀ a ∈ (Finset.range q).filter (fun p => Nat.Prime p),
      ∀ b ∈ (Finset.range q).filter (fun p => Nat.Prime p), idx a = idx b → a = b := by
    intro a ha b hb hab
    rw [← hidx a ha, ← hidx b hb, hab]
  have hsumeq :
      ∑ k ∈ ((Finset.range q).filter (fun p => Nat.Prime p)).image idx,
          (1 : ℝ) / seq k
        = ∑ p ∈ (Finset.range q).filter (fun p => Nat.Prime p), (1 : ℝ) / p := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun p hp => by rw [hidx p hp]
  rw [← hsumeq]
  exact hsum.sum_le_tsum _ (fun k _ => div_nonneg zero_le_one (Nat.cast_nonneg _))

/-- The same statement anchored at the least missing prime. -/
theorem sum_inv_primes_below_least_missing_le {q : ℕ} (hq : q ∈ MissingPrimes)
    (hmin : ∀ p ∈ MissingPrimes, q ≤ p)
    (hsum : Summable (fun k : ℕ => (1 : ℝ) / seq k)) :
    ∑ p ∈ (Finset.range q).filter (fun p => Nat.Prime p), (1 : ℝ) / p
      ≤ ∑' k, (1 : ℝ) / seq k :=
  sum_inv_primes_below_le_tsum (primes_below_smallest_missing_appeared hq hmin) hsum

/-! ## Landscape -/

/-- **The composite floor.**  Every smallness statement about the missing set implies
that infinitely many Euclid candidates are composite, and on the perpetual-primality
branch every one of them fails.  Since (C∞) is open, none of these weakenings of
Mullin's conjecture is accessible without first settling an anatomy question about the
numbers `prod n + 1`. -/
theorem composite_floor_landscape :
    (∀ N : ℕ, PerpetualPrimality N → Summable (fun k : ℕ => (1 : ℝ) / seq k)) ∧
    (ReciprocalDivergence → InfinitelyManyComposite) ∧
    (WeakMullin → InfinitelyManyComposite) ∧
    (MissingFinite → InfinitelyManyComposite) ∧
    (MullinConjecture → InfinitelyManyComposite) ∧
    (∀ N : ℕ, PerpetualPrimality N → ¬ ReciprocalDivergence ∧ ¬ WeakMullin ∧
      ¬ MissingFinite) ∧
    -- primality of a Euclid number squares the accumulator, so it is self-limiting
    (∀ N : ℕ, 2 ^ 2 ^ primeEuclidCount N ≤ prod N) ∧
    (∀ N : ℕ, primeEuclidCount N ≤ Nat.log 2 (Nat.log 2 (prod N))) :=
  ⟨fun _ hpp => summable_one_div_seq_of_perpetual hpp,
    infinitelyManyComposite_of_reciprocalDivergence,
    infinitelyManyComposite_of_weakMullin,
    infinitelyManyComposite_of_missingFinite,
    infinitelyManyComposite_of_mullin,
    fun _ hpp => ⟨not_reciprocalDivergence_of_perpetual hpp,
      not_weakMullin_of_perpetual hpp, not_missingFinite_of_perpetual hpp⟩,
    two_pow_two_pow_primeEuclidCount_le_prod,
    primeEuclidCount_le_log_log⟩

/-- **The growth floor (S).**  The floor under the smallness family is not (C∞) but a
statement about the *size* of the least prime factor of the Euclid numbers.  Every
smallness statement forces that factor below `2 ^ (n - c)` infinitely often, for every
fixed `c` — and below any benchmark at all whose reciprocals are summable.  (C∞) is the
weakest consequence of this, obtained by taking `c = 0` and noting that a factor below
`2 ^ n` cannot be the Euclid number itself.

Nothing in the proof is about primality; it is a comparison of series.  What the smallness
family actually needs is not that the Euclid numbers are sometimes composite, but that
they are sometimes *smooth relative to their own size*. -/
theorem growth_floor_landscape :
    -- (S): a large-factor branch kills the reciprocal-sum statements
    (∀ f : ℕ → ℝ, (∀ n, 0 < f n) → Summable (fun n => (1 : ℝ) / f n) →
        ∀ N : ℕ, (∀ n, N ≤ n → f n ≤ seq n) → ¬ ReciprocalDivergence) ∧
    -- the sharp contrapositive: RD undercuts every summable-reciprocal benchmark
    (ReciprocalDivergence → ∀ f : ℕ → ℝ, (∀ n, 0 < f n) →
        Summable (fun n => (1 : ℝ) / f n) → ∀ N : ℕ, ∃ n, N ≤ n ∧ (seq n : ℝ) < f n) ∧
    -- the arithmetic shape: the least prime factor of `prod n + 1` is small i.o.
    (ReciprocalDivergence → ∀ c N : ℕ, ∃ n, N ≤ n ∧ 2 ^ c * minFac (prod n + 1) < 2 ^ n) ∧
    (WeakMullin → ∀ c N : ℕ, ∃ n, N ≤ n ∧ 2 ^ c * minFac (prod n + 1) < 2 ^ n) ∧
    (MissingFinite → ∀ c N : ℕ, ∃ n, N ≤ n ∧ 2 ^ c * minFac (prod n + 1) < 2 ^ n) ∧
    (MullinConjecture → ∀ c N : ℕ, ∃ n, N ≤ n ∧ 2 ^ c * minFac (prod n + 1) < 2 ^ n) ∧
    -- and (S) ⟹ (C∞), so the old floor is a corollary of the new one
    ((∀ N : ℕ, ∃ n, N ≤ n ∧ minFac (prod n + 1) < prod n + 1) → InfinitelyManyComposite) ∧
    -- perpetual primality is the special case `f n = 2 ^ n`
    (∀ N : ℕ, PerpetualPrimality N → ∀ n, N + 1 ≤ n → (2 : ℝ) ^ n ≤ seq n) :=
  ⟨fun f hf0 hf N hgrow hrd => hrd (summable_one_div_seq_of_lower_bound hf0 hf hgrow),
    fun hrd f hf0 hf N => exists_lt_of_reciprocalDivergence hrd hf0 hf N,
    fun hrd c N => exists_small_minFac_of_reciprocalDivergence hrd c N,
    fun h c N => exists_small_minFac_of_weakMullin h c N,
    fun h c N => exists_small_minFac_of_missingFinite h c N,
    fun h c N => exists_small_minFac_of_mullin h c N,
    infinitelyManyComposite_of_small_minFac,
    fun N hpp n hn => by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hs : seq (m + 1) = prod m + 1 := perpetual_seq_succ hpp (by omega)
      have hpowR : (2 : ℝ) ^ (m + 1) ≤ ((prod m : ℕ) : ℝ) := by
        exact_mod_cast two_pow_le_prod m
      rw [hs]; push_cast; linarith⟩

end CompositeFloor

end
