import EM.Population.CompositeFloor

/-!
# The Defect Telescope: (C∞) as a Growth Statement

`EM/Population/CompositeFloor.lean` shows that the whole smallness family rests on
(C∞) — infinitely many composite Euclid candidates — and that the sharp floor is the
growth statement (S): the least prime factor of `prod n + 1` is *small* infinitely often.
Both are statements about the anatomy of individual integers, which is exactly the axis
on which the project has no leverage (`EM/Meta/BagInformation.lean`).

This file supplies the change of subject.  It replaces the anatomy question by a single
real number attached to the whole orbit, and shows that everything in sight is a
statement about that number.

## The telescope

Write `logProd n := log (prod n)`.  Since `prod (n+1) = prod n * seq (n+1)`,

    logProd (n+1) = logProd n + log (seq (n+1)) .

The *maximal* step is the perpetual-primality step `seq (n+1) = prod n + 1`, where the
second summand is essentially `logProd n` again and the accumulator doubles its
logarithm.  Measuring every step against that maximum defines the **defect**

    defect n := logProd n - log (seq (n+1)) ,

and the recursion becomes exactly

    logProd (n+1) = 2 * logProd n - defect n .

Dividing by `2 ^ (n+1)` telescopes it: with `normLog n := logProd n / 2 ^ n`,

    normLog N = logProd 0 - ∑_{n < N} defect n / 2 ^ (n+1) .

The defect is not quite nonnegative — a prime Euclid number overshoots by
`log (1 + 1/prod n)` — but the overshoot is at most `2 ^ -(n+1)`, so `normLog` is
antitone up to a summable correction and therefore **converges**.  Its limit

    growthConstant := lim_N  log (prod N) / 2 ^ N  ≥  0

is the one number this file is about.  Note the `2 ^ -n` weighting: a defect incurred at
stage `n` is discounted by `2 ^ -n`, so no finite computation can ever contribute to
`growthConstant`.  The question is entirely about the tail.

## What the constant decides

* **`growthConstant = 0` ⟺ the sub-tower growth criterion of `CompositeFloor` holds**
  (`subtower_growth_iff_growthConstant_eq_zero`).  So that criterion, which looked like a
  merely sufficient condition for (C∞), is in fact *exactly* the vanishing of the growth
  constant — and it is vacuous unless `growthConstant = 0`, because otherwise
  `log₂ log₂ (prod N) = N + log₂ growthConstant + o(1)`.

* **`growthConstant = 0` ⟺ (C∞)**
  (`infinitelyManyComposite_iff_growthConstant_eq_zero`), and dually
  **`0 < growthConstant` ⟺ perpetual primality from some stage**
  (`growthConstant_pos_iff_perpetualPrimality`).  The growth constant is a *complete
  invariant* for the dichotomy: there is no slack at all in the change of subject.

* **`ReciprocalDivergence ⟹ growthConstant = 0`**
  (`growthConstant_eq_zero_of_reciprocalDivergence`), and likewise for `WeakMullin`,
  `MissingFinite` and `MullinConjecture`.

* **`0 < growthConstant` ⟹ `log (seq (n+1)) / log (prod n) → 1`**
  (`tendsto_log_seq_div_logProd_of_pos`).

## A warning, and the fact that removes it

The last item invites a false reading: that the branch to be excluded is far wider than
perpetual primality, because the least prime factor need only be `(prod n) ^ (1 - o(1))`
rather than the Euclid number itself.  **It is not wider.**  Trial division says that a
number whose least prime factor exceeds its square root is prime
(`Euclid.minFac_sq_le`), so a ratio eventually above `1/2` *is* primality.  Quantitatively
(Part 5b): the defect is either non-positive (prime stage) or at least `(1/2) logProd n`
up to `2 ^ -(n+2)` (composite stage) — `defect_gap`.  Nothing lands in between.

Feeding the composite case back into the telescope gives the unconditional damping bound

    logProd N ≤ (log 2 + 1/3) · (3/4) ^ (#composite stages below N) · 2 ^ N

(`logProd_le_pow_mul`), a refinement of `CompositeFloor.prod_add_one_le_three_pow` in
which every composite stage costs a fixed geometric factor.  Infinitely many composite
stages therefore drive the constant to `0`, which is the converse implication above.

The upshot is the opposite of what the growth picture first suggests, and it is good news
for the programme rather than bad: the failure branch is *exactly* the autonomous branch,
so the obstruction machinery of `EM/Population/AutonomousBranch.lean` and
`EM/Population/SylvesterTower.lean` — which only ever applies where the recursion
degenerates to an autonomous map — bears on the whole of it, with nothing escaping.

## Contents

* `logProd`, `defect`, `normLog` — the telescope's three sequences.
* `logProd_succ_eq_two_mul_sub_defect` — the recursion.
* `normLog_eq_sub_sum` — the telescoped identity.
* `neg_two_pow_le_defect` — the defect is nonnegative up to `2 ^ -(n+1)`.
* `growthConstant`, `tendsto_normLog` — existence of the limit.
* `defect_gap`, `normLogCorr_succ_le_of_not_prime`, `logProd_le_pow_mul` — the
  trial-division gap and the damping bound.
* `infinitelyManyComposite_iff_growthConstant_eq_zero`,
  `growthConstant_pos_iff_perpetualPrimality` — the complete invariant.
* `subtower_growth_iff_growthConstant_eq_zero`, `defect_dichotomy`, `defect_landscape`.
-/

noncomputable section

open Mullin Euclid AutonomousBranch CompositeFloor Filter Topology

namespace DefectTelescope

/-! ## Part 1: the three sequences -/

/-- `logProd n = log (prod n)`, the logarithm of the accumulator. -/
def logProd (n : ℕ) : ℝ := Real.log (prod n)

/-- The **defect** at stage `n`: how far the selected prime falls short of the maximal
step `seq (n+1) = prod n + 1`, measured logarithmically. -/
def defect (n : ℕ) : ℝ := logProd n - Real.log (seq (n + 1))

/-- The accumulator's logarithm, normalised by the maximal growth rate. -/
def normLog (n : ℕ) : ℝ := logProd n / 2 ^ n

theorem prod_pos_real (n : ℕ) : (0 : ℝ) < (prod n : ℝ) := by
  have := prod_ge_two n
  exact_mod_cast lt_of_lt_of_le (by norm_num) this

theorem one_lt_prod_real (n : ℕ) : (1 : ℝ) < (prod n : ℝ) := by
  have := prod_ge_two n
  exact_mod_cast lt_of_lt_of_le (by norm_num) this

theorem logProd_pos (n : ℕ) : 0 < logProd n := Real.log_pos (one_lt_prod_real n)

theorem seq_pos_real (n : ℕ) : (0 : ℝ) < (seq n : ℝ) := by
  have := (seq_isPrime n).1
  exact_mod_cast lt_of_lt_of_le (by norm_num) this

/-- The step identity: the logarithm of the accumulator gains `log (seq (n+1))`. -/
theorem logProd_succ (n : ℕ) : logProd (n + 1) = logProd n + Real.log (seq (n + 1)) := by
  unfold logProd
  rw [prod_succ]
  push_cast
  exact Real.log_mul (ne_of_gt (prod_pos_real n)) (ne_of_gt (seq_pos_real (n + 1)))

/-- **The recursion.**  Every step is the maximal (doubling) step, less the defect. -/
theorem logProd_succ_eq_two_mul_sub_defect (n : ℕ) :
    logProd (n + 1) = 2 * logProd n - defect n := by
  rw [logProd_succ]; unfold defect; ring

/-! ## Part 2: the defect is nonnegative up to a summable error

`seq (n+1) ≤ prod n + 1`, so `log (seq (n+1)) ≤ logProd n + log (1 + 1/prod n)` and the
defect can only be negative by `log (1 + 1/prod n) ≤ 1/prod n ≤ 2 ^ -(n+1)`, using the
unconditional geometric bound `2 ^ (n+1) ≤ prod n`. -/

theorem seq_succ_le_prod_add_one (n : ℕ) : Mullin.seq (n + 1) ≤ prod n + 1 := by
  rw [seq_succ]
  have hge : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
  exact Nat.le_of_dvd (by omega) (minFac_dvd (prod n + 1) hge)

/-- **The defect is almost nonnegative.**  The only way to overshoot the maximal step is a
prime Euclid number, and it overshoots by at most `2 ^ -(n+1)`. -/
theorem neg_two_pow_le_defect (n : ℕ) : -((1 : ℝ) / 2) ^ (n + 1) ≤ defect n := by
  have hP0 : (0 : ℝ) < (prod n : ℝ) := prod_pos_real n
  have hPow : ((2 : ℝ)) ^ (n + 1) ≤ (prod n : ℝ) := by exact_mod_cast two_pow_le_prod n
  -- `log (seq (n+1)) ≤ log (prod n + 1)`
  have hle : Real.log (seq (n + 1)) ≤ Real.log ((prod n : ℝ) + 1) := by
    refine Real.log_le_log (seq_pos_real (n + 1)) ?_
    have := seq_succ_le_prod_add_one n
    exact_mod_cast this
  -- `log (prod n + 1) - log (prod n) ≤ 1 / prod n`
  have hgap : Real.log ((prod n : ℝ) + 1) - logProd n ≤ 1 / (prod n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos
      (x := ((prod n : ℝ) + 1) / (prod n : ℝ)) (by positivity)
    rw [Real.log_div (by positivity) (ne_of_gt hP0)] at h
    have hsimp : ((prod n : ℝ) + 1) / (prod n : ℝ) - 1 = 1 / (prod n : ℝ) := by
      field_simp
      ring
    rw [hsimp] at h
    exact h
  -- `1 / prod n ≤ (1/2) ^ (n+1)`
  have htail : 1 / (prod n : ℝ) ≤ ((1 : ℝ) / 2) ^ (n + 1) := by
    rw [div_pow, one_pow]
    exact one_div_le_one_div_of_le (by positivity) hPow
  unfold defect
  linarith

/-! ## Part 3: the telescope -/

/-- Dividing the recursion by `2 ^ (n+1)` turns it into a telescoping difference. -/
theorem normLog_succ (n : ℕ) : normLog (n + 1) = normLog n - defect n / 2 ^ (n + 1) := by
  unfold normLog
  rw [logProd_succ_eq_two_mul_sub_defect]
  have h2 : ((2 : ℝ)) ^ n ≠ 0 := by positivity
  field_simp
  ring

/-- **The telescoped identity.**  The normalised accumulator is its initial value minus a
`2 ^ -n`-weighted sum of the defects. -/
theorem normLog_eq_sub_sum (N : ℕ) :
    normLog N = logProd 0 - ∑ n ∈ Finset.range N, defect n / 2 ^ (n + 1) := by
  induction N with
  | zero => simp [normLog]
  | succ N ih => rw [normLog_succ, ih, Finset.sum_range_succ]; ring

theorem normLog_pos (n : ℕ) : 0 < normLog n := by
  unfold normLog
  exact div_pos (logProd_pos n) (by positivity)

/-- `normLog` is decreasing up to a summable error. -/
theorem normLog_succ_le (n : ℕ) : normLog (n + 1) ≤ normLog n + ((1 : ℝ) / 4) ^ (n + 1) := by
  have hd := neg_two_pow_le_defect n
  have h2 : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have hnum : -defect n ≤ ((1 : ℝ) / 2) ^ (n + 1) := by linarith
  have hdiv : (-defect n) / 2 ^ (n + 1) ≤ ((1 : ℝ) / 2) ^ (n + 1) / 2 ^ (n + 1) := by
    gcongr
  have hval : ((1 : ℝ) / 2) ^ (n + 1) / 2 ^ (n + 1) = ((1 : ℝ) / 4) ^ (n + 1) := by
    rw [div_pow, one_pow, div_pow, one_pow, div_div, ← mul_pow]
    norm_num
  rw [hval, neg_div] at hdiv
  rw [normLog_succ]
  linarith

/-! ## Part 4: the growth constant exists -/

/-- The correction that turns `normLog` into a genuinely antitone sequence:
`∑_{k ≥ n} (1/4) ^ (k+1) = (1/3) (1/4) ^ n`. -/
def normLogCorr (n : ℕ) : ℝ := normLog n + (1 / 3) * ((1 : ℝ) / 4) ^ n

theorem normLogCorr_pos (n : ℕ) : 0 < normLogCorr n := by
  have := normLog_pos n
  have : (0 : ℝ) < (1 / 3) * ((1 : ℝ) / 4) ^ n := by positivity
  unfold normLogCorr; linarith [normLog_pos n]

theorem normLogCorr_antitone : Antitone normLogCorr := by
  refine antitone_nat_of_succ_le (fun n => ?_)
  have h := normLog_succ_le n
  have hid : (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ (n + 1) + ((1 : ℝ) / 4) ^ (n + 1)
      = (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n := by
    rw [pow_succ]; ring
  unfold normLogCorr
  linarith

theorem normLogCorr_bddBelow : BddBelow (Set.range normLogCorr) := by
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  exact (normLogCorr_pos n).le

/-- **The growth constant** `C = lim_N log (prod N) / 2 ^ N`.

The `2 ^ -n` weighting in the telescope means no finite stage can move it: `C` is a pure
tail invariant of the orbit. -/
def growthConstant : ℝ := ⨅ n, normLogCorr n

theorem tendsto_normLogCorr :
    Tendsto normLogCorr atTop (𝓝 growthConstant) :=
  tendsto_atTop_ciInf normLogCorr_antitone normLogCorr_bddBelow

theorem tendsto_corr_zero :
    Tendsto (fun n : ℕ => (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ((1 : ℝ) / 4) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa using h.const_mul (1 / 3 : ℝ)

/-- **The limit exists.**  `log (prod N) / 2 ^ N → growthConstant`. -/
theorem tendsto_normLog : Tendsto normLog atTop (𝓝 growthConstant) := by
  have h := tendsto_normLogCorr.sub tendsto_corr_zero
  simp only [sub_zero] at h
  convert h using 1
  funext n
  unfold normLogCorr
  ring

theorem growthConstant_nonneg : 0 ≤ growthConstant :=
  ge_of_tendsto' tendsto_normLog (fun n => (normLog_pos n).le)

theorem growthConstant_le (n : ℕ) : growthConstant ≤ normLogCorr n :=
  ciInf_le normLogCorr_bddBelow n

/-! ## Part 5: `growthConstant = 0` is exactly the sub-tower growth criterion

`CompositeFloor.infinitelyManyComposite_of_subtower_growth` asks that `N` outrun
`log₂ log₂ (prod N)` by an unbounded margin.  That criterion is *equivalent* to the
vanishing of the growth constant — which makes precise the remark that it is vacuous
otherwise: if `C > 0` then `log₂ log₂ (prod N) = N + log₂ C + o(1)`. -/

/-- If `log (prod N) < 2 ^ K * log 2` then `prod N < 2 ^ 2 ^ K`. -/
theorem prod_lt_of_logProd_lt {N K : ℕ} (h : logProd N < 2 ^ K * Real.log 2) :
    prod N < 2 ^ 2 ^ K := by
  have hlog : Real.log ((2 : ℝ) ^ (2 ^ K : ℕ)) = (2 ^ K : ℕ) * Real.log 2 :=
    Real.log_pow 2 (2 ^ K)
  have hlt : Real.log ((prod N : ℝ)) < Real.log ((2 : ℝ) ^ (2 ^ K : ℕ)) := by
    rw [hlog]; push_cast; exact h
  have := (Real.log_lt_log_iff (prod_pos_real N) (by positivity)).mp hlt
  exact_mod_cast this

/-- **`growthConstant = 0` gives sub-tower growth.** -/
theorem subtower_growth_of_growthConstant_eq_zero (h : growthConstant = 0) (B : ℕ) :
    ∃ N : ℕ, Nat.log 2 (Nat.log 2 (prod N)) + B ≤ N := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hε : (0 : ℝ) < ((1 : ℝ) / 2) ^ B * Real.log 2 := by positivity
  have htend : Tendsto normLog atTop (𝓝 0) := h ▸ tendsto_normLog
  have hev : ∀ᶠ N in atTop, normLog N < ((1 : ℝ) / 2) ^ B * Real.log 2 := by
    have := htend.eventually (gt_mem_nhds hε)
    simpa using this
  obtain ⟨N, hN, hNB⟩ := ((hev.and (eventually_ge_atTop B)).exists)
  refine ⟨N, ?_⟩
  set K := N - B with hK
  have hNK : N = K + B := by omega
  -- `logProd N < 2 ^ K * log 2`
  have hbound : logProd N < 2 ^ K * Real.log 2 := by
    have h2N : (0 : ℝ) < 2 ^ N := by positivity
    have : logProd N < ((1 : ℝ) / 2) ^ B * Real.log 2 * 2 ^ N := by
      rw [normLog, div_lt_iff₀ h2N] at hN
      linarith
    have hid : ((1 : ℝ) / 2) ^ B * Real.log 2 * 2 ^ N = 2 ^ K * Real.log 2 := by
      rw [hNK, pow_add, div_pow, one_pow]
      field_simp
    linarith [hid ▸ this]
  have hlt : prod N < 2 ^ 2 ^ K := prod_lt_of_logProd_lt hbound
  have hprod0 : prod N ≠ 0 := by have := prod_ge_two N; omega
  have h1 : Nat.log 2 (prod N) < 2 ^ K := Nat.log_lt_of_lt_pow hprod0 hlt
  have hlog0 : Nat.log 2 (prod N) ≠ 0 := by
    have := Nat.log_pos (b := 2) (n := prod N) (by norm_num) (prod_ge_two N)
    omega
  have h2 : Nat.log 2 (Nat.log 2 (prod N)) < K := Nat.log_lt_of_lt_pow hlog0 h1
  omega

/-- **Sub-tower growth gives `growthConstant = 0`.** -/
theorem growthConstant_eq_zero_of_subtower_growth
    (h : ∀ B : ℕ, ∃ N : ℕ, Nat.log 2 (Nat.log 2 (prod N)) + B ≤ N) :
    growthConstant = 0 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- for each `B`, `growthConstant ≤ 2 * (1/2)^B * log 2 + (1/3) * (1/4)^B`
  have hkey : ∀ B : ℕ, growthConstant
      ≤ 2 * ((1 : ℝ) / 2) ^ B * Real.log 2 + (1 / 3) * ((1 : ℝ) / 4) ^ B := by
    intro B
    obtain ⟨N, hN⟩ := h B
    have hNB : B ≤ N := by omega
    set K := N - B with hK
    have hNK : N = K + B := by omega
    -- `prod N < 2 ^ 2 ^ (K + 1)`
    have hstep : Nat.log 2 (prod N) + 1 ≤ 2 ^ (K + 1) := by
      have h1 : Nat.log 2 (Nat.log 2 (prod N)) ≤ K := by omega
      have h2 : Nat.log 2 (prod N) < 2 ^ (Nat.log 2 (Nat.log 2 (prod N)) + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num) _
      have h3 : (2 : ℕ) ^ (Nat.log 2 (Nat.log 2 (prod N)) + 1) ≤ 2 ^ (K + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hprodlt : prod N < 2 ^ 2 ^ (K + 1) := by
      have h4 : prod N < 2 ^ (Nat.log 2 (prod N) + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num) _
      have h5 : (2 : ℕ) ^ (Nat.log 2 (prod N) + 1) ≤ 2 ^ 2 ^ (K + 1) :=
        Nat.pow_le_pow_right (by norm_num) hstep
      omega
    -- pass to logarithms
    have hlogle : logProd N ≤ 2 ^ (K + 1) * Real.log 2 := by
      have hR : ((prod N : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 ^ (K + 1) : ℕ) := by exact_mod_cast hprodlt.le
      have := Real.log_le_log (prod_pos_real N) hR
      rw [Real.log_pow] at this
      push_cast at this ⊢
      exact this
    have h2N : (0 : ℝ) < 2 ^ N := by positivity
    have hnorm : normLog N ≤ 2 * ((1 : ℝ) / 2) ^ B * Real.log 2 := by
      rw [normLog, div_le_iff₀ h2N]
      have hid : 2 * ((1 : ℝ) / 2) ^ B * Real.log 2 * 2 ^ N
          = 2 ^ (K + 1) * Real.log 2 := by
        rw [hNK, pow_add, div_pow, one_pow, pow_succ]
        field_simp
      linarith [hid]
    have hcorr : (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ N ≤ (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ B := by
      have : ((1 : ℝ) / 4) ^ N ≤ ((1 : ℝ) / 4) ^ B :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hNB
      linarith
    calc growthConstant ≤ normLogCorr N := growthConstant_le N
      _ = normLog N + (1 / 3) * ((1 : ℝ) / 4) ^ N := rfl
      _ ≤ 2 * ((1 : ℝ) / 2) ^ B * Real.log 2 + (1 / 3) * ((1 : ℝ) / 4) ^ B := by linarith
  have htend : Tendsto
      (fun B : ℕ => 2 * ((1 : ℝ) / 2) ^ B * Real.log 2 + (1 / 3) * ((1 : ℝ) / 4) ^ B)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun B : ℕ => ((1 : ℝ) / 2) ^ B) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h2 : Tendsto (fun B : ℕ => 2 * ((1 : ℝ) / 2) ^ B * Real.log 2) atTop (𝓝 0) := by
      simpa using (h1.const_mul (2 : ℝ)).mul_const (Real.log 2)
    simpa using h2.add tendsto_corr_zero
  have hle : growthConstant ≤ 0 := ge_of_tendsto' htend (fun B => hkey B)
  linarith [growthConstant_nonneg]

/-- **The criterion identified.**  The sub-tower growth hypothesis of `CompositeFloor` is
exactly `growthConstant = 0`. -/
theorem subtower_growth_iff_growthConstant_eq_zero :
    (∀ B : ℕ, ∃ N : ℕ, Nat.log 2 (Nat.log 2 (prod N)) + B ≤ N) ↔ growthConstant = 0 :=
  ⟨growthConstant_eq_zero_of_subtower_growth, subtower_growth_of_growthConstant_eq_zero⟩

/-- **(G) ⟹ (C∞).**  `log (prod N) = o(2 ^ N)` forces infinitely many composite Euclid
candidates. -/
theorem infinitelyManyComposite_of_growthConstant_eq_zero (h : growthConstant = 0) :
    InfinitelyManyComposite :=
  infinitelyManyComposite_of_subtower_growth
    (subtower_growth_of_growthConstant_eq_zero h)

/-! ## Part 5b: the defect is quantized, and a composite stage contracts the telescope

Everything above is soft: it never used that `seq (n+1)` is the *least* prime factor.
Using that, one elementary fact changes the shape of the whole problem — trial division.
If `X ≥ 2` is composite then `minFac X ^ 2 ≤ X` (`Nat.minFac_sq_le_self`), so at a
composite stage

    log (seq (n+1)) ≤ (1/2) log (prod n + 1) ≤ (1/2) (logProd n + 2 ^ -(n+1)) ,

that is `defect n ≥ (1/2) logProd n - (1/2) 2 ^ -(n+1)`.  At a prime stage
`seq (n+1) = prod n + 1 > prod n`, so `defect n ≤ 0`.  **The defect has a gap**: it is
either non-positive, or at least half of `logProd n`; nothing in between
(`defect_gap`).

Feeding the composite case into the telescope, one composite stage multiplies the
corrected sequence by `3/4` (`normLogCorr_succ_le_of_not_prime`), whence the
unconditional

    logProd N ≤ (log 2 + 1/3) * (3/4) ^ (compositeEuclidCount N) * 2 ^ N .

So composite stages *provably damp the tower*, at a fixed geometric rate.  Two
consequences, both sharp:

* (C∞) forces `growthConstant = 0` — the converse of Part 5, so
  **(C∞) ⟺ growthConstant = 0** (`infinitelyManyComposite_iff_growthConstant_eq_zero`);
* consequently `0 < growthConstant` ⟺ perpetual primality from some stage
  (`growthConstant_pos_iff_perpetualPrimality`).

The second corrects the natural reading of Part 6 below.  `log (seq (n+1)) / logProd n → 1`
looks like a branch far wider than perpetual primality — the least prime factor need only
be `(prod n) ^ (1 - o(1))`, not the whole number.  It is not wider: a ratio eventually
above `1/2` *is* primality, by trial division.  The failure branch is exactly the
autonomous branch, which is why every obstruction in the project is aimed at it. -/

/-- At a composite stage the least prime factor is at most the square root: trial
division.  This is the only place in the file where `seq (n+1)` being the *least* prime
factor is used, and it is what makes the growth reformulation sharp. -/
theorem minFac_sq_le_of_not_prime {n : ℕ} (h : ¬ Nat.Prime (prod n + 1)) :
    Mullin.seq (n + 1) * Mullin.seq (n + 1) ≤ prod n + 1 := by
  have hge : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
  have hle : minFac (prod n + 1) ≤ prod n + 1 :=
    Nat.le_of_dvd (by omega) (minFac_dvd (prod n + 1) hge)
  have hlt : minFac (prod n + 1) < prod n + 1 := by
    rcases lt_or_eq_of_le hle with h' | h'
    · exact h'
    · exact absurd ((MullinGroup.isPrime_iff_natPrime _).mp
        (h' ▸ minFac_isPrime (prod n + 1) hge)) h
  rw [seq_succ]
  exact minFac_sq_le (prod n + 1) hge hlt

theorem log_seq_le_half_of_not_prime {n : ℕ} (h : ¬ Nat.Prime (prod n + 1)) :
    Real.log (Mullin.seq (n + 1)) ≤ (1 / 2) * Real.log ((prod n : ℝ) + 1) := by
  have hsq := minFac_sq_le_of_not_prime h
  have hR : ((Mullin.seq (n + 1) : ℕ) : ℝ) ^ 2 ≤ ((prod n : ℕ) : ℝ) + 1 := by
    have : ((Mullin.seq (n + 1) * Mullin.seq (n + 1) : ℕ) : ℝ) ≤ ((prod n + 1 : ℕ) : ℝ) := by
      exact_mod_cast hsq
    push_cast at this
    nlinarith [this]
  have hpos : (0 : ℝ) < ((Mullin.seq (n + 1) : ℕ) : ℝ) := seq_pos_real (n + 1)
  have hlog := Real.log_le_log (by positivity) hR
  rw [Real.log_pow] at hlog
  push_cast at hlog
  linarith

/-- `log (prod n + 1)` exceeds `logProd n` by at most `2 ^ -(n+1)`. -/
theorem log_prod_add_one_le (n : ℕ) :
    Real.log ((prod n : ℝ) + 1) ≤ logProd n + ((1 : ℝ) / 2) ^ (n + 1) := by
  have hP0 : (0 : ℝ) < (prod n : ℝ) := prod_pos_real n
  have hPow : ((2 : ℝ)) ^ (n + 1) ≤ (prod n : ℝ) := by exact_mod_cast two_pow_le_prod n
  have h := Real.log_le_sub_one_of_pos
    (x := ((prod n : ℝ) + 1) / (prod n : ℝ)) (by positivity)
  rw [Real.log_div (by positivity) (ne_of_gt hP0)] at h
  have hsimp : ((prod n : ℝ) + 1) / (prod n : ℝ) - 1 = 1 / (prod n : ℝ) := by
    field_simp
    ring
  rw [hsimp] at h
  have htail : 1 / (prod n : ℝ) ≤ ((1 : ℝ) / 2) ^ (n + 1) := by
    rw [div_pow, one_pow]
    exact one_div_le_one_div_of_le (by positivity) hPow
  unfold logProd
  linarith

/-- **The composite half of the gap.**  A composite Euclid number costs half the
accumulator's logarithm. -/
theorem half_logProd_le_defect_of_not_prime {n : ℕ} (h : ¬ Nat.Prime (prod n + 1)) :
    (1 / 2) * logProd n - (1 / 2) * ((1 : ℝ) / 2) ^ (n + 1) ≤ defect n := by
  have h1 := log_seq_le_half_of_not_prime h
  have h2 := log_prod_add_one_le n
  unfold defect
  linarith

/-- **The prime half of the gap.**  A prime Euclid number overshoots the maximal step. -/
theorem defect_nonpos_of_prime {n : ℕ} (h : Nat.Prime (prod n + 1)) : defect n ≤ 0 := by
  have hseq : Mullin.seq (n + 1) = prod n + 1 := by
    rw [seq_succ]; exact AutonomousBranch.euclid_minFac_self_of_prime h
  have hlt : (prod n : ℝ) ≤ ((prod n : ℕ) : ℝ) + 1 := by linarith
  have := Real.log_le_log (prod_pos_real n) hlt
  unfold defect logProd
  rw [hseq]
  push_cast
  linarith

/-- **The defect gap.**  At every stage the defect is either non-positive (the Euclid
number is prime) or at least half of `logProd n` up to `2 ^ -(n+2)` (it is composite).
There is nothing in between: `log (seq (n+1)) / logProd n` never lies in `(1/2, 1)`. -/
theorem defect_gap (n : ℕ) :
    defect n ≤ 0 ∨ (1 / 2) * logProd n - (1 / 2) * ((1 : ℝ) / 2) ^ (n + 1) ≤ defect n := by
  by_cases h : Nat.Prime (prod n + 1)
  · exact Or.inl (defect_nonpos_of_prime h)
  · exact Or.inr (half_logProd_le_defect_of_not_prime h)

/-- **A composite stage contracts the telescope by `3/4`.** -/
theorem normLogCorr_succ_le_of_not_prime {n : ℕ} (h : ¬ Nat.Prime (prod n + 1)) :
    normLogCorr (n + 1) ≤ (3 / 4) * normLogCorr n := by
  have hd := half_logProd_le_defect_of_not_prime h
  have h2 : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  -- `defect n / 2 ^ (n+1) ≥ (1/4) * normLog n - (1/2) * (1/4) ^ (n+1)`
  have hq : ((1 : ℝ) / 4) ^ (n + 1) * 2 ^ (n + 1) = ((1 : ℝ) / 2) ^ (n + 1) := by
    rw [← mul_pow]; norm_num
  have hp : (logProd n / 2 ^ n) * 2 ^ (n + 1) = 2 * logProd n := by
    have hne : ((2 : ℝ)) ^ n ≠ 0 := by positivity
    rw [pow_succ]; field_simp
  have hdiv : (1 / 4) * normLog n - (1 / 2) * ((1 : ℝ) / 4) ^ (n + 1)
      ≤ defect n / 2 ^ (n + 1) := by
    rw [le_div_iff₀ h2, normLog]
    have hid : ((1 : ℝ) / 4 * (logProd n / 2 ^ n) - 1 / 2 * ((1 : ℝ) / 4) ^ (n + 1))
        * 2 ^ (n + 1)
        = (1 / 2) * logProd n - (1 / 2) * ((1 : ℝ) / 2) ^ (n + 1) := by
      rw [sub_mul, mul_assoc, hp, mul_assoc, hq]; ring
    rw [hid]
    exact hd
  have hcorr : ((1 : ℝ) / 4) ^ (n + 1) = (1 / 4) * ((1 : ℝ) / 4) ^ n := by
    rw [pow_succ]; ring
  rw [hcorr] at hdiv
  have ha : (0 : ℝ) ≤ ((1 : ℝ) / 4) ^ n := by positivity
  unfold normLogCorr
  rw [normLog_succ, hcorr]
  linarith

/-- **The damping bound.**  Each composite Euclid number costs the accumulator a factor
`3/4` in the normalised telescope.  Unconditional. -/
theorem normLogCorr_le_pow (N : ℕ) :
    normLogCorr N ≤ (3 / 4 : ℝ) ^ compositeEuclidCount N * normLogCorr 0 := by
  induction N with
  | zero => simp [compositeEuclidCount]
  | succ N ih =>
      by_cases h : Nat.Prime (prod N + 1)
      · rw [compositeEuclidCount_succ_of_prime h]
        exact le_trans (normLogCorr_antitone (Nat.le_succ N)) ih
      · rw [compositeEuclidCount_succ_of_not_prime h, pow_succ]
        have hpos : (0 : ℝ) ≤ (3 / 4 : ℝ) := by norm_num
        calc normLogCorr (N + 1) ≤ (3 / 4) * normLogCorr N :=
              normLogCorr_succ_le_of_not_prime h
          _ ≤ (3 / 4) * ((3 / 4 : ℝ) ^ compositeEuclidCount N * normLogCorr 0) := by
              exact mul_le_mul_of_nonneg_left ih hpos
          _ = (3 / 4 : ℝ) ^ compositeEuclidCount N * (3 / 4) * normLogCorr 0 := by ring

theorem normLogCorr_zero : normLogCorr 0 = Real.log 2 + 1 / 3 := by
  unfold normLogCorr normLog logProd
  rw [prod_zero]
  norm_num

/-- **The accumulator ceiling, refined by the composite count.**  Compare
`CompositeFloor.prod_add_one_le_three_pow`, which is the case `compositeEuclidCount N = 0`
up to constants: every composite stage improves it by a factor `3/4`. -/
theorem logProd_le_pow_mul (N : ℕ) :
    logProd N ≤ (Real.log 2 + 1 / 3) * (3 / 4 : ℝ) ^ compositeEuclidCount N * 2 ^ N := by
  have h := normLogCorr_le_pow N
  rw [normLogCorr_zero] at h
  have hle : normLog N ≤ normLogCorr N := by
    unfold normLogCorr
    have : (0 : ℝ) ≤ (1 / 3) * ((1 : ℝ) / 4) ^ N := by positivity
    linarith
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  rw [normLog, div_le_iff₀ h2N] at hle
  nlinarith [hle, h, h2N]

/-- **The growth constant is damped by every composite stage.** -/
theorem growthConstant_le_pow (N : ℕ) :
    growthConstant ≤ (3 / 4 : ℝ) ^ compositeEuclidCount N * (Real.log 2 + 1 / 3) := by
  have h := normLogCorr_le_pow N
  rw [normLogCorr_zero] at h
  exact le_trans (growthConstant_le N) h

/-- **(C∞) ⟹ `growthConstant = 0`.**  Infinitely many composite stages damp the
normalised accumulator geometrically. -/
theorem growthConstant_eq_zero_of_infinitelyManyComposite (h : InfinitelyManyComposite) :
    growthConstant = 0 := by
  have hlog2 : (0 : ℝ) < Real.log 2 + 1 / 3 := by
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); linarith
  refine le_antisymm ?_ growthConstant_nonneg
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  -- choose `M` with `(3/4) ^ M * (log 2 + 1/3) < ε`, then a stage with `M` composites
  have htend : Tendsto (fun M : ℕ => (3 / 4 : ℝ) ^ M * (Real.log 2 + 1 / 3))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun M : ℕ => (3 / 4 : ℝ) ^ M) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using h1.mul_const (Real.log 2 + 1 / 3)
  obtain ⟨M, hM⟩ := (htend.eventually (gt_mem_nhds (show (0 : ℝ) < ε by linarith))).exists
  obtain ⟨N, hN⟩ := CompositeFloor.exists_le_compositeEuclidCount h M
  have hmono : (3 / 4 : ℝ) ^ compositeEuclidCount N ≤ (3 / 4 : ℝ) ^ M :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hN
  have := growthConstant_le_pow N
  nlinarith [hM, hmono, this, hlog2]

/-- **(C∞) ⟺ `growthConstant = 0`.**  The growth constant is a complete invariant for the
composite/prime dichotomy.  In particular the growth reformulation of (C∞) is (C∞) again,
now provably so: there is no slack in the change of subject. -/
theorem infinitelyManyComposite_iff_growthConstant_eq_zero :
    InfinitelyManyComposite ↔ growthConstant = 0 :=
  ⟨growthConstant_eq_zero_of_infinitelyManyComposite,
    infinitelyManyComposite_of_growthConstant_eq_zero⟩

/-- **A positive growth constant is exactly perpetual primality.**  The failure branch is
not wider than the autonomous branch; it *is* the autonomous branch. -/
theorem growthConstant_pos_iff_perpetualPrimality :
    0 < growthConstant ↔ ∃ N : ℕ, PerpetualPrimality N := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    exact absurd (infinitelyManyComposite_iff_growthConstant_eq_zero.mp
      (no_perpetual_primality_implies_infinitelyManyComposite hcon)) (ne_of_gt h)
  · rintro ⟨N, hpp⟩
    rcases eq_or_lt_of_le growthConstant_nonneg with h | h
    · exact absurd (infinitelyManyComposite_iff_growthConstant_eq_zero.mpr h.symm)
        (fun hC => infinitelyManyComposite_implies_no_perpetual_primality hC N hpp)
    · exact h

/-! ## Part 6: the failure branch is `log (seq (n+1)) / log (prod n) → 1`

If `growthConstant > 0`, the telescoped identity forces the defects to be negligible
against `2 ^ n`, hence against `logProd n`.  By Part 5b this is *equivalent* to perpetual
primality — the ratio tending to `1` is not a weaker condition than the Euclid numbers
being eventually prime, it is the same condition, because a least prime factor above the
square root forces primality. -/

/-- The telescope's terms tend to `0`: an immediate consequence of convergence, since
`defect n / 2 ^ (n+1) = normLog n - normLog (n+1)`. -/
theorem tendsto_defect_div_two_pow :
    Tendsto (fun n : ℕ => defect n / 2 ^ (n + 1)) atTop (𝓝 0) := by
  have hshift : Tendsto (fun n : ℕ => normLog (n + 1)) atTop (𝓝 growthConstant) :=
    tendsto_normLog.comp (tendsto_add_atTop_nat 1)
  have h := tendsto_normLog.sub hshift
  simp only [sub_self] at h
  refine h.congr (fun n => ?_)
  rw [normLog_succ]; ring

theorem tendsto_defect_div_two_pow' :
    Tendsto (fun n : ℕ => defect n / 2 ^ n) atTop (𝓝 0) := by
  have h := tendsto_defect_div_two_pow.const_mul (2 : ℝ)
  simp only [mul_zero] at h
  refine h.congr (fun n => ?_)
  have h2 : ((2 : ℝ)) ^ n ≠ 0 := by positivity
  field_simp
  ring

theorem log_seq_div_logProd_eq (n : ℕ) :
    Real.log (seq (n + 1)) / logProd n = 1 - (defect n / 2 ^ n) / normLog n := by
  have h1 : logProd n ≠ 0 := ne_of_gt (logProd_pos n)
  have h2 : ((2 : ℝ)) ^ n ≠ 0 := by positivity
  have hd : Real.log (seq (n + 1)) = logProd n - defect n := by unfold defect; ring
  rw [hd, normLog]
  field_simp

/-- **The failure branch.**  If the growth constant is positive then the selected prime is
`(prod n) ^ (1 - o(1))` — the least prime factor of the Euclid number is essentially as
large as the Euclid number itself.  By `growthConstant_pos_iff_perpetualPrimality` this
hypothesis is *equivalent* to perpetual primality, so the conclusion describes the
autonomous branch rather than a larger set. -/
theorem tendsto_log_seq_div_logProd_of_pos (h : 0 < growthConstant) :
    Tendsto (fun n : ℕ => Real.log (seq (n + 1)) / logProd n) atTop (𝓝 1) := by
  have hquot : Tendsto (fun n : ℕ => (defect n / 2 ^ n) / normLog n) atTop (𝓝 0) := by
    -- state the shape explicitly: `Tendsto.div` returns the unapplied `f / g`
    have h0 : Tendsto (fun n : ℕ => (defect n / 2 ^ n) / normLog n) atTop
        (𝓝 (0 / growthConstant)) :=
      tendsto_defect_div_two_pow'.div tendsto_normLog (ne_of_gt h)
    simpa using h0
  have := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub hquot
  simp only [sub_zero] at this
  exact this.congr (fun n => (log_seq_div_logProd_eq n).symm)

/-! ## Part 7: the reciprocal sum forces the growth statement

If `growthConstant > 0`, the previous theorem makes the selected primes eventually exceed
`(√2) ^ n`, and `CompositeFloor.summable_one_div_seq_of_geometric` turns that into
convergence of `∑ 1/seq k`.  So `ReciprocalDivergence` — hence every smallness statement —
forces `growthConstant = 0`.

This route is independent of Part 5b (it never uses trial division), and is kept because
it is the one place where a *growth* hypothesis is converted back into an arithmetic one.
Given Part 5b it is also a corollary: `RD ⟹ (C∞) ⟹ growthConstant = 0`. -/

/-- `growthConstant > 0` makes the selected primes geometrically large, hence refutes
`ReciprocalDivergence`. -/
theorem not_reciprocalDivergence_of_growthConstant_pos (h : 0 < growthConstant) :
    ¬ ReciprocalDivergence := by
  set b : ℝ := Real.exp (Real.log 2 / 2) with hb
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hb1 : (1 : ℝ) < b := by rw [hb]; exact Real.one_lt_exp_iff.mpr (by positivity)
  have hlogb : Real.log b = Real.log 2 / 2 := by rw [hb, Real.log_exp]
  -- eventually `log (seq (n+1)) > (1/2) * logProd n`
  have hev : ∀ᶠ n in atTop, (1 : ℝ) / 2 < Real.log (seq (n + 1)) / logProd n := by
    have := (tendsto_log_seq_div_logProd_of_pos h).eventually
      (eventually_gt_nhds (show (1 : ℝ) / 2 < 1 by norm_num))
    simpa using this
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  intro hrd
  refine hrd (summable_one_div_seq_of_geometric (c := 1) (b := b) one_pos hb1
    (N := N₀ + 1) (fun n hn => ?_))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : N₀ ≤ m := by omega
  have hratio := hN₀ m hm
  have hlp : 0 < logProd m := logProd_pos m
  have h1 : (1 : ℝ) / 2 * logProd m < Real.log (seq (m + 1)) := by
    rw [lt_div_iff₀ hlp] at hratio; linarith
  -- `logProd m ≥ (m+1) * log 2`
  have h2 : ((m : ℝ) + 1) * Real.log 2 ≤ logProd m := by
    have hR : ((2 : ℝ)) ^ (m + 1) ≤ ((prod m : ℕ) : ℝ) := by exact_mod_cast two_pow_le_prod m
    have := Real.log_le_log (by positivity) hR
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  -- hence `log (b ^ (m+1)) < log (seq (m+1))`
  have h3 : Real.log (b ^ (m + 1)) < Real.log (seq (m + 1)) := by
    rw [Real.log_pow, hlogb]
    push_cast
    linarith
  have h4 : b ^ (m + 1) < (seq (m + 1) : ℝ) :=
    (Real.log_lt_log_iff (by positivity) (seq_pos_real (m + 1))).mp h3
  rw [one_mul]
  exact h4.le

/-- **The floor, final form.**  Divergence of `∑ 1/seq k` forces `log (prod N) = o(2 ^ N)`.
Every smallness statement of `EM/Population/WeakMullin.lean` therefore implies a pure
growth statement about the accumulator, with no primality in it. -/
theorem growthConstant_eq_zero_of_reciprocalDivergence (h : ReciprocalDivergence) :
    growthConstant = 0 := by
  by_contra hne
  exact not_reciprocalDivergence_of_growthConstant_pos
    (lt_of_le_of_ne growthConstant_nonneg (Ne.symm hne)) h

theorem growthConstant_eq_zero_of_weakMullin (h : WeakMullin) : growthConstant = 0 :=
  growthConstant_eq_zero_of_reciprocalDivergence (wm_implies_rd h)

theorem growthConstant_eq_zero_of_missingFinite (h : MissingFinite) : growthConstant = 0 :=
  growthConstant_eq_zero_of_weakMullin (missing_finite_implies_wm h)

theorem growthConstant_eq_zero_of_mullin (h : MullinConjecture) : growthConstant = 0 :=
  growthConstant_eq_zero_of_reciprocalDivergence (mc_implies_rd h)

/-! ## Part 8: the dichotomy, in its sharp form

Both alternatives below are *equivalences*, not merely sufficient conditions.  The second
alternative looks like a branch strictly wider than perpetual primality — the least prime
factor need only be `(prod n) ^ (1 - o(1))`, not the Euclid number itself.  It is not:
by trial division (Part 5b) a ratio eventually above `1/2` already forces primality.  The
failure branch *is* the autonomous branch, which is why the obstruction machinery of
`EM/Population/AutonomousBranch.lean` and `EM/Population/SylvesterTower.lean` bears on all
of it and not merely on an extreme point. -/

/-- **The dichotomy.**  Either infinitely many Euclid candidates are composite — and then
the growth constant vanishes — or the sequence is eventually on the perpetual-primality
branch, and then the least prime factor of `prod n + 1` is `(prod n) ^ (1 - o(1))` and the
growth constant is positive.  The two alternatives are mutually exclusive and exhaustive,
and each is *equivalent* to its growth-side description. -/
theorem defect_dichotomy :
    (InfinitelyManyComposite ∧ growthConstant = 0) ∨
      ((∃ N : ℕ, PerpetualPrimality N) ∧ 0 < growthConstant ∧
        Tendsto (fun n : ℕ => Real.log (Mullin.seq (n + 1)) / logProd n) atTop (𝓝 1)) := by
  rcases eq_or_lt_of_le growthConstant_nonneg with h | h
  · exact Or.inl ⟨infinitelyManyComposite_of_growthConstant_eq_zero h.symm, h.symm⟩
  · exact Or.inr ⟨growthConstant_pos_iff_perpetualPrimality.mp h, h,
      tendsto_log_seq_div_logProd_of_pos h⟩

/-- **Landscape.**  The growth constant organises the whole picture. -/
theorem defect_landscape :
    -- the telescope
    (∀ n : ℕ, logProd (n + 1) = 2 * logProd n - defect n) ∧
    (∀ N : ℕ, normLog N = logProd 0 - ∑ n ∈ Finset.range N, defect n / 2 ^ (n + 1)) ∧
    -- the limit exists and is nonnegative
    Tendsto normLog atTop (𝓝 growthConstant) ∧ 0 ≤ growthConstant ∧
    -- vanishing is exactly the sub-tower growth criterion, and gives (C∞)
    ((∀ B : ℕ, ∃ N : ℕ, Nat.log 2 (Nat.log 2 (prod N)) + B ≤ N) ↔ growthConstant = 0) ∧
    (growthConstant = 0 → InfinitelyManyComposite) ∧
    -- every smallness statement forces it to vanish
    (ReciprocalDivergence → growthConstant = 0) ∧
    (WeakMullin → growthConstant = 0) ∧
    (MissingFinite → growthConstant = 0) ∧
    (MullinConjecture → growthConstant = 0) ∧
    -- the defect gap, and the damping bound it produces
    (∀ n : ℕ, defect n ≤ 0 ∨
      (1 / 2) * logProd n - (1 / 2) * ((1 : ℝ) / 2) ^ (n + 1) ≤ defect n) ∧
    (∀ N : ℕ, logProd N ≤
      (Real.log 2 + 1 / 3) * (3 / 4 : ℝ) ^ CompositeFloor.compositeEuclidCount N * 2 ^ N) ∧
    -- (C∞) is *exactly* the vanishing of the growth constant
    (InfinitelyManyComposite ↔ growthConstant = 0) ∧
    (0 < growthConstant ↔ ∃ N : ℕ, PerpetualPrimality N) ∧
    -- and on the failure branch the least prime factor is `(prod n)^(1-o(1))`
    (0 < growthConstant →
      Tendsto (fun n : ℕ => Real.log (Mullin.seq (n + 1)) / logProd n) atTop (𝓝 1)) :=
  ⟨logProd_succ_eq_two_mul_sub_defect, normLog_eq_sub_sum, tendsto_normLog,
    growthConstant_nonneg, subtower_growth_iff_growthConstant_eq_zero,
    infinitelyManyComposite_of_growthConstant_eq_zero,
    growthConstant_eq_zero_of_reciprocalDivergence, growthConstant_eq_zero_of_weakMullin,
    growthConstant_eq_zero_of_missingFinite, growthConstant_eq_zero_of_mullin,
    defect_gap, logProd_le_pow_mul, infinitelyManyComposite_iff_growthConstant_eq_zero,
    growthConstant_pos_iff_perpetualPrimality, tendsto_log_seq_div_logProd_of_pos⟩

end DefectTelescope

end
