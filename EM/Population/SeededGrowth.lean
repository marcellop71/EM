import EM.Ensemble.Structure
import EM.Population.DefectTelescope
import EM.Stochastic.MixedWalk

/-!
# The growth constant of every seed: `C(T m) = 2 C(m)`, and `C(m) = 0 ⟺ (C∞)` for the seed `m`

`EM/Population/DefectTelescope.lean` proved, for the standard orbit `prod n = Tⁿ(2)` with
`T(n) = n · minFac (n+1)`, that `C = lim log (prod N) / 2^N` exists and is a *complete
invariant* for (C∞): `C = 0` iff infinitely many Euclid numbers are composite iff the orbit is
not eventually a tower of primes.  Nothing in that argument used the seed.  This file states
it for every seed `m ≥ 2` — `genProd m n = Tⁿ(m)` — and adds the two facts that only make
sense once the seed varies:

* **the semiconjugacy** `sgrowth (T m) = 2 · sgrowth m` (`sgrowth_T`), so `C : X → [0, ∞)` is
  a factor map from `(X, T)` onto doubling.  Doubling has no invariant probability measure
  except `δ₀`; hence `(X, T)` has none, and "a generic orbit" is meaningless.  This is the
  ergodic content of the four-way blocker as a theorem;
* **the universal statement**: the registered open point `MixedDiversity` — every seed
  `acc ≥ 2` has infinitely many composite Euclid numbers — is exactly
  `∀ m ≥ 2, sgrowth m = 0`, i.e. `{m : C(m) > 0} = ∅` (`mixedDiversity_iff_sgrowth_zero`).
  A seed with `C(m) > 0` would be an eventually-prime Sylvester-type tower — the shape of the
  Fermat question — and the set of such seeds is `T`-invariant.

`sgrowth 2 = DefectTelescope.growthConstant` (`sgrowth_two`), so nothing is duplicated.

The proofs are ports of `DefectTelescope` Parts 1–5b with `prod n ↦ genProd m n`,
`seq (n+1) ↦ genSeq m n`; the direction `C = 0 ⟹ (C∞)` is done directly (an eventually-prime
tail makes `snormLog` nondecreasing, so `C ≥ snormLog N₀ > 0`) rather than through the
sub-tower criterion.
-/

noncomputable section

open Filter Topology

namespace SeededGrowth

/-! ## Part 1: the three sequences, for a seed `m` -/

/-- `log (genProd m n)`. -/
def slogProd (m n : ℕ) : ℝ := Real.log (genProd m n)

/-- The defect at stage `n` of the orbit of `m`. -/
def sdefect (m n : ℕ) : ℝ := slogProd m n - Real.log (genSeq m n)

/-- The normalised logarithm. -/
def snormLog (m n : ℕ) : ℝ := slogProd m n / 2 ^ n

variable {m : ℕ}

theorem le_genProd (hm : 1 ≤ m) (n : ℕ) : m ≤ genProd m n := by
  have h := genProd_dvd_genProd m 0 n
  simp only [genProd, zero_add] at h
  exact Nat.le_of_dvd (genProd_pos hm n) h

theorem two_le_genProd (hm : 2 ≤ m) (n : ℕ) : 2 ≤ genProd m n :=
  le_trans hm (le_genProd (by omega) n)

theorem genProd_pos_real (hm : 2 ≤ m) (n : ℕ) : (0 : ℝ) < (genProd m n : ℝ) := by
  have := two_le_genProd hm n; exact_mod_cast lt_of_lt_of_le (by norm_num) this

theorem one_lt_genProd_real (hm : 2 ≤ m) (n : ℕ) : (1 : ℝ) < (genProd m n : ℝ) := by
  have := two_le_genProd hm n; exact_mod_cast lt_of_lt_of_le (by norm_num) this

theorem slogProd_pos (hm : 2 ≤ m) (n : ℕ) : 0 < slogProd m n :=
  Real.log_pos (one_lt_genProd_real hm n)

theorem genSeq_pos_real (hm : 2 ≤ m) (n : ℕ) : (0 : ℝ) < (genSeq m n : ℝ) := by
  have := (genSeq_prime (by omega : 1 ≤ m) n).two_le
  exact_mod_cast lt_of_lt_of_le (by norm_num) this

/-- The geometric floor `2 ^ (n+1) ≤ genProd m n`. -/
theorem two_pow_succ_le_genProd (hm : 2 ≤ m) (n : ℕ) : 2 ^ (n + 1) ≤ genProd m n := by
  have h := genProd_ge_mul_pow_two (by omega : 1 ≤ m) n
  calc 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    _ ≤ m * 2 ^ n := Nat.mul_le_mul_right _ hm
    _ ≤ genProd m n := h

theorem slogProd_succ (hm : 2 ≤ m) (n : ℕ) :
    slogProd m (n + 1) = slogProd m n + Real.log (genSeq m n) := by
  unfold slogProd
  rw [genProd_succ]
  push_cast
  exact Real.log_mul (ne_of_gt (genProd_pos_real hm n)) (ne_of_gt (genSeq_pos_real hm n))

theorem slogProd_succ_eq_two_mul_sub_sdefect (hm : 2 ≤ m) (n : ℕ) :
    slogProd m (n + 1) = 2 * slogProd m n - sdefect m n := by
  rw [slogProd_succ hm]; unfold sdefect; ring

/-! ## Part 2: the defect is nonnegative up to a summable error -/

theorem genSeq_le_genProd_add_one (m n : ℕ) : genSeq m n ≤ genProd m n + 1 :=
  Nat.le_of_dvd (by omega) (Nat.minFac_dvd _)

theorem neg_two_pow_le_sdefect (hm : 2 ≤ m) (n : ℕ) :
    -((1 : ℝ) / 2) ^ (n + 1) ≤ sdefect m n := by
  have hP0 : (0 : ℝ) < (genProd m n : ℝ) := genProd_pos_real hm n
  have hPow : ((2 : ℝ)) ^ (n + 1) ≤ (genProd m n : ℝ) := by
    exact_mod_cast two_pow_succ_le_genProd hm n
  have hle : Real.log (genSeq m n) ≤ Real.log ((genProd m n : ℝ) + 1) := by
    refine Real.log_le_log (genSeq_pos_real hm n) ?_
    exact_mod_cast genSeq_le_genProd_add_one m n
  have hgap : Real.log ((genProd m n : ℝ) + 1) - slogProd m n ≤ 1 / (genProd m n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos
      (x := ((genProd m n : ℝ) + 1) / (genProd m n : ℝ)) (by positivity)
    rw [Real.log_div (by positivity) (ne_of_gt hP0)] at h
    have hsimp : ((genProd m n : ℝ) + 1) / (genProd m n : ℝ) - 1 = 1 / (genProd m n : ℝ) := by
      field_simp; ring
    rw [hsimp] at h
    exact h
  have htail : 1 / (genProd m n : ℝ) ≤ ((1 : ℝ) / 2) ^ (n + 1) := by
    rw [div_pow, one_pow]
    exact one_div_le_one_div_of_le (by positivity) hPow
  unfold sdefect
  linarith

/-! ## Part 3: the telescope -/

theorem snormLog_succ (hm : 2 ≤ m) (n : ℕ) :
    snormLog m (n + 1) = snormLog m n - sdefect m n / 2 ^ (n + 1) := by
  unfold snormLog
  rw [slogProd_succ_eq_two_mul_sub_sdefect hm]
  have h2 : ((2 : ℝ)) ^ n ≠ 0 := by positivity
  field_simp
  ring

theorem snormLog_pos (hm : 2 ≤ m) (n : ℕ) : 0 < snormLog m n := by
  unfold snormLog
  exact div_pos (slogProd_pos hm n) (by positivity)

theorem snormLog_succ_le (hm : 2 ≤ m) (n : ℕ) :
    snormLog m (n + 1) ≤ snormLog m n + ((1 : ℝ) / 4) ^ (n + 1) := by
  have hd := neg_two_pow_le_sdefect hm n
  have h2 : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have hnum : -sdefect m n ≤ ((1 : ℝ) / 2) ^ (n + 1) := by linarith
  have hdiv : (-sdefect m n) / 2 ^ (n + 1) ≤ ((1 : ℝ) / 2) ^ (n + 1) / 2 ^ (n + 1) := by
    gcongr
  have hval : ((1 : ℝ) / 2) ^ (n + 1) / 2 ^ (n + 1) = ((1 : ℝ) / 4) ^ (n + 1) := by
    rw [div_pow, one_pow, div_pow, one_pow, div_div, ← mul_pow]
    norm_num
  rw [hval, neg_div] at hdiv
  rw [snormLog_succ hm]
  linarith

/-! ## Part 4: the growth constant of the seed -/

/-- The antitone correction. -/
def snormLogCorr (m n : ℕ) : ℝ := snormLog m n + (1 / 3) * ((1 : ℝ) / 4) ^ n

/-- **The growth constant of the seed `m`**: `C(m) = lim_N log (Tᴺ m) / 2^N`. -/
def sgrowth (m : ℕ) : ℝ := ⨅ n, snormLogCorr m n

theorem snormLogCorr_pos (hm : 2 ≤ m) (n : ℕ) : 0 < snormLogCorr m n := by
  have : (0 : ℝ) < (1 / 3) * ((1 : ℝ) / 4) ^ n := by positivity
  unfold snormLogCorr; linarith [snormLog_pos hm n]

theorem snormLogCorr_antitone (hm : 2 ≤ m) : Antitone (snormLogCorr m) := by
  refine antitone_nat_of_succ_le (fun n => ?_)
  have h := snormLog_succ_le hm n
  have hid : (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ (n + 1) + ((1 : ℝ) / 4) ^ (n + 1)
      = (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n := by
    rw [pow_succ]; ring
  unfold snormLogCorr
  linarith

theorem snormLogCorr_bddBelow (hm : 2 ≤ m) : BddBelow (Set.range (snormLogCorr m)) := by
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  exact (snormLogCorr_pos hm n).le

theorem tendsto_snormLogCorr (hm : 2 ≤ m) :
    Tendsto (snormLogCorr m) atTop (𝓝 (sgrowth m)) :=
  tendsto_atTop_ciInf (snormLogCorr_antitone hm) (snormLogCorr_bddBelow hm)

theorem tendsto_corr_zero :
    Tendsto (fun n : ℕ => (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ((1 : ℝ) / 4) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa using h.const_mul (1 / 3 : ℝ)

/-- **The limit exists**: `log (genProd m N) / 2 ^ N → sgrowth m`. -/
theorem tendsto_snormLog (hm : 2 ≤ m) : Tendsto (snormLog m) atTop (𝓝 (sgrowth m)) := by
  have h := (tendsto_snormLogCorr hm).sub tendsto_corr_zero
  simp only [sub_zero] at h
  refine h.congr fun n => ?_
  unfold snormLogCorr; ring

theorem sgrowth_nonneg (hm : 2 ≤ m) : 0 ≤ sgrowth m :=
  ge_of_tendsto' (tendsto_snormLog hm) (fun n => (snormLog_pos hm n).le)

theorem sgrowth_le (hm : 2 ≤ m) (n : ℕ) : sgrowth m ≤ snormLogCorr m n :=
  ciInf_le (snormLogCorr_bddBelow hm) n

/-! ## Part 5: `sgrowth m = 0` is exactly (C∞) for the seed -/

/-- (C∞) for the seed `m`: infinitely many composite Euclid numbers along its orbit. -/
def SeedInfinitelyManyComposite (m : ℕ) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ ¬ Nat.Prime (genProd m n + 1)

/-- At a prime stage the defect is non-positive. -/
theorem sdefect_nonpos_of_prime (hm : 2 ≤ m) {n : ℕ} (h : Nat.Prime (genProd m n + 1)) :
    sdefect m n ≤ 0 := by
  have hseq : genSeq m n = genProd m n + 1 := by
    rw [genSeq_def]; exact h.minFac_eq
  have hlt : (genProd m n : ℝ) ≤ ((genProd m n : ℕ) : ℝ) + 1 := by linarith
  have := Real.log_le_log (genProd_pos_real hm n) hlt
  unfold sdefect slogProd
  rw [hseq]
  push_cast
  linarith

/-- **`sgrowth m = 0 ⟹ (C∞)` for the seed.**  If the Euclid numbers were eventually prime,
the normalised logarithm would be nondecreasing from that stage on, hence bounded below by
a positive number, so `C > 0`. -/
theorem seedInfinitelyManyComposite_of_sgrowth_eq_zero (hm : 2 ≤ m) (h : sgrowth m = 0) :
    SeedInfinitelyManyComposite m := by
  by_contra hcon
  unfold SeedInfinitelyManyComposite at hcon
  push Not at hcon
  obtain ⟨N₀, hN₀⟩ := hcon
  -- from `N₀` on, `snormLog` is nondecreasing
  have hmono : ∀ n, N₀ ≤ n → snormLog m N₀ ≤ snormLog m n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih =>
      have hp := hN₀ n hn
      have hd := sdefect_nonpos_of_prime hm hp
      rw [snormLog_succ hm]
      have : (0 : ℝ) < 2 ^ (n + 1) := by positivity
      have : sdefect m n / 2 ^ (n + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hd this.le
      linarith
  have hlim : snormLog m N₀ ≤ sgrowth m := by
    refine ge_of_tendsto (tendsto_snormLog hm) ?_
    filter_upwards [Filter.eventually_ge_atTop N₀] with n hn using hmono n hn
  have := snormLog_pos hm N₀
  linarith

/-- Trial division: at a composite stage the least prime factor is at most the square root. -/
theorem log_genSeq_le_half_of_not_prime (hm : 2 ≤ m) {n : ℕ}
    (h : ¬ Nat.Prime (genProd m n + 1)) :
    Real.log (genSeq m n) ≤ (1 / 2) * Real.log ((genProd m n : ℝ) + 1) := by
  have hsq : Nat.minFac (genProd m n + 1) ^ 2 ≤ genProd m n + 1 :=
    Nat.minFac_sq_le_self (by omega) h
  have hR : ((genSeq m n : ℕ) : ℝ) ^ 2 ≤ ((genProd m n : ℕ) : ℝ) + 1 := by
    rw [genSeq_def]; exact_mod_cast hsq
  have hpos : (0 : ℝ) < ((genSeq m n : ℕ) : ℝ) := genSeq_pos_real hm n
  have hlog := Real.log_le_log (by positivity) hR
  rw [Real.log_pow] at hlog
  push_cast at hlog
  linarith

theorem log_genProd_add_one_le (hm : 2 ≤ m) (n : ℕ) :
    Real.log ((genProd m n : ℝ) + 1) ≤ slogProd m n + ((1 : ℝ) / 2) ^ (n + 1) := by
  have hP0 : (0 : ℝ) < (genProd m n : ℝ) := genProd_pos_real hm n
  have hPow : ((2 : ℝ)) ^ (n + 1) ≤ (genProd m n : ℝ) := by
    exact_mod_cast two_pow_succ_le_genProd hm n
  have h := Real.log_le_sub_one_of_pos
    (x := ((genProd m n : ℝ) + 1) / (genProd m n : ℝ)) (by positivity)
  rw [Real.log_div (by positivity) (ne_of_gt hP0)] at h
  have hsimp : ((genProd m n : ℝ) + 1) / (genProd m n : ℝ) - 1 = 1 / (genProd m n : ℝ) := by
    field_simp; ring
  rw [hsimp] at h
  have htail : 1 / (genProd m n : ℝ) ≤ ((1 : ℝ) / 2) ^ (n + 1) := by
    rw [div_pow, one_pow]
    exact one_div_le_one_div_of_le (by positivity) hPow
  unfold slogProd
  linarith

theorem half_slogProd_le_sdefect_of_not_prime (hm : 2 ≤ m) {n : ℕ}
    (h : ¬ Nat.Prime (genProd m n + 1)) :
    (1 / 2) * slogProd m n - (1 / 2) * ((1 : ℝ) / 2) ^ (n + 1) ≤ sdefect m n := by
  have h1 := log_genSeq_le_half_of_not_prime hm h
  have h2 := log_genProd_add_one_le hm n
  unfold sdefect
  linarith

/-- **A composite stage contracts the corrected telescope by `3/4`.** -/
theorem snormLogCorr_succ_le_of_not_prime (hm : 2 ≤ m) {n : ℕ}
    (h : ¬ Nat.Prime (genProd m n + 1)) :
    snormLogCorr m (n + 1) ≤ (3 / 4) * snormLogCorr m n := by
  have hd := half_slogProd_le_sdefect_of_not_prime hm h
  have h2 : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have hq : ((1 : ℝ) / 4) ^ (n + 1) * 2 ^ (n + 1) = ((1 : ℝ) / 2) ^ (n + 1) := by
    rw [← mul_pow]; norm_num
  have hp : (slogProd m n / 2 ^ n) * 2 ^ (n + 1) = 2 * slogProd m n := by
    have hne : ((2 : ℝ)) ^ n ≠ 0 := by positivity
    rw [pow_succ]; field_simp
  have hdiv : (1 / 4) * snormLog m n - (1 / 2) * ((1 : ℝ) / 4) ^ (n + 1)
      ≤ sdefect m n / 2 ^ (n + 1) := by
    rw [le_div_iff₀ h2, snormLog]
    have hid : ((1 : ℝ) / 4 * (slogProd m n / 2 ^ n) - 1 / 2 * ((1 : ℝ) / 4) ^ (n + 1))
        * 2 ^ (n + 1)
        = (1 / 2) * slogProd m n - (1 / 2) * ((1 : ℝ) / 2) ^ (n + 1) := by
      rw [sub_mul, mul_assoc, hp, mul_assoc, hq]; ring
    rw [hid]
    exact hd
  have hcorr : ((1 : ℝ) / 4) ^ (n + 1) = (1 / 4) * ((1 : ℝ) / 4) ^ n := by
    rw [pow_succ]; ring
  rw [hcorr] at hdiv
  have ha : (0 : ℝ) ≤ ((1 : ℝ) / 4) ^ n := by positivity
  unfold snormLogCorr
  rw [snormLog_succ hm, hcorr]
  linarith

/-- The number of composite Euclid numbers among the first `N` stages of the orbit of `m`. -/
def scompCount (m N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => ¬ Nat.Prime (genProd m n + 1))).card

theorem scompCount_succ_of_prime {N : ℕ} (h : Nat.Prime (genProd m N + 1)) :
    scompCount m (N + 1) = scompCount m N := by
  unfold scompCount
  rw [Finset.range_add_one, Finset.filter_insert, if_neg (by simpa using h)]

theorem scompCount_succ_of_not_prime {N : ℕ} (h : ¬ Nat.Prime (genProd m N + 1)) :
    scompCount m (N + 1) = scompCount m N + 1 := by
  unfold scompCount
  rw [Finset.range_add_one, Finset.filter_insert, if_pos h, Finset.card_insert_of_notMem]
  simp

theorem snormLogCorr_le_pow (hm : 2 ≤ m) (N : ℕ) :
    snormLogCorr m N ≤ (3 / 4 : ℝ) ^ scompCount m N * snormLogCorr m 0 := by
  induction N with
  | zero => simp [scompCount]
  | succ N ih =>
      by_cases h : Nat.Prime (genProd m N + 1)
      · rw [scompCount_succ_of_prime h]
        exact le_trans (snormLogCorr_antitone hm (Nat.le_succ N)) ih
      · rw [scompCount_succ_of_not_prime h, pow_succ]
        have hpos : (0 : ℝ) ≤ (3 / 4 : ℝ) := by norm_num
        calc snormLogCorr m (N + 1) ≤ (3 / 4) * snormLogCorr m N :=
              snormLogCorr_succ_le_of_not_prime hm h
          _ ≤ (3 / 4) * ((3 / 4 : ℝ) ^ scompCount m N * snormLogCorr m 0) := by
              exact mul_le_mul_of_nonneg_left ih hpos
          _ = (3 / 4 : ℝ) ^ scompCount m N * (3 / 4) * snormLogCorr m 0 := by ring

/-- Under (C∞) the composite count is unbounded. -/
theorem exists_le_scompCount (h : SeedInfinitelyManyComposite m) (M : ℕ) :
    ∃ N, M ≤ scompCount m N := by
  induction M with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ M ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨n, hn, hcomp⟩ := h N
    refine ⟨n + 1, ?_⟩
    have hmono : scompCount m N ≤ scompCount m n := by
      unfold scompCount
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr hn))
    rw [scompCount_succ_of_not_prime hcomp]
    omega

/-- **(C∞) for the seed ⟹ `sgrowth m = 0`.** -/
theorem sgrowth_eq_zero_of_seedInfinitelyManyComposite (hm : 2 ≤ m)
    (h : SeedInfinitelyManyComposite m) : sgrowth m = 0 := by
  have hc0 : 0 < snormLogCorr m 0 := snormLogCorr_pos hm 0
  refine le_antisymm ?_ (sgrowth_nonneg hm)
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have htend : Tendsto (fun M : ℕ => (3 / 4 : ℝ) ^ M * snormLogCorr m 0) atTop (𝓝 0) := by
    have h1 : Tendsto (fun M : ℕ => (3 / 4 : ℝ) ^ M) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using h1.mul_const (snormLogCorr m 0)
  obtain ⟨M, hM⟩ := (htend.eventually (gt_mem_nhds (show (0 : ℝ) < ε by linarith))).exists
  obtain ⟨N, hN⟩ := exists_le_scompCount h M
  have hmono : (3 / 4 : ℝ) ^ scompCount m N ≤ (3 / 4 : ℝ) ^ M :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hN
  have h1 := sgrowth_le hm N
  have h2 := snormLogCorr_le_pow hm N
  nlinarith [hM, hmono, h1, h2, hc0]

/-- **The growth constant of a seed is a complete invariant for (C∞) along its orbit.** -/
theorem seedInfinitelyManyComposite_iff_sgrowth_eq_zero (hm : 2 ≤ m) :
    SeedInfinitelyManyComposite m ↔ sgrowth m = 0 :=
  ⟨sgrowth_eq_zero_of_seedInfinitelyManyComposite hm,
   seedInfinitelyManyComposite_of_sgrowth_eq_zero hm⟩

/-- `sgrowth m > 0` iff the orbit of `m` is eventually a tower of primes. -/
theorem sgrowth_pos_iff_eventually_prime (hm : 2 ≤ m) :
    0 < sgrowth m ↔ ∃ N₀, ∀ n, N₀ ≤ n → Nat.Prime (genProd m n + 1) := by
  rw [← not_iff_not, not_lt, not_exists]
  have h0 : sgrowth m ≤ 0 ↔ sgrowth m = 0 := ⟨fun h => le_antisymm h (sgrowth_nonneg hm),
    fun h => h.le⟩
  rw [h0, ← seedInfinitelyManyComposite_iff_sgrowth_eq_zero hm]
  unfold SeedInfinitelyManyComposite
  constructor
  · intro h N₀ hall
    obtain ⟨n, hn, hc⟩ := h N₀
    exact hc (hall n hn)
  · intro h N
    by_contra hcon
    push Not at hcon
    exact h N hcon

/-! ## Part 6: the semiconjugacy `C(T m) = 2 C(m)` -/

/-- One step of the orbit shifts the normalised logarithm by one and doubles it. -/
theorem snormLog_step (m k : ℕ) : snormLog (genProd m 1) k = 2 * snormLog m (k + 1) := by
  unfold snormLog slogProd
  rw [genProd_restart, add_comm 1 k]
  have h2 : ((2 : ℝ)) ^ k ≠ 0 := by positivity
  rw [pow_succ]
  field_simp

/-- **The semiconjugacy**: `C(T m) = 2 · C(m)`, where `T m = genProd m 1 = m · minFac (m+1)`. -/
theorem sgrowth_T (hm : 2 ≤ m) : sgrowth (genProd m 1) = 2 * sgrowth m := by
  have hm' : 2 ≤ genProd m 1 := two_le_genProd hm 1
  have h1 := tendsto_snormLog hm'
  have h2 : Tendsto (fun k => snormLog (genProd m 1) k) atTop (𝓝 (2 * sgrowth m)) := by
    have := ((tendsto_snormLog hm).comp (tendsto_add_atTop_nat 1)).const_mul 2
    refine this.congr fun k => ?_
    simp only [Function.comp]
    exact (snormLog_step m k).symm
  exact tendsto_nhds_unique h1 h2

/-- Iterated: `C(Tᵏ m) = 2ᵏ · C(m)`. -/
theorem sgrowth_iterate (hm : 2 ≤ m) (k : ℕ) : sgrowth (genProd m k) = 2 ^ k * sgrowth m := by
  induction k with
  | zero => simp [genProd]
  | succ k ih =>
    have hk : 2 ≤ genProd m k := two_le_genProd hm k
    have := sgrowth_T hk
    rw [genProd_restart, add_comm k 1] at this
    rw [add_comm k 1] at *
    rw [this, ih]; ring

/-- The set `{m : C(m) > 0}` is `T`-invariant. -/
theorem sgrowth_pos_T (hm : 2 ≤ m) : 0 < sgrowth (genProd m 1) ↔ 0 < sgrowth m := by
  rw [sgrowth_T hm]; constructor <;> intro h <;> linarith

/-! ## Part 7: consistency with the standard orbit, and the universal statement -/

/-- The seed `2` recovers `DefectTelescope.growthConstant`. -/
theorem sgrowth_two : sgrowth 2 = DefectTelescope.growthConstant := by
  unfold sgrowth DefectTelescope.growthConstant
  congr 1; funext n
  unfold snormLogCorr DefectTelescope.normLogCorr snormLog DefectTelescope.normLog
    slogProd DefectTelescope.logProd
  rw [genProd_two_eq_prod]

/-- **The registered open point `MixedDiversity` is `{m ≥ 2 : C(m) > 0} = ∅`.**  Every seed
has vanishing growth constant iff every seed has infinitely many composite Euclid numbers. -/
theorem mixedDiversity_iff_sgrowth_zero :
    MixedDiversity ↔ ∀ acc : ℕ, 2 ≤ acc → sgrowth acc = 0 := by
  unfold MixedDiversity
  constructor
  · intro h acc hacc
    refine sgrowth_eq_zero_of_seedInfinitelyManyComposite hacc ?_
    intro N
    obtain ⟨n, hn, hc⟩ := h acc hacc N
    exact ⟨n, hn, by rwa [mixedWalkProd_minFac_eq_genProd] at hc⟩
  · intro h acc hacc N
    obtain ⟨n, hn, hc⟩ := seedInfinitelyManyComposite_of_sgrowth_eq_zero hacc (h acc hacc) N
    exact ⟨n, hn, by rwa [mixedWalkProd_minFac_eq_genProd]⟩

/-- **The seeded landscape.** -/
theorem seeded_growth_landscape :
    (∀ m : ℕ, 2 ≤ m → (SeedInfinitelyManyComposite m ↔ sgrowth m = 0)) ∧
    (∀ m : ℕ, 2 ≤ m → sgrowth (genProd m 1) = 2 * sgrowth m) ∧
    sgrowth 2 = DefectTelescope.growthConstant ∧
    (MixedDiversity ↔ ∀ acc : ℕ, 2 ≤ acc → sgrowth acc = 0) :=
  ⟨fun _ hm => seedInfinitelyManyComposite_iff_sgrowth_eq_zero hm,
   fun _ hm => sgrowth_T hm, sgrowth_two, mixedDiversity_iff_sgrowth_zero⟩

end SeededGrowth

end
