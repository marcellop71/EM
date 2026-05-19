import EM.Population.SeededGrowth

/-!
# The relative-size invariant `ρ`: a second, unscaled invariant of `T`

`C(Tm) = 2·C(m)` is scaled by `T`.  Here is an invariant that is *not*: for a seed `m ≥ 2`,

  `ρ(m) := liminf_n  log(minFac(T^n m + 1)) / log(T^n m)`,

the asymptotic relative size of the selected multiplier against the accumulator.  Since `T`
acts on the orbit as the shift, `ρ(Tm) = ρ(m)` exactly (`rho_T`), and `0 ≤ ρ ≤ 2`.

`ρ` refines the growth dichotomy and the floor ladder:

* `C(m) > 0 ⟺ ρ(m) = 1` (`sgrowth_pos_iff_rho_eq_one`): on the perpetual-primality branch the
  multiplier is `T^n m + 1` itself, ratio `→ 1`;
* `C(m) = 0 ⟺ ρ(m) ≤ 1/2 ⟺ ρ(m) < 1` (`sgrowth_eq_zero_iff_rho_le_half`): at a composite
  stage `minFac(P+1)² ≤ P+1`, ratio `≤ 1/2 + o(1)`; so `ρ ∈ [0, 1/2] ∪ {1}` (`rho_dichotomy`);
* seeded reciprocal divergence forces `ρ(m) = 0` (`rho_eq_zero_of_seedRD`): if `ρ > ε` then
  eventually `minFac(P+1) ≥ P^ε ≥ 2^{εn}` and `∑ 1/minFac` converges.

For the orbit of `2` this inserts a rung in the floor ladder
(`relative_size_landscape`):

  `MC ⇒ RD ⇒ ρ(2) = 0 ⇒ ρ(2) ≤ 1/2 ⟺ (C∞) ⟺ C = 0`.

Whether `ρ(2) = 0` is strictly weaker than RD, or strictly stronger than `(C∞)`, is open; the
paper's "(S)" (least factor below `2^{n−c}` i.o.) sits between RD and `ρ(2) = 0` as well.
Nothing here touches MC upward: `ρ` is a growth-side quantity and inherits the size–residue
decoupling of `SizeResidueDecoupling`.
-/

noncomputable section

open Filter Topology

namespace RelativeSize

variable {m : ℕ}

/-- The relative size of the multiplier at stage `n`. -/
def ratio (m n : ℕ) : ℝ := Real.log (genSeq m n) / Real.log (genProd m n)

/-- The relative-size invariant `ρ(m) = liminf ratio`. -/
def rho (m : ℕ) : ℝ := liminf (fun n => ratio m n) atTop

/-! ## Elementary bounds -/

theorem log_genProd_pos (hm : 2 ≤ m) (n : ℕ) : 0 < Real.log (genProd m n) :=
  Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two (SeededGrowth.two_le_genProd hm n))

theorem two_le_genSeq (hm : 2 ≤ m) (n : ℕ) : 2 ≤ genSeq m n := by
  have h := SeededGrowth.two_le_genProd hm n
  exact (Nat.minFac_prime (by omega : genProd m n + 1 ≠ 1)).two_le

theorem genSeq_le_succ (m n : ℕ) : genSeq m n ≤ genProd m n + 1 :=
  Nat.minFac_le (by omega)

theorem two_pow_le_genProd (hm : 2 ≤ m) (n : ℕ) : 2 ^ n ≤ genProd m n := by
  induction n with
  | zero => simp [genProd]; omega
  | succ n ih =>
    rw [genProd_succ, pow_succ]
    exact Nat.mul_le_mul ih (two_le_genSeq hm n)

theorem ratio_nonneg (hm : 2 ≤ m) (n : ℕ) : 0 ≤ ratio m n := by
  unfold ratio
  apply div_nonneg _ (log_genProd_pos hm n).le
  exact Real.log_nonneg (by exact_mod_cast le_trans one_le_two (two_le_genSeq hm n))

theorem ratio_le_two (hm : 2 ≤ m) (n : ℕ) : ratio m n ≤ 2 := by
  unfold ratio
  rw [div_le_iff₀ (log_genProd_pos hm n)]
  have hP : (2 : ℝ) ≤ genProd m n := by exact_mod_cast SeededGrowth.two_le_genProd hm n
  have h1 : (genSeq m n : ℝ) ≤ (genProd m n : ℝ) ^ 2 := by
    have := genSeq_le_succ m n
    have : (genSeq m n : ℝ) ≤ (genProd m n : ℝ) + 1 := by exact_mod_cast this
    nlinarith
  calc Real.log (genSeq m n) ≤ Real.log ((genProd m n : ℝ) ^ 2) :=
        Real.log_le_log (by exact_mod_cast lt_of_lt_of_le two_pos (two_le_genSeq hm n)) h1
    _ = 2 * Real.log (genProd m n) := by
        rw [Real.log_pow]; push_cast; ring

theorem isBoundedUnder_ratio (hm : 2 ≤ m) :
    IsBoundedUnder (· ≥ ·) atTop (fun n => ratio m n) :=
  isBoundedUnder_of_eventually_ge (Eventually.of_forall (ratio_nonneg hm))

theorem isCoboundedUnder_ratio (hm : 2 ≤ m) :
    IsCoboundedUnder (· ≥ ·) atTop (fun n => ratio m n) :=
  isCoboundedUnder_ge_of_eventually_le atTop (Eventually.of_forall (ratio_le_two hm))

theorem rho_nonneg (hm : 2 ≤ m) : 0 ≤ rho m :=
  le_liminf_of_le (isCoboundedUnder_ratio hm) (Eventually.of_forall (ratio_nonneg hm))

theorem rho_le_two (hm : 2 ≤ m) : rho m ≤ 2 :=
  liminf_le_of_le (isBoundedUnder_ratio hm) fun b hb => by
    obtain ⟨n, hn⟩ := hb.exists
    exact hn.trans (ratio_le_two hm n)

/-! ## Shift invariance -/

theorem ratio_T (m n : ℕ) : ratio (genProd m 1) n = ratio m (n + 1) := by
  unfold ratio genSeq
  rw [genProd_restart, show 1 + n = n + 1 from Nat.add_comm 1 n]

/-- **`ρ` is a genuine invariant of `T`: `ρ(Tm) = ρ(m)`.** -/
theorem rho_T (m : ℕ) : rho (genProd m 1) = rho m := by
  unfold rho
  simp_rw [ratio_T]
  exact liminf_nat_add (fun n => ratio m n) 1

theorem rho_iterate (m k : ℕ) : rho (genProd m k) = rho m := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have : genProd m (k + 1) = genProd (genProd m k) 1 := by
      rw [genProd_restart]
    rw [this, rho_T, ih]

/-! ## The dichotomy -/

/-- On the perpetual-primality branch the ratio is `≥ 1` and `≤ 1 + 2/P`. -/
theorem ratio_bounds_of_prime (hm : 2 ≤ m) {n : ℕ} (h : Nat.Prime (genProd m n + 1)) :
    1 ≤ ratio m n ∧ ratio m n ≤ 1 + 2 / (genProd m n : ℝ) := by
  have hP : (2 : ℝ) ≤ genProd m n := by exact_mod_cast SeededGrowth.two_le_genProd hm n
  have hPpos : (0 : ℝ) < genProd m n := by linarith
  have hlog := log_genProd_pos hm n
  have hseq : genSeq m n = genProd m n + 1 := Nat.Prime.minFac_eq h
  unfold ratio
  rw [hseq]
  push_cast
  constructor
  · rw [le_div_iff₀ hlog, one_mul]
    exact Real.log_le_log hPpos (by linarith)
  · rw [div_le_iff₀ hlog]
    -- `log(P+1) = log P + log(1 + 1/P) ≤ log P + 1/P`, and `1/P ≤ (2/P) log P` since `log P ≥ 1/2`
    have hsplit : Real.log ((genProd m n : ℝ) + 1) =
        Real.log (genProd m n) + Real.log (1 + 1 / (genProd m n : ℝ)) := by
      rw [← Real.log_mul hPpos.ne' (by positivity)]
      congr 1; field_simp
    have h1 : Real.log (1 + 1 / (genProd m n : ℝ)) ≤ 1 / (genProd m n : ℝ) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (genProd m n : ℝ) by positivity)
      linarith
    have hlog2 : (1 : ℝ) / 2 ≤ Real.log (genProd m n) := by
      have := Real.log_two_gt_d9
      have := Real.log_le_log two_pos hP
      linarith
    have h2 : 1 / (genProd m n : ℝ) ≤ 2 / (genProd m n : ℝ) * Real.log (genProd m n) := by
      have hinv : (0 : ℝ) < 1 / (genProd m n : ℝ) := by positivity
      calc 1 / (genProd m n : ℝ) = 2 / (genProd m n : ℝ) * (1 / 2) := by ring
        _ ≤ 2 / (genProd m n : ℝ) * Real.log (genProd m n) :=
            mul_le_mul_of_nonneg_left hlog2 (by positivity)
    rw [hsplit]
    linarith

/-- At a composite stage the ratio is `≤ 1/2 + 1/P`. -/
theorem ratio_le_of_not_prime (hm : 2 ≤ m) {n : ℕ} (h : ¬ Nat.Prime (genProd m n + 1)) :
    ratio m n ≤ 1 / 2 + 1 / (genProd m n : ℝ) := by
  have hP : (2 : ℝ) ≤ genProd m n := by exact_mod_cast SeededGrowth.two_le_genProd hm n
  have hPpos : (0 : ℝ) < genProd m n := by linarith
  have hlog := log_genProd_pos hm n
  have hsq : genSeq m n ^ 2 ≤ genProd m n + 1 := Nat.minFac_sq_le_self (by omega) h
  have hsqr : ((genSeq m n : ℝ)) ^ 2 ≤ (genProd m n : ℝ) + 1 := by exact_mod_cast hsq
  have hseq_pos : (0 : ℝ) < genSeq m n := by
    exact_mod_cast lt_of_lt_of_le two_pos (two_le_genSeq hm n)
  unfold ratio
  rw [div_le_iff₀ hlog]
  have h1 : 2 * Real.log (genSeq m n) ≤ Real.log ((genProd m n : ℝ) + 1) := by
    have hp : Real.log ((genSeq m n : ℝ) ^ 2) = 2 * Real.log (genSeq m n) := by
      rw [Real.log_pow]; push_cast; ring
    rw [← hp]
    exact Real.log_le_log (by positivity) hsqr
  have hsplit : Real.log ((genProd m n : ℝ) + 1) =
      Real.log (genProd m n) + Real.log (1 + 1 / (genProd m n : ℝ)) := by
    rw [← Real.log_mul hPpos.ne' (by positivity)]
    congr 1; field_simp
  have h2 : Real.log (1 + 1 / (genProd m n : ℝ)) ≤ 1 / (genProd m n : ℝ) := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (genProd m n : ℝ) by positivity)
    linarith
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log (genProd m n) := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log two_pos hP
    linarith
  have h3 : 1 / (genProd m n : ℝ) ≤ 1 / (genProd m n : ℝ) * (2 * Real.log (genProd m n)) := by
    have hinv : (0 : ℝ) ≤ 1 / (genProd m n : ℝ) := by positivity
    nlinarith
  nlinarith

/-- `genProd m n → ∞` (as reals). -/
theorem tendsto_genProd_atTop (hm : 2 ≤ m) :
    Tendsto (fun n => (genProd m n : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun n => ?_) (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℝ)))
  exact_mod_cast two_pow_le_genProd hm n

theorem eventually_inv_genProd_le (hm : 2 ≤ m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, 1 / (genProd m n : ℝ) ≤ ε := by
  have h := (tendsto_genProd_atTop hm).eventually_ge_atTop (1 / ε)
  filter_upwards [h] with n hn
  have hPpos : (0 : ℝ) < genProd m n := by
    have := SeededGrowth.two_le_genProd hm n
    exact_mod_cast (by omega : 0 < genProd m n)
  rw [div_le_iff₀ hPpos]
  rw [div_le_iff₀ hε] at hn
  linarith

/-- **`C(m) > 0 ⇒ ρ(m) = 1`.** -/
theorem rho_eq_one_of_sgrowth_pos (hm : 2 ≤ m) (h : 0 < SeededGrowth.sgrowth m) : rho m = 1 := by
  obtain ⟨N₀, hN₀⟩ := (SeededGrowth.sgrowth_pos_iff_eventually_prime hm).mp h
  apply le_antisymm
  · -- `ρ ≤ 1 + ε` for every `ε > 0`
    apply le_of_forall_pos_le_add
    intro ε hε
    apply liminf_le_of_le (isBoundedUnder_ratio hm)
    intro b hb
    have hev : ∀ᶠ n in atTop, ratio m n ≤ 1 + ε := by
      filter_upwards [eventually_inv_genProd_le hm (half_pos hε), eventually_ge_atTop N₀]
        with n hn hnN
      have := (ratio_bounds_of_prime hm (hN₀ n hnN)).2
      have h2 : 2 / (genProd m n : ℝ) = 2 * (1 / (genProd m n : ℝ)) := by ring
      linarith
    obtain ⟨n, hb', hn⟩ := (hb.and hev).exists
    linarith
  · apply le_liminf_of_le (isCoboundedUnder_ratio hm)
    filter_upwards [eventually_ge_atTop N₀] with n hn
    exact (ratio_bounds_of_prime hm (hN₀ n hn)).1

/-- **`C(m) = 0 ⇒ ρ(m) ≤ 1/2`.** -/
theorem rho_le_half_of_sgrowth_zero (hm : 2 ≤ m) (h : SeededGrowth.sgrowth m = 0) :
    rho m ≤ 1 / 2 := by
  have hcomp := (SeededGrowth.seedInfinitelyManyComposite_iff_sgrowth_eq_zero hm).mpr h
  apply le_of_forall_pos_le_add
  intro ε hε
  apply liminf_le_of_le (isBoundedUnder_ratio hm)
  intro b hb
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (eventually_inv_genProd_le hm hε)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hb
  obtain ⟨n, hn, hncomp⟩ := hcomp (max N₁ N₂)
  have h1 := ratio_le_of_not_prime hm hncomp
  have h2 := hN₁ n (le_trans (le_max_left _ _) hn)
  have h3 := hN₂ n (le_trans (le_max_right _ _) hn)
  linarith

theorem sgrowth_pos_iff_rho_eq_one (hm : 2 ≤ m) : 0 < SeededGrowth.sgrowth m ↔ rho m = 1 := by
  constructor
  · exact rho_eq_one_of_sgrowth_pos hm
  · intro h
    rcases eq_or_lt_of_le (SeededGrowth.sgrowth_nonneg hm) with h0 | h0
    · have := rho_le_half_of_sgrowth_zero hm h0.symm
      rw [h] at this; norm_num at this
    · exact h0

theorem sgrowth_eq_zero_iff_rho_le_half (hm : 2 ≤ m) :
    SeededGrowth.sgrowth m = 0 ↔ rho m ≤ 1 / 2 := by
  constructor
  · exact rho_le_half_of_sgrowth_zero hm
  · intro h
    rcases eq_or_lt_of_le (SeededGrowth.sgrowth_nonneg hm) with h0 | h0
    · exact h0.symm
    · have := rho_eq_one_of_sgrowth_pos hm h0
      rw [this] at h; norm_num at h

theorem sgrowth_eq_zero_iff_rho_lt_one (hm : 2 ≤ m) :
    SeededGrowth.sgrowth m = 0 ↔ rho m < 1 := by
  rw [sgrowth_eq_zero_iff_rho_le_half hm]
  constructor
  · intro h; linarith
  · intro h
    by_contra hcon
    push Not at hcon
    have h0 : 0 < SeededGrowth.sgrowth m := by
      rcases eq_or_lt_of_le (SeededGrowth.sgrowth_nonneg hm) with h0 | h0
      · exact absurd ((sgrowth_eq_zero_iff_rho_le_half hm).mp h0.symm) (not_le.mpr hcon)
      · exact h0
    have := rho_eq_one_of_sgrowth_pos hm h0
    linarith

/-- **The dichotomy: `ρ ∈ [0, 1/2] ∪ {1}`.** -/
theorem rho_dichotomy (hm : 2 ≤ m) : rho m = 1 ∨ rho m ≤ 1 / 2 := by
  rcases eq_or_lt_of_le (SeededGrowth.sgrowth_nonneg hm) with h0 | h0
  · exact Or.inr (rho_le_half_of_sgrowth_zero hm h0.symm)
  · exact Or.inl (rho_eq_one_of_sgrowth_pos hm h0)

/-! ## Reciprocal divergence forces `ρ = 0` -/

/-- Seeded reciprocal divergence: `∑ 1/genSeq m k` diverges. -/
def SeedReciprocalDivergence (m : ℕ) : Prop :=
  ¬ Summable (fun k : ℕ => (1 : ℝ) / genSeq m k)

/-- If `ρ(m) > ε > 0` then eventually `genSeq m n ≥ (2^ε)^n`, so the reciprocals are summable. -/
theorem summable_of_rho_pos (hm : 2 ≤ m) (h : 0 < rho m) :
    Summable (fun k : ℕ => (1 : ℝ) / genSeq m k) := by
  set ε := rho m / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hεlt : ε < rho m := by linarith
  have hev := eventually_lt_of_lt_liminf hεlt (isBoundedUnder_ratio hm)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  -- the geometric ratio `r = exp(ε log 2) > 1`
  set r : ℝ := Real.exp (ε * Real.log 2) with hr
  have hr1 : 1 < r := by
    rw [hr]; apply Real.one_lt_exp_iff.mpr; positivity
  have hr0 : 0 < r := by positivity
  have hle : ∀ n, N ≤ n → (1 : ℝ) / genSeq m n ≤ (r⁻¹) ^ n := by
    intro n hn
    have hratio := hN n hn
    have hlog := log_genProd_pos hm n
    have hseq_pos : (0 : ℝ) < genSeq m n := by
      exact_mod_cast lt_of_lt_of_le two_pos (two_le_genSeq hm n)
    -- `log genSeq > ε log P ≥ ε n log 2`
    have h1 : ε * Real.log (genProd m n) < Real.log (genSeq m n) := by
      unfold ratio at hratio
      rw [lt_div_iff₀ hlog] at hratio
      linarith
    have h2 : (n : ℝ) * Real.log 2 ≤ Real.log (genProd m n) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (by exact_mod_cast two_pow_le_genProd hm n)
    have h3 : r ^ n ≤ (genSeq m n : ℝ) := by
      rw [hr, ← Real.exp_nat_mul, ← Real.exp_log hseq_pos]
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left h2 hε0.le
      nlinarith
    rw [inv_pow, one_div]
    exact inv_anti₀ (by positivity) h3
  have hgeom : Summable (fun n : ℕ => (r⁻¹) ^ n) :=
    summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hr1)
  -- compare on the tail
  rw [← summable_nat_add_iff N]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => hle (k + N) (by omega)) ?_
  exact (summable_nat_add_iff N).mpr hgeom

/-- **Seeded RD ⇒ `ρ = 0`.** -/
theorem rho_eq_zero_of_seedRD (hm : 2 ≤ m) (h : SeedReciprocalDivergence m) : rho m = 0 := by
  rcases eq_or_lt_of_le (rho_nonneg hm) with h0 | h0
  · exact h0.symm
  · exact absurd (summable_of_rho_pos hm h0) h

/-! ## The orbit of `2` -/

theorem ratio_two (n : ℕ) :
    ratio 2 n = Real.log (Mullin.seq (n + 1)) / DefectTelescope.logProd n := by
  unfold ratio DefectTelescope.logProd
  rw [genSeq_two_eq_seq_succ, genProd_two_eq_prod]

theorem seedRD_two_iff : SeedReciprocalDivergence 2 ↔ ReciprocalDivergence := by
  unfold SeedReciprocalDivergence ReciprocalDivergence
  have : (fun k : ℕ => (1 : ℝ) / genSeq 2 k) = fun k => (1 : ℝ) / Mullin.seq (k + 1) := by
    funext k; rw [genSeq_two_eq_seq_succ]
  rw [this]
  exact not_congr (summable_nat_add_iff (f := fun k => (1 : ℝ) / Mullin.seq k) 1)

/-- **RD ⇒ `ρ(2) = 0`.** -/
theorem rho_two_eq_zero_of_rd (h : ReciprocalDivergence) : rho 2 = 0 :=
  rho_eq_zero_of_seedRD le_rfl (seedRD_two_iff.mpr h)

/-- **MC ⇒ `ρ(2) = 0`.** -/
theorem rho_two_eq_zero_of_mc (h : Mullin.MullinConjecture) : rho 2 = 0 :=
  rho_two_eq_zero_of_rd (mc_implies_rd h)

/-- `ρ(2) ≤ 1/2 ⟺ (C∞)` (via `sgrowth 2 = growthConstant`). -/
theorem rho_two_le_half_iff : rho 2 ≤ 1 / 2 ↔ AutonomousBranch.InfinitelyManyComposite := by
  rw [← sgrowth_eq_zero_iff_rho_le_half le_rfl, SeededGrowth.sgrowth_two]
  exact DefectTelescope.infinitelyManyComposite_iff_growthConstant_eq_zero.symm

/-- **Landscape.**  `ρ` is an exact `T`-invariant with `ρ ∈ [0,1/2] ∪ {1}`, `C > 0 ⟺ ρ = 1`,
`C = 0 ⟺ ρ ≤ 1/2`, and on the orbit of `2`: `MC ⇒ RD ⇒ ρ(2) = 0 ⇒ ρ(2) ≤ 1/2 ⟺ (C∞)`. -/
theorem relative_size_landscape :
    (∀ m : ℕ, rho (genProd m 1) = rho m) ∧
    (∀ m : ℕ, 2 ≤ m → (rho m = 1 ∨ rho m ≤ 1 / 2)) ∧
    (∀ m : ℕ, 2 ≤ m → (0 < SeededGrowth.sgrowth m ↔ rho m = 1)) ∧
    (∀ m : ℕ, 2 ≤ m → (SeededGrowth.sgrowth m = 0 ↔ rho m ≤ 1 / 2)) ∧
    (∀ m : ℕ, 2 ≤ m → SeedReciprocalDivergence m → rho m = 0) ∧
    (Mullin.MullinConjecture → rho 2 = 0) ∧
    (ReciprocalDivergence → rho 2 = 0) ∧
    (rho 2 ≤ 1 / 2 ↔ AutonomousBranch.InfinitelyManyComposite) :=
  ⟨rho_T, fun _ hm => rho_dichotomy hm, fun _ hm => sgrowth_pos_iff_rho_eq_one hm,
   fun _ hm => sgrowth_eq_zero_iff_rho_le_half hm, fun _ hm h => rho_eq_zero_of_seedRD hm h,
   rho_two_eq_zero_of_mc, rho_two_eq_zero_of_rd, rho_two_le_half_iff⟩

end RelativeSize

end
