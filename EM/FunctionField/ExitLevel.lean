import EM.FunctionField.StableAnalyticDensity

/-!
# The exit level of the tower has an exact analytic density

For a prime `p` the tower over `𝔽_p` is a sequence of level polynomials `level p k`, and
`level p (k+1)` is irreducible, given that `level p k` is, exactly when the integer discriminant
`Δ_k = discZ k` is not a square mod `p` (`StabilityCriterion.level_succ_irreducible_iff`). So the
tower is irreducible through level `K` exactly when `(Δ_k / p) = −1` for every `k < K`.

`StableAnalyticDensity` uses the detector `∏_{k<K} (1 − (Δ_k / p))` as an upper bound for the
stable primes. Here the same detector is evaluated exactly: it is `2^K` on the primes with all
`K` symbols `−1`, and `0` on every other prime not dividing `Δ_0 ⋯ Δ_{K−1}`. Since no product
`Δ_A`, `A ≠ ∅`, is a square, the conditions are independent and each has density `1/2`.

## Main results

* `survive_iff` — for odd `p`, the tower is irreducible through level `K` iff
  `(Δ_k / p) = −1` for all `k < K`.
* `survive_analytic_density` — the primes whose tower is irreducible through level `K` have
  analytic density `1 / 2^K`.
* `exit_analytic_density` — the primes whose tower is irreducible through level `K` and
  reducible at some level `≤ K + 1` (so: first reducible level exactly `K + 1`) have analytic
  density `1 / 2^(K+1)`.

Both statements are unconditional.
-/

namespace FunctionFieldAnalog

namespace ExitLevel

open Finset Filter Topology StablePrimes StableCount TowerClassification StabilityCriterion
open StableAnalyticDensity ArithmeticFunction

/-- The primes whose tower is irreducible through level `K`. -/
def surviveSet (K : ℕ) : Set ℕ := {p | ∃ h : p.Prime, ∀ k ≤ K, Irreducible (@level p ⟨h⟩ k)}

/-- The primes at which the first `K` discriminants are non-residues. -/
def nonresSet (K : ℕ) : Set ℕ := {p | p.Prime ∧ ∀ k < K, jacobiSym (discZ k) p = -1}

/-- The detector `∏_{k<K} (1 − (Δ_k / n))`. -/
def det (K n : ℕ) : ℤ := ∏ k ∈ range K, (1 - jacobiSym (discZ k) n)

/-! ## 1. Irreducibility through level `K` in terms of the symbols -/

/-- For odd `p`, the tower is irreducible through level `K` iff `(Δ_k / p) = −1` for `k < K`. -/
theorem survive_iff {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (K : ℕ) :
    (∀ k ≤ K, Irreducible (level p k)) ↔ ∀ k < K, jacobiSym (discZ k) p = -1 := by
  induction K with
  | zero =>
    refine ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ k hk => ?_⟩
    obtain rfl : k = 0 := Nat.le_zero.mp hk
    exact level_zero_irreducible
  | succ K ih =>
    have hstep : Irreducible (level p K) →
        (Irreducible (level p (K + 1)) ↔ jacobiSym (discZ K) p = -1) := fun hK => by
      rw [level_succ_irreducible_iff hp2 K hK, disc_eq_cast hp2,
        ← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
    constructor
    · intro h k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h' | rfl
      · exact (ih.mp fun j hj => h j (by omega)) k h'
      · exact (hstep (h k (by omega))).mp (h (k + 1) le_rfl)
    · intro h k hk
      have hK := ih.mpr fun j hj => h j (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hk) with h' | rfl
      · exact hK k (by omega)
      · exact (hstep (hK K le_rfl)).mpr (h K (by omega))

theorem mem_surviveSet_iff_of_ne_two {n : ℕ} (hn2 : n ≠ 2) (K : ℕ) :
    n ∈ surviveSet K ↔ n ∈ nonresSet K := by
  constructor
  · rintro ⟨hp, h⟩
    have : Fact n.Prime := ⟨hp⟩
    exact ⟨hp, (survive_iff hn2 K).mp h⟩
  · rintro ⟨hp, h⟩
    have : Fact n.Prime := ⟨hp⟩
    exact ⟨hp, (survive_iff hn2 K).mpr h⟩

theorem surviveSet_antitone {K L : ℕ} (h : K ≤ L) : surviveSet L ⊆ surviveSet K :=
  fun _ ⟨hp, hs⟩ => ⟨hp, fun k hk => hs k (hk.trans h)⟩

/-! ## 2. The detector -/

theorem det_nonneg (K n : ℕ) : 0 ≤ det K n := detector_nonneg K n

theorem det_le (K n : ℕ) : det K n ≤ 2 ^ K := by
  have h : det K n ≤ ∏ _k ∈ range K, (2 : ℤ) := by
    refine Finset.prod_le_prod₀ (fun k _ => ?_) (fun k _ => ?_) <;>
      rcases jacobiSym.trichotomy (discZ k) n with h | h | h <;> rw [h] <;> norm_num
  simpa using h

theorem det_of_mem {K n : ℕ} (h : n ∈ nonresSet K) : det K n = 2 ^ K := by
  rw [det, prod_congr rfl fun k hk => by rw [h.2 k (mem_range.mp hk)]]
  norm_num

/-- At a prime outside `nonresSet K` the detector vanishes, unless the prime divides one of the
    discriminants. -/
theorem det_eq_zero_or_dvd {K n : ℕ} (hp : n.Prime) (h : n ∉ nonresSet K) :
    det K n = 0 ∨ n ∣ ∏ k ∈ range K, (discZ k).natAbs := by
  by_cases hd : det K n = 0
  · exact Or.inl hd
  right
  have hne : ∀ k ∈ range K, 1 - jacobiSym (discZ k) n ≠ 0 := Finset.prod_ne_zero_iff.mp hd
  have hex : ∃ k, k < K ∧ jacobiSym (discZ k) n ≠ -1 := by
    by_contra hcon
    push Not at hcon
    exact h ⟨hp, hcon⟩
  obtain ⟨k, hk, hk1⟩ := hex
  have h0 : jacobiSym (discZ k) n = 0 := by
    rcases jacobiSym.trichotomy (discZ k) n with h | h | h
    · exact h
    · exact absurd (by rw [h, sub_self]) (hne k (mem_range.mpr hk))
    · exact absurd h hk1
  have hg := (jacobiSym.eq_zero_iff.mp h0).2
  have hdvd : n ∣ (discZ k).natAbs := by
    by_contra hnd
    apply hg
    have := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnd
    rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact Nat.Coprime.symm this
  exact hdvd.trans (Finset.dvd_prod_of_mem _ (mem_range.mpr hk))

theorem pw_le_log {x : ℝ} (hx : 1 ≤ x) (n : ℕ) : pw x n ≤ Real.log n := by
  by_cases hp : n.Prime
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hp.one_lt.le
    calc pw x n = vonMangoldt n / (n : ℝ) ^ x := by rw [pw, ite_eq_left hp]
      _ ≤ vonMangoldt n / n := div_rpow_le_div vonMangoldt_nonneg n hx
      _ ≤ vonMangoldt n := div_le_self vonMangoldt_nonneg hn1
      _ = Real.log n := vonMangoldt_apply_prime hp
  · rw [pw, ite_eq_right hp, zero_div]
    exact Real.log_natCast_nonneg n

theorem pw_of_not_prime (x : ℝ) {n : ℕ} (hp : ¬ n.Prime) : pw x n = 0 := by
  rw [pw, ite_eq_right hp, zero_div]

/-! ## 3. The detector series -/

theorem det_mul_pw (K : ℕ) (x : ℝ) (n : ℕ) : (det K n : ℝ) * pw x n =
    ∑ A ∈ (range K).powerset,
      (-1 : ℝ) ^ A.card * ((jacobiSym (discProd A) n : ℝ) * pw x n) := by
  rw [det, prod_one_sub_eq]
  push_cast
  rw [Finset.sum_mul]
  exact sum_congr rfl fun A _ => by ring

theorem summable_det_pw (K : ℕ) {x : ℝ} (hx : 1 < x) :
    Summable fun n : ℕ => (det K n : ℝ) * pw x n :=
  (summable_sum fun A (_ : A ∈ (range K).powerset) =>
    ((summable_mul_pw (abs_jacobiSym_le_one (discProd A)) hx).mul_left
      ((-1 : ℝ) ^ A.card))).congr fun n => (det_mul_pw K x n).symm

/-- The detector series expands over the subsets of `{0, …, K−1}`. -/
theorem tsum_det_pw (K : ℕ) {x : ℝ} (hx : 1 < x) :
    ∑' n : ℕ, (det K n : ℝ) * pw x n =
      ∑ A ∈ (range K).powerset,
        (-1 : ℝ) ^ A.card * ∑' n : ℕ, (jacobiSym (discProd A) n : ℝ) * pw x n := by
  rw [tsum_congr (det_mul_pw K x), Summable.tsum_finsetSum fun A _ =>
    (summable_mul_pw (abs_jacobiSym_le_one (discProd A)) hx).mul_left ((-1 : ℝ) ^ A.card)]
  exact sum_congr rfl fun A _ => by rw [tsum_mul_left]

/-- The detector series is `1/(x−1) + O_K(1)` on `(1, 2]`. -/
theorem det_bound (K : ℕ) : ∃ R : ℝ, ∀ x : ℝ, x ∈ Set.Ioc (1 : ℝ) 2 →
    |∑' n : ℕ, (det K n : ℝ) * pw x n - 1 / (x - 1)| ≤ R := by
  classical
  have hex : ∀ D : ℤ, ∃ C : ℝ, ¬ IsSquare D → ∀ x : ℝ, x ∈ Set.Ioc (1 : ℝ) 2 →
      |∑' n : ℕ, (jacobiSym D n : ℝ) * pw x n| ≤ C := fun D => by
    by_cases h : IsSquare D
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨C, hC⟩ := jacobi_bound h
      exact ⟨C, fun _ => hC⟩
  choose Cq hCq using hex
  obtain ⟨C0, hC0⟩ := pw_bound
  set U : Finset ℕ → ℝ := fun A => if A = ∅ then 0 else Cq (discProd A) with hU
  refine ⟨∑ A ∈ (range K).powerset, U A + C0, fun x hx => ?_⟩
  have hterm : ∀ A ∈ (range K).powerset,
      |(-1 : ℝ) ^ A.card * ∑' n : ℕ, (jacobiSym (discProd A) n : ℝ) * pw x n -
        (if A = ∅ then ∑' n, pw x n else 0)| ≤ U A := by
    intro A _
    by_cases hA : A = ∅
    · subst hA
      simp [hU, discProd, jacobiSym.one_left]
    · have hb := hCq (discProd A) (not_isSquare_prod_discZ (nonempty_iff_ne_empty.mpr hA)) x hx
      simp only [hU, ite_eq_right hA, sub_zero]
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact hb
  have h1 : |∑' n : ℕ, (det K n : ℝ) * pw x n - ∑' n, pw x n| ≤
      ∑ A ∈ (range K).powerset, U A := by
    have he : ∑' n : ℕ, (det K n : ℝ) * pw x n - ∑' n, pw x n =
        ∑ A ∈ (range K).powerset,
          ((-1 : ℝ) ^ A.card * ∑' n : ℕ, (jacobiSym (discProd A) n : ℝ) * pw x n -
            (if A = ∅ then ∑' n, pw x n else 0)) := by
      rw [sum_sub_distrib, sum_ite_eq' _ _ _, ite_eq_left (empty_mem_powerset _),
        tsum_det_pw K hx.1]
    rw [he]
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
  have h2 := hC0 x hx
  calc |∑' n : ℕ, (det K n : ℝ) * pw x n - 1 / (x - 1)|
      = |(∑' n : ℕ, (det K n : ℝ) * pw x n - ∑' n, pw x n) +
          (∑' n, pw x n - 1 / (x - 1))| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1 h2)

/-- The detector series and `2^K` times the series over `nonresSet K` differ by `O_K(1)`:
    they differ only at the primes dividing `Δ_0 ⋯ Δ_{K−1}`. -/
theorem det_error (K : ℕ) : ∃ B : ℝ, ∀ x : ℝ, 1 < x →
    |∑' n : ℕ, (det K n : ℝ) * pw x n -
      (2 : ℝ) ^ K * ∑' n, (nonresSet K).indicator (pw x) n| ≤ B := by
  classical
  set P : ℕ := ∏ k ∈ range K, (discZ k).natAbs with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ =>
    Int.natAbs_ne_zero.mpr (ne_zero_of_not_isSquare (not_isSquare_discZ k))
  set E : ℕ → ℝ := fun n => if n ∈ P.primeFactors then (2 : ℝ) ^ K * Real.log n else 0 with hE
  have hE0 : ∀ n, 0 ≤ E n := fun n => by
    simp only [hE]
    split_ifs
    · exact mul_nonneg (by positivity) (Real.log_natCast_nonneg n)
    · exact le_rfl
  have hEs : Summable E :=
    summable_of_ne_finset_zero (s := P.primeFactors) fun n hn => ite_eq_right hn
  refine ⟨∑' n, E n, fun x hx => ?_⟩
  rw [← tsum_mul_left, ← Summable.tsum_sub (summable_det_pw K hx)
    (((summable_pw hx).indicator _).mul_left _), ← Real.norm_eq_abs]
  refine tsum_of_norm_bounded hEs.hasSum fun n => ?_
  rw [Real.norm_eq_abs]
  by_cases hn : n ∈ nonresSet K
  · rw [Set.indicator_of_mem hn, det_of_mem hn]
    push_cast
    rw [sub_self, abs_zero]
    exact hE0 n
  · rw [Set.indicator_of_notMem hn, mul_zero, sub_zero]
    by_cases hp : n.Prime
    · rcases det_eq_zero_or_dvd hp hn with h0 | hdvd
      · rw [h0, Int.cast_zero, zero_mul, abs_zero]
        exact hE0 n
      · have hEn : E n = (2 : ℝ) ^ K * Real.log n := by
          simp only [hE]
          rw [ite_eq_left (Nat.mem_primeFactors.mpr ⟨hp, hdvd, hP0⟩)]
        have hd0 : (0 : ℝ) ≤ det K n := by exact_mod_cast det_nonneg K n
        have hd1 : (det K n : ℝ) ≤ 2 ^ K := by exact_mod_cast det_le K n
        rw [hEn, abs_of_nonneg (mul_nonneg hd0 (pw_nonneg x n))]
        exact mul_le_mul hd1 (pw_le_log hx.le n) (pw_nonneg x n) (by positivity)
    · rw [pw_of_not_prime x hp, mul_zero, abs_zero]
      exact hE0 n

/-- The two sets differ at most at the prime `2`, so the two series differ by `O(1)`. -/
theorem survive_error (K : ℕ) {x : ℝ} (hx : 1 < x) :
    |∑' n, (surviveSet K).indicator (pw x) n - ∑' n, (nonresSet K).indicator (pw x) n| ≤
      Real.log 2 := by
  set E : ℕ → ℝ := fun n => if n = 2 then Real.log 2 else 0 with hE
  have hEs : HasSum E (Real.log 2) := by
    have := hasSum_ite_eq (2 : ℕ) (Real.log 2)
    exact this
  rw [← Summable.tsum_sub ((summable_pw hx).indicator _) ((summable_pw hx).indicator _),
    ← Real.norm_eq_abs]
  refine tsum_of_norm_bounded hEs fun n => ?_
  rw [Real.norm_eq_abs]
  simp only [hE]
  by_cases hn2 : n = 2
  · rw [ite_eq_left hn2]
    have ha0 : 0 ≤ (surviveSet K).indicator (pw x) n :=
      Set.indicator_nonneg (fun n _ => pw_nonneg x n) n
    have hb0 : 0 ≤ (nonresSet K).indicator (pw x) n :=
      Set.indicator_nonneg (fun n _ => pw_nonneg x n) n
    have ha1 : (surviveSet K).indicator (pw x) n ≤ pw x n :=
      Set.indicator_le_self' (fun n _ => pw_nonneg x n) n
    have hb1 : (nonresSet K).indicator (pw x) n ≤ pw x n :=
      Set.indicator_le_self' (fun n _ => pw_nonneg x n) n
    have hl : pw x n ≤ Real.log 2 := by
      have := pw_le_log hx.le n
      rw [hn2] at this ⊢
      exact_mod_cast this
    rw [abs_le]
    constructor <;> linarith
  · rw [ite_eq_right hn2]
    have : (surviveSet K).indicator (pw x) n = (nonresSet K).indicator (pw x) n := by
      by_cases h : n ∈ nonresSet K
      · rw [Set.indicator_of_mem h,
          Set.indicator_of_mem ((mem_surviveSet_iff_of_ne_two hn2 K).mpr h)]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem fun h' => h ((mem_surviveSet_iff_of_ne_two hn2 K).mp h')]
    rw [this, sub_self, abs_zero]

/-! ## 4. The density -/

/-- `|(x−1) ∑_{p survives to K} log p · p^{−x} − 1/2^K| ≤ (x−1) C` on `(1, 2]`. -/
theorem survive_bound (K : ℕ) : ∃ C : ℝ, ∀ x : ℝ, x ∈ Set.Ioc (1 : ℝ) 2 →
    |(x - 1) * ∑' n, (surviveSet K).indicator (pw x) n - 1 / 2 ^ K| ≤ (x - 1) * C := by
  obtain ⟨R, hR⟩ := det_bound K
  obtain ⟨B, hB⟩ := det_error K
  refine ⟨Real.log 2 + (B + R), fun x hx => ?_⟩
  have hx0 : 0 < x - 1 := sub_pos.mpr hx.1
  have h1 := survive_error K hx.1
  have h2 := hB x hx.1
  have h3 := hR x hx
  set S' := ∑' n, (surviveSet K).indicator (pw x) n
  set S := ∑' n, (nonresSet K).indicator (pw x) n
  set T := ∑' n : ℕ, (det K n : ℝ) * pw x n
  have h2K : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
  have h4 : |(2 : ℝ) ^ K * S - 1 / (x - 1)| ≤ B + R := by
    have : (2 : ℝ) ^ K * S - 1 / (x - 1) = -(T - 2 ^ K * S) + (T - 1 / (x - 1)) := by ring
    rw [this]
    exact (abs_add_le _ _).trans (add_le_add (by rwa [abs_neg]) h3)
  have hBR : 0 ≤ B + R := (abs_nonneg _).trans h4
  have he : (x - 1) * S' - 1 / 2 ^ K =
      (x - 1) * (S' - S) + (x - 1) / 2 ^ K * (2 ^ K * S - 1 / (x - 1)) := by
    field_simp
    ring
  rw [he]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos hx0, abs_of_pos (div_pos hx0 (by positivity)), mul_add]
  refine add_le_add (mul_le_mul_of_nonneg_left h1 hx0.le) ?_
  calc (x - 1) / 2 ^ K * |(2 : ℝ) ^ K * S - 1 / (x - 1)|
      ≤ (x - 1) / 2 ^ K * (B + R) := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ ≤ (x - 1) * (B + R) :=
        mul_le_mul_of_nonneg_right (div_le_self hx0.le h2K) hBR

theorem tendsto_survive_pw (K : ℕ) :
    Tendsto (fun x : ℝ => (x - 1) * ∑' n, (surviveSet K).indicator (pw x) n) (𝓝[>] 1)
      (𝓝 (1 / 2 ^ K)) := by
  obtain ⟨C, hC⟩ := survive_bound K
  have hlo : Tendsto (fun x : ℝ => 1 / 2 ^ K - (x - 1) * C) (𝓝[>] 1)
      (𝓝 (1 / 2 ^ K - ((1 : ℝ) - 1) * C)) :=
    (Continuous.tendsto (by fun_prop) 1).mono_left nhdsWithin_le_nhds
  have hhi : Tendsto (fun x : ℝ => 1 / 2 ^ K + (x - 1) * C) (𝓝[>] 1)
      (𝓝 (1 / 2 ^ K + ((1 : ℝ) - 1) * C)) :=
    (Continuous.tendsto (by fun_prop) 1).mono_left nhdsWithin_le_nhds
  rw [show (1 : ℝ) / 2 ^ K - ((1 : ℝ) - 1) * C = 1 / 2 ^ K by ring] at hlo
  rw [show (1 : ℝ) / 2 ^ K + ((1 : ℝ) - 1) * C = 1 / 2 ^ K by ring] at hhi
  have hev : ∀ᶠ x : ℝ in 𝓝[>] 1,
      1 / 2 ^ K - (x - 1) * C ≤ (x - 1) * ∑' n, (surviveSet K).indicator (pw x) n ∧
      (x - 1) * ∑' n, (surviveSet K).indicator (pw x) n ≤ 1 / 2 ^ K + (x - 1) * C := by
    filter_upwards [Ioc_mem_nhdsGT one_lt_two] with x hx
    have h := abs_le.mp (hC x hx)
    constructor <;> linarith [h.1, h.2]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi (hev.mono fun _ h => h.1)
    (hev.mono fun _ h => h.2)

theorem indicator_surviveSet_eq (K : ℕ) (x : ℝ) :
    (surviveSet K).indicator (fun p : ℕ => Real.log p * (p : ℝ) ^ (-x)) =
      (surviveSet K).indicator (pw x) :=
  Set.indicator_congr fun _ hp => (pw_of_prime x hp.1).symm

/-- **The primes whose tower is irreducible through level `K` have analytic density `1/2^K`.**
    `(s − 1) ∑_p log p · p^{−s} → 1/2^K` as `s → 1⁺`, the sum over those primes; with no
    hypothesis. -/
theorem survive_analytic_density (K : ℕ) :
    Tendsto (fun s : ℝ => (s - 1) *
        ∑' p : ℕ, (surviveSet K).indicator (fun p : ℕ => Real.log p * (p : ℝ) ^ (-s)) p)
      (𝓝[>] 1) (𝓝 (1 / 2 ^ K)) := by
  refine (tendsto_survive_pw K).congr fun x => ?_
  rw [indicator_surviveSet_eq]

/-- **The exit level.** The primes whose tower is irreducible through level `K` and not through
    level `K + 1` (first reducible level exactly `K + 1`) have analytic density `1/2^(K+1)`. -/
theorem exit_analytic_density (K : ℕ) :
    Tendsto (fun s : ℝ => (s - 1) *
        ∑' p : ℕ, (surviveSet K \ surviveSet (K + 1)).indicator
          (fun p : ℕ => Real.log p * (p : ℝ) ^ (-s)) p)
      (𝓝[>] 1) (𝓝 (1 / 2 ^ (K + 1))) := by
  have h := (survive_analytic_density K).sub (survive_analytic_density (K + 1))
  rw [show (1 : ℝ) / 2 ^ K - 1 / 2 ^ (K + 1) = 1 / 2 ^ (K + 1) by rw [pow_succ]; field_simp; ring]
    at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
  rw [Set.indicator_sdiff (surviveSet_antitone (Nat.le_succ K)), ← mul_sub]
  congr 1
  simp only [indicator_surviveSet_eq, Pi.sub_apply]
  exact (Summable.tsum_sub ((summable_pw hx).indicator _) ((summable_pw hx).indicator _)).symm

end ExitLevel

end FunctionFieldAnalog
