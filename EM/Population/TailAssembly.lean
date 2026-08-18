import EM.Population.TailEstimate

/-!
# The quantitative tail estimate for `(LS+)`

**Scope (honest).**  This is a **population** statement about the seed ensemble
`sampleSpace q Y = [1, M_Y]` of the `q`-free dynamics.  Nothing is claimed about
the actual Euler–Mullin orbit.

Under the policy `n²/2 ≤ log Y ≤ n³` the *degenerate-prefix tail* of
`LSPlus.ls_plus` — the seeds whose first `n` `q`-free multipliers are degenerate
(`p̃_j = 1`) or exceed the truncation `Y` — has density `O(log n / n)`:

```
#{m ∈ [1, M_Y] : ¬ ∀ j < n, 2 ≤ p̃_j(m) ≤ Y}  ≤  e²⁵ · (log n / n) · M_Y.
```

The proof is the four-step scheme of Group 7:

* **first failure** (`survives_of_type_failure`, `tail_subset`): at the *first*
  index `k < n` where the type condition fails, the prefix is still
  nondegenerate and `Y`-bounded, and the seed **survives** the whole band up to
  `Y` — both failure modes (`p̃_k = 1`, i.e. the Euclid number is a `q`-power,
  and `p̃_k > Y`) say precisely that no prime `≤ Y` other than `q` divides the
  current Euclid number.  So the tail is covered by the `n` survival events.
* **divisor-mass exclusion** (`markov_mass`): at most `M_Y / z` seeds carry a
  window-divisor mass `≥ 1` in the window `(z, Y]`, `z = n⁶` (TL3).
* **per-seed survival** (`active_window_lower`, `survival_small`): off that
  exceptional set the active window of the box process retains all but `O(1)` of
  the Mertens mass of `(z, Y]`, so the survival product is at most
  `e²⁴ · log n / n²`.
* **assembly** (`cell_bound`, `tail_small`): the survival event is *exactly*
  cell-proportional by `SelectionLaw.selection_law`, and the type cells are the
  fibers of `LSPlus.typeData`, so the fibrewise bound sums to `M_Y`.

Group 7 / **C4 tail estimate**; `findings_ls_verification.md` §2.10 and §4
Group 7.  Session 311.
-/

noncomputable section
open Classical

namespace TailAssembly

open SeedCapture SeedTypes LargeStepRoughness SelectionLaw LSPlus TailEstimate

/-! ## Part 1 — the first-failure lemma -/

/-- **The type failure is a survival event.**  If the `k`-th `q`-free multiplier
is degenerate (`= 1`, i.e. the Euclid number is a power of `q`) or exceeds the
truncation `Y`, then *no* prime `≤ Y` other than `q` divides the current Euclid
number.

Both failure modes collapse to the same statement: `p̃_k` is the least prime
factor of the `q`-free part, so any prime `r ≤ Y`, `r ≠ q` dividing the Euclid
number would force `2 ≤ p̃_k ≤ r ≤ Y`.

Group 7 / C4; Session 311. -/
theorem survives_of_type_failure {q Y k m : ℕ} (hq : q.Prime)
    (h : ¬ (2 ≤ genSeqAvoid q m k ∧ genSeqAvoid q m k ≤ Y)) :
    SurvivesUpTo q Y k m := by
  intro r hr hry hrq hdvd
  have hNne : genProdAvoid q m k + 1 ≠ 0 := Nat.succ_ne_zero _
  have hgs : genSeqAvoid q m k = (qfreePart q (genProdAvoid q m k + 1)).minFac := rfl
  have hle : (qfreePart q (genProdAvoid q m k + 1)).minFac ≤ r :=
    minFac_qfreePart_least hq hNne hr hrq hdvd
  have hrd : r ∣ qfreePart q (genProdAvoid q m k + 1) :=
    (prime_dvd_qfreePart_iff hq hr hrq hNne).mpr hdvd
  have hne1 : qfreePart q (genProdAvoid q m k + 1) ≠ 1 := by
    intro hcon
    rw [hcon] at hrd
    exact hr.one_lt.ne' (Nat.dvd_one.mp hrd)
  exact h ⟨by rw [hgs]; exact (Nat.minFac_prime hne1).two_le,
    by rw [hgs]; exact le_trans hle hry⟩

/-! ## Part 2 — the window divisor mass -/

/-- The **window divisor mass** of a seed: the reciprocal sum of the primes in
`(z, Y]` dividing `m`.  This is the quantity controlled in the mean by TL3. -/
def divisorMass (z Y m : ℕ) : ℝ :=
  ∑ r ∈ ((Finset.Ioc z Y).filter Nat.Prime).filter (fun r => r ∣ m), (1 : ℝ) / r

/-- **Markov, on the sample space.**  At most `M_Y / z` seeds of the period carry
a window divisor mass of at least `1`.  (TL3 restated on `sampleSpace`.) -/
theorem markov_mass (q Y z : ℕ) (hz : 1 ≤ z) :
    (((sampleSpace q Y).filter (fun m => (1 : ℝ) ≤ divisorMass z Y m)).card : ℝ)
      ≤ (modulus q Y : ℝ) / (z : ℝ) := by
  have h := markov_divisor_mass z Y (modulus q Y) hz (δ := 1) one_pos
  rw [mul_one] at h
  simpa [sampleSpace, divisorMass] using h

/-! ## Part 3 — the active window keeps almost all of the Mertens mass -/

/-- **The active-window deficit.**  The active window `(z, y]` of the box process
loses, relative to the full prime window, at most the window divisor mass of the
seed plus `(1 + k + k²(log₂ Y + 1))/z` — one term for the avoided prime `q`, `k`
terms for the earlier multipliers, and TL1 for the old positions.

Group 7 / C4; Session 311. -/
theorem active_window_lower {q m z Y k : ℕ} (hz : 1 ≤ z)
    (hnd : ∀ i < k, 2 ≤ genSeqAvoid q m i) (hYb : ∀ i < k, genSeqAvoid q m i ≤ Y) :
    (∑ r ∈ (Finset.Ioc z Y).filter Nat.Prime, (1 : ℝ) / r)
        - divisorMass z Y m
        - ((1 + k + k * (k * (Nat.log 2 Y + 1)) : ℕ) : ℝ) / (z : ℝ)
      ≤ ∑ r ∈ activeWindow q m z Y k, (1 : ℝ) / r := by
  set W := (Finset.Ioc z Y).filter Nat.Prime with hW
  set A := activeWindow q m z Y k with hA
  have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
  have hAW : A ⊆ W := by
    intro r hr
    obtain ⟨hzr, hry, hrp, -, -, -⟩ := mem_activeWindow hr
    rw [hW, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hzr, hry⟩, hrp⟩
  have hsplit : (∑ r ∈ W \ A, (1 : ℝ) / r) + (∑ r ∈ A, (1 : ℝ) / r) = ∑ r ∈ W, (1 : ℝ) / r :=
    Finset.sum_sdiff hAW
  have hdiv : (∑ r ∈ (W \ A).filter (fun r => r ∣ m), (1 : ℝ) / r)
      + (∑ r ∈ (W \ A).filter (fun r => ¬ r ∣ m), (1 : ℝ) / r) = ∑ r ∈ W \ A, (1 : ℝ) / r :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  -- (i) the divisor part is at most the window divisor mass
  have hd1 : (∑ r ∈ (W \ A).filter (fun r => r ∣ m), (1 : ℝ) / r) ≤ divisorMass z Y m := by
    rw [divisorMass, ← hW]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
    intro r hr
    rw [Finset.mem_filter] at hr ⊢
    exact ⟨(Finset.mem_sdiff.mp hr.1).1, hr.2⟩
  -- (ii) the remaining primes are few
  have hRsub : (W \ A).filter (fun r => ¬ r ∣ m)
      ⊆ (insert q ((Finset.range k).image (fun j => genSeqAvoid q m j)))
          ∪ oldSet q m (Y + 1) k := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_sdiff] at hr
    obtain ⟨⟨hrW, hrA⟩, hrm⟩ := hr
    rw [hW, Finset.mem_filter, Finset.mem_Ioc] at hrW
    obtain ⟨⟨hzr, hrY⟩, hrp⟩ := hrW
    by_cases hrq : r = q
    · exact Finset.mem_union_left _ (Finset.mem_insert.mpr (Or.inl hrq))
    by_cases hbag : inBag q m r k
    · rcases hbag with hd | ⟨j, hj, hje⟩
      · exact absurd hd hrm
      · exact Finset.mem_union_left _ (Finset.mem_insert.mpr (Or.inr
          (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, hje⟩)))
    by_cases hnew : isNew q m r k
    · exact absurd (by
        rw [hA, activeWindow, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨hzr, hrY⟩, hrp, hrq, hbag, hnew⟩) hrA
    · refine Finset.mem_union_right _ ?_
      rw [oldSet, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hrp, hnew⟩
  have hRcard : ((W \ A).filter (fun r => ¬ r ∣ m)).card
      ≤ 1 + k + k * (k * (Nat.log 2 Y + 1)) := by
    refine le_trans (Finset.card_le_card hRsub) (le_trans (Finset.card_union_le _ _) ?_)
    have h1 : (insert q ((Finset.range k).image (fun j => genSeqAvoid q m j))).card ≤ 1 + k := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      have h := Finset.card_image_le (s := Finset.range k) (f := fun j => genSeqAvoid q m j)
      rw [Finset.card_range] at h
      omega
    have h2 := old_count_le_log hnd hYb (Y + 1)
    omega
  have hd2 : (∑ r ∈ (W \ A).filter (fun r => ¬ r ∣ m), (1 : ℝ) / r)
      ≤ ((1 + k + k * (k * (Nat.log 2 Y + 1)) : ℕ) : ℝ) / (z : ℝ) := by
    have hbd : ∀ r ∈ (W \ A).filter (fun r => ¬ r ∣ m), (1 : ℝ) / r ≤ 1 / (z : ℝ) := by
      intro r hr
      rw [Finset.mem_filter, Finset.mem_sdiff, hW, Finset.mem_filter, Finset.mem_Ioc] at hr
      have hzr : z < r := hr.1.1.1.1
      have hzrR : (z : ℝ) ≤ (r : ℝ) := by exact_mod_cast hzr.le
      exact one_div_le_one_div_of_le hzR hzrR
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hbd) ?_
    have hc : ((((W \ A).filter (fun r => ¬ r ∣ m)).card : ℕ) : ℝ)
        ≤ ((1 + k + k * (k * (Nat.log 2 Y + 1)) : ℕ) : ℝ) := by exact_mod_cast hRcard
    rw [nsmul_eq_mul, mul_one_div, div_le_div_iff₀ hzR hzR]
    exact mul_le_mul_of_nonneg_right hc hzR.le
  linarith

/-! ## Part 4 — the per-seed survival bound -/

/-- **The per-seed survival bound.**  On a seed with a nondegenerate,
`Y`-bounded prefix and window divisor mass at most `1`, the survival product of
the whole band `≤ Y` at step `k < n` is at most `e²⁴ · log n / n²`, under the
policy `n²/2 ≤ log Y ≤ n³`.

The numerics: with `z = n⁶`, Mertens gives `log log Y − log log z − 16 ≥
2 log n − log log n − 21` for the full window, the divisor mass costs `1`, and
the `1 + k + k²(log₂ Y + 1) ≤ n⁶` excluded primes cost at most `1`.

Group 7 / C4; Session 311. -/
theorem survival_small {q m Y k n : ℕ} (hq : q.Prime) (hm : 1 ≤ m) (hn : 16 ≤ n)
    (hnd : ∀ i < k, 2 ≤ genSeqAvoid q m i) (hYb : ∀ i < k, genSeqAvoid q m i ≤ Y)
    (hkn : k < n) (hlow : ((n : ℝ)) ^ 2 / 2 ≤ Real.log Y) (hhigh : Real.log Y ≤ ((n : ℝ)) ^ 3)
    (hmass : divisorMass (n ^ 6) Y m ≤ 1) :
    survival q m Y k ≤ Real.exp 24 * Real.log n / ((n : ℝ)) ^ 2 := by
  have hnR : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn : (0 : ℝ) < Real.log n := Real.log_pos (by linarith)
  -- `Y` is large
  have hY2 : 2 ≤ Y := by
    by_contra hcon
    have hYR : (Y : ℝ) ≤ 1 := by exact_mod_cast (by omega : Y ≤ 1)
    have hlY : Real.log Y ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) hYR
    nlinarith
  set z := n ^ 6 with hzdef
  have hz16 : 16 ≤ z := le_trans hn (Nat.le_self_pow (by norm_num) n)
  have hzc : ((z : ℕ) : ℝ) = (n : ℝ) ^ 6 := by rw [hzdef]; push_cast; ring
  have hlogz : Real.log ((z : ℕ) : ℝ) = 6 * Real.log n := by
    rw [hzc, Real.log_pow]; norm_num
  have hzYlog : Real.log ((z : ℕ) : ℝ) ≤ Real.log Y := by
    rw [hlogz]
    have hls := Real.log_le_sub_one_of_pos hn0
    nlinarith [sq_nonneg ((n : ℝ) - 12)]
  have hzY : z ≤ Y := by
    by_contra hcon
    have hYz : (Y : ℝ) < ((z : ℕ) : ℝ) := by exact_mod_cast (by omega : Y < z)
    have hYpos : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast (by omega : 0 < Y)
    have := Real.log_lt_log hYpos hYz
    linarith
  -- the binary logarithm of `Y`
  have hL : ((Nat.log 2 Y : ℕ) : ℝ) ≤ 2 * (n : ℝ) ^ 3 := by
    have hpow : 2 ^ Nat.log 2 Y ≤ Y := Nat.pow_log_le_self 2 (by omega)
    have hpowR : ((2 : ℝ)) ^ (Nat.log 2 Y) ≤ (Y : ℝ) := by exact_mod_cast hpow
    have h1 : Real.log ((2 : ℝ) ^ (Nat.log 2 Y)) ≤ Real.log Y :=
      Real.log_le_log (by positivity) hpowR
    rw [Real.log_pow] at h1
    have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hL0 : (0 : ℝ) ≤ ((Nat.log 2 Y : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hL0 (le_of_lt (by linarith : (0 : ℝ) < Real.log 2 - 1 / 2))]
  have hLn : Nat.log 2 Y ≤ 2 * n ^ 3 := by
    have h : ((Nat.log 2 Y : ℕ) : ℝ) ≤ ((2 * n ^ 3 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h
  -- the excluded-prime count is at most `z`
  have hcount : 1 + k + k * (k * (Nat.log 2 Y + 1)) ≤ z := by
    have hk : k ≤ n := hkn.le
    have hn3 : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ (by omega)
    have h3 : Nat.log 2 Y + 1 ≤ 3 * n ^ 3 := by linarith
    have e1 : k * (k * (Nat.log 2 Y + 1)) ≤ n * (n * (3 * n ^ 3)) :=
      Nat.mul_le_mul hk (Nat.mul_le_mul hk h3)
    have e2 : n * (n * (3 * n ^ 3)) = 3 * n ^ 5 := by ring
    have hn5 : n ≤ n ^ 5 := Nat.le_self_pow (by norm_num) n
    have hn51 : 1 ≤ n ^ 5 := Nat.one_le_pow _ _ (by omega)
    have hz5 : 16 * n ^ 5 ≤ n * n ^ 5 := Nat.mul_le_mul_right _ hn
    have hz6 : n * n ^ 5 = z := by rw [hzdef]; ring
    linarith
  have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hcountR : ((1 + k + k * (k * (Nat.log 2 Y + 1)) : ℕ) : ℝ) / (z : ℝ) ≤ 1 := by
    rw [div_le_one hzR]
    exact_mod_cast hcount
  -- the Mertens window
  have hwin := MertensLower.window_recip_lower z Y hz16 hzY
  have hactive := active_window_lower (z := z) (Y := Y) (m := m) (q := q) (by omega) hnd hYb
  have hll1 : 2 * Real.log n - 1 ≤ Real.log (Real.log Y) := by
    have h1 : Real.log ((n : ℝ) ^ 2 / 2) ≤ Real.log (Real.log Y) :=
      Real.log_le_log (by positivity) hlow
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at h1
    push_cast at h1
    have hl2 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hll2 : Real.log (Real.log ((z : ℕ) : ℝ)) ≤ 5 + Real.log (Real.log n) := by
    rw [hlogz, Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) (ne_of_gt hlogn)]
    have h6 : Real.log 6 ≤ 5 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
      linarith
    linarith
  have hE : 2 * Real.log n - Real.log (Real.log n) - 24
      ≤ ∑ r ∈ activeWindow q m z Y k, (1 : ℝ) / r := by linarith
  have hsurv := survival_le_of_active_lower hq hm hnd z Y
    (2 * Real.log n - Real.log (Real.log n) - 24) hE
  have hexp : Real.exp (-(2 * Real.log n - Real.log (Real.log n) - 24))
      = Real.exp 24 * Real.log n / (n : ℝ) ^ 2 := by
    have h1 : Real.exp (Real.log (Real.log n)) = Real.log n := Real.exp_log hlogn
    have h2 : Real.exp (2 * Real.log n) = (n : ℝ) ^ 2 := by
      rw [two_mul, Real.exp_add, Real.exp_log hn0]; ring
    rw [show -(2 * Real.log n - Real.log (Real.log n) - 24)
          = 24 + Real.log (Real.log n) - 2 * Real.log n by ring,
      Real.exp_sub, Real.exp_add, h1, h2]
  linarith [hsurv, hexp.ge, hexp.le]

/-! ## Part 5 — the fibrewise assembly -/

/-- The sample space is one full period. -/
theorem card_sampleSpace (q Y : ℕ) : (sampleSpace q Y).card = modulus q Y := by
  rw [sampleSpace, Nat.card_Ico]
  omega

/-- **The level-`k` survival bound.**  The seeds with a good `k`-prefix, a small
window divisor mass, and a surviving `k`-th Euclid number form at most an
`e²⁴ log n / n²` fraction of the period.

*Proof.*  Fibre over the type `typeData q Y k`.  On a nonempty fibre pick a
representative `m₀`: the fibre is contained in the survival-filtered type cell of
`m₀`, whose cardinality is *exactly* `survival q m₀ Y k · |cell|`
(`SelectionLaw.selection_law`), and `survival q m₀ Y k ≤ e²⁴ log n / n²`
(`survival_small`).  Since the cells are the fibres, the bound sums to the whole
period.

Group 7 / C4; Session 311. -/
theorem cell_bound {q Y k n : ℕ} (hq : q.Prime) (hn : 16 ≤ n) (hkn : k < n)
    (hlow : ((n : ℝ)) ^ 2 / 2 ≤ Real.log Y) (hhigh : Real.log Y ≤ ((n : ℝ)) ^ 3) :
    (((sampleSpace q Y).filter (fun m =>
        (∀ j < k, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y) ∧
          SurvivesUpTo q Y k m ∧ divisorMass (n ^ 6) Y m ≤ 1)).card : ℝ)
      ≤ Real.exp 24 * Real.log n / ((n : ℝ)) ^ 2 * ((sampleSpace q Y).card : ℝ) := by
  have hnR : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by linarith)
  have hεnn : (0 : ℝ) ≤ Real.exp 24 * Real.log n / ((n : ℝ)) ^ 2 := by positivity
  set G := (sampleSpace q Y).filter (fun m =>
      (∀ j < k, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y) ∧
        SurvivesUpTo q Y k m ∧ divisorMass (n ^ 6) Y m ≤ 1) with hG
  set T := (sampleSpace q Y).image (typeData q Y k) with hT
  have hGsub : G ⊆ sampleSpace q Y := by rw [hG]; exact Finset.filter_subset _ _
  have hGfib : G.card = ∑ b ∈ T, (G.filter (fun m => typeData q Y k m = b)).card :=
    Finset.card_eq_sum_card_fiberwise (fun m hm => by
      rw [hT]; exact Finset.mem_image_of_mem _ (hGsub hm))
  have hSfib : (sampleSpace q Y).card
      = ∑ b ∈ T, ((sampleSpace q Y).filter (fun m => typeData q Y k m = b)).card :=
    Finset.card_eq_sum_card_fiberwise (fun m hm => by
      rw [hT]; exact Finset.mem_image_of_mem _ hm)
  have hterm : ∀ b ∈ T, ((G.filter (fun m => typeData q Y k m = b)).card : ℝ)
      ≤ Real.exp 24 * Real.log n / ((n : ℝ)) ^ 2
          * (((sampleSpace q Y).filter (fun m => typeData q Y k m = b)).card : ℝ) := by
    intro b _
    rcases Finset.eq_empty_or_nonempty (G.filter (fun m => typeData q Y k m = b)) with he | hne
    · rw [he, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hεnn (Nat.cast_nonneg _)
    · obtain ⟨m₀, hm₀⟩ := hne
      obtain ⟨hm₀G, hm₀b⟩ := Finset.mem_filter.mp hm₀
      subst hm₀b
      have hm₀G' := hm₀G
      rw [hG, Finset.mem_filter] at hm₀G'
      obtain ⟨hm₀S, hnd, hsurvm₀, hmass⟩ := hm₀G'
      have hm₀1 : 1 ≤ m₀ := (mem_sampleSpace.mp hm₀S).1
      have hsubset : G.filter (fun m => typeData q Y k m = typeData q Y k m₀)
          ⊆ (stepCell q Y k m₀).filter (fun m => SurvivesUpTo q Y k m) := by
        intro m hm
        rw [Finset.mem_filter] at hm
        obtain ⟨hmG, hmb⟩ := hm
        have hmG' := hmG
        rw [hG, Finset.mem_filter] at hmG'
        refine Finset.mem_filter.mpr ⟨?_, hmG'.2.2.1⟩
        rw [← fiber_eq_stepCell q Y k m₀]
        exact Finset.mem_filter.mpr ⟨hmG'.1, hmb⟩
      have hsel := selection_law (q := q) (Y := Y) (y := Y) (n := k) (m₀ := m₀)
        hq hm₀1 hnd le_rfl
      have hsmall : survival q m₀ Y k ≤ Real.exp 24 * Real.log n / ((n : ℝ)) ^ 2 :=
        survival_small hq hm₀1 hn (fun i hi => (hnd i hi).1) (fun i hi => (hnd i hi).2)
          hkn hlow hhigh hmass
      rw [fiber_eq_stepCell]
      calc ((G.filter (fun m => typeData q Y k m = typeData q Y k m₀)).card : ℝ)
          ≤ (((stepCell q Y k m₀).filter (fun m => SurvivesUpTo q Y k m)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsubset
        _ = survival q m₀ Y k * ((stepCell q Y k m₀).card : ℝ) := hsel
        _ ≤ Real.exp 24 * Real.log n / ((n : ℝ)) ^ 2 * ((stepCell q Y k m₀).card : ℝ) :=
            mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg _)
  rw [hGfib, hSfib]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum hterm

/-! ## Part 6 — the tail estimate -/

/-- **C4 — the quantitative tail estimate.**  Under the policy
`n²/2 ≤ log Y ≤ n³`, the seeds of the period whose first `n` `q`-free multipliers
are not all nondegenerate and `≤ Y` form at most an `e²⁵ log n / n` fraction.

Group 7 / C4, `findings_ls_verification.md` §2.10; Session 311. -/
theorem tail_small : ∃ n₀ : ℕ, ∀ q Y n : ℕ, q.Prime → n₀ ≤ n →
    ((n : ℝ)) ^ 2 / 2 ≤ Real.log Y → Real.log Y ≤ ((n : ℝ)) ^ 3 →
    (((sampleSpace q Y).filter (fun m =>
        ¬ (∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y))).card : ℝ)
      ≤ Real.exp 25 * Real.log n / (n : ℝ) * ((sampleSpace q Y).card : ℝ) := by
  refine ⟨16, fun q Y n hq hn hlow hhigh => ?_⟩
  have hnR : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog16 : (2 : ℝ) ≤ Real.log n := by
    have h1 : Real.log (16 : ℝ) ≤ Real.log n := Real.log_le_log (by norm_num) hnR
    have h2 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_gt_d9]
  set z := n ^ 6 with hzdef
  have hz1 : 1 ≤ z := Nat.one_le_pow _ _ (by omega)
  have hnz : (n : ℝ) ≤ (z : ℝ) := by
    have : n ≤ z := le_trans (Nat.le_self_pow (by norm_num) n) (le_of_eq hzdef.symm)
    exact_mod_cast this
  have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  set G : ℕ → Finset ℕ := fun k => (sampleSpace q Y).filter (fun m =>
      (∀ j < k, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y) ∧
        SurvivesUpTo q Y k m ∧ divisorMass z Y m ≤ 1) with hG
  set E := (sampleSpace q Y).filter (fun m => (1 : ℝ) ≤ divisorMass z Y m) with hE
  -- (i) the tail is covered by the exceptional set and the `n` survival events
  have hsub : (sampleSpace q Y).filter (fun m =>
        ¬ (∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y))
      ⊆ E ∪ (Finset.range n).biUnion G := by
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨hmS, hbad⟩ := hm
    by_cases hmass : (1 : ℝ) ≤ divisorMass z Y m
    · exact Finset.mem_union_left _ (by rw [hE]; exact Finset.mem_filter.mpr ⟨hmS, hmass⟩)
    · refine Finset.mem_union_right _ ?_
      have hex : ∃ j, j < n ∧ ¬ (2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y) := by
        by_contra hcon
        exact hbad (fun j hj => not_not.mp (fun hp => hcon ⟨j, hj, hp⟩))
      have hspec := Nat.find_spec hex
      have hmin : ∀ j < Nat.find hex,
          ¬ (j < n ∧ ¬ (2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y)) :=
        fun j hj => Nat.find_min hex hj
      refine Finset.mem_biUnion.mpr ⟨Nat.find hex, Finset.mem_range.mpr hspec.1, ?_⟩
      rw [hG]
      refine Finset.mem_filter.mpr ⟨hmS, ?_, ?_, ?_⟩
      · intro j hj
        exact not_not.mp (fun hp => hmin j hj ⟨by omega, hp⟩)
      · exact survives_of_type_failure hq hspec.2
      · linarith [not_le.mp hmass]
  -- (ii) cardinalities
  have hcard0 := Finset.card_le_card hsub
  have hcard1 : (E ∪ (Finset.range n).biUnion G).card
      ≤ E.card + ∑ k ∈ Finset.range n, (G k).card :=
    le_trans (Finset.card_union_le _ _)
      (Nat.add_le_add_left (Finset.card_biUnion_le) _)
  have hcardR : (((sampleSpace q Y).filter (fun m =>
        ¬ (∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y))).card : ℝ)
      ≤ (E.card : ℝ) + ∑ k ∈ Finset.range n, ((G k).card : ℝ) := by
    have h : (((sampleSpace q Y).filter (fun m =>
        ¬ (∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y))).card : ℝ)
        ≤ ((E.card + ∑ k ∈ Finset.range n, (G k).card : ℕ) : ℝ) := by
      exact_mod_cast le_trans hcard0 hcard1
    push_cast at h
    exact h
  -- (iii) the exceptional set
  have hM : ((sampleSpace q Y).card : ℝ) = (modulus q Y : ℝ) := by
    rw [card_sampleSpace]
  have hMnn : (0 : ℝ) ≤ ((sampleSpace q Y).card : ℝ) := Nat.cast_nonneg _
  have hEbd : (E.card : ℝ) ≤ Real.log n / (n : ℝ) * ((sampleSpace q Y).card : ℝ) := by
    have h1 : (E.card : ℝ) ≤ (modulus q Y : ℝ) / (z : ℝ) := by
      rw [hE]; exact markov_mass q Y z hz1
    have h2 : (1 : ℝ) / (z : ℝ) ≤ Real.log n / (n : ℝ) := by
      rw [div_le_div_iff₀ hzR hn0]
      nlinarith
    have h3 : (modulus q Y : ℝ) / (z : ℝ)
        = ((sampleSpace q Y).card : ℝ) * ((1 : ℝ) / (z : ℝ)) := by
      rw [hM]; ring
    have h4 : ((sampleSpace q Y).card : ℝ) * ((1 : ℝ) / (z : ℝ))
        ≤ ((sampleSpace q Y).card : ℝ) * (Real.log n / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left h2 hMnn
    rw [h3] at h1
    linarith [h1, h4]
  -- (iv) the survival events
  have hGbd : ∀ k ∈ Finset.range n, ((G k).card : ℝ)
      ≤ Real.exp 24 * Real.log n / ((n : ℝ)) ^ 2 * ((sampleSpace q Y).card : ℝ) := by
    intro k hk
    rw [hG]
    exact cell_bound hq hn (Finset.mem_range.mp hk) hlow hhigh
  have hsum : ∑ k ∈ Finset.range n, ((G k).card : ℝ)
      ≤ (n : ℝ) * (Real.exp 24 * Real.log n / ((n : ℝ)) ^ 2 * ((sampleSpace q Y).card : ℝ)) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hGbd) ?_
    rw [Finset.card_range, nsmul_eq_mul]
  have hcollapse : (n : ℝ) * (Real.exp 24 * Real.log n / ((n : ℝ)) ^ 2
        * ((sampleSpace q Y).card : ℝ))
      = Real.exp 24 * (Real.log n / (n : ℝ)) * ((sampleSpace q Y).card : ℝ) := by
    field_simp
  -- (v) numerics
  have h25 : Real.exp 24 + 1 ≤ Real.exp 25 := by
    have h1 : Real.exp 25 = Real.exp 24 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h3 : (1 : ℝ) ≤ Real.exp 24 := by linarith [Real.add_one_le_exp (24 : ℝ)]
    nlinarith
  have hfrac : (0 : ℝ) ≤ Real.log n / (n : ℝ) := by positivity
  have hfin : Real.exp 24 * (Real.log n / (n : ℝ)) * ((sampleSpace q Y).card : ℝ)
      + Real.log n / (n : ℝ) * ((sampleSpace q Y).card : ℝ)
      ≤ Real.exp 25 * Real.log n / (n : ℝ) * ((sampleSpace q Y).card : ℝ) := by
    have hkey : (Real.exp 24 + 1) * (Real.log n / (n : ℝ)) * ((sampleSpace q Y).card : ℝ)
        ≤ Real.exp 25 * (Real.log n / (n : ℝ)) * ((sampleSpace q Y).card : ℝ) := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h25 hfrac) hMnn
    have hexp : Real.exp 25 * Real.log n / (n : ℝ) * ((sampleSpace q Y).card : ℝ)
        = Real.exp 25 * (Real.log n / (n : ℝ)) * ((sampleSpace q Y).card : ℝ) := by ring
    nlinarith [hkey, hexp.ge, hexp.le]
  linarith [hcardR, hEbd, hsum, hcollapse.ge, hcollapse.le, hfin]

/-! ## Part 7 — `(LS+)` with the tail estimated -/

/-! ## Part 7 — the policy window is nonempty -/

/-- **Non-vacuity of the policy.**  For every `n ≥ 2` there is a natural `Y`
with `n²/2 ≤ log Y ≤ n²`.  (Note that `log Y = n²` on the nose is impossible for
natural `Y`, since `e` is transcendental — hence the two-sided window.)

Witness: `Y = ⌊e^{n²}⌋`.  The upper bound is `Nat.floor_le`; the lower bound uses
`⌊r⌋ > r − 1` together with `e^{n²} − 1 ≥ e^{n²/2}`, which holds because
`t := e^{n²/2} ≥ 2` and `t² − 1 ≥ t`.

Group 7 / C4; Session 311. -/
theorem policy_satisfiable : ∀ n : ℕ, 2 ≤ n → ∃ Y : ℕ,
    ((n : ℝ)) ^ 2 / 2 ≤ Real.log Y ∧ Real.log Y ≤ ((n : ℝ)) ^ 2 := by
  intro n hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set t : ℝ := Real.exp (((n : ℝ)) ^ 2 / 2) with ht
  have ht2 : (2 : ℝ) ≤ t := by
    have h1 : (2 : ℝ) ≤ ((n : ℝ)) ^ 2 / 2 := by nlinarith
    have h2 := Real.add_one_le_exp (((n : ℝ)) ^ 2 / 2)
    rw [← ht] at h2
    linarith
  have hsq : Real.exp (((n : ℝ)) ^ 2) = t * t := by
    rw [ht, ← Real.exp_add]; ring_nf
  refine ⟨⌊Real.exp (((n : ℝ)) ^ 2)⌋₊, ?_, ?_⟩
  · -- lower bound
    have hfl : Real.exp (((n : ℝ)) ^ 2) - 1 < (⌊Real.exp (((n : ℝ)) ^ 2)⌋₊ : ℝ) :=
      Nat.sub_one_lt_floor _
    have hstep : t ≤ Real.exp (((n : ℝ)) ^ 2) - 1 := by rw [hsq]; nlinarith
    have hle : t ≤ (⌊Real.exp (((n : ℝ)) ^ 2)⌋₊ : ℝ) := by linarith
    have hlog : Real.log t ≤ Real.log (⌊Real.exp (((n : ℝ)) ^ 2)⌋₊ : ℝ) :=
      Real.log_le_log (by linarith) hle
    rwa [ht, Real.log_exp] at hlog
  · -- upper bound
    have hle : ((⌊Real.exp (((n : ℝ)) ^ 2)⌋₊ : ℕ) : ℝ) ≤ Real.exp (((n : ℝ)) ^ 2) :=
      Nat.floor_le (le_of_lt (Real.exp_pos _))
    have hpos : (0 : ℝ) < ((⌊Real.exp (((n : ℝ)) ^ 2)⌋₊ : ℕ) : ℝ) := by
      have hfl : Real.exp (((n : ℝ)) ^ 2) - 1 < (⌊Real.exp (((n : ℝ)) ^ 2)⌋₊ : ℝ) :=
        Nat.sub_one_lt_floor _
      nlinarith [hsq, ht2]
    have hlog := Real.log_le_log hpos hle
    rwa [Real.log_exp] at hlog

/-! ## Part 8 — `(LS+)` with the tail estimated -/

/-- **`(LS+)` with the tail estimated.**  The composition of `LSPlus.ls_plus`
with the tail estimate `tail_small`, in the policy window
`n²/2 ≤ log Y ≤ n²`: apart from an
`exp(−(3/8)(c₁/2)n) + e²⁵ log n / n` fraction of the period, every seed takes
at least `(c₁/8)n` large steps in its first `n` steps.

The policy window is nonempty by `policy_satisfiable`.  The threshold hypothesis
of `ls_plus` is kept as an explicit hypothesis; the policy lemma discharging it
is a separate work package.

Group 7 / C4; Session 311. -/
theorem ls_plus_with_tail :
    ∃ n₀ : ℕ, ∀ q Y Cc n : ℕ, q.Prime → 1 ≤ Cc → (Cc : ℝ) ≤ (n : ℝ) →
      ((n : ℝ)) ^ 2 / 2 ≤ Real.log Y → Real.log Y ≤ ((n : ℝ)) ^ 2 → n₀ ≤ n →
      (∀ m ∈ sampleSpace q Y,
          (∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y) →
          ∀ k < n, bigThreshold q m Cc k ≤ Y) →
      (((sampleSpace q Y).filter (fun m =>
          ((TreeChernoff.hitCount (bigStep q Cc) n m : ℝ) < c₁ / 8 * (n : ℝ)))).card : ℝ)
        ≤ ((sampleSpace q Y).card : ℝ) * Real.exp (-(3 / 8) * (c₁ / 2 * (n : ℝ)))
          + Real.exp 25 * Real.log n / (n : ℝ) * ((sampleSpace q Y).card : ℝ) := by
  obtain ⟨n₁, hls⟩ := ls_plus
  obtain ⟨n₂, htail⟩ := tail_small
  refine ⟨max (max n₁ n₂) 16, fun q Y Cc n hq hCc hCcap hpolL hpolU hn hthr => ?_⟩
  have hn1 : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : n₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn16 : 16 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn16
  have hhigh : Real.log Y ≤ ((n : ℝ)) ^ 3 := by nlinarith
  have h1 := hls q Y Cc n hq hCc hCcap hpolU hn1 hthr
  have h2 := htail q Y n hq hn2 hpolL hhigh
  linarith

end TailAssembly

end
