import EM.IK.Karamata
import EM.Population.LargeStepRoughness

/-!
# Lemma D, analytic core: reciprocal mass of a window of an arithmetic progression

This file proves the analytic heart of **Lemma D** of the seed-average programme: for a fixed
modulus `q` and a residue `a` coprime to `q`, the primes lying in the *window* `(y, y²]` and
congruent to `a` mod `q` carry reciprocal mass bounded below by a positive constant that
depends only on `q`:

```
∑_{y < p ≤ y², p prime, p ≡ a (q)} 1/p  ≥  1 / (8 φ(q))      (all large y).
```

The exponent `A = 2` in the window `(y, y^A]` is the choice recorded in
`agents/state/findings.md` (d-3); **no `O(1)` Mertens-in-AP input is used anywhere**.  The only
analytic input is the *asymptotic* weighted PNT in progressions

`IK.weightedPNTinAP_asymp_proved : IK.WeightedPNTinAPAsymp`

(proved unconditionally in `EM/IK/Karamata.lean` via Karamata's Tauberian theorem), together
with the elementary prime-power tail bound reproduced in §1 below.

## Contents

* §1 `prime_power_tail_bound` — the non-prime part of any von Mangoldt sum `∑ Λ(n)/n` is
  bounded by an absolute constant `B` (the technique is that of
  `IK.nonprime_pp_sum_bounded_by_tsum`, `EM/IK/Tauberian.lean`, which this lemma packages in
  the shape needed here).
* §2 `window_ap_recip_lower` — the main statement, in `Finset.Ioc ⌊y⌋ ⌊y²⌋` form.
* §2 `window_ap_recip_lower_icc` — the same statement with the window expressed as a real
  inequality `y < p` inside `Finset.Icc 1 ⌊y²⌋`.
* §3 `window_recip_upper` — the companion crude *upper* bound `∑_{y < r ≤ y²} 1/r ≤ 32` over
  all primes of the window (no progression), derived from
  `LargeStepRoughness.recip_prime_sum_le`.  This feeds the roughness-product step of Lemma D.

The proof of §2 is: apply the asymptotic weighted PNT at `x = y²` and at `x = y` with
`ε = 1/(16 φ(q))` and subtract, getting `≥ (13/16)·log y / φ(q)` of von Mangoldt mass in the
window; strip the proper prime powers (§1); and convert `(log p)/p` to `1/p` using
`log p ≤ log y² = 2 log y` on the window.  The threshold `y₀` absorbs `B` by taking
`log y ≥ 8 B φ(q)`.
-/

noncomputable section
open Classical
open Finset ArithmeticFunction

namespace LemmaD

/-! ## §1  The prime-power tail bound -/

/-- **Prime-power tail bound.**  There is an absolute constant `B ≥ 0` such that for *every*
finite set `S` of naturals, the non-prime part of the von Mangoldt sum `∑_{n ∈ S} Λ(n)/n` is at
most `B`.

Only prime powers contribute (`Λ` vanishes off prime powers), and the proper prime powers
contribute at most `∑_p 2 log p / p²`.  The estimate is `IK.nonprime_pp_sum_bounded_by_tsum`
(`EM/IK/Tauberian.lean`), repackaged here so that no hypothesis about the shape of `S` is
needed. -/
theorem prime_power_tail_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ S : Finset ℕ,
      ∑ n ∈ S.filter (fun n => ¬ Nat.Prime n), (Λ n : ℝ) / n ≤ B := by
  refine ⟨∑' p : ℕ, (if Nat.Prime p then 2 * Real.log p / (p : ℝ) ^ 2 else 0),
    tsum_nonneg (fun n => by split_ifs <;> positivity), fun S => ?_⟩
  have hsub : S.filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n) ⊆
      S.filter (fun n => ¬ Nat.Prime n) := by
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.2⟩
  have hzero : ∑ n ∈ (S.filter (fun n => ¬ Nat.Prime n)) \
      (S.filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n)), (Λ n : ℝ) / n = 0 := by
    refine Finset.sum_eq_zero (fun n hn => ?_)
    simp only [Finset.mem_sdiff, Finset.mem_filter] at hn
    have hnpp : ¬ IsPrimePow n := fun h => hn.2 ⟨hn.1.1, h, hn.1.2⟩
    simp [ArithmeticFunction.vonMangoldt_apply, hnpp]
  rw [← Finset.sum_sdiff hsub, hzero, zero_add]
  exact IK.nonprime_pp_sum_bounded_by_tsum S

/-! ## §2  The window reciprocal lower bound -/

/-- **Window AP reciprocal lower bound (Lemma D, analytic core).**

For `a` coprime to `q > 1` there is a threshold `y₀` past which the primes `p ≡ a (mod q)`
with `⌊y⌋ < p ≤ ⌊y²⌋` satisfy `∑ 1/p ≥ 1/(8 φ(q))`.

The constant is deliberately sloppy: the proof produces `11/(32 φ(q))`, and only positivity
and the dependence on `q` alone matter downstream. -/
theorem window_ap_recip_lower (q a : ℕ) (hq : 1 < q) (hcop : Nat.Coprime a q) :
    ∃ y₀ : ℝ, 2 ≤ y₀ ∧ ∀ y : ℝ, y₀ ≤ y →
      (1 : ℝ) / (8 * (Nat.totient q : ℝ)) ≤
        ∑ p ∈ (Finset.Ioc (Nat.floor y) (Nat.floor (y ^ 2))).filter
            (fun p => Nat.Prime p ∧ p % q = a % q), 1 / (p : ℝ) := by
  obtain ⟨B, hB0, hB⟩ := prime_power_tail_bound
  have hφpos : (0 : ℝ) < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have hε : (0 : ℝ) < 1 / (16 * (Nat.totient q : ℝ)) := by positivity
  obtain ⟨x₀, hx₀2, hx₀⟩ := IK.weightedPNTinAP_asymp_proved q a hq hcop _ hε
  set φ : ℝ := (Nat.totient q : ℝ) with hφdef
  have hφne : φ ≠ 0 := ne_of_gt hφpos
  refine ⟨max x₀ (Real.exp (8 * B * φ)), le_trans hx₀2 (le_max_left _ _), fun y hy => ?_⟩
  -- Basic size facts about `y`.
  have hyx₀ : x₀ ≤ y := le_trans (le_max_left _ _) hy
  have hyexp : Real.exp (8 * B * φ) ≤ y := le_trans (le_max_right _ _) hy
  have hy2 : (2 : ℝ) ≤ y := le_trans hx₀2 hyx₀
  have hL : 0 < Real.log y := Real.log_pos (by linarith)
  have hLB : 8 * B * φ ≤ Real.log y := by
    have h := Real.log_le_log (Real.exp_pos (8 * B * φ)) hyexp
    rwa [Real.log_exp] at h
  have hyy : y ≤ y ^ 2 := by nlinarith
  have hlog2 : Real.log (y ^ 2) = 2 * Real.log y := by
    rw [Real.log_pow]; push_cast; ring
  -- The two applications of the asymptotic weighted PNT.
  have h1 := hx₀ y hyx₀
  have h2 := hx₀ (y ^ 2) (le_trans hyx₀ hyy)
  rw [hlog2] at h2
  have hrw1 : 1 / (16 * φ) * Real.log y = (Real.log y / φ) / 16 := by
    field_simp
  have hrw2 : 1 / (16 * φ) * (2 * Real.log y) = (Real.log y / φ) / 8 := by
    field_simp; ring
  have hrw3 : 2 * Real.log y / φ = 2 * (Real.log y / φ) := by ring
  rw [hrw1] at h1
  rw [hrw2, hrw3] at h2
  set u : ℝ := Real.log y / φ with hu
  rw [abs_le] at h1 h2
  -- Finsets: the two initial segments and the window.
  set m : ℕ := Nat.floor y with hm
  set M : ℕ := Nat.floor (y ^ 2) with hM
  have hmM : m ≤ M := Nat.floor_mono hyy
  set S₁ : Finset ℕ := (Finset.Icc 1 m).filter (fun n => n % q = a % q) with hS₁
  set S₂ : Finset ℕ := (Finset.Icc 1 M).filter (fun n => n % q = a % q) with hS₂
  set W : Finset ℕ := (Finset.Ioc m M).filter (fun n => n % q = a % q) with hW
  set T : Finset ℕ := (Finset.Ioc m M).filter
    (fun p => Nat.Prime p ∧ p % q = a % q) with hT
  have hsub : S₁ ⊆ S₂ := by
    intro n hn
    simp only [hS₁, hS₂, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1, le_trans hn.1.2 hmM⟩, hn.2⟩
  have hdiff : S₂ \ S₁ = W := by
    ext n
    simp only [hS₁, hS₂, hW, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨⟨ha1, ha2⟩, hP⟩, h3⟩
      refine ⟨⟨?_, ha2⟩, hP⟩
      by_contra hc
      exact h3 ⟨⟨ha1, by omega⟩, hP⟩
    · rintro ⟨⟨ha1, ha2⟩, hP⟩
      exact ⟨⟨⟨by omega, ha2⟩, hP⟩, fun h => absurd h.1.2 (by omega)⟩
  have hsplit : ∑ n ∈ W, (Λ n : ℝ) / n + ∑ n ∈ S₁, (Λ n : ℝ) / n
      = ∑ n ∈ S₂, (Λ n : ℝ) / n := by
    rw [← hdiff]; exact Finset.sum_sdiff hsub
  -- Split the window sum into primes and the rest.
  have hWsplit := Finset.sum_filter_add_sum_filter_not W Nat.Prime (fun n => (Λ n : ℝ) / n)
  have hWT : W.filter Nat.Prime = T := by
    ext n
    simp only [hW, hT, Finset.mem_filter]
    tauto
  have hTsum : ∑ n ∈ W.filter Nat.Prime, (Λ n : ℝ) / n
      = ∑ p ∈ T, Real.log p / p := by
    rw [hWT]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    simp only [hT, Finset.mem_filter] at hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp.2.1]
  -- Convert `(log p)/p` to `1/p` using `log p ≤ 2 log y` on the window.
  set X : ℝ := ∑ p ∈ T, 1 / (p : ℝ) with hX
  have hkey : ∑ p ∈ T, Real.log p / p ≤ 2 * Real.log y * X := by
    rw [hX, Finset.mul_sum]
    refine Finset.sum_le_sum (fun p hp => ?_)
    simp only [hT, Finset.mem_filter, Finset.mem_Ioc] at hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.1.two_le
    have hppos : (0 : ℝ) < (p : ℝ) := by linarith
    have hple : (p : ℝ) ≤ y ^ 2 :=
      le_trans (by exact_mod_cast hp.1.2) (Nat.floor_le (by positivity))
    have hlogp : Real.log p ≤ 2 * Real.log y := by
      rw [← hlog2]; exact Real.log_le_log (by linarith) hple
    calc Real.log p / p ≤ (2 * Real.log y) / p := by gcongr
      _ = 2 * Real.log y * (1 / (p : ℝ)) := by ring
  -- Assemble: window von Mangoldt mass `≥ 13u/16`, primes carry all but `B` of it.
  have hcomb : 13 * u / 16 ≤ 2 * Real.log y * X + B := by
    linarith [hB W, h1.1, h1.2, h2.1, h2.2]
  have huφ : u * φ = Real.log y := by rw [hu]; field_simp
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 8 * φ)]
  have hmulφ : 13 * (u * φ) / 16 ≤ (2 * Real.log y * X + B) * φ := by
    have h := mul_le_mul_of_nonneg_right hcomb hφpos.le
    linarith [h]
  rw [huφ] at hmulφ
  nlinarith [hmulφ, hLB, hL, hφpos, hB0, mul_pos hL hφpos]

/-- **Window AP reciprocal lower bound, `Icc`-with-real-cutoff form.**

The same statement as `window_ap_recip_lower`, with the window written as the real condition
`y < p` inside `Finset.Icc 1 ⌊y²⌋`.  For a natural `p` the two descriptions agree because
`⌊y⌋ < p ↔ y < p` (`Nat.floor_lt`). -/
theorem window_ap_recip_lower_icc (q a : ℕ) (hq : 1 < q) (hcop : Nat.Coprime a q) :
    ∃ y₀ : ℝ, 2 ≤ y₀ ∧ ∀ y : ℝ, y₀ ≤ y →
      (1 : ℝ) / (8 * (Nat.totient q : ℝ)) ≤
        ∑ p ∈ (Finset.Icc 1 (Nat.floor (y ^ 2))).filter
            (fun p => Nat.Prime p ∧ y < (p : ℝ) ∧ p % q = a % q), 1 / (p : ℝ) := by
  obtain ⟨y₀, hy₀, h⟩ := window_ap_recip_lower q a hq hcop
  refine ⟨y₀, hy₀, fun y hy => ?_⟩
  have hy2 : (2 : ℝ) ≤ y := le_trans hy₀ hy
  have hset : (Finset.Icc 1 (Nat.floor (y ^ 2))).filter
      (fun p => Nat.Prime p ∧ y < (p : ℝ) ∧ p % q = a % q)
      = (Finset.Ioc (Nat.floor y) (Nat.floor (y ^ 2))).filter
          (fun p => Nat.Prime p ∧ p % q = a % q) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨_, h2⟩, hp, hyp, hres⟩
      exact ⟨⟨(Nat.floor_lt (by linarith)).mpr hyp, h2⟩, hp, hres⟩
    · rintro ⟨⟨h1, h2⟩, hp, hres⟩
      exact ⟨⟨hp.one_lt.le, h2⟩, hp, (Nat.floor_lt (by linarith)).mp h1, hres⟩
  rw [hset]
  exact h y hy

/-! ## §3  The companion upper bound over the whole window -/

/-- `1 < log 4`. -/
private theorem one_lt_log_four : 1 < Real.log 4 := by
  have he : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr he

/-- **Window reciprocal upper bound.**  For `y ≥ 4` the *all-primes* window `(⌊y⌋, ⌊y²⌋]`
carries reciprocal mass at most the absolute constant `32`.

This is `LargeStepRoughness.recip_prime_sum_le` (Mertens upper bound + discrete Abel summation)
applied with `u = ⌊y⌋`, `v = ⌊y²⌋`, together with `log ⌊y⌋ ≥ (log y)/2` and
`log ⌊y²⌋ ≤ 2 log y`.  Paired with `window_ap_recip_lower`, this says that a fixed positive
*proportion* of the window's reciprocal mass sits in the progression. -/
theorem window_recip_upper (y : ℝ) (hy : 4 ≤ y) :
    ∑ r ∈ (Finset.Ioc (Nat.floor y) (Nat.floor (y ^ 2))).filter Nat.Prime, (1 : ℝ) / r
      ≤ 32 := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hl4 : Real.log 4 ≤ 2 := LargeStepRoughness.log_four_le_two
  have hl41 : 1 < Real.log 4 := one_lt_log_four
  have hly : Real.log 4 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hL : 1 < Real.log y := lt_of_lt_of_le hl41 hly
  -- `⌊y⌋ ≥ 4`, in particular `≥ 2`.
  have hfl4 : 4 ≤ Nat.floor y := Nat.le_floor (by exact_mod_cast hy)
  have hflR : (4 : ℝ) ≤ (Nat.floor y : ℝ) := by exact_mod_cast hfl4
  -- `log ⌊y⌋ ≥ (log y)/2`.
  have hflge : y / 2 ≤ (Nat.floor y : ℝ) := by
    have h := Nat.sub_one_lt_floor y
    linarith
  have hlogfl : Real.log y / 2 ≤ Real.log (Nat.floor y : ℝ) := by
    have hmono : Real.log (y / 2) ≤ Real.log (Nat.floor y : ℝ) :=
      Real.log_le_log (by linarith) hflge
    have hdiv : Real.log (y / 2) = Real.log y - Real.log 2 := Real.log_div (by linarith) (by norm_num)
    have hl2 : Real.log 2 ≤ Real.log y / 2 := by
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
      linarith
    linarith
  have hlogflpos : 0 < Real.log (Nat.floor y : ℝ) := by linarith
  -- `log ⌊y²⌋ ≤ 2 log y`.
  have hlog2 : Real.log (y ^ 2) = 2 * Real.log y := by
    rw [Real.log_pow]; push_cast; ring
  have hMle : (Nat.floor (y ^ 2) : ℝ) ≤ y ^ 2 := Nat.floor_le (by positivity)
  have hMpos : (0 : ℝ) < (Nat.floor (y ^ 2) : ℝ) := by
    have : (4 : ℕ) ≤ Nat.floor (y ^ 2) := Nat.le_floor (by push_cast; nlinarith)
    have : (4 : ℝ) ≤ (Nat.floor (y ^ 2) : ℝ) := by exact_mod_cast this
    linarith
  have hlogM : Real.log (Nat.floor (y ^ 2) : ℝ) ≤ 2 * Real.log y := by
    rw [← hlog2]; exact Real.log_le_log hMpos hMle
  calc ∑ r ∈ (Finset.Ioc (Nat.floor y) (Nat.floor (y ^ 2))).filter Nat.Prime, (1 : ℝ) / r
      ≤ 2 * Real.log 4 * (2 + Real.log (Nat.floor (y ^ 2) : ℝ))
          / Real.log (Nat.floor y : ℝ) :=
        LargeStepRoughness.recip_prime_sum_le _ _ (by omega)
    _ ≤ 2 * 2 * (2 + 2 * Real.log y) / (Real.log y / 2) := by
        gcongr
    _ = 8 * (2 + 2 * Real.log y) / Real.log y := by
        rw [div_div_eq_mul_div]; ring_nf
    _ ≤ 32 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith

end LemmaD
