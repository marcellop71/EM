import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.Order
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Kornblum's theorem, part 1: two abstract lemmas on sequences

This file contains the two pieces of "analysis" that the proof of Kornblum's
theorem (Dirichlet's theorem for `F_p[t]`, see `EM/FunctionField/Kornblum.lean`)
needs. Both are statements about sequences of complex numbers; no polynomial
over a finite field appears here.

## 1. Bounded partial sums from a linear recurrence (`bounded_partial_sums`)

Let `a_0, …, a_{d-1}` be complex numbers with `a_0 + … + a_{d-1} ≠ 0`, and let
`b` be a sequence with `|b_n| ≤ 1` which satisfies the linear recurrence
`∑_{k<d} a_k b_{n-k} = 0` for all `n ≥ d`. Then the partial sums
`∑_{n<N} b_n / n` are bounded.

In the application `a_k = A_k(χ) q^{-k}` are the normalised coefficients of the
polynomial `L(u, χ)`, the sum `∑ a_k` is `L(1/q, χ)`, and `b_n = Ψ_n(χ) q^{-n}`.
The proof is a summation by parts: writing `c_n = b_n / n`, the recurrence
gives `∑_k a_k c_{n-k} = (1/n) ∑_k k a_k c_{n-k} = O(1/n²)`, and summing over
`n` shows that `(∑_k a_k) · ∑_{n<N} c_n` is bounded.

## 2. Logarithmic derivatives of power series (`theta`)

For a power series `F = ∑ F_n u^n` put `θF = ∑ n F_n u^n` (this is `u · F'`).
`θ` is a derivation (`theta_mul`), so the relation `θF = F · B` ("`B` is the
logarithmic derivative of `F`") is additive in `B` under products of `F`
(`theta_prod`). If `F_0 = 1`, `B_0 = 0` and all `B_n` are non-negative reals,
then all `F_n` are non-negative reals and `B_n ≤ n F_n`
(`coeff_nonneg_of_theta`); in particular `F_n ≠ 0` whenever `B_n ≠ 0`. This
replaces the Euler product in the classical non-vanishing argument.
-/

namespace FunctionFieldAnalog.Kornblum

open Finset

/-! ## Bounded partial sums -/

/-- A sum of complex numbers of modulus at most `1` is bounded by the number of
    terms. -/
theorem norm_sum_le_card {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ 1) (s : Finset ℕ) :
    ‖∑ n ∈ s, c n‖ ≤ s.card := by
  calc ‖∑ n ∈ s, c n‖ ≤ ∑ n ∈ s, ‖c n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ s, (1 : ℝ) := sum_le_sum fun n _ => hc n
    _ = s.card := by simp

/-- The partial sums of `∑ 1/(m+1)²` are bounded. -/
theorem exists_bound_sum_inv_sq :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ M : ℕ, ∑ m ∈ range M, 1 / ((m : ℝ) + 1) ^ 2 ≤ S := by
  have hsum : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using h
  exact ⟨∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2, tsum_nonneg fun m => by positivity,
    fun M => hsum.sum_le_tsum _ fun m _ => by positivity⟩

/-- **Bounded partial sums from a recurrence.** If `|b_n| ≤ 1`, the sequence `b`
    satisfies `∑_{k<d} a_k b_{n-k} = 0` for `n ≥ d`, and `∑_{k<d} a_k ≠ 0`, then
    the partial sums of `∑ b_n / n` are bounded. -/
theorem bounded_partial_sums {d : ℕ} (a b : ℕ → ℂ) (hb : ∀ n, ‖b n‖ ≤ 1)
    (hrec : ∀ n, d ≤ n → ∑ k ∈ range d, a k * b (n - k) = 0)
    (hs : ∑ k ∈ range d, a k ≠ 0) :
    ∃ C : ℝ, ∀ N, ‖∑ n ∈ range N, b n / n‖ ≤ C := by
  obtain ⟨S, hS0, hS⟩ := exists_bound_sum_inv_sq
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · simp at hs
    · exact h
  set c : ℕ → ℂ := fun n => b n / n with hc
  have hc1 : ∀ n, ‖c n‖ ≤ 1 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hc]
    · simp only [hc, norm_div, Complex.norm_natCast]
      rw [div_le_one (by exact_mod_cast hn)]
      exact (hb n).trans (by exact_mod_cast hn)
  have hcn : ∀ n, ‖c n‖ ≤ 1 / n := by
    intro n
    simp only [hc, norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (hb n) (Nat.cast_nonneg n)
  set s := ∑ k ∈ range d, a k with hsdef
  set Asum := ∑ k ∈ range d, ‖a k‖ with hAsum
  set K := ∑ k ∈ range d, (k : ℝ) * ‖a k‖ with hK
  set B : ℕ → ℂ := fun N => ∑ n ∈ range N, c n with hB
  have hBcard : ∀ N, ‖B N‖ ≤ N := fun N => by simpa using norm_sum_le_card hc1 (range N)
  have hAs : ‖s‖ ≤ Asum := norm_sum_le _ _
  have hA0 : 0 ≤ Asum := sum_nonneg fun _ _ => norm_nonneg _
  have hK0 : 0 ≤ K := sum_nonneg fun _ _ => by positivity
  have key : ∀ N, ‖s * B N‖ ≤ 2 * d * Asum + K * S := by
    intro N
    rcases lt_or_ge N d with hNd | hdN
    · have hNd' : (N : ℝ) ≤ d := by exact_mod_cast hNd.le
      calc ‖s * B N‖ = ‖s‖ * ‖B N‖ := norm_mul _ _
        _ ≤ Asum * d := mul_le_mul hAs ((hBcard N).trans hNd') (norm_nonneg _) hA0
        _ ≤ 2 * d * Asum + K * S := by
          nlinarith [mul_nonneg hK0 hS0, mul_nonneg hA0 (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    · set e : ℕ → ℂ := fun n => ∑ k ∈ range d, a k * c (n - k) with he_def
      have hshift : ∀ k ∈ range d, ∑ n ∈ Ico d N, c (n - k) = B (N - k) - B (d - k) := by
        intro k hk
        have hk' : k ≤ d := (mem_range.mp hk).le
        have h1 := Finset.sum_Ico_add' (fun x => c (x - k)) (d - k) (N - k) k
        simp only [Nat.add_sub_cancel] at h1
        rw [Nat.sub_add_cancel hk', Nat.sub_add_cancel (hk'.trans hdN)] at h1
        rw [← h1, Finset.sum_Ico_eq_sub _ (Nat.sub_le_sub_right hdN k)]
      have hsum_e : ∑ n ∈ Ico d N, e n = ∑ k ∈ range d, a k * (B (N - k) - B (d - k)) := by
        simp only [he_def]
        rw [sum_comm]
        refine sum_congr rfl fun k hk => ?_
        rw [← mul_sum, hshift k hk]
      have hdecomp : s * B N =
          ∑ k ∈ range d, a k * (B N - B (N - k) + B (d - k)) + ∑ n ∈ Ico d N, e n := by
        rw [hsum_e, ← sum_add_distrib, hsdef, sum_mul]
        exact sum_congr rfl fun k _ => by ring
      have hfirst : ‖∑ k ∈ range d, a k * (B N - B (N - k) + B (d - k))‖ ≤ 2 * d * Asum := by
        calc ‖∑ k ∈ range d, a k * (B N - B (N - k) + B (d - k))‖
            ≤ ∑ k ∈ range d, ‖a k * (B N - B (N - k) + B (d - k))‖ := norm_sum_le _ _
          _ ≤ ∑ k ∈ range d, ‖a k‖ * (2 * d) := by
              refine sum_le_sum fun k hk => ?_
              rw [norm_mul]
              refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              have hk' : k < d := mem_range.mp hk
              have h1 : ‖B N - B (N - k)‖ ≤ d := by
                have h : B N - B (N - k) = ∑ n ∈ Ico (N - k) N, c n :=
                  (Finset.sum_Ico_eq_sub _ (Nat.sub_le N k)).symm
                rw [h]
                refine (norm_sum_le_card hc1 _).trans ?_
                rw [Nat.card_Ico]
                exact_mod_cast (by omega : N - (N - k) ≤ d)
              have h2 : ‖B (d - k)‖ ≤ d :=
                (hBcard _).trans (by exact_mod_cast Nat.sub_le d k)
              calc ‖B N - B (N - k) + B (d - k)‖
                  ≤ ‖B N - B (N - k)‖ + ‖B (d - k)‖ := norm_add_le _ _
                _ ≤ 2 * d := by linarith
          _ = 2 * d * Asum := by rw [← sum_mul]; ring
      have he : ∀ n ∈ Ico d N, ‖e n‖ ≤ K * (1 / (((n - d : ℕ) : ℝ) + 1) ^ 2) := by
        intro n hn
        have hdn : d ≤ n := (mem_Ico.mp hn).1
        have hn0 : 0 < n := lt_of_lt_of_le hd hdn
        have hne : (n : ℂ) * e n = ∑ k ∈ range d, (k : ℂ) * a k * c (n - k) := by
          have h0 := hrec n hdn
          have h1 : ∑ k ∈ range d, a k * b (n - k) =
              ∑ k ∈ range d, a k * (((n - k : ℕ) : ℂ) * c (n - k)) := by
            refine sum_congr rfl fun k hk => ?_
            have hpos : 0 < n - k := by have := mem_range.mp hk; omega
            have hne0 : ((n - k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
            simp only [hc]
            rw [mul_div_cancel₀ _ hne0]
          rw [h1] at h0
          simp only [he_def]
          rw [mul_sum, ← sub_zero (∑ k ∈ range d, (n : ℂ) * (a k * c (n - k))), ← h0,
            ← sum_sub_distrib]
          refine sum_congr rfl fun k hk => ?_
          have hkn : k ≤ n := by have := mem_range.mp hk; omega
          rw [Nat.cast_sub hkn]
          ring
        have hbound : ‖(n : ℂ) * e n‖ ≤ K * (1 / (((n - d : ℕ) : ℝ) + 1)) := by
          rw [hne]
          calc ‖∑ k ∈ range d, (k : ℂ) * a k * c (n - k)‖
              ≤ ∑ k ∈ range d, ‖(k : ℂ) * a k * c (n - k)‖ := norm_sum_le _ _
            _ ≤ ∑ k ∈ range d, (k : ℝ) * ‖a k‖ * (1 / (((n - d : ℕ) : ℝ) + 1)) := by
                refine sum_le_sum fun k hk => ?_
                have hk' := mem_range.mp hk
                rw [norm_mul, norm_mul, Complex.norm_natCast]
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                refine (hcn (n - k)).trans ?_
                apply one_div_le_one_div_of_le (by positivity)
                have h : n - d + 1 ≤ n - k := by omega
                exact_mod_cast h
            _ = K * (1 / (((n - d : ℕ) : ℝ) + 1)) := by rw [← sum_mul]
        have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
        have hnorm : ‖e n‖ = ‖(n : ℂ) * e n‖ / n := by
          rw [norm_mul, Complex.norm_natCast]
          field_simp
        rw [hnorm, div_le_iff₀ hnpos]
        refine hbound.trans ?_
        have hm : ((n - d : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast (by omega : n - d + 1 ≤ n)
        have hmp : (0 : ℝ) < ((n - d : ℕ) : ℝ) + 1 := by positivity
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hK0
        rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hmp (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right hm hmp.le]
      have hsecond : ‖∑ n ∈ Ico d N, e n‖ ≤ K * S := by
        calc ‖∑ n ∈ Ico d N, e n‖ ≤ ∑ n ∈ Ico d N, ‖e n‖ := norm_sum_le _ _
          _ ≤ ∑ n ∈ Ico d N, K * (1 / (((n - d : ℕ) : ℝ) + 1) ^ 2) := sum_le_sum he
          _ = K * ∑ m ∈ range (N - d), 1 / ((m : ℝ) + 1) ^ 2 := by
              rw [← mul_sum, Finset.sum_Ico_eq_sum_range]
              simp
          _ ≤ K * S := mul_le_mul_of_nonneg_left (hS _) hK0
      rw [hdecomp]
      exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)
  refine ⟨(2 * d * Asum + K * S) / ‖s‖, fun N => ?_⟩
  rw [le_div_iff₀ (norm_pos_iff.mpr hs), mul_comm, ← norm_mul]
  exact key N

/-! ## Logarithmic derivatives of power series -/

/-- The operator `θ = u · d/du` on power series: `θ(∑ F_n u^n) = ∑ n F_n u^n`. -/
noncomputable def theta (F : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => (n : ℂ) * PowerSeries.coeff n F

@[simp] theorem coeff_theta (F : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n (theta F) = (n : ℂ) * PowerSeries.coeff n F := by
  simp [theta]

/-- `θ` is a derivation: `θ(FG) = θF · G + F · θG`. -/
theorem theta_mul (F G : PowerSeries ℂ) : theta (F * G) = theta F * G + F * theta G := by
  ext n
  simp only [coeff_theta, PowerSeries.coeff_mul, map_add, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  have h := Finset.mem_antidiagonal.mp hij
  rw [← h]
  push_cast
  ring

/-- `θ 1 = 0`. -/
theorem theta_one : theta 1 = 0 := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp [PowerSeries.coeff_one, hn.ne']

/-- Logarithmic derivatives add up under finite products: if `θ F_i = F_i B_i`
    for all `i`, then `θ(∏ F_i) = (∏ F_i) · ∑ B_i`. -/
theorem theta_prod {ι : Type*} (s : Finset ι) (F B : ι → PowerSeries ℂ)
    (h : ∀ i ∈ s, theta (F i) = F i * B i) :
    theta (∏ i ∈ s, F i) = (∏ i ∈ s, F i) * ∑ i ∈ s, B i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [theta_one]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, theta_mul,
      h i (Finset.mem_insert_self i s),
      ih fun j hj => h j (Finset.mem_insert_of_mem hj)]
    ring

open ComplexOrder in
/-- **Positivity from a non-negative logarithmic derivative.** If `θF = F · B`
    with `F_0 = 1`, `B_0 = 0` and all coefficients of `B` non-negative reals,
    then all coefficients of `F` are non-negative reals and `B_n ≤ n · F_n`. -/
theorem coeff_nonneg_of_theta {F B : PowerSeries ℂ} (h0 : PowerSeries.coeff 0 F = 1)
    (hB0 : PowerSeries.coeff 0 B = 0) (hθ : theta F = F * B)
    (hB : ∀ n, 0 ≤ PowerSeries.coeff n B) (n : ℕ) :
    0 ≤ PowerSeries.coeff n F ∧ PowerSeries.coeff n B ≤ (n : ℂ) * PowerSeries.coeff n F := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [h0, hB0]
    · have hcoef : (n : ℂ) * PowerSeries.coeff n F =
          ∑ ij ∈ Finset.antidiagonal n, PowerSeries.coeff ij.1 F * PowerSeries.coeff ij.2 B := by
        rw [← coeff_theta, hθ, PowerSeries.coeff_mul]
      have hterm : ∀ ij ∈ Finset.antidiagonal n,
          0 ≤ PowerSeries.coeff ij.1 F * PowerSeries.coeff ij.2 B := by
        intro ij hij
        have hsum := Finset.mem_antidiagonal.mp hij
        rcases Nat.eq_zero_or_pos ij.2 with h2 | h2
        · rw [h2, hB0, mul_zero]
        · exact mul_nonneg (ih ij.1 (by omega)).1 (hB _)
      have hle : PowerSeries.coeff n B ≤ (n : ℂ) * PowerSeries.coeff n F := by
        rw [hcoef]
        have h1 := Finset.single_le_sum hterm
          (Finset.mem_antidiagonal.mpr (zero_add n) : (0, n) ∈ Finset.antidiagonal n)
        simpa [h0] using h1
      refine ⟨?_, hle⟩
      have hnn : 0 ≤ (n : ℂ) * PowerSeries.coeff n F := (hB n).trans hle
      rw [Complex.nonneg_iff] at hnn ⊢
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero,
        Complex.mul_im, add_zero] at hnn
      refine ⟨nonneg_of_mul_nonneg_right hnn.1 hnpos, ?_⟩
      have him := hnn.2
      rcases mul_eq_zero.mp him.symm with h | h
      · exact absurd h hnpos.ne'
      · exact h.symm

end FunctionFieldAnalog.Kornblum
