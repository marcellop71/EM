import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# The finite van der Corput inequality (Mathlib-only)

For a sequence `f : ℕ → ℂ` bounded by `1` whose autocorrelations at lags `1 ≤ h ≤ H` are
bounded by `δ N`,

  `‖∑_{n<N} f n‖² ≤ 2 N² / (H+1) + 2 δ N²`.

Extracted 2026-08-18 from `EM/LargeSieve/Spectral.lean` so that it depends only on Mathlib
(candidate for upstreaming; the statement is also available un-wrapped as
`vanDerCorput_norm_sq_sum_le`).  Not in Mathlib as of v4.33.0.
-/

open Finset

/-- `‖conj z‖ = ‖z‖` (local alias of `Complex.norm_conj`). -/
private theorem norm_starRingEnd_complex (z : ℂ) : ‖starRingEnd ℂ z‖ = ‖z‖ :=
  Complex.norm_conj z

/-- `‖z‖² = Re(z · conj z)`. -/
private theorem complex_norm_sq_eq_re_mul_conj (z : ℂ) :
    ‖z‖ ^ 2 = (z * starRingEnd ℂ z).re := by
  have h := Complex.mul_conj' z
  rw [h]; norm_cast

/-- **Van der Corput bound for bounded sequences**: a corollary of the classical
    finite Van der Corput inequality. For a bounded sequence f with small
    autocorrelations, the partial sum is small.

    Precisely: for any sequence f(0), ..., f(N-1) in C with ||f(n)|| <= 1,
    if there exist H >= 1 and delta > 0 such that
    ||sum_{n<N-h} f(n) * conj(f(n+h))|| <= delta * N for all 1 <= h <= H,
    then ||sum f(n)||^2 <= C * N^2 where C depends on H, delta.

    We state the bound in the form that is most convenient for composition
    with HOD: given H and delta, the conclusion bounds the sum norm squared
    by (2*N^2/(H+1) + 2*delta*N^2), capturing the two sources of error
    (short lag window and autocorrelation size).

    This is a known result in analytic number theory, not currently in Mathlib.

    **Proof**: We use the Iwaniec-Kowalski averaging trick. Define g : ℕ → ℂ as the
    zero extension of f (g(n) = f(n) for n < N, 0 otherwise). For the windowed sum
    w(j) = ∑_{h=0}^{min(j,H)} g(j-h), we have:
    (1) ∑_j w(j) = (H+1)·S (each value f(n) is counted H+1 times)
    (2) ∑_j ‖w(j)‖² = (H+1)·R₀ + 2·Re(∑_{ℓ=1}^H (H+1-ℓ)·R_ℓ)
        where R_ℓ = ∑_{n<N-ℓ} f(n)·conj(f(n+ℓ)) is the autocorrelation at lag ℓ.
    By Cauchy-Schwarz: (H+1)²·‖S‖² ≤ (N+H)·∑‖w(j)‖².
    Bounding: ∑‖w(j)‖² ≤ (H+1)N + 2δN·H(H+1)/2 = (H+1)N(1+Hδ).
    So ‖S‖² ≤ N(N+H)(1+Hδ)/(H+1) ≤ 2N²/(H+1) + 2δN². -/
def VanDerCorputBound : Prop :=
  ∀ (N : ℕ) (f : ℕ → ℂ),
  (∀ n, ‖f n‖ ≤ 1) →
  ∀ (H : ℕ), 1 ≤ H → H ≤ N →
  ∀ (δ : ℝ), 0 < δ →
  (∀ h : ℕ, 1 ≤ h → h ≤ H →
    ‖∑ n ∈ Finset.range (N - h), f n * starRingEnd ℂ (f (n + h))‖ ≤ δ * (N : ℝ)) →
  ‖∑ n ∈ Finset.range N, f n‖ ^ 2 ≤
    2 * (N : ℝ) ^ 2 / ((H : ℝ) + 1) + 2 * δ * (N : ℝ) ^ 2

/-- Cauchy-Schwarz for `Finset.range` sums: `‖∑_{i<M} z_i‖² ≤ M · ∑_{i<M} ‖z_i‖²`. -/
private theorem norm_sq_sum_le_card_mul_range {M : ℕ} {z : ℕ → ℂ} :
    ‖∑ j ∈ Finset.range M, z j‖ ^ 2 ≤ (M : ℝ) * ∑ j ∈ Finset.range M, ‖z j‖ ^ 2 := by
  have h1 : ‖∑ j ∈ Finset.range M, z j‖ ^ 2 ≤ (∑ j ∈ Finset.range M, ‖z j‖) ^ 2 := by
    gcongr; exact norm_sum_le _ _
  calc ‖∑ j ∈ Finset.range M, z j‖ ^ 2
      ≤ (∑ j ∈ Finset.range M, ‖z j‖) ^ 2 := h1
    _ = (∑ j ∈ Finset.range M, 1 * ‖z j‖) ^ 2 := by simp
    _ ≤ (∑ _j ∈ Finset.range M, (1 : ℝ) ^ 2) * (∑ j ∈ Finset.range M, ‖z j‖ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq (Finset.range M) (fun _ => 1) (fun j => ‖z j‖)
    _ = (M : ℝ) * ∑ j ∈ Finset.range M, ‖z j‖ ^ 2 := by
        simp [Finset.card_range]

private theorem int_shift_injOn (s : Finset ℕ) (c : ℤ) :
    Set.InjOn (fun n : ℕ => (↑n + c : ℤ)) s := by
  intro a _ b _ hab; exact_mod_cast show (a : ℤ) = b by linarith

/-- Algebraic reduction: from the IK-style inequality
    `(H+1)^2 * ‖S‖^2 ≤ 2N(H+1)N(1+Hδ)` to the final VdC bound
    `‖S‖^2 ≤ 2N^2/(H+1) + 2δN^2`. -/
private theorem vdc_ik_reduction {N H : ℕ} {δ : ℝ} {S : ℂ}
    (hH1r : (0 : ℝ) < (H : ℝ) + 1) (hδ : 0 < δ) :
    ((H : ℝ) + 1) ^ 2 * ‖S‖ ^ 2 ≤
      2 * (↑N : ℝ) * ((H : ℝ) + 1) * ↑N * (1 + ↑H * δ) →
    ‖S‖ ^ 2 ≤ 2 * (N : ℝ) ^ 2 / ((H : ℝ) + 1) + 2 * δ * (N : ℝ) ^ 2 := by
  intro hIK
  have h1 : ‖S‖ ^ 2 ≤ 2 * (N : ℝ) ^ 2 * (1 + (H : ℝ) * δ) / ((H : ℝ) + 1) := by
    rw [le_div_iff₀ hH1r]
    nlinarith [sq ((H : ℝ) + 1), sq_nonneg ‖S‖]
  have h2 : 2 * (N : ℝ) ^ 2 * (1 + (H : ℝ) * δ) / ((H : ℝ) + 1)
      ≤ 2 * (N : ℝ) ^ 2 / ((H : ℝ) + 1) + 2 * δ * (N : ℝ) ^ 2 := by
    suffices h : 2 * (N : ℝ) ^ 2 * ((H : ℝ) * δ) / ((H : ℝ) + 1) ≤
        2 * δ * (N : ℝ) ^ 2 by
      have expand : 2 * (N : ℝ) ^ 2 * (1 + (H : ℝ) * δ) / ((H : ℝ) + 1) =
          2 * (N : ℝ) ^ 2 / ((H : ℝ) + 1) + 2 * (N : ℝ) ^ 2 * ((H : ℝ) * δ) / ((H : ℝ) + 1) := by
        rw [mul_add, mul_one, add_div]
      linarith
    rw [div_le_iff₀ hH1r]; nlinarith
  linarith

/-- Sum identity for windowed sums: `∑_{j∈Jset} w(j) = (H+1) * S`.
    Each shift `g(j-h)` sums to `S` over `Jset` by reindexing. -/
private theorem vdc_sum_identity {N H : ℕ} {f : ℕ → ℂ}
    (g : ℤ → ℂ) (hg_def : g = fun n => if 0 ≤ n ∧ n < (N : ℤ) then f n.toNat else 0)
    (w : ℤ → ℂ) (hw_def : w = fun j => ∑ h ∈ Finset.range (H + 1), g (j - ↑h))
    (Jset : Finset ℤ) (hJset_def : Jset = Finset.Ico (0 : ℤ) (↑N + ↑H))
    (S : ℂ) (hS_def : S = ∑ n ∈ Finset.range N, f n) :
    ∑ j ∈ Jset, w j = (↑(H + 1) : ℂ) * S := by
  -- First prove ∑_{j∈Jset} g(j-h) = S for each h ∈ [0,H]
  have hg_shift_sum : ∀ h ≤ H, ∑ j ∈ Jset, g (j - (h : ℤ)) = S := by
    intro h hh
    have : ∑ j ∈ Jset, g (j - (h : ℤ)) =
        ∑ n ∈ Finset.range N, g (↑n) := by
      set img := Finset.image (fun n : ℕ => (↑n + (h : ℤ))) (Finset.range N)
      have himg_sub : img ⊆ Jset := by
        intro j hj; simp only [img, Finset.mem_image, Finset.mem_range] at hj
        obtain ⟨n, hn, rfl⟩ := hj; simp [hJset_def, Finset.mem_Ico]; omega
      have hzero : ∀ j ∈ Jset, j ∉ img → g (j - (h : ℤ)) = 0 := by
        intro j _ hnmem
        simp only [hg_def]; split_ifs with hcond
        · exfalso; apply hnmem
          simp only [img, Finset.mem_image, Finset.mem_range]
          exact ⟨(j - (h : ℤ)).toNat, by omega, by omega⟩
        · rfl
      rw [← Finset.sum_subset himg_sub (fun j hj hnj => hzero j hj hnj)]
      rw [Finset.sum_image (int_shift_injOn _ _)]
      apply Finset.sum_congr rfl; intro n _
      show g ((↑n + (h : ℤ)) - (h : ℤ)) = g (↑n)
      congr 1; omega
    rw [this, hS_def]
    apply Finset.sum_congr rfl
    intro n hn
    have hn_lt := Finset.mem_range.mp hn
    simp [hg_def, hn_lt]
  simp only [hw_def]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun h hh => hg_shift_sum h
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)))]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Diagonal energy bound: for each `h`, the diagonal inner product
    `∑_j g(j-h) * conj(g(j-h))` equals `∑_n ‖f(n)‖^2`, and the aggregate
    diagonal sum is bounded by `(H+1) * N`. -/
private theorem vdc_diagonal_bound {N H : ℕ} {f : ℕ → ℂ}
    (hf : ∀ n, ‖f n‖ ≤ 1)
    (g : ℤ → ℂ) (hg_def : g = fun n => if 0 ≤ n ∧ n < (N : ℤ) then f n.toNat else 0)
    (Jset : Finset ℤ) (hJset_def : Jset = Finset.Ico (0 : ℤ) (↑N + ↑H))
    (Hset : Finset ℕ) (hHset_def : Hset = Finset.range (H + 1)) :
    (∑ h₁ ∈ Hset, ∑ j ∈ Jset,
      g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₁))).re ≤ (↑H + 1) * ↑N := by
  -- Each diagonal inner sum equals ∑_n ‖f(n)‖^2
  have hdiag_eq : ∀ h ∈ Hset,
      ∑ j ∈ Jset, g (j - ↑h) * starRingEnd ℂ (g (j - ↑h)) =
      ∑ n ∈ Finset.range N, (‖f n‖ ^ 2 : ℂ) := by
    intro h hh
    have hh_le : h ≤ H := by rw [hHset_def] at hh; exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)
    have heq : ∑ j ∈ Jset, g (j - ↑h) * starRingEnd ℂ (g (j - ↑h)) =
        ∑ n ∈ Finset.range N, g (↑n) * starRingEnd ℂ (g (↑n)) := by
      set img := Finset.image (fun n : ℕ => (↑n + (h : ℤ))) (Finset.range N)
      have himg_sub : img ⊆ Jset := by
        intro j hj; simp only [img, Finset.mem_image, Finset.mem_range] at hj
        obtain ⟨n, hn, rfl⟩ := hj; simp [hJset_def, Finset.mem_Ico]; omega
      rw [← Finset.sum_subset himg_sub (fun j _ hnj => by
        have : g (j - (h : ℤ)) = 0 := by
          simp only [hg_def]; split_ifs with hcond
          · exfalso; apply hnj; simp only [img, Finset.mem_image, Finset.mem_range]
            exact ⟨(j - (h : ℤ)).toNat, by omega, by omega⟩
          · rfl
        simp [this])]
      rw [Finset.sum_image (by intro a _ b _ (hab : (↑a : ℤ) + ↑h = ↑b + ↑h); omega)]
      apply Finset.sum_congr rfl; intro n _
      have hsub : (↑n + (h : ℤ)) - (h : ℤ) = ↑n := by omega
      simp only [hsub]
    rw [heq]
    apply Finset.sum_congr rfl; intro n hn
    have hn_lt := Finset.mem_range.mp hn
    simp only [hg_def, Int.natCast_nonneg, Nat.cast_lt, hn_lt, and_self, ite_true,
                Int.toNat_natCast]
    rw [Complex.mul_conj']
  -- Norm-squared sum is bounded by N
  have hf_norm_sq_le : (∑ n ∈ Finset.range N, ‖f n‖ ^ 2 : ℝ) ≤ ↑N := by
    calc (∑ n ∈ Finset.range N, ‖f n‖ ^ 2 : ℝ)
        ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) :=
          Finset.sum_le_sum (fun n _ => by nlinarith [hf n, norm_nonneg (f n)])
      _ = ↑N := by simp
  -- Assemble
  have hrewr : ∑ h₁ ∈ Hset, ∑ j ∈ Jset,
      g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₁)) =
      ∑ _h₁ ∈ Hset, ∑ n ∈ Finset.range N, (‖f n‖ ^ 2 : ℂ) :=
    Finset.sum_congr rfl (fun h hh => hdiag_eq h hh)
  rw [hrewr, Finset.sum_const, hHset_def, Finset.card_range, nsmul_eq_mul]
  rw [show (↑(H + 1) : ℂ) * ∑ n ∈ Finset.range N, (‖f n‖ ^ 2 : ℂ) =
      (↑((↑(H + 1) : ℝ) * ∑ n ∈ Finset.range N, ‖f n‖ ^ 2) : ℂ) from by
    push_cast; simp]
  rw [Complex.ofReal_re]
  calc (↑(H + 1) : ℝ) * ∑ n ∈ Finset.range N, ‖f n‖ ^ 2
      ≤ (↑(H + 1) : ℝ) * ↑N := by gcongr
    _ = (↑H + 1) * ↑N := by push_cast; ring

/-- Off-diagonal cross-sum bound: for `h₁ ≠ h₂` in `Hset`, the cross-sum
    `‖∑_j g(j-h₁) * conj(g(j-h₂))‖ ≤ δ * N`. Uses reindexing and
    conjugation symmetry to reduce to the autocorrelation hypothesis. -/
private theorem vdc_cross_bound {N H : ℕ} {f : ℕ → ℂ} {δ : ℝ}
    (hHN : H ≤ N)
    (hR : ∀ h : ℕ, 1 ≤ h → h ≤ H →
      ‖∑ n ∈ Finset.range (N - h), f n * starRingEnd ℂ (f (n + h))‖ ≤ δ * (N : ℝ))
    (g : ℤ → ℂ) (hg_def : g = fun n => if 0 ≤ n ∧ n < (N : ℤ) then f n.toNat else 0)
    (Jset : Finset ℤ) (hJset_def : Jset = Finset.Ico (0 : ℤ) (↑N + ↑H))
    (Hset : Finset ℕ) (hHset_def : Hset = Finset.range (H + 1)) :
    ∀ h₁ ∈ Hset, ∀ h₂ ∈ Hset, h₁ ≠ h₂ →
      ‖∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂))‖ ≤ δ * ↑N := by
  intro h₁ hh₁ h₂ hh₂ hne
  have hh₁_mem : h₁ ∈ Finset.range (H + 1) := hHset_def ▸ hh₁
  have hh₂_mem : h₂ ∈ Finset.range (H + 1) := hHset_def ▸ hh₂
  have hh₁_le : h₁ ≤ H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh₁_mem)
  have hh₂_le : h₂ ≤ H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh₂_mem)
  -- Reduce to the case h₁ < h₂ by conjugation symmetry
  suffices hmain : ∀ a b : ℕ, a ∈ Hset → b ∈ Hset → a < b →
      ‖∑ j ∈ Jset, g (j - ↑a) * starRingEnd ℂ (g (j - ↑b))‖ ≤ δ * ↑N by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hmain h₁ h₂ hh₁ hh₂ hlt
    · rw [show (∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂))) =
          starRingEnd ℂ (∑ j ∈ Jset, g (j - ↑h₂) * starRingEnd ℂ (g (j - ↑h₁))) from by
            rw [map_sum]; apply Finset.sum_congr rfl; intro j _
            rw [map_mul, starRingEnd_self_apply, mul_comm]]
      rw [norm_starRingEnd_complex]
      exact hmain h₂ h₁ hh₂ hh₁ hgt
  intro h₁ h₂ hh₁ hh₂ hlt
  have hh₁_mem : h₁ ∈ Finset.range (H + 1) := hHset_def ▸ hh₁
  have hh₂_mem : h₂ ∈ Finset.range (H + 1) := hHset_def ▸ hh₂
  have hh₁_le : h₁ ≤ H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh₁_mem)
  have hh₂_le : h₂ ≤ H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh₂_mem)
  set ℓ := h₂ - h₁ with hℓ_def
  have hℓ_pos : 1 ≤ ℓ := by omega
  have hℓ_le : ℓ ≤ H := by omega
  -- Reindex the Jset sum to range(N-ℓ) sum via m = j - h₂
  have hsum_reindex : ∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂)) =
      ∑ m ∈ Finset.range (N - ℓ), f (m + ℓ) * starRingEnd ℂ (f m) := by
    have hNℓ : ℓ ≤ N := le_trans hℓ_le hHN
    set img := Finset.image (fun m : ℕ => (↑m + (h₂ : ℤ))) (Finset.range (N - ℓ))
    have himg_sub : img ⊆ Jset := by
      intro j hj; simp only [img, Finset.mem_image, Finset.mem_range] at hj
      obtain ⟨m, hm, rfl⟩ := hj; simp [hJset_def, Finset.mem_Ico]; omega
    rw [← Finset.sum_subset himg_sub (fun j _ hnj => by
      by_cases hsupp2 : 0 ≤ j - (h₂ : ℤ) ∧ j - (h₂ : ℤ) < ↑N
      · by_cases hsupp1 : 0 ≤ j - (h₁ : ℤ) ∧ j - (h₁ : ℤ) < ↑N
        · exfalso; apply hnj; simp only [img, Finset.mem_image, Finset.mem_range]
          refine ⟨(j - (h₂ : ℤ)).toNat, ?_, ?_⟩
          · zify [hNℓ]; rw [Int.toNat_of_nonneg hsupp2.1]; omega
          · rw [Int.toNat_of_nonneg hsupp2.1]; omega
        · have : g (j - ↑h₁) = 0 := by
            simp only [hg_def]; exact if_neg hsupp1
          simp [this]
      · push Not at hsupp2
        have : g (j - ↑h₂) = 0 := by
          simp only [hg_def]; split_ifs with hcond
          · exact absurd hcond.2 (not_lt.mpr (hsupp2 hcond.1))
          · rfl
        simp [this])]
    rw [Finset.sum_image (by intro a _ b _ (hab : (↑a : ℤ) + ↑h₂ = ↑b + ↑h₂); omega)]
    apply Finset.sum_congr rfl; intro m hm
    have hm_lt := Finset.mem_range.mp hm
    have hmN : m + ℓ < N := by omega
    simp only [show (↑m + (h₂ : ℤ) - ↑h₁) = ↑(m + ℓ) from by push_cast; omega,
                show (↑m + (h₂ : ℤ) - ↑h₂) = ↑m from by omega]
    simp only [hg_def, Int.natCast_nonneg, Nat.cast_lt, hmN, and_self, ite_true,
                Int.toNat_natCast, show m < N from by omega]
  rw [hsum_reindex]
  rw [show (∑ m ∈ Finset.range (N - ℓ), f (m + ℓ) * starRingEnd ℂ (f m)) =
      starRingEnd ℂ (∑ m ∈ Finset.range (N - ℓ),
        f m * starRingEnd ℂ (f (m + ℓ))) from by
      rw [map_sum]; apply Finset.sum_congr rfl; intro m _
      rw [map_mul, starRingEnd_self_apply, mul_comm]]
  rw [norm_starRingEnd_complex]
  exact hR ℓ hℓ_pos hℓ_le

/-- Aggregate off-diagonal bound: the total off-diagonal contribution to the
    energy is bounded by `H * (H+1) * δ * N`, using triangle inequality and
    the per-pair cross bound. -/
private theorem vdc_offdiag_bound {N H : ℕ} {δ : ℝ}
    (g : ℤ → ℂ)
    (Jset : Finset ℤ)
    (Hset : Finset ℕ) (hHset_def : Hset = Finset.range (H + 1))
    (hcross_bound : ∀ h₁ ∈ Hset, ∀ h₂ ∈ Hset, h₁ ≠ h₂ →
      ‖∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂))‖ ≤ δ * ↑N) :
    (∑ h₁ ∈ Hset, ∑ h₂ ∈ Hset.erase h₁,
      ∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂))).re ≤
      ↑H * (↑H + 1) * δ * ↑N := by
  calc (∑ h₁ ∈ Hset, ∑ h₂ ∈ Hset.erase h₁,
        ∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂))).re
      ≤ ‖∑ h₁ ∈ Hset, ∑ h₂ ∈ Hset.erase h₁,
        ∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂))‖ :=
        Complex.re_le_norm _
    _ ≤ ∑ h₁ ∈ Hset, ‖∑ h₂ ∈ Hset.erase h₁,
        ∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ h₁ ∈ Hset, ∑ h₂ ∈ Hset.erase h₁,
        ‖∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂))‖ :=
        Finset.sum_le_sum (fun h₁ _ => norm_sum_le _ _)
    _ ≤ ∑ h₁ ∈ Hset, ∑ _h₂ ∈ Hset.erase h₁, (δ * ↑N) := by
        apply Finset.sum_le_sum; intro h₁ hh₁
        apply Finset.sum_le_sum; intro h₂ hh₂
        exact hcross_bound h₁ hh₁ h₂ (Finset.mem_of_mem_erase hh₂)
          (Finset.ne_of_mem_erase hh₂).symm
    _ = ∑ h₁ ∈ Hset, ↑(Hset.erase h₁).card * (δ * ↑N) := by
        simp_rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ _h₁ ∈ Hset, ↑H * (δ * ↑N) := by
        apply Finset.sum_congr rfl; intro h₁ hh₁; congr 1
        have : (Hset.erase h₁).card = H := by
          rw [Finset.card_erase_of_mem hh₁, hHset_def, Finset.card_range, Nat.add_sub_cancel]
        exact_mod_cast this
    _ = ↑(H + 1) * (↑H * (δ * ↑N)) := by
        rw [Finset.sum_const, hHset_def, Finset.card_range, nsmul_eq_mul]
    _ = ↑H * (↑H + 1) * δ * ↑N := by push_cast; ring

/-- **Van der Corput bound** (proved): the finite Van der Corput inequality
    for bounded sequences with small autocorrelations.

    Proof uses the Iwaniec-Kowalski averaging trick: define w(j) = ∑_{h≤H} g(j-h)
    where g is the zero extension of f. Then ∑w = (H+1)S, and Cauchy-Schwarz gives
    (H+1)^2 * ‖S‖^2 ≤ (N+H) * ∑‖w(j)‖^2. The energy ∑‖w(j)‖^2 expands via double sum
    into autocorrelations and is bounded by (H+1)N(1+Hδ). -/
theorem van_der_corput_bound : VanDerCorputBound := by
  intro N f hf H hH1 hHN δ hδ hR
  have hN_pos : 0 < N := lt_of_lt_of_le hH1 hHN
  have hNr : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN_pos
  have hH1r : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  set S := ∑ n ∈ Finset.range N, f n with hS_def
  -- Step 1: Reduce to IK inequality via algebraic helper
  apply vdc_ik_reduction hH1r hδ
  -- Step 2: Set up windowed sums
  set g : ℤ → ℂ := fun n => if 0 ≤ n ∧ n < (N : ℤ) then f n.toNat else 0 with hg_def
  set w : ℤ → ℂ := fun j => ∑ h ∈ Finset.range (H + 1), g (j - ↑h) with hw_def
  set Jset := (Finset.Ico (0 : ℤ) (↑N + ↑H)) with hJset_def
  set Hset := Finset.range (H + 1) with hHset_def
  -- Step 3: Sum identity via helper
  have hsum_identity : ∑ j ∈ Jset, w j = (↑(H + 1) : ℂ) * S :=
    vdc_sum_identity g hg_def w hw_def Jset hJset_def S hS_def
  -- Step 4: Cauchy-Schwarz
  have hcard_Jset : Jset.card = N + H := by
    simp [hJset_def, Int.card_Ico]; omega
  have hCS : ‖∑ j ∈ Jset, w j‖ ^ 2 ≤ (↑(N + H) : ℝ) * ∑ j ∈ Jset, ‖w j‖ ^ 2 := by
    calc ‖∑ j ∈ Jset, w j‖ ^ 2
        ≤ (∑ j ∈ Jset, ‖w j‖) ^ 2 := by gcongr; exact norm_sum_le _ _
      _ = (∑ j ∈ Jset, 1 * ‖w j‖) ^ 2 := by simp
      _ ≤ (∑ _j ∈ Jset, (1 : ℝ) ^ 2) * (∑ j ∈ Jset, ‖w j‖ ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq Jset (fun _ => 1) (fun j => ‖w j‖)
      _ = (↑(N + H) : ℝ) * ∑ j ∈ Jset, ‖w j‖ ^ 2 := by simp [hcard_Jset]
  have hLHS : ((H : ℝ) + 1) ^ 2 * ‖S‖ ^ 2 = ‖∑ j ∈ Jset, w j‖ ^ 2 := by
    rw [hsum_identity, norm_mul, Complex.norm_natCast, sq, sq]; push_cast; ring
  -- Step 5: Energy bound
  suffices hEnergy : (∑ j ∈ Jset, ‖w j‖ ^ 2 : ℝ) ≤
      (↑H + 1) * ↑N * (1 + ↑H * δ) by
    rw [hLHS]
    calc ‖∑ j ∈ Jset, w j‖ ^ 2
        ≤ (↑(N + H) : ℝ) * ∑ j ∈ Jset, ‖w j‖ ^ 2 := hCS
      _ ≤ (↑(N + H) : ℝ) * ((↑H + 1) * ↑N * (1 + ↑H * δ)) := by gcongr
      _ ≤ (2 * (↑N : ℝ)) * ((↑H + 1) * ↑N * (1 + ↑H * δ)) := by
          gcongr; push_cast
          have : (H : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hHN
          linarith
      _ = 2 * ↑N * (↑H + 1) * ↑N * (1 + ↑H * δ) := by ring
  -- Step 6: Expand energy as double sum and split diagonal/off-diagonal
  have hnorm_sq_w : ∀ j : ℤ, (‖w j‖ ^ 2 : ℝ) =
      (∑ h₁ ∈ Hset, ∑ h₂ ∈ Hset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂))).re := by
    intro j
    rw [complex_norm_sq_eq_re_mul_conj (w j)]
    simp only [hw_def, map_sum, Finset.mul_sum, Finset.sum_mul]
    congr 1; rw [Finset.sum_comm]
  have henergy_expand : (∑ j ∈ Jset, ‖w j‖ ^ 2 : ℝ) =
      (∑ h₁ ∈ Hset, ∑ h₂ ∈ Hset,
        ∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂))).re := by
    simp_rw [hnorm_sq_w]; rw [Complex.re_sum]; simp_rw [Complex.re_sum]
    rw [Finset.sum_comm (s := Jset) (t := Hset)]
    simp_rw [Finset.sum_comm (s := Jset) (t := Hset)]
  rw [henergy_expand]
  have hsplit : ∑ h₁ ∈ Hset, ∑ h₂ ∈ Hset,
      ∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂)) =
      (∑ h₁ ∈ Hset, ∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₁))) +
      (∑ h₁ ∈ Hset, ∑ h₂ ∈ Hset.erase h₁,
        ∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro h₁ hh₁
    rw [← Finset.add_sum_erase Hset _ hh₁]
  rw [hsplit, Complex.add_re]
  -- Step 7: Apply diagonal and off-diagonal bounds via helpers
  have hdiag := vdc_diagonal_bound hf g hg_def Jset hJset_def Hset hHset_def
  have hcross := vdc_cross_bound hHN hR g hg_def Jset hJset_def Hset hHset_def
  have hoffdiag := vdc_offdiag_bound g Jset Hset hHset_def hcross
  linarith [show (↑H + 1) * ↑N + ↑H * (↑H + 1) * δ * ↑N =
      (↑H + 1) * ↑N * (1 + ↑H * δ) from by ring]


/-- The van der Corput inequality, un-wrapped. -/
theorem vanDerCorput_norm_sq_sum_le (N : ℕ) (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (H : ℕ) (hH1 : 1 ≤ H) (hHN : H ≤ N) (δ : ℝ) (hδ : 0 < δ)
    (hcorr : ∀ h : ℕ, 1 ≤ h → h ≤ H →
      ‖∑ n ∈ Finset.range (N - h), f n * starRingEnd ℂ (f (n + h))‖ ≤ δ * (N : ℝ)) :
    ‖∑ n ∈ Finset.range N, f n‖ ^ 2 ≤
      2 * (N : ℝ) ^ 2 / ((H : ℝ) + 1) + 2 * δ * (N : ℝ) ^ 2 :=
  van_der_corput_bound N f hf H hH1 hHN δ hδ hcorr
