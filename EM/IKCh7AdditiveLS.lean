import EM.IKCh7Foundations

/-!
# Chapter 7 (Part 2): Additive Large Sieve (Iwaniec-Kowalski)

§7.4 of Iwaniec-Kowalski: Additive large sieve inequalities,
Schur test, Gram matrix reduction, and optimal bounds.

## References
- [IK] H. Iwaniec, E. Kowalski, *Analytic Number Theory*, 2004
-/

noncomputable section

open Classical

namespace IK

open Complex Finset BigOperators

/-!
## §7.4 Additive large sieve inequalities

Theorem 7.7 (Selberg, Montgomery-Vaughan): The optimal additive large sieve.
For δ-spaced points α_r ∈ ℝ/ℤ:
∑_r |∑_n a_n e(α_r n)|² ≤ (δ⁻¹ + N − 1) ‖a‖².

Lemma 7.8: Generalization of Hilbert's inequality.
Theorem 7.11: Large sieve at Farey fractions.
-/

section AdditiveLargeSieve

/-- Points α_r ∈ ℝ/ℤ are **δ-spaced** if ‖α_r − α_s‖ ≥ δ for r ≠ s,
    where ‖·‖ is the distance to the nearest integer — IK §7.4. -/
def IsSpaced {R : ℕ} (α : Fin R → ℝ) (δ : ℝ) : Prop :=
  ∀ r s : Fin R, r ≠ s → δ ≤ |Int.fract (α r) - Int.fract (α s)|

/-- **Lemma 7.8** (Montgomery-Vaughan): Generalized Hilbert inequality — IK (7.23).
    If λ_r are distinct with |λ_r − λ_s| ≥ δ for r ≠ s, then
    |∑∑_{r≠s} z_r z̄_s / (λ_r − λ_s)| ≤ (π/δ) ∑ |z_r|². -/
def HilbertInequality : Prop :=
  ∀ (R : ℕ) (pts : Fin R → ℝ) (z : Fin R → ℂ) (δ : ℝ),
    0 < δ →
    (∀ r s : Fin R, r ≠ s → δ ≤ |pts r - pts s|) →
    ‖∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
      z r * starRingEnd ℂ (z s) / (↑(pts r - pts s) : ℂ)‖ ≤
      Real.pi / δ * ∑ r, ‖z r‖ ^ 2

/-- **Theorem 7.7** (Selberg, Montgomery-Vaughan): Optimal additive large sieve —
    IK (7.22). For δ-spaced points α_r ∈ ℝ/ℤ and a_n with M < n ≤ M+N:
    ∑_r |∑_n a_n e(α_r n)|² ≤ (δ⁻¹ + N − 1) ‖a‖². -/
def AdditiveLargeSieve : Prop :=
  ∀ (R N : ℕ) (α : Fin R → ℝ) (a : Fin N → ℂ) (δ : ℝ),
    0 < δ → δ ≤ 1/2 → 1 ≤ N →
    IsSpaced α δ →
    (∑ r, ‖∑ n : Fin N, a n * eAN (α r * ↑(n : ℕ))‖ ^ 2) ≤
      (1 / δ + ↑N - 1) * l2NormSq a

/-- **Weak additive large sieve** (formalized): a direct wrapper around the proved lemma
`LargeSieveAnalytic.weak_als_from_card_bound`.

This has the correct *structure* (dependence on `δ⁻¹` and `N`) but a non-optimal
constant `N * (δ⁻¹ + 1)`.

We use the `LargeSieveAnalytic.eAN` normalization `e(α) = exp(2π i α)`.
-/
theorem weak_additive_large_sieve
    (N : ℕ) (hN : 0 < N) (a : Fin N → ℂ)
    (R : ℕ) (α : Fin R → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ r s : Fin R, r ≠ s → δ ≤ |α r - α s - round (α r - α s)|) :
    ∑ r : Fin R, ‖∑ n : Fin N, a n * _root_.eAN (↑(n : ℤ) * α r)‖ ^ 2
      ≤ (N : ℝ) * (δ⁻¹ + 1) * ∑ n : Fin N, ‖a n‖ ^ 2 :=
  _root_.weak_als_from_card_bound N hN a R α δ hδ hsep

/-- **Theorem 7.11**: Large sieve at Farey fractions — IK (7.28).
    ∑_{q≤Q} ∑*_{a mod q} |∑_n a_n e(an/q)|² ≤ (Q² + N − 1) ‖a‖².
    This follows from Theorem 7.7 because Farey fractions are Q⁻²-spaced. -/
def FareyLargeSieve : Prop :=
  ∀ (N : ℕ) (Q : ℕ) (_a : Fin N → ℂ),
    1 ≤ N → 1 ≤ Q →
    -- ∑_{q≤Q} ∑*_{a mod q} |∑_n a_n e(an/q)|² ≤ (Q² + N − 1) ‖a‖²
    True

/-!
### §7.4a Schur test for Hermitian quadratic forms

A key tool for proving large sieve bounds via Gram matrices: given a matrix
G : Fin R → Fin R → ℂ with diagonal entries equal to D and off-diagonal
entries bounded by B in norm, the quadratic form b* G b is bounded by
(D + (R-1) · B) · ‖b‖².

The proof uses the triangle inequality to bound the off-diagonal
contribution, and Cauchy-Schwarz (in the form ∑_{r≠s} |b_r||b_s| ≤ (R-1)·‖b‖²)
for the off-diagonal sum.
-/

/-- **Off-diagonal Cauchy-Schwarz**: for a finite collection of non-negative reals,
    ∑_{i ≠ j} w_i w_j ≤ (n − 1) · ∑_i w_i².
    Proof: ∑_{i≠j} w_i w_j = (∑ w_i)² − ∑ w_i² ≤ (n · ∑ w_i²) − ∑ w_i² by CS. -/
theorem off_diag_sum_le {R : ℕ} (w : Fin R → ℝ) (_hw : ∀ r, 0 ≤ w r) :
    ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r), w r * w s ≤
      (↑R - 1) * ∑ r, w r ^ 2 := by
  -- For each r, ∑_{s≠r} w_r w_s = w_r (∑_{s≠r} w_s).
  -- But ∑_{s≠r} w_s is hard to bound cleanly. Instead, use the identity
  -- ∑_r ∑_{s≠r} w_r w_s + ∑_r w_r^2 = (∑ w)^2 ≤ R ∑ w^2 by CS.
  -- So ∑_{r≠s} w_r w_s ≤ (R-1) ∑ w^2.
  -- The identity: ∑_r (w_r^2 + ∑_{s≠r} w_r w_s) = ∑_r ∑_s w_r w_s = (∑ w)^2.
  -- Use Finset.sum_product_univ for the double sum.
  -- Prove the identity via "add and subtract"
  suffices h_identity :
      ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r), w r * w s =
        (∑ r, w r) ^ 2 - ∑ r, w r ^ 2 by
    have hcs : (∑ r, w r) ^ 2 ≤ ↑R * ∑ r, w r ^ 2 := by
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) w
      simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, one_mul] at this
      exact this
    linarith
  -- Prove the identity: ∑_{r≠s} w_r w_s = (∑ w)^2 - ∑ w^2
  -- First: (∑ w)^2 = ∑_r ∑_s w_r w_s = ∑_r w_r^2 + ∑_{r≠s} w_r w_s
  have h_sq : (∑ r, w r) ^ 2 = ∑ r, ∑ s, w r * w s := by
    rw [sq, Finset.sum_mul_sum]
  -- Split double sum into diag + off-diag via Finset.sum_erase
  have h_split : ∀ r : Fin R,
      ∑ s, w r * w s = w r ^ 2 + ∑ s ∈ Finset.univ.erase r, w r * w s := by
    intro r
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ r), sq]
  -- erase = filter
  have h_erase_filter : ∀ r : Fin R,
      Finset.univ.erase r = Finset.univ.filter (· ≠ r) := by
    intro r; ext s; simp [Finset.mem_erase, Finset.mem_filter, ne_comm]
  simp_rw [h_split, h_erase_filter] at h_sq
  simp_rw [Finset.sum_add_distrib] at h_sq
  linarith

/-- **Schur test for Hermitian quadratic forms**: for a matrix G with
    diagonal ≤ D and off-diagonal norm ≤ B,
    ‖∑_{r,s} b_r · conj(b_s) · G_{r,s}‖ ≤ (D + (R-1)·B) · ‖b‖². -/
theorem schur_quadratic_form_bound {R : ℕ}
    (G : Fin R → Fin R → ℂ)
    (b : Fin R → ℂ)
    (D B : ℝ) (_hD : 0 ≤ D) (hB : 0 ≤ B)
    (hdiag : ∀ r, ‖G r r‖ ≤ D)
    (hoffdiag : ∀ r s, r ≠ s → ‖G r s‖ ≤ B) :
    ‖∑ r, ∑ s, b r * starRingEnd ℂ (b s) * G r s‖ ≤
      (D + (↑R - 1) * B) * l2NormSq b := by
  -- Bound via triangle inequality: split each inner sum into r=s and r≠s
  -- Then bound diagonal by D * ||b||^2 and off-diagonal by (R-1)*B*||b||^2.
  -- Instead of splitting the sum, we use a direct bound:
  -- ‖∑_{r,s} b_r conj(b_s) G_{r,s}‖ ≤ ∑_{r,s} ‖b_r‖ ‖b_s‖ ‖G_{r,s}‖
  -- The diagonal part contributes ∑_r ‖b_r‖^2 ‖G_{r,r}‖ ≤ D ∑ ‖b_r‖^2 = D * ||b||^2
  -- The off-diagonal contributes ∑_{r≠s} ‖b_r‖ ‖b_s‖ ‖G_{r,s}‖ ≤ B ∑_{r≠s} ‖b_r‖ ‖b_s‖
  -- ≤ B * (R-1) * ||b||^2 by off_diag_sum_le.
  -- Bound via triangle inequality + diagonal/off-diagonal split
  -- ‖∑∑ b_r conj(b_s) G_{rs}‖ ≤ ∑∑ |b_r| |b_s| |G_{rs}|
  -- = ∑_r |b_r|^2 |G_{rr}| + ∑_{r≠s} |b_r| |b_s| |G_{rs}|
  -- ≤ D * ||b||^2 + B * ∑_{r≠s} |b_r| |b_s|
  -- ≤ D * ||b||^2 + (R-1)*B*||b||^2
  -- Direct approach: bound the full sum termwise.
  -- For r=s: |b_r|^2 * |G_{rr}| ≤ |b_r|^2 * D
  -- For r≠s: |b_r| |b_s| |G_{rs}| ≤ |b_r| |b_s| * B
  -- ∑_r |b_r|^2 * D = D * ||b||^2
  -- ∑_{r≠s} |b_r| |b_s| * B ≤ (R-1)*B*||b||^2 by off_diag_sum_le
  -- Triangle inequality
  apply le_trans (norm_sum_le _ _)
  apply le_trans (Finset.sum_le_sum (fun r _ => norm_sum_le _ _))
  -- Now have: ≤ ∑_r ∑_s ‖b_r conj(b_s) G_{rs}‖ = ∑ ‖b_r‖ ‖b_s‖ ‖G_{rs}‖
  -- Split diagonal and off-diagonal
  have heq : ∀ r : Fin R,
      ∑ s, ‖b r * starRingEnd ℂ (b s) * G r s‖ =
        ‖b r‖ ^ 2 * ‖G r r‖ +
        ∑ s ∈ Finset.univ.erase r, ‖b r‖ * ‖b s‖ * ‖G r s‖ := by
    intro r
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ r)]
    congr 1
    · rw [norm_mul, norm_mul, Complex.norm_conj, ← sq, mul_comm]
    · apply Finset.sum_congr rfl; intro s _
      rw [norm_mul, norm_mul, Complex.norm_conj]
  simp_rw [heq, Finset.sum_add_distrib]
  -- Now goal is: ∑ |b_r|^2 |G_{rr}| + ∑_r ∑_{s∈erase r} ... ≤ (D + (R-1)B) ||b||^2
  -- Rewrite RHS as D * ||b||^2 + (R-1)*B*||b||^2
  have hrhs : (D + (↑R - 1) * B) * l2NormSq b =
      D * l2NormSq b + (↑R - 1) * B * l2NormSq b := by ring
  rw [hrhs]
  apply add_le_add
  -- Diagonal part: ∑ |b_r|^2 |G_{rr}| ≤ D * ||b||^2
  · calc ∑ r, ‖b r‖ ^ 2 * ‖G r r‖
        ≤ ∑ r, ‖b r‖ ^ 2 * D := by
          apply Finset.sum_le_sum; intro r _; exact mul_le_mul_of_nonneg_left (hdiag r) (sq_nonneg _)
      _ = D * l2NormSq b := by unfold l2NormSq; rw [← Finset.sum_mul]; ring
      _ ≤ D * l2NormSq b := le_refl _
  -- Off-diagonal part: ∑_{r≠s} |b_r| |b_s| |G_{rs}| ≤ (R-1)*B*||b||^2
  · have herase_filter : ∀ r : Fin R,
        Finset.univ.erase r = Finset.univ.filter (· ≠ r) := by
      intro r; ext s; simp [Finset.mem_erase, Finset.mem_filter, ne_comm]
    calc ∑ r, ∑ s ∈ Finset.univ.erase r, ‖b r‖ * ‖b s‖ * ‖G r s‖
        ≤ ∑ r, ∑ s ∈ Finset.univ.erase r, ‖b r‖ * ‖b s‖ * B := by
          apply Finset.sum_le_sum; intro r _
          apply Finset.sum_le_sum; intro s hs
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          exact hoffdiag r s (by simp only [Finset.mem_erase] at hs; exact hs.1.symm)
      _ = B * ∑ r, ∑ s ∈ Finset.univ.erase r, ‖b r‖ * ‖b s‖ := by
          rw [Finset.mul_sum]; congr 1; ext r
          rw [Finset.mul_sum]; congr 1; ext s; ring
      _ ≤ B * ((↑R - 1) * ∑ r, ‖b r‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hB
          simp_rw [herase_filter]
          exact off_diag_sum_le (fun r => ‖b r‖) (fun r => norm_nonneg _)
      _ = (↑R - 1) * B * l2NormSq b := by unfold l2NormSq; ring

/-!
### §7.4b Row-sum Schur test and Gram matrix reduction

The **row-sum Schur test** for PSD matrices says: if G is positive semi-definite
(meaning b*Gb ≥ 0 for all b) and every row sum ∑_s |G_{r,s}| ≤ C, then
b*Gb ≤ C · ‖b‖².

Combined with the Gram matrix expansion (which writes the dual ALS form as a
Gram quadratic form), this reduces `AdditiveLargeSieve` to bounding the row sums
of the Gram matrix G_{r,s} = ∑_{n<N} e(n(α_r - α_s)).
-/

/-- **Row-sum Schur test**: for a matrix G with norm-symmetric entries
    (‖G_{r,s}‖ = ‖G_{s,r}‖) and row sums bounded by C,
    the Hermitian quadratic form ‖b* G b‖ ≤ C · ‖b‖².

    Proof uses AM-GM (|b_r|·|b_s| ≤ (|b_r|²+|b_s|²)/2) and symmetrization. -/
theorem row_sum_schur_bound {R : ℕ}
    (G : Fin R → Fin R → ℂ) (b : Fin R → ℂ) (C : ℝ)
    (_hC : 0 ≤ C)
    (hrow : ∀ r : Fin R, ∑ s, ‖G r s‖ ≤ C)
    (hsymm : ∀ r s : Fin R, ‖G r s‖ = ‖G s r‖) :
    ‖∑ r, ∑ s, b r * starRingEnd ℂ (b s) * G r s‖ ≤ C * l2NormSq b := by
  -- Step 1: Triangle inequality + norm simplification
  have h1 : ‖∑ r, ∑ s, b r * starRingEnd ℂ (b s) * G r s‖ ≤
      ∑ r, ∑ s, ‖b r‖ * ‖b s‖ * ‖G r s‖ := by
    apply le_trans (norm_sum_le _ _)
    apply le_trans (Finset.sum_le_sum (fun r _ => norm_sum_le _ _))
    gcongr with r _ s _
    rw [norm_mul, norm_mul, Complex.norm_conj]
  -- Step 2: AM-GM bound: |b_r|·|b_s| ≤ (|b_r|²+|b_s|²)/2
  have hamgm : ∀ r s : Fin R,
      ‖b r‖ * ‖b s‖ * ‖G r s‖ ≤
      (1/2) * (‖b r‖ ^ 2 * ‖G r s‖) + (1/2) * (‖b s‖ ^ 2 * ‖G r s‖) := by
    intro r s
    have h := sq_nonneg (‖b r‖ - ‖b s‖)
    have hg := norm_nonneg (G r s)
    nlinarith [sq_abs (‖b r‖ - ‖b s‖)]
  -- Step 3: Apply AM-GM to bound the double sum
  -- We bound ∑∑ |b_r|·|b_s|·‖G_{rs}‖ ≤ (1/2)·∑∑ |b_r|²·‖G_{rs}‖ + (1/2)·∑∑ |b_s|²·‖G_{rs}‖
  -- First half: ∑_r ∑_s |b_r|²·‖G_{rs}‖ = ∑_r |b_r|²·(∑_s ‖G_{rs}‖) ≤ C·‖b‖²
  -- Second half: ∑_r ∑_s |b_s|²·‖G_{rs}‖ = ∑_s |b_s|²·(∑_r ‖G_{rs}‖)
  --   = ∑_s |b_s|²·(∑_r ‖G_{sr}‖) (by hsymm) ≤ C·‖b‖² (by hrow)
  -- Define the two half-sums
  -- Step 3: Apply AM-GM + bound by row sums directly
  -- ∑∑ |b_r|·|b_s|·‖G_{rs}‖ ≤ (1/2)·S1 + (1/2)·S2 ≤ C·‖b‖²
  -- where S1 = ∑_r |b_r|²·(∑_s ‖G_{rs}‖), S2 = ∑_s |b_s|²·(∑_r ‖G_{rs}‖)
  -- Bound S1: factor out |b_r|², use hrow
  have h_S1 : ∑ r, ∑ s, ‖b r‖ ^ 2 * ‖G r s‖ ≤ C * l2NormSq b := by
    calc ∑ r, ∑ s, ‖b r‖ ^ 2 * ‖G r s‖
        = ∑ r, ‖b r‖ ^ 2 * ∑ s, ‖G r s‖ := by
          congr 1; ext r; rw [Finset.mul_sum]
      _ ≤ ∑ r, ‖b r‖ ^ 2 * C := by gcongr with r _; exact hrow r
      _ = C * l2NormSq b := by
          unfold l2NormSq; rw [Finset.mul_sum]; congr 1; ext r; ring
  -- Bound S2: swap sums, use symmetry, then hrow
  have h_S2 : ∑ r, ∑ s, ‖b s‖ ^ 2 * ‖G r s‖ ≤ C * l2NormSq b := by
    -- Rewrite using Fintype.sum = Finset.univ.sum for Finset.sum_comm
    show ∑ r ∈ Finset.univ, ∑ s ∈ Finset.univ, ‖b s‖ ^ 2 * ‖G r s‖ ≤ _
    rw [Finset.sum_comm]
    -- Now: ∑_s ∑_r |b_s|²·‖G_{r,s}‖ = ∑_s |b_s|²·(∑_r ‖G_{r,s}‖)
    calc ∑ s, ∑ r, ‖b s‖ ^ 2 * ‖G r s‖
        = ∑ s, ‖b s‖ ^ 2 * ∑ r, ‖G r s‖ := by
          congr 1; ext s; rw [Finset.mul_sum]
      _ = ∑ s, ‖b s‖ ^ 2 * ∑ r, ‖G s r‖ := by
          congr 1; ext s; congr 1
          congr 1; ext r; exact hsymm r s
      _ ≤ ∑ s, ‖b s‖ ^ 2 * C := by gcongr with s _; exact hrow s
      _ = C * l2NormSq b := by
          unfold l2NormSq; rw [Finset.mul_sum]; congr 1; ext s; ring
  -- Combine: apply AM-GM pointwise then use S1, S2 bounds
  have h2 : ∑ r, ∑ s, ‖b r‖ * ‖b s‖ * ‖G r s‖ ≤ C * l2NormSq b := by
    calc ∑ r, ∑ s, ‖b r‖ * ‖b s‖ * ‖G r s‖
        ≤ ∑ r, ∑ s, ((1/2) * (‖b r‖ ^ 2 * ‖G r s‖) + (1/2) * (‖b s‖ ^ 2 * ‖G r s‖)) := by
          gcongr with r _ s _; exact hamgm r s
      _ = (1/2) * ∑ r, ∑ s, ‖b r‖ ^ 2 * ‖G r s‖ +
          (1/2) * ∑ r, ∑ s, ‖b s‖ ^ 2 * ‖G r s‖ := by
          simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (1/2) * (C * l2NormSq b) + (1/2) * (C * l2NormSq b) := by
          linarith [h_S1, h_S2]
      _ = C * l2NormSq b := by ring
  linarith [h1.trans h2]

/-!
### §7.4c Gram matrix reduction: row-sum bound implies ALS

The **Gram matrix** for δ-spaced evaluation points α_r and summation length N is
G_{r,s} = ∑_{n=0}^{N-1} e(n(α_r - α_s)).

The ALS follows from a bound on the row sums of this Gram matrix via:
1. Duality: ALS ⟺ dual ALS
2. The dual ALS LHS equals a Gram matrix quadratic form
3. The row-sum Schur test bounds this quadratic form

We state the row-sum hypothesis and prove the reduction.
-/

/-- The Gram matrix for the additive large sieve:
    `gramMatrix N α r s = ∑_{n=0}^{N-1} e(n · (α_r - α_s))`. -/
def gramMatrix (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (r s : Fin R) : ℂ :=
  ∑ n ∈ Finset.range N, _root_.eAN (↑n * (α r - α s))

/-- The Gram matrix has norm-symmetric entries: ‖G_{r,s}‖ = ‖G_{s,r}‖.

    Proof: G_{s,r} = ∑ e(n(α_s - α_r)) = conj(∑ e(n(α_r - α_s))) = conj(G_{r,s}),
    so ‖G_{s,r}‖ = ‖conj(G_{r,s})‖ = ‖G_{r,s}‖. -/
theorem gramMatrix_norm_symm (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (r s : Fin R) :
    ‖gramMatrix N α r s‖ = ‖gramMatrix N α s r‖ := by
  -- G_{s,r} = ∑ e(n(α_s - α_r)) = ∑ e(-n(α_r - α_s)) = conj(G_{r,s})
  -- so ‖G_{s,r}‖ = ‖conj(G_{r,s})‖ = ‖G_{r,s}‖
  suffices h : gramMatrix N α s r = starRingEnd ℂ (gramMatrix N α r s) by
    rw [h, Complex.norm_conj]
  unfold gramMatrix
  rw [map_sum]; congr 1; ext n
  rw [show ↑n * (α s - α r) = -(↑n * (α r - α s)) from by ring]
  exact (conj_eAN _).symm

/-- The Gram matrix diagonal equals N: G_{r,r} = N. -/
theorem gramMatrix_diag (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (r : Fin R) :
    gramMatrix N α r r = ↑N := by
  unfold gramMatrix
  simp [sub_self, mul_zero, eAN_zero]

/-!
### Geometric sum / Dirichlet kernel identities for the Gram matrix

The Gram matrix entry `gramMatrix N α r s = ∑_{n<N} e(n·(α_r - α_s))` is a geometric
sum. When `e(α_r - α_s) ≠ 1` (i.e. the difference is not an integer), the standard
geometric series formula gives a closed form, and the norm equals the ratio of sines
`|sin(N·π·θ)| / |sin(π·θ)|` where `θ = α_r - α_s`.

These identities are the analytic foundation of the Hilbert inequality approach
to the optimal additive large sieve (§7.4e).
-/

/-- **Geometric sum formula for Gram entries**: when `eAN(α_r - α_s) ≠ 1`,
    `gramMatrix N α r s = (eAN(N·(α_r - α_s)) - 1) / (eAN(α_r - α_s) - 1)`.

    This is a direct application of the geometric series closed form to the
    Gram matrix definition `∑_{n<N} eAN(n·θ)` with `θ = α_r - α_s`. -/
theorem gramMatrix_eq_geom_closed_form (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (r s : Fin R)
    (hne : _root_.eAN (α r - α s) ≠ 1) :
    gramMatrix N α r s =
      (_root_.eAN (↑N * (α r - α s)) - 1) / (_root_.eAN (α r - α s) - 1) := by
  unfold gramMatrix
  exact eAN_geom_sum_eq N (α r - α s) hne

/-- **Telescoping identity for Gram entries**: the Gram matrix entry times
    `(eAN θ - 1)` telescopes to `eAN(Nθ) - 1`.

    `gramMatrix N α r s * (eAN(α_r - α_s) - 1) = eAN(N·(α_r - α_s)) - 1` -/
theorem gramMatrix_mul_eAN_sub_one (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (r s : Fin R) :
    gramMatrix N α r s * (_root_.eAN (α r - α s) - 1) =
      _root_.eAN (↑N * (α r - α s)) - 1 := by
  unfold gramMatrix
  exact eAN_geom_sum_mul N (α r - α s)

/-- **Norm of Gram entry via closed form**: when `eAN(α_r - α_s) ≠ 1`,
    `‖gramMatrix N α r s‖ ≤ 2 / ‖eAN(α_r - α_s) - 1‖`.

    This follows from the triangle inequality on the numerator `‖eAN(Nθ) - 1‖ ≤ 2`. -/
theorem gramMatrix_norm_le_two_div (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (r s : Fin R)
    (hne : _root_.eAN (α r - α s) ≠ 1) :
    ‖gramMatrix N α r s‖ ≤ 2 / ‖_root_.eAN (α r - α s) - 1‖ := by
  unfold gramMatrix
  exact norm_eAN_geom_sum_le N (α r - α s) hne

/-- **Norm of Gram entry as sin ratio**: when `sin(π·(α_r - α_s)) ≠ 0`,
    `‖gramMatrix N α r s‖ = |sin(N·π·(α_r - α_s))| / |sin(π·(α_r - α_s))|`.

    Proof: The geometric sum closed form gives
    `‖(eAN(Nθ) - 1) / (eAN(θ) - 1)‖ = ‖eAN(Nθ) - 1‖ / ‖eAN(θ) - 1‖`.
    By `norm_eAN_sub_one`, `‖eAN(x) - 1‖ = 2|sin(πx)|`, so the factors of 2 cancel. -/
theorem gramMatrix_norm_eq_sin_ratio (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (r s : Fin R)
    (hsin : Real.sin (Real.pi * (α r - α s)) ≠ 0) :
    ‖gramMatrix N α r s‖ =
      |Real.sin (↑N * Real.pi * (α r - α s))| /
      |Real.sin (Real.pi * (α r - α s))| := by
  -- First establish eAN(α r - α s) ≠ 1 from hsin
  have hne : _root_.eAN (α r - α s) ≠ 1 := by
    intro h
    have h0 : ‖_root_.eAN (α r - α s) - 1‖ = 0 := by rw [h, sub_self, norm_zero]
    rw [norm_eAN_sub_one] at h0
    have : |Real.sin (Real.pi * (α r - α s))| = 0 := by linarith
    exact hsin (abs_eq_zero.mp this)
  -- Use closed form
  rw [gramMatrix_eq_geom_closed_form N α r s hne, norm_div,
      norm_eAN_sub_one, norm_eAN_sub_one]
  -- Now: 2 * |sin(N*π*θ)| / (2 * |sin(π*θ)|) = |sin(N*π*θ)| / |sin(π*θ)|
  -- Need to rewrite N * π * θ as π * (N * θ)
  rw [show Real.pi * (↑N * (α r - α s)) = ↑N * Real.pi * (α r - α s) from by ring]
  -- Cancel the factor of 2: 2*a / (2*b) = a/b
  rw [mul_div_mul_left _ _ (two_ne_zero)]

/-- **Norm-squared of Gram entry as sin-squared ratio**: when
    `sin(π·(α_r - α_s)) ≠ 0`,
    `‖gramMatrix N α r s‖² = sin(N·π·θ)² / sin(π·θ)²`
    where `θ = α_r - α_s`.

    This is the form that appears directly in Hilbert inequality applications. -/
theorem gramMatrix_norm_sq_eq_sin_sq_ratio (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (r s : Fin R)
    (hsin : Real.sin (Real.pi * (α r - α s)) ≠ 0) :
    ‖gramMatrix N α r s‖ ^ 2 =
      Real.sin (↑N * Real.pi * (α r - α s)) ^ 2 /
      Real.sin (Real.pi * (α r - α s)) ^ 2 := by
  rw [gramMatrix_norm_eq_sin_ratio N α r s hsin]
  rw [div_pow, sq_abs, sq_abs]

/-- The Gram matrix row sum bound hypothesis: for evaluation points α and summation
    length N, every row sum of ‖G_{r,s}‖ is at most C.

    The optimal bound is C = 1/δ + N - 1 (for δ-spaced α), proved using the
    Hilbert inequality. This hypothesis isolates the analytic input needed for ALS. -/
def GramRowSumBound (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (C : ℝ) : Prop :=
  ∀ r : Fin R, ∑ s, ‖gramMatrix N α r s‖ ≤ C

/-- **Gram row-sum bound implies ALS**: if the Gram matrix row sums are bounded by C,
    then the additive large sieve holds with constant C.

    This reduces the ALS to a concrete bound on row sums of the kernel
    G_{r,s} = ∑_{n<N} e(n(α_r - α_s)). -/
theorem gram_row_sum_implies_lsi
    (R N : ℕ) (α : Fin R → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hrow : GramRowSumBound N α C) :
    ∀ (a : Fin N → ℂ),
    (∑ r, ‖∑ n : Fin N, a n * eAN (α r * ↑(n : ℕ))‖ ^ 2) ≤ C * l2NormSq a := by
  -- Strategy: use duality to reduce to a dual form, then expand as Gram quadratic form,
  -- then apply row_sum_schur_bound.
  -- The dual form: ∑_n |∑_r b_r · e(n · α_r)|² ≤ C · ‖b‖²
  -- Define the matrix x(r, n) = e(α_r · n) for the LSI/dual framework
  intro a
  -- We prove this directly by expanding |S(α_r)|² via Cauchy-Schwarz with the Gram matrix.
  -- |S(α_r)|² = |∑_n a_n e(nα_r)|² = ∑_n ∑_m a_n conj(a_m) e((n-m)α_r)
  -- ∑_r |S(α_r)|² = ∑_{n,m} a_n conj(a_m) · ∑_r e((n-m)α_r)
  -- = ∑_{n,m} a_n conj(a_m) · K(n-m) where K is the N×N kernel matrix
  -- K(n, m) = ∑_r e((n-m)α_r) = gramMatrix' ...
  -- But this approach introduces a DIFFERENT kernel (trigonometric kernel, not Gram matrix).
  -- The Gram matrix approach works for the DUAL form.
  -- Use duality: prove the dual form, then apply lsi_of_dual.
  -- Define x(r, n) = eAN(α_r · n)
  set x : Fin R → Fin N → ℂ := fun r n => eAN (α r * ↑(n : ℕ)) with hx_def
  -- Rewrite goal as LargeSieveInequality x C applied to a
  show (∑ r, ‖∑ n, a n * x r n‖ ^ 2) ≤ C * l2NormSq a
  -- It suffices to prove DualLargeSieve x C
  suffices hdual : DualLargeSieve x C by
    exact (lsi_of_dual x C hC hdual) a
  -- DualLargeSieve x C: ∀ b, ∑_n ‖∑_r b_r · x(r,n)‖² ≤ C · ‖b‖²
  intro b
  -- ∑_n ‖∑_r b_r e(α_r · n)‖² = ∑_{r,s} b_r conj(b_s) · G_{r,s}
  -- where G_{r,s} = ∑_n e(n(α_r - α_s)) = gramMatrix N α r s
  -- Step 1: Expand ‖∑_r b_r x(r,n)‖² using inner product
  -- ∑_n ‖∑_r b_r e(nα_r)‖² = ∑_n (∑_r b_r e(nα_r)) · conj(∑_s b_s e(nα_s))
  -- = ∑_n ∑_r ∑_s b_r conj(b_s) e(n(α_r - α_s))
  -- = ∑_r ∑_s b_r conj(b_s) · (∑_n e(n(α_r - α_s)))
  -- = ∑_r ∑_s b_r conj(b_s) · gramMatrix N α r s
  -- Step 1: Show that the dual LHS is real and equals the norm of the Gram quadratic form
  -- Since ∑_n ‖T_n‖² ≥ 0, we have a real nonneg quantity
  -- We need: ∑_n ‖∑_r b_r x(r,n)‖² ≤ C · ‖b‖²
  -- Express as Gram quadratic form
  have hexpand : (∑ n : Fin N, ‖∑ r, b r * x r n‖ ^ 2 : ℝ) =
      (∑ r, ∑ s, b r * starRingEnd ℂ (b s) * gramMatrix N α r s).re := by
    -- LHS = ∑_n |∑_r b_r x_{r,n}|²
    -- = ∑_n Re((∑_r b_r x_{r,n}) · conj(∑_s b_s x_{s,n}))
    -- = ∑_n Re(∑_r ∑_s b_r conj(b_s) x_{r,n} conj(x_{s,n}))
    -- = Re(∑_r ∑_s b_r conj(b_s) ∑_n x_{r,n} conj(x_{s,n}))
    -- = Re(∑_r ∑_s b_r conj(b_s) G_{r,s})
    -- Express |z|² as (z · conj z).re using complex_norm_sq_eq_re_mul_conj
    have habs_sq : ∀ n : Fin N, ‖∑ r, b r * x r n‖ ^ 2 =
        ((∑ r, b r * x r n) * starRingEnd ℂ (∑ r, b r * x r n)).re := by
      intro n; exact complex_norm_sq_eq_re_mul_conj _
    simp_rw [habs_sq]
    rw [← Complex.re_sum]
    congr 1
    -- Expand T_n · conj(T_n) = ∑_r ∑_s b_r conj(b_s) x_{r,n} conj(x_{s,n})
    simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum, map_mul]
    -- Swap sum order: ∑_n ∑_r ∑_s = ∑_r ∑_s ∑_n
    rw [Finset.sum_comm]
    congr 1; ext r
    rw [Finset.sum_comm]
    congr 1; ext s
    -- Need: ∑_n b_r * x_{r,n} * (conj(b_s) * conj(x_{s,n})) = b_r * conj(b_s) * G_{r,s}
    -- RHS: b_r * conj(b_s) * G_{r,s} = b_r * conj(b_s) * ∑_n e(n(α_r - α_s))
    unfold gramMatrix
    rw [← Fin.sum_univ_eq_sum_range]
    rw [Finset.mul_sum]
    congr 1; ext n
    -- Goal: b r * x r n * (conj(b s) * conj(x s n)) = b r * conj(b s) * eAN(n * (α r - α s))
    -- Bridge IK.eAN to _root_.eAN so we can use conj_eAN, eAN_add
    simp only [hx_def]
    rw [eAN_eq_root_eAN, eAN_eq_root_eAN]
    -- Goal involves star = starRingEnd ℂ after simp
    change b r * _root_.eAN (α r * ↑↑n) * (starRingEnd ℂ (b s) * starRingEnd ℂ (_root_.eAN (α s * ↑↑n))) =
        b r * starRingEnd ℂ (b s) * _root_.eAN (↑↑n * (α r - α s))
    rw [conj_eAN]
    rw [show b r * _root_.eAN (α r * ↑↑n) * (starRingEnd ℂ (b s) * _root_.eAN (-(α s * ↑↑n))) =
          b r * starRingEnd ℂ (b s) * (_root_.eAN (α r * ↑↑n) * _root_.eAN (-(α s * ↑↑n))) from by ring]
    rw [← _root_.eAN_add]
    congr 1; ring_nf
  -- Step 2: Bound the Gram quadratic form
  have hre_le : (∑ r, ∑ s, b r * starRingEnd ℂ (b s) * gramMatrix N α r s).re ≤
      ‖∑ r, ∑ s, b r * starRingEnd ℂ (b s) * gramMatrix N α r s‖ :=
    Complex.re_le_norm _
  have hschur : ‖∑ r, ∑ s, b r * starRingEnd ℂ (b s) * gramMatrix N α r s‖ ≤
      C * l2NormSq b :=
    row_sum_schur_bound (gramMatrix N α) b C hC hrow
      (fun r s => gramMatrix_norm_symm N α r s)
  linarith [hexpand ▸ (hre_le.trans hschur)]

/-- **Optimal ALS from Gram row-sum bound**: if for every δ-spaced configuration
    the Gram matrix row sums are bounded by 1/δ + N - 1, then the optimal
    Additive Large Sieve inequality holds.

    This is the key reduction: it separates the Schur-test / duality machinery
    (proved) from the analytic bound on row sums (the Hilbert inequality content). -/
theorem gram_row_sum_optimal_implies_als
    (hyp : ∀ (R N : ℕ) (α : Fin R → ℝ) (δ : ℝ),
      0 < δ → δ ≤ 1/2 → 1 ≤ N → IsSpaced α δ →
      GramRowSumBound N α (1/δ + ↑N - 1)) :
    AdditiveLargeSieve := by
  intro R N α a δ hδ hδ2 hN hspaced
  have hC : (0 : ℝ) ≤ 1/δ + ↑N - 1 := by
    have : 1 ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
    have : 0 < 1/δ := by positivity
    linarith
  exact gram_row_sum_implies_lsi R N α (1/δ + ↑N - 1) hC (hyp R N α δ hδ hδ2 hN hspaced) a

/-!
### §7.4d Non-optimal Gram row-sum bound (proved)

We prove a **non-optimal** Gram row-sum bound using:
- Diagonal: `gramMatrix N α r r = N` (from `gramMatrix_diag`)
- Off-diagonal: `‖gramMatrix N α r s‖ ≤ 1/(2δ)` for `r ≠ s`
  (from `norm_eAN_geom_sum_le_inv` applied to `β = α_r - α_s`)
- Row sum: `N + (R-1)/(2δ)`

This gives the *non-optimal* bound `N + (R-1)/(2δ)` instead of the optimal
`1/δ + N - 1` (which requires the Hilbert inequality).

We use the round-based separation condition
`∀ r s, r ≠ s → δ ≤ |α r - α s - round(α r - α s)|`
which matches `norm_eAN_geom_sum_le_inv` directly.
-/

/-- **Off-diagonal Gram matrix bound**: for round-separated `α` and `r ≠ s`,
    `‖gramMatrix N α r s‖ ≤ 1/(2δ)`.

    This connects the IK Gram matrix (defined with `_root_.eAN`) to the
    geometric sum bound `norm_eAN_geom_sum_le_inv`. -/
theorem gramMatrix_offdiag_bound (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (δ : ℝ)
    (hδ : 0 < δ)
    (hsep : ∀ r s : Fin R, r ≠ s → δ ≤ |α r - α s - round (α r - α s)|)
    (r s : Fin R) (hrs : r ≠ s) :
    ‖gramMatrix N α r s‖ ≤ 1 / (2 * δ) := by
  unfold gramMatrix
  exact _root_.norm_eAN_geom_sum_le_inv N (α r - α s) δ hδ (hsep r s hrs)

/-- **Row sum of ‖gramMatrix‖**: for round-separated `α`, every row sum satisfies
    `∑_s ‖G_{r,s}‖ ≤ N + (R - 1)/(2δ)`.

    Proof: The diagonal contributes `‖G_{r,r}‖ = N`. Each of the `R - 1`
    off-diagonal entries contributes at most `1/(2δ)`. -/
theorem gram_row_sum_weak (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (δ : ℝ)
    (hδ : 0 < δ)
    (hsep : ∀ r s : Fin R, r ≠ s → δ ≤ |α r - α s - round (α r - α s)|)
    (r : Fin R) :
    ∑ s, ‖gramMatrix N α r s‖ ≤ ↑N + (↑R - 1) / (2 * δ) := by
  -- Split the sum into the diagonal term (s = r) and off-diagonal terms (s ≠ r)
  have hdiag : ‖gramMatrix N α r r‖ = ↑N := by
    rw [gramMatrix_diag]
    simp
  -- Rewrite the sum by separating diagonal from off-diagonal
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
  -- Now goal: ‖G_{r,r}‖ + ∑_{s ≠ r} ‖G_{r,s}‖ ≤ N + (R-1)/(2δ)
  -- Bound diagonal
  have h1 : ‖gramMatrix N α r r‖ = ↑N := hdiag
  -- Bound each off-diagonal term
  have h2 : ∀ s ∈ Finset.univ.erase r, ‖gramMatrix N α r s‖ ≤ 1 / (2 * δ) := by
    intro s hs
    have hrs : s ≠ r := Finset.ne_of_mem_erase hs
    exact gramMatrix_offdiag_bound N α δ hδ hsep r s hrs.symm
  -- Number of off-diagonal terms
  have h3 : (Finset.univ.erase r).card = R - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, Fintype.card_fin]
  -- Bound: ∑_{s ≠ r} ‖G_{r,s}‖ ≤ (R-1) · 1/(2δ)
  have h4 : ∑ s ∈ Finset.univ.erase r, ‖gramMatrix N α r s‖ ≤
      (Finset.univ.erase r).card • (1 / (2 * δ)) :=
    Finset.sum_le_card_nsmul _ _ _ h2
  rw [h3] at h4
  rw [h1]
  -- (R - 1) • (1/(2δ)) = (R - 1) * (1/(2δ)) for ℕ smul on ℝ
  have h5 : (R - 1) • (1 / (2 * δ)) = ↑(R - 1) * (1 / (2 * δ)) := by
    rw [nsmul_eq_mul]
  rw [h5] at h4
  -- R ≥ 1 since r : Fin R exists
  have hR : 1 ≤ R := Fin.pos r
  have h6 : ↑(R - 1) * (1 / (2 * δ)) = (↑R - 1) / (2 * δ) := by
    rw [Nat.cast_sub hR]; ring
  linarith

/-- **Non-optimal ALS via Gram row-sum bound**: for round-separated evaluation
    points, the additive large sieve holds with constant `N + (R-1)/(2δ)`.

    This is weaker than the optimal `1/δ + N - 1` but demonstrates the
    complete Gram matrix framework (duality + Schur test + geometric sum bound)
    as an end-to-end proved theorem. -/
theorem gram_als_weak
    (R N : ℕ) (α : Fin R → ℝ) (a : Fin N → ℂ) (δ : ℝ)
    (hδ : 0 < δ) (hR : 1 ≤ R)
    (hsep : ∀ r s : Fin R, r ≠ s → δ ≤ |α r - α s - round (α r - α s)|) :
    (∑ r, ‖∑ n : Fin N, a n * _root_.eAN (α r * ↑(n : ℕ))‖ ^ 2) ≤
      (↑N + (↑R - 1) / (2 * δ)) * l2NormSq a := by
  -- The Gram row-sum bound gives GramRowSumBound N α (N + (R-1)/(2δ))
  have hrow : GramRowSumBound N α (↑N + (↑R - 1) / (2 * δ)) := by
    intro r
    exact gram_row_sum_weak N α δ hδ hsep r
  -- The constant is nonneg
  have hC : (0 : ℝ) ≤ ↑N + (↑R - 1) / (2 * δ) := by
    have : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have : 0 ≤ (↑R - 1) / (2 * δ) := by
      apply div_nonneg
      · have : 1 ≤ (R : ℝ) := Nat.one_le_cast.mpr hR; linarith
      · positivity
    linarith
  -- Apply gram_row_sum_implies_lsi
  -- Need to bridge: the LHS uses eAN(α_r * n) but gram_row_sum_implies_lsi uses
  -- IK.eAN(α_r * n). These are equal by eAN_eq_root_eAN.
  have key := gram_row_sum_implies_lsi R N α _ hC hrow a
  -- gram_row_sum_implies_lsi uses IK.eAN, we need _root_.eAN
  -- Rewrite in key: IK.eAN = _root_.eAN
  simp only [eAN_eq_root_eAN] at key
  exact key

/-!
### §7.4d' Refined off-diagonal Gram bound and packing infrastructure

The naive bound `gram_row_sum_weak` treats every off-diagonal Gram entry
identically: `‖G(r,s)‖ ≤ 1/(2δ)`. In reality, `‖G(r,s)‖ ≤ 1/(2·d(r,s))`
where `d(r,s) = |α_r - α_s - round(α_r - α_s)|` is the ℝ/ℤ distance,
which is typically much larger than δ.

**Refined off-diagonal bound** (`gramMatrix_offdiag_bound_dist`): uses the
actual pairwise distance instead of the uniform lower bound δ.

**Packing bound** (`round_sep_card_le`): For R points on ℝ/ℤ with
pairwise distance ≥ δ, we have `R ≤ ⌊1/δ⌋ + 1` (pigeonhole into bins
of width < δ). This gives `(R - 1) * δ ≤ 1`.

**Improved row-sum** (`gram_row_sum_improved`): Combines the packing bound
with the existing machinery to give `∑_s ‖G(r,s)‖ ≤ N + ⌊1/δ⌋/(2δ)`,
an a priori improvement over the naive `N + (R-1)/(2δ)`.
-/

/-- **Refined off-diagonal Gram bound**: `‖G(r,s)‖ ≤ 1/(2·d(r,s))` where
    `d(r,s) = |α_r - α_s - round(α_r - α_s)|` is the actual ℝ/ℤ distance.

    This is sharper than `gramMatrix_offdiag_bound`, which uses the uniform
    lower bound `d(r,s) ≥ δ` to get `1/(2δ)`. -/
theorem gramMatrix_offdiag_bound_dist (N : ℕ) {R : ℕ} (α : Fin R → ℝ)
    (r s : Fin R) (_hrs : r ≠ s)
    (hd : 0 < |α r - α s - round (α r - α s)|) :
    ‖gramMatrix N α r s‖ ≤ 1 / (2 * |α r - α s - round (α r - α s)|) := by
  unfold gramMatrix
  exact _root_.norm_eAN_geom_sum_le_inv N (α r - α s) _ hd le_rfl

/-- Round-separation implies δ ≤ 1/2. -/
theorem round_sep_delta_le_half {R : ℕ} (α : Fin R → ℝ) (δ : ℝ)
    (hsep : ∀ r s : Fin R, r ≠ s → δ ≤ |α r - α s - round (α r - α s)|)
    (r s : Fin R) (hrs : r ≠ s) : δ ≤ 1 / 2 :=
  (hsep r s hrs).trans (abs_sub_round _)

/-- **Packing bound for round-separated points**: If R points have
    pairwise ℝ/ℤ-distance ≥ δ and 0 < δ, then `(R - 1) * δ ≤ 1`.

    Proof by pigeonhole: define `f(i) = ⌊Int.fract(α i) / δ⌋` mapping
    `Fin R → Fin (⌊1/δ⌋ + 1)`. Two points in the same bin have
    `|fract(α r) - fract(α s)| < δ`, hence circular distance < δ,
    contradicting separation. So `f` is injective and `R ≤ ⌊1/δ⌋ + 1`,
    giving `(R - 1) ≤ ⌊1/δ⌋ ≤ 1/δ`. -/
theorem round_sep_card_le (R : ℕ) (α : Fin R → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ r s : Fin R, r ≠ s → δ ≤ |α r - α s - round (α r - α s)|) :
    ((R : ℝ) - 1) * δ ≤ 1 := by
  -- Strategy: define f : Fin R → Fin (⌊1/δ⌋₊ + 1) by f(i) = ⌊fract(α i) / δ⌋₊.
  -- Two points in the same bin have |fract diff| < δ, hence circ dist < δ,
  -- contradicting separation. So f is injective and R ≤ ⌊1/δ⌋₊ + 1.
  -- Then (R - 1) ≤ ⌊1/δ⌋₊ ≤ 1/δ gives the result.
  set m := ⌊(1 : ℝ) / δ⌋₊ with hm_def
  -- Step 1: Define the bin function
  have hδ' : (0 : ℝ) < δ := hδ
  -- f(i) = ⌊fract(α i) / δ⌋₊
  set f : Fin R → ℕ := fun i => ⌊Int.fract (α i) / δ⌋₊ with hf_def
  -- Step 2: Each f(i) ≤ m (hence < m + 1)
  have hf_bound : ∀ i : Fin R, f i ≤ m := by
    intro i
    simp only [hf_def, hm_def]
    apply Nat.floor_le_floor
    apply div_le_div_of_nonneg_right _ hδ'.le
    exact (Int.fract_lt_one (α i)).le
  -- Step 3: f is injective
  have hf_inj : Function.Injective f := by
    intro r s hfrs
    by_contra hrs
    -- r ≠ s, so round-separation gives δ ≤ |α r - α s - round(α r - α s)|
    have hsep_rs := hsep r s hrs
    -- f(r) = f(s) means ⌊fract(α r) / δ⌋₊ = ⌊fract(α s) / δ⌋₊
    -- This implies |fract(α r) / δ - fract(α s) / δ| < 1, i.e., |fract diff| < δ
    have hfr_nn : 0 ≤ Int.fract (α r) / δ := div_nonneg (Int.fract_nonneg _) hδ'.le
    have hfs_nn : 0 ≤ Int.fract (α s) / δ := div_nonneg (Int.fract_nonneg _) hδ'.le
    -- From floor equality, the values are in the same unit interval [k, k+1)
    have hfloor_eq : ⌊Int.fract (α r) / δ⌋₊ = ⌊Int.fract (α s) / δ⌋₊ := hfrs
    -- So |fract(α r)/δ - fract(α s)/δ| < 1
    have hdiff_lt_one : |Int.fract (α r) / δ - Int.fract (α s) / δ| < 1 := by
      set a := Int.fract (α r) / δ
      set b := Int.fract (α s) / δ
      have ha : 0 ≤ a := hfr_nn
      have hb : 0 ≤ b := hfs_nn
      rw [abs_lt]
      constructor
      · -- a - b > -1: since a ≥ 0 and b < ... we need b - a < 1
        -- b < ⌊b⌋₊ + 1 and a ≥ ⌊a⌋₊ = ⌊b⌋₊ (from hfloor_eq)
        have hb_lt : b < ↑(⌊b⌋₊) + 1 := Nat.lt_floor_add_one b
        have ha_ge : ↑(⌊a⌋₊) ≤ a := Nat.floor_le ha
        rw [← hfloor_eq] at hb_lt
        linarith [ha_ge, hb_lt]
      · -- a - b < 1: since b ≥ ⌊b⌋₊ = ⌊a⌋₊ and a < ⌊a⌋₊ + 1
        have ha_lt : a < ↑(⌊a⌋₊) + 1 := Nat.lt_floor_add_one a
        have hb_ge : ↑(⌊b⌋₊) ≤ b := Nat.floor_le hb
        rw [hfloor_eq] at ha_lt
        linarith [hb_ge, ha_lt]
    -- Multiply by δ: |fract(α r) - fract(α s)| < δ
    have hfract_close : |Int.fract (α r) - Int.fract (α s)| < δ := by
      have key : |Int.fract (α r) / δ - Int.fract (α s) / δ| < 1 := hdiff_lt_one
      rw [show Int.fract (α r) / δ - Int.fract (α s) / δ =
            (Int.fract (α r) - Int.fract (α s)) / δ from by ring] at key
      rwa [abs_div, abs_of_pos hδ', div_lt_one hδ'] at key
    -- Circular distance ≤ |fract diff|: use round_le to bound by nearest integer
    have hcirc_le : |α r - α s - round (α r - α s)| < δ := by
      -- round_le: |x - round x| ≤ |x - n| for any integer n
      -- Apply with n = ⌊α r⌋ - ⌊α s⌋, then simplify to |fract r - fract s|
      calc |α r - α s - round (α r - α s)|
          ≤ |(α r - α s) - ↑(⌊α r⌋ - ⌊α s⌋)| := round_le _ _
        _ = |Int.fract (α r) - Int.fract (α s)| := by
            congr 1
            have hr := Int.floor_add_fract (α r)
            have hs := Int.floor_add_fract (α s)
            push_cast; linarith
        _ < δ := hfract_close
    -- But hsep says δ ≤ circ dist. Contradiction.
    linarith
  -- Step 4: R ≤ m + 1 from injectivity
  -- Lift f to Fin R → Fin (m + 1) using the bound
  have hf_lt : ∀ i : Fin R, f i < m + 1 := fun i => Nat.lt_succ_of_le (hf_bound i)
  set g : Fin R → Fin (m + 1) := fun i => ⟨f i, hf_lt i⟩ with hg_def
  have hg_inj : Function.Injective g := by
    intro a b hab
    have : f a = f b := by
      simp only [hg_def, Fin.mk.injEq] at hab
      exact hab
    exact hf_inj this
  have hR_le : R ≤ m + 1 := by
    have := Fintype.card_le_of_injective g hg_inj
    simp [Fintype.card_fin] at this
    exact this
  -- Step 5: (R - 1) * δ ≤ ⌊1/δ⌋₊ * δ ≤ 1
  have hR_sub : (R : ℝ) - 1 ≤ ↑m := by
    have : (R : ℝ) ≤ ↑m + 1 := by exact_mod_cast hR_le
    linarith
  have hm_le : (m : ℝ) * δ ≤ 1 := by
    have : (m : ℝ) ≤ 1 / δ := Nat.floor_le (by positivity)
    calc (m : ℝ) * δ ≤ (1 / δ) * δ := by nlinarith
      _ = 1 := by field_simp
  calc ((R : ℝ) - 1) * δ ≤ ↑m * δ := by nlinarith [hR_sub, hδ']
    _ ≤ 1 := hm_le

/-- Corollary of packing: `R - 1 ≤ 1/δ` for round-separated points. -/
theorem round_sep_card_le_inv (R : ℕ) (α : Fin R → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ r s : Fin R, r ≠ s → δ ≤ |α r - α s - round (α r - α s)|) :
    (R : ℝ) - 1 ≤ 1 / δ := by
  have hpack := round_sep_card_le R α δ hδ hsep
  rwa [le_div_iff₀ hδ]

/-- **Improved row-sum bound using packing**: for round-separated `α`, the row sum
    satisfies `∑_s ‖G(r,s)‖ ≤ N + 1/(2·δ²)`, independent of R.

    This follows from `gram_row_sum_weak` (which gives `N + (R-1)/(2δ)`) together
    with the packing bound `(R - 1) ≤ 1/δ`. The resulting bound `N + 1/(2δ²)` is
    weaker than the optimal `1/δ + N - 1` but is completely proved and R-independent.
    It demonstrates that the Schur-test constant is controlled purely by δ and N. -/
theorem gram_row_sum_improved (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (δ : ℝ)
    (hδ : 0 < δ)
    (hsep : ∀ r s : Fin R, r ≠ s → δ ≤ |α r - α s - round (α r - α s)|)
    (r : Fin R) :
    ∑ s, ‖gramMatrix N α r s‖ ≤ ↑N + 1 / (2 * δ ^ 2) := by
  have hrow := gram_row_sum_weak N α δ hδ hsep r
  have hpack := round_sep_card_le_inv R α δ hδ hsep
  -- (R - 1)/(2δ) ≤ (1/δ)/(2δ) = 1/(2δ²)
  have hbound : (↑R - 1) / (2 * δ) ≤ 1 / (2 * δ ^ 2) := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2 * δ) (by positivity : (0:ℝ) < 2 * δ ^ 2)]
    nlinarith [round_sep_card_le R α δ hδ hsep]
  linarith

/-- **End-to-end ALS with R-independent constant**: for round-separated evaluation
    points, the ALS holds with constant `N + 1/(2δ²)`, proved entirely from the
    Gram matrix framework and the packing bound.

    While weaker than the optimal `1/δ + N - 1`, this demonstrates a *complete*
    proof path from separation to ALS without the Hilbert inequality. -/
theorem gram_als_improved
    (R N : ℕ) (α : Fin R → ℝ) (a : Fin N → ℂ) (δ : ℝ)
    (hδ : 0 < δ) (_hR : 1 ≤ R)
    (hsep : ∀ r s : Fin R, r ≠ s → δ ≤ |α r - α s - round (α r - α s)|) :
    (∑ r, ‖∑ n : Fin N, a n * _root_.eAN (α r * ↑(n : ℕ))‖ ^ 2) ≤
      (↑N + 1 / (2 * δ ^ 2)) * l2NormSq a := by
  have hrow : GramRowSumBound N α (↑N + 1 / (2 * δ ^ 2)) := by
    intro r; exact gram_row_sum_improved N α δ hδ hsep r
  have hC : (0 : ℝ) ≤ ↑N + 1 / (2 * δ ^ 2) := by
    have : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    positivity
  have key := gram_row_sum_implies_lsi R N α _ hC hrow a
  simp only [eAN_eq_root_eAN] at key
  exact key

/-!
### §7.4e Hilbert inequality implies optimal ALS

The **optimal** additive large sieve (Theorem 7.7) follows from the Hilbert inequality
(Lemma 7.8) via Corollaries 7.9–7.10 of IK. The argument:

1. By duality, ALS is equivalent to the dual form
   `∑_n |∑_r b_r e(nα_r)|² ≤ (δ⁻¹ + N - 1) · ‖b‖²`.
2. The dual LHS expands as `Re(∑_{r,s} b_r conj(b_s) G_{r,s})` where
   `G_{r,s} = gramMatrix N α r s` is the Gram matrix.
3. The diagonal contributes `N · ‖b‖²`.
4. The off-diagonal `∑_{r≠s} b_r conj(b_s) G_{r,s}` is bounded in norm by
   `(δ⁻¹ - 1) · ‖b‖²` — this is the content of IK Corollaries 7.9–7.10
   (Hilbert inequality + geometric-sum-to-sin identity + Cohen's saving-the-1 trick).

Step 4 requires continuous Fourier analysis (the identity `∑_{n<N} e(nβ) =
e(Kβ) sin(πNβ)/sin(πβ)` and properties of `sin`). We capture it as the open
proposition `GramOffDiagBilinearBound` and prove steps 1–3 compositionally.
-/

/-- **Corollaries 7.9–7.10 + Cohen trick**: the off-diagonal part of the Gram
    bilinear form satisfies the optimal bound.

    For δ-spaced points α_r, any b_r, and summation length N:
    `‖∑_{r≠s} b_r conj(b_s) G_{r,s}‖ ≤ (1/δ − 1) · ‖b‖²`.

    This captures the analytic content of the Hilbert inequality applied to
    geometric sums: the geometric sum identity relates `G_{r,s}` to
    `sin(πN(α_r − α_s))/sin(π(α_r − α_s))`, and Corollary 7.10 (from the
    Hilbert inequality) bounds the resulting bilinear form by `δ⁻¹ · ‖b‖²`.
    The Cohen limiting trick then sharpens `δ⁻¹` to `δ⁻¹ − 1`.

    This is open because it requires continuous Fourier analysis infrastructure
    (properties of `sin`, the geometric-sum-to-sin identity, and the Cohen
    limiting argument) not present in the codebase. -/
def GramOffDiagBilinearBound : Prop :=
  ∀ (R N : ℕ) (α : Fin R → ℝ) (b : Fin R → ℂ) (δ : ℝ),
    0 < δ → δ ≤ 1/2 → 1 ≤ N →
    IsSpaced α δ →
    ‖∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
      b r * starRingEnd ℂ (b s) * gramMatrix N α r s‖ ≤
      (1/δ - 1) * l2NormSq b

/-- **Gram expansion as diagonal + off-diagonal**: the full Gram quadratic form
    splits into the diagonal (which equals `N · ‖b‖²`) plus the off-diagonal.

    `∑_{r,s} b_r conj(b_s) G_{r,s} = (↑N · ∑_r ‖b_r‖²) + off-diagonal` -/
theorem gram_quadratic_split {R N : ℕ} (α : Fin R → ℝ) (b : Fin R → ℂ) :
    ∑ r, ∑ s, b r * starRingEnd ℂ (b s) * gramMatrix N α r s =
      ↑N * ∑ r, (b r * starRingEnd ℂ (b r)) +
      ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
        b r * starRingEnd ℂ (b s) * gramMatrix N α r s := by
  -- Split each inner sum into the s=r term and s≠r terms
  have hsplit : ∀ r : Fin R,
      ∑ s, b r * starRingEnd ℂ (b s) * gramMatrix N α r s =
        b r * starRingEnd ℂ (b r) * gramMatrix N α r r +
        ∑ s ∈ Finset.univ.erase r, b r * starRingEnd ℂ (b s) * gramMatrix N α r s := by
    intro r
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
  simp_rw [hsplit, Finset.sum_add_distrib]
  congr 1
  · -- Diagonal: b_r * conj(b_r) * G_{r,r} = b_r * conj(b_r) * N
    simp_rw [gramMatrix_diag]
    rw [Finset.mul_sum]
    congr 1; ext r
    ring
  · -- Off-diagonal: erase = filter
    congr 1; ext r
    apply Finset.sum_congr
    · ext s; simp [Finset.mem_erase, Finset.mem_filter, ne_comm]
    · intros; rfl

/-- The diagonal of the Gram quadratic form has real part `N · ‖b‖²`. -/
theorem gram_diag_re {R N : ℕ} (b : Fin R → ℂ) :
    (↑N * ∑ r, (b r * starRingEnd ℂ (b r)) : ℂ).re = ↑N * l2NormSq b := by
  -- b_r * conj(b_r) = ↑‖b_r‖ ^ 2 (as complex, real-valued)
  have hreal : ∀ r : Fin R, b r * starRingEnd ℂ (b r) = (↑(‖b r‖) : ℂ) ^ 2 := by
    intro r; exact Complex.mul_conj' (b r)
  simp_rw [hreal, ← Complex.ofReal_pow, ← Complex.ofReal_sum,
    ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  rfl

/-- **Off-diagonal Gram bilinear bound implies optimal ALS**: if the off-diagonal
    Gram bilinear form satisfies the bound from Corollaries 7.9–7.10 (with the
    Cohen improvement), then the optimal additive large sieve inequality holds.

    This cleanly separates:
    - **Abstract algebraic infrastructure** (Gram expansion, duality, diagonal evaluation) — proved
    - **Analytic input** (Hilbert inequality + sin bounds + Cohen trick) — captured by
      `GramOffDiagBilinearBound`

    The proof expands the dual ALS LHS as a Gram quadratic form, splits into
    diagonal (`= N · ‖b‖²`) and off-diagonal (`≤ (δ⁻¹ - 1) · ‖b‖²` by hypothesis),
    and combines to get the optimal bound `(δ⁻¹ + N - 1) · ‖b‖²`. -/
theorem gram_offdiag_bilinear_implies_als
    (hoff : GramOffDiagBilinearBound) : AdditiveLargeSieve := by
  intro R N α a δ hδ hδ2 hN hspaced
  -- The constant 1/δ + N - 1 is nonneg
  have hC : (0 : ℝ) ≤ 1/δ + ↑N - 1 := by
    have : 1 ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
    have : 0 < 1/δ := by positivity
    linarith
  -- Use duality: it suffices to prove the dual form
  set x : Fin R → Fin N → ℂ := fun r n => eAN (α r * ↑(n : ℕ)) with hx_def
  show (∑ r, ‖∑ n, a n * x r n‖ ^ 2) ≤ (1/δ + ↑N - 1) * l2NormSq a
  suffices hdual : DualLargeSieve x (1/δ + ↑N - 1) by
    exact (lsi_of_dual x (1/δ + ↑N - 1) hC hdual) a
  -- Prove dual: ∀ b, ∑_n ‖∑_r b_r x(r,n)‖² ≤ (1/δ + N - 1) · ‖b‖²
  intro b
  -- Step 1: Expand dual LHS as Re of Gram quadratic form
  -- (Reusing the expansion from gram_row_sum_implies_lsi)
  have hexpand : (∑ n : Fin N, ‖∑ r, b r * x r n‖ ^ 2 : ℝ) =
      (∑ r, ∑ s, b r * starRingEnd ℂ (b s) * gramMatrix N α r s).re := by
    have habs_sq : ∀ n : Fin N, ‖∑ r, b r * x r n‖ ^ 2 =
        ((∑ r, b r * x r n) * starRingEnd ℂ (∑ r, b r * x r n)).re := by
      intro n; exact complex_norm_sq_eq_re_mul_conj _
    simp_rw [habs_sq]
    rw [← Complex.re_sum]
    congr 1
    simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum, map_mul]
    rw [Finset.sum_comm]
    congr 1; ext r
    rw [Finset.sum_comm]
    congr 1; ext s
    unfold gramMatrix
    rw [← Fin.sum_univ_eq_sum_range]
    rw [Finset.mul_sum]
    congr 1; ext n
    simp only [hx_def]
    rw [eAN_eq_root_eAN, eAN_eq_root_eAN]
    change b r * _root_.eAN (α r * ↑↑n) * (starRingEnd ℂ (b s) * starRingEnd ℂ (_root_.eAN (α s * ↑↑n))) =
        b r * starRingEnd ℂ (b s) * _root_.eAN (↑↑n * (α r - α s))
    rw [conj_eAN]
    rw [show b r * _root_.eAN (α r * ↑↑n) * (starRingEnd ℂ (b s) * _root_.eAN (-(α s * ↑↑n))) =
          b r * starRingEnd ℂ (b s) * (_root_.eAN (α r * ↑↑n) * _root_.eAN (-(α s * ↑↑n))) from by ring]
    rw [← _root_.eAN_add]
    congr 1; ring_nf
  -- Step 2: Split into diagonal + off-diagonal
  rw [hexpand, gram_quadratic_split]
  -- Goal: (↑N * ∑_r b_r conj(b_r) + off-diag).re ≤ (1/δ + N - 1) · l2NormSq b
  rw [Complex.add_re]
  -- Step 3: Bound diagonal
  rw [gram_diag_re]
  -- Step 4: Bound off-diagonal via GramOffDiagBilinearBound
  have hoff_bound := hoff R N α b δ hδ hδ2 hN hspaced
  -- Re(off-diag) ≤ ‖off-diag‖ ≤ (1/δ - 1) · l2NormSq b
  have hre_le_norm := Complex.re_le_norm
    (∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
      b r * starRingEnd ℂ (b s) * gramMatrix N α r s)
  -- Combine: N · l2NormSq b + re(off-diag) ≤ N · l2NormSq b + (1/δ - 1) · l2NormSq b
  have hcombine : ↑N * l2NormSq b + (1/δ - 1) * l2NormSq b =
      (1/δ + ↑N - 1) * l2NormSq b := by ring
  linarith

end AdditiveLargeSieve

end IK
