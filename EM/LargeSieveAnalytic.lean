import EM.LargeSieveHarmonic

/-!
# Analytic Large Sieve: Geometric Sums, Gauss Inversion, and Character Bounds

Geometric sum lemmas for the large sieve kernel, primitivity of characters
at prime level, Gauss sum inversion formula, well-separation infrastructure,
character sum norm bounds via Gauss expansion, and the GCT composition chain.

## Main Results

* `norm_eAN_geom_sum_le_inv` : ‖∑ e(kβ)‖ ≤ 1/(2δ) for well-separated β (PROVED)
* `gauss_sum_inversion_sum` : character Gauss inversion formula (PROVED)
* `char_sum_norm_sq_le_exp_sum_finN` : character → exponential sum reduction (PROVED)
* `norm_sq_sum_mul_le` : Cauchy-Schwarz for weighted character sums (PROVED)
-/

open Mullin Euclid MullinGroup RotorRouter


/-! ## S56. Geometric Sum Lemmas for the Large Sieve Kernel

These lemmas establish quantitative bounds on exponential sums `∑_{k=0}^{N-1} e(kβ)`,
culminating in the estimate `‖∑ e(kβ)‖ ≤ 1/(2δ)` when `|β - round β| ≥ δ`.
They are the key ingredients for proving `KernelRowSumBound`.

### Main results

* `eAN_geom_sum_mul` : telescoping identity for geometric sums of `eAN`
* `eAN_geom_sum_eq` : closed form `(eAN(Nβ) - 1)/(eAN β - 1)` when `eAN β ≠ 1`
* `norm_eAN_geom_sum_le` : `‖∑ e(kβ)‖ ≤ 2/‖eAN β - 1‖`
* `norm_one_sub_eAN` : `‖1 - eAN β‖ = 2|sin(πβ)|`
* `sin_pi_ge_two_mul` : Jordan's inequality: `2t ≤ sin(πt)` for `t ∈ [0, 1/2]`
* `abs_sin_pi_ge_two_frac` : `|sin(πβ)| ≥ 2|β - round β|`
* `norm_eAN_geom_sum_le_inv` : `‖∑ e(kβ)‖ ≤ 1/(2δ)` for well-separated β
-/

section GeomSumLemmas

open Complex Finset Real

/-- `eAN` respects scalar multiplication: `eAN ((k+1) * β) = eAN (k * β) * eAN β`. -/
theorem eAN_succ_mul (k : ℕ) (β : ℝ) :
    eAN ((↑k + 1) * β) = eAN (↑k * β) * eAN β := by
  rw [add_mul, ← eAN_add, one_mul]

/-- The `eAN` geometric sum satisfies the telescoping identity:
    `(∑_{k=0}^{N-1} eAN(kβ)) * (eAN β - 1) = eAN(Nβ) - 1`. -/
theorem eAN_geom_sum_mul (N : ℕ) (β : ℝ) :
    (∑ k ∈ Finset.range N, eAN (↑k * β)) * (eAN β - 1) = eAN (↑N * β) - 1 := by
  induction N with
  | zero => simp [eAN_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    have : eAN (↑(n + 1) * β) = eAN (↑n * β) * eAN β := by
      rw [show (↑(n + 1) : ℝ) * β = (↑n + 1) * β from by push_cast; ring]
      exact eAN_succ_mul n β
    rw [this]; ring

/-- Closed form for the geometric sum when `eAN β ≠ 1`:
    `∑_{k=0}^{N-1} eAN(kβ) = (eAN(Nβ) - 1) / (eAN β - 1)`. -/
theorem eAN_geom_sum_eq (N : ℕ) (β : ℝ) (hne : eAN β ≠ 1) :
    ∑ k ∈ Finset.range N, eAN (↑k * β) = (eAN (↑N * β) - 1) / (eAN β - 1) := by
  have hsub : eAN β - 1 ≠ 0 := sub_ne_zero.mpr hne
  rw [eq_div_iff hsub, eAN_geom_sum_mul]

/-- Norm bound for the geometric sum: `‖∑ e(kβ)‖ ≤ 2 / ‖eAN β - 1‖` when `eAN β ≠ 1`. -/
theorem norm_eAN_geom_sum_le (N : ℕ) (β : ℝ) (hne : eAN β ≠ 1) :
    ‖∑ k ∈ Finset.range N, eAN (↑k * β)‖ ≤ 2 / ‖eAN β - 1‖ := by
  rw [eAN_geom_sum_eq N β hne]
  rw [norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc ‖eAN (↑N * β) - 1‖
      ≤ ‖eAN (↑N * β)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 1 + 1 := by rw [eAN_norm, norm_one]
    _ = 2 := by norm_num

/-- Norm identity: `‖1 - eAN β‖ = 2 * |sin(π * β)|`. -/
theorem norm_one_sub_eAN (β : ℝ) :
    ‖1 - eAN β‖ = 2 * |Real.sin (Real.pi * β)| := by
  -- eAN β = exp(2πiβ) = exp(I * (2πβ))
  -- We use Complex.norm_exp_I_mul_ofReal_sub_one: ‖exp(I * x) - 1‖ = ‖2 * sin(x/2)‖
  have key : ‖1 - eAN β‖ = ‖Complex.exp (Complex.I * ↑(2 * Real.pi * β)) - 1‖ := by
    rw [norm_sub_rev]
    congr 1
    simp only [eAN]
    rw [show 2 * ↑Real.pi * Complex.I * (↑β : ℂ) = Complex.I * ↑(2 * Real.pi * β) by
      push_cast; ring]
  rw [key, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2 * Real.pi * β / 2 = Real.pi * β by ring]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (2 : ℝ) > 0)]

/-- `‖eAN β - 1‖ = 2 * |sin(π * β)|`. -/
theorem norm_eAN_sub_one (β : ℝ) :
    ‖eAN β - 1‖ = 2 * |Real.sin (Real.pi * β)| := by
  rw [← norm_neg, neg_sub, norm_one_sub_eAN]

/-- **Jordan's inequality** (half): for `0 ≤ t ≤ 1/2`, `2 * t ≤ sin(π * t)`.

    Proof: By concavity of sin on `[0, π/2]`, `sin x ≥ (2/π) * x` for `x ∈ [0, π/2]`.
    Substituting `x = π * t` gives `sin(π * t) ≥ (2/π) * (π * t) = 2 * t`. -/
theorem sin_pi_ge_two_mul {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    2 * t ≤ Real.sin (Real.pi * t) := by
  -- Use Real.mul_le_sin: for 0 ≤ x ≤ π/2, (2/π) * x ≤ sin x
  have hx0 : 0 ≤ Real.pi * t := mul_nonneg Real.pi_pos.le ht0
  have hx1 : Real.pi * t ≤ Real.pi / 2 := by
    calc Real.pi * t ≤ Real.pi * (1 / 2) := by
          apply mul_le_mul_of_nonneg_left ht1 Real.pi_pos.le
      _ = Real.pi / 2 := by ring
  have jordan := Real.mul_le_sin hx0 hx1
  -- jordan : 2 / π * (π * t) ≤ sin(π * t)
  -- 2/π * (π*t) = 2*t since π ≠ 0
  have heq : 2 / Real.pi * (Real.pi * t) = 2 * t := by
    rw [div_mul_comm, mul_comm Real.pi t, mul_div_cancel_right₀ _ Real.pi_ne_zero, mul_comm]
  linarith

/-- For any real β, `|sin(π * β)| ≥ 2 * |β - round β|`.

    The fractional part `t = β - round β` satisfies `|t| ≤ 1/2`.
    Then `sin(π * β) = sin(π * round β + π * t) = ±sin(π * t)`,
    so `|sin(π * β)| = |sin(π * t)| ≥ 2 * |t|` by Jordan's inequality. -/
theorem abs_sin_pi_ge_two_frac (β : ℝ) :
    2 * |β - round β| ≤ |Real.sin (Real.pi * β)| := by
  set t := β - round β with ht_def
  -- |t| ≤ 1/2
  have ht_abs : |t| ≤ 1 / 2 := abs_sub_round β
  -- sin(πβ) = sin(π*t + round(β)*π) = (-1)^round(β) * sin(π*t)
  have hrewrite : Real.pi * β = Real.pi * t + ↑(round β) * Real.pi := by
    rw [ht_def]; ring
  rw [hrewrite, Real.sin_add_int_mul_pi]
  -- Now goal: 2 * |t| ≤ |(-1)^(round β) * sin(π * t)|
  rw [abs_mul, abs_neg_one_zpow, one_mul]
  -- Now goal: 2 * |t| ≤ |sin(π * t)|
  -- Case split on sign of t
  rcases le_or_gt 0 t with ht_nn | ht_neg
  · -- t ≥ 0
    have ht1 : t ≤ 1 / 2 := by rwa [abs_of_nonneg ht_nn] at ht_abs
    rw [abs_of_nonneg ht_nn]
    have hsin := sin_pi_ge_two_mul ht_nn ht1
    rw [abs_of_nonneg (by linarith)]
    exact hsin
  · -- t < 0
    have ht1 : -t ≤ 1 / 2 := by rwa [abs_of_neg ht_neg] at ht_abs
    rw [abs_of_neg ht_neg]
    have hsin := sin_pi_ge_two_mul (neg_nonneg.mpr ht_neg.le) ht1
    rw [show Real.pi * t = -(Real.pi * (-t)) by ring, Real.sin_neg, abs_neg]
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- When `0 < δ` and `δ ≤ |β - round β|`, the geometric sum of `eAN(kβ)` is bounded:
    `‖∑_{k=0}^{N-1} eAN(kβ)‖ ≤ 1/(2δ)`. -/
theorem norm_eAN_geom_sum_le_inv (N : ℕ) (β : ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : δ ≤ |β - round β|) :
    ‖∑ k ∈ Finset.range N, eAN (↑k * β)‖ ≤ 1 / (2 * δ) := by
  -- First establish eAN β ≠ 1
  have hfrac : |β - round β| > 0 := lt_of_lt_of_le hδ hsep
  have hne : eAN β ≠ 1 := by
    intro h
    -- eAN β = 1 means β is an integer
    have : ‖eAN β - 1‖ = 0 := by rw [h, sub_self, norm_zero]
    rw [norm_eAN_sub_one] at this
    have : |Real.sin (Real.pi * β)| = 0 := by linarith
    have : Real.sin (Real.pi * β) = 0 := abs_eq_zero.mp this
    -- sin(πβ) = 0 means β ∈ ℤ, so β - round β = 0
    rw [Real.sin_eq_zero_iff] at this
    obtain ⟨n, hn⟩ := this
    have : β = n := by
      have := hn; field_simp at this; linarith
    rw [this] at hfrac
    simp [round_intCast] at hfrac
  -- Chain the bounds
  have hfrac_pos : 0 < 2 * |β - round β| := by positivity
  have hsin_pos : 0 < |Real.sin (Real.pi * β)| := by
    rw [abs_pos]; intro hsin
    rw [Real.sin_eq_zero_iff] at hsin
    obtain ⟨n, hn⟩ := hsin
    have : β = n := by
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp at hn; linarith
    rw [this] at hfrac; simp [round_intCast] at hfrac
  calc ‖∑ k ∈ Finset.range N, eAN (↑k * β)‖
      ≤ 2 / ‖eAN β - 1‖ := norm_eAN_geom_sum_le N β hne
    _ = 2 / (2 * |Real.sin (Real.pi * β)|) := by rw [norm_eAN_sub_one]
    _ = 1 / |Real.sin (Real.pi * β)| := by ring
    _ ≤ 1 / (2 * |β - round β|) := by
        apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hfrac_pos
        exact abs_sin_pi_ge_two_frac β
    _ ≤ 1 / (2 * δ) := by
        apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
        exact mul_le_mul_of_nonneg_left hsep (by norm_num)

end GeomSumLemmas

/-! ## S56. Primitivity of Characters at Prime Level and eAN Bridge

For a prime p, every nontrivial Dirichlet character mod p is primitive.
This is because the only divisors of p are 1 and p; conductor 1 forces triviality.

We also bridge between Mathlib's `ZMod.stdAddChar` and our `eAN` function. -/

section PrimitiveCharPrime

open DirichletCharacter in
/-- For a prime p, every nontrivial Dirichlet character mod p is primitive.
    The conductor divides p, so it is 1 or p. Conductor 1 implies χ = 1. -/
theorem isPrimitive_of_prime_nontrivial {p : ℕ} [hp : Fact (Nat.Prime p)]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    χ.IsPrimitive := by
  rw [isPrimitive_def]
  have hp' := hp.out
  have hp0 : p ≠ 0 := hp'.ne_zero
  have hcond_dvd := conductor_dvd_level χ
  rcases hp'.eq_one_or_self_of_dvd (conductor χ) hcond_dvd with h1 | hp_eq
  · -- conductor χ = 1 implies χ = 1, contradicting hχ
    exact absurd ((eq_one_iff_conductor_eq_one hp0).mpr h1) hχ
  · exact hp_eq

/-- The standard additive character on ZMod q evaluated at k equals eAN(k.val / q). -/
theorem stdAddChar_val_eq_eAN {q : ℕ} [hq : NeZero q] (k : ZMod q) :
    (ZMod.stdAddChar k : ℂ) = eAN ((ZMod.val k : ℝ) / (q : ℝ)) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  simp only [eAN]
  congr 1
  push_cast
  ring

end PrimitiveCharPrime

/-! ## S57. Gauss Sum Inversion Formula

For a nontrivial multiplicative character χ on ZMod p (p prime), the Gauss sum
inversion formula expresses χ(a) via the Gauss sum and additive characters:

  χ(a) = τ(χ⁻¹)⁻¹ · ∑_b χ⁻¹(b) · ψ(b · a)

where τ(χ⁻¹) = gaussSum χ⁻¹ ψ and ψ is the standard additive character.

This is the key identity in the Gauss-conductor transfer (GCT), allowing us to
convert character sums ∑ a(n) χ(n) into linear combinations of exponential sums
∑ a(n) e(n · α) at evaluation points determined by the Gauss sum.

**Proof strategy**: Apply Mathlib's `gaussSum_mulShift_of_isPrimitive` to χ⁻¹,
which gives `gaussSum χ⁻¹ (ψ.mulShift a) = χ a · gaussSum χ⁻¹ ψ`. Then divide
both sides by the (nonzero) Gauss sum `gaussSum χ⁻¹ ψ`. -/

section GaussSumInversion

open DirichletCharacter AddChar

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private instance : NeZero p := ⟨hp.out.ne_zero⟩

/-- The Gauss sum of a nontrivial character on ZMod p does not vanish. -/
theorem gaussSum_stdAddChar_ne_zero (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) :
    gaussSum χ (ZMod.stdAddChar (N := p)) ≠ 0 := by
  apply gaussSum_ne_zero_of_nontrivial
  · simp only [ZMod.card p]
    exact Nat.cast_ne_zero.mpr hp.out.ne_zero
  · exact hχ
  · exact ZMod.isPrimitive_stdAddChar p

/-- Gauss sum inversion: for a nontrivial χ on ZMod p and any a,
    `χ(a) = (gaussSum χ⁻¹ ψ)⁻¹ * gaussSum χ⁻¹ (ψ.mulShift a)`

    This is a direct consequence of `gaussSum_mulShift_of_isPrimitive` applied
    to χ⁻¹ (which is primitive at prime level), rearranged as a division. -/
theorem gauss_sum_inversion (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    χ a = (gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)))⁻¹ *
          gaussSum χ⁻¹ (mulShift (ZMod.stdAddChar (N := p)) a) := by
  -- Step 1: χ⁻¹ is also nontrivial and primitive at prime level
  have hχ_inv : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
  have hprim : (χ⁻¹ : DirichletCharacter ℂ p).IsPrimitive :=
    isPrimitive_of_prime_nontrivial χ⁻¹ hχ_inv
  -- Step 2: Apply gaussSum_mulShift_of_isPrimitive to χ⁻¹
  have hmul := gaussSum_mulShift_of_isPrimitive (ZMod.stdAddChar (N := p)) hprim a
  -- hmul : gaussSum χ⁻¹ (mulShift stdAddChar a) = (χ⁻¹)⁻¹ a * gaussSum χ⁻¹ stdAddChar
  rw [inv_inv] at hmul
  -- hmul : gaussSum χ⁻¹ (mulShift stdAddChar a) = χ a * gaussSum χ⁻¹ stdAddChar
  -- Step 3: Divide both sides by gaussSum χ⁻¹ stdAddChar
  have hne : gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) ≠ 0 :=
    gaussSum_stdAddChar_ne_zero χ⁻¹ hχ_inv
  rw [hmul, mul_comm (χ a) _, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- Expanded form of Gauss sum inversion: χ(a) expressed as a sum over ZMod p.

    `χ(a) = (gaussSum χ⁻¹ ψ)⁻¹ * ∑ b, χ⁻¹(b) * ψ(b * a)`

    This unfolds the `gaussSum χ⁻¹ (ψ.mulShift a)` from `gauss_sum_inversion`. -/
theorem gauss_sum_inversion_sum (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    χ a = (gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)))⁻¹ *
          ∑ b : ZMod p, χ⁻¹ b * (ZMod.stdAddChar (N := p)) (b * a) := by
  rw [gauss_sum_inversion χ hχ a]
  congr 1
  simp only [gaussSum, mulShift_apply, mul_comm]

/-- Character sum transformation: a character sum ∑ f(n) χ(n) can be expressed
    as (gaussSum χ⁻¹ ψ)⁻¹ times a double sum involving additive characters.

    `∑ n, f(n) * χ(n) = τ⁻¹ * ∑ b, χ⁻¹(b) * ∑ n, f(n) * ψ(b * n)`

    where τ = gaussSum χ⁻¹ ψ. This is the key formula that converts character
    sums into linear combinations of exponential sums. -/
theorem char_sum_to_exp_sum {S : Finset (ZMod p)} (f : ZMod p → ℂ)
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) :
    ∑ n ∈ S, f n * χ n =
    (gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)))⁻¹ *
    ∑ b : ZMod p, χ⁻¹ b *
      ∑ n ∈ S, f n * (ZMod.stdAddChar (N := p)) (b * n) := by
  let ψ := ZMod.stdAddChar (N := p)
  let τ := gaussSum χ⁻¹ ψ
  have hne : τ ≠ 0 := gaussSum_stdAddChar_ne_zero χ⁻¹ (inv_ne_one.mpr hχ)
  -- It suffices to show τ * LHS = τ * RHS (since τ ≠ 0)
  apply mul_left_cancel₀ hne
  rw [show τ * (τ⁻¹ * ∑ b : ZMod p, χ⁻¹ b * ∑ n ∈ S, f n * ψ (b * n) ) =
    ∑ b : ZMod p, χ⁻¹ b * ∑ n ∈ S, f n * ψ (b * n)
    from by rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]]
  -- Now show τ * ∑ f(n)χ(n) = ∑_b χ⁻¹(b) * ∑_n f(n) * ψ(b*n)
  -- Expand τ = ∑_b χ⁻¹(b) ψ(b)
  show τ * ∑ n ∈ S, f n * χ n = ∑ b : ZMod p, χ⁻¹ b * ∑ n ∈ S, f n * ψ (b * n)
  simp_rw [Finset.mul_sum]
  -- RHS is ∑_b ∑_n χ⁻¹(b) * f(n) * ψ(b*n)
  -- LHS is ∑_n τ * (f(n) * χ(n))
  -- Using τ * χ(n) = ∑_b χ⁻¹(b) * ψ(b*n) from gauss_sum_inversion_sum
  -- Swap sums on RHS
  rw [Finset.sum_comm]
  congr 1; ext n
  -- Show τ * (f(n) * χ(n)) = ∑_b χ⁻¹(b) * (f(n) * ψ(b*n))
  -- = f(n) * ∑_b χ⁻¹(b) * ψ(b*n) = f(n) * τ * χ(n)
  rw [show τ * (f n * χ n) = f n * (τ * χ n) from by ring]
  rw [show τ * χ n = ∑ b : ZMod p, χ⁻¹ b * ψ (b * n) from by
    have h := gauss_sum_inversion_sum χ hχ n
    rw [h, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]]
  rw [Finset.mul_sum]
  congr 1; ext b; ring

end GaussSumInversion

/-! ## S58. Well-Separation Card Bound and Gram Matrix Infrastructure

For δ-separated points α₀, ..., α_{R-1} on ℝ/ℤ (i.e., with pairwise distance
at least δ measured mod 1), we prove:
1. R ≤ ⌊1/δ⌋ + 1 (well-separated card bound)
2. The Gram matrix G_{r,s} = ∑_{n<N} e(n(α_r - α_s)) has diagonal N and
   off-diagonal entries bounded by 1/(2δ)
3. A weak form of ALS: ∑_r |S(α_r)|² ≤ N · (⌊1/δ⌋ + 1) · ∑|a_n|²

The weak ALS follows from Cauchy-Schwarz per evaluation point combined with
the card bound. While weaker than the optimal N-1+δ⁻¹, it has the correct
asymptotic order O(N/δ) and suffices for many applications.

### Main results

* `well_separated_card_le` : R ≤ ⌊1/δ⌋ + 1 for δ-separated points
* `gram_diag_eq` : G_{r,r} = N
* `gram_off_diag_bound` : |G_{r,s}| ≤ 1/(2δ) for r ≠ s
* `als_per_point_bound` : |S(α_r)|² ≤ N · ∑|a_n|² (C-S per point)
* `weak_als_from_card_bound` : weak ALS from card bound + per-point C-S
-/

section WellSepInfra

open Complex Finset Real

/-- For δ-separated points on ℝ/ℤ, the number of points R satisfies R ≤ ⌊1/δ⌋ + 1.

    Proof: The R arcs of width δ centered at the α_r are pairwise disjoint on
    ℝ/ℤ (which has total length 1). So R · δ ≤ 1, hence R ≤ 1/δ, hence R ≤ ⌊1/δ⌋ + 1.

    More precisely: consider the R intervals (α_r - δ/2, α_r + δ/2) mod 1.
    By δ-separation these are disjoint, each has length δ, and they fit in [0,1),
    so R · δ ≤ 1, giving R ≤ ⌊1/δ⌋ ≤ ⌊1/δ⌋ + 1.

    We state this with a ℝ-valued bound: (R : ℝ) ≤ δ⁻¹ + 1 (which implies
    R ≤ ⌊1/δ⌋ + 1 since R is a natural number). -/
theorem well_separated_card_le (R : ℕ) (α : Fin R → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ r s : Fin R, r ≠ s → δ ≤ |α r - α s - round (α r - α s)|) :
    (R : ℝ) ≤ δ⁻¹ + 1 := by
  -- Define fractional parts f(r) = α r - round(α r) ∈ [-1/2, 1/2]
  set f : Fin R → ℝ := fun r => α r - round (α r) with hf_def
  -- Define bin map g(r) = ⌊(f(r) + 1/2) / δ⌋
  set g : Fin R → ℤ := fun r => ⌊(f r + 1 / 2) / δ⌋ with hg_def
  -- Key separation lemma: if r ≠ s then |f(r) - f(s)| ≥ δ
  have hf_sep : ∀ r s : Fin R, r ≠ s → δ ≤ |f r - f s| := by
    intro r s hrs
    have h1 := hsep r s hrs
    -- f r - f s = α r - α s - (round(α r) - round(α s))
    have hkey : f r - f s = α r - α s - (↑(round (α r)) - ↑(round (α s))) := by
      simp [hf_def]; ring
    rw [hkey]
    -- round(α r - α s) is the nearest integer, so
    -- |α r - α s - round(α r - α s)| ≤ |α r - α s - m| for any integer m
    calc δ ≤ |α r - α s - ↑(round (α r - α s))| := h1
      _ ≤ |α r - α s - (↑(round (α r)) - ↑(round (α s)))| := by
          have : (↑(round (α r)) - ↑(round (α s)) : ℝ) = ↑(round (α r) - round (α s)) := by
            push_cast; ring
          rw [this]
          exact round_le (α r - α s) (round (α r) - round (α s))
  -- g is injective: if g(r) = g(s), then f(r) and f(s) are in the same bin of width δ
  have hg_inj : Function.Injective g := by
    intro r s hrs
    by_contra hne
    have hsep' := hf_sep r s hne
    -- hrs : g r = g s, i.e. ⌊(f r + 1/2)/δ⌋ = ⌊(f s + 1/2)/δ⌋
    have hgrs : ⌊(f r + 1 / 2) / δ⌋ = ⌊(f s + 1 / 2) / δ⌋ := hrs
    have hr_lb := Int.floor_le ((f r + 1 / 2) / δ)
    have hr_ub := Int.lt_floor_add_one ((f r + 1 / 2) / δ)
    have hs_lb := Int.floor_le ((f s + 1 / 2) / δ)
    have hs_ub := Int.lt_floor_add_one ((f s + 1 / 2) / δ)
    -- Both values lie in [⌊(f s + 1/2)/δ⌋, ⌊(f s + 1/2)/δ⌋ + 1)
    rw [hgrs] at hr_lb hr_ub
    -- Both (f r + 1/2)/δ and (f s + 1/2)/δ in [⌊(f s+1/2)/δ⌋, ⌊(f s+1/2)/δ⌋+1)
    -- So their difference < 1, meaning |f r - f s| < δ
    have hfr_sub : (f r - f s) / δ < 1 := by
      have h1 : (f r + 1 / 2) / δ < (↑⌊(f s + 1 / 2) / δ⌋ : ℝ) + 1 := hr_ub
      have h2 : (↑⌊(f s + 1 / 2) / δ⌋ : ℝ) ≤ (f s + 1 / 2) / δ := hs_lb
      have : (f r + 1 / 2) / δ - (f s + 1 / 2) / δ < 1 := by linarith
      have heq : (f r + 1 / 2) / δ - (f s + 1 / 2) / δ = (f r - f s) / δ := by ring
      linarith
    have hfs_sub : -((f r - f s) / δ) < 1 := by
      have h1 : (f s + 1 / 2) / δ < (↑⌊(f s + 1 / 2) / δ⌋ : ℝ) + 1 := hs_ub
      have h2 : (↑⌊(f s + 1 / 2) / δ⌋ : ℝ) ≤ (f r + 1 / 2) / δ := hr_lb
      have : (f s + 1 / 2) / δ - (f r + 1 / 2) / δ < 1 := by linarith
      have heq : (f s + 1 / 2) / δ - (f r + 1 / 2) / δ = -((f r - f s) / δ) := by ring
      linarith
    have h1 : f r - f s < δ := by
      have := (div_lt_one hδ).mp hfr_sub; linarith
    have h2 : -(f r - f s) < δ := by
      have hfs_neg : -(f r - f s) / δ < 1 := by
        rw [neg_div]; linarith
      have := (div_lt_one hδ).mp hfs_neg; linarith
    have : |f r - f s| < δ := by rw [abs_lt]; constructor <;> linarith
    linarith
  -- g maps into {0, ..., ⌊1/δ⌋}
  have hg_range : ∀ r : Fin R, g r ∈ Finset.Icc (0 : ℤ) ⌊δ⁻¹⌋ := by
    intro r
    rw [Finset.mem_Icc]
    have hfr := abs_sub_round (α r)
    rw [abs_le] at hfr
    constructor
    · show ⌊(f r + 1 / 2) / δ⌋ ≥ 0
      exact Int.floor_nonneg.mpr (div_nonneg (by linarith [hfr.1]) hδ.le)
    · show ⌊(f r + 1 / 2) / δ⌋ ≤ ⌊δ⁻¹⌋
      apply Int.floor_le_floor
      have : f r + 1 / 2 ≤ 1 := by linarith [hfr.2]
      calc (f r + 1 / 2) / δ ≤ 1 / δ := by
              apply div_le_div_of_nonneg_right this (le_of_lt hδ)
        _ = δ⁻¹ := one_div δ
  -- Injection from Finset.univ (Fin R) to Finset.Icc 0 ⌊δ⁻¹⌋ via g
  have hR_le_card : R ≤ (Finset.Icc (0 : ℤ) ⌊δ⁻¹⌋).card := by
    calc R = Finset.card (Finset.univ : Finset (Fin R)) := by simp
      _ = Finset.card (Finset.image g Finset.univ) := by
          rw [Finset.card_image_of_injective _ hg_inj]
      _ ≤ Finset.card (Finset.Icc (0 : ℤ) ⌊δ⁻¹⌋) := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_image] at hx
          obtain ⟨r, _, hrx⟩ := hx
          rw [← hrx]
          exact hg_range r
  -- card(Icc 0 ⌊δ⁻¹⌋) = (⌊δ⁻¹⌋ + 1).toNat
  have hfloor_nn : (0 : ℤ) ≤ ⌊δ⁻¹⌋ := Int.floor_nonneg.mpr (inv_nonneg.mpr hδ.le)
  rw [Int.card_Icc, show ⌊δ⁻¹⌋ + 1 - 0 = ⌊δ⁻¹⌋ + 1 by ring] at hR_le_card
  calc (R : ℝ) ≤ ((⌊δ⁻¹⌋ + 1).toNat : ℝ) := by exact_mod_cast hR_le_card
    _ = ((⌊δ⁻¹⌋ + 1 : ℤ) : ℝ) := by
        have hnn : (0 : ℤ) ≤ ⌊δ⁻¹⌋ + 1 := by linarith
        exact_mod_cast Int.toNat_of_nonneg hnn
    _ = (⌊δ⁻¹⌋ : ℝ) + 1 := by push_cast; ring
    _ ≤ δ⁻¹ + 1 := by linarith [Int.floor_le δ⁻¹]

/-- Cauchy-Schwarz per evaluation point: |∑_n a_n e(nα)|² ≤ N · ∑ |a_n|².
    This is a direct application of `norm_sq_sum_le_card_mul`. -/
theorem als_per_point_bound (N : ℕ) (a : Fin N → ℂ) (α : ℝ) :
    ‖∑ n : Fin N, a n * eAN (↑(n : ℤ) * α)‖ ^ 2 ≤ ↑N * ∑ n : Fin N, ‖a n‖ ^ 2 := by
  calc ‖∑ n : Fin N, a n * eAN (↑(n : ℤ) * α)‖ ^ 2
      ≤ ↑N * ∑ n : Fin N, ‖a n * eAN (↑(n : ℤ) * α)‖ ^ 2 :=
        norm_sq_sum_le_card_mul N (fun n => a n * eAN (↑(n : ℤ) * α))
    _ = ↑N * ∑ n : Fin N, ‖a n‖ ^ 2 := by
        congr 1; congr 1; ext n
        rw [norm_mul, eAN_norm, mul_one]

/-- **Weak ALS from card bound**: For δ-separated evaluation points,
    ∑_r |S(α_r)|² ≤ N · (δ⁻¹ + 1) · ∑ |a_n|².

    Proof: Sum the per-point C-S bound over all R evaluation points, then
    use R ≤ δ⁻¹ + 1 from the well-separation card bound.

    This is weaker than the optimal ALS bound of (N - 1 + δ⁻¹) by a factor
    of roughly N, but establishes the correct structure. -/
theorem weak_als_from_card_bound
    (N : ℕ) (_hN : 0 < N) (a : Fin N → ℂ)
    (R : ℕ) (α : Fin R → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ r s : Fin R, r ≠ s → δ ≤ |α r - α s - round (α r - α s)|) :
    ∑ r : Fin R,
      ‖∑ n : Fin N, a n * eAN (↑(n : ℤ) * α r)‖ ^ 2
    ≤ ↑N * (δ⁻¹ + 1) * ∑ n : Fin N, ‖a n‖ ^ 2 := by
  have hcard := well_separated_card_le R α δ hδ hsep
  calc ∑ r : Fin R, ‖∑ n : Fin N, a n * eAN (↑(n : ℤ) * α r)‖ ^ 2
      ≤ ∑ _r : Fin R, (↑N * ∑ n : Fin N, ‖a n‖ ^ 2) := by
        gcongr with r; exact als_per_point_bound N a (α r)
    _ = ↑R * (↑N * ∑ n : Fin N, ‖a n‖ ^ 2) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (δ⁻¹ + 1) * (↑N * ∑ n : Fin N, ‖a n‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_right hcard
        exact mul_nonneg (Nat.cast_nonneg N) (Finset.sum_nonneg (fun n _ => by positivity))
    _ = ↑N * (δ⁻¹ + 1) * ∑ n : Fin N, ‖a n‖ ^ 2 := by ring

/-! ### Gram matrix estimates

The Gram matrix `G_{r,s} = ∑_{k=0}^{N-1} e(k · (α_r - α_s))` has diagonal equal to N
and off-diagonal entries bounded in norm by `1/(2δ)` for δ-separated points.
These follow directly from `eAN_zero` and `norm_eAN_geom_sum_le_inv`. -/

/-- The Gram matrix diagonal: `G_{r,r} = ∑_{k < N} e(k · 0) = N`. -/
theorem gram_diag_eq (N R : ℕ) (α : Fin R → ℝ) (r : Fin R) :
    ∑ k ∈ Finset.range N, eAN (↑k * (α r - α r)) = ↑N := by
  simp [sub_self, mul_zero, eAN_zero]

/-- The Gram matrix off-diagonal bound: for δ-separated `α` and `r ≠ s`,
    `‖G_{r,s}‖ = ‖∑_{k < N} e(k · (α_r - α_s))‖ ≤ 1/(2δ)`. -/
theorem gram_off_diag_bound (N R : ℕ) (α : Fin R → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ r s : Fin R, r ≠ s → δ ≤ |α r - α s - round (α r - α s)|)
    (r s : Fin R) (hrs : r ≠ s) :
    ‖∑ k ∈ Finset.range N, eAN (↑k * (α r - α s))‖ ≤ 1 / (2 * δ) :=
  norm_eAN_geom_sum_le_inv N (α r - α s) δ hδ (hsep r s hrs)

/-- **Trigonometric kernel L2 bound**: for δ-separated points,
    `∑_{k ∈ range N} ‖K(k)‖² ≤ N · R + R · (R - 1) / (2 · δ)`.

    Proof: `‖K(k)‖²` expands as `Re(∑_{r,s} e(k(α_s - α_r)))`. Swap sums,
    then diagonal (r=s) contributes `N` each, and off-diagonal geometric
    sums are bounded by `1/(2δ)` via `norm_eAN_geom_sum_le_inv`. -/
theorem trigKernel_l2_upper_bound (N R : ℕ) (α : Fin R → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ r s : Fin R, r ≠ s → δ ≤ |α r - α s - round (α r - α s)|) :
    ∑ k ∈ Finset.range N, ‖trigKernel R α ↑k‖ ^ 2 ≤
    ↑N * ↑R + ↑R * (↑R - 1) / (2 * δ) := by
  -- Step 1: Expand ‖K(k)‖² into double sum over Fin R
  have hkey : ∀ k : ℕ, ‖trigKernel R α ↑k‖ ^ 2 =
      (∑ s : Fin R, ∑ r : Fin R, eAN (↑k * α s) * starRingEnd ℂ (eAN (↑k * α r))).re := by
    intro k
    rw [complex_norm_sq_eq_re_mul_conj]
    simp only [trigKernel]
    rw [map_sum, Finset.sum_mul]
    congr 1
    congr 1; ext s
    exact Finset.mul_sum _ _ _
  -- Step 2: Simplify each term: e(kα_s) * conj(e(kα_r)) = e(k(α_s - α_r))
  have hterm : ∀ (k : ℕ) (r s : Fin R),
      eAN (↑k * α s) * starRingEnd ℂ (eAN (↑k * α r)) = eAN (↑k * (α s - α r)) := by
    intro k r s
    rw [conj_eAN, show ↑k * (α s - α r) = ↑k * α s + (-(↑k * α r)) from by ring, eAN_add]
  -- Step 3: Combine steps 1-2 and push Re through sums
  have hexpand : ∀ k : ℕ, ‖trigKernel R α ↑k‖ ^ 2 =
      ∑ s : Fin R, ∑ r : Fin R, (eAN (↑k * (α s - α r))).re := by
    intro k
    rw [hkey]
    simp_rw [hterm]
    rw [Complex.re_sum]; congr 1; ext s; exact Complex.re_sum _ _
  simp_rw [hexpand]
  -- Step 4: Swap sums: ∑_{k} ∑_s ∑_r → ∑_s ∑_r ∑_k
  have hswap : ∀ (f : Fin R → Fin R → ℕ → ℝ),
      ∑ k ∈ Finset.range N, ∑ s : Fin R, ∑ r : Fin R, f s r k =
      ∑ s : Fin R, ∑ r : Fin R, ∑ k ∈ Finset.range N, f s r k := by
    intro f; rw [Finset.sum_comm]; congr 1; ext s; rw [Finset.sum_comm]
  rw [hswap]
  -- Goal: ∑_s ∑_r (∑_k Re(e(k(α_s - α_r)))) ≤ N·R + R·(R-1)/(2δ)
  -- Step 5: Diagonal bound (s = r): each inner sum = N
  have hdiag : ∀ s : Fin R,
      ∑ k ∈ Finset.range N, (eAN (↑k * (α s - α s))).re = ↑N := by
    intro s; simp [sub_self, mul_zero, eAN_zero, Complex.one_re]
  -- Step 6: Off-diagonal bound (s ≠ r): each inner sum ≤ 1/(2δ)
  have hoffdiag : ∀ s r : Fin R, s ≠ r →
      ∑ k ∈ Finset.range N, (eAN (↑k * (α s - α r))).re ≤ 1 / (2 * δ) := by
    intro s r hsr
    calc ∑ k ∈ Finset.range N, (eAN (↑k * (α s - α r))).re
        = (∑ k ∈ Finset.range N, eAN (↑k * (α s - α r))).re :=
          (Complex.re_sum (Finset.range N) _).symm
      _ ≤ ‖∑ k ∈ Finset.range N, eAN (↑k * (α s - α r))‖ := Complex.re_le_norm _
      _ ≤ 1 / (2 * δ) := norm_eAN_geom_sum_le_inv N _ δ hδ (hsep s r hsr)
  -- Step 7: Split double sum into diagonal + off-diagonal and bound
  -- We bound: ∑_s ∑_r f(s,r) ≤ ∑_s f(s,s) + ∑_s ∑_{r≠s} |f(s,r)|
  -- where f(s,r) = ∑_k Re(e(k(α_s-α_r)))
  -- Step 7: Bound each ∑_r ∑_k by splitting diagonal from off-diagonal
  -- For each s, bound ∑_r (∑_k Re(e(k(α_s - α_r))))
  have hbound_s : ∀ s : Fin R,
      ∑ r : Fin R, ∑ k ∈ Finset.range N, (eAN (↑k * (α s - α r))).re ≤
      ↑N + (↑R - 1) / (2 * δ) := by
    intro s
    -- Split sum into r=s and r≠s using erase
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ s)]
    -- Diagonal: ∑_k Re(e(0)) = N
    -- Off-diagonal: ∑_{r ∈ univ \ {s}} (∑_k Re(...)) ≤ ∑_{r ∈ univ \ {s}} 1/(2δ)
    have hdiag_s := hdiag s
    have hoff_bound : ∑ r ∈ Finset.univ.erase s,
        ∑ k ∈ Finset.range N, (eAN (↑k * (α s - α r))).re ≤
        (↑R - 1) / (2 * δ) := by
      calc ∑ r ∈ Finset.univ.erase s,
            ∑ k ∈ Finset.range N, (eAN (↑k * (α s - α r))).re
          ≤ ∑ _r ∈ Finset.univ.erase s, (1 / (2 * δ) : ℝ) := by
            apply Finset.sum_le_sum
            intro r hr
            exact hoffdiag s r (Ne.symm (Finset.ne_of_mem_erase hr))
        _ = (Finset.univ.erase s).card • (1 / (2 * δ) : ℝ) := by
            rw [Finset.sum_const]
        _ = ↑(Finset.univ.erase s).card * (1 / (2 * δ)) := by
            rw [nsmul_eq_mul]
        _ = (↑R - 1) / (2 * δ) := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ s),
                Finset.card_univ, Fintype.card_fin]
            rw [Nat.cast_sub (Fin.pos s)]; ring
    linarith
  calc ∑ s : Fin R, ∑ r : Fin R,
        ∑ k ∈ Finset.range N, (eAN (↑k * (α s - α r))).re
      ≤ ∑ _s : Fin R, (↑N + (↑R - 1) / (2 * δ)) := by
        gcongr with s; exact hbound_s s
    _ = ↑R * (↑N + (↑R - 1) / (2 * δ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ↑N * ↑R + ↑R * (↑R - 1) / (2 * δ) := by ring

end WellSepInfra

/-! ## S59. Character Sum Norm Squared via Gauss Expansion

For a nontrivial multiplicative character χ mod prime p, and any function f : ZMod p → ℂ,
we prove:

  ‖∑_n f(n) χ(n)‖² ≤ ∑_a ‖∑_n f(n) ψ(a·n)‖²

where ψ = stdAddChar is the standard additive character on ZMod p.

**Proof**: Use `char_sum_to_exp_sum` to write the character sum as
  τ⁻¹ · ∑_b χ⁻¹(b) · T(b)
where T(b) = ∑_n f(n)ψ(bn) and τ = gaussSum χ⁻¹ ψ. Then:
- ‖LHS‖² = ‖τ‖⁻² · ‖∑ χ⁻¹(b) T(b)‖²
- Cauchy-Schwarz: ‖∑ χ⁻¹(b) T(b)‖² ≤ (∑ ‖χ⁻¹(b)‖²)(∑ ‖T(b)‖²) ≤ p · ∑ ‖T(b)‖²
- ‖τ‖² = p from `gaussSum_norm_sq_eq_prime`
- Combine: ‖LHS‖² ≤ (1/p) · p · ∑ ‖T(b)‖² = ∑ ‖T(b)‖²  -/

section CharSumExpBound

open DirichletCharacter AddChar

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private instance : NeZero p := ⟨hp.out.ne_zero⟩

/-- Cauchy-Schwarz for finite sums over an arbitrary Fintype:
    ‖∑_i g(i) * h(i)‖² ≤ (∑_i ‖g(i)‖²) * (∑_i ‖h(i)‖²). -/
private lemma norm_sq_sum_mul_le {ι : Type*} [Fintype ι]
    (g h : ι → ℂ) :
    ‖∑ i : ι, g i * h i‖ ^ 2 ≤
    (∑ i : ι, ‖g i‖ ^ 2) * (∑ i : ι, ‖h i‖ ^ 2) := by
  have step1 : ‖∑ i : ι, g i * h i‖ ≤ ∑ i : ι, ‖g i * h i‖ :=
    norm_sum_le _ _
  have step2 : ∀ i, ‖g i * h i‖ = ‖g i‖ * ‖h i‖ := fun i => norm_mul _ _
  simp_rw [step2] at step1
  calc ‖∑ i, g i * h i‖ ^ 2
      ≤ (∑ i, ‖g i‖ * ‖h i‖) ^ 2 := by gcongr
    _ ≤ (∑ i, ‖g i‖ ^ 2) * (∑ i, ‖h i‖ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖g i‖) (fun i => ‖h i‖)

/-- Sum of ‖χ⁻¹(b)‖² over ZMod p is at most p. -/
private lemma sum_inv_char_norm_sq_le (χ : MulChar (ZMod p) ℂ) :
    ∑ b : ZMod p, ‖χ⁻¹ b‖ ^ 2 ≤ (p : ℝ) := by
  calc ∑ b : ZMod p, ‖χ⁻¹ b‖ ^ 2
      ≤ ∑ _b : ZMod p, (1 : ℝ) := by
        gcongr with b
        have h : ‖χ⁻¹ b‖ ≤ 1 := DirichletCharacter.norm_le_one χ⁻¹ b
        have h0 : (0 : ℝ) ≤ ‖χ⁻¹ b‖ := norm_nonneg _
        calc ‖χ⁻¹ b‖ ^ 2 = ‖χ⁻¹ b‖ * ‖χ⁻¹ b‖ := by ring
          _ ≤ 1 * 1 := mul_le_mul h h h0 zero_le_one
          _ = 1 := by ring
    _ = (p : ℝ) := by
        simp [Finset.sum_const, Finset.card_univ, ZMod.card p, nsmul_eq_mul, mul_one]

/-- Auxiliary: the character sum equals the Gauss-expanded form (full sum version). -/
private lemma char_sum_eq_gauss_exp (f : ZMod p → ℂ)
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) :
    ∑ n : ZMod p, f n * χ n =
    (gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)))⁻¹ *
    ∑ b : ZMod p, χ⁻¹ b *
      ∑ n : ZMod p, f n * (ZMod.stdAddChar (N := p)) (b * n) :=
  char_sum_to_exp_sum (S := Finset.univ) f χ hχ

set_option maxHeartbeats 1600000 in
/-- **Character sum norm squared bound via Gauss expansion**:
    For a nontrivial character χ on ZMod p (p prime) and any f : ZMod p → ℂ,

    ‖∑_n f(n) χ(n)‖² ≤ ∑_a ‖∑_n f(n) · ψ(a·n)‖²

    where ψ = stdAddChar. This bound converts a multiplicative character sum
    into a family of additive character (exponential) sums, which is the key
    step in the Gauss conductor transfer. -/
theorem char_sum_norm_sq_le_exp_sum (f : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) :
    ‖∑ n : ZMod p, f n * χ n‖ ^ 2 ≤
    ∑ a : ZMod p, ‖∑ n : ZMod p, f n * (ZMod.stdAddChar (N := p)) (a * n)‖ ^ 2 := by
  -- Use abbreviations with `set` to prevent unfolding
  set ψ := ZMod.stdAddChar (N := p)
  set τ := gaussSum χ⁻¹ ψ
  -- Step 1: Rewrite LHS using Gauss expansion
  rw [char_sum_eq_gauss_exp f χ hχ]
  -- Step 2: Factor out ‖τ⁻¹‖²
  rw [norm_mul, mul_pow]
  -- Abbreviate the inner double sum
  set T : ZMod p → ℂ := fun b => ∑ n : ZMod p, f n * ψ (b * n)
  -- Step 3: Cauchy-Schwarz on ∑ χ⁻¹(b) * T(b)
  have hCS := norm_sq_sum_mul_le (fun b : ZMod p => χ⁻¹ b) T
  -- Step 4: Bound on character norm sums
  have hchar_sq := sum_inv_char_norm_sq_le χ
  -- Step 5: Gauss sum norm
  have hτ_norm : ‖τ‖ ^ 2 = (p : ℝ) :=
    gaussSum_norm_sq_eq_prime χ⁻¹ (inv_ne_one.mpr hχ)
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.out.pos
  -- Step 6: ‖τ⁻¹‖² = 1/p
  have hτ_inv_norm : ‖τ⁻¹‖ ^ 2 = (p : ℝ)⁻¹ := by
    rw [norm_inv, inv_pow, hτ_norm]
  -- Step 7: Combine
  have hT_nonneg : (0 : ℝ) ≤ ∑ b : ZMod p, ‖T b‖ ^ 2 :=
    Finset.sum_nonneg (fun b _ => by positivity)
  calc ‖τ⁻¹‖ ^ 2 * ‖∑ b : ZMod p, χ⁻¹ b * T b‖ ^ 2
      ≤ ‖τ⁻¹‖ ^ 2 * ((∑ b : ZMod p, ‖χ⁻¹ b‖ ^ 2) *
        (∑ b : ZMod p, ‖T b‖ ^ 2)) := by
        gcongr
    _ ≤ ‖τ⁻¹‖ ^ 2 * ((p : ℝ) * (∑ b : ZMod p, ‖T b‖ ^ 2)) := by
        gcongr
    _ = (p : ℝ)⁻¹ * (p : ℝ) * (∑ b : ZMod p, ‖T b‖ ^ 2) := by
        rw [hτ_inv_norm]; ring
    _ = 1 * (∑ b : ZMod p, ‖T b‖ ^ 2) := by
        rw [inv_mul_cancel₀ (ne_of_gt hp_pos)]
    _ = ∑ b : ZMod p, ‖T b‖ ^ 2 := one_mul _

end CharSumExpBound

-- ============================================================================
-- §60. Parseval for multiplicative characters on (ZMod p)ˣ
-- ============================================================================
/-! ### §60. Parseval for multiplicative characters on (ZMod p)ˣ

For any function `g : (ZMod p)ˣ → ℂ`, we prove:
  ∑_{χ mod p} ‖∑_{a : units} g(a) · χ(a)‖² = (p-1) · ∑_{a : units} ‖g(a)‖²

This is the Parseval/Plancherel identity for the character group of (ZMod p)ˣ.
The proof expands the norm squared, swaps sums, and uses character orthogonality
(`DirichletCharacter.sum_characters_eq`).
-/

section CharParsevalUnits

open DirichletCharacter

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private instance neZeroP60 : NeZero p := ⟨hp.out.ne_zero⟩

/-- Character orthogonality on units using `sum_char_inv_mul_char_eq`:
    ∑_χ χ(↑a) * conj(χ(↑b)) = p.totient · [a = b]. -/
private lemma sum_char_unit_orth (a b : (ZMod p)ˣ) :
    ∑ χ : DirichletCharacter ℂ p,
      χ (↑a : ZMod p) * starRingEnd ℂ (χ (↑b : ZMod p)) =
    if a = b then ((p : ℕ).totient : ℂ) else 0 := by
  -- conj(χ(↑b)) = χ⁻¹(↑b) by mulChar_conj_eq_inv
  simp_rw [mulChar_conj_eq_inv _ b]
  -- χ⁻¹(↑b) = χ((↑b)⁻¹) by MulChar.inv_apply'
  simp_rw [MulChar.inv_apply' _ (↑b : ZMod p)]
  -- Rewrite as ∑_χ χ((↑b)⁻¹) * χ(↑a) by commutativity
  conv_lhs => arg 2; ext χ; rw [mul_comm]
  -- Now apply sum_char_inv_mul_char_eq with a := ↑b, b := ↑a
  have hb_unit : IsUnit (↑b : ZMod p) := Units.isUnit b
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb_unit]
  -- Goal: if ↑b = ↑a then totient else 0 = if a = b then totient else 0
  simp only [Units.val_injective.eq_iff, eq_comm]

/-- **ℂ-valued Parseval for multiplicative characters on (ZMod p)ˣ**:
    ∑_χ (∑_a g(a) χ(a)) * conj(∑_b g(b) χ(b)) = p.totient · ∑_a g(a) · conj(g(a)). -/
private lemma char_parseval_units_complex (g : (ZMod p)ˣ → ℂ) :
    ∑ χ : DirichletCharacter ℂ p,
      (∑ a : (ZMod p)ˣ, g a * χ (↑a)) *
      starRingEnd ℂ (∑ b : (ZMod p)ˣ, g b * χ (↑b)) =
    ((p : ℕ).totient : ℂ) * ∑ a : (ZMod p)ˣ, g a * starRingEnd ℂ (g a) := by
  -- Step 1: Expand conj of sum
  simp_rw [map_sum (starRingEnd ℂ), map_mul (starRingEnd ℂ)]
  -- Step 2: Expand product of sums to double sum
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  -- Step 3: Rearrange factors and swap summation
  -- After expansion, LHS = ∑_χ ∑_a ∑_b g(a) * χ(↑a) * (conj(g(b)) * conj(χ(↑b)))
  -- Rewrite each summand
  conv_lhs =>
    arg 2; ext χ; arg 2; ext a; arg 2; ext b
    rw [show g a * χ (↑a) * (starRingEnd ℂ (g b) * starRingEnd ℂ (χ (↑b))) =
        g a * starRingEnd ℂ (g b) * (χ (↑a) * starRingEnd ℂ (χ (↑b))) by ring]
  -- Swap ∑_χ with ∑_a ∑_b
  rw [Finset.sum_comm (s := Finset.univ)]
  simp_rw [Finset.sum_comm (s := Finset.univ (α := DirichletCharacter ℂ p))]
  -- Factor out g(a) * conj(g(b)) from inner ∑_χ
  simp_rw [← Finset.mul_sum]
  -- Apply orthogonality: ∑_χ χ(↑a) * conj(χ(↑b)) = totient · [a = b]
  simp_rw [sum_char_unit_orth]
  -- The inner sum over b with if a = b collapses to diagonal
  -- Each inner sum: ∑_b g(a)*conj(g(b)) * if a=b then tot else 0
  simp_rw [mul_ite, mul_zero]
  -- Now: ∑_b if a=b then g(a)*conj(g(b))*totient else 0
  -- Use Fintype.sum_ite_eq: ∑_b if a = b then f b else 0 = f a
  simp_rw [Fintype.sum_ite_eq]
  -- Now: ∑_a g(a) * conj(g(a)) * totient = totient * ∑_a g(a) * conj(g(a))
  rw [← Finset.sum_mul, mul_comm]

/-- **Parseval for multiplicative characters on (ZMod p)ˣ**:
    ∑_χ ‖∑_{a : units} g(a) · χ(a)‖² = (p-1) · ∑_{a : units} ‖g(a)‖². -/
theorem char_parseval_units (g : (ZMod p)ˣ → ℂ) :
    ∑ χ : DirichletCharacter ℂ p,
      ‖∑ a : (ZMod p)ˣ, g a * χ (↑a)‖ ^ 2 =
    ((p : ℝ) - 1) * ∑ a : (ZMod p)ˣ, ‖g a‖ ^ 2 := by
  -- Key identity: z * conj(z) = ↑(‖z‖²) for z : ℂ
  have hmc : ∀ z : ℂ, z * starRingEnd ℂ z = ↑(‖z‖ ^ 2 : ℝ) := by
    intro z; rw [Complex.mul_conj']; simp
  -- ℂ-valued Parseval
  have hparseval := char_parseval_units_complex g
  -- Rewrite RHS of Parseval using hmc
  simp_rw [hmc] at hparseval
  -- Now hparseval: ∑_χ ↑(‖S(χ)‖²) = totient * ∑_a ↑(‖g(a)‖²)
  -- Push ↑ through ∑
  simp_rw [← Complex.ofReal_sum] at hparseval
  -- totient(p) = p - 1
  have htot : ((p : ℕ).totient : ℂ) = ↑((p : ℝ) - 1) := by
    rw [Nat.totient_prime hp.out]
    push_cast
    simp [Nat.cast_sub hp.out.one_le]
  rw [htot] at hparseval
  -- Now hparseval: ↑(∑ ‖S(χ)‖²) = ↑((p-1) * ∑ ‖g(a)‖²)
  rw [← Complex.ofReal_mul] at hparseval
  exact Complex.ofReal_injective hparseval

end CharParsevalUnits

/-! ## S61. Uniform Points Well-Separated

For a prime p, the evaluation points {b/p : b ∈ Fin p} are (1/p)-well-separated
on ℝ/ℤ. This is needed to apply `weak_als_from_card_bound` in the GCT route.

The proof uses the key observation: for distinct b, b' ∈ {0,...,p-1}, let
d = b - b' as an integer, so 0 < |d| < p. Then p does not divide d, hence
d - p · round(d/p) is a nonzero integer, giving |d/p - round(d/p)| ≥ 1/p. -/

section UniformWellSep

/-- For nonzero integer d with |d| < p, the distance from d/p to the nearest
    integer is at least 1/p. Core arithmetic lemma for well-separation. -/
private theorem int_div_round_lower_bound {p : ℕ} (hp : 1 < p)
    (d : ℤ) (hd_ne : d ≠ 0) (hd_lt : |d| < (p : ℤ)) :
    (1 : ℝ) / (p : ℝ) ≤ |(↑d / (p : ℝ)) - ↑(round ((d : ℝ) / (p : ℝ)))| := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by positivity
  have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp_pos
  set m := round ((d : ℝ) / (p : ℝ)) with hm_def
  -- Key: |d/p - m| = |d - p*m| / p
  have hfactor : (↑d / (p : ℝ)) - ↑m = (↑d - ↑m * ↑p) / (p : ℝ) := by
    field_simp
  rw [hfactor, abs_div, abs_of_pos hp_pos]
  rw [div_le_div_iff_of_pos_right hp_pos]
  -- Goal: 1 ≤ |↑d - ↑m * ↑p|
  -- d - m*p is an integer and is nonzero (because p ∤ d)
  -- First show d - m*p ≠ 0
  suffices h : (↑d - ↑m * (p : ℝ)) ≠ 0 by
    have hint : ↑d - ↑m * (p : ℝ) = ((d - m * ↑p : ℤ) : ℝ) := by push_cast; ring
    rw [hint]
    rw [← Int.cast_abs]
    have hne : d - m * ↑p ≠ 0 := by
      intro heq; apply h; rw [hint]; simp [heq]
    exact_mod_cast Int.one_le_abs hne
  -- Show d - m*p ≠ 0, i.e., p ∤ d
  intro heq
  -- From heq: d = m * p as reals, so d = m * p as integers
  have hd_eq : d = m * ↑p := by
    have : (↑d : ℝ) = ↑m * (p : ℝ) := by linarith
    exact_mod_cast this
  -- d = m*p, |d| < p, d ≠ 0 → contradiction
  -- If m = 0 then d = 0, contradiction with hd_ne
  -- If |m| ≥ 1 then |d| = |m|*p ≥ p, contradiction with hd_lt
  rcases eq_or_ne m 0 with hm_zero | hm_ne
  · rw [hm_zero, zero_mul] at hd_eq; exact hd_ne hd_eq
  · have : (p : ℤ) ≤ |d| := by
      rw [hd_eq]
      have hm_abs : 1 ≤ |m| := Int.one_le_abs hm_ne
      have hp_nonneg : (0 : ℤ) ≤ ↑p := Int.natCast_nonneg p
      calc (p : ℤ) = 1 * |↑p| := by simp [abs_of_nonneg hp_nonneg]
        _ ≤ |m| * |↑p| := by exact mul_le_mul_of_nonneg_right hm_abs (abs_nonneg _)
        _ = |m * ↑p| := (abs_mul m ↑p).symm
    linarith

/-- The uniform points {b/p : b ∈ Fin p} are (1/p)-well-separated:
    for distinct r, s : Fin p, |r/p - s/p - round(r/p - s/p)| ≥ 1/p. -/
theorem uniform_points_well_separated {p : ℕ} (hp : 1 < p)
    (r s : Fin p) (hrs : r ≠ s) :
    (1 : ℝ) / (p : ℝ) ≤ |(↑(r : ℕ) / (p : ℝ) - ↑(s : ℕ) / (p : ℝ)) -
      round (↑(r : ℕ) / (p : ℝ) - ↑(s : ℕ) / (p : ℝ))| := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by positivity
  have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp_pos
  -- Rewrite r/p - s/p = (r - s)/p
  have hdiff : (↑(r : ℕ) : ℝ) / (p : ℝ) - ↑(s : ℕ) / (p : ℝ) =
      ((↑(r : ℕ) : ℤ) - ↑(s : ℕ) : ℤ) / (p : ℝ) := by
    push_cast; field_simp
  rw [hdiff]
  -- Apply the core lemma
  set d := ((r : ℕ) : ℤ) - ((s : ℕ) : ℤ) with hd_def
  apply int_div_round_lower_bound hp d
  · -- d ≠ 0
    intro heq
    apply hrs
    have : (r : ℕ) = (s : ℕ) := by omega
    exact Fin.ext this
  · -- |d| < p
    have hr := r.isLt
    have hs := s.isLt
    simp only [hd_def]
    rw [abs_lt]
    constructor <;> omega

end UniformWellSep

-- ============================================================================
-- §62. GCT Composition: Nontrivial Character Sum Bound
-- ============================================================================
/-! ### §62. GCT Composition: Nontrivial Character Sum Bound

Composing `char_sum_norm_sq_le_exp_sum` (§59) over all nontrivial characters,
using that there are at most p-1 such characters.

For any f : ZMod p → ℂ:

  ∑_{χ ≠ 1} ‖∑ f(n)χ(n)‖² ≤ (p-1) · ∑_a ‖∑ f(n)·ψ(a·n)‖²

This converts multiplicative character sums into exponential/additive sums,
which can then be bounded by the large sieve.
-/

section GCTComposition

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private instance neZeroP62 : NeZero p := ⟨hp.out.ne_zero⟩

/-- The number of Dirichlet characters mod p equals p - 1 (as a natural number). -/
private lemma dirichlet_card_eq_totient :
    Fintype.card (DirichletCharacter ℂ p) = (p : ℕ).totient := by
  rw [← Nat.card_eq_fintype_card]
  exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ p

/-- The number of Dirichlet characters mod p equals p - 1. -/
private lemma dirichlet_card_eq_pred :
    Fintype.card (DirichletCharacter ℂ p) = p - 1 := by
  rw [dirichlet_card_eq_totient, Nat.totient_prime hp.out]

open Classical in
/-- **GCT composition**: summing `char_sum_norm_sq_le_exp_sum` over all nontrivial
    characters gives a bound in terms of exponential sums.

    ∑\_{χ ≠ 1} ‖∑\_n f(n) χ(n)‖² ≤ (p-1) * ∑\_a ‖∑\_n f(n) * ψ(a*n)‖²

    where ψ = stdAddChar. -/
theorem gct_nontrivial_char_sum_le (f : ZMod p → ℂ) :
    (Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ ≠ 1)).sum
      (fun χ => ‖∑ n : ZMod p, f n * χ n‖ ^ 2) ≤
    ((p : ℝ) - 1) *
      ∑ a : ZMod p, ‖∑ n : ZMod p, f n * (ZMod.stdAddChar (N := p)) (a * n)‖ ^ 2 := by
  -- Abbreviate the exponential sum
  set S := ∑ a : ZMod p, ‖∑ n : ZMod p, f n * (ZMod.stdAddChar (N := p)) (a * n)‖ ^ 2
  set F := Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ ≠ 1)
  -- Each nontrivial χ satisfies the pointwise bound from §59
  have hpt : ∀ χ ∈ F, ‖∑ n : ZMod p, f n * χ n‖ ^ 2 ≤ S := by
    intro χ hχ
    rw [Finset.mem_filter] at hχ
    exact char_sum_norm_sq_le_exp_sum f χ hχ.2
  -- Sum ≤ |filter| • S via Finset.sum_le_card_nsmul
  have hcard_bound : F.sum (fun χ => ‖∑ n : ZMod p, f n * χ n‖ ^ 2) ≤ F.card • S :=
    Finset.sum_le_card_nsmul _ _ S hpt
  -- |filter| ≤ |univ| = p - 1
  have hfilter_le_univ : F.card ≤
      Finset.card (Finset.univ : Finset (DirichletCharacter ℂ p)) :=
    Finset.card_filter_le _ _
  have huniv_card :
      Finset.card (Finset.univ : Finset (DirichletCharacter ℂ p)) = p - 1 := by
    rw [Finset.card_univ, dirichlet_card_eq_pred]
  have hfilter_le : F.card ≤ p - 1 :=
    hfilter_le_univ.trans (le_of_eq huniv_card)
  -- Cast to ℝ
  have hfilter_le_real : (F.card : ℝ) ≤ (p : ℝ) - 1 := by
    calc (F.card : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hfilter_le
      _ = (p : ℝ) - 1 := by
          rw [Nat.cast_sub hp.out.one_le]; simp
  -- S is nonneg
  have hS_nonneg : (0 : ℝ) ≤ S := Finset.sum_nonneg (fun _ _ => by positivity)
  -- Combine
  calc F.sum (fun χ => ‖∑ n, f n * χ n‖ ^ 2)
      ≤ F.card • S := hcard_bound
    _ = ↑F.card * S := by rw [nsmul_eq_mul]
    _ ≤ ((p : ℝ) - 1) * S := by gcongr

end GCTComposition

/-! ## S63. GCT Full Character Sum Bound

Composing the GCT nontrivial character sum bound (S62) with Parseval (S53),
we prove that for any `f : ZMod p -> C`:

  `sum_chi ||sum_n f(n) chi(n)||^2 <= p^2 * sum_n ||f(n)||^2`

This bounds the total energy across ALL Dirichlet characters mod p,
completing the GCT composition for a single prime modulus.

The proof splits the sum into the trivial character (bounded by Cauchy-Schwarz)
and the nontrivial characters (bounded by `gct_nontrivial_char_sum_le` composed
with Parseval). The exponential sum energy is evaluated exactly via Parseval:

  `sum_a ||sum_n f(n) psi(a*n)||^2 = p * sum_n ||f(n)||^2`

which is proved by identifying the additive character sum with the DFT at `-a`.
-/

section GCTFullBound

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private instance neZeroP63 : NeZero p := ⟨hp.out.ne_zero⟩

open scoped ZMod

/-- The additive character sum `sum_n f(n) * psi(a*n)` equals the DFT of `f` at `-a`.

    Since `F f k = sum_j stdAddChar(-(j*k)) * f(j)`, we have
    `F f (-a) = sum_j stdAddChar(j*a) * f(j) = sum_j f(j) * stdAddChar(a*j)`. -/
theorem exp_sum_eq_dft_neg (f : ZMod p → ℂ) (a : ZMod p) :
    ∑ n : ZMod p, f n * (ZMod.stdAddChar (N := p)) (a * n) = 𝓕 f (-a) := by
  simp_rw [ZMod.dft_apply, smul_eq_mul]
  congr 1; ext n
  rw [show -(n * (-a)) = a * n from by ring]
  ring

/-- The exponential sum energy equals `p * sum ||f||^2` by Parseval.

    `sum_a ||sum_n f(n) * psi(a*n)||^2 = p * sum_n ||f(n)||^2`

    Proof: rewrite each sum as `F f (-a)`, use that negation is a bijection
    on `ZMod p` to get `sum_k ||F f k||^2`, then apply `zmod_dft_parseval`. -/
theorem exp_sum_energy_eq_parseval (f : ZMod p → ℂ) :
    ∑ a : ZMod p, ‖∑ n : ZMod p, f n * (ZMod.stdAddChar (N := p)) (a * n)‖ ^ 2 =
    (p : ℝ) * ∑ n : ZMod p, ‖f n‖ ^ 2 := by
  -- Step 1: Rewrite each inner sum as DFT at -a
  conv_lhs => arg 2; ext a; rw [exp_sum_eq_dft_neg f a]
  -- Step 2: Change of variables a -> -a (negation is a bijection)
  have h_neg_bij : ∑ a : ZMod p, ‖𝓕 f (-a)‖ ^ 2 = ∑ k : ZMod p, ‖𝓕 f k‖ ^ 2 :=
    Fintype.sum_equiv (Equiv.neg (ZMod p))
      (fun a => ‖𝓕 f (-a)‖ ^ 2)
      (fun k => ‖𝓕 f k‖ ^ 2)
      (fun a => by simp [Equiv.neg_apply])
  rw [h_neg_bij]
  -- Step 3: Apply Parseval
  exact zmod_dft_parseval f

/-- Cauchy-Schwarz for `ZMod p` sums: `||sum_n f(n)||^2 <= p * sum ||f(n)||^2`. -/
theorem norm_sq_sum_le_card_mul_zmod (f : ZMod p → ℂ) :
    ‖∑ n : ZMod p, f n‖ ^ 2 ≤ (p : ℝ) * ∑ n : ZMod p, ‖f n‖ ^ 2 := by
  have h1 : ‖∑ n : ZMod p, f n‖ ^ 2 ≤ (∑ n : ZMod p, ‖f n‖) ^ 2 := by
    gcongr; exact norm_sum_le _ _
  calc ‖∑ n : ZMod p, f n‖ ^ 2
      ≤ (∑ n : ZMod p, ‖f n‖) ^ 2 := h1
    _ = (∑ n : ZMod p, 1 * ‖f n‖) ^ 2 := by simp
    _ ≤ (∑ _n : ZMod p, (1 : ℝ) ^ 2) * (∑ n : ZMod p, ‖f n‖ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => 1) (fun n => ‖f n‖)
    _ = (p : ℝ) * ∑ n : ZMod p, ‖f n‖ ^ 2 := by
        simp [Finset.card_univ, ZMod.card]

/-- The trivial Dirichlet character applied to `n : ZMod p` is 1 when `n` is a unit
    and 0 otherwise. For p prime, this means it is 0 at 0 and 1 elsewhere.

    The character sum for the trivial character is `sum_{n != 0} f(n)`,
    bounded by `(p-1) * sum ||f||^2` via Cauchy-Schwarz over `p-1` terms. -/
theorem trivial_char_sum_bound (f : ZMod p → ℂ) :
    ‖∑ n : ZMod p, f n * (1 : DirichletCharacter ℂ p) n‖ ^ 2 ≤
    (p : ℝ) * ∑ n : ZMod p, ‖f n‖ ^ 2 := by
  -- The trivial character is ≤ 1 in norm, so |f(n) * χ(n)| ≤ |f(n)|
  calc ‖∑ n : ZMod p, f n * (1 : DirichletCharacter ℂ p) n‖ ^ 2
      ≤ (∑ n : ZMod p, ‖f n * (1 : DirichletCharacter ℂ p) n‖) ^ 2 := by
        gcongr; exact norm_sum_le _ _
    _ ≤ (∑ n : ZMod p, ‖f n‖) ^ 2 := by
        gcongr with n
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)
    _ = (∑ n : ZMod p, 1 * ‖f n‖) ^ 2 := by simp
    _ ≤ (∑ _n : ZMod p, (1 : ℝ) ^ 2) * (∑ n : ZMod p, ‖f n‖ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => 1) (fun n => ‖f n‖)
    _ = (p : ℝ) * ∑ n : ZMod p, ‖f n‖ ^ 2 := by
        simp [Finset.card_univ, ZMod.card]

open Classical in
/-- **GCT full character sum bound**: for a prime modulus p and any `f : ZMod p -> C`,

    `sum_chi ||sum_n f(n) chi(n)||^2 <= p^2 * sum_n ||f(n)||^2`

    This bounds the total energy of `f` across ALL Dirichlet characters mod p.

    **Proof**: Split the sum over characters into chi = 1 and chi != 1.
    - Trivial character: bounded by `p * sum ||f||^2` (Cauchy-Schwarz)
    - Nontrivial characters: by `gct_nontrivial_char_sum_le`, bounded by
      `(p-1) * sum_a ||sum_n f(n) psi(an)||^2`, and by Parseval
      (`exp_sum_energy_eq_parseval`) the exponential sum energy equals
      `p * sum ||f||^2`. So the nontrivial contribution is `(p-1)*p * sum ||f||^2`.
    - Total: `p + (p-1)*p = p^2`, giving `p^2 * sum ||f||^2`. -/
theorem gct_full_char_sum_bound (f : ZMod p → ℂ) :
    ∑ χ : DirichletCharacter ℂ p, ‖∑ n : ZMod p, f n * χ n‖ ^ 2 ≤
    (p : ℝ) ^ 2 * ∑ n : ZMod p, ‖f n‖ ^ 2 := by
  -- Abbreviate the energy
  set E := ∑ n : ZMod p, ‖f n‖ ^ 2
  -- Split sum into trivial and nontrivial characters
  set g : DirichletCharacter ℂ p → ℝ :=
    fun χ => ‖∑ n : ZMod p, f n * χ n‖ ^ 2
  have hsplit : ∑ χ : DirichletCharacter ℂ p, g χ =
      g 1 +
      (Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ ≠ 1)).sum g := by
    have hmem : (1 : DirichletCharacter ℂ p) ∈ Finset.univ := Finset.mem_univ _
    rw [← Finset.add_sum_erase _ _ hmem]
    congr 1
    apply Finset.sum_congr
    · ext χ
      simp [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, ne_eq, and_iff_left]
    · intros; rfl
  rw [hsplit]
  -- Bound trivial character
  have h_triv : g 1 ≤ (p : ℝ) * E := trivial_char_sum_bound f
  -- Bound nontrivial characters
  have h_nontriv : (Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ ≠ 1)).sum g ≤
      ((p : ℝ) - 1) * ((p : ℝ) * E) := by
    calc (Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ ≠ 1)).sum g
        ≤ ((p : ℝ) - 1) *
          ∑ a : ZMod p, ‖∑ n : ZMod p, f n * (ZMod.stdAddChar (N := p)) (a * n)‖ ^ 2 :=
          gct_nontrivial_char_sum_le f
      _ = ((p : ℝ) - 1) * ((p : ℝ) * E) := by
          congr 1; exact exp_sum_energy_eq_parseval f
  -- Combine: p * E + (p-1) * p * E = p^2 * E
  calc g 1 + (Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ ≠ 1)).sum g
      ≤ (p : ℝ) * E + ((p : ℝ) - 1) * ((p : ℝ) * E) := add_le_add h_triv h_nontriv
    _ = (p : ℝ) ^ 2 * E := by ring

end GCTFullBound

-- ============================================================================
-- §64. Prime Arithmetic Large Sieve via GCT
-- ============================================================================
/-! ## §64. Prime Arithmetic Large Sieve

For prime moduli, we can prove the arithmetic large sieve from the analytic one
via the Gauss sum expansion. The key steps:

1. Bridge: additive characters on ZMod p evaluated at integer arguments equal eAN
2. Gauss expansion for Fin N sequences: character sums become exponential sums
3. Apply ALS at evaluation points {b/p : b ∈ Fin p} with separation 1/p
4. Sum over characters using the GCT composition

Since `MultiModularCSB` only requires prime moduli, this suffices for the MC chain.
-/

section PrimeArithLS

open DirichletCharacter AddChar

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private instance neZeroP64 : NeZero p := ⟨hp.out.ne_zero⟩

/-- Bridge: the standard additive character on ZMod p applied to `b * (↑n : ZMod p)`
    equals `eAN(n * val(b) / p)` for any `b : ZMod p` and `n : ℤ`.

    Proof: both sides are equal to `eAN(val(b * ↑n) / p)` via `stdAddChar_val_eq_eAN`,
    and `val(b * ↑n) / p` and `val(b) * n / p` differ by an integer (ℤ-periodicity). -/
lemma stdAddChar_mul_intCast_eq_eAN (b : ZMod p) (n : ℤ) :
    (ZMod.stdAddChar (N := p) (b * (n : ZMod p)) : ℂ) =
    eAN ((n : ℝ) * (ZMod.val b : ℝ) / (p : ℝ)) := by
  rw [stdAddChar_val_eq_eAN]
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.out.pos
  -- Reduce to showing the arguments differ by an integer
  suffices h : ∃ k : ℤ, (ZMod.val (b * (n : ZMod p)) : ℤ) =
      ZMod.val b * n + k * p by
    obtain ⟨k, hk⟩ := h
    have : (ZMod.val (b * (n : ZMod p)) : ℝ) / (p : ℝ) =
        (n : ℝ) * (ZMod.val b : ℝ) / (p : ℝ) + (k : ℝ) := by
      field_simp
      have hk_real : (ZMod.val (b * (n : ZMod p)) : ℝ) =
          (ZMod.val b : ℝ) * (n : ℝ) + (k : ℝ) * (p : ℝ) := by
        exact_mod_cast hk
      linarith
    rw [this, eAN_add, eAN_intCast, mul_one]
  -- b * ↑n = ↑(val(b) * n) in ZMod p
  have hzmod : (b * (n : ZMod p) : ZMod p) = ((ZMod.val b * n : ℤ) : ZMod p) := by
    have hb : (b : ZMod p) = ((ZMod.val b : ℕ) : ZMod p) := by
      simp [ZMod.natCast_val]
    rw [hb]; push_cast
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt b)]
  -- So val(b * ↑n) (as ℤ) = (val(b)*n) % p  (by ZMod.val_intCast)
  have hval : (ZMod.val (b * (n : ZMod p)) : ℤ) = (ZMod.val b * n) % (p : ℤ) := by
    rw [show (ZMod.val (b * (n : ZMod p)) : ℤ) =
        (ZMod.val ((ZMod.val b * n : ℤ) : ZMod p) : ℤ) from by
      exact_mod_cast congr_arg ZMod.val hzmod]
    exact ZMod.val_intCast (ZMod.val b * n)
  -- (val(b)*n) % p = val(b)*n - p * ((val(b)*n) / p) by Int.emod_def
  rw [hval, Int.emod_def]
  exact ⟨-(ZMod.val b * n / (p : ℤ)), by ring⟩

/-- Gauss sum expansion for Fin N sequences: a character sum over Fin N equals
    a linear combination of exponential sums.

    `∑_{n:Fin N} a(n) χ(↑n) = τ⁻¹ ∑_b χ̄(b) ∑_n a(n) ψ(b·↑n)`

    where τ = gaussSum χ⁻¹ ψ. -/
lemma char_sum_gauss_expansion (N : ℕ) (a : Fin N → ℂ)
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) :
    ∑ n : Fin N, a n * χ ((↑(↑n : ℤ) : ZMod p)) =
    (gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)))⁻¹ *
    ∑ b : ZMod p, χ⁻¹ b *
      ∑ n : Fin N, a n * (ZMod.stdAddChar (N := p)) (b * (↑(↑n : ℤ) : ZMod p)) := by
  set ψ := ZMod.stdAddChar (N := p)
  set τ := gaussSum χ⁻¹ ψ
  have hne : τ ≠ 0 := gaussSum_stdAddChar_ne_zero χ⁻¹ (inv_ne_one.mpr hχ)
  -- Use Gauss inversion on each term
  have hinv : ∀ m : ZMod p,
      χ m = τ⁻¹ * ∑ b : ZMod p, χ⁻¹ b * ψ (b * m) := by
    intro m; rw [gauss_sum_inversion_sum χ hχ m]
  simp_rw [hinv]
  -- Now: ∑_n a(n) * (τ⁻¹ * ∑_b χ⁻¹(b) ψ(b·↑n))
  --    = τ⁻¹ * ∑_n ∑_b a(n) * χ⁻¹(b) * ψ(b·↑n)
  --    = τ⁻¹ * ∑_b χ⁻¹(b) * ∑_n a(n) * ψ(b·↑n)
  -- It suffices to show τ * LHS = τ * RHS (since τ ≠ 0)
  apply mul_left_cancel₀ hne
  rw [show τ * (τ⁻¹ * ∑ b : ZMod p, χ⁻¹ b *
      ∑ n : Fin N, a n * ψ (b * (↑(↑n : ℤ) : ZMod p))) =
    ∑ b : ZMod p, χ⁻¹ b * ∑ n : Fin N, a n * ψ (b * (↑(↑n : ℤ) : ZMod p))
    from by rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]]
  -- After multiplying by τ, LHS = ∑_n ∑_b τ * (a(n) * (τ⁻¹ * (χ⁻¹(b) * ψ(b·↑n))))
  simp_rw [Finset.mul_sum]
  -- Cancel τ * τ⁻¹ and rearrange each (n,b) summand
  have hcancel : τ * τ⁻¹ = 1 := mul_inv_cancel₀ hne
  -- Transform LHS summand to match RHS summand
  have hsummand : ∀ (n : Fin N) (b : ZMod p),
      τ * (a n * (τ⁻¹ * (χ⁻¹ b * (ψ (b * (↑(↑n : ℤ) : ZMod p)) : ℂ)))) =
      a n * χ⁻¹ b * (ψ (b * (↑(↑n : ℤ) : ZMod p)) : ℂ) := by
    intro n b
    calc τ * (a n * (τ⁻¹ * (χ⁻¹ b * (ψ (b * (↑(↑n : ℤ) : ZMod p)) : ℂ))))
        = (τ * τ⁻¹) * (a n * χ⁻¹ b * (ψ (b * (↑(↑n : ℤ) : ZMod p)) : ℂ)) := by ring
      _ = a n * χ⁻¹ b * (ψ (b * (↑(↑n : ℤ) : ZMod p)) : ℂ) := by rw [hcancel, one_mul]
  conv_lhs => arg 2; ext n; arg 2; ext b; rw [hsummand n b]
  -- Now swap sums ∑_n ∑_b → ∑_b ∑_n and factor out χ⁻¹(b)
  -- LHS is ∑_n ∑_b a(n)*χ⁻¹(b)*ψ(b·↑n)
  -- RHS is ∑_b χ⁻¹(b) * ∑_n a(n)*ψ(b·↑n)
  -- Transform to common form: ∑_b ∑_n χ⁻¹(b) * a(n) * ψ(b·↑n)
  -- Step 1: swap LHS to ∑_b ∑_n, then factor out χ⁻¹(b)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  have : ∀ n : Fin N, a n * χ⁻¹ b * (ψ (b * (↑(↑n : ℤ) : ZMod p)) : ℂ) =
      χ⁻¹ b * (a n * (ψ (b * (↑(↑n : ℤ) : ZMod p)) : ℂ)) := fun n => by ring
  simp_rw [this]

set_option maxHeartbeats 1600000 in
/-- **Character sum norm bound for Fin N sequences**: for nontrivial χ mod p (p prime),

    `‖∑_{n:Fin N} a(n) χ(↑n)‖² ≤ ∑_b ‖∑_n a(n) eAN(↑n · val(b)/p)‖²`

    Proof: Gauss expansion + Cauchy-Schwarz + Gauss norm cancellation. -/
private theorem char_sum_norm_sq_le_exp_sum_finN (N : ℕ) (a : Fin N → ℂ)
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) :
    ‖∑ n : Fin N, a n * χ ((↑(↑n : ℤ) : ZMod p))‖ ^ 2 ≤
    ∑ b : ZMod p, ‖∑ n : Fin N, a n *
      eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val b : ℝ) / (p : ℝ))‖ ^ 2 := by
  set ψ := ZMod.stdAddChar (N := p)
  set τ := gaussSum χ⁻¹ ψ
  -- Rewrite using the bridge lemma
  set T : ZMod p → ℂ := fun b => ∑ n : Fin N, a n *
    eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val b : ℝ) / (p : ℝ))
  -- First, show ψ(b·↑n) = eAN(n · val(b)/p) using bridge
  have hbridge : ∀ b : ZMod p, ∀ n : Fin N,
      (ψ (b * (↑(↑n : ℤ) : ZMod p)) : ℂ) =
      eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val b : ℝ) / (p : ℝ)) :=
    fun b n => stdAddChar_mul_intCast_eq_eAN b (↑n : ℤ)
  -- Rewrite character sum using Gauss expansion
  rw [char_sum_gauss_expansion N a χ hχ]
  -- Factor out ‖τ⁻¹‖²
  rw [norm_mul, mul_pow]
  -- Replace ψ(b·↑n) by eAN terms
  have hsum_eq : ∀ b : ZMod p,
      ∑ n : Fin N, a n * (ψ (b * (↑(↑n : ℤ) : ZMod p)) : ℂ) = T b := by
    intro b; congr 1; ext n; congr 1; exact hbridge b n
  conv_lhs => rw [show ∑ b : ZMod p, χ⁻¹ b *
      ∑ n : Fin N, a n * (ψ (b * (↑(↑n : ℤ) : ZMod p)) : ℂ) =
      ∑ b : ZMod p, χ⁻¹ b * T b from by congr 1; ext b; rw [hsum_eq]]
  -- Now: ‖τ⁻¹‖² * ‖∑_b χ⁻¹(b) T(b)‖² ≤ ∑_b ‖T(b)‖²
  -- Step: Cauchy-Schwarz
  have hCS := norm_sq_sum_mul_le (fun b : ZMod p => χ⁻¹ b) T
  have hchar_sq := sum_inv_char_norm_sq_le χ
  -- Gauss sum norm
  have hτ_norm : ‖τ‖ ^ 2 = (p : ℝ) := gaussSum_norm_sq_eq_prime χ⁻¹ (inv_ne_one.mpr hχ)
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.out.pos
  have hτ_inv_norm : ‖τ⁻¹‖ ^ 2 = (p : ℝ)⁻¹ := by rw [norm_inv, inv_pow, hτ_norm]
  have hT_nonneg : (0 : ℝ) ≤ ∑ b : ZMod p, ‖T b‖ ^ 2 :=
    Finset.sum_nonneg (fun b _ => by positivity)
  calc ‖τ⁻¹‖ ^ 2 * ‖∑ b : ZMod p, χ⁻¹ b * T b‖ ^ 2
      ≤ ‖τ⁻¹‖ ^ 2 * ((∑ b : ZMod p, ‖χ⁻¹ b‖ ^ 2) *
        (∑ b : ZMod p, ‖T b‖ ^ 2)) := by gcongr
    _ ≤ ‖τ⁻¹‖ ^ 2 * ((p : ℝ) * (∑ b : ZMod p, ‖T b‖ ^ 2)) := by gcongr
    _ = (p : ℝ)⁻¹ * (p : ℝ) * (∑ b : ZMod p, ‖T b‖ ^ 2) := by rw [hτ_inv_norm]; ring
    _ = 1 * (∑ b : ZMod p, ‖T b‖ ^ 2) := by rw [inv_mul_cancel₀ (ne_of_gt hp_pos)]
    _ = ∑ b : ZMod p, ‖T b‖ ^ 2 := one_mul _

end PrimeArithLS

-- ============================================================================
-- §65. Prime Arithmetic Large Sieve from Analytic Large Sieve
-- ============================================================================
/-! ## §65. Prime Arithmetic Large Sieve from Analytic Large Sieve

For each prime p and sequence `a : Fin N → ℂ`, the analytic large sieve implies:

  `∑_χ ‖∑_n a(n) χ(↑n)‖² ≤ p · (N - 1 + p) · ∑ ‖a(n)‖²`

**Proof strategy**:
- For nontrivial χ: by `char_sum_norm_sq_le_exp_sum_finN` (§64), the character sum norm
  squared is bounded by the exponential sum energy `∑_b ‖∑_n a(n) eAN(n·b/p)‖²`.
- The evaluation points `{b/p : b ∈ Fin p}` are `(1/p)`-separated by
  `uniform_points_well_separated` (§61).
- The ALS bounds this exponential sum energy by `(N-1+p) · ∑ ‖a(n)‖²`.
- Each nontrivial χ gets the SAME upper bound (independent of χ), so summing over
  p-1 nontrivial characters gives `(p-1)·(N-1+p) · ∑ ‖a(n)‖²`.
- The trivial character contributes at most `N · ∑ ‖a(n)‖² ≤ (N-1+p) · ∑ ‖a(n)‖²`.
- Total: `p · (N-1+p) · ∑ ‖a(n)‖²`.
-/

section PrimeArithLSFromALS

open DirichletCharacter AddChar

/-- **Prime Arithmetic Large Sieve**: for each prime p, every N ≥ 1, and every
    sequence `a : Fin N → ℂ`, the sum of character sum norms squared over ALL
    Dirichlet characters mod p is bounded:

    `∑_χ ‖∑_n a(n) χ(↑n)‖² ≤ p · (N - 1 + p) · ∑_n ‖a(n)‖²`

    This is the single-prime-modulus version of the arithmetic large sieve.
    The constant `p · (N-1+p)` is slightly worse than the optimal `(N-1+p²)`,
    but suffices for all downstream applications to MC. -/
def PrimeArithmeticLargeSieve : Prop :=
  ∀ (p : ℕ) (_hp : Nat.Prime p) (N : ℕ) (_hN : 0 < N) (a : Fin N → ℂ),
    ∑ χ : DirichletCharacter ℂ p, ‖∑ n : Fin N, a n * χ (↑(↑n : ℤ))‖ ^ 2
    ≤ (p : ℝ) * ((N : ℝ) - 1 + (p : ℝ)) * ∑ n : Fin N, ‖a n‖ ^ 2

open Classical in
set_option maxHeartbeats 3200000 in
/-- **ALS implies Prime Arithmetic Large Sieve**.

    Proof: Apply the ALS to the evaluation points `α_b = b/p` for `b : Fin p`,
    which are `(1/p)`-separated, then use the Gauss expansion bound
    (`char_sum_norm_sq_le_exp_sum_finN`) to bridge character sums to
    exponential sums. -/
theorem als_implies_prime_arith_ls (hals : AnalyticLargeSieve) :
    PrimeArithmeticLargeSieve := by
  intro p hp_prime N hN a
  haveI : Fact (Nat.Prime p) := ⟨hp_prime⟩
  -- Define evaluation points α_b = b/p for b : Fin p
  set α : Fin p → ℝ := fun b => (b : ℕ) / (p : ℝ) with hα_def
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_prime.pos
  have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp_pos
  have hp_ge2 : 1 < p := hp_prime.one_lt
  -- δ = 1/p
  set δ : ℝ := 1 / (p : ℝ)
  have hδ_pos : 0 < δ := div_pos one_pos hp_pos
  have hδ_le1 : δ ≤ 1 := by
    rw [div_le_one hp_pos]; exact_mod_cast hp_prime.one_le
  -- Separation: the evaluation points are δ-separated
  have hsep : ∀ r s : Fin p, r ≠ s →
      δ ≤ |α r - α s - round (α r - α s)| := by
    intro r s hrs
    exact uniform_points_well_separated hp_ge2 r s hrs
  -- Apply the ALS to get the exponential sum bound
  have hals_bound := hals N hN a p α δ hδ_pos hδ_le1 hsep
  -- Rewrite ALS LHS to eAN form
  rw [als_lhs_eq_eAN] at hals_bound
  -- Simplify δ⁻¹ = p
  have hδ_inv : δ⁻¹ = (p : ℝ) := by
    simp only [δ, one_div, inv_inv]
  rw [hδ_inv] at hals_bound
  -- Now: ∑_{b : Fin p} ‖∑_n a(n) · eAN(↑n · α_b)‖² ≤ (N - 1 + p) · ∑ ‖a(n)‖²
  set E := ∑ n : Fin N, ‖a n‖ ^ 2
  -- For each nontrivial χ: char sum ≤ exponential sum energy ≤ (N-1+p)·E
  -- The bridge between ZMod p and Fin p sums uses Equiv.sum_comp.
  have hnontriv : ∀ (χ : DirichletCharacter ℂ p), χ ≠ 1 →
      ‖∑ n : Fin N, a n * χ (↑(↑n : ℤ))‖ ^ 2 ≤
      ((N : ℝ) - 1 + (p : ℝ)) * E := by
    intro χ hχ
    -- §64 gives: ‖char sum‖² ≤ ∑_{b:ZMod p} ‖exp sum(b)‖²
    have h64 := char_sum_norm_sq_le_exp_sum_finN N a χ hχ
    -- Bound the ZMod p exponential sum energy by the ALS bound
    suffices hexp : ∑ b : ZMod p, ‖∑ n : Fin N, a n *
        eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val b : ℝ) / (p : ℝ))‖ ^ 2 ≤
        ((N : ℝ) - 1 + (p : ℝ)) * E from le_trans h64 hexp
    -- Reindex: use (ZMod.finEquiv p).symm to convert ZMod p → Fin p
    -- ∑_{b:ZMod p} f(b) = ∑_{r:Fin p} f(finEquiv r)
    set F : ZMod p → ℝ := fun b =>
      ‖∑ n : Fin N, a n *
        eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val b : ℝ) / (p : ℝ))‖ ^ 2
    -- Use Equiv.sum_comp for the reindexing
    have hreindex : ∑ b : ZMod p, F b =
        ∑ r : Fin p, F ((ZMod.finEquiv p) r) :=
      Eq.symm (Equiv.sum_comp (ZMod.finEquiv p).toEquiv F)
    rw [hreindex]
    -- For p prime, ZMod.val (finEquiv r) = r.val
    -- finEquiv for (n+1) is .refl, so this holds by rfl for concrete p
    -- For variable p, we case-split on p
    have hval_eq : ∀ r : Fin p, ZMod.val ((ZMod.finEquiv p) r) = r.val := by
      -- For p prime (hence p ≥ 1), ZMod p = Fin p and finEquiv is .refl
      -- We prove this by obtaining p = p'+1 and using definitional equality
      obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 :=
        ⟨p - 1, (Nat.succ_pred_eq_of_pos hp_prime.pos).symm⟩
      intro r; rfl
    -- Match summands
    have hF_eq : ∀ r : Fin p,
        F ((ZMod.finEquiv p) r) =
        ‖∑ n : Fin N, a n * eAN (↑(n : ℤ) * α r)‖ ^ 2 := by
      intro r; simp only [F, hval_eq, hα_def]; congr 2
      apply Finset.sum_congr rfl; intro n _; congr 1; congr 1; ring
    simp_rw [hF_eq]
    exact hals_bound
  -- For the trivial character: use Cauchy-Schwarz
  have htriv : ‖∑ n : Fin N, a n * (1 : DirichletCharacter ℂ p) (↑(↑n : ℤ))‖ ^ 2 ≤
      ((N : ℝ) - 1 + (p : ℝ)) * E := by
    -- Trivial char has norm ≤ 1, so |a(n) · χ₀(↑n)| ≤ |a(n)|
    have h1 : ‖∑ n : Fin N, a n * (1 : DirichletCharacter ℂ p) (↑(↑n : ℤ))‖ ^ 2 ≤
        (↑N * E) := by
      have hle : ‖∑ n : Fin N, a n * (1 : DirichletCharacter ℂ p) (↑(↑n : ℤ))‖ ^ 2 ≤
          (∑ n : Fin N, ‖a n * (1 : DirichletCharacter ℂ p) (↑(↑n : ℤ))‖) ^ 2 := by
        gcongr; exact norm_sum_le _ _
      calc ‖∑ n : Fin N, a n * (1 : DirichletCharacter ℂ p) (↑(↑n : ℤ))‖ ^ 2
          ≤ (∑ n : Fin N, ‖a n * (1 : DirichletCharacter ℂ p) (↑(↑n : ℤ))‖) ^ 2 := hle
        _ ≤ (∑ n : Fin N, ‖a n‖) ^ 2 := by
            gcongr with n
            rw [norm_mul]
            exact mul_le_of_le_one_right (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)
        _ = (∑ n : Fin N, 1 * ‖a n‖) ^ 2 := by simp
        _ ≤ (∑ _n : Fin N, (1 : ℝ) ^ 2) * (∑ n : Fin N, ‖a n‖ ^ 2) :=
            Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => 1) (fun n => ‖a n‖)
        _ = ↑N * E := by
            simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, E]
    -- N ≤ N - 1 + p since p ≥ 2
    have hN_le : (N : ℝ) ≤ (N : ℝ) - 1 + (p : ℝ) := by
      have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.one_le
      linarith
    have hE_nonneg : 0 ≤ E :=
      Finset.sum_nonneg (fun n _ => by positivity)
    calc ‖∑ n : Fin N, a n * (1 : DirichletCharacter ℂ p) (↑(↑n : ℤ))‖ ^ 2
        ≤ ↑N * E := h1
      _ ≤ ((N : ℝ) - 1 + (p : ℝ)) * E := by gcongr
  -- Now sum over ALL characters
  -- Split: ∑_χ = (sum over χ = 1) + (sum over χ ≠ 1)
  set g : DirichletCharacter ℂ p → ℝ :=
    fun χ => ‖∑ n : Fin N, a n * χ (↑(↑n : ℤ))‖ ^ 2
  have hsplit : ∑ χ : DirichletCharacter ℂ p, g χ =
      g 1 +
      (Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ ≠ 1)).sum g := by
    have hmem : (1 : DirichletCharacter ℂ p) ∈ Finset.univ := Finset.mem_univ _
    rw [← Finset.add_sum_erase _ _ hmem]
    congr 1
    apply Finset.sum_congr
    · ext χ
      simp [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, ne_eq, and_iff_left]
    · intros; rfl
  rw [hsplit]
  -- Bound the nontrivial sum
  have h_nontriv_sum :
      (Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ ≠ 1)).sum g ≤
      ((p : ℝ) - 1) * (((N : ℝ) - 1 + (p : ℝ)) * E) := by
    -- Each nontrivial χ contributes ≤ (N-1+p)·E
    -- There are at most p-1 nontrivial characters
    have hcard :
        ((Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ ≠ 1)).card : ℝ) ≤
        (p : ℝ) - 1 := by
      have hfle : (Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ ≠ 1)).card ≤
          p - 1 := by
        calc (Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ ≠ 1)).card
            ≤ Finset.card (Finset.univ : Finset (DirichletCharacter ℂ p)) :=
              Finset.card_filter_le _ _
          _ = p - 1 := by rw [Finset.card_univ, dirichlet_card_eq_pred]
      calc ((Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ ≠ 1)).card : ℝ)
          ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hfle
        _ = (p : ℝ) - 1 := by rw [Nat.cast_sub hp_prime.one_le]; simp
    calc (Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ ≠ 1)).sum g
        ≤ ∑ _χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ ≠ 1)),
            (((N : ℝ) - 1 + (p : ℝ)) * E) := by
          apply Finset.sum_le_sum
          intro χ hχ_mem
          have hχ : χ ≠ 1 := (Finset.mem_filter.mp hχ_mem).2
          exact hnontriv χ hχ
      _ = ((Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ ≠ 1)).card : ℝ) *
            (((N : ℝ) - 1 + (p : ℝ)) * E) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((p : ℝ) - 1) * (((N : ℝ) - 1 + (p : ℝ)) * E) := by
          apply mul_le_mul_of_nonneg_right hcard
          have hE_nonneg : 0 ≤ E := Finset.sum_nonneg (fun n _ => by positivity)
          have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.one_le
          have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
          nlinarith
  -- Combine
  have hE_nonneg : 0 ≤ E := Finset.sum_nonneg (fun n _ => by positivity)
  calc g 1 + (Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ ≠ 1)).sum g
      ≤ ((N : ℝ) - 1 + (p : ℝ)) * E +
        ((p : ℝ) - 1) * (((N : ℝ) - 1 + (p : ℝ)) * E) :=
        add_le_add htriv h_nontriv_sum
    _ = (1 + ((p : ℝ) - 1)) * (((N : ℝ) - 1 + (p : ℝ)) * E) := by ring
    _ = (p : ℝ) * (((N : ℝ) - 1 + (p : ℝ)) * E) := by
        congr 1
        have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.one_le
        linarith
    _ = (p : ℝ) * ((N : ℝ) - 1 + (p : ℝ)) * E := by ring

/-- **Transfer Prop**: PrimeArithmeticLargeSieve implies MultiModularCSB.
    This is the single-prime-modulus version of the ArithLS→MMCSB transfer.
    **Open Prop**: requires connecting the abstract large sieve bound to the
    EM walk character sum cancellation (the sieve-to-dynamics transfer). -/
def PrimeArithLSImpliesMMCSB : Prop :=
  PrimeArithmeticLargeSieve → MultiModularCSB

/-- **PrimeArithLS chain to MC**: composing PrimeArithLS with the transfer to MMCSB
    and the proved MMCSB→MC reduction. -/
theorem prime_arith_ls_chain_mc
    (hpals : PrimeArithmeticLargeSieve)
    (htransfer : PrimeArithLSImpliesMMCSB)
    (hfin : FiniteMCBelow (htransfer hpals).choose) :
    MullinConjecture :=
  mmcsb_implies_mc (htransfer hpals) hfin

/-- **ALS → PrimeArithLS → MC chain**: the full chain from analytic large sieve
    through the prime arithmetic large sieve to Mullin's Conjecture. -/
theorem als_prime_arith_ls_chain_mc
    (hals : AnalyticLargeSieve)
    (htransfer : PrimeArithLSImpliesMMCSB)
    (hfin : FiniteMCBelow (htransfer (als_implies_prime_arith_ls hals)).choose) :
    MullinConjecture :=
  prime_arith_ls_chain_mc (als_implies_prime_arith_ls hals) htransfer hfin

/-- **ALS + PrimeArithLS transfer with small threshold → MC unconditionally**. -/
theorem als_prime_arith_ls_small_threshold_mc
    (hals : AnalyticLargeSieve)
    (htransfer : PrimeArithLSImpliesMMCSB)
    (hsmall : (htransfer (als_implies_prime_arith_ls hals)).choose ≤ 11) :
    MullinConjecture :=
  mmcsb_small_threshold_mc (htransfer (als_implies_prime_arith_ls hals)) hsmall

end PrimeArithLSFromALS

-- ============================================================================
-- §81. Walk as Partial Product Sum
-- ============================================================================
/-!
## §81 Walk as Partial Product Sum

The walk character sum decomposes as a product of the initial character value
times a sum of partial products of multiplier character values:

  ∑_{n<N} χ(w(n)) = χ(w(0)) · ∑_{n<N} ∏_{k<n} χ(m(k))

This reformulation connects CCSB to the classical problem of partial product
equidistribution. The partial products P_n = ∏_{k<n} χ(m(k)) are d-th roots
of unity (where d = ord(χ)), and CCSB asks whether their sum cancels.

**Dead End #95 (Session 62)**: The "spectral gap" of the step distribution
(i.e., |∑ χ(m(k))|/N bounded away from 1) does NOT imply CCSB.
Counterexample: steps clumped as (1-δ)N kernel steps then δN escape steps
give spectral gap ρ < 1 but walk sum = (1-δ)N + O(1) = Θ(N).
Even Dec (step distribution perfectly equidistributed, ρ → 0) does NOT
imply CCSB: cycling steps 0,1,2 in Z/3Z satisfy Dec but the walk is
periodic with sum Θ(N). The gap between step-level frequency and walk-level
equidistribution is a fundamental ORDER-vs-FREQUENCY phenomenon.
-/

section WalkAsPartialProduct

open Euclid Mullin

/-- **Walk as partial product sum**: The walk character sum decomposes as
    the initial walk character value times a sum of partial products over
    the multiplier character values. -/
theorem walk_as_partial_product (q : ℕ) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ) =
    (χ (emWalkUnit q hq hne 0) : ℂ) *
    ∑ n ∈ Finset.range N, ∏ k ∈ Finset.range n, (χ (emMultUnit q hq hne k) : ℂ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _hn => ?_)
  have h := char_walk_multi_step q hq hne χ 0 n
  rw [zero_add] at h
  rw [show ∏ k ∈ Finset.range n, (χ (emMultUnit q hq hne k) : ℂ) =
           ∏ j ∈ Finset.range n, (χ (emMultUnit q hq hne (0 + j)) : ℂ) from
       Finset.prod_congr rfl (fun j _hj => by rw [zero_add])]
  exact h

end WalkAsPartialProduct

-- ============================================================================
-- §82. Dead End #96: LoD Scale Mismatch
-- ============================================================================
/-!
## §82 Dead End #96: LoD Scale Mismatch

The "Level of Distribution" (LoD) approach defines character sum bounds at moduli
`q ≤ (prod N)^θ / (log prod N)^A`. The error term in such bounds is typically
of order `(prod N)^θ / (log prod N)^A`.

**Dead End #96**: This error term grows EXPONENTIALLY in N, since
`prod N ≥ 2^N` (by `prod_exponential_lower`). Specifically:
- `(prod N)^θ ≥ (2^N)^θ = 2^{θN}`, which is exponential in N.
- MMCSB requires walk character sums bounded by `ε * N` (linear in N).
- For any fixed `θ > 0`, eventually `(prod N)^θ > ε * N` for any `ε > 0`.

Therefore the LoD bound is WEAKER than the trivial bound `N` for large `N`.
The open Prop `LoDImpliesMMCSB` is vacuously unprovable: the LoD hypothesis
gives a character sum bound that grows exponentially, while MMCSB needs `o(N)`.

The correct analogue of "level of distribution" for the EM sequence would need
error terms measured relative to N (not relative to prod N), but this is NOT
what the standard LoD formulation provides.

### Main results

* `exp_dominates_linear` : `C * N < 2^N` for all sufficiently large N
* `prod_superlinear` : `C * N < prod N` for all sufficiently large N
-/

section LoDScaleMismatch

open Euclid Mullin Filter Asymptotics

/-- **Exponential eventually dominates linear**: for any `C > 0`,
    eventually `C * n < 2^n`. This is a consequence of
    `n = o(2^n)` (from `isLittleO_coe_const_pow_of_one_lt`). -/
theorem exp_dominates_linear (C : ℝ) (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → C * ↑N < (2 : ℝ) ^ N := by
  -- From n = o(2^n), extract: eventually ‖n‖ ≤ (1/(C+1)) * ‖2^n‖
  have ho := isLittleO_coe_const_pow_of_one_lt (R := ℝ) (one_lt_two)
  have hC1 : (0 : ℝ) < 1 / (C + 1) := div_pos one_pos (by linarith)
  rw [isLittleO_iff] at ho
  have hev := ho hC1
  rw [eventually_atTop] at hev
  obtain ⟨N₀, hN₀⟩ := hev
  refine ⟨N₀, fun N hN => ?_⟩
  have hNN := hN₀ N hN
  -- hNN : ‖(↑N : ℝ)‖ ≤ 1 / (C + 1) * ‖(2 : ℝ) ^ N‖
  rw [Real.norm_of_nonneg (Nat.cast_nonneg' N),
      Real.norm_of_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) N)] at hNN
  -- hNN : (↑N : ℝ) ≤ 1 / (C + 1) * 2 ^ N
  -- Goal : C * ↑N < 2 ^ N
  -- Multiply both sides by (C + 1) to get (C + 1) * N ≤ 2^N
  have hC1_pos : (0 : ℝ) < C + 1 := by linarith
  -- From hNN: N ≤ 2^N / (C + 1), so (C + 1) * N ≤ 2^N
  have h1 : (C + 1) * ↑N ≤ (2 : ℝ) ^ N := by
    rw [one_div, mul_comm (C + 1)⁻¹, ← div_eq_mul_inv, le_div_iff₀ hC1_pos] at hNN
    linarith
  -- Now C * N < (C + 1) * N ≤ 2^N (when N > 0); and C * 0 = 0 < 1 ≤ 2^0 when N = 0
  by_cases hN0 : N = 0
  · simp [hN0]
  · have hN_pos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN0)
    nlinarith

/-- **The running product is eventually superlinear**: for any `C > 0`,
    eventually `C * N < prod N`. This follows from `prod N ≥ 2^N`
    (exponential lower bound) and `2^N` eventually exceeding `C * N`.

    **Dead End #96**: Since `prod N` grows exponentially, `(prod N)^θ`
    for any `θ > 0` also grows exponentially. The LoD error term
    `(prod N)^θ / (log prod N)^A` therefore grows exponentially in N,
    making it useless as an `o(N)` bound. `LoDImpliesMMCSB` is vacuous. -/
theorem prod_superlinear (C : ℝ) (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → C * ↑N < (prod N : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := exp_dominates_linear C hC
  refine ⟨N₀, fun N hN => ?_⟩
  have h2N := hN₀ N hN
  have hprod : (2 : ℝ) ^ N ≤ (prod N : ℝ) := by
    have := prod_exponential_lower N
    exact_mod_cast this
  linarith

end LoDScaleMismatch
