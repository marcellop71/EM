import EM.LargeSieve.Analytic

/-!
# Prime Arithmetic Large Sieve via GCT, Walk Products, and LoD Dead End

For prime moduli, the analytic large sieve implies the arithmetic large sieve
via the Gauss sum expansion and GCT composition. This file also contains the
walk-as-partial-product reformulation and the LoD scale mismatch dead end.

## Main Results

* `stdAddChar_mul_intCast_eq_eAN` : additive character bridge to eAN (PROVED)
* `char_sum_gauss_expansion` : Gauss expansion for Fin N sequences (PROVED)
* `als_implies_prime_arith_ls` : ALS → PrimeArithmeticLargeSieve (PROVED)
* `walk_as_partial_product` : walk char sum = initial × sum of partial products (PROVED)
* `exp_dominates_linear` : exponential eventually dominates linear (PROVED)
* `prod_superlinear` : prod N eventually superlinear (PROVED, Dead End #96)
-/

open Mullin Euclid MullinGroup RotorRouter

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
theorem stdAddChar_mul_intCast_eq_eAN (b : ZMod p) (n : ℤ) :
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
theorem char_sum_gauss_expansion (N : ℕ) (a : Fin N → ℂ)
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
  have : Fact (Nat.Prime p) := ⟨hp_prime⟩
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
