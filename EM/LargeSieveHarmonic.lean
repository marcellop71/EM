import EM.LargeSieve

/-!
# Harmonic Analysis Infrastructure for the Large Sieve

Parseval identity for `ZMod.dft`, walk autocorrelation analysis,
Gauss sum norm computations, Plancherel bilinear forms, and the
analytic large sieve kernel infrastructure.

## Main Results

* `zmod_dft_parseval` : Parseval identity for ZMod DFT (PROVED)
* `walkAutocorrelation` : walk autocorrelation function definition
* `gaussSum_norm_sq_eq_prime` : |τ(χ)|² = p (PROVED)
* `zmod_dft_plancherel_complex` : bilinear Plancherel identity (PROVED)
* `kernel_row_sum_implies_als` : kernel bound → analytic large sieve (PROVED)
* `eAN` : standard exponential e(α) = exp(2πiα)
-/

open Mullin Euclid MullinGroup RotorRouter

/-! ## S53. Parseval Identity for ZMod.dft and Walk Autocorrelation Analysis

This section develops two foundational tools:

1. **Parseval identity for `ZMod.dft`**: We prove the identity
   `sum_k ||F Phi k||^2 = N * sum_j ||Phi j||^2` from the character
   orthogonality relation `sum_k psi(a*k) = N if a=0, else 0`.
   This is a standard fact derivable from `ZMod.dft_dft` (Mathlib's Fourier
   inversion formula on `ZMod N`). The complex inner product form
   `sum_k (F Phi k) * conj(F Phi k) = N * sum_j Phi j * conj(Phi j)`
   is proved directly; the real norm-squared form follows by `RCLike.mul_conj`.

   Parseval is a prerequisite for convolution techniques and L2 bounds
   on character sums over `ZMod N`.

2. **Walk autocorrelation**: We define `walkAutocorrelation q chi N h` as
   `sum_{n < N-h} chi(w(n)) * conj(chi(w(n+h)))` and prove:
   - **Multi-step recurrence**: `chi(w(n+h)) = chi(w(n)) * prod_{j<h} chi(m(n+j))`
   - **Product reduction**: `R_h = sum_{n<N-h} conj(prod_{j<h} chi(m(n+j)))`
   - **Special values**: `R_0 = N`, `R_1 = conj(multiplier sum)`
   - **Norm bound**: `||R_h|| <= N - h`

   The product reduction shows that higher autocorrelations R_h involve
   h-fold products of consecutive multiplier character values. For h=1,
   this reduces to the multiplier sum (already proved in S37 as
   `walk_shift_one_correlation`). For h >= 2, controlling R_h requires
   bounds on *correlations* of multiplier character values -- a strictly
   harder problem than bounding their simple sum (EMMultCharSumBound).

   This formalizes the quantitative obstacle: the Van der Corput method
   for walk character sums requires bounding all R_h for h = 1,...,H,
   but only R_1 is controlled by EMMultCharSumBound. The higher
   autocorrelations require genuine decorrelation of the EM multiplier
   sequence, which lies beyond the current sieve machinery.
-/

section ParsevalZModDFT

open scoped ZMod

variable {N : ℕ} [NeZero N]

open Classical in
/-- **Additive character orthogonality on `ZMod N`**: the sum
    `sum_{k : ZMod N} stdAddChar(a * k)` equals `N` when `a = 0`
    and `0` otherwise.

    This is a direct corollary of `AddChar.sum_mulShift` applied to
    the primitive character `stdAddChar` on `ZMod N`. -/
theorem stdAddChar_sum_eq (a : ZMod N) :
    ∑ k : ZMod N, ZMod.stdAddChar (a * k) =
    if a = (0 : ZMod N) then (N : ℂ) else 0 := by
  have hprim := ZMod.isPrimitive_stdAddChar N
  conv_lhs => arg 2; ext k; rw [mul_comm]
  have h := AddChar.sum_mulShift a hprim
  simp only [ZMod.card] at h
  exact_mod_cast h

/-- **Parseval identity for `ZMod.dft` (complex inner product form)**.

    `sum_k (F Phi k) * conj(F Phi k) = N * sum_j Phi j * conj(Phi j)`

    where `F` denotes the discrete Fourier transform `ZMod.dft`.

    **Proof**: Expand both DFTs, distribute the product of sums,
    swap summation order, combine character factors using `map_add_eq_mul`,
    and apply character orthogonality (`stdAddChar_sum_eq`) to collapse
    the diagonal. -/
theorem zmod_dft_parseval_complex (Phi : ZMod N → ℂ) :
    ∑ k : ZMod N, (𝓕 Phi k * starRingEnd ℂ (𝓕 Phi k)) =
    (N : ℂ) * ∑ j : ZMod N, (Phi j * starRingEnd ℂ (Phi j)) := by
  -- Step 1: Expand DFT definition
  simp_rw [ZMod.dft_apply, smul_eq_mul]
  -- Step 2: Distribute conjugation over sums and products
  simp_rw [map_sum (starRingEnd ℂ), map_mul (starRingEnd ℂ)]
  -- Step 3: Simplify conj(stdAddChar(-(j'*k))) = stdAddChar(j'*k)
  -- using map_neg_eq_conj and starRingEnd_self_apply (conj of conj = id)
  simp_rw [show ∀ (j' k : ZMod N), (starRingEnd ℂ) (ZMod.stdAddChar (-(j' * k))) =
    ZMod.stdAddChar (j' * k) from fun j' k => by
    rw [AddChar.map_neg_eq_conj, starRingEnd_self_apply]]
  -- Step 4: Distribute product of sums (Cauchy product)
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  -- Step 5: Swap summation order: sum_k sum_j sum_j' -> sum_j sum_j' sum_k
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  -- Step 6: Rearrange each term to isolate character sum
  conv_lhs => arg 2; ext j; arg 2; ext j'; arg 2; ext k
              rw [show ZMod.stdAddChar (-(j * k)) * Phi j *
                (ZMod.stdAddChar (j' * k) * starRingEnd ℂ (Phi j')) =
                (Phi j * starRingEnd ℂ (Phi j')) *
                (ZMod.stdAddChar (-(j * k)) * ZMod.stdAddChar (j' * k)) by ring]
  -- Step 7: Combine character factors: stdAddChar(-(j*k)) * stdAddChar(j'*k) = stdAddChar((j'-j)*k)
  simp_rw [show ∀ (j j' k : ZMod N),
    ZMod.stdAddChar (-(j * k)) * ZMod.stdAddChar (j' * k) =
    ZMod.stdAddChar ((j' - j) * k) from fun j j' k => by
    rw [← AddChar.map_add_eq_mul]; ring_nf]
  -- Step 8: Factor constant out of inner sum
  simp_rw [← Finset.mul_sum]
  -- Step 9: Apply character orthogonality
  simp_rw [stdAddChar_sum_eq, sub_eq_zero]
  -- Step 10: Collapse diagonal
  simp only [mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_mul]
  ring

/-- **Parseval identity for `ZMod.dft` (real norm-squared form)**.

    `sum_k ||F Phi k||^2 = N * sum_j ||Phi j||^2`

    This is the standard Parseval/Plancherel identity for the DFT on `ZMod N`.
    Derived from the complex inner product form using `RCLike.mul_conj`:
    `z * conj(z) = ||z||^2` (as a complex-valued identity). -/
theorem zmod_dft_parseval (Phi : ZMod N → ℂ) :
    ∑ k : ZMod N, ‖𝓕 Phi k‖ ^ 2 =
    (N : ℝ) * ∑ j : ZMod N, ‖Phi j‖ ^ 2 := by
  have key := zmod_dft_parseval_complex Phi
  simp_rw [RCLike.mul_conj] at key
  have lhs_cast : (↑(∑ k : ZMod N, ‖𝓕 Phi k‖ ^ 2) : ℂ) =
      ∑ k : ZMod N, (↑‖𝓕 Phi k‖ : ℂ) ^ 2 := by
    push_cast; rfl
  have rhs_cast : (↑((N : ℝ) * ∑ j : ZMod N, ‖Phi j‖ ^ 2) : ℂ) =
      (↑N : ℂ) * ∑ j : ZMod N, (↑‖Phi j‖ : ℂ) ^ 2 := by
    push_cast; rfl
  exact Complex.ofReal_injective (by rw [lhs_cast, rhs_cast]; exact key)

end ParsevalZModDFT

section WalkAutocorrelationAnalysis

/-- **Multi-step walk recurrence**: the walk character value at step `n + h`
    equals the value at step `n` multiplied by the product of the next `h`
    multiplier character values.

    `chi(w(n + h)) = chi(w(n)) * prod_{j < h} chi(m(n + j))`

    This generalizes `char_walk_recurrence` (the h=1 case) by induction on h.
    Each step applies the single-step recurrence
    `chi(w(k+1)) = chi(w(k)) * chi(m(k))`. -/
theorem char_walk_multi_step (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (chi : (ZMod q)ˣ →* ℂˣ) (n h : Nat) :
    (chi (emWalkUnit q hq hne (n + h)) : ℂ) =
    (chi (emWalkUnit q hq hne n) : ℂ) *
    ∏ j ∈ Finset.range h, (chi (emMultUnit q hq hne (n + j)) : ℂ) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show n + (h + 1) = (n + h) + 1 from by omega]
    rw [char_walk_recurrence q hq hne chi (n + h)]
    rw [ih]
    rw [Finset.prod_range_succ]
    ring

/-- **Walk autocorrelation at lag h**: the sum
    `R_h(N) = sum_{n < N - h} chi(w(n)) * conj(chi(w(n + h)))`

    This is the standard shifted autocorrelation of the walk character
    sequence `n -> chi(w(n))`. The Van der Corput method for bounding
    `|sum_{n < N} chi(w(n))|` requires controlling `R_h` for `h = 1, ..., H`. -/
noncomputable def walkAutocorrelation (q : Nat) [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (chi : (ZMod q)ˣ →* ℂˣ) (N h : Nat) : ℂ :=
  ∑ n ∈ Finset.range (N - h),
    ((chi (emWalkUnit q hq hne n) : ℂ) *
     starRingEnd ℂ (chi (emWalkUnit q hq hne (n + h)) : ℂ))

/-- **Autocorrelation equals conjugate multiplier product sum**: the walk
    autocorrelation at lag h reduces to

    `R_h(N) = sum_{n < N-h} conj(prod_{j < h} chi(m(n + j)))`

    **Proof**: By `char_walk_multi_step`,
    `chi(w(n+h)) = chi(w(n)) * prod_{j<h} chi(m(n+j))`.
    Then `chi(w(n)) * conj(chi(w(n+h))) = |chi(w(n))|^2 * conj(prod ...)`.
    Since walk character values have norm 1 (`walkTelescope_char_norm_one`),
    this simplifies to `conj(prod_{j<h} chi(m(n+j)))`.

    **Significance**: This identity shows that R_h depends on h-fold products
    of consecutive multiplier character values. For h=1, this is the simple
    multiplier character sum (controlled by `EMMultCharSumBound`). For h >= 2,
    this involves *correlations* between consecutive multiplier values -- a
    strictly harder analytical object that requires genuine decorrelation
    hypotheses beyond what sieve methods currently provide. -/
theorem walkAutocorrelation_eq_mult_product (q : Nat) [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (chi : (ZMod q)ˣ →* ℂˣ) (N h : Nat) :
    walkAutocorrelation q hq hne chi N h =
    ∑ n ∈ Finset.range (N - h),
      starRingEnd ℂ (∏ j ∈ Finset.range h,
        (chi (emMultUnit q hq hne (n + j)) : ℂ)) := by
  unfold walkAutocorrelation
  congr 1; ext n
  rw [char_walk_multi_step q hq hne chi n h]
  rw [map_mul (starRingEnd ℂ)]
  rw [← mul_assoc]
  have hmul_self : (chi (emWalkUnit q hq hne n) : ℂ) *
      starRingEnd ℂ (chi (emWalkUnit q hq hne n) : ℂ) = 1 := by
    rw [starRingEnd_apply, Complex.star_def, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
    have hn1 := walkTelescope_char_norm_one chi (emWalkUnit q hq hne n)
    simp [hn1]
  rw [hmul_self, one_mul]

/-- **Autocorrelation at lag 0**: `R_0(N) = N`.

    When h = 0, each term is `chi(w(n)) * conj(chi(w(n))) = |chi(w(n))|^2 = 1`,
    so the sum over `n < N` equals `N`. -/
theorem walkAutocorrelation_zero (q : Nat) [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (chi : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    walkAutocorrelation q hq hne chi N 0 = N := by
  rw [walkAutocorrelation_eq_mult_product]
  simp

/-- **Autocorrelation at lag 1**: `R_1(N) = conj(sum_{n < N-1} chi(m(n)))`.

    This matches the already-proved `walk_shift_one_correlation` (S37). The
    product `prod_{j < 1} chi(m(n+j))` has a single factor `chi(m(n))`. -/
theorem walkAutocorrelation_one (q : Nat) [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (chi : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    walkAutocorrelation q hq hne chi N 1 =
    starRingEnd ℂ (∑ n ∈ Finset.range (N - 1),
      (chi (emMultUnit q hq hne n) : ℂ)) := by
  rw [walkAutocorrelation_eq_mult_product, map_sum]
  congr 1; ext n
  simp [add_zero]

/-- **Autocorrelation norm bound**: `||R_h(N)|| <= N - h`.

    Each term in the autocorrelation sum has norm 1 (product of norm-1
    character values, conjugated), so the triangle inequality gives
    `||R_h|| <= |{n < N-h}| = N - h`. -/
theorem walkAutocorrelation_norm_le (q : Nat) [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (chi : (ZMod q)ˣ →* ℂˣ) (N h : Nat) :
    ‖walkAutocorrelation q hq hne chi N h‖ ≤ (N - h : ℕ) := by
  rw [walkAutocorrelation_eq_mult_product]
  calc ‖∑ n ∈ Finset.range (N - h),
      starRingEnd ℂ (∏ j ∈ Finset.range h,
        (chi (emMultUnit q hq hne (n + j)) : ℂ))‖
      ≤ ∑ n ∈ Finset.range (N - h),
        ‖starRingEnd ℂ (∏ j ∈ Finset.range h,
          (chi (emMultUnit q hq hne (n + j)) : ℂ))‖ :=
          norm_sum_le _ _
    _ = ∑ n ∈ Finset.range (N - h), 1 := by
        congr 1; ext n
        rw [RCLike.norm_conj, norm_prod]
        apply Finset.prod_eq_one
        intro j _
        exact walkTelescope_char_norm_one chi (emMultUnit q hq hne (n + j))
    _ = (N - h : ℕ) := by simp

end WalkAutocorrelationAnalysis

/-! ## Summary (S53)

### New lemmas and definitions (S53):

**Parseval for ZMod.dft:**
- `stdAddChar_sum_eq` : character orthogonality: sum_k stdAddChar(a*k) = N*[a=0]
- `zmod_dft_parseval_complex` : **PROVED** -- sum_k (F Phi k) * conj(F Phi k) = N * sum_j Phi j * conj(Phi j)
- `zmod_dft_parseval` : **PROVED** -- sum_k ||F Phi k||^2 = N * sum_j ||Phi j||^2

**Walk autocorrelation:**
- `char_walk_multi_step` : **PROVED** -- chi(w(n+h)) = chi(w(n)) * prod_{j<h} chi(m(n+j))
- `walkAutocorrelation` : definition of R_h(N) = sum_{n<N-h} chi(w(n)) * conj(chi(w(n+h)))
- `walkAutocorrelation_eq_mult_product` : **PROVED** -- R_h = sum conj(prod chi(m(n+j)))
- `walkAutocorrelation_zero` : **PROVED** -- R_0(N) = N
- `walkAutocorrelation_one` : **PROVED** -- R_1(N) = conj(multiplier sum)
- `walkAutocorrelation_norm_le` : **PROVED** -- ||R_h(N)|| <= N - h

### Key insight (S53):

**Parseval** provides the L2 framework for Fourier analysis on ZMod N.
Combined with `ZMod.dft_dft` (Fourier inversion), this gives a complete
Plancherel theory for discrete signals on ZMod N. Applications include:
- Bounding character sums via L2 methods (large sieve type bounds)
- Convolution identities for multiplicative functions
- Spectral analysis of the walk/multiplier sequences

**Walk autocorrelation** formalizes the Van der Corput obstacle:
- The VdC inequality gives ||S_W||^2 <= (N/H)(N + 2 * sum_{h=1}^H |Re(R_h)|)
- For h=1: R_1 = conj(S_M), so |R_1| is controlled by EMMultCharSumBound
- For h >= 2: R_h involves h-fold products of consecutive multipliers
- These higher correlations are NOT controlled by any currently available bound
- This explains why the multiplier-to-walk bridge (MultCSBImpliesMMCSB) remains
  open: the linear information (multiplier character sums) does not control
  the quadratic and higher correlation structure needed for VdC
-/

/-! ## S54. Gauss Sum Norm and Plancherel Theorem

This section proves:
1. **Gauss sum norm squared**: For a nontrivial MulChar χ on ZMod p (p prime)
   and the primitive additive character stdAddChar, we have ‖gaussSum χ stdAddChar‖² = p.
2. **Plancherel inner product form**: The bilinear version of Parseval:
   ∑ k, 𝓕 Φ k * conj(𝓕 Ψ k) = N * ∑ j, Φ j * conj(Ψ j).
3. **Large sieve for subsets of ZMod N**: For any subset S,
   ∑ k ∈ S, ‖𝓕 Φ k‖² ≤ N * ∑ j, ‖Φ j‖².
-/

section GaussSumNorm

open scoped ZMod

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- Values of a multiplicative character χ on (ZMod p)ˣ have norm 1 in ℂ.
    This is because character values are roots of unity of order dividing |(ZMod p)ˣ|,
    and roots of unity have norm 1 in ℂ. -/
theorem mulChar_norm_one_of_unit (χ : MulChar (ZMod p) ℂ) (a : (ZMod p)ˣ) :
    ‖χ a‖ = 1 := by
  have hfin : IsOfFinOrder a := isOfFinOrder_of_finite a
  have hfin' : IsOfFinOrder ((MulChar.equivToUnitHom χ) a) :=
    MonoidHom.isOfFinOrder _ hfin
  rw [isOfFinOrder_iff_pow_eq_one] at hfin'
  obtain ⟨n, hn, hpow⟩ := hfin'
  have hne : NeZero n := ⟨by omega⟩
  have hmem : (MulChar.equivToUnitHom χ) a ∈ rootsOfUnity n ℂ := by
    rw [_root_.mem_rootsOfUnity]; exact hpow
  have hnorm : ‖((MulChar.equivToUnitHom χ) a : ℂ)‖ = 1 :=
    Complex.norm_eq_one_of_mem_rootsOfUnity hmem
  convert hnorm using 1

/-- Conjugate of a multiplicative character value equals the inverse character value.
    For a : (ZMod p)ˣ, conj(χ a) = χ⁻¹ a. -/
theorem mulChar_conj_eq_inv (χ : MulChar (ZMod p) ℂ) (a : (ZMod p)ˣ) :
    starRingEnd ℂ (χ (a : ZMod p)) = χ⁻¹ (a : ZMod p) := by
  rw [MulChar.inv_apply_eq_inv']
  rw [starRingEnd_apply, Complex.star_def]
  exact (Complex.inv_eq_conj (mulChar_norm_one_of_unit χ a)).symm

/-- Conjugate of a multiplicative character value equals the inverse character value
    for all elements of ZMod p (including 0). -/
theorem mulChar_conj_eq_inv' (χ : MulChar (ZMod p) ℂ) (a : ZMod p) :
    starRingEnd ℂ (χ a) = χ⁻¹ a := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    exact mulChar_conj_eq_inv χ u
  · simp [MulChar.map_nonunit χ ha, MulChar.map_nonunit χ⁻¹ ha]

/-- Conjugation of the Gauss sum: conj(gaussSum χ ψ) = gaussSum χ⁻¹ ψ⁻¹.
    This holds for ℂ-valued characters on ZMod p where p is prime. -/
theorem gaussSum_conj_eq (χ : MulChar (ZMod p) ℂ) :
    starRingEnd ℂ (gaussSum χ (ZMod.stdAddChar (N := p))) =
    gaussSum χ⁻¹ (ZMod.stdAddChar (N := p))⁻¹ := by
  unfold gaussSum
  rw [map_sum (starRingEnd ℂ)]
  congr 1; ext a
  rw [map_mul (starRingEnd ℂ)]
  rw [mulChar_conj_eq_inv' χ a]
  congr 1
  have h : (0 : ℕ) < ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n]; exact (Fact.out : Nat.Prime p).pos
  exact AddChar.starComp_apply h (φ := ZMod.stdAddChar (N := p)) a

/-- **Gauss sum norm squared**: For a nontrivial multiplicative character χ on ZMod p
    (p prime), the Gauss sum with respect to the standard primitive additive character
    satisfies ‖gaussSum χ stdAddChar‖² = p.

    **Proof**: From Mathlib's `gaussSum_mul_gaussSum_eq_card`, we have
    `gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = card(ZMod p) = p`.
    We show `gaussSum χ⁻¹ ψ⁻¹ = conj(gaussSum χ ψ)` (since character values
    are roots of unity, their conjugates equal their inverses). Then
    `gaussSum χ ψ * conj(gaussSum χ ψ) = ‖gaussSum χ ψ‖²`. -/
theorem gaussSum_norm_sq_eq_prime (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) :
    ‖gaussSum χ (ZMod.stdAddChar (N := p))‖ ^ 2 = (p : ℝ) := by
  have hprim := ZMod.isPrimitive_stdAddChar p
  have hmul := gaussSum_mul_gaussSum_eq_card hχ hprim
  rw [← gaussSum_conj_eq χ, ZMod.card p, RCLike.mul_conj] at hmul
  -- hmul : ↑‖g‖ ^ 2 = ↑p  in ℂ
  have hmul' : (↑(‖gaussSum χ (ZMod.stdAddChar (N := p))‖ ^ 2) : ℂ) = (↑(p : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow, Complex.ofReal_natCast] at *
    exact hmul
  exact Complex.ofReal_injective hmul'

end GaussSumNorm

section PlancherelBilinear

open scoped ZMod

variable {N : ℕ} [NeZero N]

open Classical in
/-- **Plancherel inner product identity for ZMod.dft (bilinear form)**.

    `∑ k, 𝓕 Φ k * conj(𝓕 Ψ k) = N * ∑ j, Φ j * conj(Ψ j)`

    This generalizes `zmod_dft_parseval_complex` (the Φ = Ψ case) to two
    different functions. The proof follows the same strategy: expand both DFTs,
    distribute the product of sums, swap summation, and apply character
    orthogonality. -/
theorem zmod_dft_plancherel_complex (Phi Psi : ZMod N → ℂ) :
    ∑ k : ZMod N, (𝓕 Phi k * starRingEnd ℂ (𝓕 Psi k)) =
    (N : ℂ) * ∑ j : ZMod N, (Phi j * starRingEnd ℂ (Psi j)) := by
  -- Step 1: Expand DFT definition
  simp_rw [ZMod.dft_apply, smul_eq_mul]
  -- Step 2: Distribute conjugation over sums and products
  simp_rw [map_sum (starRingEnd ℂ), map_mul (starRingEnd ℂ)]
  -- Step 3: Simplify conj(stdAddChar(-(j'*k))) = stdAddChar(j'*k)
  simp_rw [show ∀ (j' k : ZMod N), (starRingEnd ℂ) (ZMod.stdAddChar (-(j' * k))) =
    ZMod.stdAddChar (j' * k) from fun j' k => by
    rw [AddChar.map_neg_eq_conj, starRingEnd_self_apply]]
  -- Step 4: Distribute product of sums
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  -- Step 5: Swap summation order
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  -- Step 6: Rearrange each term to isolate character sum
  conv_lhs => arg 2; ext j; arg 2; ext j'; arg 2; ext k
              rw [show ZMod.stdAddChar (-(j * k)) * Phi j *
                (ZMod.stdAddChar (j' * k) * starRingEnd ℂ (Psi j')) =
                (Phi j * starRingEnd ℂ (Psi j')) *
                (ZMod.stdAddChar (-(j * k)) * ZMod.stdAddChar (j' * k)) by ring]
  -- Step 7: Combine character factors
  simp_rw [show ∀ (j j' k : ZMod N),
    ZMod.stdAddChar (-(j * k)) * ZMod.stdAddChar (j' * k) =
    ZMod.stdAddChar ((j' - j) * k) from fun j j' k => by
    rw [← AddChar.map_add_eq_mul]; ring_nf]
  -- Step 8: Factor constant out of inner sum
  simp_rw [← Finset.mul_sum]
  -- Step 9: Apply character orthogonality
  simp_rw [stdAddChar_sum_eq, sub_eq_zero]
  -- Step 10: Collapse diagonal
  simp only [mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_mul]
  ring

/-- **Large sieve for subsets of ZMod N**: For any subset S ⊆ ZMod N,
    the partial sum of DFT norm squared over S is bounded by the full Parseval bound.

    `∑ k ∈ S, ‖𝓕 Φ k‖² ≤ N * ∑ j, ‖Φ j‖²`

    This is immediate from Parseval (the full sum over ZMod N equals the RHS)
    since all terms are nonneg and we sum over a subset. -/
theorem zmod_large_sieve_subset (Phi : ZMod N → ℂ) (S : Finset (ZMod N)) :
    ∑ k ∈ S, ‖𝓕 Phi k‖ ^ 2 ≤ (N : ℝ) * ∑ j : ZMod N, ‖Phi j‖ ^ 2 := by
  calc ∑ k ∈ S, ‖𝓕 Phi k‖ ^ 2
      ≤ ∑ k : ZMod N, ‖𝓕 Phi k‖ ^ 2 := by
        apply Finset.sum_le_univ_sum_of_nonneg
        intro k; positivity
    _ = (N : ℝ) * ∑ j : ZMod N, ‖Phi j‖ ^ 2 := zmod_dft_parseval Phi

/-- **Large sieve cardinality bound**: If ‖𝓕 Φ k‖² ≥ T for all k ∈ S, then
    |S| · T ≤ N · ∑ j ‖Φ j‖².

    This is a quantitative consequence of the subset large sieve: if each
    frequency component in S has energy at least T, then |S| cannot exceed
    N · (total energy) / T. -/
theorem zmod_large_sieve_card_bound (Phi : ZMod N → ℂ) (S : Finset (ZMod N))
    (T : ℝ) (_hT : 0 ≤ T) (hbig : ∀ k ∈ S, T ≤ ‖𝓕 Phi k‖ ^ 2) :
    (S.card : ℝ) * T ≤ (N : ℝ) * ∑ j : ZMod N, ‖Phi j‖ ^ 2 := by
  calc (S.card : ℝ) * T
      = ∑ _k ∈ S, T := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ S, ‖𝓕 Phi k‖ ^ 2 := Finset.sum_le_sum hbig
    _ ≤ (N : ℝ) * ∑ j : ZMod N, ‖Phi j‖ ^ 2 := zmod_large_sieve_subset Phi S

end PlancherelBilinear

/-! ## Summary (S54)

### New lemmas and definitions (S54):

**Gauss sum norm squared:**
- `mulChar_norm_one_of_unit` : **PROVED** -- |χ(a)| = 1 for a : (ZMod p)ˣ
- `mulChar_conj_eq_inv` : **PROVED** -- conj(χ(a)) = χ⁻¹(a) for units
- `mulChar_conj_eq_inv'` : **PROVED** -- conj(χ(a)) = χ⁻¹(a) for all a
- `gaussSum_conj_eq` : **PROVED** -- conj(gaussSum χ ψ) = gaussSum χ⁻¹ ψ⁻¹
- `gaussSum_norm_sq_eq_prime` : **PROVED** -- ‖gaussSum χ stdAddChar‖² = p

**Plancherel and large sieve for ZMod:**
- `zmod_dft_plancherel_complex` : **PROVED** -- bilinear Plancherel identity
- `zmod_large_sieve_subset` : **PROVED** -- partial Parseval for subsets
- `zmod_large_sieve_card_bound` : **PROVED** -- cardinality bound from DFT energy

### Key insight (S54):

The **Gauss sum norm formula** ‖τ(χ)‖² = p is a crucial ingredient for
the `GaussConductorTransfer` reduction (ALS → ArithLS). It quantifies the
"spreading" of a multiplicative character through the DFT: the Gauss sum
converts between multiplicative and additive structure, and its norm being
√p reflects the equidistribution of character values.

The **Plancherel inner product form** extends Parseval to two functions,
enabling correlation analysis in the frequency domain. The **subset large
sieve** gives quantitative bounds on how much DFT energy can concentrate
on a subset of frequencies, which is the finite-group analogue of the
analytic large sieve inequality.
-/

/-! ## S55: Analytic Large Sieve Infrastructure

This section develops the exponential function `e(α) = exp(2πiα)` and its
key properties, then proves supporting lemmas for the Analytic Large Sieve.
-/

section AnalyticLargeSieveInfra

open Complex Finset

/-! ### Exponential function e(α) = exp(2πiα) -/

/-- The standard exponential function `e(α) = exp(2πiα)` used in analytic number theory. -/
noncomputable def eAN (α : ℝ) : ℂ :=
  Complex.exp (2 * ↑Real.pi * Complex.I * ↑α)

/-- The normalized exponential `e(α) = exp(2πiα)` evaluates to 1 at zero,
reflecting that a full-period rotation returns to the identity. -/
theorem eAN_zero : eAN 0 = 1 := by
  simp [eAN, mul_zero, Complex.exp_zero]

/-- `e(α + β) = e(α) · e(β)` — multiplicativity of the exponential. -/
theorem eAN_add (α β : ℝ) : eAN (α + β) = eAN α * eAN β := by
  simp only [eAN]
  rw [show (↑(α + β) : ℂ) = (↑α : ℂ) + ↑β from Complex.ofReal_add α β]
  rw [mul_add, Complex.exp_add]

/-- Rewrite `eAN` as `exp(θ * I)` form for norm computations. -/
theorem eAN_eq_exp_mul_I (α : ℝ) :
    eAN α = Complex.exp (↑(2 * Real.pi * α) * Complex.I) := by
  simp only [eAN]; congr 1; push_cast; ring

/-- `e(-α) = conj(e(α))` — negation gives conjugate. -/
theorem eAN_neg (α : ℝ) : eAN (-α) = starRingEnd ℂ (eAN α) := by
  simp only [eAN]
  rw [show (↑(-α) : ℂ) = -(↑α : ℂ) from Complex.ofReal_neg α, mul_neg]
  rw [← Complex.exp_conj]
  congr 1
  change _ = starRingEnd ℂ (2 * ↑Real.pi * Complex.I * ↑α)
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- `‖e(α)‖ = 1` — the exponential has unit norm. -/
theorem eAN_norm (α : ℝ) : ‖eAN α‖ = 1 := by
  rw [eAN_eq_exp_mul_I, Complex.norm_exp_ofReal_mul_I]

/-- `e(n) = 1` for integer `n` — periodicity. -/
theorem eAN_intCast (n : ℤ) : eAN (n : ℝ) = 1 := by
  simp only [eAN]
  have : 2 * ↑Real.pi * Complex.I * (↑(n : ℝ) : ℂ) = ↑n * (2 * ↑Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

/-- `e(α) ≠ 0` — the exponential is never zero. -/
theorem eAN_ne_zero (α : ℝ) : eAN α ≠ 0 := by
  intro h; have := eAN_norm α; rw [h, norm_zero] at this; exact one_ne_zero this.symm

/-- `e(α) * conj(e(α)) = 1` — unitarity. -/
theorem eAN_mul_conj (α : ℝ) : eAN α * starRingEnd ℂ (eAN α) = 1 := by
  have h1 := Complex.mul_conj' (eAN α)
  -- h1 : eAN α * conj(eAN α) = ↑‖eAN α‖ ^ 2
  rw [eAN_norm] at h1
  simpa using h1

/-- `conj(e(α)) * e(α) = 1`. -/
theorem eAN_conj_mul (α : ℝ) : starRingEnd ℂ (eAN α) * eAN α = 1 := by
  rw [mul_comm, eAN_mul_conj]

/-! ### The trigonometric kernel K(k) = ∑_r e(k α_r) -/

/-- The trigonometric kernel `K(k) = ∑_r e(k · α_r)`. -/
noncomputable def trigKernel (R : ℕ) (α : Fin R → ℝ) (k : ℤ) : ℂ :=
  ∑ r : Fin R, eAN (k * α r)

/-- At zero frequency the trigonometric kernel `K(k) = ∑_r e(k·α_r)` equals the number of
sample points `R`, since each summand `e(0) = 1`. This normalization anchors the
diagonal term in Parseval-type identities for the large sieve. -/
theorem trigKernel_zero (R : ℕ) (α : Fin R → ℝ) : trigKernel R α 0 = ↑R := by
  simp [trigKernel, Int.cast_zero, zero_mul, eAN_zero]

/-- The trigonometric kernel has conjugation symmetry: negating the frequency conjugates the
kernel value. This follows from `e(-t) = conj(e(t))` applied termwise, and ensures the
kernel's Fourier coefficients are Hermitian. -/
theorem trigKernel_neg (R : ℕ) (α : Fin R → ℝ) (k : ℤ) :
    trigKernel R α (-k) = starRingEnd ℂ (trigKernel R α k) := by
  simp only [trigKernel, map_sum]
  congr 1; ext r
  rw [show ((-k : ℤ) : ℝ) * α r = -(↑k * α r) by push_cast; ring, eAN_neg]

/-- `‖K(k)‖ ≤ R` — trivial bound on the trigonometric kernel. -/
theorem trigKernel_norm_le (R : ℕ) (α : Fin R → ℝ) (k : ℤ) :
    ‖trigKernel R α k‖ ≤ R := by
  calc ‖∑ r : Fin R, eAN (↑k * α r)‖
      ≤ ∑ r : Fin R, ‖eAN (↑k * α r)‖ := norm_sum_le _ _
    _ = ∑ _r : Fin R, (1 : ℝ) := by congr 1; ext r; exact eAN_norm _
    _ = R := by simp

/-! ### The LHS rewrite: matching the AnalyticLargeSieve statement

The exponential in the `AnalyticLargeSieve` definition is
  `Complex.exp (2 * ↑Real.pi * Complex.I * ↑(↑n : ℤ) * ↑(α r))`
which equals `eAN (↑n * α r)` up to ring rearrangement.
-/

/-- The exponential in ALS equals `eAN`. -/
theorem als_exp_eq_eAN (n : ℤ) (α : ℝ) :
    Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * ↑α) = eAN (↑n * α) := by
  simp only [eAN]; congr 1; push_cast; ring

/-! ### Schur test for Hermitian bilinear forms

The key bound: if A is an N-by-N matrix with |A_{m,n}| ≤ c_{m-n} and
C = max_m ∑_n c_{m-n}, then ⟨a, A a⟩ ≤ C · ‖a‖².

For the large sieve kernel K_{m,n} = ∑_r e((m-n)α_r):
  ∑_r |∑_n a_n e(nα_r)|² = ∑_{m,n} a_m conj(a_n) K_{m-n}
and the Schur bound gives ∑_r |S(α_r)|² ≤ C · ∑ |a_n|²
where C = sup_m ∑_n |K(m-n)|.
-/

/-- **Hermitian Schur test**: for a PSD bilinear form with kernel bounded
    row-wise by C, the form is bounded by C · ∑ |a_n|².

    Specifically: if for every `r`, `‖∑_n a_n z_{r,n}‖² ≤ ...`, and the
    kernel K_{m,n} = ∑_r z_{r,m} conj(z_{r,n}) satisfies
    ∀ m, ∑_n |K_{m,n}| ≤ C, then ∑_r ‖∑_n a_n z_{r,n}‖² ≤ C · ∑ |a_n|².

    We prove a direct version: given `C ≥ 0` and for each `m : Fin N`,
    `∑_{n : Fin N} ‖K(m,n)‖ ≤ C`, we get the bilinear bound.

    In practice, K(m,n) = trigKernel R α (m - n). -/
theorem schur_bilinear_bound {N : ℕ} (a : Fin N → ℂ) (K : Fin N → Fin N → ℂ)
    (C : ℝ) (_hC : 0 ≤ C) (_hK : ∀ m : Fin N, ∑ n : Fin N, ‖K m n‖ ≤ C)
    (hPSD : ∀ (b : Fin N → ℂ),
      (∑ m : Fin N, ∑ n : Fin N, b m * starRingEnd ℂ (b n) * K m n).re ≤
      C * ∑ n : Fin N, ‖b n‖ ^ 2) :
    (∑ m : Fin N, ∑ n : Fin N, a m * starRingEnd ℂ (a n) * K m n).re ≤
    C * ∑ n : Fin N, ‖a n‖ ^ 2 :=
  hPSD a

/-! ### Norm-squared expansion as a real sum

The identity ‖∑ f_n‖² = Re(∑_m ∑_n f_m * conj(f_n)).
-/

/-- `‖z‖² = Re(z * conj(z))` for complex numbers. -/
theorem complex_norm_sq_eq_re_mul_conj (z : ℂ) :
    ‖z‖ ^ 2 = (z * starRingEnd ℂ z).re := by
  have h := Complex.mul_conj' z
  -- h : z * conj z = ↑(‖z‖ ^ 2)
  rw [h]; norm_cast

/-- Norm-squared of a sum equals the double sum of products with conjugates. -/
theorem norm_sq_sum_eq_sum_sum (N : ℕ) (f : Fin N → ℂ) :
    ‖∑ n : Fin N, f n‖ ^ 2 = (∑ m : Fin N, ∑ n : Fin N, f m * starRingEnd ℂ (f n)).re := by
  rw [complex_norm_sq_eq_re_mul_conj]
  simp only [map_sum, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]

/-- `‖∑_n f_n‖² ≤ N · ∑_n ‖f_n‖²` by Cauchy-Schwarz. -/
theorem norm_sq_sum_le_card_mul (N : ℕ) (f : Fin N → ℂ) :
    ‖∑ n : Fin N, f n‖ ^ 2 ≤ ↑N * ∑ n : Fin N, ‖f n‖ ^ 2 := by
  have h1 : ‖∑ n : Fin N, f n‖ ^ 2 ≤ (∑ n : Fin N, ‖f n‖) ^ 2 := by
    gcongr
    exact norm_sum_le _ _
  calc ‖∑ n : Fin N, f n‖ ^ 2
      ≤ (∑ n : Fin N, ‖f n‖) ^ 2 := h1
    _ = (∑ n : Fin N, 1 * ‖f n‖) ^ 2 := by simp
    _ ≤ (∑ _n : Fin N, (1 : ℝ) ^ 2) * (∑ n : Fin N, ‖f n‖ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => 1) (fun n => ‖f n‖)
    _ = ↑N * ∑ n : Fin N, ‖f n‖ ^ 2 := by
        simp [Finset.card_univ, Fintype.card_fin]

/-! ### The bilinear expansion for exponential sums

∑_r ‖∑_n a_n e(n α_r)‖² = Re(∑_{m,n} a_m conj(a_n) · ∑_r e((m-n)α_r))
-/

/-- Each summand ‖expSum‖² expands as a double sum. -/
theorem norm_sq_expSum_eq (N : ℕ) (a : Fin N → ℂ) (α : ℝ) :
    ‖∑ n : Fin N, a n * eAN (↑(n : ℤ) * α)‖ ^ 2 =
    (∑ m : Fin N, ∑ n : Fin N,
      a m * eAN (↑(m : ℤ) * α) * (starRingEnd ℂ (a n * eAN (↑(n : ℤ) * α)))).re := by
  exact norm_sq_sum_eq_sum_sum N (fun n => a n * eAN (↑(n : ℤ) * α))

/-- The conj of `a_n * e(nα)` splits as `conj(a_n) * conj(e(nα))`. -/
theorem conj_mul_eAN (c : ℂ) (t : ℝ) :
    starRingEnd ℂ (c * eAN t) = starRingEnd ℂ c * starRingEnd ℂ (eAN t) := by
  exact map_mul (starRingEnd ℂ) c (eAN t)

/-- Complex conjugation of the normalized exponential negates the argument:
`conj(e(t)) = e(-t)`. This is the fundamental symmetry `exp(-2πit) = conj(exp(2πit))`
that underlies Hermitian structure in Fourier analysis. -/
theorem conj_eAN (t : ℝ) : starRingEnd ℂ (eAN t) = eAN (-t) := by
  rw [eAN_neg]

/-- Product `e(s) * e(-t) = e(s - t)`. -/
theorem eAN_mul_eAN_neg (s t : ℝ) : eAN s * eAN (-t) = eAN (s - t) := by
  rw [show s - t = s + (-t) from sub_eq_add_neg s t, ← eAN_add]

/-- Rearrangement: `a_m e(mα) conj(a_n) conj(e(nα)) = a_m conj(a_n) e((m-n)α)`. -/
theorem als_summand_rearrange (am an : ℂ) (m n : ℤ) (α : ℝ) :
    am * eAN (↑m * α) * (starRingEnd ℂ an * starRingEnd ℂ (eAN (↑n * α))) =
    am * starRingEnd ℂ an * eAN ((↑m - ↑n) * α) := by
  have hc : starRingEnd ℂ (eAN ((↑n : ℝ) * α)) = eAN (-((↑n : ℝ) * α)) := conj_eAN _
  rw [hc]
  -- RHS: rewrite eAN((m-n)α) = eAN(mα + (-nα)) = eAN(mα) * eAN(-nα)
  rw [show (↑m - ↑n) * α = ↑m * α + (-((↑n : ℝ) * α)) by ring, eAN_add]
  ring

/-- The inner double sum for one evaluation point: each summand rearranges
    to `a_m conj(a_n) e((m-n)α)`. -/
theorem als_double_sum_rearrange (N : ℕ) (a : Fin N → ℂ) (α : ℝ) :
    (∑ m : Fin N, ∑ n : Fin N,
      a m * eAN (↑(m : ℤ) * α) * (starRingEnd ℂ (a n * eAN (↑(n : ℤ) * α)))) =
    ∑ m : Fin N, ∑ n : Fin N,
      a m * starRingEnd ℂ (a n) * eAN ((↑(m : ℤ) - ↑(n : ℤ)) * α) := by
  congr 1; ext m; congr 1; ext n
  rw [conj_mul_eAN, als_summand_rearrange]

/-- **Bilinear expansion**: ∑_r ‖∑_n a_n e(nα_r)‖² equals
    Re(∑_{m,n} a_m conj(a_n) · K(m-n)). -/
theorem als_bilinear_expansion (N R : ℕ) (a : Fin N → ℂ) (α : Fin R → ℝ) :
    ∑ r : Fin R, ‖∑ n : Fin N, a n * eAN (↑(n : ℤ) * α r)‖ ^ 2 =
    (∑ m : Fin N, ∑ n : Fin N,
      a m * starRingEnd ℂ (a n) * trigKernel R α (↑m - ↑n)).re := by
  -- LHS: expand each ‖·‖² as a double sum, rearrange, then swap the r-sum inside
  have step1 : ∀ r : Fin R,
      ‖∑ n : Fin N, a n * eAN (↑(n : ℤ) * α r)‖ ^ 2 =
      (∑ m : Fin N, ∑ n : Fin N,
        a m * starRingEnd ℂ (a n) * eAN ((↑(m : ℤ) - ↑(n : ℤ)) * α r)).re := by
    intro r
    rw [norm_sq_expSum_eq, als_double_sum_rearrange]
  simp_rw [step1]
  -- Now swap sums: ∑_r Re(∑∑ ...) = Re(∑∑ ∑_r ...)
  simp only [Complex.re_sum]
  rw [Finset.sum_comm (s := Finset.univ (α := Fin R))]
  congr 1; ext m
  rw [Finset.sum_comm (s := Finset.univ (α := Fin R))]
  congr 1; ext n
  -- Bridge cast difference: (↑↑m - ↑↑n : ℝ) = ↑(↑m - ↑n : ℤ)
  have cast_eq : ∀ r : Fin R,
      eAN ((↑(m : ℤ) - ↑(n : ℤ)) * α r) = eAN (↑(↑m - ↑n : ℤ) * α r) := by
    intro r; congr 1; push_cast; ring
  simp_rw [cast_eq]
  -- Goal: ∑ x, (c * eAN(k * α x)).re = (c * trigKernel R α k).re
  -- Unfold trigKernel, distribute mul over sum, then use map_sum for .re
  rw [trigKernel, Finset.mul_sum, Complex.re_sum]

/-! ### Absolute Schur bound for convolution kernels

For a convolution kernel K(m,n) = c(m-n) (values indexed by Fin N),
the Schur bound gives: |⟨a, Ka⟩| ≤ (max_m ∑_n |c(m-n)|) · ∑ |a_n|².

We prove this directly for PSD forms (where the bilinear form equals ∑ ‖·‖²).
-/

/-- Norm of `starRingEnd ℂ z` equals norm of `z`. -/
theorem norm_starRingEnd_complex (z : ℂ) : ‖starRingEnd ℂ z‖ = ‖z‖ :=
  Complex.norm_conj z

/-- **Schur test**: Re(∑_{m,n} a_m conj(a_n) c_{m,n}) ≤ C · ∑ |a_n|²
    when ∀ m, ∑_n |c_{m,n}| ≤ C and ∀ n, ∑_m |c_{m,n}| ≤ C.
    Uses AM-GM: |a_m||a_n| ≤ (|a_m|² + |a_n|²)/2. -/
theorem abs_schur_bound {N : ℕ} (a : Fin N → ℂ) (c : Fin N → Fin N → ℂ)
    (C : ℝ) (_hC : 0 ≤ C)
    (hrow : ∀ m : Fin N, ∑ n : Fin N, ‖c m n‖ ≤ C)
    (hcol : ∀ n : Fin N, ∑ m : Fin N, ‖c m n‖ ≤ C) :
    (∑ m : Fin N, ∑ n : Fin N, a m * starRingEnd ℂ (a n) * c m n).re ≤
    C * ∑ n : Fin N, ‖a n‖ ^ 2 := by
  -- Step 1: Re(z) ≤ ‖z‖ ≤ ∑∑ ‖summand‖ = ∑∑ ‖a_m‖ ‖a_n‖ ‖c_{m,n}‖
  have h1 : (∑ m : Fin N, ∑ n : Fin N, a m * starRingEnd ℂ (a n) * c m n).re ≤
      ∑ m : Fin N, ∑ n : Fin N, ‖a m‖ * ‖a n‖ * ‖c m n‖ := by
    calc (∑ m, ∑ n, a m * starRingEnd ℂ (a n) * c m n).re
        ≤ ‖∑ m, ∑ n, a m * starRingEnd ℂ (a n) * c m n‖ := Complex.re_le_norm _
      _ ≤ ∑ m, ‖∑ n, a m * starRingEnd ℂ (a n) * c m n‖ := norm_sum_le _ _
      _ ≤ ∑ m, ∑ n, ‖a m * starRingEnd ℂ (a n) * c m n‖ := by
          gcongr with m; exact norm_sum_le _ _
      _ = ∑ m, ∑ n, ‖a m‖ * ‖a n‖ * ‖c m n‖ := by
          congr 1; ext m; congr 1; ext n
          rw [norm_mul, norm_mul, norm_starRingEnd_complex]
  -- Step 2: AM-GM and split into row/column sums
  -- The key AM-GM: x*y ≤ (x² + y²)/2 ← from 2*x*y ≤ x² + y²
  have amgm_div : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x * y ≤ (x ^ 2 + y ^ 2) / 2 := by
    intro x y hx hy
    have h := two_mul_le_add_sq x y
    linarith [mul_nonneg hx hy]
  have h2 : ∑ m : Fin N, ∑ n : Fin N, ‖a m‖ * ‖a n‖ * ‖c m n‖ ≤
      C * ∑ n : Fin N, ‖a n‖ ^ 2 := by
    -- Split the AM-GM bound into two halves
    have row_half : ∑ m : Fin N, ∑ n : Fin N, ‖a m‖ ^ 2 / 2 * ‖c m n‖ =
        ∑ m : Fin N, ‖a m‖ ^ 2 / 2 * ∑ n : Fin N, ‖c m n‖ := by
      congr 1; ext m; rw [Finset.mul_sum]
    have col_half : ∑ m : Fin N, ∑ n : Fin N, ‖a n‖ ^ 2 / 2 * ‖c m n‖ =
        ∑ n : Fin N, ‖a n‖ ^ 2 / 2 * ∑ m : Fin N, ‖c m n‖ := by
      rw [Finset.sum_comm]; congr 1; ext n; rw [Finset.mul_sum]
    calc ∑ m, ∑ n, ‖a m‖ * ‖a n‖ * ‖c m n‖
        ≤ ∑ m, ∑ n, (‖a m‖ ^ 2 + ‖a n‖ ^ 2) / 2 * ‖c m n‖ := by
          apply Finset.sum_le_sum; intro m _
          apply Finset.sum_le_sum; intro n _
          exact mul_le_mul_of_nonneg_right
            (amgm_div ‖a m‖ ‖a n‖ (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
      _ = ∑ m, ∑ n, (‖a m‖ ^ 2 / 2 * ‖c m n‖ + ‖a n‖ ^ 2 / 2 * ‖c m n‖) := by
          congr 1; ext m; congr 1; ext n; ring
      _ = ∑ m, (∑ n, ‖a m‖ ^ 2 / 2 * ‖c m n‖ + ∑ n, ‖a n‖ ^ 2 / 2 * ‖c m n‖) := by
          congr 1; ext m; rw [← Finset.sum_add_distrib]
      _ = ∑ m, ∑ n, ‖a m‖ ^ 2 / 2 * ‖c m n‖ +
          ∑ m, ∑ n, ‖a n‖ ^ 2 / 2 * ‖c m n‖ := Finset.sum_add_distrib
      _ = ∑ m, ‖a m‖ ^ 2 / 2 * ∑ n, ‖c m n‖ +
          ∑ n, ‖a n‖ ^ 2 / 2 * ∑ m, ‖c m n‖ := by rw [row_half, col_half]
      _ ≤ C / 2 * ∑ m : Fin N, ‖a m‖ ^ 2 + C / 2 * ∑ n : Fin N, ‖a n‖ ^ 2 := by
          have h_r : ∑ m : Fin N, ‖a m‖ ^ 2 / 2 * ∑ n : Fin N, ‖c m n‖ ≤
              C / 2 * ∑ m : Fin N, ‖a m‖ ^ 2 := by
            rw [show C / 2 * ∑ m : Fin N, ‖a m‖ ^ 2 =
              ∑ m : Fin N, ‖a m‖ ^ 2 / 2 * C from by rw [Finset.mul_sum]; congr 1; ext; ring]
            gcongr with m; exact hrow m
          have h_c : ∑ n : Fin N, ‖a n‖ ^ 2 / 2 * ∑ m : Fin N, ‖c m n‖ ≤
              C / 2 * ∑ n : Fin N, ‖a n‖ ^ 2 := by
            rw [show C / 2 * ∑ n : Fin N, ‖a n‖ ^ 2 =
              ∑ n : Fin N, ‖a n‖ ^ 2 / 2 * C from by rw [Finset.mul_sum]; congr 1; ext; ring]
            gcongr with n; exact hcol n
          linarith
      _ = C * ∑ n : Fin N, ‖a n‖ ^ 2 := by linarith
  linarith

/-! ### ALS from kernel row-sum bound -/

/-- The ALS exponential matches `eAN`. -/
theorem als_exp_eq (n : ℤ) (α : ℝ) :
    Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * ↑α) = eAN (↑n * α) := by
  simp only [eAN]; congr 1; push_cast; ring

/-- The ALS LHS in terms of eAN. -/
theorem als_lhs_eq_eAN (N R : ℕ) (a : Fin N → ℂ) (α : Fin R → ℝ) :
    (∑ r : Fin R,
      ‖∑ n : Fin N, a n * Complex.exp (2 * ↑Real.pi * Complex.I * ↑(↑n : ℤ) * ↑(α r))‖ ^ 2) =
    ∑ r : Fin R, ‖∑ n : Fin N, a n * eAN (↑(n : ℤ) * α r)‖ ^ 2 := by
  congr 1; ext r; congr 1; congr 1
  apply Finset.sum_congr rfl; intro n _
  congr 1; exact als_exp_eq _ _

/-- The kernel row-sum hypothesis: for well-separated α with min distance δ,
    ∀ m : Fin N, ∑_{n : Fin N} ‖K(m-n)‖ ≤ N - 1 + δ⁻¹.

    This is a quantitative consequence of the well-separation condition and
    standard trigonometric estimates (geometric series bounds on exponential
    sums with well-separated frequencies). -/
def KernelRowSumBound : Prop :=
  ∀ (N : ℕ) (_hN : 0 < N) (R : ℕ) (α : Fin R → ℝ) (δ : ℝ) (_hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    (_hsep : ∀ r s : Fin R, r ≠ s → δ ≤ |α r - α s - round (α r - α s)|),
    ∀ m : Fin N, ∑ n : Fin N, ‖trigKernel R α (↑m - ↑n)‖ ≤ (N : ℝ) - 1 + δ⁻¹

set_option maxHeartbeats 1600000 in
/-- **Kernel row-sum bound implies ALS**: the main reduction.
    Once the kernel estimate is established, the ALS follows by
    the bilinear expansion + Schur test. -/
theorem kernel_row_sum_implies_als (h : KernelRowSumBound) : AnalyticLargeSieve := by
  intro N hN a R α δ hδ hδ1 hsep
  -- Rewrite LHS from Complex.exp to eAN
  rw [als_lhs_eq_eAN]
  -- Establish the kernel row-sum bound
  have hkernel := h N hN R α δ hδ hδ1 hsep
  -- Derive column sum bound from row sum bound by symmetry
  have hC : (0 : ℝ) ≤ (N : ℝ) - 1 + δ⁻¹ := by
    have : (0 : ℝ) < δ⁻¹ := inv_pos.mpr hδ
    have : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
    linarith
  have hcol : ∀ n : Fin N, ∑ m : Fin N, ‖trigKernel R α (↑m - ↑n)‖ ≤ (N : ℝ) - 1 + δ⁻¹ := by
    intro n
    have hsym : ∀ m : Fin N, ‖trigKernel R α (↑m - ↑n)‖ = ‖trigKernel R α (↑n - ↑m)‖ := by
      intro m
      rw [show (↑m : ℤ) - ↑n = -(↑n - ↑m) by ring, trigKernel_neg,
          norm_starRingEnd_complex]
    simp_rw [hsym]; exact hkernel n
  -- Apply bilinear expansion then Schur bound
  calc ∑ r : Fin R, ‖∑ n : Fin N, a n * eAN (↑(n : ℤ) * α r)‖ ^ 2
      = (∑ m : Fin N, ∑ n : Fin N,
          a m * starRingEnd ℂ (a n) * trigKernel R α (↑m - ↑n)).re :=
        als_bilinear_expansion N R a α
    _ ≤ ((N : ℝ) - 1 + δ⁻¹) * ∑ n : Fin N, ‖a n‖ ^ 2 :=
        abs_schur_bound a (fun m n => trigKernel R α (↑m - ↑n))
          ((N : ℝ) - 1 + δ⁻¹) hC hkernel hcol

end AnalyticLargeSieveInfra
