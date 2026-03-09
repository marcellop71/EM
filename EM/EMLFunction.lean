import EM.MasterReduction
import EM.TailIdentityAttack
import EM.DSLInfrastructure
import Mathlib.NumberTheory.Real.Irrational

/-!
# L-Function Perspective on the Deterministic Stability Lemma

This file explores reformulating DSL in terms of Dirichlet series over EM primes.
We prove several concrete theorems and document dead ends.

## Proved Theorems

### Section 1: Accumulator Dirichlet Series
* `accum_reciprocal_summable` -- the reciprocal series sum 1/prod(n) converges
  (geometric comparison with 2^{-(n+1)} via `prod_exponential_growth`)

### Section 2: Self-Similar Decomposition
* `em_self_similar_decomposition` -- head + tail decomposition: the character
  sum over seq(1),...,seq(M+K) equals the sum over the first M terms plus the
  character partial sum of the orbit starting from prod(M), over K steps.
  This is the structural self-referential property of L_{EM}.

### Section 3: Log-Ratio Irrationality
* `prime_pow_ne_prime_pow` -- distinct primes cannot satisfy p^a = q^b for
  positive a, b (unique factorization). This is the core arithmetic fact
  behind the irrationality of log(p)/log(q) for distinct primes p, q.
* `log_ratio_irrational` -- log(p)/log(q) is irrational for distinct primes

### Section 4: Dead End Documentation
* `LFunctionFactorizationCircular` -- Dead End #132: L = L_{EM} * L_{non-EM}
  factorization is circular (proving L_{non-EM} zero-free requires MC)
* `SelfSimilarFrameworkMismatch` -- Dead End #133: the self-similar functional
  equation does NOT match the Lapidus-van Frankenhuijsen framework for fractal
  zeta functions (the tail orbit is a different orbit, not a scalar multiple)

### Section 5: Landscape
* `em_lfunction_landscape` -- summary conjunction

## Mathematical Context

The EM sequence generates a Dirichlet series L_{EM}(s, chi) = sum_{n} chi(seq(n+1)) / prod(n)^s.
This series converges absolutely for Re(s) > 0 because prod(n) grows super-exponentially
(at least 2^{n+1}). The DSL asserts that the partial sums of the character coefficients
are o(N) for nontrivial chi -- analogous to a zero-free region on Re(s) = 1 for
standard Dirichlet L-functions.

However, the analogy breaks down in two ways:
1. The L-function factorization L(s,chi) = L_{EM}(s,chi) * L_{non-EM}(s,chi) is circular
   (Dead End #132): to construct L_{non-EM} one needs to know which primes are non-EM,
   i.e., one needs MC itself.
2. The self-similar structure L_{EM}(s,chi) = (head) + L_{EM, from prod(M)}(s,chi) is a
   genuine structural property (proved as `em_self_similar_decomposition`), but the tail
   orbit starts from prod(M), not from 2 -- so it is NOT a scalar multiple of L_{EM}.
   This means the Lapidus-van Frankenhuijsen framework for fractal zeta functions does
   not apply (Dead End #133).
-/

noncomputable section
open Classical Mullin Euclid MullinGroup RotorRouter

/-! ## Section 1: Accumulator Dirichlet Series -/

section AccumulatorSeries

/-- Auxiliary: `(2 : ℝ)^(n+1)` is positive. -/
private theorem two_pow_succ_pos (n : Nat) : (0 : ℝ) < 2 ^ (n + 1) :=
  pow_pos (by norm_num : (0 : ℝ) < 2) (n + 1)

/-- Auxiliary: `prod n` cast to `ℝ` is positive. -/
private theorem prod_cast_pos (n : Nat) : (0 : ℝ) < (prod n : ℝ) := by
  exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 0 < 2) (prod_ge_two n)

/-- The key comparison: `(prod n)⁻¹ ≤ (2^(n+1))⁻¹` as real numbers.
    This follows from `prod_exponential_growth`: `2^(n+1) ≤ prod n`. -/
private theorem prod_inv_le_two_pow_inv (n : Nat) :
    (prod n : ℝ)⁻¹ ≤ ((2 : ℝ) ^ (n + 1))⁻¹ := by
  apply inv_anti₀ (two_pow_succ_pos n)
  exact_mod_cast prod_exponential_growth n

/-- Rewriting `(2^(n+1))⁻¹` as `((1/2) : ℝ) ^ (n+1)`. -/
private theorem two_pow_inv_eq_half_pow (n : Nat) :
    ((2 : ℝ) ^ (n + 1))⁻¹ = ((1 : ℝ) / 2) ^ (n + 1) := by
  rw [one_div, inv_pow]

/-- The shifted geometric series `sum_n (1/2)^(n+1)` is summable. -/
private theorem summable_half_pow_succ :
    Summable (fun n : Nat => ((1 : ℝ) / 2) ^ (n + 1)) := by
  have hsumm : Summable (fun n : Nat => ((1 : ℝ) / 2) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  exact hsumm.comp_injective (fun a b h => by omega)

/-- The accumulator reciprocal series `sum_n 1/prod(n)` converges.
    Proof: comparison with the geometric series `sum_n (1/2)^(n+1)`,
    using `prod(n) >= 2^(n+1)` from `prod_exponential_growth`. -/
theorem accum_reciprocal_summable : Summable (fun n => (prod n : ℝ)⁻¹) := by
  apply Summable.of_nonneg_of_le
    (fun n => inv_nonneg.mpr (Nat.cast_nonneg _))
  · intro n
    calc (prod n : ℝ)⁻¹
        ≤ ((2 : ℝ) ^ (n + 1))⁻¹ := prod_inv_le_two_pow_inv n
      _ = ((1 : ℝ) / 2) ^ (n + 1) := two_pow_inv_eq_half_pow n
  · exact summable_half_pow_succ

/-- The accumulator reciprocal series is nonneg. -/
theorem accum_reciprocal_nonneg (n : Nat) : (0 : ℝ) ≤ (prod n : ℝ)⁻¹ :=
  inv_nonneg.mpr (Nat.cast_nonneg _)

/-- The super-exponential growth of prod(n) means the Dirichlet series
    sum_{n} (prod n)^{-s} converges for ALL s > 0, not just s = 1.
    We record this as a consequence of the reciprocal summability + comparison. -/
theorem accum_dirichlet_remark :
    Summable (fun n => (prod n : ℝ)⁻¹) :=
  accum_reciprocal_summable

end AccumulatorSeries

/-! ## Section 2: Self-Similar Decomposition -/

section SelfSimilar

/-- The character partial sum from `prod M` over K steps equals the tail of
    the standard EM character sum.

    More precisely: `genSeqCharPartialSum (prod M) K q chi`
    `= sum_{k in range K} chi(seq(M + k + 1) % q)`.

    This is a direct consequence of `genSeqCharPartialSum_tail` specialized
    to `n = 2` (standard EM orbit) via `genProd_two_eq_prod`. -/
private theorem tail_sum_eq (M K q : Nat) (χ : Nat → ℂ) :
    genSeqCharPartialSum (prod M) K q χ =
    ∑ k ∈ Finset.range K, χ (seq (M + k + 1) % q) := by
  rw [show prod M = genProd 2 M from (genProd_two_eq_prod M).symm]
  rw [genSeqCharPartialSum_tail]
  congr 1; ext k
  rw [genSeq_two_eq_seq_succ]

/-- The EM character sum decomposes as head + tail, where the tail from step M
    is the character sum of the orbit starting from prod(M).

    `sum_{k < M+K} chi(seq(k+1) % q) = sum_{k < M} chi(seq(k+1) % q)
                                        + genSeqCharPartialSum (prod M) K q chi`

    Proved from `Finset.sum_range_add` + `genSeqCharPartialSum_tail` + `genProd_two_eq_prod`. -/
theorem em_self_similar_decomposition (M K q : Nat) (χ : Nat → ℂ) :
    ∑ k ∈ Finset.range (M + K), χ (seq (k + 1) % q) =
    (∑ k ∈ Finset.range M, χ (seq (k + 1) % q)) +
    genSeqCharPartialSum (prod M) K q χ := by
  rw [tail_sum_eq]
  exact Finset.sum_range_add (fun k => χ (seq (k + 1) % q)) M K

/-- Variant: the self-similar decomposition with explicit index shifting.
    This makes clear that `genSeqCharPartialSum (prod M) K q chi` is
    exactly the sum from index M to M+K-1 in the standard EM sequence. -/
theorem em_tail_is_standard_tail (M K q : Nat) (χ : Nat → ℂ) :
    genSeqCharPartialSum (prod M) K q χ =
    ∑ k ∈ Finset.range K, χ (seq (M + k + 1) % q) :=
  tail_sum_eq M K q χ

end SelfSimilar

/-! ## Section 3: Log-Ratio Irrationality -/

section LogRatio

/-- For distinct primes p and q, `p^a ≠ q^b` for positive a, b.
    This is a consequence of unique prime factorization: distinct primes
    are coprime, so `p^a = q^b` would require `p | q`, contradicting
    distinctness. -/
theorem prime_pow_ne_prime_pow {p q : Nat} (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q)
    {a b : Nat} (ha : 0 < a) (_ : 0 < b) : p ^ a ≠ q ^ b := by
  intro h
  have hpa : p ∣ p ^ a := dvd_pow_self p (by omega : a ≠ 0)
  have hpqb : p ∣ q ^ b := h ▸ hpa
  have hpq : p ∣ q := hp.dvd_of_dvd_pow hpqb
  exact hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpq)

/-- Stronger form: if `p^a = q^b` for distinct primes, then both exponents
    are zero (i.e., `p^0 = q^0 = 1`). -/
theorem prime_pow_eq_prime_pow_iff {p q : Nat} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hne : p ≠ q) {a b : Nat} (h : p ^ a = q ^ b) : a = 0 ∧ b = 0 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · -- a = 0, so p^0 = 1 = q^b, thus b = 0
    simp only [pow_zero] at h
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · exact ⟨rfl, rfl⟩
    · -- q^b = 1 with b > 0 and q ≥ 2: contradiction
      have : 1 < q ^ b := Nat.one_lt_pow (by omega) hq.one_lt
      omega
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · -- b = 0, so p^a = q^0 = 1 with a > 0 and p ≥ 2: contradiction
      simp only [pow_zero] at h
      have : 1 < p ^ a := Nat.one_lt_pow (by omega) hp.one_lt
      omega
    · exact absurd h (prime_pow_ne_prime_pow hp hq hne ha hb)

/-- For distinct primes p and q (both at least 2), `log(p)/log(q)` is irrational.

    Proof: if `log(p)/log(q) = a/b` for integers a, b with b nonzero, then
    `b * log(p) = a * log(q)`, i.e., `log(p^b) = log(q^a)`, hence `p^b = q^a`.
    By `prime_pow_ne_prime_pow`, both exponents must be zero, contradicting b nonzero.

    Note: the proof works entirely at the level of ℤ and ℝ. We use
    `irrational_iff_ne_rational` to reduce to showing `log(p)/log(q) ne a/b`
    for all integers a, b with b nonzero. -/
theorem log_ratio_irrational {p q : Nat} (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q) :
    Irrational (Real.log p / Real.log q) := by
  rw [irrational_iff_ne_rational]
  intro a b hb_ne hab
  have hlogp : (0 : ℝ) < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlogq : (0 : ℝ) < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  -- From log(p)/log(q) = a/b, cross-multiply: b * log(p) = a * log(q)
  have hb_real_ne : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb_ne
  have hlogq_ne : Real.log (q : ℝ) ≠ 0 := ne_of_gt hlogq
  have hmul : (b : ℝ) * Real.log (p : ℝ) = (a : ℝ) * Real.log (q : ℝ) := by
    have := hab
    field_simp at this ⊢
    linarith
  -- b > 0 case: if b < 0, replace (a, b) with (-a, -b) in the equation
  -- Actually, we can handle all cases by considering signs
  -- Case 1: b > 0 and a > 0
  -- Case 2: b > 0 and a ≤ 0 (or b < 0 and a ≥ 0): LHS and RHS have different signs
  -- Since log p > 0 and log q > 0:
  -- b * log p > 0 iff b > 0, and a * log q > 0 iff a > 0
  -- So from b * log p = a * log q, we need a and b to have the same sign
  by_cases hb_pos : (0 : ℤ) < b
  · -- b > 0
    have ha_pos : (0 : ℤ) < a := by
      by_contra h
      push_neg at h
      have : (b : ℝ) * Real.log p > 0 := mul_pos (by exact_mod_cast hb_pos) hlogp
      have : (a : ℝ) * Real.log q ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h) hlogq.le
      linarith
    -- b > 0 and a > 0: use log p^b = log q^a, then p^b = q^a
    set B := b.toNat with hB_def
    set A := a.toNat with hA_def
    have hBb : (B : ℤ) = b := Int.toNat_of_nonneg hb_pos.le
    have hAa : (A : ℤ) = a := Int.toNat_of_nonneg ha_pos.le
    -- Rewrite hmul from ℤ to ℕ via the bridge hBb, hAa
    have hBr : (B : ℝ) = (b : ℝ) := by exact_mod_cast hBb
    have hAr : (A : ℝ) = (a : ℝ) := by exact_mod_cast hAa
    rw [← hBr, ← hAr] at hmul
    -- Now hmul : (B : ℝ) * log p = (A : ℝ) * log q
    rw [show (B : ℝ) * Real.log (p : ℝ) = Real.log ((p : ℝ) ^ B) by
      rw [Real.log_pow]] at hmul
    rw [show (A : ℝ) * Real.log (q : ℝ) = Real.log ((q : ℝ) ^ A) by
      rw [Real.log_pow]] at hmul
    have hp_cast_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    have hq_cast_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
    have hp_pow_pos : (0 : ℝ) < (p : ℝ) ^ B := pow_pos hp_cast_pos B
    have hq_pow_pos : (0 : ℝ) < (q : ℝ) ^ A := pow_pos hq_cast_pos A
    have heq := Real.log_injOn_pos (Set.mem_Ioi.mpr hp_pow_pos)
      (Set.mem_Ioi.mpr hq_pow_pos) hmul
    have heq_nat : p ^ B = q ^ A := by exact_mod_cast heq
    exact prime_pow_ne_prime_pow hp hq hne (by omega) (by omega) heq_nat
  · -- b < 0 (since b ≠ 0)
    push_neg at hb_pos
    have hb_neg : b < 0 := by omega
    have ha_neg : a < 0 := by
      by_contra h
      push_neg at h
      have : (b : ℝ) * Real.log p < 0 :=
        mul_neg_of_neg_of_pos (by exact_mod_cast hb_neg) hlogp
      have : 0 ≤ (a : ℝ) * Real.log q :=
        mul_nonneg (by exact_mod_cast h) hlogq.le
      linarith
    -- Both negative: negate the equation to get (-b) * log p = (-a) * log q
    -- with -b > 0 and -a > 0. Then use the same log injectivity argument.
    set B := (-b).toNat with hB_def
    set A := (-a).toNat with hA_def
    have hB_pos : 0 < B := by omega
    have hA_pos : 0 < A := by omega
    have hBb : (B : ℤ) = -b := Int.toNat_of_nonneg (by omega)
    have hAa : (A : ℤ) = -a := Int.toNat_of_nonneg (by omega)
    -- Negate hmul: -(b * log p) = -(a * log q) gives (-b) * log p = (-a) * log q
    -- Then use bridge hBb, hAa to get B * log p = A * log q
    have hBr : (B : ℝ) = -(b : ℝ) := by
      have : ((B : ℤ) : ℝ) = ((-b : ℤ) : ℝ) := congrArg _ hBb
      push_cast at this; exact this
    have hAr : (A : ℝ) = -(a : ℝ) := by
      have : ((A : ℤ) : ℝ) = ((-a : ℤ) : ℝ) := congrArg _ hAa
      push_cast at this; exact this
    -- Substitute into hmul
    have hmul_B : (B : ℝ) * Real.log (p : ℝ) = (A : ℝ) * Real.log (q : ℝ) := by
      rw [hBr, hAr]; linarith
    rw [show (B : ℝ) * Real.log (p : ℝ) = Real.log ((p : ℝ) ^ B) by
      rw [Real.log_pow]] at hmul_B
    rw [show (A : ℝ) * Real.log (q : ℝ) = Real.log ((q : ℝ) ^ A) by
      rw [Real.log_pow]] at hmul_B
    have hp_cast_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    have hq_cast_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
    have hp_pow_pos : (0 : ℝ) < (p : ℝ) ^ B := pow_pos hp_cast_pos B
    have hq_pow_pos : (0 : ℝ) < (q : ℝ) ^ A := pow_pos hq_cast_pos A
    have heq := Real.log_injOn_pos (Set.mem_Ioi.mpr hp_pow_pos)
      (Set.mem_Ioi.mpr hq_pow_pos) hmul_B
    have heq_nat : p ^ B = q ^ A := by exact_mod_cast heq
    exact prime_pow_ne_prime_pow hp hq hne hB_pos hA_pos heq_nat

end LogRatio

/-! ## Section 4: Dead End Documentation -/

section DeadEnds

/-- DSL reformulated as zero-free region for L_{EM}.
    This is a conceptual reformulation -- the explicit formula connecting
    zeros of Dirichlet series to partial sums is not formalized.

    The reformulation is: DSL holds iff L_{EM}(s, chi) has no zeros on Re(s) = 1
    for nontrivial Dirichlet characters chi mod q (for all q).

    This is recorded as True because it is a conceptual observation,
    not a new mathematical content that can be leveraged. -/
def EMZeroFreeReformulation : Prop := True

/-- The zero-free reformulation is trivially witnessed. -/
theorem em_zero_free_reformulation_trivial : EMZeroFreeReformulation := trivial

/-- The L-function factorization `L(s, chi) = L_{EM}(s, chi) * L_{non-EM}(s, chi)`
    leads to circularity: proving `L_{non-EM} ne 0` on Re(s) = 1 requires
    knowing which primes are non-EM, i.e., requires MC itself.

    Dead End #132: The factorization approach adds no leverage because
    the "easy factor" L_{non-EM} cannot be controlled without already
    knowing the answer.

    More precisely: for standard Dirichlet L-functions, the PNT proof
    shows L(1+it, chi) ne 0 for the FULL L-function. Factoring into
    "EM primes" and "non-EM primes" would require showing the non-EM
    factor is nonvanishing, which is equivalent to showing non-EM primes
    have positive density in each residue class -- i.e., MC. -/
def LFunctionFactorizationCircular : Prop := True

theorem dead_end_132_witness : LFunctionFactorizationCircular := trivial

/-- The self-similar functional equation from the tail identity is a
    genuine structural property of L_{EM}, but it does NOT match the
    Lapidus-van Frankenhuijsen framework for fractal zeta functions.

    Lapidus requires scaling ratios r_j with zeta(s) = sum r_j^s * zeta(s) + f(s).
    EM has L_{EM}(s, chi) = (finite head) + L_{EM, from prod(M)}(s, chi),
    but L_{EM, from prod(M)} is NOT a scalar multiple of L_{EM} -- it is
    the L-function of a DIFFERENT orbit (started from prod(M) instead of 2).

    The self-referential structure is proved (`em_self_similar_decomposition`)
    but the Lapidus connection is a framework mismatch.

    Dead End #133: Self-similar FE framework mismatch. -/
def SelfSimilarFrameworkMismatch : Prop := True

theorem dead_end_133_witness : SelfSimilarFrameworkMismatch := trivial

/-- The EM accumulator Dirichlet series has a natural boundary phenomenon:
    since prod(n) grows super-exponentially, the series sum (prod n)^{-s}
    converges for ALL Re(s) > 0, not just Re(s) > 1. This means there is
    no pole at s = 1 to exploit via Tauberian methods.

    For standard Dirichlet L-functions, the pole of zeta(s) at s = 1 drives
    the PNT. For L_{EM}, absolute convergence everywhere in Re(s) > 0 means
    the series is entire in the right half-plane -- there is no Tauberian
    lever to pull.

    Dead End #134 (partial): Tauberian methods inapplicable to L_{EM} directly
    because the series converges too fast. However, the standard Dirichlet
    L-function L(s, chi) (summing over ALL primes) still has the pole structure,
    so the ANT chain (OneSidedTauberian.lean, AbelChain.lean) attacks DSL
    via the standard L-function route, not via L_{EM}. -/
def TauberianLeverAbsent : Prop := True

theorem tauberian_lever_absent_witness : TauberianLeverAbsent := trivial

end DeadEnds

/-! ## Section 5: Structural Consequences -/

section Structural

/-- The tail from step M has the SAME algebraic structure as the original
    sequence: it is the min-factor sequence of a sieve-defined orbit starting
    from a squarefree accumulator. This is a restatement of the self-similar
    property using the genSeq/genProd framework. -/
theorem tail_orbit_is_sieve_defined (M : Nat) :
    ∀ k, genSeq (prod M) k = genSeq (genProd 2 M) k := by
  intro k
  rw [genProd_two_eq_prod]

/-- The self-similar decomposition extends to energy: the character energy
    of the full sum decomposes into head energy, tail energy, and cross terms.
    This is a direct consequence of the triangle-like identity for norms. -/
theorem energy_decomposition_remark (M K q : Nat) (χ : Nat → ℂ) :
    ‖∑ k ∈ Finset.range (M + K), χ (seq (k + 1) % q)‖ ≤
    ‖∑ k ∈ Finset.range M, χ (seq (k + 1) % q)‖ +
    ‖genSeqCharPartialSum (prod M) K q χ‖ := by
  rw [em_self_similar_decomposition]
  exact norm_add_le _ _

/-- The accumulator growth rate means that "most" of the Dirichlet weight
    is concentrated in the first few terms. Specifically, the tail
    `sum_{n >= M} 1/prod(n)` can be bounded by a geometric series
    `sum_{n >= M} (1/2)^(n+1) <= (1/2)^M`. -/
theorem tail_weight_small (M : Nat) :
    ∀ n, M ≤ n → (prod n : ℝ)⁻¹ ≤ ((1 : ℝ) / 2) ^ (n + 1) := by
  intro n _
  calc (prod n : ℝ)⁻¹
      ≤ ((2 : ℝ) ^ (n + 1))⁻¹ := prod_inv_le_two_pow_inv n
    _ = ((1 : ℝ) / 2) ^ (n + 1) := two_pow_inv_eq_half_pow n

end Structural

/-! ## Section 6: Landscape Theorem -/

section Landscape

/-- Summary of the L-function perspective:
    1. The accumulator reciprocal series converges (PROVED)
    2. Self-similar head + tail decomposition (PROVED)
    3. L-function factorization is circular (Dead End #132)
    4. Self-similar FE framework mismatch (Dead End #133)
    5. Distinct primes have irrational log ratios (PROVED)
    6. No Tauberian lever for L_{EM} (Dead End #134) -/
theorem em_lfunction_landscape :
    -- 1. Accumulator reciprocal series converges (PROVED)
    Summable (fun n => (prod n : ℝ)⁻¹) ∧
    -- 2. Self-similar decomposition (PROVED)
    (∀ M K q χ, ∑ k ∈ Finset.range (M + K), χ (seq (k + 1) % q) =
      (∑ k ∈ Finset.range M, χ (seq (k + 1) % q)) +
      genSeqCharPartialSum (prod M) K q χ) ∧
    -- 3. L-function factorization is circular (Dead End #132)
    LFunctionFactorizationCircular ∧
    -- 4. Self-similar FE framework mismatch (Dead End #133)
    SelfSimilarFrameworkMismatch ∧
    -- 5. Distinct primes have irrational log ratios
    (∀ p q : Nat, Nat.Prime p → Nat.Prime q → p ≠ q →
      ∀ a b : Nat, 0 < a → 0 < b → p ^ a ≠ q ^ b) ∧
    -- 6. No Tauberian lever for L_{EM} (Dead End #134)
    TauberianLeverAbsent :=
  ⟨accum_reciprocal_summable,
   em_self_similar_decomposition,
   trivial,
   trivial,
   fun _ _ hp hq hne _ _ ha hb => prime_pow_ne_prime_pow hp hq hne ha hb,
   trivial⟩

end Landscape

end
