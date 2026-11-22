import EM.FunctionField.StablePrimes
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Counting stable primes: the sieve identity and the input from GRH

A prime `p` is stable when no integer discriminant `Δ_k = discZ k` is a square mod `p`
(`StablePrimes.stable_iff_discZ`); the function-field Mullin conjecture over `𝔽_p` is false
exactly for those `p` among the primes where it is not the dichotomy. This file reduces the
count of stable primes to sums of one quadratic character over primes.

## The sieve identity

For a prime `p` put `ε_k = (Δ_k / p)`. Then `∏_{k<K} (1 − ε_k)` is `2^K` when every `ε_k` is
`−1` and is non-negative always, and it expands as
`∑_{A ⊆ {0..K−1}} (−1)^{|A|} (Δ_A / p)` with `Δ_A = ∏_{k∈A} Δ_k`. Summing over primes `p ≤ x`:

`2^K · #{stable p ≤ x} ≤ π(x) + ∑_{A ≠ ∅} |∑_{p ≤ x} (Δ_A / p)|`.

No `Δ_A` with `A ≠ ∅` is a square (`StablePrimes.not_isSquare_prod_discZ`), so each inner sum
is the sum over primes of a non-trivial quadratic character.

## Main results

* `two_pow_mul_card_stable_le` — the inequality above, with any bound `E` for the inner sums.
* `abs_discProd_le` — `|Δ_A| ≤ 4^{2^K}` for `A ⊆ {0..K−1}`.
* `card_stable_le` — under `QuadPrimeSumBound C`,
  `#{stable p ≤ x} ≤ x / 2^K + C √x log²(4^{2^K} x)` for every `K`.

## The analytic input

`GRHDirichlet` is the statement "no Dirichlet `L`-function vanishes for `Re s > 1/2`", written
with Mathlib's definitions only. It is the statement
`DirichletLNonvanishingRightOfHalf` of `src/Challenge.lean` in the repository
`leanprover-community/riemann-hypothesis`, where it is proved as
`LFunction_ne_zero_of_half_lt_re`. That repository is not a dependency of this one: here the
statement is a `Prop`, used only as a hypothesis, never as an axiom.

`QuadPrimeSumBound C` is the classical consequence for prime sums of quadratic characters,
`|∑_{p ≤ x} (D / p)| ≤ C √x log²(|D| x)` for non-square `D` (Davenport, *Multiplicative Number
Theory*, ch. 20, with the conductor of `(D / ·)` at most `4|D|`). The implication
`IK.GRHPsiBound C → ∃ C', QuadPrimeSumBound C'` is proved in `QuadCharBridge.lean`, and
`GRHPsiBound` from the explicit formula, the zero count and GRH in `EM/IK/GRHBridge.lean`;
the chain is assembled in `StableGRH.lean`.

Taking `2^K` of size `x^{1/6}` in `card_stable_le` gives `#{stable p ≤ x} = O(x^{5/6})`, so
the reciprocals of the stable primes have a convergent sum. Without GRH the same identity
gives only density zero (`docs/analysis/fibre_rule_2026-11-15.md` §12, §15).
-/

namespace FunctionFieldAnalog

namespace StableCount

open Finset TowerClassification StablePrimes

/-- **GRH for Dirichlet `L`-functions**, in the form of `Challenge.lean` of
    `leanprover-community/riemann-hypothesis` (`DirichletLNonvanishingRightOfHalf`). -/
def GRHDirichlet : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- The primes up to `x`. -/
def primesLE (x : ℕ) : Finset ℕ := (Icc 1 x).filter Nat.Prime

/-- The sum of the quadratic symbol `(D / p)` over the primes `p ≤ x`. -/
def charSum (D : ℤ) (x : ℕ) : ℤ := ∑ p ∈ primesLE x, jacobiSym D p

/-- `Δ_A = ∏_{k ∈ A} Δ_k`. -/
def discProd (A : Finset ℕ) : ℤ := ∏ k ∈ A, discZ k

/-- The prime-sum bound for quadratic characters that follows from GRH. -/
def QuadPrimeSumBound (C : ℝ) : Prop :=
  ∀ D : ℤ, ¬ IsSquare D → ∀ x : ℕ, 2 ≤ x →
    |(charSum D x : ℝ)| ≤ C * Real.sqrt x * Real.log (|(D : ℝ)| * x) ^ 2

open Classical in
/-- The stable primes up to `x`. -/
noncomputable def stableLE (x : ℕ) : Finset ℕ :=
  (primesLE x).filter fun p => ∃ h : p.Prime, @Stable p ⟨h⟩

theorem card_primesLE_le (x : ℕ) : (primesLE x).card ≤ x := by
  have := card_filter_le (Icc 1 x) Nat.Prime
  simpa [primesLE] using this

/-! ## 1. The symbol at a stable prime -/

/-- At a stable prime every discriminant has symbol `−1`. -/
theorem jacobiSym_discZ_of_stable {p : ℕ} (hp : p.Prime) (hs : @Stable p ⟨hp⟩) (k : ℕ) :
    jacobiSym (discZ k) p = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact not_stable_two hs
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
  exact (stable_iff_discZ hp2).mp hs k

/-- The symbol is multiplicative over a product of discriminants. -/
theorem jacobiSym_discProd (A : Finset ℕ) (p : ℕ) :
    jacobiSym (discProd A) p = ∏ k ∈ A, jacobiSym (discZ k) p := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [discProd, jacobiSym.one_left]
  | insert a s ha ih =>
    rw [discProd, prod_insert ha, jacobiSym.mul_left, prod_insert ha]
    rw [discProd] at ih
    rw [ih]

/-! ## 2. The sieve identity -/

/-- Expansion of the detector `∏ (1 − ε_k)`. -/
theorem prod_one_sub_eq (K p : ℕ) :
    ∏ k ∈ range K, (1 - jacobiSym (discZ k) p) =
      ∑ A ∈ (range K).powerset, (-1) ^ A.card * jacobiSym (discProd A) p := by
  simp only [sub_eq_add_neg]
  rw [prod_one_add]
  refine sum_congr rfl fun A _ => ?_
  rw [prod_neg, jacobiSym_discProd]

/-- The detector is non-negative, and equals `2^K` at a stable prime. -/
theorem detector_nonneg (K p : ℕ) : 0 ≤ ∏ k ∈ range K, (1 - jacobiSym (discZ k) p) :=
  prod_nonneg fun k _ => by
    rcases jacobiSym.trichotomy (discZ k) p with h | h | h <;> rw [h] <;> norm_num

theorem detector_of_stable (K : ℕ) {p : ℕ} (hp : p.Prime) (hs : @Stable p ⟨hp⟩) :
    ∏ k ∈ range K, (1 - jacobiSym (discZ k) p) = 2 ^ K := by
  rw [prod_congr rfl fun k _ => by rw [jacobiSym_discZ_of_stable hp hs k]]
  norm_num

/-- **The sieve inequality over `ℤ`.** -/
theorem two_pow_mul_card_stable_le_sum (K x : ℕ) :
    (2 : ℤ) ^ K * (stableLE x).card ≤
      ∑ A ∈ (range K).powerset, (-1) ^ A.card * charSum (discProd A) x := by
  classical
  have h1 : (2 : ℤ) ^ K * (stableLE x).card =
      ∑ p ∈ stableLE x, ∏ k ∈ range K, (1 - jacobiSym (discZ k) p) := by
    rw [sum_congr rfl fun p hp => ?_, sum_const, nsmul_eq_mul, mul_comm]
    obtain ⟨h, hs⟩ := (mem_filter.mp hp).2
    exact detector_of_stable K h hs
  have h2 : ∑ p ∈ stableLE x, ∏ k ∈ range K, (1 - jacobiSym (discZ k) p) ≤
      ∑ p ∈ primesLE x, ∏ k ∈ range K, (1 - jacobiSym (discZ k) p) :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ => detector_nonneg K p
  rw [h1]
  refine h2.trans (le_of_eq ?_)
  simp only [prod_one_sub_eq, charSum, mul_sum]
  exact sum_comm

/-- **The sieve inequality.** If every character sum `∑_{p ≤ x} (Δ_A / p)` with
    `∅ ≠ A ⊆ {0..K−1}` is at most `E` in absolute value, then
    `2^K · #{stable p ≤ x} ≤ π(x) + (2^K − 1) E`. -/
theorem two_pow_mul_card_stable_le (K x : ℕ) (E : ℝ)
    (hE : ∀ A, A ⊆ range K → A.Nonempty → |(charSum (discProd A) x : ℝ)| ≤ E) :
    (2 : ℝ) ^ K * (stableLE x).card ≤ (primesLE x).card + (2 ^ K - 1) * E := by
  classical
  have h := two_pow_mul_card_stable_le_sum K x
  have hR : ((2 : ℤ) ^ K * (stableLE x).card : ℤ) ≤ _ := h
  have hcast : (2 : ℝ) ^ K * (stableLE x).card ≤
      ∑ A ∈ (range K).powerset, (-1 : ℝ) ^ A.card * (charSum (discProd A) x : ℝ) := by
    have := (Int.cast_le (R := ℝ)).mpr hR
    push_cast at this
    exact this
  refine hcast.trans ?_
  have hmem : (∅ : Finset ℕ) ∈ (range K).powerset := empty_mem_powerset _
  rw [← add_sum_erase _ _ hmem]
  have h0 : (-1 : ℝ) ^ (∅ : Finset ℕ).card * (charSum (discProd ∅) x : ℝ) = (primesLE x).card := by
    simp [charSum, discProd, jacobiSym.one_left]
  rw [h0]
  gcongr
  have hcard : (((range K).powerset.erase ∅).card : ℝ) = 2 ^ K - 1 := by
    rw [card_erase_of_mem hmem, card_powerset, card_range]
    have : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    push_cast [Nat.cast_sub this]
    ring
  calc ∑ A ∈ (range K).powerset.erase ∅, (-1 : ℝ) ^ A.card * (charSum (discProd A) x : ℝ)
      ≤ ∑ _A ∈ (range K).powerset.erase ∅, E := by
        refine sum_le_sum fun A hA => ?_
        obtain ⟨hne, hsub⟩ := mem_erase.mp hA
        have hb := hE A (mem_powerset.mp hsub) (nonempty_iff_ne_empty.mpr hne)
        calc (-1 : ℝ) ^ A.card * (charSum (discProd A) x : ℝ)
            ≤ |(-1 : ℝ) ^ A.card * (charSum (discProd A) x : ℝ)| := le_abs_self _
          _ = |(charSum (discProd A) x : ℝ)| := by
              rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
          _ ≤ E := hb
    _ = (2 ^ K - 1) * E := by rw [sum_const, nsmul_eq_mul, hcard]

/-! ## 3. The size of the moduli -/

/-- `−4^{2^k} < n_k < 0`. -/
theorem nZ_bounds (k : ℕ) : nZ k < 0 ∧ -(4 ^ 2 ^ k) < nZ k := by
  induction k with
  | zero => constructor <;> norm_num [nZ]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have hM : (4 : ℤ) ^ 2 ^ (k + 1) = 4 ^ 2 ^ k * 4 ^ 2 ^ k := by
      rw [pow_succ, pow_mul, sq]
    rw [nZ_succ, eZ, hM]
    constructor
    · nlinarith
    · nlinarith [sq_nonneg (nZ k + 4 ^ 2 ^ k), sq_nonneg (nZ k)]

/-- `0 < e_k < 4^{2^k}`. -/
theorem eZ_bounds (k : ℕ) : 0 < eZ k ∧ eZ k < 4 ^ 2 ^ k := by
  obtain ⟨h1, h2⟩ := nZ_bounds k
  rw [eZ]
  constructor <;> linarith

theorem abs_discZ_le (k : ℕ) : |discZ k| ≤ 4 ^ 2 ^ k := by
  obtain ⟨h1, h2⟩ := eZ_bounds k
  rw [discZ, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos h1]
  exact h2.le

theorem sum_two_pow_lt (K : ℕ) : ∑ k ∈ range K, 2 ^ k < 2 ^ K := by
  induction K with
  | zero => simp
  | succ K ih => rw [sum_range_succ, pow_succ]; omega

/-- `|Δ_A| ≤ 4^{2^K}` for `A ⊆ {0..K−1}`. -/
theorem abs_discProd_le {A : Finset ℕ} {K : ℕ} (hA : A ⊆ range K) :
    |discProd A| ≤ 4 ^ 2 ^ K := by
  rw [discProd, abs_prod]
  calc ∏ k ∈ A, |discZ k| ≤ ∏ k ∈ A, (4 : ℤ) ^ 2 ^ k :=
        Finset.prod_le_prod₀ (fun k _ => abs_nonneg (discZ k)) (fun k _ => abs_discZ_le k)
    _ = 4 ^ ∑ k ∈ A, 2 ^ k := prod_pow_eq_pow_sum A (fun k => 2 ^ k) 4
    _ ≤ 4 ^ 2 ^ K := by
        refine pow_le_pow_right₀ (by norm_num) ?_
        exact (sum_le_sum_of_subset hA).trans (sum_two_pow_lt K).le

/-! ## 4. The count under the GRH prime-sum bound -/

/-- **Stable primes under the GRH prime-sum bound.** For every `K` and `x ≥ 2`,
    `#{stable p ≤ x} ≤ x / 2^K + C √x log²(4^{2^K} x)`. -/
theorem card_stable_le {C : ℝ} (hC : 0 ≤ C) (h : QuadPrimeSumBound C) (K x : ℕ) (hx : 2 ≤ x) :
    ((stableLE x).card : ℝ) ≤
      (x : ℝ) / 2 ^ K + C * Real.sqrt x * Real.log ((4 : ℝ) ^ 2 ^ K * x) ^ 2 := by
  set E : ℝ := C * Real.sqrt x * Real.log ((4 : ℝ) ^ 2 ^ K * x) ^ 2 with hEdef
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (by omega : 1 ≤ x)
  have hE0 : 0 ≤ E := by positivity
  have hE : ∀ A, A ⊆ range K → A.Nonempty → |(charSum (discProd A) x : ℝ)| ≤ E := by
    intro A hA hne
    refine (h (discProd A) (not_isSquare_prod_discZ hne) x hx).trans ?_
    have hD0 : discProd A ≠ 0 := fun h0 =>
      not_isSquare_prod_discZ hne (by rw [show ∏ k ∈ A, discZ k = 0 from h0]; exact ⟨0, by ring⟩)
    have hD1 : (1 : ℝ) ≤ |(discProd A : ℝ)| := by
      have : (1 : ℤ) ≤ |discProd A| := Int.one_le_abs hD0
      exact_mod_cast this
    have hDle : |(discProd A : ℝ)| ≤ (4 : ℝ) ^ 2 ^ K := by
      have := abs_discProd_le hA
      exact_mod_cast this
    have hlog0 : 0 ≤ Real.log (|(discProd A : ℝ)| * x) :=
      Real.log_nonneg (by nlinarith)
    have hlog : Real.log (|(discProd A : ℝ)| * x) ≤ Real.log ((4 : ℝ) ^ 2 ^ K * x) :=
      Real.log_le_log (by positivity) (by gcongr)
    rw [hEdef]
    gcongr
  have hmain := two_pow_mul_card_stable_le K x E hE
  have hpi : ((primesLE x).card : ℝ) ≤ x := by exact_mod_cast card_primesLE_le x
  have h2 : (0 : ℝ) < 2 ^ K := by positivity
  have hstep : (2 : ℝ) ^ K * (stableLE x).card ≤ x + 2 ^ K * E := by
    nlinarith
  rw [div_add' _ _ _ h2.ne', le_div_iff₀ h2]
  linarith

end StableCount

end FunctionFieldAnalog
