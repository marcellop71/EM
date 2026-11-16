import EM.FunctionField.StabilityCriterion
import Mathlib.RingTheory.Int.Basic

/-!
# Which primes are stable

`Stable p` (`TowerClassification.lean`) says that the tower `g^k(Y) + 1` is irreducible at
every level over `𝔽_p`; the function-field Mullin conjecture over `𝔽_p` is false for stable
`p` and equivalent to the dichotomy otherwise.

## Small cases

* `stable_iff_perpetual` — `p` is stable iff every sequence over `𝔽_p` is a tower.
* `not_stable_two`, `not_stable_three`, `not_stable_of_one_mod_three`, `stable_five`.

## The integer discriminants

The elements of `𝔽_p` that decide stability (`StabilityCriterion.disc`) are the reductions
of **one sequence of integers**, independent of `p`: with `n_0 = -1`,
`n_{k+1} = n_k (n_k + 4^{2^k})` (so that `g^k(-1/4) = n_k / 4^{2^k}`),

    discZ k = (-1)^{2^k} (n_k + 4^{2^k}),      discZ 0 = -3,  discZ 1 = 13, …

* `disc_eq_cast` — `disc p k = (discZ k : ZMod p)` for odd `p`.
* `stable_iff_discZ` — odd `p` is stable iff no `discZ k` is a square mod `p`.
* `isCoprime_discZ` — the `discZ k` are pairwise coprime (the Euclid argument:
  `n_j ≡ 0` modulo the earlier ones).
* `not_isSquare_discZ_of_stable` — **a stable prime certifies that no `discZ k` is a square
  in `ℤ`**; `not_isSquare_discZ` — and `5` is stable.
* `not_isSquare_prod_discZ` — **independence**: no non-empty finite product of distinct
  `discZ k` is a square in `ℤ`. (A coprime factor of a square is `±` a square, and `-1` is a
  square mod `5`.)

## Consequence (not formalised)

For each `K`, the conditions "`discZ k` is a non-square mod `p`", `k ≤ K`, are `K + 1`
independent quadratic conditions on `p`: by quadratic reciprocity and Dirichlet's theorem
the primes satisfying all of them have density `2^{-(K+1)}`. Stable primes satisfy them for
every `K`, so **the stable primes have density zero**. See
`docs/analysis/fibre_rule_2026-11-15.md` §12.
-/

namespace FunctionFieldAnalog

namespace StablePrimes

open Polynomial CompositeFloors FFDegreeTelescope TowerClassification StabilityCriterion

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ## 1. Small cases -/

/-- `p` is stable iff every sequence over `𝔽_p` is a tower from stage `0`. -/
theorem stable_iff_perpetual (p : ℕ) [Fact (Nat.Prime p)] :
    Stable p ↔ ∀ d : FFEMData p, FFPerpetualIrreducibility d 0 := by
  constructor
  · exact fun h d => perpetual_of_stable h d
  · intro h k
    obtain ⟨d⟩ : Nonempty (FFEMData p) := inferInstance
    exact level_irreducible_of_run d 0 k (fun j _ => by simpa using h d j (Nat.zero_le j))

theorem not_stable_of_infinitelyManyReducible
    (h : ∀ d : FFEMData p, FFInfinitelyManyReducible d) : ¬ Stable p := by
  intro hs
  obtain ⟨d⟩ : Nonempty (FFEMData p) := inferInstance
  exact (ffInfinitelyManyReducible_iff d).mp (h d) 0 (perpetual_of_stable hs d)

/-- **`2` is not stable.** -/
theorem not_stable_two : ¬ Stable 2 :=
  not_stable_of_infinitelyManyReducible infinitelyManyReducible_of_two

theorem not_stable_three : ¬ Stable 3 :=
  not_stable_of_infinitelyManyReducible CharThree.infinitelyManyReducible

theorem not_stable_of_one_mod_three (hp3 : p % 3 = 1) : ¬ Stable p :=
  not_stable_of_infinitelyManyReducible (infinitelyManyReducible_of_one_mod_three hp3)

/-- **`5` is stable.** -/
theorem stable_five : Stable 5 := fun k =>
  level_irreducible_of_run StableTower.tower 0 k
    (fun j _ => by simpa using StableTower.tower_euclid_irreducible j)

/-! ## 2. The integer discriminants -/

/-- Numerators of the critical orbit: `g^k(-1/4) = nZ k / 4^{2^k}`. -/
def nZ : ℕ → ℤ
  | 0 => -1
  | k + 1 => nZ k * (nZ k + 4 ^ 2 ^ k)

/-- `eZ k = 4^{2^k} (g^k(-1/4) + 1)`. -/
def eZ (k : ℕ) : ℤ := nZ k + 4 ^ 2 ^ k

/-- The integer discriminants. -/
def discZ (k : ℕ) : ℤ := (-1) ^ 2 ^ k * eZ k

theorem nZ_succ (k : ℕ) : nZ (k + 1) = nZ k * eZ k := rfl

theorem iter_eval_succ (c : ZMod p) (k : ℕ) :
    eval c (iter p (k + 1)) = eval c (iter p k) * (eval c (iter p k) + 1) := by
  show eval c (iter p k * (iter p k + 1)) = _
  simp

theorem nZ_cast (hp2 : p ≠ 2) (k : ℕ) :
    ((nZ k : ℤ) : ZMod p) = 4 ^ 2 ^ k * eval (-(4 : ZMod p)⁻¹) (iter p k) := by
  have h4 := mul_inv_cancel₀ (four_ne_zero (p := p) hp2)
  induction k with
  | zero =>
    simp only [nZ, iter, pow_zero, pow_one, eval_X]
    push_cast
    linear_combination h4
  | succ k ih =>
    rw [nZ, iter_eval_succ, pow_succ, pow_mul]
    push_cast
    rw [ih]
    ring

/-- The discriminant elements are the reductions of the integers `discZ k`. -/
theorem disc_eq_cast (hp2 : p ≠ 2) (k : ℕ) : disc p k = ((discZ k : ℤ) : ZMod p) := by
  rw [disc, discZ, eZ]
  push_cast
  rw [nZ_cast hp2 k, level, eval_add, eval_one, neg_pow]
  ring

/-- Odd `p` is stable iff no integer discriminant is a square mod `p`. -/
theorem stable_iff_discZ (hp2 : p ≠ 2) :
    Stable p ↔ ∀ k, ¬ IsSquare ((discZ k : ℤ) : ZMod p) := by
  rw [stable_iff hp2]
  simp only [disc_eq_cast hp2]

/-- **A stable prime certifies non-squareness over `ℤ`.** -/
theorem not_isSquare_discZ_of_stable (hp2 : p ≠ 2) (hs : Stable p) (k : ℕ) :
    ¬ IsSquare (discZ k) := fun h =>
  (stable_iff_discZ hp2).mp hs k (h.map (Int.castRingHom (ZMod p)))

/-- No integer discriminant is a square (witness: the stable prime `5`). -/
theorem not_isSquare_discZ (k : ℕ) : ¬ IsSquare (discZ k) :=
  not_isSquare_discZ_of_stable (p := 5) (by decide) stable_five k

/-! ## 3. Pairwise coprimality and independence -/

theorem eZ_dvd_nZ {k j : ℕ} (h : k < j) : eZ k ∣ nZ j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [nZ_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · exact Dvd.dvd.mul_right (ih h) _
    · exact Dvd.intro_left _ rfl

theorem odd_nZ_eZ (k : ℕ) : Odd (nZ k) ∧ Odd (eZ k) := by
  induction k with
  | zero => exact ⟨⟨-1, by simp [nZ]⟩, ⟨1, by simp [eZ, nZ]⟩⟩
  | succ k ih =>
    have h1 : Odd (nZ (k + 1)) := by rw [nZ_succ]; exact ih.1.mul ih.2
    refine ⟨h1, ?_⟩
    rw [eZ]
    have h4 : Even (4 : ℤ) := ⟨2, by norm_num⟩
    exact h1.add_even (h4.pow_of_ne_zero (pow_ne_zero _ two_ne_zero))

theorem isCoprime_eZ {k j : ℕ} (h : k < j) : IsCoprime (eZ k) (eZ j) := by
  obtain ⟨t, ht⟩ := (odd_nZ_eZ k).2
  have h2 : IsCoprime (eZ k) 2 := ⟨1, -t, by rw [ht]; ring⟩
  have h4 : IsCoprime (eZ k) ((4 : ℤ) ^ 2 ^ j) := by
    have : (4 : ℤ) = 2 ^ 2 := by norm_num
    rw [this]
    exact (h2.pow_right).pow_right
  obtain ⟨y, hy⟩ := eZ_dvd_nZ h
  show IsCoprime (eZ k) (nZ j + 4 ^ 2 ^ j)
  rw [hy, add_comm]
  exact h4.add_mul_left_right y

theorem isCoprime_sign_mul (m : ℕ) {a b : ℤ} (h : IsCoprime a b) :
    IsCoprime ((-1) ^ m * a) b := by
  rcases neg_one_pow_eq_or ℤ m with hm | hm
  · rw [hm, one_mul]; exact h
  · rw [hm, neg_one_mul]; exact h.neg_left

theorem isCoprime_discZ {k j : ℕ} (h : k ≠ j) : IsCoprime (discZ k) (discZ j) := by
  have key : IsCoprime (eZ k) (eZ j) := by
    rcases lt_or_gt_of_ne h with h | h
    · exact isCoprime_eZ h
    · exact (isCoprime_eZ h).symm
  rw [discZ, discZ]
  exact isCoprime_sign_mul _ (isCoprime_sign_mul _ key.symm).symm

/-- **Independence.** No non-empty product of distinct integer discriminants is a square. -/
theorem not_isSquare_prod_discZ {A : Finset ℕ} (hA : A.Nonempty) :
    ¬ IsSquare (∏ k ∈ A, discZ k) := by
  classical
  obtain ⟨k, hk⟩ := hA
  rintro ⟨c, hc⟩
  rw [← Finset.mul_prod_erase A _ hk] at hc
  have hcop : IsCoprime (discZ k) (∏ j ∈ A.erase k, discZ j) :=
    IsCoprime.prod_right fun j hj => isCoprime_discZ (Finset.ne_of_mem_erase hj).symm
  obtain ⟨a, ha | ha⟩ := Int.sq_of_isCoprime hcop (by rw [hc]; ring)
  · exact not_isSquare_discZ k ⟨a, by rw [ha]; ring⟩
  · -- `-1` is a square mod `5`, so `-a²` is a square mod `5`
    have h5 : IsSquare ((discZ k : ℤ) : ZMod 5) :=
      ⟨2 * (a : ZMod 5), by
        rw [ha]; push_cast
        have : (4 : ZMod 5) = -1 := by decide
        linear_combination (-(a : ZMod 5) ^ 2) * this⟩
    exact (stable_iff_discZ (p := 5) (by decide)).mp stable_five k h5

end StablePrimes

end FunctionFieldAnalog
