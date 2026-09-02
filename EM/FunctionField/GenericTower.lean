import EM.FunctionField.StableTower
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.Eval.Irreducible

/-!
# The generic Euclid–Mullin sequence, and the level polynomials over `ℚ`

`EM/FunctionField/StableTower.lean` proves that every level polynomial
`g_n = Φ₆ⁿ(X) + 1`, `Φ₆(y) = y(y+1)`, is irreducible over `𝔽_5`.  A monic integer polynomial
whose reduction mod a prime is irreducible is irreducible over `ℤ`, hence (Gauss) over `ℚ`.  So:

* **every level polynomial is irreducible over `ℤ` and over `ℚ`** (`gZ_irreducible`,
  `gQ_irreducible`): the backward-orbit tree of `−1` under `y ↦ y² + y` is *stable* over `ℚ`,
  and the Galois group acts transitively on every level;
* **the generic Euclid–Mullin sequence is a Sylvester tower.**  Over `R[x]` with the seed `x`
  (the generic point), the accumulator on the autonomous branch is `iterR R n = Φ₆ⁿ(x)` and the
  Euclid polynomial is `iterR R n + 1 = g_n(x)`.  Over `ℚ[x]` every one of them is irreducible
  (`gQ_irreducible`), so the greedy sequence from the seed `x` is
  `x, x+1, x²+x+1, x⁴+2x³+2x²+x+1, …` forever: it never leaves the tower and misses every
  irreducible polynomial not of the form `g_n`.

## Specialization versus reduction

Every function-field seed-`X` sequence over `𝔽_p[X]` is the reduction mod `p` of this generic
sequence, and the integer Euclid–Mullin sequence is its specialization at `x = 2`
(`g_0(2) = 3`, `g_1(2) = 7`, `g_2(2) = 43`).  The reduction leaves the tower at the first level
where `g_k` factors mod `p` (a Galois-theoretic event; never, for exceptional `p` such as `5`).
The specialization leaves it at stage `3`, because `g_3(2) = 1807 = 13 · 139` is composite
(`gZ_three_eval_two`) — an arithmetic event about a *value* of an irreducible polynomial.
Mullin's conjecture over `ℤ` lives entirely in this third regime: (C∞) says the specialization
leaves every tower it enters, whereas the generic sequence never does.

Consequence for the shape of (C∞): perpetual primality from stage `N` says that the single
integer `P_N` is a simultaneous prime value of the infinitely many irreducible polynomials
`g_k`; even the Bunyakovsky instance "`y² + y + 1` is prime infinitely often" is open.

See `docs/analysis/logic_routes_2026-09-01.md` §14.
-/

namespace FunctionFieldAnalog

open Polynomial

namespace GenericTower

/-! ## 1. The level polynomials over an arbitrary commutative ring -/

/-- `iterR R n = Φ₆ⁿ(X)` over `R`: the accumulator of the generic sequence. -/
noncomputable def iterR (R : Type*) [CommRing R] : ℕ → R[X]
  | 0 => X
  | n + 1 => iterR R n * (iterR R n + 1)

variable {R S : Type*} [CommRing R] [CommRing S]

theorem iterR_zero : iterR R 0 = X := rfl

theorem iterR_succ (n : ℕ) : iterR R (n + 1) = iterR R n * (iterR R n + 1) := rfl

/-- Reduction commutes with the recursion. -/
theorem map_iterR (f : R →+* S) (n : ℕ) : (iterR R n).map f = iterR S n := by
  induction n with
  | zero => simp [iterR]
  | succ n ih => simp [iterR, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_one, ih]

theorem iterR_monic_natDegree [Nontrivial R] (n : ℕ) :
    (iterR R n).Monic ∧ (iterR R n).natDegree = 2 ^ n := by
  induction n with
  | zero => exact ⟨monic_X, natDegree_X⟩
  | succ n ih =>
    obtain ⟨hm, hd⟩ := ih
    have hpos : 0 < (iterR R n).natDegree := by rw [hd]; positivity
    have hlt : (1 : R[X]).natDegree < (iterR R n).natDegree := by rw [natDegree_one]; exact hpos
    have hm1 : (iterR R n + 1).Monic := by
      refine hm.add_of_left ?_
      rw [degree_one, degree_eq_natDegree hm.ne_zero]
      exact_mod_cast hpos
    refine ⟨hm.mul hm1, ?_⟩
    rw [iterR_succ, hm.natDegree_mul hm1, natDegree_add_eq_left_of_natDegree_lt hlt, hd]
    ring

theorem gR_monic [Nontrivial R] (n : ℕ) : (iterR R n + 1).Monic := by
  obtain ⟨hm, hd⟩ := iterR_monic_natDegree (R := R) n
  refine hm.add_of_left ?_
  rw [degree_one, degree_eq_natDegree hm.ne_zero, hd]
  exact_mod_cast (by positivity : 0 < 2 ^ n)

theorem gR_natDegree [Nontrivial R] (n : ℕ) : (iterR R n + 1).natDegree = 2 ^ n := by
  obtain ⟨_, hd⟩ := iterR_monic_natDegree (R := R) n
  rw [natDegree_add_eq_left_of_natDegree_lt, hd]
  rw [natDegree_one, hd]; positivity

/-- Over `𝔽_5` the generic recursion is the one of `StableTower`. -/
theorem iterR_zmod_five (n : ℕ) : iterR (ZMod 5) n = StableTower.iter n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterR_succ, StableTower.iter_succ, ih]

/-! ## 2. Irreducibility over `ℤ` and `ℚ` -/

/-- **Every level polynomial `Φ₆ⁿ(X) + 1` is irreducible over `ℤ`.**  Its reduction mod `5` is
irreducible (`StableTower.g_irreducible`). -/
theorem gZ_irreducible (n : ℕ) : Irreducible (iterR ℤ n + 1) := by
  refine Polynomial.Monic.irreducible_of_irreducible_map (φ := Int.castRingHom (ZMod 5)) _
    (gR_monic n) ?_
  rw [Polynomial.map_add, Polynomial.map_one, map_iterR, iterR_zmod_five]
  exact StableTower.g_irreducible n

/-- **Every level polynomial `Φ₆ⁿ(X) + 1` is irreducible over `ℚ`**: the tree over `−1` under
`y ↦ y² + y` is stable over `ℚ`, and the generic Euclid–Mullin sequence (seed `x` in `ℚ[x]`)
is a perpetually irreducible Sylvester tower. -/
theorem gQ_irreducible (n : ℕ) : Irreducible (iterR ℚ n + 1) := by
  have h := (gR_monic (R := ℤ) n).irreducible_iff_irreducible_map_fraction_map (K := ℚ)
  have hmap : (iterR ℤ n + 1).map (algebraMap ℤ ℚ) = iterR ℚ n + 1 := by
    rw [Polynomial.map_add, Polynomial.map_one, map_iterR]
  rw [hmap] at h
  exact h.mp (gZ_irreducible n)

/-! ## 3. The specialization at `2` leaves the tower at stage 3 -/

theorem gZ_eval_two_zero : (iterR ℤ 0 + 1).eval 2 = 3 := by simp [iterR]

theorem gZ_eval_two_one : (iterR ℤ 1 + 1).eval 2 = 7 := by simp [iterR]

theorem gZ_eval_two_two : (iterR ℤ 2 + 1).eval 2 = 43 := by simp [iterR]

/-- `g_3(2) = 1807 = 13 · 139`: the integer sequence leaves the generic tower at stage `3`
because a *value* of the irreducible polynomial `g_3` is composite. -/
theorem gZ_three_eval_two : (iterR ℤ 3 + 1).eval 2 = 13 * 139 := by simp [iterR]

end GenericTower

end FunctionFieldAnalog
