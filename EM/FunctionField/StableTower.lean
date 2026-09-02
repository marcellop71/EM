import EM.FunctionField.Analog
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# The function-field Mullin conjecture is false over `𝔽_5[X]`

`FFMullinConjecture p` (`EM/FunctionField/Analog.lean`) says that for every function-field
Euclid–Mullin sequence over `𝔽_p[X]` (seed `X`, least-degree monic irreducible factor at each
step, any tie-break) every monic irreducible appears.  This file refutes it for `p = 5`.

## The mechanism: a stable Sylvester tower

On the *autonomous branch* — as long as every Euclid number `E_n = P_n + 1` is irreducible —
the accumulator follows the take-all map `Φ₆(P) = P(P+1)`, so `P_n = Φ₆ⁿ(X)` and
`E_n = g_n(X)` with `g_n := Φ₆ⁿ + 1` (the level polynomials of the arboreal tower).  For the
seed `X` the branch is perpetual iff every `g_n` is irreducible over `𝔽_p`.

By Capelli's lemma and the finite-field norm criterion, `g_n` is irreducible iff `g_{n-1}` is
and `Φ₆^{n-1}(-1/4) + 1` is a non-square mod `p`.  Over `𝔽_5` we have `-1/4 = 1`, the orbit of
`1` under `y ↦ y² + y` is the 2-cycle `1, 2, 1, 2, …`, and the shifted values `3, 2` are both
non-squares mod 5.  So every `g_n` is irreducible over `𝔽_5`, the sequence is

    X, X+1, X²+X+1, X⁴+2X³+2X²+X+1, g₃(X), g₄(X), …

(one irreducible of each degree `2^k`, no ties ever), and every irreducible of degree not a power
of two — as well as the linear polynomials `X + 2` and `X + 3` — is missed.

## The proof, without Capelli

We avoid Capelli and norms.  In `L = 𝔽̄_5` build `α₀ = -1`, `α_{k+1} = 3 s_{k+1} + 2` with
`s_{k+1}² = 1 + 4 α_k`, so that `α_{k+1}² + α_{k+1} = α_k` and `g_n(α_n) = 0`.  Writing
`q_e = 5^{2^e}` and `m_e = (q_e - 1)/2`, a single simultaneous induction proves

* `α_k^{q_k} = α_k`,
* `(1 + 4α_k)^{m_k} = -1`,
* `(2 + 4α_k)^{m_k} = -1`,

using only that `x ↦ x^{q_e}` is a ring endomorphism fixing `𝔽_5` (`add_pow_char_pow`) and the
exponent identity `m_{e+1} = m_e (q_e + 1)`.  Hence `s_{k+1}^{q_k} = -s_{k+1}`, so
`α_n^{q_{n-1}} = -3 s_n + 2 ≠ α_n`: the Frobenius orbit of `α_n` has exactly `2^n` points, all
roots of the minimal polynomial of `α_n`, which therefore has degree `≥ 2^n = deg g_n` and
divides `g_n`.  So `g_n` *is* the minimal polynomial, hence irreducible.

## Main results

* `StableTower.g_irreducible` — every level polynomial `g n` is irreducible over `𝔽_5`.
* `StableTower.tower : FFEMData 5` — the stable-tower sequence (`ffSeq (n+1) = g n`).
* `not_ffMullinConjecture_five : ¬ FFMullinConjecture 5`.

## Consequences (see `docs/analysis/logic_routes_2026-09-01.md` §9, §11, §13.1)

The composite floor `(C∞)_FF` and FF-MC fail *together* over `𝔽_5[X]` for the seed `X`: the
perpetually irreducible Sylvester tower that cannot be excluded over `ℤ` is realised.  The
function-field conjecture therefore cannot be stated uniformly in `p`; the honest form excludes
the *exceptional primes* (those whose critical orbit of `-1/4` under `y² + y` avoids all
squares-minus-one; they are `≡ 2 (mod 3)` and rare — `11, 17, 23, 29, 41, 47` are not
exceptional).  Contrast: over `𝔽_2[X]` and over `𝔽_p[X]` with `p ≡ 1 (mod 3)` the composite
floor is a theorem (`EM/FunctionField/CompositeFloors.lean`), and over `ℤ` it is open.  The
quadratic seeds `X² + 1`, `X² + 2` over `𝔽_5` are perpetual towers too
(`EM/FunctionField/QuadraticSeeds.lean`); the level polynomials are irreducible over `ℚ`
(`EM/FunctionField/GenericTower.lean`).
-/

namespace FunctionFieldAnalog

open Polynomial

namespace StableTower

instance instFactPrimeFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-! ## 1. The level polynomials -/

/-- `iter n = Φ₆ⁿ(X)`, `Φ₆(y) = y(y+1)`: the accumulator on the autonomous branch. -/
noncomputable def iter : ℕ → (ZMod 5)[X]
  | 0 => X
  | n + 1 => iter n * (iter n + 1)

/-- The level polynomial `g n = Φ₆ⁿ(X) + 1`: the `n`-th Euclid number on the autonomous branch. -/
noncomputable def g (n : ℕ) : (ZMod 5)[X] := iter n + 1

theorem iter_zero : iter 0 = X := rfl

theorem iter_succ (n : ℕ) : iter (n + 1) = iter n * (iter n + 1) := rfl

theorem iter_monic_natDegree (n : ℕ) : (iter n).Monic ∧ (iter n).natDegree = 2 ^ n := by
  induction n with
  | zero => exact ⟨monic_X, natDegree_X⟩
  | succ n ih =>
    obtain ⟨hm, hd⟩ := ih
    have hpos : 0 < (iter n).natDegree := by rw [hd]; positivity
    have hlt : (1 : (ZMod 5)[X]).natDegree < (iter n).natDegree := by
      rw [natDegree_one]; exact hpos
    have hm1 : (iter n + 1).Monic := by
      refine hm.add_of_left ?_
      rw [degree_one, degree_eq_natDegree hm.ne_zero]
      exact_mod_cast hpos
    refine ⟨hm.mul hm1, ?_⟩
    rw [iter_succ, hm.natDegree_mul hm1, natDegree_add_eq_left_of_natDegree_lt hlt, hd]
    ring

theorem iter_monic (n : ℕ) : (iter n).Monic := (iter_monic_natDegree n).1

theorem iter_natDegree (n : ℕ) : (iter n).natDegree = 2 ^ n := (iter_monic_natDegree n).2

theorem g_monic (n : ℕ) : (g n).Monic := by
  unfold g
  refine (iter_monic n).add_of_left ?_
  rw [degree_one, degree_eq_natDegree (iter_monic n).ne_zero, iter_natDegree]
  exact_mod_cast (by positivity : 0 < 2 ^ n)

theorem g_natDegree (n : ℕ) : (g n).natDegree = 2 ^ n := by
  unfold g
  rw [natDegree_add_eq_left_of_natDegree_lt, iter_natDegree]
  rw [natDegree_one, iter_natDegree]; positivity

/-! ## 2. The tower in the algebraic closure of `𝔽_5` -/

/-- The algebraic closure of `𝔽_5`. -/
abbrev L : Type := AlgebraicClosure (ZMod 5)

theorem five_eq_zero : (5 : L) = 0 := by
  have := CharP.cast_eq_zero L 5
  exact_mod_cast this

/-- A chosen square root in `L`. -/
noncomputable def sqrtL (x : L) : L :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq x (by norm_num : 0 < 2))

theorem sqrtL_sq (x : L) : sqrtL x ^ 2 = x :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq x (by norm_num : 0 < 2))

/-- `alpha 0 = -1`, `alpha (k+1) = 3 s + 2` where `s² = 1 + 4 alpha k`. -/
noncomputable def alpha : ℕ → L
  | 0 => -1
  | k + 1 => 3 * sqrtL (1 + 4 * alpha k) + 2

/-- The square root adjoined at level `k+1` (`s 0 := 0` is unused). -/
noncomputable def s : ℕ → L
  | 0 => 0
  | k + 1 => sqrtL (1 + 4 * alpha k)

theorem alpha_zero : alpha 0 = -1 := rfl

theorem alpha_succ (k : ℕ) : alpha (k + 1) = 3 * s (k + 1) + 2 := rfl

theorem s_succ_sq (k : ℕ) : s (k + 1) ^ 2 = 1 + 4 * alpha k := sqrtL_sq _

/-- The defining recursion of the tower: `α(k+1)² + α(k+1) = α k`. -/
theorem alpha_succ_sq_add (k : ℕ) : alpha (k + 1) ^ 2 + alpha (k + 1) = alpha k := by
  rw [alpha_succ]
  linear_combination (9 : L) * s_succ_sq k + (7 * alpha k + 3 * s (k + 1) + 3) * five_eq_zero

/-! ## 3. Exponents -/

/-- `q e = 5^(2^e)`, the cardinality of `𝔽_{5^{2^e}}`. -/
def q (e : ℕ) : ℕ := 5 ^ 2 ^ e

/-- `m e = (q e - 1) / 2`, the Euler exponent. -/
def m (e : ℕ) : ℕ := (5 ^ 2 ^ e - 1) / 2

theorem q_odd (e : ℕ) : Odd (q e) := Odd.pow (by decide)

theorem two_mul_m_add_one (e : ℕ) : 2 * m e + 1 = q e := by
  obtain ⟨t, ht⟩ := q_odd e
  unfold m; unfold q at ht ⊢
  rw [ht]; omega

theorem q_succ (e : ℕ) : q (e + 1) = q e * q e := by
  unfold q; rw [pow_succ, pow_mul, sq]

theorem m_succ (e : ℕ) : m (e + 1) = m e * (q e + 1) := by
  have h1 := two_mul_m_add_one e
  have h2 := two_mul_m_add_one (e + 1)
  rw [q_succ, ← h1] at h2
  have key : 2 * m (e + 1) = 2 * (m e * (q e + 1)) := by
    rw [← h1]; nlinarith [h2]
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) key

theorem m_pos (e : ℕ) : 0 < m e := by
  have h := two_mul_m_add_one e
  have : 5 ≤ q e := by unfold q; exact Nat.le_self_pow (by positivity) 5
  omega

/-! ## 4. Frobenius powers on `L` -/

theorem add_pow_q (e : ℕ) (x y : L) : (x + y) ^ q e = x ^ q e + y ^ q e := by
  unfold q; exact add_pow_char_pow x y 5 (2 ^ e)

theorem algebraMap_pow_q (c : ZMod 5) (e : ℕ) :
    (algebraMap (ZMod 5) L c) ^ q e = algebraMap (ZMod 5) L c := by
  unfold q; rw [← map_pow, ZMod.pow_card_pow]

theorem two_pow_q (e : ℕ) : (2 : L) ^ q e = 2 := by
  have := algebraMap_pow_q 2 e; rwa [map_ofNat] at this

theorem three_pow_q (e : ℕ) : (3 : L) ^ q e = 3 := by
  have := algebraMap_pow_q 3 e; rwa [map_ofNat] at this

theorem four_pow_q (e : ℕ) : (4 : L) ^ q e = 4 := by
  have := algebraMap_pow_q 4 e; rwa [map_ofNat] at this

/-- `s^{q} = s · u^{m}` where `s² = u`. -/
theorem s_succ_pow_q_of (k : ℕ) (hB : (1 + 4 * alpha k) ^ m k = -1) :
    s (k + 1) ^ q k = -s (k + 1) := by
  rw [← two_mul_m_add_one k, pow_succ, pow_mul, s_succ_sq, hB]; ring

/-! ## 5. The simultaneous invariant -/

/-- **The tower invariant.**  `α_k` is fixed by `x ↦ x^{q_k}`, and both `1 + 4α_k` and
`2 + 4α_k` are non-squares in `𝔽_{q_k}` (Euler symbol `-1`). -/
theorem tower_invariant (k : ℕ) :
    alpha k ^ q k = alpha k ∧ (1 + 4 * alpha k) ^ m k = -1 ∧
      (1 + (1 + 4 * alpha k)) ^ m k = -1 := by
  induction k with
  | zero =>
    have hq0 : q 0 = 5 := rfl
    have hm0 : m 0 = 2 := rfl
    rw [hq0, hm0, alpha_zero]
    refine ⟨by norm_num, ?_, ?_⟩
    · linear_combination (2 : L) * five_eq_zero
    · linear_combination five_eq_zero
  | succ k ih =>
    obtain ⟨_, hB, hC⟩ := ih
    have hs2 : s (k + 1) ^ 2 = 1 + 4 * alpha k := s_succ_sq k
    have hsq : s (k + 1) ^ q k = -s (k + 1) := s_succ_pow_q_of k hB
    have hα : alpha (k + 1) = 3 * s (k + 1) + 2 := alpha_succ k
    have hαq : alpha (k + 1) ^ q k = -3 * s (k + 1) + 2 := by
      rw [hα, add_pow_q, mul_pow, three_pow_q, two_pow_q, hsq]; ring
    refine ⟨?_, ?_, ?_⟩
    · -- fixed by `x ↦ x^{q_{k+1}}`
      rw [q_succ, pow_mul, hαq,
        show (-3 * s (k + 1) + 2 : L) = (-3) * s (k + 1) + 2 by ring, add_pow_q, mul_pow, hsq,
        two_pow_q, Odd.neg_pow (q_odd k), three_pow_q, hα]
      ring
    · -- `(1 + 4 α_{k+1})^{m_{k+1}} = -1`
      have hu : (1 + 4 * alpha (k + 1) : L) = 4 + 2 * s (k + 1) := by
        rw [hα]; linear_combination (1 + 2 * s (k + 1)) * five_eq_zero
      have hpow : (4 + 2 * s (k + 1) : L) ^ (q k + 1) = 1 + (1 + 4 * alpha k) := by
        rw [pow_succ, add_pow_q, mul_pow, four_pow_q, two_pow_q, hsq]
        linear_combination (-4 : L) * hs2 + (2 - 4 * alpha k) * five_eq_zero
      rw [hu, m_succ, mul_comm (m k), pow_mul, hpow, hC]
    · -- `(2 + 4 α_{k+1})^{m_{k+1}} = -1`
      have hu' : (1 + (1 + 4 * alpha (k + 1)) : L) = 2 * s (k + 1) := by
        rw [hα]; linear_combination (2 + 2 * s (k + 1)) * five_eq_zero
      have hpow : (2 * s (k + 1) : L) ^ (q k + 1) = 1 + 4 * alpha k := by
        rw [pow_succ, mul_pow, two_pow_q, hsq]
        linear_combination (-4 : L) * hs2 + (-(1 + 4 * alpha k)) * five_eq_zero
      rw [hu', m_succ, mul_comm (m k), pow_mul, hpow, hB]

theorem s_succ_pow_q (k : ℕ) : s (k + 1) ^ q k = -s (k + 1) :=
  s_succ_pow_q_of k (tower_invariant k).2.1

theorem alpha_succ_pow_q (k : ℕ) : alpha (k + 1) ^ q k = -3 * s (k + 1) + 2 := by
  rw [alpha_succ, add_pow_q, mul_pow, three_pow_q, two_pow_q, s_succ_pow_q]; ring

theorem s_succ_ne_zero (k : ℕ) : s (k + 1) ≠ 0 := by
  intro h
  have hB := (tower_invariant k).2.1
  rw [← s_succ_sq k, h, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_pow (m_pos k).ne'] at hB
  exact zero_ne_one (by simpa using congrArg Neg.neg hB : (0 : L) = 1)

/-! ## 6. `α_n` is a root of `g n` -/

theorem aeval_alpha_iter (k j : ℕ) (hj : j ≤ k) : aeval (alpha k) (iter j) = alpha (k - j) := by
  induction j with
  | zero => simp [iter]
  | succ j ih =>
    have hj' : j ≤ k := by omega
    rw [iter_succ, map_mul, map_add, map_one, ih hj']
    obtain ⟨t, ht⟩ : ∃ t, k - j = t + 1 := ⟨k - (j + 1), by omega⟩
    rw [ht, show k - (j + 1) = t by omega]
    linear_combination alpha_succ_sq_add t

theorem aeval_alpha_g (k : ℕ) : aeval (alpha k) (g k) = 0 := by
  rw [g, map_add, map_one, aeval_alpha_iter k k le_rfl, Nat.sub_self, alpha_zero]; ring

theorem isIntegral_alpha (k : ℕ) : IsIntegral (ZMod 5) (alpha k) :=
  ⟨g k, g_monic k, by rw [← aeval_def]; exact aeval_alpha_g k⟩

/-! ## 7. The Frobenius orbit of `α_n` has exactly `2^n` points -/

/-- Frobenius `x ↦ x^5` on `L`. -/
noncomputable abbrev φ : L →+* L := frobenius L 5

theorem φ_apply (x : L) : φ x = x ^ 5 := frobenius_def 5 x

theorem φ_iterate (i : ℕ) (x : L) : (⇑φ)^[i] x = x ^ 5 ^ i := by
  induction i generalizing x with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', ih, φ_apply, ← pow_mul, ← pow_succ]

theorem φ_comp_algebraMap : φ.comp (algebraMap (ZMod 5) L) = algebraMap (ZMod 5) L := by
  ext c
  simp only [RingHom.comp_apply, φ_apply, ← map_pow, ZMod.pow_card]

/-- Frobenius iterates of a root of an `𝔽_5`-polynomial are roots. -/
theorem φ_iterate_root {p : (ZMod 5)[X]} {x : L} (hx : aeval x p = 0) (i : ℕ) :
    aeval ((⇑φ)^[i] x) p = 0 := by
  induction i with
  | zero => simpa
  | succ i ih =>
    rw [Function.iterate_succ_apply', aeval_def, ← φ_comp_algebraMap, ← hom_eval₂, ← aeval_def,
      ih, map_zero]

theorem minimalPeriod_alpha (n : ℕ) :
    Function.minimalPeriod (⇑φ) (alpha (n + 1)) = 2 ^ (n + 1) := by
  have hper : Function.IsPeriodicPt (⇑φ) (2 ^ (n + 1)) (alpha (n + 1)) := by
    show (⇑φ)^[2 ^ (n + 1)] (alpha (n + 1)) = alpha (n + 1)
    rw [φ_iterate]; exact (tower_invariant (n + 1)).1
  have hnot : ¬ Function.IsPeriodicPt (⇑φ) (2 ^ n) (alpha (n + 1)) := by
    intro h
    have h' : (⇑φ)^[2 ^ n] (alpha (n + 1)) = alpha (n + 1) := h
    rw [φ_iterate, show (5 : ℕ) ^ 2 ^ n = q n from rfl, alpha_succ_pow_q, alpha_succ] at h'
    apply s_succ_ne_zero n
    linear_combination (-1 : L) * h' + (-(s (n + 1))) * five_eq_zero
  have hdvd : Function.minimalPeriod (⇑φ) (alpha (n + 1)) ∣ 2 ^ (n + 1) :=
    hper.minimalPeriod_dvd
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases Nat.lt_or_ge k (n + 1) with hlt | hge
  · exfalso; apply hnot
    rw [Function.isPeriodicPt_iff_minimalPeriod_dvd, hkeq]
    exact Nat.pow_dvd_pow 2 (by omega)
  · rw [hkeq]; congr 1; omega

theorem two_pow_le_natDegree_minpoly (n : ℕ) :
    2 ^ (n + 1) ≤ (minpoly (ZMod 5) (alpha (n + 1))).natDegree := by
  classical
  set P : L[X] := (minpoly (ZMod 5) (alpha (n + 1))).map (algebraMap (ZMod 5) L) with hP
  have hint := isIntegral_alpha (n + 1)
  have hP0 : P ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap (ZMod 5) L).injective).mpr (minpoly.ne_zero hint)
  have hmem : ∀ i, (⇑φ)^[i] (alpha (n + 1)) ∈ P.roots := fun i => by
    rw [mem_roots hP0, IsRoot, hP, eval_map, ← aeval_def]
    exact φ_iterate_root (minpoly.aeval _ _) i
  have hinj : Set.InjOn (fun i => (⇑φ)^[i] (alpha (n + 1)))
      (Finset.range (2 ^ (n + 1)) : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
      (by rw [minimalPeriod_alpha]; exact hi) (by rw [minimalPeriod_alpha]; exact hj)).mp hij
  calc 2 ^ (n + 1) = (Finset.range (2 ^ (n + 1))).card := (Finset.card_range _).symm
    _ = ((Finset.range (2 ^ (n + 1))).image (fun i => (⇑φ)^[i] (alpha (n + 1)))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ P.roots.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        exact Multiset.mem_toFinset.mpr (hmem i)
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' _
    _ = (minpoly (ZMod 5) (alpha (n + 1))).natDegree := natDegree_map _

/-! ## 8. Every level polynomial is irreducible over `𝔽_5` -/

/-- **Every level polynomial `g n = Φ₆ⁿ(X) + 1` is irreducible over `𝔽_5`.**  The tower over
`-1` under `y ↦ y² + y` is *stable* over `𝔽_5`: `5` is an exceptional prime. -/
theorem g_irreducible (n : ℕ) : Irreducible (g n) := by
  rcases n with _ | n
  · have : g 0 = X - C (-1 : ZMod 5) := by simp [g, iter, sub_eq_add_neg]
    rw [this]; exact irreducible_X_sub_C _
  · have hint := isIntegral_alpha (n + 1)
    have hdvd : minpoly (ZMod 5) (alpha (n + 1)) ∣ g (n + 1) := minpoly.dvd _ _ (aeval_alpha_g _)
    have hdeg : (g (n + 1)).natDegree ≤ (minpoly (ZMod 5) (alpha (n + 1))).natDegree := by
      rw [g_natDegree]; exact two_pow_le_natDegree_minpoly n
    have heq : g (n + 1) = minpoly (ZMod 5) (alpha (n + 1)) :=
      eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (g_monic _) hdvd hdeg
    rw [heq]; exact minpoly.irreducible hint

/-! ## 9. The stable-tower sequence is an `FFEMData 5` -/

/-- `towerSeq 0 = X`, `towerSeq (n+1) = g n`. -/
noncomputable def towerSeq : ℕ → (ZMod 5)[X]
  | 0 => X
  | n + 1 => g n

/-- **The function-field Euclid–Mullin sequence over `𝔽_5[X]`, seed `X`.**  Every Euclid number
is irreducible, so there is never a choice to make: this is *the* sequence, for every tie-break. -/
noncomputable def tower : FFEMData 5 where
  ffSeq := towerSeq
  ffProd := iter
  ffSeq_zero := rfl
  ffProd_zero := rfl
  ffSeq_succ := fun n => ⟨g_monic n, g_irreducible n, dvd_rfl⟩
  ffProd_succ := fun _ => rfl
  ffSeq_minimal := fun n f _ hirr hdvd => by
    have h : Associated f (g n) := hirr.associated_of_dvd (g_irreducible n) hdvd
    exact le_of_eq (natDegree_eq_of_degree_eq (degree_eq_degree_of_associated h)).symm

theorem tower_ffSeq_zero : tower.ffSeq 0 = X := rfl

theorem tower_ffSeq_succ (n : ℕ) : tower.ffSeq (n + 1) = g n := rfl

/-- The autonomous branch is perpetual: every Euclid number of the `𝔽_5` sequence is irreducible.
This is `FFPerpetualIrreducibility` (`DegreeTelescope.lean`) as a *theorem*, from stage `0`. -/
theorem tower_euclid_irreducible (n : ℕ) : Irreducible (tower.ffProd n + 1) := g_irreducible n

theorem tower_ffSeq_natDegree (n : ℕ) : (tower.ffSeq (n + 1)).natDegree = 2 ^ n :=
  g_natDegree n

end StableTower

/-! ## 10. The refutation -/

open StableTower in
/-- **The function-field Mullin conjecture is false over `𝔽_5[X]`.**  The linear irreducible
`X + 3` (i.e. `X - 2`) never appears: the sequence is `X, X + 1, g₁(X), g₂(X), …` with
`deg g_n = 2^n`, so its only linear terms are `X` and `X + 1`. -/
theorem not_ffMullinConjecture_five : ¬ FFMullinConjecture 5 := by
  intro h
  have hirr : Irreducible (X + C (3 : ZMod 5)) := by
    rw [show (X + C (3 : ZMod 5)) = X - C (-3) by simp [sub_eq_add_neg]]
    exact irreducible_X_sub_C _
  obtain ⟨n, hn⟩ := h tower (X + C 3) (monic_X_add_C 3) hirr
  rcases n with _ | _ | n
  · have h0 : (X : (ZMod 5)[X]) = X + C 3 := hn
    have := congrArg (fun p : (ZMod 5)[X] => p.coeff 0) h0
    simp at this
    exact absurd this (by decide)
  · have h1 : (X + 1 : (ZMod 5)[X]) = X + C 3 := hn
    have := congrArg (fun p : (ZMod 5)[X] => p.coeff 0) h1
    simp at this
    exact absurd this (by decide)
  · have h2 : g (n + 1) = X + C 3 := hn
    have hd := congrArg natDegree h2
    rw [g_natDegree, natDegree_X_add_C] at hd
    have : 2 ≤ 2 ^ (n + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end FunctionFieldAnalog
