import EM.FunctionField.StableTower
import EM.FunctionField.FactorTree

/-!
# Quadratic seeds over `𝔽_5`: the stable tower is not a feature of the seed `X` alone

`StableTower.lean` shows that the greedy sequence over `𝔽_5[X]` from the seed `X` is a
perpetually irreducible Sylvester tower.  There the Capelli seed condition is automatic because
`X` is the generic point.  This file shows the same for the **quadratic seeds `X² + 1` and
`X² + 2`**: for `c ∈ {1, 2}` every polynomial `g_n(X² + c)` (`g_n = Φ₆ⁿ + 1` the level
polynomial) is irreducible over `𝔽_5` (`g_comp_irreducible`), hence every valid factor
selection from the seed `X² + c` follows the tower and every Euclid polynomial along it is
irreducible (`quad_seed_perpetual`); no linear irreducible is ever selected
(`quad_seed_sel_natDegree`).

## The criterion, and why `c ∈ {1, 2}`

Let `α_n` be a root of `g_n` and `β² = α_n − c`.  Then `β` is a root of `g_n(X² + c)`, and the
Frobenius orbit of `β` has `2^{n+1}` points iff `α_n − c` is a non-square in `𝔽_5(α_n)`.  The
descent of `StableTower` gives `(α_{k+1} − c)^{q_k + 1} = Φ₆(c) − α_k`, so the Euler symbol
of `α_k − c` at level `k` equals that of `α_{k−1} − Φ₆(c)` at level `k − 1` (the exponents
`m_e = (5^{2^e} − 1)/2` are even, so the sign `−1` is invisible), and unwinding,
`χ_n(α_n − c) = χ_0(Φ₆ⁿ(c) + 1) = (g_n(c))^2`.  This is the norm criterion
`N(α_n − c) = g_n(c)` made elementary.  The seed `X² + c` therefore gives a perpetual tower iff
the `Φ₆`-orbit of `c` in `𝔽_5` stays inside `{1, 2}`, the set of residues whose successor is a
non-square: exactly `c ∈ {1, 2}` (the two-cycle `1 ↦ 2 ↦ 1`).  For `c = 0, 3, 4` the very first
Euclid polynomial `X² + c + 1` is reducible.

Since any quadratic `X² + bX + c'` is affinely conjugate to some `X² + c`, ten of the twenty-five
monic quadratics over `𝔽_5` are perpetual seeds.  For seeds of degree `≥ 3` the Capelli condition
is a value-set condition on `P(X) − α_k`, no longer a norm, and heuristically breaks within a few
levels.  The failing seeds over `𝔽_5` are the small structured ones.

See `docs/analysis/logic_routes_2026-09-01.md` §14.
-/

namespace FunctionFieldAnalog

namespace QuadraticSeeds

open Polynomial StableTower

/-! ## 1. Exponent parity -/

theorem q_mod_four (e : ℕ) : q e % 4 = 1 := by
  unfold q; rw [Nat.pow_mod]; simp

theorem m_even (e : ℕ) : Even (m e) := by
  have h := two_mul_m_add_one e
  have h4 := q_mod_four e
  rw [Nat.even_iff]; omega

/-! ## 2. The quadratic-seed invariant -/

/-- `(α_{k+1} − c)^{q_k + 1} = Φ₆(c) − α_k` for every constant `c` fixed by `x ↦ x^{q_k}`. -/
theorem alpha_succ_sub_pow (k : ℕ) (c : L) (hc : c ^ q k = c) :
    (alpha (k + 1) - c) ^ (q k + 1) = (c ^ 2 + c) - alpha k := by
  have hs2 := s_succ_sq k
  have hsq := s_succ_pow_q k
  have h : alpha (k + 1) - c = (2 + -c) + 3 * s (k + 1) := by rw [alpha_succ]; ring
  rw [h, pow_succ, add_pow_q, mul_pow, three_pow_q, hsq, add_pow_q, two_pow_q,
    Odd.neg_pow (q_odd k), hc]
  linear_combination (-9 : L) * hs2 + (-(c + 1 + 7 * alpha k)) * five_eq_zero

/-- **The invariant**: at every level, `α_k − 1` and `α_k − 2` are non-squares in `𝔽_{q_k}`. -/
theorem quad_invariant (k : ℕ) : (alpha k - 1) ^ m k = -1 ∧ (alpha k - 2) ^ m k = -1 := by
  induction k with
  | zero =>
    have hm0 : m 0 = 2 := rfl
    rw [alpha_zero, hm0]
    exact ⟨by linear_combination five_eq_zero, by linear_combination (2 : L) * five_eq_zero⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor
    · rw [m_succ, mul_comm (m k), pow_mul, alpha_succ_sub_pow k 1 (one_pow _),
        show ((1 : L) ^ 2 + 1 - alpha k) = -(alpha k - 2) by ring, Even.neg_pow (m_even k), h2]
    · rw [m_succ, mul_comm (m k), pow_mul, alpha_succ_sub_pow k 2 (two_pow_q k),
        show ((2 : L) ^ 2 + 2 - alpha k) = -(alpha k - 1) by linear_combination five_eq_zero,
        Even.neg_pow (m_even k), h1]

/-! ## 3. The Frobenius-orbit lemma, in general form -/

theorem two_ne_zero_L : (2 : L) ≠ 0 := by
  intro h
  have h5 := five_eq_zero
  have : (1 : L) = 0 := by linear_combination (-2 : L) * h + h5
  exact one_ne_zero this

/-- If `β^{q_{N+1}} = β`, `β^{q_N} = −β` and `β ≠ 0`, the Frobenius orbit of `β` has exactly
`2^{N+1}` points, all roots of its minimal polynomial. -/
theorem two_pow_le_natDegree_minpoly_of_pow {β : L} (N : ℕ) (hfix : β ^ q (N + 1) = β)
    (hneg : β ^ q N = -β) (hβ : β ≠ 0) (hint : IsIntegral (ZMod 5) β) :
    2 ^ (N + 1) ≤ (minpoly (ZMod 5) β).natDegree := by
  classical
  have hmin : Function.minimalPeriod (⇑φ) β = 2 ^ (N + 1) := by
    have hper : Function.IsPeriodicPt (⇑φ) (2 ^ (N + 1)) β := by
      show (⇑φ)^[2 ^ (N + 1)] β = β
      rw [φ_iterate]; exact hfix
    have hnot : ¬ Function.IsPeriodicPt (⇑φ) (2 ^ N) β := by
      intro h
      have h' : (⇑φ)^[2 ^ N] β = β := h
      rw [φ_iterate, show (5 : ℕ) ^ 2 ^ N = q N from rfl, hneg] at h'
      apply hβ
      have : (2 : L) * β = 0 := by linear_combination -h'
      exact (mul_eq_zero.mp this).resolve_left two_ne_zero_L
    have hdvd : Function.minimalPeriod (⇑φ) β ∣ 2 ^ (N + 1) := hper.minimalPeriod_dvd
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rcases Nat.lt_or_ge k (N + 1) with hlt | hge
    · exfalso; apply hnot
      rw [Function.isPeriodicPt_iff_minimalPeriod_dvd, hkeq]
      exact Nat.pow_dvd_pow 2 (by omega)
    · rw [hkeq]; congr 1; omega
  set P : L[X] := (minpoly (ZMod 5) β).map (algebraMap (ZMod 5) L) with hP
  have hP0 : P ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap (ZMod 5) L).injective).mpr (minpoly.ne_zero hint)
  have hmem : ∀ i, (⇑φ)^[i] β ∈ P.roots := fun i => by
    rw [mem_roots hP0, IsRoot, hP, eval_map, ← aeval_def]
    exact φ_iterate_root (minpoly.aeval _ _) i
  have hinj : Set.InjOn (fun i => (⇑φ)^[i] β) (Finset.range (2 ^ (N + 1)) : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
      (by rw [hmin]; exact hi) (by rw [hmin]; exact hj)).mp hij
  calc 2 ^ (N + 1) = (Finset.range (2 ^ (N + 1))).card := (Finset.card_range _).symm
    _ = ((Finset.range (2 ^ (N + 1))).image (fun i => (⇑φ)^[i] β)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ P.roots.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        exact Multiset.mem_toFinset.mpr (hmem i)
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' _
    _ = (minpoly (ZMod 5) β).natDegree := natDegree_map _

/-! ## 4. `g_n(X² + c)` is irreducible for `c ∈ {1, 2}` -/

/-- The quadratic seed `X² + c`. -/
noncomputable abbrev quadSeed (c : ZMod 5) : (ZMod 5)[X] := X ^ 2 + C c

theorem quadSeed_monic (c : ZMod 5) : (quadSeed c).Monic := monic_X_pow_add_C c two_ne_zero

theorem quadSeed_natDegree (c : ZMod 5) : (quadSeed c).natDegree = 2 := natDegree_X_pow_add_C

theorem g_comp_monic (c : ZMod 5) (n : ℕ) : ((g n).comp (quadSeed c)).Monic :=
  (g_monic n).comp (quadSeed_monic c) (by rw [quadSeed_natDegree]; norm_num)

theorem g_comp_natDegree (c : ZMod 5) (n : ℕ) :
    ((g n).comp (quadSeed c)).natDegree = 2 ^ (n + 1) := by
  rw [natDegree_comp, g_natDegree, quadSeed_natDegree]; ring

/-- The Euler symbol of `α_n − c` for `c ∈ {1, 2}`, as an element of `L`. -/
theorem alpha_sub_pow_m {c : ZMod 5} (hc : c = 1 ∨ c = 2) (n : ℕ) :
    (alpha n - algebraMap (ZMod 5) L c) ^ m n = -1 := by
  rcases hc with rfl | rfl
  · rw [map_one]; exact (quad_invariant n).1
  · rw [map_ofNat]; exact (quad_invariant n).2

/-- **Every `g_n(X² + c)`, `c ∈ {1, 2}`, is irreducible over `𝔽_5`.** -/
theorem g_comp_irreducible {c : ZMod 5} (hc : c = 1 ∨ c = 2) (n : ℕ) :
    Irreducible ((g n).comp (quadSeed c)) := by
  set cL : L := algebraMap (ZMod 5) L c with hcL
  set β : L := sqrtL (alpha n - cL) with hβdef
  have hβ2 : β ^ 2 = alpha n - cL := sqrtL_sq _
  have hE : (alpha n - cL) ^ m n = -1 := alpha_sub_pow_m hc n
  -- β is a root
  have hroot : aeval β ((g n).comp (quadSeed c)) = 0 := by
    rw [aeval_comp]
    have : aeval β (quadSeed c) = alpha n := by
      simp only [quadSeed, map_add, map_pow, aeval_X, aeval_C, hβ2, hcL]; ring
    rw [this]; exact aeval_alpha_g n
  have hint : IsIntegral (ZMod 5) β :=
    ⟨(g n).comp (quadSeed c), g_comp_monic c n, by rw [← aeval_def]; exact hroot⟩
  -- Frobenius data
  have hneg : β ^ q n = -β := by
    rw [← two_mul_m_add_one n, pow_succ, pow_mul, hβ2, hE]; ring
  have hfix : β ^ q (n + 1) = β := by
    rw [q_succ, pow_mul, hneg, Odd.neg_pow (q_odd n), hneg, neg_neg]
  have hβ : β ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hβ2
    rw [← hβ2, zero_pow (m_pos n).ne'] at hE
    exact one_ne_zero (by simpa using congrArg Neg.neg hE : (1 : L) = 0)
  -- degree comparison
  have hdvd : minpoly (ZMod 5) β ∣ (g n).comp (quadSeed c) := minpoly.dvd _ _ hroot
  have hdeg : ((g n).comp (quadSeed c)).natDegree ≤ (minpoly (ZMod 5) β).natDegree := by
    rw [g_comp_natDegree]; exact two_pow_le_natDegree_minpoly_of_pow n hfix hneg hβ hint
  have heq : (g n).comp (quadSeed c) = minpoly (ZMod 5) β :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (g_comp_monic c n) hdvd hdeg
  rw [heq]; exact minpoly.irreducible hint

/-! ## 5. The seeded greedy sequence follows the tower -/

theorem iter_comp_add_one (c : ZMod 5) (n : ℕ) :
    (iter n).comp (quadSeed c) + 1 = (g n).comp (quadSeed c) := by
  simp [g, add_comp, one_comp]

/-- **Perpetual irreducibility from a quadratic seed.**  For `c ∈ {1, 2}` and any valid factor
selection `σ` from the seed `X² + c` (there is only one: no Euclid polynomial ever has two
factors), the accumulator is `Φ₆ⁿ(X² + c)` and every Euclid polynomial is irreducible. -/
theorem quad_seed_perpetual {c : ZMod 5} (hc : c = 1 ∨ c = 2) (σ : FFMixedSelection 5)
    (hσ : FFMixedSelectionValid 5 (quadSeed c) σ) (n : ℕ) :
    ffMixedWalkProd 5 (quadSeed c) σ n = (iter n).comp (quadSeed c) ∧
      Irreducible (ffMixedWalkProd 5 (quadSeed c) σ n + 1) := by
  induction n with
  | zero =>
    refine ⟨by simp [ffMixedWalkProd, iter], ?_⟩
    have h := g_comp_irreducible hc 0
    rwa [← iter_comp_add_one, iter_zero, X_comp] at h
  | succ n ih =>
    obtain ⟨hacc, hirr⟩ := ih
    obtain ⟨hm, hi, hd⟩ := hσ.2.2 n
    have hEm : (ffMixedWalkProd 5 (quadSeed c) σ n + 1).Monic := by
      rw [hacc, iter_comp_add_one]; exact g_comp_monic c n
    have hsel : σ.sel n = ffMixedWalkProd 5 (quadSeed c) σ n + 1 :=
      eq_of_monic_of_associated hm hEm (hi.associated_of_dvd hirr hd)
    have hacc' : ffMixedWalkProd 5 (quadSeed c) σ (n + 1) = (iter (n + 1)).comp (quadSeed c) := by
      rw [ffMixedWalkProd, hsel, hacc, iter_succ, mul_comp, add_comp, one_comp]
    refine ⟨hacc', ?_⟩
    rw [hacc', iter_comp_add_one]
    exact g_comp_irreducible hc (n + 1)

/-- Every selected factor from the seed `X² + c` has degree `2^{n+1}`; in particular no linear
irreducible is ever selected, so the seeded sequence misses `X, X+1, …, X+4`. -/
theorem quad_seed_sel_natDegree {c : ZMod 5} (hc : c = 1 ∨ c = 2) (σ : FFMixedSelection 5)
    (hσ : FFMixedSelectionValid 5 (quadSeed c) σ) (n : ℕ) :
    (σ.sel n).natDegree = 2 ^ (n + 1) := by
  obtain ⟨hacc, hirr⟩ := quad_seed_perpetual hc σ hσ n
  obtain ⟨hm, hi, hd⟩ := hσ.2.2 n
  have hEm : (ffMixedWalkProd 5 (quadSeed c) σ n + 1).Monic := by
    rw [hacc, iter_comp_add_one]; exact g_comp_monic c n
  rw [eq_of_monic_of_associated hm hEm (hi.associated_of_dvd hirr hd), hacc, iter_comp_add_one,
    g_comp_natDegree]

end QuadraticSeeds

end FunctionFieldAnalog
