import EM.FunctionField.TowerClassification
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# The stability criterion for odd `p`: the critical orbit decides

`TowerClassification.lean` reduces "is the function-field Mullin conjecture over `𝔽_p` the
dichotomy, or is it false" to the stability of the tower `T k = g^k(Y) + 1`, `g = Y² + Y`.
This file decides stability for odd `p` by the classical route: a root `α` of `T (k+1)` lies
over a root `θ = g(α)` of `T k`, by a quadratic equation of discriminant `1 + 4θ`, and
`1 + 4θ` is a square in `𝔽_p(θ)` iff its norm to `𝔽_p` is a square. The norm is
`(-4)^{deg} · T k (-1/4)`, and `-1/4 = g(-1/2)` is the critical value of `g`.

## Main results

* `minimalPeriod_eq_natDegree` — a root of an irreducible polynomial of degree `m` over `𝔽_p`
  has Frobenius period exactly `m`.
* `prod_sub_conj` — the norm: `∏_{i<m} (c − β^{p^i}) = f(c)` for `f` monic irreducible with
  root `β`, `c ∈ 𝔽_p`.
* `level_succ_irreducible_iff` — if `T k` is irreducible, then `T (k+1)` is irreducible iff
  `(-4)^{2^k} · T k (-1/4)` is not a square in `𝔽_p`.
* `stable_iff` — `p` is stable iff none of these elements is a square.

With `TowerClassification.ffMullinConjecture_iff_not_stable_and_dichotomy`: for odd `p`, if
some `(-4)^{2^k} · (g^k(-1/4) + 1)` is a square mod `p`, the conjecture over `𝔽_p` is
equivalent to the dichotomy; if none is, the conjecture over `𝔽_p` is false.
The values `g^k(-1/4)` are the orbit of the critical value in the finite set `𝔽_p`, so the
condition is eventually periodic in `k`.
-/

namespace FunctionFieldAnalog

namespace StabilityCriterion

open Polynomial FrobeniusOrbit TowerClassification

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ## 1. Frobenius powers as ring homomorphisms -/

/-- The `m`-th power of Frobenius on `𝔽̄_p`. -/
noncomputable def Φ (p : ℕ) [Fact (Nat.Prime p)] (m : ℕ) : Lp p →+* Lp p := (φ p) ^ m

theorem Φ_apply (m : ℕ) (x : Lp p) : Φ p m x = x ^ p ^ m := by
  rw [Φ, RingHom.coe_pow, φ_iterate]

theorem Φ_algebraMap (m : ℕ) (z : ZMod p) :
    Φ p m (algebraMap (ZMod p) (Lp p) z) = algebraMap (ZMod p) (Lp p) z := by
  rw [Φ_apply, ← map_pow]
  congr 1
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_mul, ih, ZMod.pow_card]

theorem Φ_aeval (m : ℕ) (f : (ZMod p)[X]) (x : Lp p) :
    Φ p m (aeval x f) = aeval (Φ p m x) f := by
  rw [Φ, RingHom.coe_pow]
  exact (aeval_iterate p f x m).symm

/-! ## 2. Period and norm of a root of an irreducible polynomial -/

theorem natDegree_dvd_of_fixed {f : (ZMod p)[X]} (hf : Irreducible f) {β : Lp p}
    (hβ : aeval β f = 0) {e : ℕ} (he : β ^ p ^ e = β) : f.natDegree ∣ e := by
  have hdvd : f ∣ X ^ p ^ e - X :=
    FibreRule.dvd_of_aeval_eq_zero p hf hβ (by simp [he])
  apply hf.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
  rwa [Nat.card_zmod]

/-- A root of an irreducible polynomial of degree `m` has Frobenius period exactly `m`. -/
theorem minimalPeriod_eq_natDegree {f : (ZMod p)[X]} (hf : Irreducible f) {β : Lp p}
    (hβ : aeval β f = 0) : Function.minimalPeriod (⇑(φ p)) β = f.natDegree := by
  have h1 := (isPeriodicPt_natDegree p hf hβ).minimalPeriod_dvd
  have h2 : f.natDegree ∣ Function.minimalPeriod (⇑(φ p)) β := by
    apply natDegree_dvd_of_fixed hf hβ
    rw [← φ_iterate]
    exact Function.isPeriodicPt_minimalPeriod _ _
  exact Nat.dvd_antisymm h1 h2

/-- **The norm.** For `f` monic irreducible of degree `m` with root `β` and `c ∈ 𝔽_p`,
    `∏_{i<m} (c − β^{p^i}) = f(c)`. -/
theorem prod_sub_conj {f : (ZMod p)[X]} (hfm : f.Monic) (hf : Irreducible f) {β : Lp p}
    (hβ : aeval β f = 0) (c : ZMod p) :
    ∏ i ∈ Finset.range f.natDegree, (algebraMap (ZMod p) (Lp p) c - β ^ p ^ i) =
      algebraMap (ZMod p) (Lp p) (eval c f) := by
  classical
  set P : (Lp p)[X] := f.map (algebraMap (ZMod p) (Lp p)) with hP
  have hPm : P.Monic := hfm.map _
  have hPdeg : P.natDegree = f.natDegree := natDegree_map _
  have hinj : ∀ i ∈ Finset.range f.natDegree, ∀ j ∈ Finset.range f.natDegree,
      β ^ p ^ i = β ^ p ^ j → i = j := by
    intro i hi j hj hij
    rw [Finset.mem_range, ← minimalPeriod_eq_natDegree hf hβ] at hi hj
    rw [← φ_iterate, ← φ_iterate] at hij
    exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hi hj).mp hij
  set O := (Finset.range f.natDegree).image (fun i => β ^ p ^ i) with hO
  have hOcard : O.card = f.natDegree := by
    rw [hO, Finset.card_image_of_injOn (fun i hi j hj h => hinj i hi j hj h), Finset.card_range]
  have hOroots : O.val ≤ P.roots := by
    rw [Multiset.le_iff_subset O.nodup]
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_val.mp hx)
    rw [mem_roots hPm.ne_zero, IsRoot.def, hP, eval_map, ← aeval_def, ← φ_iterate]
    exact aeval_iterate_root p hβ i
  have hroots : O.val = P.roots := by
    refine Multiset.eq_of_le_of_card_le hOroots ?_
    calc Multiset.card P.roots ≤ P.natDegree := card_roots' _
      _ = f.natDegree := hPdeg
      _ = Multiset.card O.val := hOcard.symm
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPm
    (by rw [← hroots, hPdeg]; exact hOcard)
  have hev := congrArg (eval (algebraMap (ZMod p) (Lp p) c)) hprod
  rw [← hroots, eval_multiset_prod, Multiset.map_map] at hev
  have hPc : eval (algebraMap (ZMod p) (Lp p) c) P = algebraMap (ZMod p) (Lp p) (eval c f) := by
    rw [hP, eval_map, eval₂_at_apply]
  rw [hPc] at hev
  rw [← hev]
  have h1 : ∏ x ∈ O, (algebraMap (ZMod p) (Lp p) c - x) =
      ∏ i ∈ Finset.range f.natDegree, (algebraMap (ZMod p) (Lp p) c - β ^ p ^ i) := by
    rw [hO, Finset.prod_image hinj]
  rw [← h1, Finset.prod_eq_multiset_prod]
  congr 1
  apply Multiset.map_congr rfl
  intro x _
  simp

/-! ## 3. The tower -/

theorem iter_monic_natDegree (k : ℕ) : (iter p k).Monic ∧ (iter p k).natDegree = 2 ^ k := by
  induction k with
  | zero => exact ⟨monic_X, natDegree_X⟩
  | succ k ih =>
    obtain ⟨hm, hd⟩ := ih
    have hpos : 0 < (iter p k).natDegree := by rw [hd]; positivity
    have hlt : (1 : (ZMod p)[X]).natDegree < (iter p k).natDegree := by
      rw [natDegree_one]; exact hpos
    have hm1 : (iter p k + 1).Monic := by
      refine hm.add_of_left ?_
      rw [degree_one, degree_eq_natDegree hm.ne_zero]
      exact_mod_cast hpos
    refine ⟨hm.mul hm1, ?_⟩
    show (iter p k * (iter p k + 1)).natDegree = _
    rw [hm.natDegree_mul hm1, natDegree_add_eq_left_of_natDegree_lt hlt, hd]
    ring

theorem level_monic (k : ℕ) : (level p k).Monic := by
  unfold level
  refine (iter_monic_natDegree k).1.add_of_left ?_
  rw [degree_one, degree_eq_natDegree (iter_monic_natDegree k).1.ne_zero,
    (iter_monic_natDegree k).2]
  exact_mod_cast (by positivity : 0 < 2 ^ k)

theorem level_natDegree (k : ℕ) : (level p k).natDegree = 2 ^ k := by
  unfold level
  rw [natDegree_add_eq_left_of_natDegree_lt, (iter_monic_natDegree k).2]
  rw [natDegree_one, (iter_monic_natDegree k).2]; positivity

theorem iter_succ_comp (k : ℕ) : iter p (k + 1) = (iter p k).comp (X * (X + 1)) := by
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    show iter p (k + 1) * (iter p (k + 1) + 1) = (iter p k * (iter p k + 1)).comp _
    rw [ih]; simp [mul_comp, add_comp]

theorem level_succ_comp (k : ℕ) : level p (k + 1) = (level p k).comp (X * (X + 1)) := by
  unfold level
  rw [iter_succ_comp]; simp [add_comp]

theorem level_zero_irreducible : Irreducible (level p 0) := by
  have : level p 0 = X + C 1 := by simp [level, iter]
  rw [this]
  exact irreducible_of_degree_eq_one (degree_X_add_C 1)

/-! ## 4. One step of the tower -/

theorem geom (r m : ℕ) : r * ∑ i ∈ Finset.range m, (r + 1) ^ i + 1 = (r + 1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, add_right_comm, ih]
    ring

theorem four_ne_zero (hp2 : p ≠ 2) : (4 : ZMod p) ≠ 0 := by
  intro h
  have h4 : ((4 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h4
  have hp : p.Prime := Fact.out
  have : p ∣ 2 := by
    rcases (hp.dvd_mul (m := 2) (n := 2)).mp (by simpa using h4) with h | h <;> exact h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)

/-- The element of `𝔽_p` whose square class decides level `k + 1`. -/
noncomputable def disc (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ) : ZMod p :=
  (-4) ^ 2 ^ k * eval (-(4 : ZMod p)⁻¹) (level p k)

/-- **The Frobenius of the square root of the discriminant.** For `α` a root of `T (k+1)`,
    with `T k` irreducible, `(2α + 1)^{p^{2^k}} = disc^{(p-1)/2} · (2α + 1)`. -/
theorem frob_delta (hp2 : p ≠ 2) (k : ℕ) (hk : Irreducible (level p k)) {α : Lp p}
    (hα : aeval α (level p (k + 1)) = 0) :
    Φ p (2 ^ k) (2 * α + 1) =
      algebraMap (ZMod p) (Lp p) (disc p k ^ (p / 2)) * (2 * α + 1) ∧
    ((2 * α + 1 = 0) → disc p k = 0) ∧ (disc p k = 0 → 2 * α + 1 = 0) := by
  set a := algebraMap (ZMod p) (Lp p) with ha
  set m := 2 ^ k with hm
  set S := ∑ i ∈ Finset.range m, p ^ i with hS
  set θ : Lp p := aeval α (X * (X + 1) : (ZMod p)[X]) with hθ
  have hθval : θ = α * (α + 1) := by simp [hθ]
  have hθroot : aeval θ (level p k) = 0 := by
    rw [hθ, ← aeval_comp, ← level_succ_comp]; exact hα
  have h4 : (4 : ZMod p) ≠ 0 := four_ne_zero hp2
  have ha4 : a (-4) * a (-(4 : ZMod p)⁻¹) = 1 := by
    rw [← map_mul, neg_mul_neg, mul_inv_cancel₀ h4, map_one]
  have ham4 : a (-4) = -4 := by rw [map_neg, map_ofNat]
  -- the norm of the discriminant
  have hu : ∀ i, (1 + 4 * θ) ^ p ^ i = a (-4) * (a (-(4 : ZMod p)⁻¹) - θ ^ p ^ i) := by
    intro i
    rw [← Φ_apply, map_add, map_mul, map_one, map_ofNat, Φ_apply, mul_sub, ha4, ham4]
    ring
  have hN : (1 + 4 * θ) ^ S = a (disc p k) := by
    rw [hS, ← Finset.prod_pow_eq_pow_sum]
    simp only [hu]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, hm, ← level_natDegree (p := p) k,
      prod_sub_conj (level_monic k) hk hθroot, level_natDegree, disc, map_mul, map_pow]
  have hpodd : 2 * (p / 2) + 1 = p := by
    have hp : p.Prime := Fact.out
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hexp : p ^ m = 2 * (p / 2 * S) + 1 := by
    have := geom (2 * (p / 2)) m
    rw [hpodd] at this
    rw [← this, hS]; ring
  have hsq : (2 * α + 1) ^ 2 = 1 + 4 * θ := by rw [hθval]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [Φ_apply, hexp, pow_succ, pow_mul, hsq, mul_comm (p / 2) S, pow_mul, hN, ← map_pow]
  · intro h0
    have : a (disc p k) = 0 := by
      rw [← hN, ← hsq, h0]
      have hSpos : S ≠ 0 := by
        rw [hS]
        have : 0 < ∑ i ∈ Finset.range m, p ^ i :=
          Finset.sum_pos (fun i _ => pow_pos (Fact.out : p.Prime).pos i)
            ⟨0, Finset.mem_range.mpr (by rw [hm]; positivity)⟩
        omega
      simp [hSpos]
    exact (map_eq_zero a).mp this
  · intro h0
    have : (1 + 4 * θ) ^ S = 0 := by rw [hN, h0, map_zero]
    have hu0 : 1 + 4 * θ = 0 := (pow_eq_zero_iff (fun hS0 => by
      rw [hS0, pow_zero] at this; exact one_ne_zero this)).mp this
    rw [← hsq] at hu0
    exact (pow_eq_zero_iff two_ne_zero).mp hu0

/-! ## 5. The criterion -/

theorem two_ne_zero_L (hp2 : p ≠ 2) : (2 : Lp p) ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := fun h => four_ne_zero hp2 (by linear_combination (2 : ZMod p) * h)
  intro h
  apply h2
  apply (map_eq_zero (algebraMap (ZMod p) (Lp p))).mp
  rw [map_ofNat]; exact h

theorem half_ne_zero : p / 2 ≠ 0 := by
  have := (Fact.out : p.Prime).two_le
  omega

/-- A root `α` of `T (k+1)` lies in `𝔽_{p^{2^k}}` iff the discriminant element is a square. -/
theorem fixed_iff_isSquare (hp2 : p ≠ 2) (k : ℕ) (hk : Irreducible (level p k)) {α : Lp p}
    (hα : aeval α (level p (k + 1)) = 0) :
    Φ p (2 ^ k) α = α ↔ IsSquare (disc p k) := by
  obtain ⟨hδ, h0, h0'⟩ := frob_delta hp2 k hk hα
  have h2 := two_ne_zero_L hp2
  have hΦδ : Φ p (2 ^ k) (2 * α + 1) = 2 * Φ p (2 ^ k) α + 1 := by
    rw [map_add, map_mul, map_ofNat, map_one]
  constructor
  · intro hfix
    rw [hΦδ, hfix] at hδ
    by_cases hd : 2 * α + 1 = 0
    · rw [h0 hd]; exact ⟨0, by simp⟩
    · have h1 : algebraMap (ZMod p) (Lp p) (disc p k ^ (p / 2)) = 1 := by
        have : (algebraMap (ZMod p) (Lp p) (disc p k ^ (p / 2)) - 1) * (2 * α + 1) = 0 := by
          linear_combination -hδ
        rcases mul_eq_zero.mp this with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hd
      have h1' : disc p k ^ (p / 2) = 1 :=
        (algebraMap (ZMod p) (Lp p)).injective (by rw [h1, map_one])
      have hne : disc p k ≠ 0 := by
        intro h
        rw [h, zero_pow half_ne_zero] at h1'
        exact zero_ne_one h1'
      exact (ZMod.euler_criterion p hne).mpr h1'
  · intro hsq
    by_cases hd0 : disc p k = 0
    · have hz := h0' hd0
      have : 2 * Φ p (2 ^ k) α + 1 = 2 * α + 1 := by rw [← hΦδ, hz, map_zero]
      exact mul_left_cancel₀ h2 (add_right_cancel this)
    · have h1 := (ZMod.euler_criterion p hd0).mp hsq
      rw [h1, map_one, one_mul, hΦδ] at hδ
      exact mul_left_cancel₀ h2 (add_right_cancel hδ)

/-- **One step of the tower.** If `T k` is irreducible over `𝔽_p`, `p` odd, then `T (k+1)` is
    irreducible iff `(-4)^{2^k} · T k (-1/4)` is not a square in `𝔽_p`. -/
theorem level_succ_irreducible_iff (hp2 : p ≠ 2) (k : ℕ) (hk : Irreducible (level p k)) :
    Irreducible (level p (k + 1)) ↔ ¬ IsSquare (disc p k) := by
  have hdeg : 0 < (level p (k + 1)).natDegree := by rw [level_natDegree]; positivity
  obtain ⟨α, hα⟩ := exists_root_of_natDegree_pos p hdeg
  have hmpos : 0 < 2 ^ k := by positivity
  rw [← fixed_iff_isSquare hp2 k hk hα]
  constructor
  · intro hirr hfix
    have h := natDegree_dvd_of_fixed hirr hα (by rw [← Φ_apply]; exact hfix)
    rw [level_natDegree] at h
    have := Nat.le_of_dvd hmpos h
    rw [pow_succ] at this
    omega
  · intro hnf
    obtain ⟨hδ, h0, h0'⟩ := frob_delta hp2 k hk hα
    have h2 := two_ne_zero_L hp2
    have hns : ¬ IsSquare (disc p k) := fun h => hnf ((fixed_iff_isSquare hp2 k hk hα).mpr h)
    have hdne : disc p k ≠ 0 := fun h => hns ⟨0, by simp [h]⟩
    have hε : algebraMap (ZMod p) (Lp p) (disc p k ^ (p / 2)) *
        algebraMap (ZMod p) (Lp p) (disc p k ^ (p / 2)) = 1 := by
      have hp : p.Prime := Fact.out
      have hodd : p / 2 + p / 2 = p - 1 := by
        rcases hp.eq_two_or_odd with h | h
        · exact absurd h hp2
        · omega
      rw [← map_mul, ← pow_add, hodd, ZMod.pow_card_sub_one_eq_one hdne, map_one]
    have hΦδ : ∀ x : Lp p, Φ p (2 ^ k) (2 * x + 1) = 2 * Φ p (2 ^ k) x + 1 := fun x => by
      rw [map_add, map_mul, map_ofNat, map_one]
    have hΦΦ : Φ p (2 ^ k) (Φ p (2 ^ k) α) = α := by
      have h1 : Φ p (2 ^ k) (Φ p (2 ^ k) (2 * α + 1)) = 2 * α + 1 := by
        rw [hδ, map_mul, Φ_algebraMap, hδ, ← mul_assoc, hε, one_mul]
      rw [hΦδ, hΦδ] at h1
      exact mul_left_cancel₀ h2 (add_right_cancel h1)
    have hiter : ∀ (m : ℕ) (x : Lp p), (⇑(φ p))^[m] x = Φ p m x := fun m x => by
      rw [Φ, RingHom.coe_pow]
    have hper : Function.IsPeriodicPt (⇑(φ p)) (2 ^ k + 2 ^ k) α := by
      show (⇑(φ p))^[2 ^ k + 2 ^ k] α = α
      rw [Function.iterate_add_apply, hiter, hiter, hΦΦ]
    set e := Function.minimalPeriod (⇑(φ p)) α with he
    have he2 : e ∣ 2 ^ k + 2 ^ k := hper.minimalPeriod_dvd
    have hefix : Φ p e α = α := by
      rw [← hiter]; exact Function.isPeriodicPt_minimalPeriod _ _
    have hθroot : aeval (aeval α (X * (X + 1) : (ZMod p)[X])) (level p k) = 0 := by
      rw [← aeval_comp, ← level_succ_comp]; exact hα
    have hme : 2 ^ k ∣ e := by
      have := natDegree_dvd_of_fixed hk hθroot (e := e) (by rw [← Φ_apply, Φ_aeval, hefix])
      rwa [level_natDegree] at this
    obtain ⟨t, ht⟩ := hme
    have ht2 : t ∣ 2 := by
      rw [ht, ← mul_two] at he2
      exact Nat.dvd_of_mul_dvd_mul_left hmpos he2
    have hedeg : e = 2 ^ (k + 1) := by
      rcases (Nat.dvd_prime Nat.prime_two).mp ht2 with h1 | h1
      · exfalso
        apply hnf
        rw [h1, mul_one] at ht
        rw [← ht]; exact hefix
      · rw [ht, h1, pow_succ]
    exact irreducible_of_natDegree_eq_minimalPeriod p (level_monic (k + 1)) hα
      (by rw [level_natDegree, ← he, hedeg])

/-- **The stability criterion.** For odd `p`, the tower is stable iff no discriminant element
    is a square. -/
theorem stable_iff (hp2 : p ≠ 2) : Stable p ↔ ∀ k, ¬ IsSquare (disc p k) := by
  constructor
  · intro h k
    exact (level_succ_irreducible_iff hp2 k (h k)).mp (h (k + 1))
  · intro h k
    induction k with
    | zero => exact level_zero_irreducible
    | succ k ih => exact (level_succ_irreducible_iff hp2 k ih).mpr (h k)

/-- The first discriminant element is `-3`. -/
theorem disc_zero (hp2 : p ≠ 2) : disc p 0 = -3 := by
  have h := mul_inv_cancel₀ (four_ne_zero (p := p) hp2)
  simp only [disc, level, iter, pow_zero, pow_one, eval_add, eval_X, eval_one]
  linear_combination h

/-- If some discriminant element is a square, the conjecture over `𝔽_p` is the dichotomy. -/
theorem ffMullinConjecture_iff_dichotomy_of_isSquare (hp2 : p ≠ 2) {k : ℕ}
    (h : IsSquare (disc p k)) : FFMullinConjecture p ↔ Dichotomy.FFDichotomy p :=
  ffMullinConjecture_iff_of_not_stable (fun hs => (stable_iff hp2).mp hs k h)

/-- If no discriminant element is a square, the conjecture over `𝔽_p` is false. -/
theorem not_ffMullinConjecture_of_forall_not_isSquare (hp2 : p ≠ 2)
    (h : ∀ k, ¬ IsSquare (disc p k)) : ¬ FFMullinConjecture p :=
  not_ffMullinConjecture_of_stable ((stable_iff hp2).mpr h)

end StabilityCriterion

end FunctionFieldAnalog
