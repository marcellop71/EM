import EM.FunctionField.StabilityCriterion
import EM.FunctionField.SecondGeneration

/-!
# The cubic step: the critical value of the accumulator decides

2026-11-22.

For `p ≡ 1 (mod 3)` every sequence over `𝔽_p[X]` has accumulator
`P = X (X + 1) (X − ω)` at stage `2` (`SecondGeneration.lean`). `P` is a pure cubic about its
centre,

  `P = (X + (1 − ω)/3)³ + e`,   `e = (1 + 2ω)/9`,

and `e` is the critical value of `P` (the value at the centre, the only finite critical
point). This file proves the cubic counterpart of
`StabilityCriterion.level_succ_irreducible_iff`:

  for `F` monic irreducible over `𝔽_p`,  `F(P)` is irreducible iff `F(e)` is not a cube.

The quadratic statement reads: `T_k (Y² + Y)` is irreducible iff `T_k(−1/4)` is not a square
(up to the unit `(−4)^{2^k}`), and `−1/4` is the critical value of `Y² + Y`. Here the map is
of degree `3` with a symmetry of order `3`, the character is cubic, and the element is again
the value of the outer polynomial at the critical value of the inner one.

As long as the terms chosen after stage `2` are polynomials in `P`, each Euclid polynomial is
`A(P) + 1` and its factors are of the form `F(P)`; the criterion decides each of them. Two
instances are recorded:

* stage `3`, when stage `2` is prime: `E_3 = (P − ω)(P − ω²)`, and the term at stage `4` has
  degree `3` iff neither `e − ω` nor `e − ω²` is a cube; otherwise it is linear;
* stage `4`, when the term at stage `4` is `P − ω'`: `E_4` is the stage-`2` cubic composed
  with `P` — the second generation again, one level up — and it is irreducible iff the value
  of that cubic at `e` is not a cube.

## Main results

* `exists_cube_of_pow_eq_one` — in `𝔽_p`, `p ≡ 1 (mod 3)`: `x^{(p−1)/3} = 1` implies `x` is a
  cube.
* `comp_cube_irreducible_iff` — `F(X³ + e)` is irreducible iff `F(e)` is not a cube.
* `acc_eq` — `X (X+1) (X−ω) = (X + (1−ω)/3)³ + (1+2ω)/9`.
* `comp_acc_irreducible_iff` — `F(X (X+1) (X−ω))` is irreducible iff `F((1+2ω)/9)` is not a
  cube.
* `euclid_three_factor`, `ffSeq_four` — stage `3` and the term at stage `4`.
* `euclid_four_irreducible_iff` — stage `4`.
-/

namespace FunctionFieldAnalog

namespace CubicStep

open Polynomial FrobeniusOrbit StabilityCriterion SecondGeneration CompositeFloors

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ## 1. Cubes in `𝔽_p`, `p ≡ 1 (mod 3)` -/

theorem three_mul_div (hp3 : p % 3 = 1) : 3 * ((p - 1) / 3) + 1 = p := by
  have := (Fact.out : p.Prime).two_le
  omega

/-- For `p ≡ 1 (mod 3)`: if `x ≠ 0` and `x^{(p−1)/3} = 1`, then `x` is a cube. -/
theorem exists_cube_of_pow_eq_one (hp3 : p % 3 = 1) {x : ZMod p} (hx : x ≠ 0)
    (h : x ^ ((p - 1) / 3) = 1) : ∃ b : ZMod p, b ^ 3 = x := by
  set n := (p - 1) / 3 with hn
  have hpn : 3 * n + 1 = p := three_mul_div hp3
  have hnpos : 0 < n := by
    have := (Fact.out : p.Prime).two_le
    omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = 3 * n := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
    omega
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg (Units.mk0 x hx))
  have hu : (Units.mk0 x hx) ^ n = 1 := by
    apply Units.ext
    simpa using h
  have hdvd : ((3 * n : ℕ) : ℤ) ∣ j * n := by
    rw [← hord, orderOf_dvd_iff_zpow_eq_one, zpow_mul, hj]
    exact_mod_cast hu
  have h3 : (3 : ℤ) ∣ j := by
    have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hnpos.ne'
    have : (3 : ℤ) * n ∣ j * n := by exact_mod_cast hdvd
    exact (mul_dvd_mul_iff_right hn0).mp this
  obtain ⟨t, ht⟩ := h3
  refine ⟨((g ^ t : (ZMod p)ˣ) : ZMod p), ?_⟩
  have : (g ^ t) ^ 3 = Units.mk0 x hx := by
    rw [← hj, ht, mul_comm, zpow_mul]
    norm_cast
  have h' := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) this
  simpa using h'

/-! ## 2. The Kummer step over an irreducible polynomial -/

/-- The element of `𝔽_p` whose cubic class decides `F (X³ + e)`. -/
noncomputable def cnorm (F : (ZMod p)[X]) (e : ZMod p) : ZMod p :=
  (-1) ^ F.natDegree * eval e F

theorem neg_one_pow_cube (m : ℕ) : (((-1 : ZMod p)) ^ m) ^ 3 = (-1) ^ m := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-- `F(e)` is a cube iff the signed norm is. -/
theorem cube_cnorm_iff (F : (ZMod p)[X]) (e : ZMod p) :
    (∃ b : ZMod p, b ^ 3 = cnorm F e) ↔ ∃ b : ZMod p, b ^ 3 = eval e F := by
  have hsq : ((-1 : ZMod p) ^ F.natDegree) * (-1) ^ F.natDegree = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨(-1) ^ F.natDegree * b, ?_⟩
    rw [mul_pow, neg_one_pow_cube, hb, cnorm, ← mul_assoc, hsq, one_mul]
  · rintro ⟨b, hb⟩
    exact ⟨(-1) ^ F.natDegree * b, by rw [mul_pow, neg_one_pow_cube, hb, cnorm]⟩

/-- **Frobenius on a root of `F (X³ + e)`.** With `m = deg F`, `α^{p^m} = N^{(p−1)/3} · α`,
    where `N = (−1)^m F(e)` is the norm of `α³`. -/
theorem frob_root (hp3 : p % 3 = 1) {F : (ZMod p)[X]} (hFm : F.Monic) (hF : Irreducible F)
    (e : ZMod p) {α : Lp p} (hα : aeval α (F.comp (X ^ 3 + C e)) = 0) :
    Φ p F.natDegree α =
      algebraMap (ZMod p) (Lp p) (cnorm F e ^ ((p - 1) / 3)) * α ∧
    (α = 0 → cnorm F e = 0) ∧ (cnorm F e = 0 → α = 0) := by
  set a := algebraMap (ZMod p) (Lp p) with ha
  set m := F.natDegree with hm
  set n := (p - 1) / 3 with hn
  set S := ∑ i ∈ Finset.range m, p ^ i with hS
  set θ : Lp p := α ^ 3 + a e with hθ
  have hpn : 3 * n + 1 = p := three_mul_div hp3
  have hθroot : aeval θ F = 0 := by
    have h := hα
    rw [aeval_comp] at h
    simpa [hθ, ha] using h
  have hmpos : 0 < m := hF.natDegree_pos
  have hu : ∀ i, (θ - a e) ^ p ^ i = (-1) * (a e - θ ^ p ^ i) := by
    intro i
    rw [← Φ_apply, map_sub, Φ_algebraMap, Φ_apply]
    ring
  have hN : (θ - a e) ^ S = a (cnorm F e) := by
    rw [hS, ← Finset.prod_pow_eq_pow_sum]
    simp only [hu]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      prod_sub_conj hFm hF hθroot, cnorm, map_mul, map_pow, map_neg, map_one]
  have hcube : α ^ 3 = θ - a e := by rw [hθ]; ring
  have hexp : p ^ m = 3 * (n * S) + 1 := by
    have := geom (3 * n) m
    rw [hpn] at this
    rw [← this, hS]; ring
  have hSpos : S ≠ 0 := by
    rw [hS]
    have : 0 < ∑ i ∈ Finset.range m, p ^ i :=
      Finset.sum_pos (fun i _ => pow_pos (Fact.out : p.Prime).pos i)
        ⟨0, Finset.mem_range.mpr hmpos⟩
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [Φ_apply, hexp, pow_succ, pow_mul, hcube, mul_comm n S, pow_mul, hN, ← map_pow]
  · intro h0
    have : a (cnorm F e) = 0 := by
      rw [← hN, ← hcube, h0]
      simp [hSpos]
    exact (map_eq_zero a).mp this
  · intro h0
    have : (θ - a e) ^ S = 0 := by rw [hN, h0, map_zero]
    have hu0 : θ - a e = 0 := (pow_eq_zero_iff hSpos).mp this
    rw [← hcube] at hu0
    exact (pow_eq_zero_iff (by norm_num)).mp hu0

/-- **The cubic step.** For `p ≡ 1 (mod 3)`, `F` monic irreducible over `𝔽_p` and `e ∈ 𝔽_p`:
    `F (X³ + e)` is irreducible iff `F(e)` is not a cube in `𝔽_p`. -/
theorem comp_cube_irreducible_iff (hp3 : p % 3 = 1) {F : (ZMod p)[X]} (hFm : F.Monic)
    (hF : Irreducible F) (e : ZMod p) :
    Irreducible (F.comp (X ^ 3 + C e)) ↔ ∀ b : ZMod p, b ^ 3 ≠ eval e F := by
  set G := F.comp (X ^ 3 + C e) with hG
  set m := F.natDegree with hm
  set n := (p - 1) / 3 with hn
  have hpn : 3 * n + 1 = p := three_mul_div hp3
  have hmpos : 0 < m := hF.natDegree_pos
  have hGdeg : G.natDegree = m * 3 := by
    rw [hG, natDegree_comp, natDegree_X_pow_add_C]
  have hGm : G.Monic := by
    rw [hG]
    refine hFm.comp (monic_X_pow_add_C e (by norm_num)) ?_
    rw [natDegree_X_pow_add_C]; norm_num
  obtain ⟨α, hα⟩ := exists_root_of_natDegree_pos p (f := G) (by rw [hGdeg]; omega)
  obtain ⟨hfrob, h0, h0'⟩ := frob_root hp3 hFm hF e hα
  change Φ p m α = algebraMap (ZMod p) (Lp p) (cnorm F e ^ n) * α at hfrob
  have hnc : (∀ b : ZMod p, b ^ 3 ≠ eval e F) ↔ ¬ ∃ b : ZMod p, b ^ 3 = cnorm F e := by
    rw [cube_cnorm_iff]; exact not_exists.symm
  rw [hnc]
  constructor
  · rintro hirr ⟨c, hc⟩
    have hfix : Φ p m α = α := by
      by_cases hc0 : c = 0
      · have : α = 0 := h0' (by rw [← hc, hc0]; norm_num)
        rw [this, map_zero]
      · have h1 : cnorm F e ^ n = 1 := by
          rw [← hc, ← pow_mul]
          have : 3 * n = p - 1 := by omega
          rw [this, ZMod.pow_card_sub_one_eq_one hc0]
        rw [hfrob, h1, map_one, one_mul]
    have h := natDegree_dvd_of_fixed hirr hα (by rw [← Φ_apply]; exact hfix)
    rw [hGdeg] at h
    have := Nat.le_of_dvd hmpos h
    omega
  · intro hncube
    have hdne : cnorm F e ≠ 0 := fun h => hncube ⟨0, by rw [h]; norm_num⟩
    have hαne : α ≠ 0 := fun h => hdne (h0 h)
    set ε := cnorm F e ^ n with hε
    have hε3 : ε ^ 3 = 1 := by
      rw [hε, ← pow_mul]
      have : n * 3 = p - 1 := by omega
      rw [this, ZMod.pow_card_sub_one_eq_one hdne]
    have hε1 : ε ≠ 1 := fun h => hncube (exists_cube_of_pow_eq_one hp3 hdne h)
    have hΦ3 : Φ p m (Φ p m (Φ p m α)) = α := by
      have hstep : ∀ x : Lp p, Φ p m (algebraMap (ZMod p) (Lp p) ε * x) =
          algebraMap (ZMod p) (Lp p) ε * Φ p m x := fun x => by
        rw [map_mul, Φ_algebraMap]
      have hcol : ∀ z : ZMod p, algebraMap (ZMod p) (Lp p) z * (algebraMap (ZMod p) (Lp p) z *
          (algebraMap (ZMod p) (Lp p) z * α)) = algebraMap (ZMod p) (Lp p) (z ^ 3) * α :=
        fun z => by rw [map_pow]; ring
      rw [hfrob, hstep, hfrob, hstep, hstep, hfrob, hcol ε, hε3, map_one, one_mul]
    have hiter : ∀ (k : ℕ) (x : Lp p), (⇑(φ p))^[k] x = Φ p k x := fun k x => by
      rw [Φ, RingHom.coe_pow]
    have hper : Function.IsPeriodicPt (⇑(φ p)) (m + (m + m)) α := by
      show (⇑(φ p))^[m + (m + m)] α = α
      rw [Function.iterate_add_apply, Function.iterate_add_apply, hiter, hiter, hiter, hΦ3]
    set r := Function.minimalPeriod (⇑(φ p)) α with hr
    have hr3 : r ∣ m + (m + m) := hper.minimalPeriod_dvd
    have hrfix : Φ p r α = α := by
      rw [← hiter]; exact Function.isPeriodicPt_minimalPeriod _ _
    have hθroot : aeval (aeval α (X ^ 3 + C e : (ZMod p)[X])) F = 0 := by
      rw [← aeval_comp]; exact hα
    have hmr : m ∣ r :=
      natDegree_dvd_of_fixed hF hθroot (e := r) (by rw [← Φ_apply, Φ_aeval, hrfix])
    obtain ⟨t, ht⟩ := hmr
    have ht3 : t ∣ 3 := by
      have : m * t ∣ m * 3 := by rw [← ht]; convert hr3 using 1; ring
      exact Nat.dvd_of_mul_dvd_mul_left hmpos this
    have hrdeg : r = m * 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp ht3 with h1 | h1
      · exfalso
        rw [h1, mul_one] at ht
        rw [ht] at hrfix
        have hz : (algebraMap (ZMod p) (Lp p) ε - 1) * α = 0 := by
          rw [sub_mul, one_mul, ← hfrob, hrfix, sub_self]
        rcases mul_eq_zero.mp hz with h | h
        · apply hε1
          apply (algebraMap (ZMod p) (Lp p)).injective
          rw [map_one]; exact sub_eq_zero.mp h
        · exact hαne h
      · rw [ht, h1]
    exact irreducible_of_natDegree_eq_minimalPeriod p hGm hα (by rw [hGdeg, ← hr, hrdeg])

/-! ## 3. The accumulator is a pure cubic about its centre -/

section Field

variable {K : Type*} [Field K]

/-- The accumulator at stage `2`: `X (X + 1) (X − ω)`. -/
noncomputable def acc (ω : K) : K[X] := X * (X + 1) * (X - C ω)

/-- The critical value of the accumulator: `(1 + 2ω)/9`. -/
noncomputable def crit (ω : K) : K := (1 + 2 * ω) / 9

/-- The centre of the accumulator is `−(1 − ω)/3`. -/
noncomputable def shift (ω : K) : K := (1 - ω) / 3

theorem cubic_eq_acc (ω : K) : cubic ω = acc ω + 1 := rfl

/-- **The accumulator is a pure cubic about its centre.** -/
theorem acc_eq {ω : K} (h3 : (3 : K) ≠ 0) (hω : ω ^ 2 + ω + 1 = 0) :
    acc ω = (X + C (shift ω)) ^ 3 + C (crit ω) := by
  have h9 : (9 : K) ≠ 0 := by
    have : (9 : K) = 3 ^ 2 := by norm_num
    rw [this]; exact pow_ne_zero 2 h3
  have h3s : 3 * C (shift ω) = 1 - C ω := by
    have h : 3 * shift ω = 1 - ω := by rw [shift]; field_simp
    have := congrArg (C : K → K[X]) h
    simpa only [map_sub, map_mul, map_one, map_ofNat] using this
  have h27e : 27 * C (crit ω) = 3 + 6 * C ω := by
    have h : 27 * crit ω = 3 + 6 * ω := by rw [crit]; field_simp; ring
    have := congrArg (C : K → K[X]) h
    simpa only [map_add, map_mul, map_ofNat] using this
  have h27 : (27 : K[X]) ≠ 0 := by
    have : (27 : K[X]) = C 27 := (map_ofNat C 27).symm
    rw [this, Ne, C_eq_zero]
    have : (27 : K) = 3 ^ 3 := by norm_num
    rw [this]; exact pow_ne_zero 3 h3
  apply mul_left_cancel₀ h27
  rw [acc]
  linear_combination (-(9 * X + 4 - C ω)) * C_root hω
    - ((3 * X + 3 * C (shift ω)) ^ 2 + (3 * X + 3 * C (shift ω)) * (3 * X + 1 - C ω)
        + (3 * X + 1 - C ω) ^ 2) * h3s - h27e

/-- The value of the accumulator at `−shift − b` is `crit − b³`. -/
theorem acc_eval {ω : K} (h3 : (3 : K) ≠ 0) (hω : ω ^ 2 + ω + 1 = 0) (b : K) :
    eval (-shift ω - b) (acc ω) = crit ω - b ^ 3 := by
  rw [acc_eq h3 hω]
  simp only [eval_add, eval_pow, eval_X, eval_C]
  ring

end Field

/-- **The critical value decides.** For `p ≡ 1 (mod 3)`, `ω` a primitive cube root of unity
    and `F` monic irreducible over `𝔽_p`: `F (X (X+1) (X−ω))` is irreducible iff
    `F((1 + 2ω)/9)` is not a cube. -/
theorem comp_acc_irreducible_iff (hp3 : p % 3 = 1) {ω : ZMod p} (hω : ω ^ 2 + ω + 1 = 0)
    {F : (ZMod p)[X]} (hFm : F.Monic) (hF : Irreducible F) :
    Irreducible (F.comp (acc ω)) ↔ ∀ b : ZMod p, b ^ 3 ≠ eval (crit ω) F := by
  have h3 := three_ne_zero_of_one_mod_three hp3
  rw [← comp_cube_irreducible_iff hp3 hFm hF (crit ω)]
  have hcomp : F.comp (acc ω) =
      algEquivAevalXAddC (shift ω) (F.comp (X ^ 3 + C (crit ω))) := by
    rw [acc_eq h3 hω, algEquivAevalXAddC_apply, ← comp_eq_aeval, comp_assoc]
    simp
  rw [hcomp]
  exact MulEquiv.irreducible_iff (algEquivAevalXAddC (shift ω)).toMulEquiv

/-- The case `F = X − t`: `P − t` is irreducible iff `e − t` is not a cube. -/
theorem acc_sub_C_irreducible_iff (hp3 : p % 3 = 1) {ω : ZMod p} (hω : ω ^ 2 + ω + 1 = 0)
    (t : ZMod p) :
    Irreducible (acc ω - C t) ↔ ∀ b : ZMod p, b ^ 3 ≠ crit ω - t := by
  have := comp_acc_irreducible_iff hp3 hω (monic_X_sub_C t) (irreducible_X_sub_C t)
  simpa using this

/-! ## 4. Stages `3` and `4` of every sequence, `p ≡ 1 (mod 3)` -/

/-- For `p ≡ 1 (mod 3)`, the accumulator of every sequence at stage `2` is `X (X+1) (X−ω)`. -/
theorem ffProd_two (hp3 : p % 3 = 1) (d : FFEMData p) :
    ∃ ω : ZMod p, ω ^ 2 + ω + 1 = 0 ∧ d.ffProd 2 = acc ω := by
  obtain ⟨ω, hω, h2⟩ := exists_ffSeq_two hp3 d
  exact ⟨ω, hω, by rw [d.ffProd_succ 1, ffProd_one, h2, acc]⟩

/-- **Stage `3`.** If stage `2` is prime, `E_3 = (P − ω)(P − ω²)` with `P` the accumulator at
    stage `2`. -/
theorem euclid_three_factor (d : FFEMData p) {ω : ZMod p} (hω : ω ^ 2 + ω + 1 = 0)
    (h2 : Irreducible (d.ffProd 2 + 1)) :
    d.ffProd 3 + 1 = (d.ffProd 2 - C ω) * (d.ffProd 2 - C (ω ^ 2)) := by
  rw [ffProd_succ_of_irreducible d 2 h2, C_pow]
  linear_combination (d.ffProd 2 - (C ω - 1)) * C_root hω

theorem acc_sub_C_natDegree (ω t : ZMod p) : (acc ω - C t).natDegree = 3 := by
  rw [acc]; compute_degree!

theorem acc_sub_C_monic (ω t : ZMod p) : (acc ω - C t).Monic := by
  rw [acc]; monicity!

/-- **The term at stage `4`.** For `p ≡ 1 (mod 3)`, if stage `2` is prime then, with
    `P = X (X+1) (X−ω)` the accumulator at stage `2` and `e = (1 + 2ω)/9`:
    if neither `e − ω` nor `e − ω²` is a cube, the term at stage `4` is `P − ω` or `P − ω²`
    (degree `3`); otherwise it is linear. -/
theorem ffSeq_four (hp3 : p % 3 = 1) (d : FFEMData p) (h2 : Irreducible (d.ffProd 2 + 1)) :
    ∃ ω : ZMod p, ω ^ 2 + ω + 1 = 0 ∧ d.ffProd 2 = acc ω ∧
      (((∀ b : ZMod p, b ^ 3 ≠ crit ω - ω) ∧ (∀ b : ZMod p, b ^ 3 ≠ crit ω - ω ^ 2)) →
        (d.ffSeq 4 = acc ω - C ω ∨ d.ffSeq 4 = acc ω - C (ω ^ 2))) ∧
      (¬ ((∀ b : ZMod p, b ^ 3 ≠ crit ω - ω) ∧ (∀ b : ZMod p, b ^ 3 ≠ crit ω - ω ^ 2)) →
        (d.ffSeq 4).natDegree = 1) := by
  obtain ⟨ω, hω, hP⟩ := ffProd_two hp3 d
  have h3 := three_ne_zero_of_one_mod_three hp3
  have hfac := euclid_three_factor d hω h2
  rw [hP] at hfac
  obtain ⟨hm, hirr, hdvd⟩ := d.ffSeq_succ 3
  refine ⟨ω, hω, hP, ?_, ?_⟩
  · rintro ⟨h1, h2'⟩
    have hi1 := (acc_sub_C_irreducible_iff hp3 hω ω).mpr h1
    have hi2 := (acc_sub_C_irreducible_iff hp3 hω (ω ^ 2)).mpr h2'
    rw [hfac] at hdvd
    rcases hirr.prime.dvd_or_dvd hdvd with h | h
    · exact Or.inl (eq_of_monic_irreducible_dvd hm hirr (acc_sub_C_monic ω ω) hi1 h)
    · exact Or.inr (eq_of_monic_irreducible_dvd hm hirr (acc_sub_C_monic ω _) hi2 h)
  · intro hnot
    have hex : ∃ t b : ZMod p, (t = ω ∨ t = ω ^ 2) ∧ b ^ 3 = crit ω - t := by
      by_contra hcon
      apply hnot
      constructor
      · intro b hb; exact hcon ⟨ω, b, Or.inl rfl, hb⟩
      · intro b hb; exact hcon ⟨ω ^ 2, b, Or.inr rfl, hb⟩
    obtain ⟨t, b, ht, hb⟩ := hex
    have hroot : (acc ω - C t).IsRoot (-shift ω - b) := by
      rw [IsRoot.def, eval_sub, eval_C, acc_eval h3 hω, hb]; ring
    have hdvd1 : X - C (-shift ω - b) ∣ acc ω - C t := dvd_iff_isRoot.mpr hroot
    have hdvd2 : acc ω - C t ∣ d.ffProd 3 + 1 := by
      rw [hfac]
      rcases ht with rfl | rfl
      · exact dvd_mul_right _ _
      · exact dvd_mul_left _ _
    have hle : (d.ffSeq 4).natDegree ≤ _ :=
      d.ffSeq_minimal 3 _ (monic_X_sub_C _) (irreducible_X_sub_C _) (hdvd1.trans hdvd2)
    rw [natDegree_X_sub_C] at hle
    have hpos : 0 < (d.ffSeq 4).natDegree := hirr.natDegree_pos
    omega

theorem cubic_monic (ω : ZMod p) : (cubic ω).Monic := by
  rw [cubic]; monicity!

/-- **Stage `4`: the second generation, one level up.** If stage `2` is prime and the term at
    stage `4` is `P − ω'` for a primitive cube root of unity `ω'`, then `E_4` is the cubic
    `Y (Y+1) (Y−ω') + 1` composed with `P`, and — when that cubic is irreducible — `E_4` is
    irreducible iff the value of the cubic at the critical value `e` is not a cube. -/
theorem euclid_four_irreducible_iff (hp3 : p % 3 = 1) (d : FFEMData p) {ω ω' : ZMod p}
    (hω : ω ^ 2 + ω + 1 = 0) (hP : d.ffProd 2 = acc ω)
    (h2 : Irreducible (d.ffProd 2 + 1)) (h4 : d.ffSeq 4 = acc ω - C ω')
    (hc : Irreducible (cubic ω')) :
    d.ffProd 4 + 1 = (cubic ω').comp (acc ω) ∧
      (Irreducible (d.ffProd 4 + 1) ↔ ∀ b : ZMod p, b ^ 3 ≠ eval (crit ω) (cubic ω')) := by
  have hE : d.ffProd 4 + 1 = (cubic ω').comp (acc ω) := by
    rw [d.ffProd_succ 3, ffProd_succ_of_irreducible d 2 h2, h4, hP, cubic]
    simp [mul_comp, add_comp, sub_comp]
  exact ⟨hE, by rw [hE]; exact comp_acc_irreducible_iff hp3 hω (cubic_monic ω') hc⟩

end CubicStep

end FunctionFieldAnalog
