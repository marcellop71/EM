import EM.Population.ProfiniteHeadline
import EM.Population.GrowingRange
import Mathlib.Topology.Instances.ZMod
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Mullin's conjecture as convergence to `0`, and the first coincidence

Session 317 (2026-08-20), second half.  Three short results that reframe *why* the
ensemble methods of this project cannot see an integer orbit, and what is left.

## 1. MC is "the orbit converges to `0`" in the profinite topology

On `Ω = ∏_r ℤ/r` with the product topology, a sequence of integers converges to `0` iff
every prime eventually divides it.  For the greedy orbit `genProd m n` this is exactly
`GenMullinConjecture m` (`genMC_iff_tendsto_zero`), and for `m = 2` it is MC
(`mc_iff_tendsto_zero`).  So MC says: **`0` is an attractor of the greedy map on `Ω`, and the
seed `2` lies in its basin.**  Session 314's profinite headline says the basin has full
Haar measure.  The open question is whether the basin contains the diagonal.

## 2. The first coincidence: almost every point has infinitely many vanishing coordinates

`DivisorFinite = {x | (vanishSet x).Finite}` is the set of points whose Euclid element
`x + 1` has only finitely many vanishing coordinates.  Every diagonal point lies in it
(`iota_mem_divisorFinite`: `m + 1` has finitely many prime divisors), and it is **`μ`-null**
(`measure_divisorFinite_eq_zero`).  The proof is the second Borel–Cantelli lemma made
finite: the event "no coordinate in `(N, Y]` vanishes" has measure `∏ (1 − 1/r) ≤
exp(−Σ 1/r)`, and `Σ_{N<r≤Y} 1/r → ∞` (`not_summable_one_div_on_primes`).

This sharpens "ℕ is null in `Ω`" (`measure_range_iota_eq_zero`) into a *structural*
statement: the integers sit inside the null set of points whose Euclid numbers are
*divisor-finite*, and the same Borel–Cantelli argument recurs at every step of the orbit.
An integer orbit is an **infinite sequence of measure-zero coincidences** — one per step —
so no product-type measure on the coordinates, Haar or otherwise, can charge it.  This is
the precise content of dead end #90 in the profinite language: the obstruction is not that
ℕ is small, it is that ℕ lies in a set on which no countably additive coordinate-compatible
measure exists at all.  The only resource that remains is the *eventual constancy* of an
integer's coordinates (`n mod r = n` for `r > n`), i.e. archimedean size.

## 3. Descent: the only measure-free way to empty a `T`-invariant set

`T m = m · minFac (m+1) = genProd m 1` satisfies `T m > m`, so a set of positive seeds in
which every element has a `T`-preimage is empty (`descent_empty`).  In particular, if every
seed missing `q` had a `T`-preimage missing `q`, no seed would miss `q`
(`misses_descent`).  This is the Vieta-jumping shape — the one pattern that converts
invariance (`GrowingRange.misses_genProd_iff`) into emptiness without a measure.  As
stated it cannot be used: `T(ℕ) ⊆ 2ℕ` (`two_dvd_genProd_one`), so odd seeds have no
preimage at all (`odd_not_in_range_T`).  A usable descent would need a second relation
that preserves "misses `q`" and decreases on an infinite family; none is known.  Recorded
so the shape is on file.

## Scope

Nothing here constrains the orbit of `2`.  Part 1 is a reformulation; Part 2 is a statement
about `μ`; Part 3 is a conditional with an unsatisfiable-as-stated hypothesis.
-/

noncomputable section
open Classical Filter Topology MeasureTheory
open scoped ENNReal

namespace ProfiniteAttractor

open ProfiniteEnsemble (Ω μ localUniform localUniform_apply_finset)
open ProfiniteDynamics (vanishSet mem_vanishSet_iota)

/-! ## 1. MC as convergence to `0` -/

/-- A prime divides the accumulator iff it divides the seed or is one of the multipliers. -/
theorem prime_dvd_genProd_iff {r : ℕ} (hr : r.Prime) (m n : ℕ) :
    r ∣ genProd m n ↔ r ∣ m ∨ ∃ k < n, genSeq m k = r := by
  induction n with
  | zero => simp [genProd]
  | succ n ih =>
    rw [genProd_succ, hr.dvd_mul, ih]
    constructor
    · rintro ((h | ⟨k, hk, hkr⟩) | h)
      · exact Or.inl h
      · exact Or.inr ⟨k, by omega, hkr⟩
      · right
        refine ⟨n, Nat.lt_succ_self n, ?_⟩
        by_cases h0 : genProd m n = 0
        · exfalso
          have h1 : genSeq m n = 1 := by
            show Nat.minFac (genProd m n + 1) = 1
            simp [h0]
          rw [h1] at h
          exact hr.one_lt.ne' (Nat.dvd_one.mp h)
        · exact ((Nat.prime_dvd_prime_iff_eq hr (Nat.minFac_prime (by
            show genProd m n + 1 ≠ 1; omega))).mp h).symm
    · rintro (h | ⟨k, hk, hkr⟩)
      · exact Or.inl (Or.inl h)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact Or.inl (Or.inr ⟨k, hk, hkr⟩)
        · exact Or.inr (hkr ▸ dvd_rfl)

/-- **`GenMC m` is convergence of the orbit to `0` in `Ω`.** -/
theorem genMC_iff_tendsto_zero (m : ℕ) :
    GenMullinConjecture m ↔
      Tendsto (fun n => ProfiniteDynamics.iota (genProd m n)) atTop (𝓝 (0 : Ω)) := by
  rw [tendsto_pi_nhds]
  simp only [ProfiniteDynamics.iota, Pi.zero_apply, nhds_discrete, tendsto_pure]
  constructor
  · intro h r
    by_cases hrm : (r : ℕ) ∣ m
    · exact Eventually.of_forall fun n => (ZMod.natCast_eq_zero_iff _ _).mpr
        ((prime_dvd_genProd_iff r.2 m n).mpr (Or.inl hrm))
    · obtain ⟨k, hk⟩ := h r r.2 hrm
      refine eventually_atTop.mpr ⟨k + 1, fun n hn => ?_⟩
      exact (ZMod.natCast_eq_zero_iff _ _).mpr
        ((prime_dvd_genProd_iff r.2 m n).mpr (Or.inr ⟨k, by omega, hk⟩))
  · intro h q hq hqm
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h ⟨q, hq⟩)
    have := (ZMod.natCast_eq_zero_iff _ _).mp (hN N le_rfl)
    rcases (prime_dvd_genProd_iff hq m N).mp this with h | ⟨k, _, hk⟩
    · exact absurd h hqm
    · exact ⟨k, hk⟩

/-- **Mullin's conjecture is "`prod n → 0` in the profinite topology".**  `0` is the
candidate attractor of the greedy map; MC says the seed `2` is in its basin. -/
theorem mc_iff_tendsto_zero :
    Mullin.MullinConjecture ↔
      Tendsto (fun n => ProfiniteDynamics.iota (Mullin.prod n)) atTop (𝓝 (0 : Ω)) := by
  rw [← gen_mc_two_iff_mc, genMC_iff_tendsto_zero]
  simp only [genProd_two_eq_prod]

/-! ## 2. The first coincidence -/

/-- Points whose Euclid element `x + 1` has finitely many vanishing coordinates. -/
def DivisorFinite : Set Ω := {x | (vanishSet x).Finite}

/-- Every diagonal point is divisor-finite: `m + 1` has finitely many prime divisors. -/
theorem iota_mem_divisorFinite (m : ℕ) : ProfiniteDynamics.iota m ∈ DivisorFinite := by
  refine (Set.finite_Iic (m + 1)).subset fun r hr => ?_
  exact Set.mem_Iic.mpr (Nat.le_of_dvd (Nat.succ_pos m) (mem_vanishSet_iota.mp hr).2)

/-- No coordinate above `N` vanishes. -/
def tailClear (N : ℕ) : Set Ω := {x | ∀ r : Nat.Primes, N < (r : ℕ) → x r + 1 ≠ 0}

theorem divisorFinite_subset_iUnion : DivisorFinite ⊆ ⋃ N, tailClear N := by
  intro x hx
  obtain ⟨N, hN⟩ := hx.bddAbove
  refine Set.mem_iUnion.mpr ⟨N, fun r hr h => ?_⟩
  have hmem : (r : ℕ) ∈ vanishSet x := ⟨r.2, h⟩
  exact absurd (hN hmem) (not_le.mpr hr)

/-- The primes in `(N, Y]`. -/
def block (N Y : ℕ) : Finset Nat.Primes := (Finset.Ico (N + 1) (Y + 1)).subtype Nat.Prime

theorem mem_block {N Y : ℕ} {r : Nat.Primes} : r ∈ block N Y ↔ N < (r : ℕ) ∧ (r : ℕ) ≤ Y := by
  unfold block
  erw [Finset.mem_subtype, Finset.mem_Ico]
  omega

/-- The non-death residues mod `r`. -/
def nonDeath (r : Nat.Primes) : Finset (ZMod (r : ℕ)) :=
  Finset.univ.filter (fun b => b + 1 ≠ 0)

theorem card_nonDeath (r : Nat.Primes) : (nonDeath r).card = (r : ℕ) - 1 := by
  have : nonDeath r = Finset.univ.erase (-1 : ZMod (r : ℕ)) := by
    ext b
    simp only [nonDeath, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
      and_true, Ne, add_eq_zero_iff_eq_neg]
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]

theorem localUniform_nonDeath (r : Nat.Primes) :
    localUniform r (↑(nonDeath r) : Set (ZMod (r : ℕ))) = ENNReal.ofReal (1 - 1 / (r : ℝ)) := by
  rw [localUniform_apply_finset, card_nonDeath]
  have hr1 : (1 : ℕ) ≤ (r : ℕ) := r.2.one_lt.le
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast r.2.pos
  have : (1 - 1 / (r : ℝ)) = (((r : ℕ) - 1 : ℕ) : ℝ) / (r : ℝ) := by
    rw [Nat.cast_sub hr1]; push_cast; field_simp
  rw [this, ENNReal.ofReal_div_of_pos hrpos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

theorem one_sub_inv_nonneg (r : Nat.Primes) : (0 : ℝ) ≤ 1 - 1 / (r : ℝ) := by
  have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast r.2.one_lt.le
  rw [sub_nonneg, div_le_one (by linarith)]
  exact this

/-- **Finite Borel–Cantelli bound.**  The tail-clear event is contained in the cylinder
"no coordinate in `(N, Y]` vanishes", of measure `∏ (1 − 1/r) ≤ exp(−Σ 1/r)`. -/
theorem measure_tailClear_le (N Y : ℕ) :
    μ (tailClear N) ≤ ENNReal.ofReal (Real.exp (-(∑ r ∈ block N Y, 1 / (r : ℝ)))) := by
  have hsub : tailClear N ⊆
      Set.pi (↑(block N Y)) (fun r => (↑(nonDeath r) : Set (ZMod (r : ℕ)))) := by
    intro x hx r hr
    have := hx r (mem_block.mp (Finset.mem_coe.mp hr)).1
    simpa [nonDeath] using this
  calc μ (tailClear N)
      ≤ μ (Set.pi (↑(block N Y)) (fun r => (↑(nonDeath r) : Set (ZMod (r : ℕ))))) :=
        measure_mono hsub
    _ = ∏ r ∈ block N Y, localUniform r (↑(nonDeath r)) := by
        unfold μ
        exact Measure.infinitePi_pi localUniform (fun r _ => (nonDeath r).measurableSet)
    _ = ∏ r ∈ block N Y, ENNReal.ofReal (1 - 1 / (r : ℝ)) :=
        Finset.prod_congr rfl (fun r _ => localUniform_nonDeath r)
    _ = ENNReal.ofReal (∏ r ∈ block N Y, (1 - 1 / (r : ℝ))) :=
        (ENNReal.ofReal_prod_of_nonneg (fun r _ => one_sub_inv_nonneg r)).symm
    _ ≤ ENNReal.ofReal (Real.exp (-(∑ r ∈ block N Y, 1 / (r : ℝ)))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← Finset.sum_neg_distrib, Real.exp_sum]
        refine Finset.prod_le_prod (fun r _ => one_sub_inv_nonneg r) (fun r _ => ?_)
        have := Real.add_one_le_exp (-(1 / (r : ℝ)))
        linarith

/-- The block sums of prime reciprocals are unbounded: `Σ_{N<r≤Y} 1/r → ∞`. -/
theorem exists_block_sum_ge (N : ℕ) (t : ℝ) : ∃ Y, t ≤ ∑ r ∈ block N Y, 1 / (r : ℝ) := by
  set f : ℕ → ℝ := Set.indicator {p | p.Prime} (fun n => (1 : ℝ) / n) with hf_def
  have hf : ∀ n, 0 ≤ f n := fun n => Set.indicator_nonneg (fun n _ => by positivity) n
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg hf).mp
    not_summable_one_div_on_primes
  obtain ⟨Y₀, hY₀⟩ := tendsto_atTop_atTop.mp hdiv (t + ∑ n ∈ Finset.range (N + 1), f n)
  refine ⟨max Y₀ N, ?_⟩
  have hblock : ∑ r ∈ block N (max Y₀ N), 1 / (r : ℝ)
      = ∑ n ∈ Finset.Ico (N + 1) (max Y₀ N + 1), f n := by
    have h1 := Finset.sum_subtype_eq_sum_filter (s := Finset.Ico (N + 1) (max Y₀ N + 1))
      (p := Nat.Prime) (fun n : ℕ => (1 : ℝ) / n)
    refine h1.trans ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [hf_def, Set.indicator_apply, Set.mem_ofPred_eq]
  rw [hblock, Finset.sum_Ico_eq_sub _ (by omega)]
  have := hY₀ (max Y₀ N + 1) (by omega)
  linarith

/-- The tail-clear events are null. -/
theorem measure_tailClear_eq_zero (N : ℕ) : μ (tailClear N) = 0 := by
  by_contra hne
  have hpos : 0 < μ (tailClear N) := pos_iff_ne_zero.mpr hne
  have hlt_top : μ (tailClear N) ≠ ⊤ := measure_ne_top _ _
  set ε := (μ (tailClear N)).toReal with hε
  have hεpos : 0 < ε := ENNReal.toReal_pos hne hlt_top
  obtain ⟨Y, hY⟩ := exists_block_sum_ge N (-Real.log (ε / 2))
  have h1 := measure_tailClear_le N Y
  have h2 : Real.exp (-(∑ r ∈ block N Y, 1 / (r : ℝ))) ≤ ε / 2 := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < ε / 2)]
    exact Real.exp_le_exp.mpr (by linarith)
  have h3 : μ (tailClear N) ≤ ENNReal.ofReal (ε / 2) :=
    le_trans h1 (ENNReal.ofReal_le_ofReal h2)
  have h4 : ENNReal.ofReal (ε / 2) < μ (tailClear N) := by
    rw [← ENNReal.ofReal_toReal hlt_top, ← hε]
    exact (ENNReal.ofReal_lt_ofReal_iff hεpos).mpr (by linarith)
  exact absurd (lt_of_le_of_lt h3 h4) (lt_irrefl _)

/-- **The first coincidence.**  `μ`-almost every point has infinitely many vanishing
coordinates; the divisor-finite points — among them every integer — form a null set. -/
theorem measure_divisorFinite_eq_zero : μ DivisorFinite = 0 :=
  measure_mono_null divisorFinite_subset_iUnion
    (measure_iUnion_null fun N => measure_tailClear_eq_zero N)

/-- The diagonal is null *because* it is divisor-finite (structural reproof of
`ProfiniteEnsemble.measure_range_iota_eq_zero`). -/
theorem measure_range_iota_eq_zero' : μ (Set.range ProfiniteDynamics.iota) = 0 :=
  measure_mono_null (by rintro _ ⟨m, rfl⟩; exact iota_mem_divisorFinite m)
    measure_divisorFinite_eq_zero

/-! ## 3. Descent -/

theorem lt_genProd_one {m : ℕ} (hm : 1 ≤ m) : m < genProd m 1 := by
  show m < m * genSeq m 0
  have h2 : 2 ≤ genSeq m 0 :=
    (Nat.minFac_prime (by show m + 1 ≠ 1; omega)).two_le
  have := Nat.mul_le_mul_left m h2
  omega

/-- **Descent principle.**  A set of positive seeds in which every element is the `T`-image
of another element is empty. -/
theorem descent_empty (S : Set ℕ) (h1 : ∀ m ∈ S, 1 ≤ m)
    (hdesc : ∀ m ∈ S, ∃ m' ∈ S, genProd m' 1 = m) : S = ∅ := by
  have key : ∀ n, ∀ m ∈ S, m ≤ n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro m hm hmn
      obtain ⟨m', hm', hEq⟩ := hdesc m hm
      have := lt_genProd_one (h1 m' hm')
      exact ih m' (by omega) m' hm' le_rfl
  ext m
  exact ⟨fun hm => (key m m hm le_rfl).elim, fun h => h.elim⟩

/-- If every positive seed missing `q` were the `T`-image of a positive seed missing `q`,
no positive seed would miss `q`. -/
theorem misses_descent (q : ℕ)
    (hdesc : ∀ m, 1 ≤ m → GrowingRange.Misses q m →
      ∃ m', 1 ≤ m' ∧ GrowingRange.Misses q m' ∧ genProd m' 1 = m) :
    ∀ m, 1 ≤ m → ¬ GrowingRange.Misses q m := by
  intro m hm hmiss
  have h := descent_empty {m | 1 ≤ m ∧ GrowingRange.Misses q m} (fun _ h => h.1)
    (fun m hm' => by
      obtain ⟨m', h1, h2, h3⟩ := hdesc m hm'.1 hm'.2
      exact ⟨m', ⟨h1, h2⟩, h3⟩)
  have : m ∈ ({m | 1 ≤ m ∧ GrowingRange.Misses q m} : Set ℕ) := ⟨hm, hmiss⟩
  rw [h] at this
  exact this

/-- `T(ℕ) ⊆ 2ℕ`: the image of the greedy map consists of even numbers. -/
theorem two_dvd_genProd_one (m : ℕ) : 2 ∣ genProd m 1 := by
  show 2 ∣ m * genSeq m 0
  rcases Nat.even_or_odd m with he | ho
  · exact Dvd.dvd.mul_right (even_iff_two_dvd.mp he) _
  · have h2 : genSeq m 0 = 2 := by
      show Nat.minFac (m + 1) = 2
      have hdvd : 2 ∣ m + 1 := by
        obtain ⟨k, hk⟩ := ho; exact ⟨k + 1, by omega⟩
      exact le_antisymm (Nat.minFac_le_of_dvd (le_refl 2) hdvd)
        (Nat.minFac_prime (by omega)).two_le
    rw [h2]
    exact Dvd.intro_left m rfl

/-- Odd seeds have no `T`-preimage, so the descent hypothesis is unsatisfiable as stated. -/
theorem odd_not_in_range_T {m : ℕ} (ho : Odd m) : ¬ ∃ m', genProd m' 1 = m := by
  rintro ⟨m', rfl⟩
  exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr (two_dvd_genProd_one m'))

end ProfiniteAttractor

end
