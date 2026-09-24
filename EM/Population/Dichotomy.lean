import EM.Population.SeededGrowth
import EM.Population.AutonomousBranch
import EM.Ensemble.WeylChain
import EM.FunctionField.CompositeFloors
import EM.FunctionField.StableTower
import Mathlib.Analysis.Polynomial.Basic

/-!
# The dichotomy conjecture (Zilber–Pink form) and the algebraic part of the orbit

2026-09-24.  Companion to `docs/analysis/euclid_systems_theory_2026-09-23.md` §9.

## The Ax–Lindemann analogue: the only algebraic reason is the tower

`algebraic_multiplier_implies_tower`: if the multiplier is a polynomial function of the
Euclid number from some stage on, `Mullin.seq (n+1) = g(prod n + 1)` for `g ∈ ℤ[X]` and all `n ≥ N`,
then `g = X` and every Euclid number from stage `N` is prime.  So the orbit satisfies an
algebraic recursion only on the Sylvester tower `E ↦ E² − E + 1`, which is the one branch on
which missing a prime has a structural reason (`Φ₃`).  Proof: `2 ≤ g(E) ≤ E` on an unbounded
set forces `deg g ≤ 1` (polynomial growth over `ℝ`), and the linear case is divisibility.

## The conjecture

`DichotomyConjecture`: for every seed `m ≥ 2`, `GenMullinConjecture m ↔ sgrowth m = 0`, i.e.
an orbit misses a prime coprime to its seed iff it is eventually a Sylvester tower.  For the
seed `2` the direction `MC ⟹ growthConstant = 0` is on file; the conjecture reduces MC to the
floor `(C∞)` (`mc_of_dichotomy`).  Over `𝔽_2[t]` and `𝔽_p[t]` with `p ≡ 1 (mod 3)` the floor is
a theorem for every sequence, so the function-field form of the conjecture implies FF-MC
there (`ffMC_two_of_ffDichotomy`, `ffMC_of_ffDichotomy_one_mod_three`); over `𝔽_5[t]` it is
consistent with the refutation, because the refuting sequence has positive growth constant
(`stableTower_ffGrowthConstant_ne_zero`).

**Scope.**  The conjecture is open in both directions for general seeds and its easy
direction is only recorded for the seed `2`.  Nothing here constrains the orbit of `2`.
-/

noncomputable section
open Classical Filter Polynomial Mullin

namespace Dichotomy

/-! ## 1. Growth of the accumulator -/

theorem add_two_le_prod (n : ℕ) : n + 2 ≤ prod n := by
  induction n with
  | zero => simp [prod_zero]
  | succ n ih =>
    rw [prod_succ]
    have h2 : 2 ≤ Mullin.seq (n + 1) :=
      ((MullinGroup.isPrime_iff_natPrime _).mp (seq_isPrime (n + 1))).two_le
    nlinarith

/-- The Euclid numbers past any stage exceed any given integer. -/
theorem exists_euclid_gt (N : ℕ) (c : ℤ) : ∃ n, N ≤ n ∧ c < ((prod n + 1 : ℕ) : ℤ) := by
  refine ⟨max N c.toNat, le_max_left _ _, ?_⟩
  have h1 := add_two_le_prod (max N c.toNat)
  have h2 : c.toNat ≤ max N c.toNat := le_max_right _ _
  have h3 : c ≤ (c.toNat : ℤ) := Int.self_le_toNat c
  push_cast
  omega

/-! ## 2. A polynomial with `0 < g(x) ≤ x` on an unbounded set has degree `≤ 1` -/

theorem natDegree_le_one_of_bounded (g : ℤ[X])
    (h : ∀ B : ℕ, ∃ x : ℕ, B ≤ x ∧ 0 < g.eval (x : ℤ) ∧ g.eval (x : ℤ) ≤ x) :
    g.natDegree ≤ 1 := by
  by_contra hdeg
  push Not at hdeg
  have hg0 : g ≠ 0 := by
    rintro rfl
    simp at hdeg
  set f : ℤ →+* ℝ := Int.castRingHom ℝ
  have hinj : Function.Injective f := Int.cast_injective
  set gR : ℝ[X] := g.map f
  have hdegR : (X : ℝ[X]).degree < gR.degree := by
    rw [degree_X, degree_map_eq_of_injective hinj, degree_eq_natDegree hg0]
    exact_mod_cast (show 1 < g.natDegree by omega)
  have hlead : gR.leadingCoeff = (g.leadingCoeff : ℝ) := leadingCoeff_map_of_injective hinj g
  have hevalR : ∀ x : ℕ, gR.eval (x : ℝ) = ((g.eval (x : ℤ) : ℤ) : ℝ) := by
    intro x
    have h1 : ((x : ℕ) : ℝ) = (((x : ℕ) : ℤ) : ℝ) := by simp
    rw [h1, eval_intCast_map]
    simp [f]
  -- the ratio `g(x)/x` lies in `(0, 1]` on an unbounded set
  have hratio : ∀ B : ℕ, ∃ x : ℕ, B ≤ x ∧ 0 < gR.eval (x : ℝ) / (X : ℝ[X]).eval (x : ℝ) ∧
      gR.eval (x : ℝ) / (X : ℝ[X]).eval (x : ℝ) ≤ 1 := by
    intro B
    obtain ⟨x, hx, hpos, hle⟩ := h (B + 1)
    have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
    refine ⟨x, by omega, ?_, ?_⟩
    · rw [hevalR, eval_X]
      apply div_pos _ hx0
      exact_mod_cast hpos
    · rw [hevalR, eval_X, div_le_one hx0]
      exact_mod_cast hle
  rcases le_or_gt 0 g.leadingCoeff with hnn | hneg
  · -- leading coefficient `≥ 0`: the ratio tends to `+∞`
    have ht : Tendsto (fun x : ℝ => gR.eval x / (X : ℝ[X]).eval x) atTop atTop :=
      div_tendsto_atTop_of_degree_gt gR X hdegR X_ne_zero
        (by rw [hlead, leadingCoeff_X, div_one]; exact_mod_cast hnn)
    obtain ⟨R, hR⟩ := eventually_atTop.mp (tendsto_atTop.mp ht 2)
    obtain ⟨x, hx, -, hle⟩ := hratio ⌈R⌉₊
    have hxR : R ≤ (x : ℝ) := (Nat.le_ceil R).trans (by exact_mod_cast hx)
    linarith [hR (x : ℝ) hxR]
  · -- leading coefficient `< 0`: the ratio tends to `−∞`
    have ht : Tendsto (fun x : ℝ => gR.eval x / (X : ℝ[X]).eval x) atTop atBot :=
      div_tendsto_atBot_of_degree_gt gR X hdegR X_ne_zero
        (by rw [hlead, leadingCoeff_X, div_one]; exact_mod_cast hneg.le)
    obtain ⟨R, hR⟩ := eventually_atTop.mp (tendsto_atBot.mp ht 0)
    obtain ⟨x, hx, hpos, -⟩ := hratio ⌈R⌉₊
    have hxR : R ≤ (x : ℝ) := (Nat.le_ceil R).trans (by exact_mod_cast hx)
    linarith [hR (x : ℝ) hxR]

/-! ## 3. The Ax–Lindemann analogue -/

/-- **An algebraic multiplier law forces the Sylvester tower.**  If `Mullin.seq (n+1) = g(prod n + 1)`
for a polynomial `g ∈ ℤ[X]` and all `n ≥ N`, then `g = X` and `prod n + 1` is prime for all
`n ≥ N`. -/
theorem algebraic_multiplier_implies_tower (g : ℤ[X]) (N : ℕ)
    (h : ∀ n, N ≤ n → (Mullin.seq (n + 1) : ℤ) = g.eval ((prod n + 1 : ℕ) : ℤ)) :
    g = X ∧ ∀ n, N ≤ n → Nat.Prime (prod n + 1) := by
  -- basic facts about the multiplier
  have hprime : ∀ n, (Mullin.seq (n + 1)).Prime := fun n =>
    (MullinGroup.isPrime_iff_natPrime _).mp (seq_isPrime (n + 1))
  have hdvd : ∀ n, Mullin.seq (n + 1) ∣ prod n + 1 := fun n => by
    rw [seq_succ]; exact Euclid.minFac_dvd _ (by have := prod_ge_two n; omega)
  have hle : ∀ n, Mullin.seq (n + 1) ≤ prod n + 1 := fun n =>
    Nat.le_of_dvd (by omega) (hdvd n)
  -- degree `≤ 1`
  have hdeg : g.natDegree ≤ 1 := by
    apply natDegree_le_one_of_bounded
    intro B
    refine ⟨prod (max N B) + 1, ?_, ?_, ?_⟩
    · have := add_two_le_prod (max N B); have := le_max_right N B; omega
    · rw [← h _ (le_max_left N B)]; exact_mod_cast (hprime _).pos
    · rw [← h _ (le_max_left N B)]; exact_mod_cast hle _
  obtain ⟨a, b, hg⟩ := exists_eq_X_add_C_of_natDegree_le_one hdeg
  -- the linear law
  have hlin : ∀ n, N ≤ n → (Mullin.seq (n + 1) : ℤ) = a * ((prod n + 1 : ℕ) : ℤ) + b := by
    intro n hn
    rw [h n hn, hg]
    simp
  have hbig := exists_euclid_gt N
  -- `a ≠ 0`: the multipliers are distinct
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h1 := hlin N le_rfl
    have h2 := hlin (N + 1) (by omega)
    simp only [zero_mul, zero_add] at h1 h2
    have : Mullin.seq (N + 1) = Mullin.seq (N + 1 + 1) := by exact_mod_cast h1.trans h2.symm
    have := seq_injective _ _ this
    omega
  -- `a = 1`
  have ha1 : a = 1 := by
    rcases lt_trichotomy a 1 with ha | ha | ha
    · -- `a ≤ −1`: the multiplier would eventually be `< 2`
      exfalso
      obtain ⟨n, hn, hE⟩ := hbig (b - 2)
      have h2 : (2 : ℤ) ≤ Mullin.seq (n + 1) := by exact_mod_cast (hprime n).two_le
      have hE0 : (0 : ℤ) ≤ ((prod n + 1 : ℕ) : ℤ) := by positivity
      have hlt : a ≤ -1 := by omega
      have := hlin n hn
      nlinarith
    · exact ha
    · -- `a ≥ 2`: the multiplier would exceed the Euclid number
      exfalso
      obtain ⟨n, hn, hE⟩ := hbig (-b)
      have hle' : (Mullin.seq (n + 1) : ℤ) ≤ ((prod n + 1 : ℕ) : ℤ) := by exact_mod_cast hle n
      have hE0 : (0 : ℤ) ≤ ((prod n + 1 : ℕ) : ℤ) := by positivity
      have hge : 2 ≤ a := by omega
      have := hlin n hn
      nlinarith
  subst ha1
  -- `b = 0`: `E + b ∣ E` forces `E + b ∣ b`
  have hb0 : b = 0 := by
    by_contra hb
    obtain ⟨n, hn, hE⟩ := hbig (2 * |b|)
    set E : ℤ := ((prod n + 1 : ℕ) : ℤ) with hEdef
    have hval : (Mullin.seq (n + 1) : ℤ) = E + b := by rw [hlin n hn]; ring
    have hdvdE : E + b ∣ E := by rw [← hval, hEdef]; exact_mod_cast hdvd n
    have hdvdb : E + b ∣ b := by
      have := dvd_sub (dvd_refl (E + b)) hdvdE
      simpa using this
    have hpos : 0 < E + b := by
      rw [← hval]; exact_mod_cast (hprime n).pos
    have hle_abs : E + b ≤ |b| := by
      have := Int.le_of_dvd (abs_pos.mpr hb) (hdvdb.trans (dvd_abs b b |>.mpr dvd_rfl))
      exact this
    have := abs_nonneg b
    have hb' : b ≤ |b| := le_abs_self b
    have : -|b| ≤ b := neg_abs_le b
    linarith
  subst hb0
  refine ⟨by simp [hg], fun n hn => ?_⟩
  have hval : (Mullin.seq (n + 1) : ℤ) = ((prod n + 1 : ℕ) : ℤ) := by rw [hlin n hn]; ring
  have : Mullin.seq (n + 1) = prod n + 1 := by exact_mod_cast hval
  rw [← this]
  exact hprime n

/-- The recursion form: if `prod (n+1) + 1 = f(prod n + 1)` for a polynomial `f` and all
`n ≥ N`, then the orbit is a Sylvester tower from `N`. -/
theorem algebraic_recursion_implies_tower (f : ℤ[X]) (N : ℕ)
    (h : ∀ n, N ≤ n → ((prod (n + 1) + 1 : ℕ) : ℤ) = f.eval ((prod n + 1 : ℕ) : ℤ)) :
    ∀ n, N ≤ n → Nat.Prime (prod n + 1) := by
  -- `f(E) − 1 = (E − 1)·seq(n+1)`; polynomial division `f − 1 = (X − 1) g + C r` with `r = 0`
  obtain ⟨g, r, hfr⟩ : ∃ g : ℤ[X], ∃ r : ℤ, f - 1 = (X - 1) * g + C r := by
    refine ⟨(f - 1) /ₘ (X - 1), ((f - 1) %ₘ (X - 1)).coeff 0, ?_⟩
    have hmonic : (X - 1 : ℤ[X]).Monic := by
      simpa using monic_X_sub_C (1 : ℤ)
    have hdeg : ((f - 1) %ₘ (X - 1)).degree < (X - 1 : ℤ[X]).degree := degree_modByMonic_lt _ hmonic
    have hdeg1 : (X - 1 : ℤ[X]).degree = 1 := by simpa using degree_X_sub_C (1 : ℤ)
    rw [hdeg1] at hdeg
    have hC : (f - 1) %ₘ (X - 1) = C (((f - 1) %ₘ (X - 1)).coeff 0) :=
      eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp hdeg)
    conv_lhs => rw [← modByMonic_add_div (f - 1) (X - 1)]
    rw [← hC]; ring
  -- evaluate along the orbit: `(E − 1)·seq = (E − 1)·g(E) + r`
  have hstep : ∀ n, N ≤ n →
      (((prod n : ℕ) : ℤ)) * (Mullin.seq (n + 1) : ℤ) = ((prod n : ℕ) : ℤ) * g.eval ((prod n + 1 : ℕ) : ℤ) + r := by
    intro n hn
    have h1 := h n hn
    have h2 : ((prod (n + 1) + 1 : ℕ) : ℤ) - 1 = ((prod n : ℕ) : ℤ) * (Mullin.seq (n + 1) : ℤ) := by
      rw [prod_succ]; push_cast; ring
    have h3 : (f - 1).eval ((prod n + 1 : ℕ) : ℤ) = ((prod n : ℕ) : ℤ) * g.eval ((prod n + 1 : ℕ) : ℤ) + r := by
      rw [hfr]; simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_one]; push_cast; ring
    rw [← h3, eval_sub, eval_one, ← h1, h2]
  -- `r = 0` since `prod n ∣ r` for unboundedly many `n`
  have hr : r = 0 := by
    by_contra hr
    obtain ⟨n, hn, hE⟩ := exists_euclid_gt N (|r| + 1)
    have h1 := hstep n hn
    have hdvd : ((prod n : ℕ) : ℤ) ∣ r := by
      have : r = ((prod n : ℕ) : ℤ) * ((Mullin.seq (n + 1) : ℤ) - g.eval ((prod n + 1 : ℕ) : ℤ)) := by
        linear_combination -h1
      exact ⟨_, this⟩
    have hle := Int.le_of_dvd (abs_pos.mpr hr) (hdvd.trans ((dvd_abs r r).mpr dvd_rfl))
    push_cast at hE
    linarith
  subst hr
  have hmult : ∀ n, N ≤ n → (Mullin.seq (n + 1) : ℤ) = g.eval ((prod n + 1 : ℕ) : ℤ) := by
    intro n hn
    have h1 := hstep n hn
    have hP : ((prod n : ℕ) : ℤ) ≠ 0 := by
      have := prod_ge_two n; positivity
    rw [add_zero] at h1
    exact mul_left_cancel₀ hP h1
  exact (algebraic_multiplier_implies_tower g N hmult).2

/-! ## 4. The dichotomy conjecture -/

open SeededGrowth in
/-- **The dichotomy conjecture (Zilber–Pink form).**  For every seed `m ≥ 2`, the greedy orbit
captures every prime coprime to `m` iff it is not eventually a Sylvester tower. -/
def DichotomyConjecture : Prop :=
  ∀ m : ℕ, 2 ≤ m → (GenMullinConjecture m ↔ sgrowth m = 0)

open SeededGrowth in
/-- The seed-`2` instance of the proved direction: MC forces the growth constant to vanish. -/
theorem sgrowth_two_eq_zero_of_mc (hmc : MullinConjecture) : sgrowth 2 = 0 := by
  rw [sgrowth_two]
  exact DefectTelescope.infinitelyManyComposite_iff_growthConstant_eq_zero.mp
    (AutonomousBranch.mullin_implies_infinitelyManyComposite hmc)

open SeededGrowth in
/-- Under the dichotomy conjecture, MC reduces to the floor `(C∞)`. -/
theorem mc_of_dichotomy (hd : DichotomyConjecture) (hc : DefectTelescope.growthConstant = 0) :
    MullinConjecture := by
  rw [← gen_mc_two_iff_mc, hd 2 le_rfl, sgrowth_two]
  exact hc

/-! ## 5. The function-field form and its consequences -/

open FunctionFieldAnalog FFDegreeTelescope in
/-- The function-field dichotomy: a sequence over `𝔽_p[t]` captures every monic irreducible
iff its growth constant vanishes. -/
def FFDichotomy (p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ∀ d : FFEMData p,
    (∀ Q : Polynomial (ZMod p), Q.Monic → Irreducible Q → ∃ n, d.ffSeq n = Q) ↔
      ffGrowthConstant d = 0

open FunctionFieldAnalog FFDegreeTelescope in
/-- Over `𝔽_2[t]` the floor is a theorem, so the dichotomy implies FF-MC. -/
theorem ffMC_two_of_ffDichotomy (h : FFDichotomy 2) : FFMullinConjecture 2 := by
  intro d Q hQm hQi
  exact (h d).mpr (CompositeFloors.ffGrowthConstant_eq_zero_of_two d) Q hQm hQi

open FunctionFieldAnalog FFDegreeTelescope in
/-- Over `𝔽_p[t]`, `p ≡ 1 (mod 3)`, likewise. -/
theorem ffMC_of_ffDichotomy_one_mod_three {p : ℕ} [Fact (Nat.Prime p)] (hp3 : p % 3 = 1)
    (h : FFDichotomy p) : FFMullinConjecture p := by
  intro d Q hQm hQi
  exact (h d).mpr (CompositeFloors.ffGrowthConstant_eq_zero_of_one_mod_three hp3 d) Q hQm hQi

open FunctionFieldAnalog FFDegreeTelescope in
/-- Over `𝔽_5[t]` the dichotomy is consistent with the refutation: the stable tower, which
misses every cubic, has positive growth constant. -/
theorem stableTower_ffGrowthConstant_ne_zero : ffGrowthConstant StableTower.tower ≠ 0 := by
  intro h0
  have hred := (ffInfinitelyManyReducible_iff_ffGrowthConstant_eq_zero _).mpr h0
  obtain ⟨n, -, hn⟩ := hred 0
  exact hn (StableTower.tower_euclid_irreducible n)

end Dichotomy

end
