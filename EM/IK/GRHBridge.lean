import EM.IK.GRHStatements
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order

/-!
# From GRH to the bound `ψ(x, χ) ≪ √x log²(N x)`

The repository `leanprover-community/riemann-hypothesis` proves three things about Dirichlet
`L`-functions that it never combines:

* the Riemann hypothesis for them (`DirichletLZerosOnLine`, see `EM.IK.GRHStatements`);
* a truncated explicit formula for `ψ(u, χ)`, `χ` primitive, with an explicit error term
  (`TruncatedExplicitFormula` below);
* a count of the zeros in a window of height one (`ZeroCountUnitWindow` below).

That repository is not a dependency. The last two statements are restated here with Mathlib's
definitions only, as `Prop`s, and used as hypotheses. From the three together we prove the
classical bound (Davenport, *Multiplicative Number Theory*, ch. 20).

## Results

* `grh_psi_bound_primitive` : for primitive `χ ≠ 1` mod `N` and `x ≥ 2`,
  `|ψ(x, χ)| ≤ C √x log²(N x)`, with `C` absolute.
* `norm_psiChi_sub_primitive_le` (unconditional) : `ψ(x, χ)` and `ψ(x, χ*)`, with `χ*` the
  primitive character inducing `χ`, differ by at most `⌊log₂ x⌋ · log N`: the two sums differ
  only at powers of the primes dividing `N`.
* `grhPsiBound_of_primitive`, `grhPsiBound_of_explicitFormula` : the bound for every
  non-principal `χ`, that is `∃ C, GRHPsiBound C`.

## Proof

Take `T = u = x` in the explicit formula. Its error term is then
`≪ log²(N x) + ∑_{|Im ρ| < 1} m(ρ)/|ρ|`. On the line `Re ρ = 1/2` each term of the sum over
zeros has size `m(ρ) √x / |ρ|`, so everything reduces to
`∑_{|Im ρ| < x} m(ρ)/|ρ| ≪ log²(N x)`. A zero with `j ≤ |Im ρ| < j + 1` lies in the unit
window centred at `j` or at `-j` and satisfies `|ρ| ≥ (j + 1)/3`; the zero count bounds the
total multiplicity of each window by `≪ log(N x)`, and `∑_{j ≤ x} 1/(j + 1) ≪ log x`.
-/

namespace IK

open Finset DirichletCharacter

/-! ### The two external statements -/

open Classical in
/-- Truncated explicit formula for primitive Dirichlet characters, with the zeros counted with
multiplicity and the error term explicit in the modulus.

This is the statement of `GlobalTheory.ExplicitFormula.truncated_explicit_formula` in
`Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedExplicitFormula.lean`
of `leanprover-community/riemann-hypothesis`, with its `psi0 χ u` unfolded to
`∑_{n ≤ u} Λ(n) χ(n) - (u if χ = 1, else 0)`; nothing else is changed. The finiteness of the
set of zeros with `|Im ρ| < T` is part of the statement, so the sums over zeros are sums over
finite sets. -/
def TruncatedExplicitFormula : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ u T : ℝ, 2 ≤ T → T ≤ u →
      {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ LFunction χ ρ = 0}.Finite ∧
      ‖((∑ n ∈ Finset.Icc 1 ⌊u⌋₊,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)) -
            (if χ = 1 then (u : ℂ) else 0)) +
          ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ LFunction χ ρ = 0},
            ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
        C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) +
          ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0},
            ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖)

/-- Zero count in a window of height one: for primitive `χ` mod `q`, the zeros of `L(s, χ)`
in the critical strip with `|Im ρ - t| ≤ 1`, counted with multiplicity, number at most
`C log(q (|t| + 2))`.

This is `GlobalTheory.Mem.An.ZeroCount`, proved as `GlobalTheory.Mem.An.zeroCount_holds` in
`Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ZeroCountHolds.lean` of
`leanprover-community/riemann-hypothesis` (definitions in
`Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ZeroCount.lean` and
`Development/AbelianVarietyTheory/Definitions/Foundations/RayPrimes.lean`), with `zsumR`,
`zerosIn`, `zmult` unfolded. The only change is that the summand `m(ρ) * (fun _ => 1) ρ` is
written `m(ρ)`. The window is a finite set (it is contained in a set that
`TruncatedExplicitFormula` asserts to be finite), so the sum is a genuine count. -/
def ZeroCountUnitWindow : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ t : ℝ,
    ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0},
      ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) ≤ C * Real.log (q * (|t| + 2))

/-! ### The sum of `m(ρ)/|ρ|` over a finite set of points on the critical line -/

/-- Let `Z` be a finite set of points on the line `Re ρ = 1/2` with `|Im ρ| < x`, weighted by
`m ≥ 0`, where `x ≥ 0`. If every window `|Im ρ - t| ≤ 1` with `|t| ≤ x` has total weight at most `B`, then
`∑ m(ρ)/|ρ| ≤ 6 B ∑_{j ≤ x} 1/(j + 1)`. -/
theorem sum_div_norm_le_of_window (Z : Finset ℂ) (m : ℂ → ℝ) (hm : ∀ ρ, 0 ≤ m ρ) (x B : ℝ) (hx : 0 ≤ x)
    (hZ : ∀ ρ ∈ Z, ρ.re = 1 / 2 ∧ |ρ.im| < x)
    (hW : ∀ t : ℝ, |t| ≤ x → ∑ ρ ∈ Z with |ρ.im - t| ≤ 1, m ρ ≤ B) :
    ∑ ρ ∈ Z, m ρ / ‖ρ‖ ≤ 6 * B * ∑ j ∈ range (⌊x⌋₊ + 1), ((j : ℝ) + 1)⁻¹ := by
  classical
  have key : ∀ ρ ∈ Z, m ρ / ‖ρ‖ ≤ ∑ j ∈ range (⌊x⌋₊ + 1), 3 / ((j : ℝ) + 1) *
      ((if |ρ.im - (j : ℝ)| ≤ 1 then m ρ else 0) +
        (if |ρ.im - (-(j : ℝ))| ≤ 1 then m ρ else 0)) := by
    intro ρ hρ
    obtain ⟨hre, him⟩ := hZ ρ hρ
    have hmρ : 0 ≤ m ρ := hm ρ
    have hj0le : ((⌊|ρ.im|⌋₊ : ℕ) : ℝ) ≤ |ρ.im| := Nat.floor_le (abs_nonneg _)
    have hj0lt : |ρ.im| < ((⌊|ρ.im|⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have hmem : ⌊|ρ.im|⌋₊ ∈ range (⌊x⌋₊ + 1) := by
      rw [mem_range, Nat.lt_succ_iff]
      exact Nat.floor_le_floor him.le
    have hnn : ∀ j ∈ range (⌊x⌋₊ + 1), 0 ≤ 3 / ((j : ℝ) + 1) *
        ((if |ρ.im - (j : ℝ)| ≤ 1 then m ρ else 0) +
          (if |ρ.im - (-(j : ℝ))| ≤ 1 then m ρ else 0)) := by
      intro j _
      have h1 : 0 ≤ (if |ρ.im - (j : ℝ)| ≤ 1 then m ρ else 0) := by split_ifs <;> simp [hmρ]
      have h2 : 0 ≤ (if |ρ.im - (-(j : ℝ))| ≤ 1 then m ρ else 0) := by
        split_ifs <;> simp [hmρ]
      have h3 : 0 ≤ 3 / ((j : ℝ) + 1) := by positivity
      exact mul_nonneg h3 (add_nonneg h1 h2)
    refine le_trans ?_ (single_le_sum hnn hmem)
    have hnorm_re : (1 : ℝ) / 2 ≤ ‖ρ‖ := by
      rw [← hre]; exact (le_abs_self _).trans (Complex.abs_re_le_norm ρ)
    have hnorm_im : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
    have hpos : 0 < ‖ρ‖ := by linarith
    have hj0nn : (0 : ℝ) ≤ ((⌊|ρ.im|⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    have hinv : 1 / ‖ρ‖ ≤ 3 / (((⌊|ρ.im|⌋₊ : ℕ) : ℝ) + 1) := by
      rw [div_le_div_iff₀ hpos (by positivity)]
      linarith
    have hone : m ρ ≤ (if |ρ.im - ((⌊|ρ.im|⌋₊ : ℕ) : ℝ)| ≤ 1 then m ρ else 0) +
        (if |ρ.im - (-((⌊|ρ.im|⌋₊ : ℕ) : ℝ))| ≤ 1 then m ρ else 0) := by
      rcases le_total 0 ρ.im with h | h
      · have hw : |ρ.im - ((⌊|ρ.im|⌋₊ : ℕ) : ℝ)| ≤ 1 := by
          have ha : |ρ.im| = ρ.im := abs_of_nonneg h
          rw [abs_le]; constructor <;> linarith
        simp only [hw, ↓reduceIte]
        split_ifs <;> linarith
      · have hw : |ρ.im - (-((⌊|ρ.im|⌋₊ : ℕ) : ℝ))| ≤ 1 := by
          have ha : |ρ.im| = -ρ.im := abs_of_nonpos h
          rw [abs_le]; constructor <;> linarith
        simp only [hw, ↓reduceIte]
        split_ifs <;> linarith
    calc m ρ / ‖ρ‖ = m ρ * (1 / ‖ρ‖) := by ring
      _ ≤ m ρ * (3 / (((⌊|ρ.im|⌋₊ : ℕ) : ℝ) + 1)) := mul_le_mul_of_nonneg_left hinv hmρ
      _ = 3 / (((⌊|ρ.im|⌋₊ : ℕ) : ℝ) + 1) * m ρ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hone (by positivity)
  calc ∑ ρ ∈ Z, m ρ / ‖ρ‖
      ≤ ∑ ρ ∈ Z, ∑ j ∈ range (⌊x⌋₊ + 1), 3 / ((j : ℝ) + 1) *
          ((if |ρ.im - (j : ℝ)| ≤ 1 then m ρ else 0) +
            (if |ρ.im - (-(j : ℝ))| ≤ 1 then m ρ else 0)) := sum_le_sum key
    _ = ∑ j ∈ range (⌊x⌋₊ + 1), 3 / ((j : ℝ) + 1) *
          ((∑ ρ ∈ Z with |ρ.im - (j : ℝ)| ≤ 1, m ρ) +
            (∑ ρ ∈ Z with |ρ.im - (-(j : ℝ))| ≤ 1, m ρ)) := by
        rw [sum_comm]
        refine sum_congr rfl fun j _ => ?_
        rw [← mul_sum, sum_add_distrib, sum_filter, sum_filter]
    _ ≤ ∑ j ∈ range (⌊x⌋₊ + 1), 3 / ((j : ℝ) + 1) * (B + B) := by
        refine sum_le_sum fun j hj => ?_
        have hjx : (j : ℝ) ≤ x := by
          have hj' : j ≤ ⌊x⌋₊ := Nat.lt_succ_iff.mp (mem_range.mp hj)
          exact (Nat.cast_le.mpr hj').trans (Nat.floor_le hx)
        have hjnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
        have h1 := hW (j : ℝ) (by rw [abs_of_nonneg hjnn]; exact hjx)
        have h2 := hW (-(j : ℝ)) (by rw [abs_neg, abs_of_nonneg hjnn]; exact hjx)
        exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
    _ = 6 * B * ∑ j ∈ range (⌊x⌋₊ + 1), ((j : ℝ) + 1)⁻¹ := by
        rw [mul_sum]
        exact sum_congr rfl fun j _ => by ring

/-! ### Primitive characters -/

/-- **GRH bound for primitive characters.** Assume the truncated explicit formula, the zero
count in unit windows and the Riemann hypothesis for Dirichlet `L`-functions. Then there is
an absolute constant `C` such that `|ψ(x, χ)| ≤ C √x log²(N x)` for every primitive
non-principal character `χ` mod `N` and every `x ≥ 2`. -/
theorem grh_psi_bound_primitive (hE : TruncatedExplicitFormula) (hZC : ZeroCountUnitWindow)
    (hGRH : DirichletLZerosOnLine) :
    ∃ C : ℝ, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      ∀ x : ℝ, 2 ≤ x → ‖psiChi χ x‖ ≤ C * Real.sqrt x * Real.log (N * x) ^ 2 := by
  classical
  obtain ⟨C₁, hC₁, h₁⟩ := hE
  obtain ⟨C₂, h₂⟩ := hZC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 1 / Real.log 2 := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; positivity
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 12 * |C₂| * (c + 2) := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKdef]; positivity
  refine ⟨K + C₁ * (4 + c) + C₁ * K, fun N _ χ hχ hχ1 x hx => ?_⟩
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hNx : 2 ≤ (N : ℝ) * x := by nlinarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log (N * x) := ⟨_, rfl⟩
  have hL2 : Real.log 2 ≤ L := by rw [hLdef]; exact Real.log_le_log (by norm_num) hNx
  have hLpos : 0 < L := by linarith
  have hcL : 1 ≤ c * L := by
    rw [hcdef, one_div, inv_mul_eq_div, le_div_iff₀ hlog2]; linarith
  have h2L : Real.log (((N : ℝ) * x) ^ 2) = 2 * L := by
    rw [Real.log_pow, hLdef]; norm_num
  -- anything at most `(N x)²` and at least `1` has logarithm in `[0, 2 L]`
  have hlogle : ∀ y : ℝ, 1 ≤ y → y ≤ ((N : ℝ) * x) ^ 2 →
      0 ≤ Real.log y ∧ Real.log y ≤ 2 * L := fun y hy1 hy2 =>
    ⟨Real.log_nonneg hy1, h2L ▸ Real.log_le_log (by linarith) hy2⟩
  have hsq : x * x ≤ ((N : ℝ) * x) ^ 2 := by
    have : (1 : ℝ) * (x * x) ≤ (N : ℝ) * N * (x * x) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (mul_nonneg hx0 hx0)
    nlinarith
  -- the explicit formula at `T = u = x`
  obtain ⟨hfin, hb⟩ := h₁ N χ hχ x x hx le_rfl
  simp only [hχ1, ↓reduceIte, sub_zero] at hb
  have hfin1 : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0}.Finite :=
    hfin.subset fun ρ hρ => ⟨hρ.1, hρ.2.1, by linarith [hρ.2.2.1], hρ.2.2.2⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin1] at hb
  obtain ⟨m, hmdef⟩ : ∃ m : ℂ → ℝ,
      m = fun ρ => ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) := ⟨_, rfl⟩
  have hm : ∀ ρ, 0 ≤ m ρ := fun ρ => by rw [hmdef]; positivity
  have hZmem : ∀ ρ, ρ ∈ hfin.toFinset ↔
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < x ∧ LFunction χ ρ = 0 := fun ρ => by
    rw [Set.Finite.mem_toFinset]; rfl
  have hZline : ∀ ρ ∈ hfin.toFinset, ρ.re = 1 / 2 ∧ |ρ.im| < x := fun ρ hρ => by
    obtain ⟨h0, h1, h2, h3⟩ := (hZmem ρ).mp hρ
    exact ⟨hGRH N χ ρ h0 h1 h3, h2⟩
  -- the zero count bounds every window that matters by `|C₂| · 2 L`
  have hW : ∀ t : ℝ, |t| ≤ x →
      ∑ ρ ∈ hfin.toFinset with |ρ.im - t| ≤ 1, m ρ ≤ |C₂| * (2 * L) := by
    intro t ht
    have htnn : 0 ≤ |t| := abs_nonneg t
    have hfinW : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0}.Finite := by
      refine (h₁ N χ hχ (|t| + 2) (|t| + 2) (by linarith) le_rfl).1.subset fun ρ hρ => ?_
      refine ⟨hρ.1, hρ.2.1, ?_, hρ.2.2.2⟩
      have h1 : |ρ.im| ≤ |ρ.im - t| + |t| := by
        have := abs_add_le (ρ.im - t) t
        rwa [sub_add_cancel] at this
      linarith [hρ.2.2.1]
    have hcount := h₂ N χ hχ t
    rw [finsum_mem_eq_finite_toFinset_sum _ hfinW] at hcount
    have hsub : (hfin.toFinset.filter fun ρ : ℂ => |ρ.im - t| ≤ 1) ⊆ hfinW.toFinset := by
      intro ρ hρ
      rw [mem_filter, hZmem] at hρ
      rw [Set.Finite.mem_toFinset]
      exact ⟨hρ.1.1, hρ.1.2.1, hρ.2, hρ.1.2.2.2⟩
    have hle1 : ∑ ρ ∈ hfin.toFinset with |ρ.im - t| ≤ 1, m ρ ≤ ∑ ρ ∈ hfinW.toFinset, m ρ :=
      sum_le_sum_of_subset_of_nonneg hsub fun ρ _ _ => hm ρ
    have hy : (1 : ℝ) ≤ (N : ℝ) * (|t| + 2) ∧ (N : ℝ) * (|t| + 2) ≤ ((N : ℝ) * x) ^ 2 := by
      constructor
      · nlinarith
      · have h1 : (N : ℝ) * (|t| + 2) ≤ (N : ℝ) * (x * x) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
        have h2 : (N : ℝ) * (x * x) ≤ (N : ℝ) * (N * (x * x)) :=
          mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hx0 hx0]) (by linarith)
        nlinarith
    obtain ⟨hl0, hl1⟩ := hlogle _ hy.1 hy.2
    have hsum_eq : ∑ ρ ∈ hfinW.toFinset, m ρ =
        ∑ ρ ∈ hfinW.toFinset, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) := by
      rw [hmdef]
    calc ∑ ρ ∈ hfin.toFinset with |ρ.im - t| ≤ 1, m ρ
        ≤ C₂ * Real.log (N * (|t| + 2)) := hle1.trans (hsum_eq ▸ hcount)
      _ ≤ |C₂| * Real.log (N * (|t| + 2)) := mul_le_mul_of_nonneg_right (le_abs_self _) hl0
      _ ≤ |C₂| * (2 * L) := mul_le_mul_of_nonneg_left hl1 (abs_nonneg _)
  -- hence `∑ m(ρ)/|ρ| ≤ K L²`
  have hharm : ∑ j ∈ range (⌊x⌋₊ + 1), ((j : ℝ) + 1)⁻¹ ≤ (c + 2) * L := by
    have h1 : ∑ j ∈ range (⌊x⌋₊ + 1), ((j : ℝ) + 1)⁻¹ = ((harmonic (⌊x⌋₊ + 1) : ℚ) : ℝ) := by
      simp [harmonic]
    have h2 := harmonic_le_one_add_log (⌊x⌋₊ + 1)
    have hfl : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
    have h3 : Real.log ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * L := by
      refine (hlogle _ ?_ ?_).2
      · push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌊x⌋₊]
      · push_cast; nlinarith
    rw [h1]
    linarith
  have hS : ∑ ρ ∈ hfin.toFinset, m ρ / ‖ρ‖ ≤ K * L ^ 2 := by
    have h := sum_div_norm_le_of_window hfin.toFinset m hm x (|C₂| * (2 * L)) hx0 hZline hW
    have hB : 0 ≤ 6 * (|C₂| * (2 * L)) := by positivity
    calc ∑ ρ ∈ hfin.toFinset, m ρ / ‖ρ‖
        ≤ 6 * (|C₂| * (2 * L)) * ∑ j ∈ range (⌊x⌋₊ + 1), ((j : ℝ) + 1)⁻¹ := h
      _ ≤ 6 * (|C₂| * (2 * L)) * ((c + 2) * L) := mul_le_mul_of_nonneg_left hharm hB
      _ = K * L ^ 2 := by rw [hKdef]; ring
  -- the three pieces of the explicit formula
  have hS1 : ∑ ρ ∈ hfin1.toFinset, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖ ≤
      ∑ ρ ∈ hfin.toFinset, m ρ / ‖ρ‖ := by
    rw [hmdef]
    refine sum_le_sum_of_subset_of_nonneg (fun ρ hρ => ?_) fun ρ _ _ => by positivity
    rw [Set.Finite.mem_toFinset] at hρ ⊢
    exact ⟨hρ.1, hρ.2.1, by linarith [hρ.2.2.1], hρ.2.2.2⟩
  have hxpos : (0 : ℝ) < x := by linarith
  have hzeros : ‖∑ ρ ∈ hfin.toFinset,
      ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((x : ℂ) ^ ρ / ρ)‖ ≤
      Real.sqrt x * ∑ ρ ∈ hfin.toFinset, m ρ / ‖ρ‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun ρ hρ => le_of_eq ?_
    rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hxpos,
      (hZline ρ hρ).1, ← Real.sqrt_eq_rpow, hmdef]
    ring
  have hmain : Real.log (N * x * x) ^ 2 ≤ 4 * L ^ 2 := by
    have hy : (1 : ℝ) ≤ N * x * x ∧ (N : ℝ) * x * x ≤ ((N : ℝ) * x) ^ 2 := by
      constructor
      · nlinarith
      · have : (N : ℝ) * (x * x) ≤ (N : ℝ) * (N * (x * x)) :=
          mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hx0 hx0]) (by linarith)
        nlinarith
    obtain ⟨hl0, hl1⟩ := hlogle _ hy.1 hy.2
    nlinarith
  have hfirst : x * Real.log (N * x * x) ^ 2 / x = Real.log (N * x * x) ^ 2 := by
    field_simp
  rw [hfirst, ← hLdef] at hb
  have hLle : L ≤ c * L ^ 2 := by
    have : 1 * L ≤ c * L * L := mul_le_mul_of_nonneg_right hcL hLpos.le
    nlinarith
  have hpsi_eq : psiChi χ x = (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)) := rfl
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = L ^ 2 := ⟨_, rfl⟩
  have hA : 0 ≤ A := by rw [hAdef]; positivity
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt x := ⟨_, rfl⟩
  have hs : 1 ≤ s := by
    rw [hsdef]; exact Real.one_le_sqrt.mpr (by linarith)
  rw [← hAdef] at hS hmain hLle
  have hinner : Real.log (N * x * x) ^ 2 + L +
      ∑ ρ ∈ hfin1.toFinset, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖ ≤
      4 * A + c * A + K * A := by linarith
  have hbound : ‖psiChi χ x‖ ≤ C₁ * (4 * A + c * A + K * A) + s * (K * A) := by
    have htri : ‖psiChi χ x‖ ≤ ‖psiChi χ x + ∑ ρ ∈ hfin.toFinset,
        ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((x : ℂ) ^ ρ / ρ)‖ +
        ‖∑ ρ ∈ hfin.toFinset,
          ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((x : ℂ) ^ ρ / ρ)‖ := by
      have := norm_sub_le (psiChi χ x + ∑ ρ ∈ hfin.toFinset,
        ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((x : ℂ) ^ ρ / ρ))
        (∑ ρ ∈ hfin.toFinset,
          ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((x : ℂ) ^ ρ / ρ))
      rwa [add_sub_cancel_right] at this
    rw [hpsi_eq] at htri ⊢
    have h1 := hb.trans (mul_le_mul_of_nonneg_left hinner hC₁.le)
    have h2 : Real.sqrt x * ∑ ρ ∈ hfin.toFinset, m ρ / ‖ρ‖ ≤ s * (K * A) := by
      rw [← hsdef]
      exact mul_le_mul_of_nonneg_left hS (by linarith)
    linarith
  have hslack : 0 ≤ (C₁ * (4 + c) + C₁ * K) * A * (s - 1) :=
    mul_nonneg (mul_nonneg (by positivity) hA) (by linarith)
  calc ‖psiChi χ x‖ ≤ C₁ * (4 * A + c * A + K * A) + s * (K * A) := hbound
    _ = (K + C₁ * (4 + c) + C₁ * K) * s * A - (C₁ * (4 + c) + C₁ * K) * A * (s - 1) := by ring
    _ ≤ (K + C₁ * (4 + c) + C₁ * K) * s * A := by linarith
    _ = (K + C₁ * (4 + c) + C₁ * K) * Real.sqrt x * Real.log (N * x) ^ 2 := by
        rw [hsdef, hAdef, hLdef]

/-! ### From primitive characters to all non-principal characters -/

/-- The von Mangoldt function summed over the `n ≤ M` that are not coprime to `N` is at most
`⌊log₂ M⌋ · log N`: such an `n` with `Λ(n) ≠ 0` is `p ^ k` with `p ∣ N` and `2 ^ k ≤ M`. -/
theorem sum_vonMangoldt_not_coprime_le (N : ℕ) (hN : N ≠ 0) (M : ℕ) :
    ∑ n ∈ Icc 1 M with ¬ n.Coprime N, ArithmeticFunction.vonMangoldt n ≤
      (Nat.log 2 M : ℝ) * Real.log N := by
  classical
  have hsub : ((Icc 1 M).filter fun n => ¬ n.Coprime N).filter
        (fun n => ArithmeticFunction.vonMangoldt n ≠ 0) ⊆
      (N.primeFactors ×ˢ Icc 1 (Nat.log 2 M)).image fun q : ℕ × ℕ => q.1 ^ q.2 := by
    intro n hn
    rw [mem_filter, mem_filter, mem_Icc] at hn
    obtain ⟨⟨⟨-, hnM⟩, hncop⟩, hΛ⟩ := hn
    obtain ⟨p, k, hp, hk, rfl⟩ :=
      (isPrimePow_nat_iff n).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
    have hpN : p ∣ N := by
      by_contra hnd
      exact hncop (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd))
    refine mem_image.mpr ⟨(p, k), ?_, rfl⟩
    rw [mem_product, Nat.mem_primeFactors, mem_Icc]
    refine ⟨⟨hp, hpN, hN⟩, hk, Nat.le_log_of_pow_le (by norm_num) ?_⟩
    exact (Nat.pow_le_pow_left hp.two_le k).trans hnM
  have hprod : ∑ p ∈ N.primeFactors, Real.log (p : ℝ) ≤ Real.log N := by
    rw [← Real.log_prod (fun p hp => by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
    have hdvd := Nat.prod_primeFactors_dvd N
    have hle : ∏ p ∈ N.primeFactors, p ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hdvd
    have hpos : 0 < ∏ p ∈ N.primeFactors, p :=
      Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
    have hcast : ((∏ p ∈ N.primeFactors, p : ℕ) : ℝ) = ∏ p ∈ N.primeFactors, (p : ℝ) := by
      push_cast; rfl
    rw [← hcast]
    exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)
  calc ∑ n ∈ Icc 1 M with ¬ n.Coprime N, ArithmeticFunction.vonMangoldt n
      = ∑ n ∈ ((Icc 1 M).filter fun n => ¬ n.Coprime N) with
          ArithmeticFunction.vonMangoldt n ≠ 0, ArithmeticFunction.vonMangoldt n :=
        (sum_filter_ne_zero _).symm
    _ ≤ ∑ n ∈ (N.primeFactors ×ˢ Icc 1 (Nat.log 2 M)).image (fun q : ℕ × ℕ => q.1 ^ q.2),
          ArithmeticFunction.vonMangoldt n :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ ∑ q ∈ N.primeFactors ×ˢ Icc 1 (Nat.log 2 M),
          ArithmeticFunction.vonMangoldt (q.1 ^ q.2) :=
        sum_image_le_of_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
    _ = ∑ p ∈ N.primeFactors, ∑ _k ∈ Icc 1 (Nat.log 2 M), Real.log (p : ℝ) := by
        rw [sum_product]
        refine sum_congr rfl fun p hp => sum_congr rfl fun k hk => ?_
        rw [ArithmeticFunction.vonMangoldt_apply_pow (by have := (mem_Icc.mp hk).1; omega),
          ArithmeticFunction.vonMangoldt_apply_prime (Nat.prime_of_mem_primeFactors hp)]
    _ = (Nat.log 2 M : ℝ) * ∑ p ∈ N.primeFactors, Real.log (p : ℝ) := by
        rw [mul_sum]
        refine sum_congr rfl fun p _ => ?_
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp
    _ ≤ (Nat.log 2 M : ℝ) * Real.log N :=
        mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)

/-- `ψ(x, χ)` and `ψ(x, χ*)`, where `χ*` is the primitive character inducing `χ` mod `N`,
differ by at most `⌊log₂ ⌊x⌋⌋ · log N`. No hypothesis. -/
theorem norm_psiChi_sub_primitive_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) :
    ‖psiChi χ x - psiChi χ.primitiveCharacter x‖ ≤ (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log N := by
  classical
  refine le_trans ?_ (sum_vonMangoldt_not_coprime_le N (NeZero.ne N) ⌊x⌋₊)
  unfold psiChi
  rw [← sum_sub_distrib, sum_filter]
  refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
  by_cases hcop : n.Coprime N
  · have h := χ.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ))
      (Nat.isCoprime_iff_coprime.mpr hcop)
    simp only [Int.cast_natCast] at h
    rw [h, sub_self, norm_zero]
    simp [hcop]
  · have hχ0 : χ (n : ZMod N) = 0 :=
      MulChar.map_nonunit χ (fun hu => hcop ((ZMod.isUnit_iff_coprime n N).mp hu))
    rw [hχ0, mul_zero, zero_sub, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    simp only [hcop, not_false_eq_true, ↓reduceIte]
    calc ArithmeticFunction.vonMangoldt n * ‖χ.primitiveCharacter (n : ZMod χ.conductor)‖
        ≤ ArithmeticFunction.vonMangoldt n * 1 :=
          mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one _ _)
            ArithmeticFunction.vonMangoldt_nonneg
      _ = ArithmeticFunction.vonMangoldt n := mul_one _

/-- **From primitive to all non-principal characters.** A bound `C √x log²(N x)` for `ψ(x, χ)`
over primitive non-principal `χ` gives the same bound, with a larger constant, over all
non-principal `χ`. No hypothesis beyond the primitive bound. -/
theorem grhPsiBound_of_primitive
    (h : ∃ C : ℝ, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      ∀ x : ℝ, 2 ≤ x → ‖psiChi χ x‖ ≤ C * Real.sqrt x * Real.log (N * x) ^ 2) :
    ∃ C : ℝ, GRHPsiBound C := by
  obtain ⟨C, hC⟩ := h
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨|C| + 1 / Real.log 2, fun N _ χ hχ1 x hx => ?_⟩
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim_ne : χ.primitiveCharacter ≠ 1 := by
    intro h1
    apply hχ1
    rw [← χ.changeLevel_primitiveCharacter, h1, changeLevel_one]
  have hstar := hC χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hprim_ne x hx
  have hdiff := norm_psiChi_sub_primitive_le χ x
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hd1 : (1 : ℝ) ≤ χ.conductor := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero
  have hdN : (χ.conductor : ℝ) ≤ N := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) χ.conductor_dvd_level
  have hx0 : (0 : ℝ) ≤ x := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log (N * x) := ⟨_, rfl⟩
  have hlogN : 0 ≤ Real.log (N : ℝ) ∧ Real.log (N : ℝ) ≤ L :=
    ⟨Real.log_nonneg hN, hLdef ▸ Real.log_le_log (by linarith) (by nlinarith)⟩
  have hlogx : 0 ≤ Real.log x ∧ Real.log x ≤ L :=
    ⟨Real.log_nonneg (by linarith), hLdef ▸ Real.log_le_log (by linarith) (by nlinarith)⟩
  have hLd : 0 ≤ Real.log (χ.conductor * x) ∧ Real.log (χ.conductor * x) ≤ L :=
    ⟨Real.log_nonneg (by nlinarith),
      hLdef ▸ Real.log_le_log (by nlinarith) (mul_le_mul_of_nonneg_right hdN hx0)⟩
  have hL0 : 0 ≤ L := hlogx.1.trans hlogx.2
  have hs : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr (by linarith)
  -- `⌊log₂ ⌊x⌋⌋ ≤ log x / log 2`
  have hfloor : (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log 2 ≤ Real.log x := by
    have hfl : ⌊x⌋₊ ≠ 0 := by
      have : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
      omega
    have h1 : ((2 : ℝ)) ^ Nat.log 2 ⌊x⌋₊ ≤ x := by
      have := Nat.pow_log_le_self 2 hfl
      calc ((2 : ℝ)) ^ Nat.log 2 ⌊x⌋₊ ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast this
        _ ≤ x := Nat.floor_le hx0
    exact Real.le_log_of_pow_le (by norm_num) h1
  have hK : (Nat.log 2 ⌊x⌋₊ : ℝ) ≤ 1 / Real.log 2 * L := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hlog2]
    linarith [hlogx.2]
  have hdiff' : ‖psiChi χ x - psiChi χ.primitiveCharacter x‖ ≤ 1 / Real.log 2 * L * L :=
    hdiff.trans (mul_le_mul hK hlogN.2 hlogN.1 (by positivity))
  have hsq : Real.log (χ.conductor * x) ^ 2 ≤ L ^ 2 := by nlinarith [hLd.1, hLd.2]
  have hstar' : ‖psiChi χ.primitiveCharacter x‖ ≤ |C| * Real.sqrt x * L ^ 2 := by
    refine hstar.trans ?_
    have h1 : C * Real.sqrt x * Real.log (χ.conductor * x) ^ 2 ≤
        |C| * Real.sqrt x * Real.log (χ.conductor * x) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg x)) (by positivity)
    exact h1.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
  have htri : ‖psiChi χ x‖ ≤ ‖psiChi χ.primitiveCharacter x‖ +
      ‖psiChi χ x - psiChi χ.primitiveCharacter x‖ := by
    have := norm_add_le (psiChi χ.primitiveCharacter x)
      (psiChi χ x - psiChi χ.primitiveCharacter x)
    rwa [add_sub_cancel] at this
  have hlast : 1 / Real.log 2 * L * L ≤ 1 / Real.log 2 * Real.sqrt x * L ^ 2 := by
    have hc : 0 ≤ 1 / Real.log 2 := by positivity
    have : 1 / Real.log 2 * L ^ 2 * 1 ≤ 1 / Real.log 2 * L ^ 2 * Real.sqrt x :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    nlinarith
  rw [← hLdef]
  calc ‖psiChi χ x‖ ≤ |C| * Real.sqrt x * L ^ 2 + 1 / Real.log 2 * Real.sqrt x * L ^ 2 := by
        linarith
    _ = (|C| + 1 / Real.log 2) * Real.sqrt x * L ^ 2 := by ring

/-- **GRH bound for `ψ(x, χ)`.** The truncated explicit formula, the zero count in unit
windows and the Riemann hypothesis for Dirichlet `L`-functions together give
`|ψ(x, χ)| ≤ C √x log²(N x)` for every non-principal `χ` mod `N` and `x ≥ 2`. -/
theorem grhPsiBound_of_explicitFormula (hE : TruncatedExplicitFormula)
    (hZC : ZeroCountUnitWindow) (hGRH : DirichletLZerosOnLine) : ∃ C : ℝ, GRHPsiBound C :=
  grhPsiBound_of_primitive (grh_psi_bound_primitive hE hZC hGRH)

end IK
