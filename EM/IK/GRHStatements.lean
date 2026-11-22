import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# GRH for Dirichlet `L`-functions: statements used as hypotheses

The repository `leanprover-community/riemann-hypothesis` proves the Riemann hypothesis for
Dirichlet `L`-functions. It is not a dependency of this formalization (different Lean
version, no licence). Its conclusions are stated with Mathlib's definitions only, so they
can be quoted verbatim; here they are `Prop`s, used as hypotheses and never as axioms.

* `DirichletLZerosOnLine` — the statement of that name in its `Challenge.lean`, proved there
  as `LFunction_eq_zero_re`.
* `GRHPsiBound C` — the classical consequence for the twisted Chebyshev function,
  `|ψ(x, χ)| ≤ C √x log²(N x)` for every non-principal `χ` mod `N` and `x ≥ 2`
  (Davenport, *Multiplicative Number Theory*, ch. 20; for imprimitive `χ` the difference
  from the primitive character is at most `log N · log x / log 2`).

`StableCount.GRHDirichlet` is the non-vanishing form (`DirichletLNonvanishingRightOfHalf`).
-/

namespace IK

open Finset

/-- Every zero of a Dirichlet `L`-function in the open critical strip has real part `1/2`. -/
def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- The twisted Chebyshev function `ψ(x, χ) = ∑_{n ≤ x} Λ(n) χ(n)`. -/
noncomputable def psiChi {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N)

/-- The GRH bound for `ψ(x, χ)`, uniform in the modulus. -/
def GRHPsiBound (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ x : ℝ, 2 ≤ x →
    ‖psiChi χ x‖ ≤ C * Real.sqrt x * Real.log (N * x) ^ 2

end IK
