import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Chapter 2: Elementary Theory of Prime Numbers (Iwaniec-Kowalski)

Formalization of Chapter 2 of H. Iwaniec and E. Kowalski,
*Analytic Number Theory*, AMS Colloquium Publications vol. 53, 2004.

## Contents
- §2.1: The Prime Number Theorem (statements and equivalences)
- §2.2: Tchebyshev method (bounds on ψ and θ, Mertens' formulas)
- §2.3: Primes in arithmetic progressions (Dirichlet's theorem)
- §2.4: Reflections on elementary proofs (Selberg's formula)

## References
- [IK] H. Iwaniec, E. Kowalski, *Analytic Number Theory*, 2004
-/

noncomputable section

open Classical

namespace IK

open Nat ArithmeticFunction Finset BigOperators Filter
open scoped ArithmeticFunction.Moebius

/-!
## §2.1 The Prime Number Theorem
-/

section PNT

/-- The Möbius summatory function `M(x) = ∑_{m≤x} μ(m)` — IK §2.1. -/
def mobiusSummatory (x : ℝ) : ℝ :=
  ∑ m ∈ Icc 1 (Nat.floor x), (μ m : ℝ)

/-- The log summatory function `L(x) = ∑_{n≤x} log n` — IK (2.9). -/
def logSummatory (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 (Nat.floor x), Real.log n

/-- `θ(x) ≤ ψ(x)` — bridge to Mathlib. -/
theorem theta_le_psi' (x : ℝ) : Chebyshev.theta x ≤ Chebyshev.psi x :=
  Chebyshev.theta_le_psi x

/-- `|ψ(x) − θ(x)| ≤ 2√x log x` — bridge to Mathlib. -/
theorem psi_sub_theta_bound {x : ℝ} (hx : 1 ≤ x) :
    |Chebyshev.psi x - Chebyshev.theta x| ≤ 2 * Real.sqrt x * Real.log x :=
  Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx

/-- The Prime Number Theorem: `π(x) ~ x / log x` — IK (2.1). -/
def PrimeNumberTheorem : Prop :=
  Tendsto (fun x : ℝ => (Nat.primeCounting (Nat.floor x) : ℝ) * Real.log x / x)
    atTop (nhds 1)

/-- PNT in the form `ψ(x) ~ x` — IK (2.5). -/
def PNT_psi : Prop :=
  Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1)

/-- PNT in the form `θ(x) ~ x` — IK (2.5). -/
def PNT_theta : Prop :=
  Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (nhds 1)

/-- PNT in the form `M(x) = o(x)` — IK (2.6). -/
def PNT_moebius : Prop :=
  Asymptotics.IsLittleO atTop (fun x : ℝ => mobiusSummatory x) (fun x : ℝ => x)

/-- Equivalence: `ψ(x) ~ x ↔ M(x) = o(x)` — IK §2.1. -/
def PNT_psi_iff_moebius : Prop :=
  PNT_psi ↔ PNT_moebius

/-- Equivalence: `ψ(x) ~ x ↔ θ(x) ~ x`.
    Follows from `|ψ(x) − θ(x)| ≤ 2√x log x = o(x)`. -/
def PNT_psi_iff_theta : Prop :=
  PNT_psi ↔ PNT_theta

/-- Equivalence: `π(x) ~ x/log x ↔ ψ(x) ~ x` — follows by partial summation. -/
def PNT_pi_iff_psi : Prop :=
  PrimeNumberTheorem ↔ PNT_psi

end PNT

/-!
## §2.2 Tchebyshev method

Chebyshev bounds on ψ(x) and θ(x), and Mertens' formulas.
-/

section Tchebyshev

/-- Chebyshev's upper bound: `θ(x) ≤ (log 4) x` — IK (2.12) upper. Bridge to Mathlib. -/
theorem chebyshev_theta_upper {x : ℝ} (hx : 0 ≤ x) : Chebyshev.theta x ≤ Real.log 4 * x :=
  Chebyshev.theta_le_log4_mul_x hx

/-- Chebyshev's upper bound: `ψ(x) ≤ (log 4 + 4) x` — bridge to Mathlib. -/
theorem chebyshev_psi_upper {x : ℝ} (hx : 0 ≤ x) :
    Chebyshev.psi x ≤ (Real.log 4 + 4) * x :=
  Chebyshev.psi_le_const_mul_self hx

/-- `L(x) = x log x − x + O(log x)` — IK (2.9). -/
def LogSummatoryAsymptotics : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
    |logSummatory x - (x * Real.log x - x)| ≤ C * Real.log x

/-- `L(x) = ∑_{m≤x} ψ(x/m)` — IK (2.10). -/
def LogSummatoryConvolution : Prop :=
  ∀ x : ℝ, 1 ≤ x →
    logSummatory x = ∑ m ∈ Icc 1 (Nat.floor x), Chebyshev.psi (x / m)

/-- Chebyshev's alternating sum:
    `ψ(x) − ψ(x/2) + ψ(x/3) − ⋯ = x log 2 + O(log x)` — IK (2.11). -/
def ChebyshevAlternatingSum : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
    |∑ m ∈ Icc 1 (Nat.floor x),
      (-1 : ℝ) ^ (m + 1) * Chebyshev.psi (x / m) - x * Real.log 2| ≤ C * Real.log x

/-- Chebyshev's lower bound: `ψ(x) ≥ x log 2 − C log x` — IK (2.12) lower. -/
def ChebyshevLowerBound : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    x * Real.log 2 - C * Real.log x ≤ Chebyshev.psi x

/-- Improved Chebyshev bounds with 30-periodic function — IK (2.13).
    `α = 1/2 log 2 + 1/3 log 3 + 1/5 log 5 − 1/30 log 30 ≈ 0.9212`. -/
def ChebyshevImprovedBounds : Prop :=
  let α := 1/2 * Real.log 2 + 1/3 * Real.log 3 + 1/5 * Real.log 5 - 1/30 * Real.log 30
  ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    α * x - C * Real.log x ≤ Chebyshev.psi x ∧
    Chebyshev.psi x ≤ 6/5 * α * x + C * Real.log x

/-- Mertens' first theorem: `∑_{n≤x} Λ(n)/n = log x + O(1)` — IK (2.14). -/
def MertensFirst : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
    |∑ n ∈ Icc 1 (Nat.floor x), Λ n / n - Real.log x| ≤ C

/-- Mertens' second theorem: `∑_{p≤x} 1/p = log log x + β + O(1/log x)` — IK (2.15). -/
def MertensSecond : Prop :=
  ∃ (β : ℝ) (C : ℝ), 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
    |∑ p ∈ (Icc 2 (Nat.floor x)).filter Nat.Prime,
      (1 : ℝ) / p - (Real.log (Real.log x) + β)| ≤ C / Real.log x

/-- Mertens' third theorem:
    `∏_{p≤x}(1 − 1/p) = e^{−γ}(log x)⁻¹(1 + O(1/log x))` — IK (2.16). -/
def MertensThird : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
    |∏ p ∈ (Icc 2 (Nat.floor x)).filter Nat.Prime,
      ((1 : ℝ) - 1 / p) -
      Real.exp (-Real.eulerMascheroniConstant) / Real.log x| ≤
    C / (Real.log x) ^ 2

/-- `∑_{m≤x} μ(m)⌊x/m⌋ = 1` for `x ≥ 1` — IK (2.17). -/
def MobiusFloorIdentity : Prop :=
  ∀ x : ℝ, 1 ≤ x →
    ∑ m ∈ Icc 1 (Nat.floor x), (μ m : ℤ) * (Nat.floor (x / m) : ℤ) = 1

/-- `|∑_{m≤x} μ(m)/m| ≤ 1` — IK (2.18). -/
def MobiusReciprocalBound : Prop :=
  ∀ x : ℝ, 1 ≤ x →
    |∑ m ∈ Icc 1 (Nat.floor x), (μ m : ℝ) / m| ≤ 1

end Tchebyshev

/-!
## §2.3 Primes in arithmetic progressions

Dirichlet's theorem on primes in arithmetic progressions.
-/

section PrimesInAP

/-- Dirichlet's theorem: infinitely many primes in any coprime residue class — IK §2.3.
    Bridges to Mathlib's `Nat.infinite_setOf_prime_and_eq_mod` /
    `Nat.forall_exists_prime_gt_and_eq_mod`. -/
def DirichletPrimesInAP : Prop :=
  ∀ (q : ℕ) (a : ℕ), 0 < q → Nat.Coprime a q →
    ∀ n : ℕ, ∃ p > n, p.Prime ∧ p % q = a % q

/-- Weighted PNT in arithmetic progressions:
    `∑_{n≤x, n≡a (mod q)} Λ(n)/n = (log x)/φ(q) + O(1)` — IK Theorem 2.2, (2.30). -/
def WeightedPNTinAP : Prop :=
  ∀ (q : ℕ) (a : ℕ), 1 < q → Nat.Coprime a q →
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |∑ n ∈ (Icc 1 (Nat.floor x)).filter (fun n => n % q = a % q),
        Λ n / n - Real.log x / Nat.totient q| ≤ C

/-- Primes equidistributed in residue classes — IK (2.25).
    `∑_{p≤x, p≡a (q)} p⁻ˢ = (1/φ(q)) log(1/(s−1)) + O(1)` as `s → 1⁺`. -/
def PrimesEquidistributedInAP : Prop :=
  ∀ (q : ℕ) (a : ℕ), 1 < q → Nat.Coprime a q →
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
      |∑ p ∈ ((Icc 2 (Nat.floor x)).filter Nat.Prime).filter (fun p => p % q = a % q),
        (1 : ℝ) / p - Real.log (Real.log x) / Nat.totient q| ≤ C

end PrimesInAP

/-!
## §2.4 Reflections on elementary proofs

Selberg's formula, higher von Mangoldt functions, and PNT error terms.
-/

section ElementaryProofs

/-- The `k`-th von Mangoldt function `Λ_k = μ ⋆ (log)^k`:
    `Λ_k(n) = ∑_{d|n} μ(d) (log(n/d))^k` — IK §2.4. -/
def vonMangoldtK (k : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => ∑ d ∈ n.divisors, (μ d : ℝ) * Real.log (↑(n / d)) ^ k,
   by simp [Nat.divisors_zero]⟩

/-- `Λ_2(n) = ∑_{d|n} μ(d)(log(n/d))²` — the function appearing in Selberg's formula. -/
theorem vonMangoldtK_two_apply {n : ℕ} :
    vonMangoldtK 2 n = ∑ d ∈ n.divisors, (μ d : ℝ) * Real.log (↑(n / d)) ^ 2 := rfl

/-- Selberg's formula:
    `∑_{p≤x} (log p)² + ∑_{pq≤x} (log p)(log q) = 2x log x + O(x)` — IK (2.32).
    Equivalently, `∑_{n≤x} Λ₂(n) = 2x log x + O(x)`. -/
def SelbergFormula : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
    |∑ n ∈ Icc 1 (Nat.floor x), vonMangoldtK 2 n - 2 * x * Real.log x| ≤ C * x

/-- Selberg's `Λ_k` formula:
    `∑_{n≤x} Λ_k(n) = k x (log x)^{k−1} (1 + O(1/log x))` — IK (2.33). -/
def SelbergLambdaK (k : ℕ) : Prop :=
  2 ≤ k → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
    |∑ n ∈ Icc 1 (Nat.floor x), vonMangoldtK k n -
      k * x * Real.log x ^ (k - 1)| ≤ C * x * Real.log x ^ (k - 2)

/-- Postnikov-Romanov inequality — IK (2.34). -/
def PostnikovRomanov : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
    |mobiusSummatory x| * Real.log x ≤
      ∑ n ∈ Icc 1 (Nat.floor x), |mobiusSummatory (x / n)| +
        C * x * Real.log (Real.log (3 * x))

/-- PNT with power-saving error:
    `ψ(x) = x + O(x(log x)^{−A})` for any `A > 0` — IK (2.35). -/
def PNT_PowerSaving : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
    ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.psi x - x| ≤ C * x * Real.log x ^ (-A)

/-- Diamond-Steinig PNT error bound — IK (2.36). -/
def PNT_DiamondSteinig : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    |Chebyshev.psi x - x| ≤
      x * Real.exp (-Real.log x ^ ((1 : ℝ) / 7) / (Real.log (Real.log x)) ^ 2)

/-- de la Vallée-Poussin PNT:
    `ψ(x) = x + O(x exp(−c√(log x)))` — IK (2.37). -/
def PNT_delaValleePoussin : Prop :=
  ∃ (c : ℝ) (C : ℝ), 0 < c ∧ 0 < C ∧
    ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.psi x - x| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))

/-- Korobov-Vinogradov PNT: best known error term — IK, see Corollary 8.31.
    `ψ(x) = x + O(x exp(−c(log x)^{3/5}(log log x)^{−1/5}))`. -/
def PNT_KorobovVinogradov : Prop :=
  ∃ (c : ℝ) (C : ℝ), 0 < c ∧ 0 < C ∧
    ∀ x : ℝ, 3 ≤ x →
      |Chebyshev.psi x - x| ≤
        C * x * Real.exp (-c * Real.log x ^ ((3 : ℝ) / 5) /
          (Real.log (Real.log x)) ^ ((1 : ℝ) / 5))

end ElementaryProofs

end IK

end
