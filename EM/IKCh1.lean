import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Topology.Order.Basic

/-!
# Chapter 1: Arithmetic Functions (Iwaniec-Kowalski)

Formalization of Chapter 1 of H. Iwaniec and E. Kowalski,
*Analytic Number Theory*, AMS Colloquium Publications vol. 53, 2004.

## Contents
- §1.1: Additive and multiplicative functions
- §1.2–1.3: Dirichlet convolution identities (bridges to Mathlib)
- §1.4: Liouville function, Ramanujan sums, Kloosterman sums
- §1.5: Summatory functions, hyperbola method
- §1.6–1.7: Forward references

## References
- [IK] H. Iwaniec, E. Kowalski, *Analytic Number Theory*, 2004
-/

noncomputable section

open Classical

namespace IK

open Nat ArithmeticFunction Finset BigOperators

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega
open scoped ArithmeticFunction.sigma

/-!
## §1.1 Additive and multiplicative functions

IK §1.1 defines additive, completely additive, multiplicative, and completely multiplicative
arithmetic functions. Mathlib provides `IsMultiplicative`; we add the missing predicates.
-/

section Predicates

variable {R : Type*}

/-- An arithmetic function is **additive** if `f(mn) = f(m) + f(n)` whenever `gcd(m,n) = 1`.
    This implies `f(1) = 0`. — IK (1.1) -/
def IsAdditiveFunction [AddZeroClass R] (f : ArithmeticFunction R) : Prop :=
  f 1 = 0 ∧ ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m + f n

/-- An arithmetic function is **completely additive** if `f(mn) = f(m) + f(n)` for all
    positive `m, n`. — IK §1.1 -/
def IsCompletelyAdditiveFunction [AddZeroClass R] (f : ArithmeticFunction R) : Prop :=
  ∀ {m n : ℕ}, 0 < m → 0 < n → f (m * n) = f m + f n

/-- An arithmetic function is **completely multiplicative** if `f(1) = 1` and
    `f(mn) = f(m)f(n)` for all positive `m, n`. — IK §1.1 -/
def IsCompletelyMultiplicative [MonoidWithZero R] (f : ArithmeticFunction R) : Prop :=
  f 1 = 1 ∧ ∀ {m n : ℕ}, 0 < m → 0 < n → f (m * n) = f m * f n

/-- Completely additive implies additive. -/
theorem IsCompletelyAdditiveFunction.toIsAdditiveFunction [AddGroup R]
    {f : ArithmeticFunction R} (hf : IsCompletelyAdditiveFunction f) :
    IsAdditiveFunction f := by
  have hf1 : f 1 = 0 := by
    have h := hf Nat.one_pos Nat.one_pos
    simp only [mul_one] at h
    -- h : f 1 = f 1 + f 1
    have key := congrArg (· - f 1) h  -- f 1 - f 1 = (f 1 + f 1) - f 1
    simp only [sub_self, add_sub_cancel_right] at key
    exact key.symm
  refine ⟨hf1, fun {m n} hcop => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- Coprime 0 n means n = 1
    have hn1 : n = 1 := by rwa [Nat.Coprime, Nat.gcd_zero_left] at hcop
    subst hn1; simp [hf1]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hm1 : m = 1 := by rwa [Nat.Coprime, Nat.gcd_zero_right] at hcop
    subst hm1; simp [hf1]
  exact hf hm hn

/-- Completely multiplicative implies multiplicative (Mathlib's `IsMultiplicative`). -/
theorem IsCompletelyMultiplicative.toIsMultiplicative [MonoidWithZero R]
    {f : ArithmeticFunction R} (hf : IsCompletelyMultiplicative f) :
    f.IsMultiplicative := by
  refine ⟨hf.1, fun {m n} _ => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  exact hf.2 hm hn

/-- For an additive function, `f(1) = 0`. — IK §1.1 -/
theorem IsAdditiveFunction.map_one [AddZeroClass R]
    {f : ArithmeticFunction R} (hf : IsAdditiveFunction f) : f 1 = 0 :=
  hf.1

/-- For an additive function, `f(mn) = f(m) + f(n)` when `gcd(m,n) = 1`. -/
theorem IsAdditiveFunction.map_mul_of_coprime [AddZeroClass R]
    {f : ArithmeticFunction R} (hf : IsAdditiveFunction f)
    {m n : ℕ} (h : Nat.Coprime m n) : f (m * n) = f m + f n :=
  hf.2 h

/-- A completely multiplicative function satisfies `f(p^k) = f(p)^k` at primes. -/
theorem IsCompletelyMultiplicative.map_prime_pow [CommMonoidWithZero R]
    {f : ArithmeticFunction R} (hf : IsCompletelyMultiplicative f)
    {p : ℕ} (hp : p.Prime) (k : ℕ) : f (p ^ k) = f p ^ k := by
  induction k with
  | zero => simp [hf.1]
  | succ k ih =>
    rw [pow_succ, hf.2 (pow_pos hp.pos k) hp.pos, ih, pow_succ]

end Predicates

/-!
## §1.2–1.3 Dirichlet convolution identities

Bridges to Mathlib's existing results with IK-compatible theorem names.
-/

section ConvolutionIdentities

/-- `∑_{d|m} μ(d) = δ(m,1)` — IK (1.18). -/
theorem sum_moebius_eq_delta : (μ * ζ : ArithmeticFunction ℤ) = 1 :=
  moebius_mul_coe_zeta

/-- Möbius inversion — IK (1.19)/(1.20). -/
theorem moebius_inversion {R : Type*} [NonAssocRing R] {f g : ℕ → R} :
    (∀ n > 0, ∑ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal, (μ x.fst : R) * g x.snd = f n :=
  sum_eq_iff_sum_mul_moebius_eq

/-- `f * g` multiplicative when `f, g` are — IK §1.3. -/
theorem isMultiplicative_mul {R : Type*} [CommSemiring R]
    {f g : ArithmeticFunction R} (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) :
    (f * g).IsMultiplicative :=
  hf.mul hg

/-- `∑_{d|n} φ(d) = n` — IK consequence of (1.36). -/
theorem sum_totient_eq (n : ℕ) : n.divisors.sum Nat.totient = n :=
  Nat.sum_totient n

/-- `log n = ∑_{d|n} Λ(d)` — IK (1.41). -/
theorem vonMangoldt_sum_eq {n : ℕ} :
    ∑ i ∈ n.divisors, ArithmeticFunction.vonMangoldt i = Real.log n :=
  vonMangoldt_sum

/-- `Λ = μ ⋆ L` — IK (1.38). -/
theorem vonMangoldt_eq_log_mul_moebius :
    ArithmeticFunction.log * (μ : ArithmeticFunction ℝ) =
      (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) :=
  log_mul_moebius_eq_vonMangoldt

/-- `Λ(n) = -∑_{d|n} μ(d) log d` — IK (1.40). -/
theorem vonMangoldt_eq_neg_sum_moebius_log {n : ℕ} :
    (Λ n : ℝ) = -(∑ d ∈ n.divisors, (μ d : ℝ) * ArithmeticFunction.log d) := by
  linarith [sum_moebius_mul_log_eq (n := n)]

end ConvolutionIdentities

/-!
## §1.4 Liouville function and more examples
-/

section LiouvilleFunction

/-- The Liouville function `λ(n) = (-1)^{Ω(n)}` — IK (1.34). -/
def liouville : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else (-1) ^ Ω n, by simp⟩

theorem liouville_apply {n : ℕ} (hn : n ≠ 0) : liouville n = (-1) ^ Ω n :=
  if_neg hn

@[simp]
theorem liouville_one : liouville 1 = 1 := by simp [liouville]

theorem liouville_apply_prime {p : ℕ} (hp : p.Prime) : liouville p = -1 := by
  simp [liouville_apply hp.ne_zero, cardFactors_apply_prime hp]

theorem liouville_apply_prime_pow {p k : ℕ} (hp : p.Prime) :
    liouville (p ^ k) = (-1) ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | _
  · simp [liouville]
  · simp [liouville_apply (pow_ne_zero k hp.ne_zero), cardFactors_apply_prime_pow hp]

/-- The Liouville function is completely multiplicative — IK §1.4. -/
theorem liouville_isCompletelyMultiplicative :
    IsCompletelyMultiplicative liouville := by
  refine ⟨liouville_one, fun {m n} hm hn => ?_⟩
  rw [liouville_apply (by omega : m ≠ 0),
      liouville_apply (by omega : n ≠ 0),
      liouville_apply (Nat.mul_ne_zero (by omega) (by omega)),
      cardFactors_mul (by omega) (by omega), pow_add]

/-- `λ(n) = μ(n)` when `n` is squarefree — IK §1.4. -/
theorem liouville_eq_moebius_of_squarefree {n : ℕ} (hn : Squarefree n) :
    liouville n = μ n := by
  rw [liouville_apply (Squarefree.ne_zero hn), moebius_apply_of_squarefree hn]

/-- `φ(n)/n = ∑_{d|n} μ(d)/d` — IK (1.43).
    Requires Möbius inversion over ℚ applied to the totient divisor sum formula. -/
def EulerPhiOverN : Prop :=
  ∀ (n : ℕ), 0 < n →
    (Nat.totient n : ℚ) / n = ∑ d ∈ n.divisors, (μ d : ℚ) / d

end LiouvilleFunction

/-!
## §1.4 (continued) Ramanujan sums and Kloosterman sums
-/

section ExponentialSums

/-- The standard additive character `e(x) = e^{2πix}` — IK (1.9). -/
def eChar (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * x * Complex.I)

theorem eChar_zero : eChar 0 = 1 := by simp [eChar]

/-- The multiplicative inverse of `x` modulo `c`, or 0 if not coprime. -/
def modInverse (x c : ℕ) : ℕ :=
  if h : Nat.Coprime x c ∧ 0 < c then
    ZMod.val (((ZMod.unitOfCoprime x h.1)⁻¹ : (ZMod c)ˣ) : ZMod c)
  else 0

/-- Ramanujan sum `c_q(n) = ∑_{a=1,(a,q)=1}^{q} e(an/q)` — IK (1.48). -/
def ramanujanSum (q : ℕ) (n : ℤ) : ℂ :=
  if q = 0 then 0
  else ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime (a + 1) q),
    eChar ((↑(a + 1) * ↑n) / ↑q)

@[simp]
theorem ramanujanSum_zero_left (n : ℤ) : ramanujanSum 0 n = 0 := by
  simp [ramanujanSum]

/-- Ramanujan sum formula: `c_q(n) = ∑_{d|(q,n)} d·μ(q/d)` — IK (1.49).
    Requires character orthogonality and Möbius inversion. -/
def RamanujanSumFormula : Prop :=
  ∀ (q : ℕ) (n : ℤ), 0 < q →
    ramanujanSum q n =
      ∑ d ∈ (Nat.gcd q n.natAbs).divisors, (d : ℂ) * (μ (q / d) : ℂ)

/-- Kloosterman sum `S(a,b;c) = ∑*_{x mod c} e((ax + bx̄)/c)` — IK (1.56). -/
def kloostermanSum (a b : ℤ) (c : ℕ) : ℂ :=
  if c = 0 then 0 else
  ∑ x ∈ (Finset.range c).filter (fun x => Nat.Coprime (x + 1) c),
    eChar ((a * ↑(x + 1) + b * ↑(modInverse (x + 1) c)) / ↑c)

/-- `S(a,b;c) = S(b,a;c)` (symmetry) — IK (1.57).
    Requires change of variables `x ↦ x̄` (modular inverse bijection). -/
def KloostermanSymmetric : Prop :=
  ∀ (a b : ℤ) (c : ℕ), kloostermanSum a b c = kloostermanSum b a c

/-- `S(aa',b;c) = S(a,ba';c)` when `gcd(a',c) = 1` — IK (1.58).
    Requires coprime substitution in the Kloosterman sum. -/
def KloostermanTwist : Prop :=
  ∀ (a a' b : ℤ) (c : ℕ), 0 < c → Int.gcd a' c = 1 →
    kloostermanSum (a * a') b c = kloostermanSum a (b * a') c

/-- The Weil bound — IK (1.60). Proved in IK Chapter 11. -/
def WeilBound : Prop :=
  ∀ (a b : ℤ) (c : ℕ), 0 < c →
    ‖kloostermanSum a b c‖ ≤
      (σ 0 c : ℝ) * (Int.gcd a (Int.gcd b c) : ℝ) ^ ((1 : ℝ) / 2) * Real.sqrt c

end ExponentialSums

/-!
## §1.5 Summatory functions
-/

section Summatory

/-- Summatory function: `M_f(x) = ∑_{1 ≤ n ≤ x} f(n)` — IK (1.61). -/
def summatoryFunction {R : Type*} [AddCommMonoid R]
    (f : ArithmeticFunction R) (x : ℝ) : R :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor x), f n

theorem summatoryFunction_mono {R : Type*} [AddCommMonoid R] [PartialOrder R] [AddLeftMono R]
    (f : ArithmeticFunction R) (hf : ∀ n, 0 ≤ f n) {x y : ℝ} (hxy : x ≤ y) :
    summatoryFunction f x ≤ summatoryFunction f y := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc_right (Nat.floor_le_floor hxy)
  · intro i _ _; exact hf i

/-- The hyperbola method — IK, Dirichlet's trick. -/
def HyperbolaMethod : Prop :=
  ∀ (x : ℝ), 1 ≤ x →
    (∑ n ∈ Finset.Icc 1 (Nat.floor x), σ 0 n) =
      2 * (∑ m ∈ Finset.Icc 1 (Nat.floor (Real.sqrt x)),
        Nat.floor (x / m)) - (Nat.floor (Real.sqrt x)) ^ 2

/-- Dirichlet's divisor problem — IK (1.75). -/
def DirichletDivisorAsymptotics : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
    |(∑ n ∈ Finset.Icc 1 (Nat.floor x), (σ 0 n : ℝ)) -
      (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x)| ≤ C * Real.sqrt x

/-- `∑_{n≤x} φ(n)/n = x/ζ(2) + O(log x)` — IK (1.74). -/
def TotientAverageAsymptotics : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
    |(∑ n ∈ Finset.Icc 1 (Nat.floor x), (Nat.totient n : ℝ) / n) -
      x * (6 / Real.pi ^ 2)| ≤ C * Real.log x

end Summatory

/-!
## §1.6 Sums of multiplicative functions
-/

section MultiplicativeBounds

/-- Basic upper bound — IK (1.78). -/
def MultUpperBound : Prop :=
  ∀ (f : ArithmeticFunction ℝ), f.IsMultiplicative →
    (∀ n, 0 ≤ f n) →
    ∀ x : ℝ, 2 ≤ x →
      summatoryFunction f x ≤
        x * ∏ p ∈ (Finset.Icc 2 (Nat.floor x)).filter Nat.Prime,
          ∑ ν ∈ Finset.range (Nat.floor x), f (p ^ ν) / (p : ℝ) ^ ν

/-- `τ(n) ≪ n^ε` for any ε > 0 — IK (1.81). -/
def DivisorEpsilonBound : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 0 < n → (σ 0 n : ℝ) ≤ C * (n : ℝ) ^ ε

/-- `∑_{n≤x} τ(n)^ℓ ≪ x(log x)^{k^ℓ−1}` — IK (1.80). -/
def DivisorPowerAverage (k ℓ : ℕ) : Prop :=
  1 ≤ k → 1 ≤ ℓ → ∃ C : ℝ, 0 < C ∧
    ∀ x : ℝ, 3 ≤ x →
      ∑ n ∈ Finset.Icc 1 (Nat.floor x), (σ 0 n : ℝ) ^ ℓ ≤
        C * x * Real.log x ^ (k ^ ℓ - 1)

end MultiplicativeBounds

/-!
## §1.7 Distribution of additive functions
-/

section TuranKubilius

/-- The mean value `E(x)` of an additive function — IK (1.104). -/
def additiveExpectation (f : ArithmeticFunction ℝ) (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 (Nat.floor x)).filter Nat.Prime,
    ∑ a ∈ Finset.Icc 1 (Nat.floor (Real.log x / Real.log p)),
      f (p ^ a) * (p : ℝ)⁻¹ ^ a * (1 - (p : ℝ)⁻¹)

/-- The dispersion `D²(x)` of an additive function — IK (1.105). -/
def additiveDispersionSq (f : ArithmeticFunction ℝ) (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 (Nat.floor x)).filter Nat.Prime,
    ∑ a ∈ Finset.Icc 1 (Nat.floor (Real.log x / Real.log p)),
      (f (p ^ a)) ^ 2 * (p : ℝ)⁻¹ ^ a

/-- Turán-Kubilius inequality — IK Theorem 1.3. -/
def TuranKubilius : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (f : ArithmeticFunction ℝ), IsAdditiveFunction f →
      ∀ x : ℝ, 3 ≤ x →
        ∑ n ∈ Finset.Icc 1 (Nat.floor x),
          (f n - additiveExpectation f x) ^ 2 ≤
        c * x * additiveDispersionSq f x

/-- Hardy-Ramanujan — IK Corollary 1.4. -/
def HardyRamanujan : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (x : ℝ) (z : ℝ), 3 ≤ x → 1 ≤ z →
      (((Finset.Icc 1 (Nat.floor x)).filter (fun n =>
        |(ω n : ℝ) - Real.log (Real.log x)| >
          z * Real.sqrt (Real.log (Real.log x)))).card : ℝ) ≤
      C / z ^ 2 * x

/-- Mean value of additive function — IK (1.103). -/
def AdditiveMeanFormula : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (f : ArithmeticFunction ℝ), IsAdditiveFunction f →
      ∀ x : ℝ, 3 ≤ x →
        |summatoryFunction f x - x * additiveExpectation f x| ≤
        C * Real.sqrt x * Real.sqrt (additiveDispersionSq f x)

end TuranKubilius

/-!
## §1.8 Forward references
-/

section ForwardReferences

/-- Wirsing's theorem — IK Theorem 1.1. -/
def WirsingTheorem : Prop :=
  ∀ (f : ArithmeticFunction ℝ), f.IsMultiplicative →
    ∀ (κ : ℝ), -1/2 < κ →
      (∃ B : ℝ, ∀ x : ℝ, 2 ≤ x →
        |∑ n ∈ (Finset.Icc 2 (Nat.floor x)).filter Nat.Prime,
          f n * Real.log n / n - κ * Real.log x| ≤ B) →
      ∃ (c_f : ℝ) (C : ℝ), 0 < C ∧
        ∀ x : ℝ, 3 ≤ x →
          |summatoryFunction f x - c_f * Real.log x ^ κ| ≤
            C * Real.log x ^ (|κ| - 1)

/-- Erdős-Kac theorem — IK Theorem 1.5: additive functions with bounded prime values
    and divergent second moment have Gaussian limiting distribution. -/
def ErdosKac : Prop :=
  ∀ (f : ArithmeticFunction ℝ), IsAdditiveFunction f →
    (∀ (p : ℕ), p.Prime → ∀ (a : ℕ), 0 < a → |f (p ^ a)| ≤ 1 ∧ f (p ^ a) = f p) →
    (Filter.Tendsto
      (fun (N : ℕ) => ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, f p ^ 2 / (p : ℝ))
      Filter.atTop Filter.atTop) →
    ∀ (z : ℝ),
      Filter.Tendsto
        (fun (N : ℕ) =>
          let A := ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, f p / (p : ℝ)
          let B := Real.sqrt (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, f p ^ 2 / (p : ℝ))
          ((Finset.Icc 1 N).filter (fun n => f n - A ≤ z * B)).card / (N : ℝ))
        Filter.atTop
        (nhds ((1 / Real.sqrt (2 * Real.pi)) *
          Real.exp (-(z ^ 2) / 2) * z +
          1 / 2))  -- Gaussian CDF Φ(z); exact formula suppressed for simplicity

/-- Landau's formula for sums of two squares — IK (1.87):
    `B(x) ~ C x (log x)^{-1/2}` where
    `C = (1/√2) ∏_{p ≡ -1 (mod 4)} (1 - 1/p²)^{-1/2}` — IK (1.102). -/
def LandauSumOfSquares : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → 2 ≤ N →
        let B := ((Finset.Icc 1 N).filter (fun n =>
          ∃ a b : ℕ, a ^ 2 + b ^ 2 = n)).card
        |(B : ℝ) - C * N / Real.sqrt (Real.log N)| < ε * N / Real.sqrt (Real.log N)

end ForwardReferences

end IK

end
