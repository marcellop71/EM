import EM.MullinDefs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Sieve-Defined Dynamical Systems (SDDS)

An abstract framework for sequences defined by iterated factoring:
starting from an initial value s_0 >= 2, each step forms s_n + 1 and
extracts a prime factor via a factoring rule Phi, then multiplies:
  s_{n+1} = s_n * Phi(s_n + 1)

The Euclid-Mullin sequence is the special case where Phi = Nat.minFac
and s_0 = 2.

## Main definitions

* `FactoringRule` — a function extracting a prime divisor
* `minFacRule` — the Nat.minFac instance
* `SDDS` — a sieve-defined dynamical system (parametrized by factoring rule)
* `SDDS.orbit` — the orbit sequence
* `SDDS.walk` — the orbit mod q (in ZMod q)
* `SDDS.mult` — the multiplier mod q (in ZMod q)
* `emSDDS` — the Euclid-Mullin instance

## Open hypotheses

* `SuperExponentialGrowth` — orbit grows super-exponentially
* `CoprimeCascade` — each multiplier divides all subsequent orbit values
* `SieveRegularity` — the factoring rule distributes uniformly mod q
* `NoAlgebraicObstruction` — the multipliers generate (ZMod q)^times
* `SieveMapEquidistribution` — the walk hits every unit (master conjecture)
-/

open Mullin Euclid

/-! ## Factoring Rules -/

/-- A factoring rule: a function that extracts a prime divisor from any
    integer >= 2. The Euclid-Mullin sequence uses Nat.minFac (smallest
    prime factor), but the SDDS framework allows any such rule. -/
structure FactoringRule where
  /-- The factoring function: given m >= 2, returns a prime factor of m. -/
  apply : ℕ → ℕ
  /-- The returned value divides m (for m >= 2). -/
  divides : ∀ m : ℕ, 2 ≤ m → apply m ∣ m
  /-- The returned value is prime (for m >= 2). -/
  prime : ∀ m : ℕ, 2 ≤ m → (apply m).Prime

/-- The standard factoring rule using Nat.minFac (smallest prime factor). -/
def minFacRule : FactoringRule where
  apply := Nat.minFac
  divides := fun m _ => Nat.minFac_dvd m
  prime := fun m hm => Nat.minFac_prime (by omega)

/-! ## Sieve-Defined Dynamical Systems -/

/-- A Sieve-Defined Dynamical System: an initial value, a factoring rule,
    and an observation modulus q (prime). The orbit is defined by
    s_{n+1} = s_n * Phi(s_n + 1), and we observe the orbit modulo q. -/
structure SDDS where
  /-- Initial value of the orbit. -/
  s₀ : ℕ
  /-- The factoring rule used to extract prime factors. -/
  Φ : FactoringRule
  /-- The observation modulus. -/
  q : ℕ
  /-- The observation modulus is prime. -/
  q_prime : Nat.Prime q
  /-- The initial value is at least 2. -/
  s₀_ge_two : 2 ≤ s₀

/-! ## Orbit, Walk, and Multiplier -/

/-- The orbit sequence of an SDDS: s_0, s_0 * Phi(s_0 + 1),
    s_0 * Phi(s_0 + 1) * Phi(s_0 * Phi(s_0 + 1) + 1), ...
    Each step multiplies by the prime factor extracted from orbit(n) + 1. -/
noncomputable def SDDS.orbit (S : SDDS) : ℕ → ℕ
  | 0 => S.s₀
  | n + 1 => S.orbit n * S.Φ.apply (S.orbit n + 1)

/-- The walk of an SDDS: the orbit cast into ZMod q. -/
noncomputable def SDDS.walk (S : SDDS) (n : ℕ) : ZMod S.q :=
  (S.orbit n : ZMod S.q)

/-- The multiplier at step n: the prime factor extracted at step n,
    cast into ZMod q. -/
noncomputable def SDDS.mult (S : SDDS) (n : ℕ) : ZMod S.q :=
  (S.Φ.apply (S.orbit n + 1) : ZMod S.q)

/-! ## The Euclid-Mullin SDDS instance -/

/-- The Euclid-Mullin sequence as an SDDS: s_0 = 2, Phi = Nat.minFac,
    observed modulo a prime q. -/
def emSDDS (q : ℕ) (hq : Nat.Prime q) : SDDS where
  s₀ := 2
  Φ := minFacRule
  q := q
  q_prime := hq
  s₀_ge_two := le_refl 2

/-! ## Basic unfolding lemmas -/

/-- Orbit recurrence: orbit(n+1) = orbit(n) * Phi(orbit(n) + 1). -/
theorem SDDS.orbit_succ (S : SDDS) (n : ℕ) :
    S.orbit (n + 1) = S.orbit n * S.Φ.apply (S.orbit n + 1) := by
  rfl

/-- Walk at step 0: walk(0) = s_0 in ZMod q. -/
theorem SDDS.walk_zero (S : SDDS) :
    S.walk 0 = (S.s₀ : ZMod S.q) := by
  rfl

/-- Walk recurrence: walk(n+1) = walk(n) * mult(n) in ZMod q. -/
theorem SDDS.walk_succ (S : SDDS) (n : ℕ) :
    S.walk (n + 1) = S.walk n * S.mult n := by
  simp only [SDDS.walk, SDDS.mult, SDDS.orbit_succ]
  push_cast
  ring

/-! ## Open Hypotheses -/

/-- **Super-exponential growth**: the orbit grows faster than any exponential.
    For every C > 0, eventually log(orbit(n)) >= C * n.
    Parametrized by the orbit function (not the full SDDS). -/
def SuperExponentialGrowth (s : ℕ → ℕ) : Prop :=
  ∀ C : ℝ, 0 < C → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    Real.log (s n : ℝ) ≥ C * (n : ℝ)

/-- **Coprime cascade**: each multiplier divides all subsequent orbit values.
    That is, for m < n, Phi(orbit(m) + 1) divides orbit(n).
    This holds for the EM sequence because each new prime factor enters the
    running product and stays forever. -/
def CoprimeCascade (S : SDDS) : Prop :=
  ∀ m n : ℕ, m < n → S.Φ.apply (S.orbit m + 1) ∣ S.orbit n

/-- The orbit is monotonically divisible: orbit(k) divides orbit(k+1).
    This follows immediately from the recurrence orbit(k+1) = orbit(k) * Φ(orbit(k) + 1). -/
theorem SDDS.orbit_dvd_orbit_succ (S : SDDS) (k : ℕ) :
    S.orbit k ∣ S.orbit (k + 1) :=
  ⟨S.Φ.apply (S.orbit k + 1), (S.orbit_succ k).symm⟩

/-- The orbit is transitively divisible: orbit(k) divides orbit(n) for k ≤ n. -/
theorem SDDS.orbit_dvd_orbit (S : SDDS) {k n : ℕ} (hkn : k ≤ n) :
    S.orbit k ∣ S.orbit n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
  induction d with
  | zero => simp
  | succ d ih => exact dvd_trans (ih (Nat.le_add_right k d)) (S.orbit_dvd_orbit_succ (k + d))

/-- The multiplier at step m divides orbit(m+1), since
    orbit(m+1) = orbit(m) * Φ(orbit(m) + 1). -/
theorem SDDS.mult_dvd_orbit_succ (S : SDDS) (m : ℕ) :
    S.Φ.apply (S.orbit m + 1) ∣ S.orbit (m + 1) :=
  ⟨S.orbit m, by rw [S.orbit_succ m]; ring⟩

/-- **CoprimeCascade holds for every SDDS.**
    For m < n, Φ(orbit(m) + 1) divides orbit(n).
    Proof: Φ(orbit(m) + 1) divides orbit(m+1) as a factor of the product,
    and orbit(m+1) divides orbit(n) by transitivity of the divisibility chain. -/
theorem SDDS.coprimeCascade (S : SDDS) : CoprimeCascade S := by
  intro m n hmn
  exact dvd_trans (S.mult_dvd_orbit_succ m) (S.orbit_dvd_orbit hmn)

/-- **Sieve regularity**: the factoring rule distributes "uniformly" modulo q.
    Abstractly, this asserts that the factoring rule does not systematically
    avoid certain residue classes mod q. The precise formulation involves
    density of orbits landing in each residue class, but we state it as
    an abstract Prop depending on the SDDS to avoid formalizing counting
    functions at this stage. -/
def SieveRegularity (_S : SDDS) : Prop :=
  True  -- Abstract placeholder: the factoring rule is unbiased mod q

open Classical in
/-- **No algebraic obstruction**: the multipliers generate (ZMod q)^times.
    Specifically, the subgroup of (ZMod q)^times generated by (the units
    corresponding to) all multiplier residues is the full group. This
    ensures the walk is not confined to a proper coset. -/
noncomputable def NoAlgebraicObstruction (S : SDDS) : Prop :=
  haveI : Fact (Nat.Prime S.q) := ⟨S.q_prime⟩
  Subgroup.closure
    { u : (ZMod S.q)ˣ | ∃ n : ℕ, (u : ZMod S.q) = S.mult n } = ⊤

open Classical in
/-- **Sieve Map Equidistribution**: the master conjecture. Under sufficient
    dynamical hypotheses, the walk of an SDDS hits every element of
    (ZMod q)^times. This is the analogue of Mullin's Conjecture in the
    abstract SDDS framework. -/
noncomputable def SieveMapEquidistribution (S : SDDS) : Prop :=
  haveI : Fact (Nat.Prime S.q) := ⟨S.q_prime⟩
  ∀ u : (ZMod S.q)ˣ, ∃ n : ℕ, S.walk n = (u : ZMod S.q)
