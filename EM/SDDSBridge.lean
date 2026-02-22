import EM.SieveDefinedDynamics
import EM.MullinGroupCore

/-!
# Bridge: SDDS Framework to Euclid-Mullin Sequence

This file connects the abstract SDDS framework (which uses Mathlib's
`Nat.minFac`) to the existing Euclid-Mullin formalization (which uses
the project's custom `Euclid.minFac`).

## Main results

* `euclid_minFac_eq_nat_minFac` — the two minFac implementations agree
  for n >= 2
* `emSDDS_orbit_eq_prod` — the EM SDDS orbit equals `Mullin.prod`
* `emSDDS_walk_eq_walkZ` — the EM SDDS walk equals `MullinGroup.walkZ`
* `emSDDS_mult_eq_multZ` — the EM SDDS mult equals `MullinGroup.multZ`
-/

open Mullin Euclid MullinGroup

/-! ## MinFac equivalence

Both `Euclid.minFac` and `Nat.minFac` compute the smallest prime factor.
We prove they agree for n >= 2 using their shared minimality properties:
- Both divide n
- Both are >= 2
- Both are <= every other factor >= 2
-/

/-- The two minFac implementations agree for n >= 2.

`Euclid.minFac` is defined in the project's constructive Euclid module;
`Nat.minFac` is Mathlib's version. Both return the smallest factor >= 2.
We prove equality via antisymmetry of their minimality properties. -/
theorem euclid_minFac_eq_nat_minFac (n : ℕ) (hn : 2 ≤ n) :
    Euclid.minFac n = Nat.minFac n := by
  apply Nat.le_antisymm
  · -- Euclid.minFac n <= Nat.minFac n
    -- Nat.minFac n divides n and is >= 2 (since it's prime for n >= 2)
    have h_prime : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
    have h_dvd : Nat.minFac n ∣ n := Nat.minFac_dvd n
    have h_ge : 2 ≤ Nat.minFac n := h_prime.two_le
    exact Euclid.minFac_min' n (Nat.minFac n) hn h_ge h_dvd
  · -- Nat.minFac n <= Euclid.minFac n
    -- Euclid.minFac n divides n and is >= 2
    have h_dvd : Euclid.minFac n ∣ n := Euclid.minFac_dvd n hn
    have h_ge : 2 ≤ Euclid.minFac n := Euclid.two_le_minFac n hn
    exact Nat.minFac_le_of_dvd h_ge h_dvd

/-! ## Orbit-Product bridge

The EM SDDS orbit (using `Nat.minFac`) equals `Mullin.prod` (using
`Euclid.minFac`). Both satisfy the same recurrence with the same
initial condition, and the two minFac functions agree.
-/

/-- The orbit of the EM SDDS at step n is at least 2.
    This mirrors `Mullin.prod_ge_two`. -/
theorem emSDDS_orbit_ge_two (q : ℕ) (hq : Nat.Prime q) (n : ℕ) :
    2 ≤ (emSDDS q hq).orbit n := by
  induction n with
  | zero => simp [SDDS.orbit, emSDDS]
  | succ n ih =>
    simp only [SDDS.orbit]
    have h1 : 1 ≤ (emSDDS q hq).Φ.apply ((emSDDS q hq).orbit n + 1) := by
      have hp := (emSDDS q hq).Φ.prime ((emSDDS q hq).orbit n + 1) (by omega)
      exact Nat.one_le_iff_ne_zero.mpr hp.ne_zero
    calc 2 ≤ (emSDDS q hq).orbit n := ih
      _ = (emSDDS q hq).orbit n * 1 := (Nat.mul_one _).symm
      _ ≤ (emSDDS q hq).orbit n *
            (emSDDS q hq).Φ.apply ((emSDDS q hq).orbit n + 1) :=
          Nat.mul_le_mul_left _ h1

/-- The orbit of the EM SDDS equals `Mullin.prod`.

Proved by induction:
- Base: orbit(0) = 2 = prod(0)
- Step: orbit(n+1) = orbit(n) * Nat.minFac(orbit(n) + 1)
        = prod(n) * Nat.minFac(prod(n) + 1)      (by IH)
        = prod(n) * Euclid.minFac(prod(n) + 1)    (by minFac agreement)
        = prod(n) * seq(n+1)                       (by seq_succ)
        = prod(n+1)                                (by prod_succ)
-/
theorem emSDDS_orbit_eq_prod (q : ℕ) (hq : Nat.Prime q) (n : ℕ) :
    (emSDDS q hq).orbit n = Mullin.prod n := by
  induction n with
  | zero =>
    -- orbit(0) = 2 = prod(0)
    simp [SDDS.orbit, emSDDS, Mullin.prod_zero]
  | succ n ih =>
    -- orbit(n+1) = orbit(n) * Nat.minFac(orbit(n) + 1)
    simp only [SDDS.orbit]
    -- Rewrite orbit(n) = prod(n) using IH
    rw [ih]
    -- Now need: prod(n) * Nat.minFac(prod(n) + 1) = prod(n+1)
    -- First, Nat.minFac = Euclid.minFac for prod(n) + 1 >= 3 >= 2
    have h_ge : 2 ≤ Mullin.prod n + 1 := by
      have := Mullin.prod_ge_two n; omega
    rw [show (emSDDS q hq).Φ.apply (Mullin.prod n + 1) =
            Nat.minFac (Mullin.prod n + 1) from rfl]
    rw [← euclid_minFac_eq_nat_minFac _ h_ge]
    -- Now: prod(n) * Euclid.minFac(prod(n) + 1) = prod(n+1)
    rw [← Mullin.seq_succ]
    rw [← Mullin.prod_succ]

/-- The walk of the EM SDDS equals `MullinGroup.walkZ`.

walkZ is defined as `(Mullin.prod n : ZMod q)`, and the SDDS walk
is `(orbit n : ZMod q)`. Since orbit = prod, these are equal. -/
theorem emSDDS_walk_eq_walkZ (q : ℕ) (hq : Nat.Prime q) (n : ℕ) :
    (emSDDS q hq).walk n = MullinGroup.walkZ q n := by
  simp only [SDDS.walk, MullinGroup.walkZ, emSDDS_orbit_eq_prod]

/-- The multiplier of the EM SDDS equals `MullinGroup.multZ`.

multZ is defined as `(Mullin.seq (n+1) : ZMod q)`, and the SDDS mult
is `(Phi.apply(orbit(n) + 1) : ZMod q) = (Nat.minFac(prod(n) + 1) : ZMod q)`.
Since Nat.minFac(prod(n)+1) = Euclid.minFac(prod(n)+1) = seq(n+1), equal. -/
theorem emSDDS_mult_eq_multZ (q : ℕ) (hq : Nat.Prime q) (n : ℕ) :
    (emSDDS q hq).mult n = MullinGroup.multZ q n := by
  simp only [SDDS.mult, MullinGroup.multZ]
  congr 1
  -- Need: Nat.minFac(orbit(n) + 1) = seq(n+1)
  rw [emSDDS_orbit_eq_prod]
  have h_ge : 2 ≤ Mullin.prod n + 1 := by
    have := Mullin.prod_ge_two n; omega
  rw [show (emSDDS q hq).Φ.apply (Mullin.prod n + 1) =
          Nat.minFac (Mullin.prod n + 1) from rfl]
  rw [← euclid_minFac_eq_nat_minFac _ h_ge]
  exact (Mullin.seq_succ n).symm

/-! ## SME implies walk hits -1

If SieveMapEquidistribution holds for the EM SDDS, then the walk hits
every unit mod q, including -1. This connects to the existing
infrastructure for proving MC.
-/

open Classical in
/-- If SME holds for the EM SDDS at prime q, then `walkZ q` hits -1.
    This is the key bridge: SME gives every unit is hit, and -1 is a unit
    when q is an odd prime. -/
theorem sme_implies_walkZ_hits_neg_one (q : ℕ) (hq : Nat.Prime q)
    [Fact (Nat.Prime q)]
    (hsme : SieveMapEquidistribution (emSDDS q hq)) :
    ∃ n : ℕ, MullinGroup.walkZ q n = -1 := by
  -- -1 is a unit in ZMod q (for prime q): (-1) * (-1) = 1
  let u : (ZMod q)ˣ := Units.mkOfMulEqOne (-1) (-1) (by ring)
  -- Apply SME to get n with walk(n) = (u : ZMod q) = -1
  obtain ⟨n, hn⟩ := hsme u
  exact ⟨n, by rwa [emSDDS_walk_eq_walkZ] at hn⟩
