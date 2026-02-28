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

/-! ## Super-exponential growth of Mullin.prod

The running product `prod(n)` grows faster than any exponential.
Since `seq` is injective with values in the primes (all ≥ 2),
for any bound M, at most M-1 values of `seq` fall in {2,...,M}.
The remaining factors are all > M, so `prod(n)` eventually grows
at least as `(M+1)^n` (up to a bounded correction). Since M is
arbitrary, `log(prod(n))/n → ∞`.
-/

section SuperExponentialGrowth

open Real

/-- The set of indices where `seq` takes a specific value has at most one element. -/
private theorem seq_fiber_finite (v : ℕ) : (Set.Finite {n : ℕ | seq n = v}) := by
  by_cases h : ∃ n, seq n = v
  · obtain ⟨n, hn⟩ := h
    apply Set.Finite.subset (Set.finite_singleton n)
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    simp only [Set.mem_singleton_iff]
    exact seq_injective m n (by rw [hm, hn])
  · push_neg at h
    convert Set.finite_empty (α := ℕ)
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact h n

/-- The set of indices where `seq` takes a value ≤ M is finite.
    Since `seq` is injective, at most M-1 indices map to {2,...,M}. -/
private theorem seq_bounded_indices_finite (M : ℕ) :
    Set.Finite {n : ℕ | seq n ≤ M} := by
  apply Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iio (M + 1))
    (fun v _ => seq_fiber_finite v))
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  simp only [Set.mem_iUnion]
  exact ⟨seq n, Set.mem_Iio.mpr (by omega), rfl⟩

/-- For any M, there exists n₀ such that seq(n) > M for all n > n₀. -/
private theorem seq_eventually_gt (M : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ < n → M < seq n := by
  have hfin := seq_bounded_indices_finite M
  by_cases hne : hfin.toFinset.Nonempty
  · refine ⟨hfin.toFinset.max' hne, fun n hn => ?_⟩
    by_contra h
    push_neg at h
    have hn_mem : n ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]; exact h
    exact absurd (hfin.toFinset.le_max' n hn_mem) (by omega)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine ⟨0, fun n _ => ?_⟩
    by_contra h
    push_neg at h
    have : n ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]; exact h
    rw [hne] at this
    simp at this

/-- Product growth bound: if `seq(k) ≥ B` for all `k` with `n₀ < k ≤ n`,
    then `prod(n) ≥ prod(n₀) * B^(n - n₀)`. -/
private theorem prod_ge_mul_pow (B n₀ : ℕ) :
    ∀ d : ℕ, (∀ k, n₀ < k → k ≤ n₀ + d → B ≤ Mullin.seq k) →
    Mullin.prod n₀ * B ^ d ≤ Mullin.prod (n₀ + d)
  | 0, _ => by simp
  | d + 1, h_seq => by
    rw [show n₀ + (d + 1) = (n₀ + d) + 1 from by omega, Mullin.prod_succ]
    have hB : B ≤ Mullin.seq (n₀ + d + 1) := h_seq _ (by omega) (by omega)
    calc Mullin.prod n₀ * B ^ (d + 1)
        = Mullin.prod n₀ * B ^ d * B := by ring
      _ ≤ Mullin.prod (n₀ + d) * Mullin.seq (n₀ + d + 1) :=
          Nat.mul_le_mul
            (prod_ge_mul_pow B n₀ d (fun k hk1 hk2 => h_seq k hk1 (by omega)))
            hB

/-- `log(prod(n)) ≥ (n - n₀) * log(M+1)` when seq(k) > M for all k > n₀. -/
private theorem log_prod_ge_of_seq_large (M n₀ n : ℕ) (h_le : n₀ ≤ n)
    (h_seq : ∀ k, n₀ < k → M < seq k) :
    ((n - n₀ : ℕ) : ℝ) * Real.log ((M : ℝ) + 1) ≤ Real.log (prod n : ℝ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h_le
  simp only [Nat.add_sub_cancel_left]
  have h_bound := prod_ge_mul_pow (M + 1) n₀ d
    (fun k hk1 hk2 => by have := h_seq k hk1; omega)
  have hprod0_pos : (0 : ℝ) < prod n₀ := by
    have := prod_ge_two n₀; positivity
  have hM1_pos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hpow_pos : (0 : ℝ) < ((M : ℝ) + 1) ^ d := pow_pos hM1_pos _
  calc (d : ℝ) * Real.log ((M : ℝ) + 1)
      = Real.log (((M : ℝ) + 1) ^ d) := by rw [Real.log_pow]
    _ ≤ Real.log ((prod n₀ : ℝ) * ((M : ℝ) + 1) ^ d) := by
          apply Real.log_le_log hpow_pos
          have h1 : (1 : ℝ) ≤ (prod n₀ : ℝ) := by
            have := prod_ge_two n₀; exact_mod_cast (show 1 ≤ prod n₀ by omega)
          linarith [mul_le_mul_of_nonneg_right h1 (le_of_lt hpow_pos)]
    _ ≤ Real.log (prod (n₀ + d) : ℝ) := by
          apply Real.log_le_log (mul_pos hprod0_pos hpow_pos)
          exact_mod_cast h_bound

/-- **Super-exponential growth of the Euclid-Mullin product.**

For every C > 0, eventually `log(prod(n)) ≥ C * n`.

Proof sketch: `seq` is injective among primes, so for any M, at most
finitely many indices have `seq(n) ≤ M`. Beyond those indices, each
factor is > M, so `prod(n)` grows at least as `(M+1)^n` (modulo
initial correction). Since M is arbitrary, `log(prod(n))/n → ∞`. -/
theorem em_super_exponential_growth : SuperExponentialGrowth Mullin.prod := by
  intro C hC
  -- Choose M large enough that log(M+1) > 2*C
  have hlog_tends : Filter.Tendsto (fun m : ℕ => Real.log (m : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  -- Eventually log(m) ≥ 2C+1, which gives > 2C
  obtain ⟨M, hM_large⟩ : ∃ M : ℕ, 2 * C < Real.log ((M : ℝ) + 1) := by
    have h_ev := Filter.tendsto_atTop.mp hlog_tends (2 * C + 1)
    obtain ⟨m, hm⟩ := h_ev.exists
    refine ⟨m, ?_⟩
    have h1 : 2 * C + 1 ≤ Real.log (m : ℝ) := hm
    have h2 : Real.log (m : ℝ) ≤ Real.log ((m : ℝ) + 1) := by
      by_cases hm0 : (m : ℝ) ≤ 0
      · have : Real.log (m : ℝ) ≤ 0 := by
          rcases le_antisymm hm0 (Nat.cast_nonneg m) with hm_eq
          rw [hm_eq]; simp
        have : 0 ≤ Real.log ((m : ℝ) + 1) := by
          apply Real.log_nonneg
          have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg' m
          linarith
        linarith
      · push_neg at hm0
        exact Real.log_le_log hm0 (by linarith)
    linarith
  -- Get n₀ such that seq(k) > M for all k > n₀
  obtain ⟨n₀, hn₀⟩ := seq_eventually_gt M
  -- For n ≥ 2 * n₀ + 1, we have log(prod(n)) ≥ C * n
  refine ⟨2 * n₀ + 1, fun n hn => ?_⟩
  have h_le : n₀ ≤ n := by omega
  -- Apply the growth bound
  have h_key := log_prod_ge_of_seq_large M n₀ n h_le (fun k hk => hn₀ k hk)
  have hlog_pos : 0 ≤ Real.log ((M : ℝ) + 1) := by
    apply Real.log_nonneg
    have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg' M
    linarith
  -- Chain: C*n ≤ (n-n₀)*log(M+1) ≤ log(prod n)
  -- Key: n ≤ 2*(n-n₀) since n ≥ 2*n₀+1
  have h_n_le : (n : ℕ) ≤ 2 * (n - n₀) := by omega
  calc C * (n : ℝ)
      ≤ ((n - n₀ : ℕ) : ℝ) * Real.log ((M : ℝ) + 1) := by
        calc C * (n : ℝ)
            ≤ C * (2 * ((n - n₀ : ℕ) : ℝ)) := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hC)
              exact_mod_cast h_n_le
          _ = 2 * C * ((n - n₀ : ℕ) : ℝ) := by ring
          _ ≤ Real.log ((M : ℝ) + 1) * ((n - n₀ : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_right (le_of_lt hM_large) (Nat.cast_nonneg _)
          _ = ((n - n₀ : ℕ) : ℝ) * Real.log ((M : ℝ) + 1) := by ring
    _ ≤ Real.log (prod n : ℝ) := h_key

end SuperExponentialGrowth

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
