import EM.Ensemble.Structure
import EM.Reduction.ShiftedDensity

/-!
# Visit Equidistribution: Spectral Decomposition and DSL Infrastructure

This file connects the excess energy of the EM walk to visit count
deviations, and provides infrastructure for DSL proof attempts.

## Key Identity (PROVED)

The excess energy equals the sum of squared visit deviations:
`excessEnergy(w) = (p−1) · ∑_a (V(a) − N/(p−1))²`

This shows SVE (excess energy = o(N²)) is equivalent to visit
equidistribution (each position visited ≈ N/(p−1) times).

## Main Results

### Proved Theorems
* `excessEnergy_eq_visit_deviation` — excess energy = (p−1) · ∑(V−N/(p−1))²
* `fiberMultCharSum_step`           — fiber sum one-step recurrence

### Definitions
* `VisitEquidistribution`           — walk visits each position ≈ N/(q−1) times

### Spectral Hierarchy

```
CME → CCSB → SVE ↔ VE → MC
```

SVE and VE express the same condition differently: SVE says total
character sum energy is small; VE says visit counts are close to uniform.
The identity `excessEnergy = (p−1)·∑(V−N/(p−1))²` makes this equivalence
explicit.
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Excess Energy Decomposition -/

section EnergyDecomposition

open Finset DirichletCharacter

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private instance neZeroVE : NeZero p := ⟨hp.out.ne_zero⟩

/-- The excess energy equals the total squared visit deviation:
    `excessEnergy(w) = (p−1) · ∑_a (V(a) − N/(p−1))²`.

    This identity shows that SVE (excess energy = o(N²)) is equivalent to
    visit equidistribution (each position visited ≈ N/(p−1) times).

    Proof: expand (V(a) − N/(p−1))² = V(a)² − 2V(a)·N/(p−1) + N²/(p−1)²,
    sum over a using ∑V(a) = N and |G| = p−1, simplify. -/
theorem excessEnergy_eq_visit_deviation {N : ℕ} (w : Fin N → (ZMod p)ˣ)
    (hp1 : 1 < p) :
    excessEnergy w =
    ((p : ℝ) - 1) *
      ∑ a : (ZMod p)ˣ,
        ((walkVisitCount w a : ℝ) - (N : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
  -- Key facts
  have hv : ∑ a : (ZMod p)ˣ, (walkVisitCount w a : ℝ) = (N : ℝ) := by
    exact_mod_cast walkVisitCount_sum w
  have hcard : (Finset.univ : Finset (ZMod p)ˣ).card = p - 1 := by
    rw [Finset.card_univ, ZMod.card_units_eq_totient, Nat.totient_prime hp.out]
  have hcard_real : ((Finset.univ : Finset (ZMod p)ˣ).card : ℝ) = (p : ℝ) - 1 := by
    rw [hcard]; push_cast [Nat.cast_sub hp.out.one_le]; ring
  have hp1_ne : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp1
    linarith
  -- Expand squares and rearrange sums
  unfold excessEnergy
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, hcard_real]
  -- Factor the linear term: ∑ 2·V·(N/(p-1)) = 2·(N/(p-1))·∑V
  simp_rw [show ∀ (a : (ZMod p)ˣ),
    2 * (walkVisitCount w a : ℝ) * ((N : ℝ) / ((p : ℝ) - 1)) =
    (2 * ((N : ℝ) / ((p : ℝ) - 1))) * (walkVisitCount w a : ℝ) from fun a => by ring]
  rw [← Finset.mul_sum, hv]
  -- Now: (p-1) * (∑V² - 2·N/(p-1)·N + (p-1)·(N/(p-1))²) = (p-1)·∑V² - N²
  field_simp
  ring

end EnergyDecomposition

/-! ## Fiber Sum Step Recurrence -/

section FiberRecurrence

variable {q : ℕ} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)

/-- The fiber character sum evolves one step at a time: at step N, the fiber
    sum for position a increases by χ(m(N)) if the walk is at a, and stays
    the same otherwise.

    This makes the incremental structure explicit:
    each step either contributes a character value (when the walk visits
    this fiber) or does nothing (when it visits another fiber). -/
theorem fiberMultCharSum_step (χ : (ZMod q)ˣ →* ℂˣ) (a : (ZMod q)ˣ) (N : ℕ) :
    fiberMultCharSum q hq hne χ a (N + 1) =
    fiberMultCharSum q hq hne χ a N +
      if emWalkUnit q hq hne N = a
      then (χ (emMultUnit q hq hne N) : ℂ)
      else 0 := by
  simp only [fiberMultCharSum]
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · -- Walk is at position a: add χ(m(N))
    rw [Finset.sum_insert]
    · ring
    · simp only [Finset.mem_filter, Finset.mem_range]
      exact fun ⟨hlt, _⟩ => Nat.lt_irrefl N hlt
  · -- Walk is not at position a: no contribution
    simp

end FiberRecurrence

/-! ## Visit Equidistribution -/

section VisitEquidist

/-- **Visit Equidistribution at an explicit threshold** (added 2026-11-10): the body of
    `VisitEquidistribution` with the threshold `Q₀` as a parameter. -/
def VisitEquidistributionAt (Q₀ : ℕ) : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)], q ≥ Q₀ →
  ∀ (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a : (ZMod q)ˣ,
    |((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card / (N : ℝ) -
      1 / ((q : ℝ) - 1)| ≤ ε

/-- **VE at `Q₀` gives cofinal visits**: for a missing prime `q ≥ Q₀` the walk visits every
    unit `a` at arbitrarily late times (a positive limiting frequency forces infinitely many
    visits). -/
theorem veAt_walk_cofinal {Q₀ : ℕ} (h : VisitEquidistributionAt Q₀)
    {q : Nat} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hge : q ≥ Q₀) (a : (ZMod q)ˣ) :
    ∀ M, ∃ n, M ≤ n ∧ emWalkUnit q hq hne n = a := by
  intro M
  by_contra hno
  push_neg at hno
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (Fact.out : Nat.Prime q).one_lt
  have hpos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  set ε : ℝ := 1 / (2 * ((q : ℝ) - 1)) with hε
  have hεpos : 0 < ε := by positivity
  have he : ε * (2 * ((q : ℝ) - 1)) = 1 := by rw [hε]; field_simp
  have he' : 1 / ((q : ℝ) - 1) = 2 * ε := by rw [hε]; field_simp
  obtain ⟨N₀, hN₀⟩ := h q hge hq hne ε hεpos
  have hb := hN₀ (max N₀ (2 * q * (M + 1))) (le_max_left _ _) a
  have hcard : ((Finset.range (max N₀ (2 * q * (M + 1)))).filter
      (fun n => emWalkUnit q hq hne n = a)).card ≤ M := by
    calc _ ≤ (Finset.range M).card := Finset.card_le_card (by
            intro n hn
            rw [Finset.mem_filter] at hn
            rw [Finset.mem_range]
            by_contra hlt
            exact hno n (not_lt.mp hlt) hn.2)
      _ = M := Finset.card_range M
  have hcardR : (((Finset.range (max N₀ (2 * q * (M + 1)))).filter
      (fun n => emWalkUnit q hq hne n = a)).card : ℝ) ≤ M := by exact_mod_cast hcard
  have hNge : (2 * (q : ℝ) * ((M : ℝ) + 1)) ≤ ((max N₀ (2 * q * (M + 1)) : ℕ) : ℝ) := by
    exact_mod_cast le_max_right N₀ (2 * q * (M + 1))
  have hNpos : (0 : ℝ) < ((max N₀ (2 * q * (M + 1)) : ℕ) : ℝ) := by
    have : (0 : ℝ) < 2 * (q : ℝ) * ((M : ℝ) + 1) := by positivity
    linarith
  have h1 := (abs_le.mp hb).1
  rw [he'] at h1
  have h2 : ε ≤ (((Finset.range (max N₀ (2 * q * (M + 1)))).filter
      (fun n => emWalkUnit q hq hne n = a)).card : ℝ) /
      ((max N₀ (2 * q * (M + 1)) : ℕ) : ℝ) := by linarith
  rw [le_div_iff₀ hNpos] at h2
  have h3 : ε * (2 * (q : ℝ) * ((M : ℝ) + 1)) ≤
      ε * ((max N₀ (2 * q * (M + 1)) : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hNge hεpos.le
  have h4 : ε * (2 * (q : ℝ) * ((M : ℝ) + 1)) =
      (ε * (2 * ((q : ℝ) - 1))) * ((M : ℝ) + 1) + 2 * ε * ((M : ℝ) + 1) := by ring
  have h5 : (0 : ℝ) ≤ 2 * ε * ((M : ℝ) + 1) := by positivity
  rw [he] at h4
  linarith

/-- **Visit Equidistribution**: the EM walk visits every residue class
    mod q with asymptotic frequency 1/(q−1).

    By `excessEnergy_eq_visit_deviation`, VE is equivalent to SVE
    (SubquadraticVisitEnergy), which implies MC via `sve_implies_mc`.

    VE is a consequence of CME since CME → CCSB → SVE ↔ VE.

    Note (2026-11-10): the equivalence with SVE is not proved in Lean as a single theorem;
    what is proved is that VE, SVE and MMCSB are each equivalent to *cofinite* MC,
    `MissingFinite` (`ve_iff_missingFinite`, `EM/CME/Equivalences.lean`).  The threshold is
    existential; the form with a named threshold is `VisitEquidistributionAt Q₀`. -/
def VisitEquidistribution : Prop :=
  ∃ Q₀ : ℕ, ∀ (q : Nat) [Fact (Nat.Prime q)], q ≥ Q₀ →
  ∀ (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a : (ZMod q)ˣ,
    |((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card / (N : ℝ) -
      1 / ((q : ℝ) - 1)| ≤ ε

/-- `VisitEquidistribution` is `VisitEquidistributionAt Q₀` for some `Q₀`. -/
theorem visitEquidistribution_iff_exists_at :
    VisitEquidistribution ↔ ∃ Q₀ : ℕ, VisitEquidistributionAt Q₀ := Iff.rfl

end VisitEquidist

/-! ## Spectral Hierarchy

The spectral conditions form a strict hierarchy:

```
CME (Conditional Multiplier Equidist)     — strongest open hypothesis
  ↓ cme_implies_ccsb (proved)
CCSB (Complex Character Sum Bound)        — character sums o(N)
  ↓ ccsb_implies_sve (proved)
SVE (Subquadratic Visit Energy)           — excess energy o(N²)
  ↔ excessEnergy_eq_visit_deviation (this file)
VE (Visit Equidistribution)               — V(a)/N → 1/(q−1) for all a
  ↓ sve_implies_mmcsb (proved)
MMCSB (Multi-Modular CSB)                 — each χ individually bounded
  ↓ mmcsb_implies_mc (proved)
MC (Mullin's Conjecture)                  — every prime appears
```

The identity `excessEnergy = (p−1) · ∑(V−N/(p−1))²` (proved above) shows
SVE and VE measure the same thing: SVE bounds the L² energy while VE bounds
each individual visit count. They are equivalent because the energy IS the
sum of squared deviations.

### DSL Connection

The Deterministic Stability Lemma (PE → CME) would complete the chain:
  PE → CME → CCSB → SVE/VE → MC

The `fiberMultCharSum_step` recurrence shows that each fiber sum F(a,N)
grows by χ(m(N)) when the walk visits position a. By position-blindness
(`crt_multiplier_invariance`), the multiplier χ(m(N)) does not depend on
the walk position a. By PE, the multiplier values are approximately
uniformly distributed. If these approximate cancellations accumulate,
the fiber sums remain o(N), giving CME.

The gap: proving that deterministic approximate cancellations (from PE +
position-blindness) actually accumulate to o(N) requires either an ergodic
theorem or an explicit variance bound — exactly what DSL asserts.
-/

end
