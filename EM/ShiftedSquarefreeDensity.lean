import EM.PopulationEquidistProof

/-!
# Shifted Squarefree Density: The Function g(r) = r/(r²-1)

This file formalizes the **divisibility density function** g(r) = r/(r²−1),
which gives the conditional probability that a random shifted squarefree
number m (with μ²(m−1) = 1) is divisible by a prime r.

## Mathematical Background

For a prime r, among integers m with μ²(m−1) = 1:
- r | m forces m−1 ≡ −1 (mod r), so squarefreeness at r is automatic
- For primes s ≠ r: conditions r | m and s² ∤ m−1 are on coprime moduli
- By CRT: density = (1/r) · (6/π²)/(1−1/r²) = (6/π²) · r/(r²−1)
- Conditioning on squarefree: g(r) = r/(r²−1)

The minFac distribution over the q-rough shifted squarefree population is
d_S(p) = g(p) · ∏_{r<p}(1−g(r)), a Buchstab-type identity. Writing this
as h(p)/p where h depends only on |p| (not p mod q), Dirichlet's theorem
gives MinFacResidueEquidist → PE.

## Main Results

### Algebraic Properties of g (all PROVED)
* `sieveDensity_pos`            — g(r) > 0 for r ≥ 2
* `sieveDensity_lt_one`         — g(r) < 1 for r ≥ 2
* `sieveDensity_partial_frac`   — g(r) = (1/2)(1/(r−1) + 1/(r+1))
* `sieveDensity_gt_inv`         — g(r) > 1/r for r ≥ 2
* `sieveDensity_sub_inv`        — g(r) − 1/r = 1/(r(r²−1)) (exact correction)
* `sieveDensity_correction_pos` — g(r) − 1/r > 0
* `sieveDensity_lt_inv_pred`    — g(r) < 1/(r−1) for r ≥ 2
* `one_sub_sieveDensity_pos`    — 1 − g(r) > 0 (complement density is positive)
* `sieveDensity_at_two`         — g(2) = 2/3
* `sieveDensity_at_three`       — g(3) = 3/8

### Counting and Density Framework
* `shiftedSquarefreeDivCount`   — count of m ∈ [2,X] with μ²(m−1)=1, r|m
* `shiftedSquarefreeDivCount_le` — count ≤ total shifted squarefree count

### Open Hypothesis
* `SieveDensityAxiom`           — g(r) gives the conditional divisibility density
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## The Divisibility Density Function -/

section SieveDensity

/-- The divisibility density function g(r) = r/(r²−1).
    For a prime r, g(r) is the conditional probability that a uniformly random
    shifted squarefree number m (with μ²(m−1) = 1) satisfies r | m.

    The formula comes from CRT: r | m forces m ≡ 0 (mod r), i.e., m−1 ≡ −1 (mod r),
    so the squarefreeness constraint at r is automatically satisfied. For primes
    s ≠ r, the constraints r | m and s² ∤ m−1 act on coprime moduli. The density
    is therefore (1/r) / (1 − 1/r²) = r/(r²−1). -/
def sieveDensity (r : Nat) : ℝ := (r : ℝ) / ((r : ℝ) ^ 2 - 1)

/-- The denominator r²−1 is positive for r ≥ 2. -/
private theorem sieveDensity_denom_pos {r : Nat} (hr : 2 ≤ r) :
    0 < (r : ℝ) ^ 2 - 1 := by
  have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  nlinarith [sq_nonneg ((r : ℝ) - 1)]

/-- g(r) > 0 for r ≥ 2. -/
theorem sieveDensity_pos {r : Nat} (hr : 2 ≤ r) : 0 < sieveDensity r := by
  exact div_pos (by exact_mod_cast (show 0 < r from by omega))
    (sieveDensity_denom_pos hr)

/-- g(r) < 1 for r ≥ 2. Since r < r²−1 for r ≥ 2 (equivalently r²−r−1 > 0). -/
theorem sieveDensity_lt_one {r : Nat} (hr : 2 ≤ r) : sieveDensity r < 1 := by
  rw [sieveDensity, div_lt_one (sieveDensity_denom_pos hr)]
  have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  nlinarith [sq_nonneg ((r : ℝ) - 1)]

/-- Partial fractions: g(r) = (1/2)(1/(r−1) + 1/(r+1)). -/
theorem sieveDensity_partial_frac {r : Nat} (hr : 2 ≤ r) :
    sieveDensity r =
      (1 : ℝ) / 2 * (1 / ((r : ℝ) - 1) + 1 / ((r : ℝ) + 1)) := by
  have hr' : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h1 : (r : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (r : ℝ) + 1 ≠ 0 := by linarith
  have h3 : (r : ℝ) ^ 2 - 1 ≠ 0 := ne_of_gt (sieveDensity_denom_pos hr)
  simp only [sieveDensity]; field_simp; ring

/-- g(r) > 1/r for r ≥ 2: the density of divisibility by r among shifted
    squarefree numbers exceeds the naive 1/r (because squarefreeness at r
    is automatic when r | m, boosting the density). -/
theorem sieveDensity_gt_inv {r : Nat} (hr : 2 ≤ r) :
    1 / (r : ℝ) < sieveDensity r := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r from by omega)
  rw [sieveDensity, div_lt_div_iff₀ hr_pos (sieveDensity_denom_pos hr)]
  have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  nlinarith [sq_nonneg ((r : ℝ) - 1)]

/-- The exact correction: g(r) − 1/r = 1/(r(r²−1)). This measures the
    density boost from the automatic squarefreeness at r. -/
theorem sieveDensity_sub_inv {r : Nat} (hr : 2 ≤ r) :
    sieveDensity r - 1 / (r : ℝ) =
      1 / ((r : ℝ) * ((r : ℝ) ^ 2 - 1)) := by
  have hr_ne : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 from by omega)
  have h_denom : (r : ℝ) ^ 2 - 1 ≠ 0 := ne_of_gt (sieveDensity_denom_pos hr)
  simp only [sieveDensity]; field_simp; ring

/-- The correction g(r) − 1/r is positive (the density boost is real). -/
theorem sieveDensity_correction_pos {r : Nat} (hr : 2 ≤ r) :
    0 < sieveDensity r - 1 / (r : ℝ) := by
  rw [sieveDensity_sub_inv hr]
  exact div_pos one_pos (mul_pos
    (by exact_mod_cast (show 0 < r from by omega))
    (sieveDensity_denom_pos hr))

/-- g(r) < 1/(r−1) for r ≥ 2. Combined with g(r) > 1/r, this sandwiches
    g(r) between 1/r and 1/(r−1). -/
theorem sieveDensity_lt_inv_pred {r : Nat} (hr : 2 ≤ r) :
    sieveDensity r < 1 / ((r : ℝ) - 1) := by
  have hr' : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h1 : (0 : ℝ) < (r : ℝ) - 1 := by linarith
  rw [sieveDensity, div_lt_div_iff₀ (sieveDensity_denom_pos hr) h1]
  nlinarith

/-- 1 − g(r) > 0 for r ≥ 2 (the complement density is positive). Used in
    sieve product computations where we need ∏(1 − g(r)) > 0. -/
theorem one_sub_sieveDensity_pos {r : Nat} (hr : 2 ≤ r) :
    0 < 1 - sieveDensity r :=
  sub_pos.mpr (sieveDensity_lt_one hr)

/-- g(2) = 2/3. The density of even numbers among shifted squarefree is 2/3
    (higher than 1/2 because m even forces m−1 odd, automatically squarefree
    at 2). -/
theorem sieveDensity_at_two : sieveDensity 2 = 2 / 3 := by
  simp only [sieveDensity]; push_cast; norm_num

/-- g(3) = 3/8. -/
theorem sieveDensity_at_three : sieveDensity 3 = 3 / 8 := by
  simp only [sieveDensity]; push_cast; norm_num

/-- g(5) = 5/24. -/
theorem sieveDensity_at_five : sieveDensity 5 = 5 / 24 := by
  simp only [sieveDensity]; push_cast; norm_num

/-- g is strictly decreasing on [2,∞): if 2 ≤ r < s then g(s) < g(r). -/
theorem sieveDensity_strict_anti {r s : Nat} (hr : 2 ≤ r) (hrs : r < s) :
    sieveDensity s < sieveDensity r := by
  have hs : 2 ≤ s := by omega
  -- g(r) < 1/(r-1) and g(s) > 1/s, so we need 1/s < 1/(r-1)... no
  -- Actually: g(x) = x/(x²-1) is decreasing for x ≥ 2.
  -- Direct proof: g(r) - g(s) = r/(r²-1) - s/(s²-1)
  -- = [r(s²-1) - s(r²-1)] / [(r²-1)(s²-1)]
  -- = [rs² - r - sr² + s] / [...]
  -- = [rs(s-r) + (s-r)] / [...]
  -- = [(s-r)(rs+1)] / [...]
  -- > 0 since s > r ≥ 2.
  simp only [sieveDensity]
  rw [div_lt_div_iff₀ (sieveDensity_denom_pos hs) (sieveDensity_denom_pos hr)]
  -- Goal: s * (r^2 - 1) < r * (s^2 - 1)
  -- i.e., sr² - s < rs² - r
  -- i.e., r - s < rs² - sr² = rs(s - r)
  -- i.e., -(s-r) < rs(s-r)
  -- i.e., 0 < (s-r)(rs + 1)
  have hrs' : (r : ℝ) < (s : ℝ) := by exact_mod_cast hrs
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r from by omega)
  have hs_pos : (0 : ℝ) < (s : ℝ) := by linarith
  nlinarith [mul_pos hr_pos hs_pos,
             sq_nonneg ((r : ℝ) - 1), sq_nonneg ((s : ℝ) - 1)]

end SieveDensity

/-! ## Shifted Squarefree Divisibility Counting -/

section Counting

/-- Count of m ∈ [2,X] with μ²(m−1) = 1 and r | m. -/
noncomputable def shiftedSquarefreeDivCount (r X : Nat) : Nat :=
  ((Finset.Icc 2 X).filter (fun m => Squarefree (m - 1) ∧ r ∣ m)).card

/-- Count of all m ∈ [2,X] with μ²(m−1) = 1. -/
noncomputable def shiftedSquarefreeCount (X : Nat) : Nat :=
  ((Finset.Icc 2 X).filter (fun m => Squarefree (m - 1))).card

/-- The divisibility count is at most the total shifted squarefree count. -/
theorem shiftedSquarefreeDivCount_le (r X : Nat) :
    shiftedSquarefreeDivCount r X ≤ shiftedSquarefreeCount X := by
  apply Finset.card_le_card
  intro m
  simp only [Finset.mem_filter]
  exact fun ⟨hm, hsq, _⟩ => ⟨hm, hsq⟩

end Counting

/-! ## Sieve Density Axiom -/

section SieveDensityAxiom

/-- **Sieve Density Axiom**: for every prime r, the proportion of shifted
    squarefree numbers m (with μ²(m−1) = 1) divisible by r converges to
    g(r) = r/(r²−1) as the range X → ∞.

    **Proof from standard ANT:**
    - The event r | m constrains m to {0} mod r (density 1/r)
    - The event μ²(m−1) = 1 constrains m−1 to be squarefree
    - When r | m, m−1 ≡ −1 (mod r), so r ∤ m−1 automatically — hence
      the squarefree constraint at r is free
    - For primes s ≠ r, the constraints r | m and s² ∤ m−1 are on
      coprime moduli r and s², hence independent by CRT
    - Therefore: density = (1/r) · ∏_{s≠r}(1−1/s²) / ∏_s(1−1/s²)
      = (1/r) / (1−1/r²) = r/(r²−1) = g(r)

    This is used to derive κ = ∑_p g(p) · ∏_{r<p}(1−g(r)) · (1/p) > 0,
    the expected reciprocal of minFac over the shifted squarefree population. -/
def SieveDensityAxiom : Prop :=
  ∀ (r : Nat), Nat.Prime r →
    Filter.Tendsto
      (fun X : Nat =>
        (shiftedSquarefreeDivCount r X : ℝ) /
        (shiftedSquarefreeCount X : ℝ))
      Filter.atTop (nhds (sieveDensity r))

end SieveDensityAxiom

/-! ## Connection to PE Infrastructure

The sieve density axiom connects to the PE reduction chain as follows:

```
SieveDensityAxiom (g(r) for individual primes)
  + Buchstab identity (d_S(p) = g(p) · ∏(1−g(r)))
  + Dirichlet's theorem (primes equidistributed in APs)
  → MinFacResidueEquidist (minFac equidist mod q in S_q)
  → PE (PopulationEquidist, proved in PopulationEquidistProof.lean)
  + DSL (Deterministic Stability Lemma)
  → MC (Mullin's Conjecture)
```

The sieve density axiom provides the **input** to the minFac distribution
computation. The key insight is that h(p) := p · d_S(p) depends on p only
through its magnitude (not through p mod q), because the Euler product
factors defining g(r) treat all primes equally modulo their size.

This "size-only" dependence is what allows Dirichlet's theorem to give
the equidistribution conclusion: primes p ≡ a (mod q) with weight h(p)/p
have the same total as primes p ≡ b (mod q) with weight h(p)/p,
for any a, b coprime to q.
-/

end
