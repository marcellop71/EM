import EM.IK.DirichletDensity
import EM.Ensemble.FirstMoment

/-!
# The first multiplier of the correct-parity ensemble

`genSeq n 0 = minFac (n + 1)` (`EM/Ensemble/GenEM.lean`): the distribution of `minFac` on
a family of shifted integers **is** the first-multiplier distribution of the generalized
Euclid–Mullin ensemble restricted to that family.

Dead End #157 refutes `EnsembleMultiplierEquidist` over *all* squarefree starting points
for a parity reason: at least half of the squarefree `n` are odd, and for odd `n` we have
`genSeq n 0 = minFac (n + 1) = 2`, so the class of `2` carries density `≥ 1/2` against the
asserted `1/(q-1)`.  That defect is an artifact: the real Euclid–Mullin accumulator is
always **even** (`seq 0 = 2`), so every real candidate `Pₙ + 1` is odd and the multiplier
is never `2`.

This file asks what survives at the correct parity, on the smallest nontrivial family:
starting points `n = 2p` with `p` prime (squarefree, even, `ω = 2`).  Equidistribution
still fails, and fails for a structural reason rather than a parity artifact —
**small-prime domination**, with an explicit constant:

  the Dirichlet density of `{p prime : minFac (2p + 1) = 3}` is exactly `1/2`.

Equivalently: for half of this ensemble the first multiplier is `3` itself, so the
accumulator `2p · 3` is divisible by `3` and the walk mod `3` is **absorbed at the very
first step** — the mechanism of Dead End #137, here with a density attached.

## Main results

* `minFac_two_mul_add_one_eq_three_iff` — the arithmetic core, unconditional and
  analysis-free: for `1 ≤ n`, `minFac (2n + 1) = 3 ↔ (n : ZMod 3) = 1`.
* `tendsto_minFacThree_density` — the density is exactly `1/2`.
* `first_multiplier_not_equidistributed` — for every *prime* modulus `Q ≥ 5` the class of
  the first multiplier does not equidistribute over the `φ(Q) = Q - 1` invertible
  classes: the single class of `3` already carries density `≥ 1/2 > 1/(Q-1)`.
* `minFacThree_absorbed` — the reading in walk terms: `3 ∣ genProd (2p) 1`, i.e.
  absorption mod `3` after one step, on a density-`1/2` set of starting points.

## Scope, honestly

Dirichlet density throughout (`IK/DirichletDensity.lean` Parts 9–10), *not* natural
density: the latter needs PNT in arithmetic progressions, carried by this project as the
open `IK.WeightedPNTinAP`.

Primality of `Q` matters in `first_multiplier_not_equidistributed` and is not cosmetic:
`φ(6) = 2`, so `1/φ(Q) = 1/2` at `Q = 6` and the contradiction would evaporate.  The EM
walk modulus is prime, so this is the relevant case.

This is an **ensemble** statement.  It does not cross Dead End #90: the Euclid–Mullin
orbit is a single point, and the tail identity cannot transfer a density statement to it
(Dead End #158).  Its value is that it replaces the *refutation* of #157 by a theorem
with an explicit limit, at the correct parity where the parity artifact is gone.
-/

noncomputable section

open Mullin Euclid
open IK.DirichletDensity

namespace MinFacShifted

/-! ## Part 1: The arithmetic core

No analysis here.  `minFac (2n+1) = 3` is a congruence condition on `n` mod `3`, because
`2n+1` is odd (so its least factor is at least `3`) and `3` is the least odd prime. -/

/-- **The arithmetic core.**  The first multiplier of the starting point `2n` is `3`
exactly when `n ≡ 1 (mod 3)`.  No lower bound on `n` is needed: at `n = 0` both sides are
false, since `minFac 1 = 1`. -/
theorem minFac_two_mul_add_one_eq_three_iff {n : ℕ} :
    Nat.minFac (2 * n + 1) = 3 ↔ ((n : ZMod 3) = 1) := by
  have hodd : ¬ (2 ∣ 2 * n + 1) := by omega
  -- Step 1: for an odd `N ≥ 3`, `minFac N = 3 ↔ 3 ∣ N`.
  have hstep : Nat.minFac (2 * n + 1) = 3 ↔ (3 ∣ 2 * n + 1) := by
    constructor
    · intro h
      rw [← h]; exact Nat.minFac_dvd _
    · intro h
      have hne1 : 2 * n + 1 ≠ 1 := by omega
      have hle : Nat.minFac (2 * n + 1) ≤ 3 := Nat.minFac_le_of_dvd (by norm_num) h
      have hpr : (Nat.minFac (2 * n + 1)).Prime := Nat.minFac_prime hne1
      have hne2 : Nat.minFac (2 * n + 1) ≠ 2 := by
        intro h2
        have hd : Nat.minFac (2 * n + 1) ∣ 2 * n + 1 := Nat.minFac_dvd _
        rw [h2] at hd
        exact hodd hd
      have := hpr.two_le
      omega
  -- Step 2: the cast to `ZMod 3` is the residue condition `n % 3 = 1`.
  have hcast : ((n : ℕ) : ZMod 3) = 1 ↔ n % 3 = 1 := by
    rw [show (1 : ZMod 3) = ((1 : ℕ) : ZMod 3) by norm_num, ZMod.natCast_eq_natCast_iff]
    simp [Nat.ModEq]
  rw [hstep, hcast]
  omega

/-! ## Part 2: The density

By Part 1 the event is the single invertible class `1` mod `3`, so Parts 9–10 of
`IK/DirichletDensity.lean` apply with `φ(3) = 2`. -/

/-- Summand of the prime sum over starting points whose first multiplier is `3`. -/
def minFacThreeTerm (σ : ℝ) (p : Nat.Primes) : ℝ :=
  if Nat.minFac (2 * (p : ℕ) + 1) = 3 then (p : ℝ) ^ (-σ) else 0

/-- `∑_{p : minFac (2p+1) = 3} p^{-σ}`. -/
def minFacThreeSum (σ : ℝ) : ℝ := ∑' p : Nat.Primes, minFacThreeTerm σ p

/-- The event is exactly the class `1` mod `3`. -/
theorem minFacThreeSum_eq_classPrimeSum (σ : ℝ) :
    minFacThreeSum σ = classPrimeSum (1 : ZMod 3) σ := by
  rw [minFacThreeSum, classPrimeSum]
  refine tsum_congr fun p => ?_
  rw [minFacThreeTerm, classTerm]
  by_cases h : ((p : ℕ) : ZMod 3) = 1
  · rw [if_pos (minFac_two_mul_add_one_eq_three_iff.mpr h), if_pos h]
  · rw [if_neg (fun hc => h (minFac_two_mul_add_one_eq_three_iff.mp hc)), if_neg h]

lemma summable_minFacThreeTerm {σ : ℝ} (hσ : 1 < σ) : Summable (minFacThreeTerm σ) := by
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (summable_rpow_neg hσ)
  · rw [minFacThreeTerm]; split_ifs
    · positivity
    · exact le_rfl
  · rw [minFacThreeTerm]; split_ifs
    · exact le_rfl
    · positivity

/-- **The density is `1/2`.**  Among the prime starting parameters `p` — i.e. the
`ω = 2`, correct-parity generalized Euclid–Mullin starting points `2p` — exactly half
have first multiplier `3`. -/
theorem tendsto_minFacThree_density :
    Filter.Tendsto (fun σ : ℝ => minFacThreeSum σ / primeZetaSum σ)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 / 2)) := by
  have h := tendsto_classPrimeSum_div_primeZetaSum (q := 3) (by norm_num)
    (isUnit_one : IsUnit (1 : ZMod 3))
  have h3n : (3 : ℕ).totient = 2 := by decide
  rw [h3n] at h
  norm_num at h
  refine h.congr' (Filter.Eventually.of_forall fun σ => ?_)
  show classPrimeSum (1 : ZMod 3) σ / primeZetaSum σ = minFacThreeSum σ / primeZetaSum σ
  rw [minFacThreeSum_eq_classPrimeSum]

/-! ## Part 3: Non-equidistribution

The first multiplier is a genuine prime, so it has a class modulo any `Q`.  Since
`minFac (2p+1) = 3` forces that class to be `3 mod Q`, the density-`1/2` event of Part 2
piles onto a *single* class — against the `1/φ(Q)` that equidistribution asserts. -/

/-- Summand of the prime sum over starting points whose first multiplier lies in the
class `b` mod `Q`. -/
def multClassTerm (Q : ℕ) (b : ZMod Q) (σ : ℝ) (p : Nat.Primes) : ℝ :=
  if ((Nat.minFac (2 * (p : ℕ) + 1) : ℕ) : ZMod Q) = b then (p : ℝ) ^ (-σ) else 0

/-- `∑_{p : minFac (2p+1) ≡ b (mod Q)} p^{-σ}`. -/
def multClassSum (Q : ℕ) (b : ZMod Q) (σ : ℝ) : ℝ :=
  ∑' p : Nat.Primes, multClassTerm Q b σ p

lemma multClassTerm_nonneg (Q : ℕ) (b : ZMod Q) (σ : ℝ) (p : Nat.Primes) :
    0 ≤ multClassTerm Q b σ p := by
  rw [multClassTerm]; split_ifs
  · positivity
  · exact le_rfl

lemma multClassTerm_le (Q : ℕ) (b : ZMod Q) (σ : ℝ) (p : Nat.Primes) :
    multClassTerm Q b σ p ≤ (p : ℝ) ^ (-σ) := by
  rw [multClassTerm]; split_ifs
  · exact le_rfl
  · positivity

lemma summable_multClassTerm (Q : ℕ) (b : ZMod Q) {σ : ℝ} (hσ : 1 < σ) :
    Summable (multClassTerm Q b σ) :=
  Summable.of_nonneg_of_le (multClassTerm_nonneg Q b σ) (multClassTerm_le Q b σ)
    (summable_rpow_neg hσ)

/-- Every starting point with first multiplier `3` contributes to the class of `3`. -/
theorem minFacThreeSum_le_multClassSum (Q : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    minFacThreeSum σ ≤ multClassSum Q ((3 : ℕ) : ZMod Q) σ := by
  refine Summable.tsum_le_tsum (fun p => ?_) (summable_minFacThreeTerm hσ)
    (summable_multClassTerm Q _ hσ)
  rw [minFacThreeTerm, multClassTerm]
  by_cases h : Nat.minFac (2 * (p : ℕ) + 1) = 3
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h]
    positivity

/-- **The first multiplier does not equidistribute.**  For every prime modulus `Q ≥ 5`,
the class of `3` carries Dirichlet density at least `1/2`, whereas equidistribution over
the `φ(Q) = Q - 1` invertible classes would give it `1/(Q-1) ≤ 1/4`.

The obstruction uses nothing about the residue structure of `Q`: a *single* small prime
absorbs half the ensemble.  Primality is used only through `φ(Q) = Q - 1`; for composite
`Q` the totient can be small (`φ(6) = 2`) and the numbers no longer separate. -/
theorem first_multiplier_not_equidistributed {Q : ℕ} (hQ : Nat.Prime Q) (hQ5 : 5 ≤ Q) :
    ¬ Filter.Tendsto (fun σ : ℝ => multClassSum Q ((3 : ℕ) : ZMod Q) σ / primeZetaSum σ)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 / (Q.totient : ℝ))) := by
  intro hcon
  -- the class of `3` carries density at least `1/2`
  have hle : (1 : ℝ) / 2 ≤ 1 / (Q.totient : ℝ) := by
    refine le_of_tendsto_of_tendsto tendsto_minFacThree_density hcon ?_
    filter_upwards [self_mem_nhdsWithin,
      tendsto_primeZetaSum_atTop.eventually_gt_atTop 0] with σ hσ hzpos
    have hσ' : (1 : ℝ) < σ := hσ
    gcongr
    exact minFacThreeSum_le_multClassSum Q hσ'
  -- but `φ(Q) = Q - 1 ≥ 4`, so it is at most `1/4`
  have hφ : (4 : ℝ) ≤ (Q.totient : ℝ) := by
    rw [Nat.totient_prime hQ]
    have : (4 : ℕ) ≤ Q - 1 := by omega
    exact_mod_cast this
  have : (1 : ℝ) / (Q.totient : ℝ) ≤ 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num) hφ
  linarith

/-! ## Part 4: The walk reading

`minFac (2p+1) = 3` says the first multiplier *is* `3`, so the accumulator after one step
is divisible by `3`: the walk mod `3` is absorbed immediately.  Combined with Part 2, a
density-`1/2` set of correct-parity `ω = 2` starting points dies at `3` on step one. -/

/-- If the first multiplier is `3` then `3` divides the accumulator after one step —
absorption in the sense of Dead End #137. -/
theorem minFacThree_absorbed {n : ℕ} (h : Nat.minFac (2 * n + 1) = 3) :
    3 ∣ genProd (2 * n) 1 := by
  rw [genProd_succ, genSeq_def]
  exact Dvd.dvd.mul_left (by rw [show genProd (2 * n) 0 = 2 * n from rfl, h]) _

/-- **Landscape.**  The three facts of this file in one statement: the arithmetic
characterisation, the density `1/2`, and the absorption reading. -/
theorem minFacShifted_landscape :
    (∀ n : ℕ, Nat.minFac (2 * n + 1) = 3 ↔ ((n : ZMod 3) = 1)) ∧
    Filter.Tendsto (fun σ : ℝ => minFacThreeSum σ / primeZetaSum σ)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 / 2)) ∧
    (∀ n : ℕ, Nat.minFac (2 * n + 1) = 3 → 3 ∣ genProd (2 * n) 1) :=
  ⟨fun _ => minFac_two_mul_add_one_eq_three_iff,
   tendsto_minFacThree_density,
   fun _ h => minFacThree_absorbed h⟩

end MinFacShifted

end
