import EM.Stochastic.RandomTwoPointMCB
import EM.Group.Bridge

/-!
# The One-Horizon Fourier Criterion

Every sufficient hypothesis in the reduction network is *asymptotic*: CCSB asks that the
walk character sums be `o(N)` for all large `N`, CME likewise.  This file records the
weakest form of the same idea — a **single finite horizon** at which the nontrivial
character sums total less than the horizon itself:

```
    ∑_{χ ≠ 1} ‖∑_{n < N} χ(w(n))‖  <  N .
```

Fourier inversion then forces the walk to visit *every* unit before `N`, in particular the
death class `-1`.  Combined with the first-missing-prime bootstrap, one such horizon at
the least missing prime settles Mullin's conjecture there.

## What this does and does not buy

It is genuinely weaker as a *global* statement: one horizon rather than every large one.
It is genuinely **stronger per character** at that horizon.  With `|G| = q - 1` characters,
the hypothesis needs an average of `‖S_χ‖ < N/(q-2)` — a saving by a factor of order `q`,
not merely "some cancellation".  CCSB, giving `ε → 0`, implies the criterion for large
`N`; the criterion does not imply CCSB.

For a walk with square-root cancellation `‖S_χ‖ ≍ √N` the criterion bites once
`√N · q < N`, i.e. `N ≳ q²`.  So the honest reading of this hypothesis is a
**quantitative coverage target**:

> past the sieve gap, the walk covers `(ℤ/qℤ)ˣ` within `O(q²)` steps.

That is a better-posed open problem than `o(N)` — finite, quantitative, and with partial
progress measurable — but it is not an easier one.  No technique bounds walk character
sums for the actual orbit at *any* horizon: the whole difficulty lies between the trivial
bound `N` and anything below it, and that gap is indifferent to the quantifier over `N`.
The obstruction is orbit-specificity (Dead Ends #90, #117), which this reformulation does
not touch.

## Main results

* `covers_of_charSum_lt` — the criterion, for an arbitrary sequence in `(ZMod q)ˣ`.
* `WindowFourierGain` — the criterion as a hypothesis about EM walk windows.
* `windowFourierGain_hits` — it produces a hit on the death class past any stage.
-/

noncomputable section

open Mullin Euclid MullinGroup
open scoped BigOperators
open scoped Classical

namespace OneHorizon

variable {q : ℕ} [Fact (Nat.Prime q)]

/-- **The one-horizon Fourier criterion.**  If the nontrivial character sums over the
window `[0, N)` total less than `N`, then every unit occurs as a walk value in the window.

This is the standard Weyl/orthogonality count with the limit removed: the trivial
character contributes exactly `N`, and the remaining characters cannot cancel it. -/
theorem covers_of_charSum_lt (w : ℕ → (ZMod q)ˣ) (N : ℕ)
    (h : ∑ f ∈ Finset.univ.erase (1 : (ZMod q)ˣ →* ℂˣ),
          ‖∑ n ∈ Finset.range N, (f (w n) : ℂ)‖ < (N : ℝ)) :
    ∀ a : (ZMod q)ˣ, ∃ n ∈ Finset.range N, w n = a := by
  classical
  intro a
  by_contra hcon
  push Not at hcon
  -- with no hit, the indicator sum vanishes
  have hzero : ∀ n ∈ Finset.range N,
      ∑ f : (ZMod q)ˣ →* ℂˣ, starRingEnd ℂ (f a : ℂ) * (f (w n) : ℂ) = 0 := by
    intro n hn
    rw [hom_indicator_units a (w n), if_neg (hcon n hn)]
  have hsum : ∑ f : (ZMod q)ˣ →* ℂˣ,
      starRingEnd ℂ (f a : ℂ) * ∑ n ∈ Finset.range N, (f (w n) : ℂ) = 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero hzero
  -- split off the trivial character
  have hmem : (1 : (ZMod q)ˣ →* ℂˣ) ∈ (Finset.univ : Finset ((ZMod q)ˣ →* ℂˣ)) :=
    Finset.mem_univ _
  rw [← Finset.add_sum_erase _ _ hmem] at hsum
  have htriv : starRingEnd ℂ (((1 : (ZMod q)ˣ →* ℂˣ) a : ℂ)) *
      ∑ n ∈ Finset.range N, (((1 : (ZMod q)ˣ →* ℂˣ) (w n)) : ℂ) = (N : ℂ) := by
    simp
  rw [htriv] at hsum
  -- the rest cannot cancel `N`
  have hrest : ‖∑ f ∈ Finset.univ.erase (1 : (ZMod q)ˣ →* ℂˣ),
      starRingEnd ℂ (f a : ℂ) * ∑ n ∈ Finset.range N, (f (w n) : ℂ)‖ ≤
      ∑ f ∈ Finset.univ.erase (1 : (ZMod q)ˣ →* ℂˣ),
        ‖∑ n ∈ Finset.range N, (f (w n) : ℂ)‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun f _ => ?_)
    rw [norm_mul, RCLike.norm_conj]
    have : ‖(f a : ℂ)‖ = 1 := char_norm_one_of_hom f a
    rw [this, one_mul]
  have heq : ∑ f ∈ Finset.univ.erase (1 : (ZMod q)ˣ →* ℂˣ),
      starRingEnd ℂ (f a : ℂ) * ∑ n ∈ Finset.range N, (f (w n) : ℂ) = -(N : ℂ) := by
    linear_combination hsum
  rw [heq, norm_neg, Complex.norm_natCast] at hrest
  linarith

/-! ## The criterion for the EM walk -/

/-- **WindowFourierGain**: for every missing prime and every stage `N₀`, some window
`[N₀, N₀+N)` at which the nontrivial character sums total less than `N`.

This is the finite-horizon relaxation of `ComplexCharSumBound`.  It is implied by CCSB and
does not imply it; see the module docstring for the quantitative comparison and the
`O(q²)` reading. -/
def WindowFourierGain : Prop :=
  ∀ (q : ℕ) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (N₀ : ℕ),
    ∃ N : ℕ, 0 < N ∧
      ∑ f ∈ Finset.univ.erase (1 : (ZMod q)ˣ →* ℂˣ),
        ‖∑ j ∈ Finset.range N, (f (emWalkUnit q hq hne (N₀ + j)) : ℂ)‖ < (N : ℝ)

/-- **One horizon suffices for a hit.**  Under `WindowFourierGain` the walk reaches the
death class `-1` past every stage — which is `HittingHypothesis`, hence MC. -/
theorem windowFourierGain_hits (h : WindowFourierGain) :
    ∀ (q : ℕ) [Fact (Nat.Prime q)], IsPrime q → (∀ k, seq k ≠ q) → ∀ N₀ : ℕ,
      ∃ n, N₀ ≤ n ∧ q ∣ (prod n + 1) := by
  intro q _ hq hne N₀
  obtain ⟨N, hNpos, hN⟩ := h q hq hne N₀
  have : Fact (Nat.Prime q) := ‹_›
  have hqp : Nat.Prime q := Fact.out
  have : NeZero q := ⟨hqp.ne_zero⟩
  -- `-1` is a unit of `(ZMod q)ˣ`
  have hunit : IsUnit (-1 : ZMod q) := (isUnit_one).neg
  obtain ⟨n, hn, hval⟩ :=
    covers_of_charSum_lt (fun j => emWalkUnit q hq hne (N₀ + j)) N hN hunit.unit
  refine ⟨N₀ + n, Nat.le_add_right _ _, ?_⟩
  have : walkZ q (N₀ + n) = -1 := by
    have := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hval
    simpa [emWalkUnit] using this
  exact (walkZ_eq_neg_one_iff (N₀ + n)).mp this

/-- **One horizon at every prime implies Mullin's conjecture.**  Composing with the
walk-divisibility bridge and the hitting hypothesis. -/
theorem windowFourierGain_implies_mc (h : WindowFourierGain) : MullinConjecture := by
  refine Mullin.hh_implies_mullin ?_
  intro q hq hne N
  have : Fact (Nat.Prime q) := ⟨(isPrime_iff_natPrime q).mp hq⟩
  exact windowFourierGain_hits h q hq hne N

/-! ## The multiplier constraint at the least missing prime

A hard combinatorial fact about the least missing prime, which the character-sum framing
discards.  Past the stage at which all primes below `q` have appeared, injectivity forbids
any of them from being selected again, and `q` itself is missing — so **every subsequent
multiplier is a prime strictly greater than `q`, and they are pairwise distinct.**

Equivalently: `Pₙ + 1` is `q`-rough for all large `n`.  This is not a distributional
statement and survives whatever the character sums do; it is the sharpest unconditional
structure available at a missing prime, and is the reason `hittingSet_finite` works. -/

/-- **Past the sieve gap every multiplier exceeds the missing prime.** -/
theorem multipliers_exceed {q : ℕ} (hne : ∀ k, seq k ≠ q) (N₀ : ℕ)
    (hbelow : ∀ p, p < q → Nat.Prime p → ∃ m, m ≤ N₀ ∧ seq m = p) :
    ∀ n ≥ N₀, q < seq (n + 1) := by
  intro n hn
  have hpr : Nat.Prime (seq (n + 1)) := (isPrime_iff_natPrime _).mp (seq_isPrime (n + 1))
  rcases lt_trichotomy (seq (n + 1)) q with hlt | heq | hgt
  · obtain ⟨m, hm, hseq⟩ := hbelow _ hlt hpr
    have : m = n + 1 := seq_injective m (n + 1) hseq
    omega
  · exact absurd heq (hne (n + 1))
  · exact hgt

/-- The `q`-roughness form: no prime below `q` divides the Euclid number past the gap. -/
theorem rough_at_missing {q : ℕ} (hne : ∀ k, seq k ≠ q) (N₀ : ℕ)
    (hbelow : ∀ p, p < q → Nat.Prime p → ∃ m, m ≤ N₀ ∧ seq m = p) :
    ∀ n ≥ N₀, q < Nat.minFac (prod n + 1) := by
  intro n hn
  have hge : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
  have := multipliers_exceed hne N₀ hbelow n hn
  rwa [seq_succ, euclid_minFac_eq_nat_minFac _ hge] at this

/-- The landscape: the criterion is a genuine sufficient condition, and it follows from a
single finite horizon per prime rather than an asymptotic bound. -/
theorem one_horizon_landscape :
    (∀ (q : ℕ) [Fact (Nat.Prime q)] (w : ℕ → (ZMod q)ˣ) (N : ℕ),
      ∑ f ∈ Finset.univ.erase (1 : (ZMod q)ˣ →* ℂˣ),
        ‖∑ n ∈ Finset.range N, (f (w n) : ℂ)‖ < (N : ℝ) →
      ∀ a : (ZMod q)ˣ, ∃ n ∈ Finset.range N, w n = a) ∧
    (WindowFourierGain → MullinConjecture) :=
  ⟨fun _ _ w N h => covers_of_charSum_lt w N h, windowFourierGain_implies_mc⟩

end OneHorizon

end
