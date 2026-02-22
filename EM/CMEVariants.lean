import EM.LargeSieveSpectral

/-!
# Weaker variants of Conditional Multiplier Equidistribution (CME)

Named Props that weaken CME in various ways: fixing parameters, averaging
over fibers, relaxing "eventually" to "infinitely often", or allowing an
existential fiber choice.  Each comes with a trivial implication from CME.

All definitions are abstract (no computation).
-/
open Mullin Euclid MullinGroup RotorRouter

namespace Mullin

open scoped BigOperators

/-- `CME_d` (fixed character/fiber): for fixed `q, χ, a`, the fiber-restricted
multiplier character sum is `o(N)`.  Drops uniformity in `χ` and `a`. -/
def CME_d (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1) (a : (ZMod q)ˣ) : Prop :=
  ∀ (ε : ℝ) (_hε : 0 < ε), ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ‖fiberMultCharSum q hq hne χ a N‖ ≤ ε * N

/-- `CME_avg` (averaged over fibers): for fixed `q, χ`, the **sum** of fiber
norms is `o(N)`.  Weaker than CME since summing `q−1` fibers each bounded
by `(ε/(q−1))·N` gives `≤ ε·N`. -/
def CME_avg (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1) : Prop :=
  ∀ (ε : ℝ) (_hε : 0 < ε), ∃ N₀ : ℕ, ∀ N ≥ N₀,
    (∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖) ≤ ε * N

/-- `CME_subseq` (infinitely often): for fixed `q, χ, a`, the fiber bound
holds for infinitely many `N` rather than all sufficiently large `N`. -/
def CME_subseq (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1) (a : (ZMod q)ˣ) : Prop :=
  ∀ (ε : ℝ) (_hε : 0 < ε), ∀ N₀ : ℕ, ∃ N ≥ N₀,
    ‖fiberMultCharSum q hq hne χ a N‖ ≤ ε * N

/-- `CME_target` (existential fiber): full uniformity in `q, χ` but only
requires the bound at some *chosen* fiber `a` (replaces `∀ a` with `∃ a`). -/
def CME_target : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ a : (ZMod q)ˣ,
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ‖fiberMultCharSum q hq hne χ a N‖ ≤ ε * N

/-! ## Implications from CME -/

/-- CME implies `CME_d` (just fix parameters). -/
theorem cme_implies_CME_d (hcme : ConditionalMultiplierEquidist)
    (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hχ : χ ≠ 1) (a : (ZMod q)ˣ) :
    CME_d q hq hne χ hχ a := by
  intro ε hε
  exact hcme q hq hne χ hχ a ε hε

/-- CME implies `CME_subseq` ("eventually" implies "infinitely often"). -/
theorem cme_implies_CME_subseq (hcme : ConditionalMultiplierEquidist)
    (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hχ : χ ≠ 1) (a : (ZMod q)ˣ) :
    CME_subseq q hq hne χ hχ a := by
  intro ε hε N₀
  obtain ⟨M, hM⟩ := hcme q hq hne χ hχ a ε hε
  exact ⟨max N₀ M, le_max_left _ _, hM _ (le_max_right _ _)⟩

/-- CME implies `CME_target` (CME holds for all fibers, so pick any). -/
theorem cme_implies_CME_target (hcme : ConditionalMultiplierEquidist) :
    CME_target := by
  intro q _inst hq hne χ hχ ε hε
  exact ⟨1, hcme q hq hne χ hχ 1 ε hε⟩

open Classical in
/-- CME implies `CME_avg` (distribute `ε` across fibers, take max `N₀`).

Follows the same choose/sup/sum_le_sum/sum_const pattern as `cme_implies_dec`
in LargeSieveSpectral.lean. -/
theorem cme_implies_CME_avg (hcme : ConditionalMultiplierEquidist)
    (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hχ : χ ≠ 1) :
    CME_avg q hq hne χ hχ := by
  intro ε hε
  -- Number of fibers
  set C := Fintype.card (ZMod q)ˣ with hC_def
  have hC_pos : (0 : ℝ) < C := by
    have : 0 < C := Fintype.card_pos
    exact Nat.cast_pos.mpr this
  -- Apply CME to each fiber with ε' = ε / C
  set ε' := ε / C with hε'_def
  have hε'_pos : 0 < ε' := div_pos hε hC_pos
  have hcme_a : ∀ a : (ZMod q)ˣ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖fiberMultCharSum q hq hne χ a N‖ ≤ ε' * N :=
    fun a => hcme q hq hne χ hχ a ε' hε'_pos
  choose N₀_fn hN₀_fn using hcme_a
  -- Take the max over all fibers
  set N₀ := Finset.univ.sup N₀_fn
  refine ⟨N₀, fun N hN => ?_⟩
  -- Sum: ∑_a ‖F(a)‖ ≤ ∑_a ε'·N = C · ε'·N = ε·N
  calc (∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖)
      ≤ ∑ _a : (ZMod q)ˣ, ε' * N := by
        apply Finset.sum_le_sum
        intro a _
        apply hN₀_fn a N
        exact le_trans (Finset.le_sup (Finset.mem_univ a)) hN
    _ = C * (ε' * N) := by
        rw [Finset.sum_const, nsmul_eq_mul, hC_def, Finset.card_univ]
    _ = ε * N := by
        rw [hε'_def]
        field_simp

end Mullin
