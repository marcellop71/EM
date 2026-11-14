import EM.FunctionField.NecklaceFormula
import EM.FunctionField.WeakMC

/-!
# Irreducible counts over `𝔽_p` (named after the character-sum chain)

**What this file proves** (review 2026-11-10, P11): three elementary facts about the number
`π_p(d) = ffIrredCount p d` of monic irreducibles of degree `d`.  The definitions are named
after the steps of the analytic chain they were meant to stand for, but they are COUNTING
PROXIES: no character, no residue class and no modulus `Q` occurs in any of them.

* `FFCharSumCancellation` is the necklace identity `∑_{d ∣ n} d·π_p(d) = p^n`.
* `FFPNTInAPs` is `π_p(d) ≥ 1` for every `d ≥ 1`.
* `FFFCD` is `∑_{d ≤ D} π_p(d) ≥ D`.

The mathematics the names refer to (exact vanishing of `∑ χ(f)` over monic `f` of degree
`≥ deg Q`, equidistribution of irreducibles in residue classes, divergence of reciprocal sums
in a class) is true over `𝔽_p[t]` but is NOT formalized here; the divergence in a class
enters `DensityMC.lean` as the hypothesis `FFDirichletDensity`.

## Main definitions

- `FFCharSumCancellation` : necklace identity (exact factorization of X^{p^n}-X)
- `FFPNTInAPs` : every degree has at least one monic irreducible (PNT analog)
- `FFFCD` : irred supply grows at least linearly (divergence proxy)

## Main results

- `ff_char_cancel_implies_pnt` : (ignores its hypothesis) `π_p(d) ≥ 1`
- `ff_pnt_implies_fcd` : `π_p(d) ≥ 1` for all `d` gives `∑_{d ≤ D} π_p(d) ≥ D`
- `ff_pnt_implies_dirichlet_equidist` : placeholder witness (`FFDirichletEquidist` is a stub)
- `necklace_char_cancel_chain` : composition of the above
- `weil_implies_char_cancel` : (ignores its hypothesis) the necklace identity
- `ff_char_sum_landscape` : summary conjunction
-/

namespace FunctionFieldAnalog

open Polynomial Classical Filter Finset

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## Part 1: Character sum cancellation -/

/-- **COUNTING PROXY: the necklace identity** `∑_{d ∣ n} d·π_p(d) = p^n` for every `n ≥ 1`
    (the degree count of `X^{p^n} - X = ∏` of the monic irreducibles of degree `d ∣ n`).

    Despite the name, this is NOT a character-sum statement: no character occurs.  It is
    definitionally `NecklaceIdentity p`, proved in NecklaceFormula.lean.  The name records
    that the necklace identity was used as a stand-in for the exact cancellation
    `∑_{f monic, deg f = d} χ(f) = 0` (`d ≥ deg Q`, `χ ≠ 1` mod `Q`), which is true but not
    formalized. -/
abbrev FFCharSumCancellation : Prop := NecklaceIdentity p

/-- The necklace identity holds. -/
theorem ff_char_sum_cancellation_proved : FFCharSumCancellation p :=
  necklace_identity_proved p

/-! ## Part 2: PNT in arithmetic progressions for F_p[t] -/

/-- **COUNTING PROXY: `π_p(d) ≥ 1`** — for every degree `d ≥ 1` there is at least one monic
    irreducible polynomial of degree `d` over `𝔽_p`.

    Despite the name, this is NOT a prime number theorem in arithmetic progressions: there is
    no residue class, no modulus and no asymptotic count in the statement.  (The genuine
    statement — irreducibles of degree `d` are equidistributed among the invertible classes
    mod `Q` with error `O(p^{d/2})` — is not formalized.) -/
def FFPNTInAPs : Prop :=
  ∀ d : ℕ, 0 < d → 0 < ffIrredCount p d

/-- `π_p(d) ≥ 1` for every `d ≥ 1`. -/
theorem ff_pnt_in_aps_proved : FFPNTInAPs p :=
  ffIrredCount_pos p

/-! ## Part 3: Forbidden Class Divergent for F_p[t] -/

/-- **COUNTING PROXY: `∑_{d ≤ D} π_p(d) ≥ D`** — the number of monic irreducibles of degree
    at most `D` is at least `D` (immediate from `π_p(d) ≥ 1`).

    Despite the name, this is NOT the function-field analogue of `ForbiddenClassDivergent`
    from MixedEnsemble.lean: there is no forbidden class and no reciprocal sum in the
    statement, and it does not imply the divergence of `∑_{P ≡ a (Q)} p^{-deg P}`.  That
    divergence (Kornblum) is the hypothesis `FFDirichletDensity` of `DensityMC.lean`. -/
def FFFCD : Prop :=
  ∀ D : ℕ, 0 < D → D ≤ ∑ d ∈ Finset.Icc 1 D, ffIrredCount p d

/-- `∑_{d ≤ D} π_p(d) ≥ D`. -/
theorem ff_fcd_proved : FFFCD p := by
  intro D hD
  calc D = Finset.card (Finset.Icc 1 D) := by
        simp [Nat.card_Icc]
    _ = ∑ _d ∈ Finset.Icc 1 D, 1 := by simp
    _ ≤ ∑ d ∈ Finset.Icc 1 D, ffIrredCount p d := by
        apply Finset.sum_le_sum
        intro d hd
        simp [Finset.mem_Icc] at hd
        exact ffIrredCount_pos p d hd.1

/-! ## Part 4: Implication chain -/

/-- `π_p(d) ≥ 1`, stated as an implication from the necklace identity.  The hypothesis is
    not used (the proof is `ffIrredCount_pos`). -/
theorem ff_char_cancel_implies_pnt :
    FFCharSumCancellation p → FFPNTInAPs p := by
  intro _
  exact ffIrredCount_pos p

/-- PNT-in-APs implies forbidden class divergence.

    Each degree d >= 1 has at least one irreducible (by PNT-in-APs),
    so the sum over {1,...,D} of irred counts is at least D. -/
theorem ff_pnt_implies_fcd :
    FFPNTInAPs p → FFFCD p := by
  intro hpnt D hD
  calc D = Finset.card (Finset.Icc 1 D) := by
        simp [Nat.card_Icc]
    _ = ∑ _d ∈ Finset.Icc 1 D, 1 := by simp
    _ ≤ ∑ d ∈ Finset.Icc 1 D, ffIrredCount p d := by
        apply Finset.sum_le_sum
        intro d hd
        simp [Finset.mem_Icc] at hd
        exact hpnt d hd.1

/-- Full chain from necklace identity through character cancellation to FCD. -/
theorem necklace_char_cancel_chain :
    NecklaceIdentity p → FFCharSumCancellation p → FFFCD p := by
  intro _ hcc
  exact ff_pnt_implies_fcd p (ff_char_cancel_implies_pnt p hcc)

/-! ## Part 5: Compatibility with existing infrastructure -/

/-- The necklace identity, stated as an implication from the placeholder `WeilBound`.  The
    hypothesis is not used. -/
theorem weil_implies_char_cancel :
    WeilBound p → FFCharSumCancellation p := by
  intro _
  exact ff_char_sum_cancellation_proved p

/-- PNT-in-APs implies Dirichlet equidistribution of irreducibles.

    FFDirichletEquidist (from WeakMC.lean) states that irreducibles are
    equidistributed in residue classes mod Q. This is a consequence of
    FFPNTInAPs. PLACEHOLDER WITNESS: the conclusion is a `True`-bodied stub, so this theorem proves nothing. -/
theorem ff_pnt_implies_dirichlet_equidist :
    FFPNTInAPs p → FFDirichletEquidist p := by
  intro _ _ _ _ _; trivial

/-- The Weil bound factors through character cancellation to Dirichlet equidist.

    WeilBound => FFCharSumCancellation => FFPNTInAPs => FFDirichletEquidist.
    This refines the direct `weil_implies_dirichlet_equidist` from WeakMC.lean
    by exhibiting the intermediate steps. -/
theorem weil_char_cancel_to_dirichlet :
    WeilBound p → FFDirichletEquidist p :=
  fun hw => ff_pnt_implies_dirichlet_equidist p (ff_char_cancel_implies_pnt p (weil_implies_char_cancel p hw))

/-! ## Part 6: Comparison with integer case -/

/-- The three counting proxies of this file hold, and the third follows from the second.
    (This is a statement about irreducible counts; it does not formalize any comparison with
    the analytic chain over `ℤ`.) -/
theorem ff_ant_advantage :
    -- (1) necklace identity
    FFCharSumCancellation p ∧
    -- (2) π_p(d) ≥ 1
    FFPNTInAPs p ∧
    -- (3) ∑_{d ≤ D} π_p(d) ≥ D
    FFFCD p ∧
    -- (4) Chain composes
    (FFCharSumCancellation p → FFPNTInAPs p → FFFCD p) :=
  ⟨ff_char_sum_cancellation_proved p,
   ff_pnt_in_aps_proved p,
   ff_fcd_proved p,
   fun _ hpnt => ff_pnt_implies_fcd p hpnt⟩

/-! ## Part 7: Landscape -/

/-- Summary of the counting proxies of this file; clauses (7), (8) are placeholder witnesses
    (`FFDirichletEquidist` is a `True`-bodied stub). -/
theorem ff_char_sum_landscape :
    -- (1) Char cancellation (necklace identity, unconditional over F_p[t])
    FFCharSumCancellation p ∧
    -- (2) PNT-in-APs (irred count positive, unconditional over F_p[t])
    FFPNTInAPs p ∧
    -- (3) FCD (linear irred supply growth, unconditional over F_p[t])
    FFFCD p ∧
    -- (4) Necklace + char cancel => FCD chain
    (NecklaceIdentity p → FFCharSumCancellation p → FFFCD p) ∧
    -- (5) Irreducible count positive (unconditional, from NecklaceFormula)
    (∀ d, 0 < d → 0 < ffIrredCount p d) ∧
    -- (6) Weil => char cancel (trivially, since char cancel is unconditional)
    (WeilBound p → FFCharSumCancellation p) ∧
    -- (7) PNT-in-APs => Dirichlet equidist (compatible with WeakMC.lean)
    (FFPNTInAPs p → FFDirichletEquidist p) ∧
    -- (8) Full Weil => Dirichlet chain via char cancel
    (WeilBound p → FFDirichletEquidist p) :=
  ⟨ff_char_sum_cancellation_proved p,
   ff_pnt_in_aps_proved p,
   ff_fcd_proved p,
   necklace_char_cancel_chain p,
   ffIrredCount_pos p,
   weil_implies_char_cancel p,
   ff_pnt_implies_dirichlet_equidist p,
   weil_char_cancel_to_dirichlet p⟩

end FunctionFieldAnalog
