import EM.MullinGroupCore
import EM.RotorRouter

/-!
# Bridge: Scheduled Walk Coverage → Mullin's Conjecture

This file connects the scheduled walk coverage theorem (`RotorRouter.lean`) to the
Mullin Conjecture via **EMPointwiseRecurrence** — the hypothesis that the EM walk
satisfies pointwise recurrence (at each infinitely-visited unit, every multiplier
residue that generates the group is used infinitely often as the schedule).

Unlike the earlier `FairnessHypothesis` (which was probably false due to the
counterexample in Z/6Z with a fair but non-mixing schedule), `EMPointwiseRecurrence`
is the correct hypothesis: it IS sufficient for mixing, via `scheduled_walk_covers_all`.

## Main Results

* `emWalkUnit` / `emMultUnit`: the EM walk and multiplier lifted to `(ZMod q)ˣ`
* `emWalkUnit_succ`: walk recurrence at the unit level
* `EMPointwiseRecurrence`: the EM multiplier schedule has pointwise recurrence
* `empr_implies_mixing`: EMPointwiseRecurrence → MixingHypothesis (**no sorry**)
* `empr_se_implies_mullin`: EMPR + SE → MullinConjecture (**no sorry**)
-/

open Mullin Euclid MullinGroup RotorRouter

/-! ## Unit-level walk -/

/-- The EM walk lifted to units in `(ZMod q)ˣ`. -/
noncomputable def emWalkUnit (q : Nat) [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (n : Nat) : (ZMod q)ˣ :=
  Units.mk0 (walkZ q n) (walkZ_ne_zero hq hne n)

/-- The EM multiplier at step n, as a unit in `(ZMod q)ˣ`. -/
noncomputable def emMultUnit (q : Nat) [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (n : Nat) : (ZMod q)ˣ :=
  Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)

/-- Walk recurrence at the unit level: `w(n+1) = w(n) * m(n)`. -/
theorem emWalkUnit_succ (q : Nat) [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (n : Nat) :
    emWalkUnit q hq hne (n + 1) = emWalkUnit q hq hne n * emMultUnit q hq hne n := by
  ext
  simp only [emWalkUnit, emMultUnit, Units.val_mk0, Units.val_mul]
  exact walkZ_succ q n

/-! ## The correct open hypothesis -/

/-- **EM Pointwise Recurrence**: the EM walk satisfies pointwise recurrence —
    at each infinitely-visited unit, every multiplier residue from the generating
    set is used as the schedule infinitely often.

    This is the correct hypothesis that bridges scheduled walk coverage to mixing.
    Unlike global fairness, pointwise recurrence IS sufficient for coverage. -/
def EMPointwiseRecurrence : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    PointwiseRecurrence
      (emWalkUnit q hq hne)
      (emMultUnit q hq hne)
      (Set.range (emMultUnit q hq hne))

/-! ## The sorry-free bridge -/

/-- **EMPR → Mixing**: pointwise recurrence implies the walk hits `-1` infinitely
    often, via the scheduled walk coverage theorem. **No sorry.** -/
theorem empr_implies_mixing (hempr : EMPointwiseRecurrence) : MixingHypothesis := by
  intro q inst hq hne hfull N
  haveI : Fact (Nat.Prime q) := inst
  -- Apply scheduled walk coverage (Set.range matches definitionally)
  have hcovers := scheduled_walk_covers_all
    (emWalkUnit q hq hne) (emMultUnit q hq hne)
    (Set.range (emMultUnit q hq hne))
    (emWalkUnit_succ q hq hne) hfull (hempr q hq hne)
  -- Get a visit to -1 as a unit
  have hm1_ne : (-1 : ZMod q) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  let neg1 : (ZMod q)ˣ := Units.mk0 (-1) hm1_ne
  obtain ⟨n, hn, hwn⟩ := hcovers neg1 N
  exact ⟨n, hn, by
    have : (emWalkUnit q hq hne n).val = neg1.val := congrArg Units.val hwn
    simpa [emWalkUnit, neg1] using this⟩

/-- **EMPR + SE → Mullin's Conjecture**: the complete conditional reduction
    with **zero sorry**. `EMPointwiseRecurrence` and `SubgroupEscape` are the
    two independent open hypotheses at the leaves. -/
theorem empr_se_implies_mullin
    (hempr : EMPointwiseRecurrence) (hse : SubgroupEscape) : MullinConjecture :=
  se_mixing_implies_mullin hse (empr_implies_mixing hempr)
