import EM.FunctionField.IdentityTarget
import EM.FunctionField.StableTower
import EM.FunctionField.CharThree

/-!
# The dichotomy: a sequence misses a prime only by becoming a tower

`CompositeEntry.exists_missed_of_perpetual` shows, for every `p`, that a sequence whose
stages are eventually all prime misses a prime. The **dichotomy** is the converse:

> if a function-field Euclid–Mullin sequence over `𝔽_p` misses a prime, then from some stage
> on every Euclid polynomial is irreducible.

It is the statement "the only way to fail is the way `𝔽_5` fails", and it has the same form
for every `p`. It is **open** (`FFDichotomy p` is a definition, not a theorem).

## What is proved about it

* `misses_iff_eventuallyPrime_of_dichotomy` — under the dichotomy, missing a prime and being
  eventually a tower are the same property of a sequence.
* `ffMullinConjecture_iff` — for every `p`, the conjecture splits exactly into two parts:
  `FFMullinConjecture p ↔ FFDichotomy p ∧ ∀ d, FFInfinitelyManyReducible d`.
  The second part is a question about irreducibility of iterates (arithmetic dynamics of
  `x² + x`); the first part is the selection problem.
* `ffDichotomy_of_ffMullinConjecture` — the dichotomy is implied by the conjecture.
* `ffDichotomy_five` — **over `𝔽_5` the dichotomy holds while the conjecture fails**: the
  unique sequence is a tower from stage `0`.
* `ffDichotomy_two_iff`, `ffDichotomy_three_iff` — over `𝔽_2` and `𝔽_3` composite stages are
  forced, so the dichotomy is equivalent to the conjecture.

## Reading

The dichotomy is the statement that is uniform in `p`: no instance of it is known to be
false, and the `𝔽_5` counterexample to the conjecture is an instance where it is true. The
dependence on `p` is confined to the second part, whether the tower `g^n(X) + 1` can stay
irreducible, which for odd `p` is governed by the finite orbit of the critical point of
`g = X² + X`.
-/

namespace FunctionFieldAnalog

namespace Dichotomy

open Polynomial CompositeEntry FFDegreeTelescope

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The sequence misses some monic irreducible polynomial. -/
def Misses (d : FFEMData p) : Prop :=
  ∃ Q : (ZMod p)[X], Q.Monic ∧ Irreducible Q ∧ ∀ n, d.ffSeq n ≠ Q

/-- From some stage on every Euclid polynomial is irreducible: the sequence is eventually a
    tower of compositions of `X² + X`. -/
def EventuallyPrime (d : FFEMData p) : Prop :=
  ∃ N, FFPerpetualIrreducibility d N

/-- **A tower misses a prime (any `p`).** -/
theorem misses_of_eventuallyPrime (d : FFEMData p) (h : EventuallyPrime d) : Misses d := by
  obtain ⟨N, hN⟩ := h
  exact exists_missed_of_perpetual d N hN

theorem eventuallyPrime_iff_not_infinitelyManyReducible (d : FFEMData p) :
    EventuallyPrime d ↔ ¬ FFInfinitelyManyReducible d := by
  rw [ffInfinitelyManyReducible_iff, EventuallyPrime]
  push Not
  rfl

theorem ffMullinConjecture_iff_not_misses (p : ℕ) [Fact (Nat.Prime p)] :
    FFMullinConjecture p ↔ ∀ d : FFEMData p, ¬ Misses d := by
  constructor
  · rintro h d ⟨Q, hQm, hQi, hQ⟩
    obtain ⟨n, hn⟩ := h d Q hQm hQi
    exact hQ n hn
  · intro h d Q hQm hQi
    by_contra hcon
    push Not at hcon
    exact h d ⟨Q, hQm, hQi, hcon⟩

/-- **The dichotomy (open).** A sequence over `𝔽_p` that misses a prime is eventually a
    tower. -/
def FFDichotomy (p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ∀ d : FFEMData p, Misses d → EventuallyPrime d

/-- Under the dichotomy, missing a prime and being eventually a tower coincide. -/
theorem misses_iff_eventuallyPrime_of_dichotomy (h : FFDichotomy p) (d : FFEMData p) :
    Misses d ↔ EventuallyPrime d :=
  ⟨h d, misses_of_eventuallyPrime d⟩

/-- The conjecture implies the dichotomy. -/
theorem ffDichotomy_of_ffMullinConjecture (h : FFMullinConjecture p) : FFDichotomy p :=
  fun d hd => absurd hd ((ffMullinConjecture_iff_not_misses p).mp h d)

/-- **The conjecture splits into the dichotomy and a statement about towers (any `p`).** -/
theorem ffMullinConjecture_iff (p : ℕ) [Fact (Nat.Prime p)] :
    FFMullinConjecture p ↔ FFDichotomy p ∧ ∀ d : FFEMData p, FFInfinitelyManyReducible d := by
  constructor
  · intro h
    exact ⟨ffDichotomy_of_ffMullinConjecture h,
      fun d => infinitelyManyReducible_of_ffMullinConjecture h d⟩
  · rintro ⟨hdich, hinf⟩
    rw [ffMullinConjecture_iff_not_misses]
    intro d hd
    exact (eventuallyPrime_iff_not_infinitelyManyReducible d).mp (hdich d hd) (hinf d)

/-- Where composite stages are forced, the dichotomy is the conjecture. -/
theorem ffDichotomy_iff_of_forced (hinf : ∀ d : FFEMData p, FFInfinitelyManyReducible d) :
    FFDichotomy p ↔ FFMullinConjecture p :=
  ⟨fun h => (ffMullinConjecture_iff p).mpr ⟨h, hinf⟩, ffDichotomy_of_ffMullinConjecture⟩

theorem ffDichotomy_two_iff : FFDichotomy 2 ↔ FFMullinConjecture 2 :=
  ffDichotomy_iff_of_forced CompositeFloors.infinitelyManyReducible_of_two

theorem ffDichotomy_three_iff : FFDichotomy 3 ↔ FFMullinConjecture 3 :=
  ffDichotomy_iff_of_forced CharThree.infinitelyManyReducible

/-- **Over `𝔽_5` the dichotomy holds**, although the conjecture fails
    (`not_ffMullinConjecture_five`): the unique sequence is a tower from stage `0`. -/
theorem ffDichotomy_five : FFDichotomy 5 := by
  intro d _
  refine ⟨0, fun n _ => ?_⟩
  rw [(ffEMData_five_eq_tower d).2]
  exact StableTower.tower_euclid_irreducible n

end Dichotomy

end FunctionFieldAnalog
