import EM.Obstruction.Fragment

/-!
# The Cox–van der Poorten Obstruction Class, Parameterised by the Selection Rule

`EM/Obstruction/MaxVariant.lean` machine-verifies the Cox–van der Poorten proof that `5`
never occurs in the *max* Euclid–Mullin sequence, and packages it as an inhabited
obstruction `MaxCvdPObstruction 5 12 {6}`.  It closes with a "Reconciliation TODO" asking
for the complementary min-side statement over a transition system parameterised by the
selection rule.  This file discharges that TODO.

## Why the existing no-go did not already cover it

`Obstruction.no_congruence_induction_proof` proves the min-side fragment empty, but only
for **odd** moduli — and the one inhabited instance in the literature lives at `m = 12`.
The exact modulus where the technique works was outside the theorem.

The oddness entered at a single point.  Extraction
(`CongruenceInductionProof.toCertificate`) has to produce, at each invariant residue `r`,
an *odd* candidate `N ≥ 3` in the class `r + 1`; for odd `m` every class contains odd
naturals, but for even `m` a class can consist entirely of even numbers, and there the
fragment's `step` and `avoid` clauses say nothing.

## The fix: carry the parity as a witness

`OddRepresentable m r` says the class `r + 1` contains an odd natural.  Three facts make
it exactly the right side condition:

* it holds along the orbit — `prod n` is even, so `prod n + 1` is odd
  (`oddRepresentable_orbit`);
* it is closed under the transition, and for a reason cheaper than expected: `r + 1` odd
  means `r` is even, so `r · s` is even whatever `s` is — no hypothesis on the multiplier
  is needed (`OddRepresentable.mul`);
* it is exactly what realisation needs — `N = c + 2 m K` stays in the class, stays odd,
  and exceeds any bound (`exists_large_odd_of_representable`), for **every** modulus.

Intersecting the fragment's invariant with `OddRepresentable` therefore yields a genuine
certificate at every modulus, and `no_congruence_induction_proof_of_ne_zero` drops the
oddness hypothesis outright.

## The unification

`R Φ m` is the one-step relation for an arbitrary selection rule `Φ`, with
`Propagating`, `ForcingState`, `Blocks` and `RuleObstruction` defined from it.  Taking
`Φ = MaxVariant.maxFac` recovers `MaxVariant.MaxR` and friends definitionally; taking
`Φ = Nat.minFac` recovers `CvdP.Transition`, and a min-side obstruction is *precisely* a
congruence-invariant induction proof (`toCongruenceProof`).

## Two forcing notions, kept straight

`ForcingState Φ` here is the *existential* reading — some admissible candidate in the
class has `Φ`-value `q`, i.e. `q` can be selected at `r`.  That is the notion
`MaxVariant` verifies, and the notion under which "S blocks q" means what it says.  It is
strictly stronger than `CvdP.ForcingState`, which is the *universal* reading (every
candidate in the class is divisible by `q` and by no smaller odd prime) used as a
sufficient condition for compulsory capture inside the certificate machinery.  Universal
forcing implies existential forcing whenever the class contains an odd candidate, so
blocking in the sense used here implies `CvdP.Blocks` under the same parity side
condition.  Consequently `no_min_rule_obstruction` does not subsume
`CvdP.no_cvdp_obstruction`; it trades that direction for the removal of both the parity
and the richness hypotheses, which is what the max-side instance at `m = 12` requires.

## The dichotomy

`cvdp_dichotomy`: the obstruction class is **inhabited** for `maxFac` at `(q, m) = (5, 12)`
and **empty** for `minFac` at every missing `q` and every modulus.  This replaces the
single-number witness `MaxVariant.cvdp_selection_rule_asymmetry` (the integer `35`) with a
statement about the whole class, and it is the min/max dichotomy at the level of proof
technique rather than of outcome.
-/

noncomputable section

open Mullin Euclid MullinGroup CvdP

namespace RuleTransition

/-! ## Part 1: parity witnesses -/

/-- The class `r + 1` contains an odd natural.  Vacuous for odd `m`; for even `m` it is
the parity condition the actual orbit satisfies. -/
def OddRepresentable (m : ℕ) (r : ZMod m) : Prop :=
  ∃ c : ℕ, Odd c ∧ (c : ZMod m) = r + 1

/-- For an odd modulus every residue is odd-representable. -/
theorem oddRepresentable_of_odd {m : ℕ} (hmodd : Odd m) (r : ZMod m) :
    OddRepresentable m r := by
  obtain ⟨N, _, hodd, _, hcast⟩ := exists_large_odd_in_class hmodd (r + 1) 0
  exact ⟨N, hodd, hcast⟩

/-- The orbit is odd-representable at every modulus: `prod n` is even. -/
theorem oddRepresentable_orbit (m n : ℕ) :
    OddRepresentable m ((prod n : ℕ) : ZMod m) := by
  have h2 : (2 : ℕ) ∣ prod n := by
    have := seq_dvd_prod 0 n (Nat.zero_le n)
    rwa [seq_zero] at this
  exact ⟨prod n + 1, Nat.odd_iff.mpr (by omega), by push_cast; ring⟩

/-- Odd-representability is closed under multiplication by **any** natural, hence under
the transition.  The reason is parity: `r + 1` odd means `r` is even, and `r · s` stays
even whatever `s` is.  No hypothesis on the multiplier is needed. -/
theorem OddRepresentable.mul (m : ℕ) {r : ZMod m} (h : OddRepresentable m r)
    (s : ℕ) : OddRepresentable m (r * (s : ZMod m)) := by
  obtain ⟨c, hcodd, hcast⟩ := h
  have hc1 : 1 ≤ c := by have := Nat.odd_iff.mp hcodd; omega
  obtain ⟨k, hk⟩ : ∃ k, c - 1 = 2 * k := ⟨(c - 1) / 2, by have := Nat.odd_iff.mp hcodd; omega⟩
  refine ⟨(c - 1) * s + 1, ?_, ?_⟩
  · have hmul : (c - 1) * s = 2 * (k * s) := by rw [hk]; ring
    exact Nat.odd_iff.mpr (by omega)
  · have hsub : ((c - 1 : ℕ) : ZMod m) = r := by
      rw [Nat.cast_sub hc1, hcast, Nat.cast_one]; ring
    push_cast
    rw [hsub]

/-- **Realisation at every modulus.**  From a parity witness, the class `r + 1` contains
odd naturals above any bound: `N = c + 2 m K`.  This is the general-modulus replacement
for `CvdP.exists_large_odd_in_class`. -/
theorem exists_large_odd_of_representable {m : ℕ} (hm : m ≠ 0) {r : ZMod m}
    (h : OddRepresentable m r) (B : ℕ) :
    ∃ N : ℕ, B < N ∧ Odd N ∧ 3 ≤ N ∧ (N : ZMod m) = r + 1 := by
  obtain ⟨c, hcodd, hcast⟩ := h
  obtain ⟨j, hj⟩ := hcodd
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
  have hbig : 2 * (B + 3) ≤ 2 * m * (B + 3) := Nat.mul_le_mul_right _ (by omega)
  refine ⟨c + 2 * m * (B + 3), by omega, ⟨j + m * (B + 3), by rw [hj]; ring⟩, by omega, ?_⟩
  push_cast [ZMod.natCast_self]
  simpa using hcast

/-! ## Part 2: extraction and emptiness at every modulus -/

variable {q m : ℕ}

/-- **Extraction at an arbitrary modulus.**  The invariant is intersected with the parity
witness; the intersection still contains the orbit tail, is still propagating, and now
admits an odd candidate at every one of its states, which is what turns `avoid` into
`blocks`. -/
def certificateOfProof (hq2 : 2 ≤ q) (hm : m ≠ 0)
    (π : Obstruction.CongruenceInductionProof q m) :
    Obstruction.Certificate (Obstruction.congruence m) q where
  S := {r | r ∈ π.inv ∧ OddRepresentable m r}
  propagating := by
    rintro r ⟨hr, hpar⟩ r' ⟨N, hNodd, h3, hcast, rfl⟩
    exact ⟨π.step _ hr N hNodd h3 hcast, hpar.mul m _⟩
  containsTail := ⟨π.N₀, fun n hn => ⟨π.orbit_mem n hn, oddRepresentable_orbit m n⟩⟩
  blocks := by
    rintro r ⟨hr, hpar⟩ hf
    obtain ⟨N, _, hNodd, hN3, hNcast⟩ :=
      exists_large_odd_of_representable hm hpar 0
    obtain ⟨hqN, hsmall⟩ := hf N hNcast
    have hNne1 : N ≠ 1 := by omega
    have hpr : (Nat.minFac N).Prime := Nat.minFac_prime hNne1
    have hdvd : Nat.minFac N ∣ N := Nat.minFac_dvd N
    have hne2 : Nat.minFac N ≠ 2 := by
      intro h2
      have : (2 : ℕ) ∣ N := h2 ▸ hdvd
      have := Nat.odd_iff.mp hNodd
      omega
    have hle : Nat.minFac N ≤ q := Nat.minFac_le_of_dvd hq2 hqN
    have hgeq : q ≤ Nat.minFac N := by
      by_contra hcon
      exact hsmall _ hpr (hpr.odd_of_ne_two hne2) (by omega) hdvd
    exact π.avoid _ hr N hNodd hN3 hNcast (by omega)

/-- **The Unprovability Theorem without the parity restriction.**  For a missing prime the
congruence fragment is empty at *every* modulus — in particular at the even moduli where
the Cox–van der Poorten argument lives. -/
theorem no_congruence_induction_proof_of_ne_zero {q m : ℕ} (hq : q ∈ MissingPrimes)
    (hm : m ≠ 0) : IsEmpty (Obstruction.CongruenceInductionProof q m) := by
  constructor
  intro π
  set m' : ℕ := m * forcingModulus q with hm'
  have hMne : forcingModulus q ≠ 0 := by
    have := Nat.odd_iff.mp (Obstruction.odd_forcingModulus hq); omega
  have hm'ne : m' ≠ 0 := Nat.mul_ne_zero hm hMne
  have hrich : RichEnough q m' := richEnough_of_forcingModulus_dvd (dvd_mul_left _ m)
  have π' := π.lift (dvd_mul_right m (forcingModulus q))
  exact (Obstruction.no_certificate (Obstruction.congruence_killable hq hm'ne hrich)).false
    (certificateOfProof hq.1.two_le hm'ne π')

/-! ## Part 3: the rule-parameterised transition system -/

variable (Φ : ℕ → ℕ)

/-- One step under the selection rule `Φ`: an admissible candidate `N` in the class
`r + 1` moves the accumulator's residue to `r · Φ N`. -/
def R (m : ℕ) (r r' : ZMod m) : Prop :=
  ∃ N : ℕ, Odd N ∧ 3 ≤ N ∧ (N : ZMod m) = r + 1 ∧ r' = r * (Φ N : ZMod m)

/-- A set of residues closed under `R Φ m`. -/
def Propagating (m : ℕ) (S : Set (ZMod m)) : Prop :=
  ∀ r ∈ S, ∀ r', R Φ m r r' → r' ∈ S

/-- `r` is a forcing state for `q` if some admissible candidate in the class `r + 1` has
`Φ`-value `q`, i.e. `q` can be selected at `r`. -/
def ForcingState (m q : ℕ) (r : ZMod m) : Prop :=
  ∃ N : ℕ, Odd N ∧ 3 ≤ N ∧ (N : ZMod m) = r + 1 ∧ Φ N = q

/-- `S` blocks `q` if it contains no forcing state. -/
def Blocks (m q : ℕ) (S : Set (ZMod m)) : Prop :=
  ∀ r ∈ S, ¬ ForcingState Φ m q r

/-- `S` contains the tail of the accumulator `acc`. -/
def ContainsTail (m : ℕ) (acc : ℕ → ℕ) (S : Set (ZMod m)) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ((acc n : ℕ) : ZMod m) ∈ S

/-- A **Cox–van der Poorten obstruction for the rule `Φ`** with accumulator `acc`: a
propagating set of residues containing the orbit tail and blocking `q`.  This is the shape
of every known omission certificate for a Euclid-type sequence. -/
structure RuleObstruction (acc : ℕ → ℕ) (q m : ℕ) (S : Set (ZMod m)) : Prop where
  propagating : Propagating Φ m S
  blocks : Blocks Φ m q S
  containsTail : ContainsTail m acc S

/-! ### The max rule is an instance -/

theorem maxR_iff (m : ℕ) (r r' : ZMod m) :
    MaxVariant.MaxR m r r' ↔ R MaxVariant.maxFac m r r' := Iff.rfl

theorem maxForcingState_iff (m q : ℕ) (r : ZMod m) :
    MaxVariant.MaxForcingState m q r ↔ ForcingState MaxVariant.maxFac m q r := Iff.rfl

/-- Cox–van der Poorten's certificate, read in the unified system. -/
theorem ruleObstruction_of_maxCvdP {q m : ℕ} {S : Set (ZMod m)}
    (h : MaxVariant.MaxCvdPObstruction q m S) :
    RuleObstruction MaxVariant.maxFac MaxVariant.mprod q m S where
  propagating := fun r hr r' hstep => h.propagating r hr r' hstep
  blocks := fun r hr hf => h.blocks r hr hf
  containsTail := ⟨1, fun n hn => h.contains_tail n hn⟩

/-! ### The min rule is an instance, and its obstructions are fragment proofs -/

theorem minR_iff (m : ℕ) (r r' : ZMod m) :
    Transition m r r' ↔ R Nat.minFac m r r' := Iff.rfl

/-- A min-side obstruction **is** a congruence-invariant induction proof: propagation is
the step case, tail-containment supplies the base, and blocking is the `avoid` clause. -/
def toCongruenceProof {q m : ℕ} {S : Set (ZMod m)}
    (h : RuleObstruction Nat.minFac prod q m S) :
    Obstruction.CongruenceInductionProof q m where
  inv := S
  N₀ := h.containsTail.choose
  base := h.containsTail.choose_spec _ le_rfl
  step := fun r hr N hodd h3 hcast =>
    h.propagating r hr _ ⟨N, hodd, h3, hcast, rfl⟩
  avoid := fun r hr N hodd h3 hcast hval =>
    h.blocks r hr ⟨N, hodd, h3, hcast, hval⟩

/-- **The min side of the obstruction class is empty**, at every modulus. -/
theorem no_min_rule_obstruction {q m : ℕ} (hq : q ∈ MissingPrimes) (hm : m ≠ 0)
    (S : Set (ZMod m)) : ¬ RuleObstruction Nat.minFac prod q m S :=
  fun h => (no_congruence_induction_proof_of_ne_zero hq hm).false (toCongruenceProof h)

/-! ## Part 4: the dichotomy -/

/-- **The Cox–van der Poorten dichotomy.**  In one and the same rule-parameterised
obstruction class: the max rule *has* a certificate — Cox–van der Poorten's, at
`q = 5`, `m = 12` — and the min rule has none, for any missing prime and any modulus.

This is the min/max asymmetry at the level of proof technique.  It supersedes the
single-number witness of `MaxVariant.cvdp_selection_rule_asymmetry` (the integer `35`,
which shows only that one particular argument fails on the min side) with a statement
about the entire class of arguments. -/
theorem cvdp_dichotomy :
    RuleObstruction MaxVariant.maxFac MaxVariant.mprod 5 12 {(6 : ZMod 12)} ∧
    (∀ (q m : ℕ) (S : Set (ZMod m)), q ∈ MissingPrimes → m ≠ 0 →
      ¬ RuleObstruction Nat.minFac prod q m S) :=
  ⟨ruleObstruction_of_maxCvdP MaxVariant.max_cvdp_obstruction_five,
    fun _ _ S hq hm => no_min_rule_obstruction hq hm S⟩

/-- Landscape: extraction now works at every modulus, the fragment is empty at every
modulus, and the obstruction class separates the two selection rules. -/
theorem rule_transition_landscape :
    (∀ q m : ℕ, q ∈ MissingPrimes → m ≠ 0 →
      IsEmpty (Obstruction.CongruenceInductionProof q m)) ∧
    (∀ (q m : ℕ) (S : Set (ZMod m)), q ∈ MissingPrimes → m ≠ 0 →
      ¬ RuleObstruction Nat.minFac prod q m S) ∧
    RuleObstruction MaxVariant.maxFac MaxVariant.mprod 5 12 {(6 : ZMod 12)} :=
  ⟨fun _ _ hq hm => no_congruence_induction_proof_of_ne_zero hq hm,
    fun _ _ S hq hm => no_min_rule_obstruction hq hm S,
    cvdp_dichotomy.1⟩

end RuleTransition

end
