import EM.Obstruction.RuleTransition

/-!
# The Anatomy Axis: What the Selection Rule Tells You About the Candidate

The obstruction programme has two axes.  Along the **guard** axis a proof is allowed to
*assume* facts about the candidate — a size bound, a lower bound on `ω`, smoothness — and
that axis is closed (`Obstruction.guard_analysis_complete`).  Along the **state** axis the
invariant itself records anatomy rather than congruence data, and that axis is what this
file addresses.

## The question, made precise

An omission proof reasons backwards from the selection event: *if `q` were selected at
`N`, then `N` would have to look like this*.  So the content of the axis is the strength
of the implication

    Φ N = q   ⟹   (some property of N).

For the two Euclid–Mullin rules the answers could hardly be further apart, and the
difference is exactly the difference between congruence data and anatomy.

* **`minFac N = q` is a congruence condition.**  It says `q ∣ N` and no odd prime below
  `q` divides `N` — nothing else (`minFac_eq_iff`).  Every clause is a divisibility by a
  prime `≤ q`, so the whole condition is decided by `N` modulo any rich enough modulus
  (`minFac_eq_congruence_determined`).  The min rule hands a proof **no anatomy at all**.
* **`maxFac N = q` is decided by no modulus whatever.**  For every `M` there are two
  admissible candidates congruent mod `M`, one of which has `maxFac` equal to a prime `q`
  and the other not (`maxFac_not_congruence_determined`).  The witness is cheap: an odd
  `N₁ = 2M+1` and a prime `p ≡ 1 (mod M)` with `p > N₁`; `maxFac p = p` while
  `maxFac N₁ ≤ N₁ < p`.  The max rule hands a proof genuine anatomy — `maxFac N = 5`
  forces `5`-smoothness, which is what Cox–van der Poorten's argument consumes.

So the min side's rule-supplied information is *already* inside the congruence fragment,
which `RuleTransition.no_congruence_induction_proof_of_ne_zero` shows to be empty at every
modulus.

## Anatomy as state

That leaves the possibility of an invariant carrying an anatomy component that is *not*
derived from the selection event — `ω` of the accumulator, its largest prime factor, its
smoothness.  `AnatomyInductionProof` models exactly this: the invariant is a set of pairs
(residue, anatomy value), and the step clause must admit **every** anatomy value, because
the anatomy of `Pₙ₊₁` is not a function of the residue of `Pₙ` and the candidate.

Such a proof projects onto its first coordinate and *is* a congruence-invariant induction
proof (`AnatomyInductionProof.toCongruenceProof`), so the fragment is empty for every
missing prime at every modulus (`no_anatomy_induction_proof`).  The anatomy component is
inert: `avoid` cannot consult it, because whether `q` is selected at `N` depends on `N`,
not on the accumulator's factorisation.

*Remark, not formalised here.*  The one anatomy datum of the accumulator that is
predictable is its own `ω`: `prod n` is a product of `n + 1` distinct primes
(`seq_isPrime`, `seq_injective`, `seq_dvd_prod`), so an invariant tracking `ω(prod n)` is
tracking the stage index.  Stage-dependent invariants are the graded fragment, killed by
`Obstruction.no_graded_induction_proof` — which still carries the parity hypothesis that
`RuleTransition` removed from the plain fragment, so that combination is covered only at
odd moduli for now.

## What this leaves — stated precisely

Nothing on this axis is an *invariant* question any more.  What survives is a demand for a
theorem about the anatomy of the specific integers `prod n + 1` — that they are composite
infinitely often (`AutonomousBranch.InfinitelyManyComposite`, the floor identified in
`EM/Population/CompositeFloor.lean`), or that their largest prime factor is large, or that
they are not smooth.  Those are not properties of a proof system; they are number-theoretic
facts about one orbit, and the orbit-specificity barrier (Dead End #90) applies to them
verbatim.

The residue of the obstruction programme is therefore not a wider class of invariants to
kill.  It is a single, named, open anatomy statement.
-/

noncomputable section

open Mullin Euclid MullinGroup CvdP

namespace Anatomy

/-! ## Part 1: the min rule supplies only congruence data -/

/-- **The selection condition for `minFac`, unpacked.**  For an odd candidate, `q` is the
least factor exactly when `q` divides it and no odd prime below `q` does.  Every clause is
a divisibility by a prime `≤ q`. -/
theorem minFac_eq_iff {q N : ℕ} (hq : Nat.Prime q) (hN : 3 ≤ N) (hodd : Odd N) :
    Nat.minFac N = q ↔ q ∣ N ∧ ∀ p : ℕ, Nat.Prime p → Odd p → p < q → ¬ p ∣ N := by
  have hNne1 : N ≠ 1 := by omega
  have hpr : (Nat.minFac N).Prime := Nat.minFac_prime hNne1
  have hdvd : Nat.minFac N ∣ N := Nat.minFac_dvd N
  have hne2 : Nat.minFac N ≠ 2 := by
    intro h2
    have : (2 : ℕ) ∣ N := h2 ▸ hdvd
    have := Nat.odd_iff.mp hodd
    omega
  constructor
  · intro h
    refine ⟨h ▸ hdvd, fun p hp _ hlt hpd => ?_⟩
    have := Nat.minFac_le_of_dvd hp.two_le hpd
    omega
  · rintro ⟨hqd, hsmall⟩
    have hle : Nat.minFac N ≤ q := Nat.minFac_le_of_dvd hq.two_le hqd
    have hge : q ≤ Nat.minFac N := by
      by_contra hcon
      exact hsmall _ hpr (hpr.odd_of_ne_two hne2) (by omega) hdvd
    omega

/-- Divisibility by a divisor of the modulus is a congruence condition. -/
private theorem dvd_iff_of_cast_eq {M d N₁ N₂ : ℕ} (hM : M ≠ 0) (hd : d ∣ M)
    (hcong : (N₁ : ZMod M) = (N₂ : ZMod M)) : d ∣ N₁ ↔ d ∣ N₂ := by
  have hdne : d ≠ 0 := by
    rintro rfl
    exact hM (Nat.eq_zero_of_zero_dvd hd)
  have : NeZero d := ⟨hdne⟩
  have hstep : ((N₁ : ℕ) : ZMod d) = ((N₂ : ℕ) : ZMod d) := by
    have := congrArg (ZMod.castHom hd (ZMod d)) hcong
    simpa using this
  constructor
  · intro h
    have h1 : ((N₁ : ℕ) : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
    exact (ZMod.natCast_eq_zero_iff _ _).mp (hstep ▸ h1)
  · intro h
    have h2 : ((N₂ : ℕ) : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
    exact (ZMod.natCast_eq_zero_iff _ _).mp (hstep.symm ▸ h2)

/-- **The min rule's selection condition is congruence-determined.**  At a modulus rich
enough for `q`, whether `minFac N = q` depends only on `N mod M`.  A proof that reasons
from "`q` would be selected here" therefore learns nothing a congruence invariant does not
already carry. -/
theorem minFac_eq_congruence_determined {q M : ℕ} (hq : Nat.Prime q) (hM : M ≠ 0)
    (hrich : RichEnough q M) {N₁ N₂ : ℕ}
    (h1 : 3 ≤ N₁) (ho1 : Odd N₁) (h2 : 3 ≤ N₂) (ho2 : Odd N₂)
    (hcong : (N₁ : ZMod M) = (N₂ : ZMod M)) :
    Nat.minFac N₁ = q ↔ Nat.minFac N₂ = q := by
  rw [minFac_eq_iff hq h1 ho1, minFac_eq_iff hq h2 ho2]
  constructor
  · rintro ⟨hqd, hsmall⟩
    refine ⟨(dvd_iff_of_cast_eq hM hrich.1 hcong).mp hqd, fun p hp hpodd hlt hpd => ?_⟩
    exact hsmall p hp hpodd hlt
      ((dvd_iff_of_cast_eq hM (hrich.2 p hp hpodd hlt) hcong).mpr hpd)
  · rintro ⟨hqd, hsmall⟩
    refine ⟨(dvd_iff_of_cast_eq hM hrich.1 hcong).mpr hqd, fun p hp hpodd hlt hpd => ?_⟩
    exact hsmall p hp hpodd hlt
      ((dvd_iff_of_cast_eq hM (hrich.2 p hp hpodd hlt) hcong).mp hpd)

/-! ## Part 2: the max rule supplies anatomy no modulus can see -/

/-- **The max rule's selection condition is congruence-determined at no modulus.**  For
every `M` there are admissible candidates `N₁ ≡ N₂ (mod M)` and a prime `q` with
`maxFac N₂ = q` and `maxFac N₁ ≠ q`.

Take `N₁ = 2M + 1` and, by Dirichlet, a prime `p ≡ 1 (mod M)` exceeding it: `maxFac p = p`
while `maxFac N₁ ≤ N₁ < p`.  Contrast Part 1 — this is precisely the extra information
`maxFac` hands to an omission proof, and it is why Cox–van der Poorten's argument has a
smoothness step and the min-side story has none. -/
theorem maxFac_not_congruence_determined (M : ℕ) (hM : M ≠ 0) :
    ∃ N₁ N₂ q : ℕ, Odd N₁ ∧ 3 ≤ N₁ ∧ Odd N₂ ∧ 3 ≤ N₂ ∧
      (N₁ : ZMod M) = (N₂ : ZMod M) ∧ Nat.Prime q ∧
      MaxVariant.maxFac N₂ = q ∧ MaxVariant.maxFac N₁ ≠ q := by
  have : NeZero M := ⟨hM⟩
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM
  obtain ⟨p, hpgt, hpprime, hpeq⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (a := (1 : ZMod M)) isUnit_one (2 * M + 1)
  have hN₁odd : Odd (2 * M + 1) := ⟨M, by ring⟩
  have hN₁cast : ((2 * M + 1 : ℕ) : ZMod M) = 1 := by
    push_cast [ZMod.natCast_self]; ring
  have hN₁gt1 : 1 < 2 * M + 1 := by omega
  have hmaxle : MaxVariant.maxFac (2 * M + 1) ≤ 2 * M + 1 :=
    Nat.le_of_dvd (by omega) (MaxVariant.maxFac_dvd hN₁gt1)
  refine ⟨2 * M + 1, p, p, hN₁odd, by omega, hpprime.odd_of_ne_two (by omega), by omega,
    by rw [hN₁cast, hpeq], hpprime, MaxVariant.maxFac_eq_self_of_prime hpprime, ?_⟩
  omega

/-! ## Part 3: anatomy as invariant state is inert -/

/-- An **anatomy-state induction proof**: the invariant records a residue *and* an anatomy
value drawn from an arbitrary type `α`.  The step clause must admit every anatomy value,
because the anatomy of `Pₙ₊₁` is not a function of the residue of `Pₙ` together with the
candidate — a proof that could predict it would already be an anatomy theorem about the
Euclid numbers, which is the thing being sought, not a tool for finding it. -/
structure AnatomyInductionProof (q m : ℕ) (α : Type*) where
  /-- The invariant: residues paired with anatomy values. -/
  inv : Set (ZMod m × α)
  /-- The stage from which the invariant is maintained. -/
  N₀ : ℕ
  /-- The anatomy value at that stage. -/
  a₀ : α
  /-- The invariant holds on the actual orbit at stage `N₀`. -/
  base : (((prod N₀ : ℕ) : ZMod m), a₀) ∈ inv
  /-- The induction step, uniform over candidates *and* over the unpredictable anatomy. -/
  step : ∀ r a, (r, a) ∈ inv → ∀ N : ℕ, Odd N → 3 ≤ N → (N : ZMod m) = r + 1 →
    ∀ a' : α, (r * (Nat.minFac N : ZMod m), a') ∈ inv
  /-- The conclusion: invariant states exclude capture of `q`. -/
  avoid : ∀ r a, (r, a) ∈ inv → ∀ N : ℕ, Odd N → 3 ≤ N → (N : ZMod m) = r + 1 →
    Nat.minFac N ≠ q

/-- **The anatomy component projects away.**  Forgetting it leaves a congruence-invariant
induction proof: the step survives because the anatomy value may be carried unchanged, and
`avoid` never consulted it in the first place. -/
def AnatomyInductionProof.toCongruenceProof {q m : ℕ} {α : Type*}
    (π : AnatomyInductionProof q m α) : Obstruction.CongruenceInductionProof q m where
  inv := {r | ∃ a, (r, a) ∈ π.inv}
  N₀ := π.N₀
  base := ⟨π.a₀, π.base⟩
  step := by
    rintro r ⟨a, ha⟩ N hodd h3 hcast
    exact ⟨a, π.step r a ha N hodd h3 hcast a⟩
  avoid := by
    rintro r ⟨a, ha⟩ N hodd h3 hcast
    exact π.avoid r a ha N hodd h3 hcast

/-- **No anatomy-state induction proof blocks a missing prime**, at any modulus and with
any anatomy type. -/
theorem no_anatomy_induction_proof {q m : ℕ} (α : Type*) (hq : q ∈ MissingPrimes)
    (hm : m ≠ 0) : IsEmpty (AnatomyInductionProof q m α) :=
  ⟨fun π => (RuleTransition.no_congruence_induction_proof_of_ne_zero hq hm).false
    π.toCongruenceProof⟩

/-! ## Landscape -/

/-- **The anatomy axis, settled.**  The min rule's selection condition is pure congruence
data and is decided by any rich modulus; the max rule's is decided by no modulus at all;
and an invariant that carries anatomy as state proves nothing a congruence invariant
cannot, so its fragment is empty at every modulus.

What remains is not a class of invariants but a theorem about the integers `prod n + 1`
themselves. -/
theorem anatomy_axis_landscape :
    (∀ q M : ℕ, Nat.Prime q → M ≠ 0 → RichEnough q M → ∀ N₁ N₂ : ℕ,
      3 ≤ N₁ → Odd N₁ → 3 ≤ N₂ → Odd N₂ → (N₁ : ZMod M) = (N₂ : ZMod M) →
      (Nat.minFac N₁ = q ↔ Nat.minFac N₂ = q)) ∧
    (∀ M : ℕ, M ≠ 0 → ∃ N₁ N₂ q : ℕ, Odd N₁ ∧ 3 ≤ N₁ ∧ Odd N₂ ∧ 3 ≤ N₂ ∧
      (N₁ : ZMod M) = (N₂ : ZMod M) ∧ Nat.Prime q ∧
      MaxVariant.maxFac N₂ = q ∧ MaxVariant.maxFac N₁ ≠ q) ∧
    (∀ (q m : ℕ) (α : Type), q ∈ MissingPrimes → m ≠ 0 →
      IsEmpty (AnatomyInductionProof q m α)) :=
  ⟨fun _ _ hq hM hrich _ _ h1 ho1 h2 ho2 hc =>
      minFac_eq_congruence_determined hq hM hrich h1 ho1 h2 ho2 hc,
    fun _ hM => maxFac_not_congruence_determined _ hM,
    fun _ _ α hq hm => no_anatomy_induction_proof α hq hm⟩

end Anatomy

end
