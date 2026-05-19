import EM.Obstruction.Calculus

/-!
# The Proof-Theoretic Dichotomy: Invariant-Style Proofs Cannot Disprove MC

This file upgrades the No-Invariant Theorem from *semantic* invariants to
*syntactic* proofs.  It defines a proof fragment — **congruence-invariant
induction proofs** of eventual omission — and proves:

* **Soundness** (`CongruenceInductionProof.eventually_avoids`): an inhabitant of
  the fragment genuinely proves that `q` is eventually never captured.  The
  fragment is a real proof system.
* **Extraction** (`CongruenceInductionProof.toCertificate`): every fragment
  proof yields a `Certificate` of the obstruction calculus.  This is the
  proof-mining step: an induction proof whose invariant is a congruence
  condition can only maintain its step case by handling *every* candidate the
  residue admits, so its invariant is propagating for the over-approximated
  transition; and its conclusion can only exclude capture by inspecting the
  class, so its invariant blocks forcing states.
* **Unprovability** (`no_congruence_induction_proof`): for a missing prime the
  fragment is EMPTY, at every odd modulus — via extraction, `congruence_killable`
  and the generic Emptiness Theorem.  Proofs lift along modulus divisibility
  (`CongruenceInductionProof.lift`) — NOTE: at the proof level the
  `BlocksDeath` caveat of `NoInvariant.lean` Part 6 dissolves, because every
  field of a fragment proof is universally quantified over candidates, and
  candidates cast down.  Richness is then obtained by lifting, so no richness
  hypothesis appears in the final statement.
* **Completeness on appeared primes** (`appeared_congruence_proof`): for a
  prime that HAS appeared, the fragment is inhabited — Euclid's argument
  ("once in the product, never again a factor") *is* a congruence-invariant
  proof, with invariant `q ∣ r`.
* **The provability equivalence** (`congruence_provability_iff`):

      the fragment proves "q eventually avoided"  ⟺  q appears.

  Congruence-inductive provability *decides* membership in the sequence.
* **The max-side control** (`maxProofFive`): the corresponding max-rule
  fragment is INHABITED at `q = 5`, `m = 12` — Cox–van der Poorten's proof is
  literally a fragment inhabitant, and fragment soundness re-derives the
  omission (`max_fragment_proves_five`).  So the provability equivalence
  FAILS for the max rule (`max_provability_not_iff`): the fragment proves an
  omission there.  The dichotomy, at the level of proofs:

      the same proof system that proves the max sequence misses 5
      provably cannot establish any omission for the min sequence.

## Scope, honestly

Parts 1–5 capture *uniform* congruence-invariant induction: the invariant is a
set of residues mod `m`, fixed in `n`, and the step and conclusion are uniform
over candidates in a class.  This covers every omission proof in the
Cox–van der Poorten / classical-mod-`m` genre.

**Part 6 removes two of the three restrictions, and then some.**
`OmegaGradedInductionProof` lets the invariant depend on the step index, lets
the proof assume an archimedean lower bound `B n` on the candidate, *and* lets
it assume the candidate has at least `K n` distinct prime factors.  Admissible
guards are `B n ≤ prod n + 1` and `K n ≤ ω(prod n + 1)` — i.e. up to the size
and the factor count the Euclid number actually has.  The fragment is still
empty for every missing prime (`no_omega_graded_induction_proof`), and
provability still decides appearance (`omega_graded_provability_iff`).

Why each relaxation is free:

* *time-dependence* — the congruence enrichment is killable in ONE step
  (`congruence_killableIn`), so a graded invariant is dragged onto a forcing
  state exactly as a constant one is;
* *size* — Dirichlet supplies arbitrarily large primes
  (`CvdP.free_transition_large`, `CvdP.exists_large_odd_in_class`);
* *`ω`* — multiplying by a prime `≡ 1 (mod m)` above the current value changes
  neither the residue class nor the least factor while raising `ω` by one
  (`CvdP.exists_class_omega`).

So `ω` is **not** the surviving part of anatomy.

**Part 7 closes the remaining axis.**  The one direction Part 6 left open is a
guard bounding the candidate from *above* — `y`-smoothness, or control of the
largest prime factor, which is the max-side ingredient since `maxFac N = q`
*is* a smoothness condition.  It closes not by another killing argument but
because the guard is **inadmissible**: the Euclid numbers are eventually
`y`-rough for every `y` (`CvdP.eventually_rough`), so a `y`-smooth fragment
excludes the orbit's own candidates and proves nothing about the orbit
(`smooth_fragment_never_sound`).  With `fragment_analysis_complete`, the
analysis for fixed-threshold guards is finished in both directions.

What is left:

* **growing** smoothness guards `y(n)`, admissible only under an unproven
  anatomy statement about `P⁺(Pₙ+1)` — vacuous when loose, and when tight
  enough to be useful placing one on the branch where the Euclid numbers are
  eventually prime, on which MC is false anyway (Dead End #146);
Reciprocity data between sequence elements — symbols against moduli that grow
with the orbit, the Booker genre — was the third disclaimer, and it is now
handled in `EM/Reciprocity/NoReciprocityInvariant.lean`: by (R1) such an
invariant is a congruence invariant at the growing symbol modulus `Πₙ`, and the
fragment is still empty (`Reciprocity.no_reciprocity_induction_proof`).

Design choice making unprovability STRONGER: the fragment's conclusion field
`avoid` only requires the proof to exclude *capture* (`minFac N ≠ q`), the
weakest conclusion an omission proof can have — not divisibility avoidance
(`q ∤ N`).  A broader fragment makes its emptiness a stronger theorem.
-/

open Mullin Euclid MullinGroup RotorRouter
open Classical
open CvdP

namespace Obstruction

/-! ## Part 1: The fragment -/

/-- A **congruence-invariant induction proof** that the prime `q` is eventually
never captured by the min rule.  This is the common shape of every classical
omission proof in the Euclid–Mullin family, made into an object:

* `inv` — the induction hypothesis, a set of residues mod `m` (this is what
  "the invariant is expressible as a congruence condition" means);
* `base` — the invariant holds at some stage `N₀` of the actual orbit;
* `step` — the induction step.  Because the proof's only knowledge of the orbit
  is the residue `r`, the step must be valid for EVERY admissible candidate
  `N` in the class `r + 1` (odd, `≥ 3`): the proof cannot distinguish
  candidates the invariant does not separate;
* `avoid` — the conclusion: at an invariant state, no admissible candidate is
  captured by `q`. -/
structure CongruenceInductionProof (q m : ℕ) where
  /-- The induction hypothesis: a congruence condition mod `m`. -/
  inv : Set (ZMod m)
  /-- The stage from which the invariant is maintained. -/
  N₀ : ℕ
  /-- The invariant holds on the actual orbit at stage `N₀`. -/
  base : ((prod N₀ : ℕ) : ZMod m) ∈ inv
  /-- The induction step, uniform over admissible candidates in the class. -/
  step : ∀ r ∈ inv, ∀ N : ℕ, Odd N → 3 ≤ N → (N : ZMod m) = r + 1 →
    r * (Nat.minFac N : ZMod m) ∈ inv
  /-- The conclusion: invariant states exclude capture of `q`. -/
  avoid : ∀ r ∈ inv, ∀ N : ℕ, Odd N → 3 ≤ N → (N : ZMod m) = r + 1 →
    Nat.minFac N ≠ q

namespace CongruenceInductionProof

variable {q m : ℕ}

/-- The actual candidate at stage `n` is admissible, and the invariant follows
the actual orbit from `N₀` on. -/
theorem orbit_mem (π : CongruenceInductionProof q m) :
    ∀ n ≥ π.N₀, ((prod n : ℕ) : ZMod m) ∈ π.inv := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact π.base
  | succ n hn ih =>
    have hge : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
    have hodd : Odd (prod n + 1) := by
      have h2 : (2 : ℕ) ∣ prod n := by
        have := seq_dvd_prod 0 n (Nat.zero_le n)
        rwa [seq_zero] at this
      obtain ⟨k, hk⟩ := h2
      exact Nat.odd_iff.mpr (by omega)
    have hcast : ((prod n + 1 : ℕ) : ZMod m) = ((prod n : ℕ) : ZMod m) + 1 := by
      push_cast; ring
    have h3 : 3 ≤ prod n + 1 := by have := prod_ge_two n; omega
    have hmem := π.step _ (ih) (prod n + 1) hodd h3 hcast
    have hstep : prod (n + 1) = prod n * Nat.minFac (prod n + 1) := by
      rw [prod_succ, seq_succ, euclid_minFac_eq_nat_minFac _ hge]
    rw [hstep]
    push_cast
    exact hmem

/-- **Soundness of the fragment**: an inhabitant genuinely proves that `q` is
eventually never captured.  The fragment is a real proof system, not a straw
man. -/
theorem eventually_avoids (π : CongruenceInductionProof q m) :
    ∀ n ≥ π.N₀, seq (n + 1) ≠ q := by
  intro n hn
  have hge : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
  have hodd : Odd (prod n + 1) := by
    have h2 : (2 : ℕ) ∣ prod n := by
      have := seq_dvd_prod 0 n (Nat.zero_le n)
      rwa [seq_zero] at this
    obtain ⟨k, hk⟩ := h2
    exact Nat.odd_iff.mpr (by omega)
  have hcast : ((prod n + 1 : ℕ) : ZMod m) = ((prod n : ℕ) : ZMod m) + 1 := by
    push_cast; ring
  have h3 : 3 ≤ prod n + 1 := by have := prod_ge_two n; omega
  have hav := π.avoid _ (π.orbit_mem n hn) (prod n + 1) hodd h3 hcast
  rw [seq_succ, euclid_minFac_eq_nat_minFac _ hge]
  exact hav

/-- **Proofs lift along modulus divisibility.**  Every field of a fragment
proof is universally quantified over candidates, and candidates at the finer
modulus cast down to candidates at the coarser one — so the `BlocksDeath`
subtlety of certificate lifting (`NoInvariant.lean` Part 6) does not arise at
the proof level. -/
def lift {m' : ℕ} (h : m ∣ m') (π : CongruenceInductionProof q m) :
    CongruenceInductionProof q m' where
  inv := (ZMod.castHom h (ZMod m)) ⁻¹' π.inv
  N₀ := π.N₀
  base := by
    show (ZMod.castHom h (ZMod m)) ((prod π.N₀ : ℕ) : ZMod m') ∈ π.inv
    rw [map_natCast]
    exact π.base
  step := by
    intro r hr N hodd h3 hcast
    show (ZMod.castHom h (ZMod m)) (r * (Nat.minFac N : ZMod m')) ∈ π.inv
    rw [map_mul, map_natCast]
    refine π.step _ hr N hodd h3 ?_
    have := congrArg (ZMod.castHom h (ZMod m)) hcast
    rwa [map_natCast, map_add, map_one] at this
  avoid := by
    intro r hr N hodd h3 hcast
    refine π.avoid _ hr N hodd h3 ?_
    have := congrArg (ZMod.castHom h (ZMod m)) hcast
    rwa [map_natCast, map_add, map_one] at this

/-- **The extraction theorem** (proof mining): a fragment proof yields a
certificate of the obstruction calculus.  Propagation is the step case read
semantically; tail-containment is soundness of the base-plus-step induction;
blocking is the point with content — at an invariant state, a forcing state
would provide an admissible candidate whose `minFac` IS `q` (choose an odd
representative of the class, possible since `m` is odd), contradicting
`avoid`. -/
def toCertificate (hq2 : 2 ≤ q) (hmodd : Odd m)
    (π : CongruenceInductionProof q m) : Certificate (congruence m) q where
  S := π.inv
  propagating := by
    rintro r hr r' ⟨N, hodd, h3, hcast, rfl⟩
    exact π.step _ hr N hodd h3 hcast
  containsTail := ⟨π.N₀, π.orbit_mem⟩
  blocks := by
    show ∀ r ∈ π.inv, ¬ ForcingState q m r
    intro r hr hf
    have hm : m ≠ 0 := by
      have := Nat.odd_iff.mp hmodd
      omega
    -- an odd candidate `N ≥ 3` in the class `r + 1`
    obtain ⟨N₁, hN₁⟩ := exists_nat_in_class hm (r + 1)
    have hmm : m % 2 = 1 := Nat.odd_iff.mp hmodd
    obtain ⟨N, hNodd, hN3, hNcast⟩ :
        ∃ N : ℕ, Odd N ∧ 3 ≤ N ∧ (N : ZMod m) = r + 1 := by
      have hcast3 : ((N₁ + 3 * m : ℕ) : ZMod m) = r + 1 := by
        push_cast [ZMod.natCast_self]
        simpa using hN₁
      have hcast4 : ((N₁ + 4 * m : ℕ) : ZMod m) = r + 1 := by
        push_cast [ZMod.natCast_self]
        simpa using hN₁
      rcases Nat.even_or_odd N₁ with he | ho
      · have h1 : N₁ % 2 = 0 := Nat.even_iff.mp he
        exact ⟨N₁ + 3 * m, Nat.odd_iff.mpr (by omega), by omega, hcast3⟩
      · have h1 : N₁ % 2 = 1 := Nat.odd_iff.mp ho
        exact ⟨N₁ + 4 * m, Nat.odd_iff.mpr (by omega), by omega, hcast4⟩
    -- the forcing data at that candidate
    obtain ⟨hqN, hsmall⟩ := hf N hNcast
    -- its least factor is exactly `q`, contradicting `avoid`
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

end CongruenceInductionProof

/-! ## Part 2: Unprovability for missing primes -/

/-- The forcing modulus is odd (it is a product of odd primes, led by the
missing prime itself, which cannot be `2` since `2 = seq 0` appears). -/
theorem odd_forcingModulus {q : ℕ} (hq : q ∈ MissingPrimes) :
    Odd (forcingModulus q) := by
  have hqp : Nat.Prime q := hq.1
  have hq2 : q ≠ 2 := fun h => hq.2 0 (by rw [seq_zero, h])
  have hqodd : ¬ (2 : ℕ) ∣ q := fun h =>
    hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hqp).mp h).symm
  rcases Nat.even_or_odd (forcingModulus q) with he | ho
  swap
  · exact ho
  exfalso
  have h2 : (2 : ℕ) ∣ forcingModulus q := he.two_dvd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
  · exact hqodd h
  · obtain ⟨p, hp, hpd⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff (fun p => p)).mp h
    have hodd : Odd p := (Finset.mem_filter.mp hp).2.2
    have : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two
      (Finset.mem_filter.mp hp).2.1).mp hpd).symm
    rw [this] at hodd
    exact (by decide : ¬ Odd 2) hodd

/-- **The Unprovability Theorem.**  For a missing prime `q`, the congruence
fragment is EMPTY at every odd modulus: no congruence-invariant induction
proof of `q`'s eventual avoidance exists.

No richness hypothesis: a proof at a poor modulus lifts to the rich modulus
`m · M(q)` (proofs lift unconditionally), where extraction and killability
apply.  The min sequence's avoidances — if any exist — are invisible to this
entire proof genre. -/
theorem no_congruence_induction_proof {q m : ℕ} (hq : q ∈ MissingPrimes)
    (hmodd : Odd m) : IsEmpty (CongruenceInductionProof q m) := by
  -- NOTE: the oddness hypothesis is removable; see
  -- `RuleTransition.no_congruence_induction_proof_of_ne_zero`, which carries the parity
  -- of the class as a witness and covers the even moduli where Cox–van der Poorten lives.
  constructor
  intro π
  -- lift to the rich modulus
  set m' : ℕ := m * forcingModulus q with hm'
  have hm'odd : Odd m' := hmodd.mul (odd_forcingModulus hq)
  have hm'ne : m' ≠ 0 := by
    have := Nat.odd_iff.mp hm'odd
    omega
  have hrich : RichEnough q m' :=
    richEnough_of_forcingModulus_dvd (dvd_mul_left _ m)
  have π' := π.lift (dvd_mul_right m (forcingModulus q))
  exact (no_certificate (congruence_killable hq hm'ne hrich)).false
    (π'.toCertificate hq.1.two_le hm'odd)

/-! ## Part 3: Completeness on appeared primes

For a prime that HAS appeared, the fragment is inhabited: Euclid's own
argument — once `q` divides the accumulator, it divides it forever and can
never divide a candidate — is a congruence-invariant proof, with invariant
"`q ∣ r`". -/

/-- Euclid's argument as a fragment inhabitant: if `seq k = q` and `q ∣ m`,
the invariant `{r : q ∣ r}` (read through the projection to `ZMod q`) gives a
congruence-invariant proof that `q` is eventually never captured. -/
def appearedProof {q m k : ℕ} (hqp : Nat.Prime q) (hk : seq k = q)
    (hqm : q ∣ m) : CongruenceInductionProof q m where
  inv := (ZMod.castHom hqm (ZMod q)) ⁻¹' {0}
  N₀ := k
  base := by
    have : NeZero q := ⟨hqp.pos.ne'⟩
    show (ZMod.castHom hqm (ZMod q)) ((prod k : ℕ) : ZMod m) ∈ ({0} : Set (ZMod q))
    rw [map_natCast]
    have hdvd : q ∣ prod k := hk ▸ seq_dvd_prod k k le_rfl
    simpa using (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  step := by
    intro r hr N _ _ _
    show (ZMod.castHom hqm (ZMod q)) (r * (Nat.minFac N : ZMod m)) ∈ ({0} : Set (ZMod q))
    have hr0 : (ZMod.castHom hqm (ZMod q)) r = 0 := hr
    rw [map_mul, hr0, zero_mul]
    rfl
  avoid := by
    intro r hr N _ _ hcast hmf
    have : NeZero q := ⟨hqp.pos.ne'⟩
    have hr0 : (ZMod.castHom hqm (ZMod q)) r = 0 := hr
    -- `q ∣ N` since `minFac N = q`
    have hqN : q ∣ N := hmf ▸ Nat.minFac_dvd N
    -- but `N ≡ 1 (mod q)` since `N ≡ r + 1` and `q ∣ r`
    have h1 : ((N : ℕ) : ZMod q) = 1 := by
      have := congrArg (ZMod.castHom hqm (ZMod q)) hcast
      rwa [map_natCast, map_add, map_one, hr0, zero_add] at this
    have h0 : ((N : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hqN
    rw [h0] at h1
    -- h1 : (0 : ZMod q) = 1, so q ∣ 1, contradicting q prime
    have h10 : ((1 : ℕ) : ZMod q) = 0 := by push_cast; exact h1.symm
    have hdvd1 : q ∣ 1 := (ZMod.natCast_eq_zero_iff _ _).mp h10
    have := Nat.le_of_dvd one_pos hdvd1
    have h2q := hqp.two_le
    omega

/-- The fragment is inhabited for appeared primes. -/
theorem appeared_congruence_proof {q m : ℕ} (hqp : Nat.Prime q) (hqm : q ∣ m)
    (h : ∃ k, seq k = q) : Nonempty (CongruenceInductionProof q m) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨appearedProof hqp hk hqm⟩

/-! ## Part 4: The provability equivalence, and the dichotomy -/

/-- **Provability decides appearance.**  For a prime `q` and an odd modulus
`m` divisible by `q`: the congruence fragment proves "`q` eventually avoided"
IF AND ONLY IF `q` appears in the sequence.

The forward direction is the Unprovability Theorem (a proof for a missing
prime cannot exist); the backward direction is Euclid's argument.  So within
this proof genre, provability of avoidance and membership in the sequence are
the SAME predicate — the fragment can certify avoidance only for the trivial
reason. -/
theorem congruence_provability_iff {q m : ℕ} (hqp : Nat.Prime q)
    (hmodd : Odd m) (hqm : q ∣ m) :
    Nonempty (CongruenceInductionProof q m) ↔ ∃ k, seq k = q := by
  constructor
  · intro hπ
    by_contra hcon
    have hmiss : q ∈ MissingPrimes := ⟨hqp, fun k hk => hcon ⟨k, hk⟩⟩
    exact (no_congruence_induction_proof hmiss hmodd).false hπ.some
  · exact appeared_congruence_proof hqp hqm

/-! ### The max-side fragment: the control -/

open MaxVariant

/-- The max-rule fragment: identical shape, `maxFac` in place of `minFac`,
the max orbit in place of the min orbit. -/
structure MaxCongruenceInductionProof (q m : ℕ) where
  inv : Set (ZMod m)
  N₀ : ℕ
  base : ((mprod N₀ : ℕ) : ZMod m) ∈ inv
  step : ∀ r ∈ inv, ∀ N : ℕ, Odd N → 3 ≤ N → (N : ZMod m) = r + 1 →
    r * (maxFac N : ZMod m) ∈ inv
  avoid : ∀ r ∈ inv, ∀ N : ℕ, Odd N → 3 ≤ N → (N : ZMod m) = r + 1 →
    maxFac N ≠ q

/-- Soundness of the max fragment. -/
theorem MaxCongruenceInductionProof.eventually_avoids {q m : ℕ}
    (π : MaxCongruenceInductionProof q m) : ∀ n ≥ π.N₀, mseq (n + 1) ≠ q := by
  have horbit : ∀ n ≥ π.N₀, ((mprod n : ℕ) : ZMod m) ∈ π.inv := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact π.base
    | succ n hn ih =>
      have hmem := π.step _ ih (mprod n + 1) (Nat.odd_iff.mpr (mprod_succ_odd n))
        (by have := mprod_ge_two n; omega) (by push_cast; ring)
      rw [mprod_succ, mseq_succ]
      push_cast
      exact hmem
  intro n hn
  have hav := π.avoid _ (horbit n hn) (mprod n + 1) (Nat.odd_iff.mpr (mprod_succ_odd n))
    (by have := mprod_ge_two n; omega) (by push_cast; ring)
  rw [mseq_succ]
  exact hav

/-- **Cox–van der Poorten's proof IS a fragment inhabitant**: invariant `{6}`
mod `12`, base stage `1`. -/
def maxProofFive : MaxCongruenceInductionProof 5 12 where
  inv := {(6 : ZMod 12)}
  N₀ := 1
  base := mprod_mem_six le_rfl
  step := fun r hr N hodd h3 hcast =>
    maxPropagating_six r hr _ ⟨N, hodd, h3, hcast, rfl⟩
  avoid := fun r hr N hodd h3 hcast hmf =>
    maxBlocks_six_five r hr ⟨N, hodd, h3, hcast, hmf⟩

/-- The max fragment PROVES the omission of `5`: fragment soundness applied to
the CvdP inhabitant re-derives the headline theorem. -/
theorem max_fragment_proves_five : ∀ n ≥ 1, mseq (n + 1) ≠ 5 :=
  maxProofFive.eventually_avoids

/-- **The provability equivalence FAILS for the max rule**: the fragment is
inhabited at `q = 5` although `5` never appears.  This is the exact point at
which the min and max sequences separate at the level of proofs. -/
theorem max_provability_not_iff :
    ¬ (Nonempty (MaxCongruenceInductionProof 5 12) ↔ ∃ k, mseq k = 5) := by
  intro h
  obtain ⟨k, hk⟩ := h.mp ⟨maxProofFive⟩
  exact five_not_mem_mseq k hk

/-! ## Part 5: The dichotomy, as one statement -/

/-- **The proof-theoretic dichotomy.**
1.  The congruence fragment is sound (its inhabitants prove eventual
    avoidance) — for both rules.
2.  MIN: for every missing prime and every odd modulus the fragment is empty;
    and provability is *equivalent* to appearance (for `q ∣ m`).
3.  MAX: the fragment is inhabited at `5` mod `12`, proves the omission, and
    the provability-appearance equivalence fails.

The same proof system that proves the max sequence misses `5` provably cannot
establish any omission for the min sequence. -/
theorem proof_theoretic_dichotomy :
    -- soundness, min
    (∀ q m : ℕ, ∀ π : CongruenceInductionProof q m, ∀ n ≥ π.N₀, seq (n + 1) ≠ q) ∧
    -- unprovability, min
    (∀ q m : ℕ, q ∈ MissingPrimes → Odd m → IsEmpty (CongruenceInductionProof q m)) ∧
    -- provability ≡ appearance, min
    (∀ q m : ℕ, Nat.Prime q → Odd m → q ∣ m →
      (Nonempty (CongruenceInductionProof q m) ↔ ∃ k, seq k = q)) ∧
    -- provability, max — and the equivalence fails there
    Nonempty (MaxCongruenceInductionProof 5 12) ∧
    (∀ n ≥ 1, mseq (n + 1) ≠ 5) ∧
    ¬ (Nonempty (MaxCongruenceInductionProof 5 12) ↔ ∃ k, mseq k = 5) :=
  ⟨fun _ _ π => π.eventually_avoids,
    fun _ _ hq hm => no_congruence_induction_proof hq hm,
    fun _ _ hqp hm hqm => congruence_provability_iff hqp hm hqm,
    ⟨maxProofFive⟩,
    max_fragment_proves_five,
    max_provability_not_iff⟩

/-! ## Part 6: Widening the fragment — time-dependent invariants and size guards

Part 1's "Scope, honestly" disclaims three things the fragment does not cover.  Two of
them fall here, to the same argument:

* **time-dependent invariants** `inv n` — the invariant may now depend on the step index;
* **invariants using the size of `Pₙ`** — the step and conclusion clauses need only be
  established for candidates `N ≥ B n`, so the proof may assume an archimedean lower
  bound on the Euclid number.

Neither helps.  Time-dependence dies because the killability witness of the congruence
enrichment is a *single* transition (`congruence_killableIn`), so a graded invariant is
dragged from level `n` to level `n + 1` and the blocking condition is imposed there too.
Size guards die because `free_transition_large` and `exists_large_odd_in_class` supply
candidates above any prescribed bound — Dirichlet hands out arbitrarily large primes, so
an archimedean *lower* bound costs the argument nothing.

The admissible range for `B` is generous: `B n ≤ prod n + 1`, i.e. the proof may restrict
attention to candidates as large as the actual Euclid number.  Beyond that the guard is
vacuous (it excludes the orbit's own candidate, so the fragment says nothing about the
orbit and soundness fails).

What still escapes, and is the boundary of the whole programme: an *upper* bound on the
candidate, or a smoothness / largest-prime-factor condition.  Both constructions above
produce candidates with huge prime cofactors, so a fragment demanding `y`-smoothness is
not reached.  That is exactly the max-side ingredient of Cox–van der Poorten, and the
anatomy facet of Dead End #146. -/

/-- A **graded, size-guarded congruence-invariant induction proof**: `inv` may depend on
the stage, and the step and conclusion clauses are required only for candidates `N ≥ B n`.
Taking `B ≡ 0` and a constant `inv` recovers `CongruenceInductionProof`
(`CongruenceInductionProof.toGraded`). -/
structure GradedInductionProof (q m : ℕ) (B : ℕ → ℕ) where
  /-- The induction hypothesis at each stage. -/
  inv : ℕ → Set (ZMod m)
  /-- The stage from which the invariant is maintained. -/
  N₀ : ℕ
  /-- The invariant holds on the actual orbit at stage `N₀`. -/
  base : ((prod N₀ : ℕ) : ZMod m) ∈ inv N₀
  /-- The induction step, for candidates at least `B n`. -/
  step : ∀ n, ∀ r ∈ inv n, ∀ N : ℕ, Odd N → 3 ≤ N → B n ≤ N → (N : ZMod m) = r + 1 →
    r * (Nat.minFac N : ZMod m) ∈ inv (n + 1)
  /-- The conclusion, for candidates at least `B n`. -/
  avoid : ∀ n, ∀ r ∈ inv n, ∀ N : ℕ, Odd N → 3 ≤ N → B n ≤ N → (N : ZMod m) = r + 1 →
    Nat.minFac N ≠ q

namespace GradedInductionProof

variable {q m : ℕ} {B : ℕ → ℕ}

/-- The invariant follows the actual orbit, provided the size guard admits the orbit's
own candidates. -/
theorem orbit_mem (π : GradedInductionProof q m B) (hB : ∀ n, B n ≤ prod n + 1) :
    ∀ n ≥ π.N₀, ((prod n : ℕ) : ZMod m) ∈ π.inv n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact π.base
  | succ n hn ih =>
    have hge : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
    have hodd : Odd (prod n + 1) := by
      have h2 : (2 : ℕ) ∣ prod n := by
        have := seq_dvd_prod 0 n (Nat.zero_le n)
        rwa [seq_zero] at this
      obtain ⟨k, hk⟩ := h2
      exact Nat.odd_iff.mpr (by omega)
    have hcast : ((prod n + 1 : ℕ) : ZMod m) = ((prod n : ℕ) : ZMod m) + 1 := by
      push_cast; ring
    have h3 : 3 ≤ prod n + 1 := by have := prod_ge_two n; omega
    have hmem := π.step n _ ih (prod n + 1) hodd h3 (hB n) hcast
    have hstep : prod (n + 1) = prod n * Nat.minFac (prod n + 1) := by
      rw [prod_succ, seq_succ, euclid_minFac_eq_nat_minFac _ hge]
    rw [hstep]
    push_cast
    exact hmem

/-- **Soundness** of the widened fragment. -/
theorem eventually_avoids (π : GradedInductionProof q m B) (hB : ∀ n, B n ≤ prod n + 1) :
    ∀ n ≥ π.N₀, seq (n + 1) ≠ q := by
  intro n hn
  have hge : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
  have hodd : Odd (prod n + 1) := by
    have h2 : (2 : ℕ) ∣ prod n := by
      have := seq_dvd_prod 0 n (Nat.zero_le n)
      rwa [seq_zero] at this
    obtain ⟨k, hk⟩ := h2
    exact Nat.odd_iff.mpr (by omega)
  have hcast : ((prod n + 1 : ℕ) : ZMod m) = ((prod n : ℕ) : ZMod m) + 1 := by
    push_cast; ring
  have h3 : 3 ≤ prod n + 1 := by have := prod_ge_two n; omega
  have hav := π.avoid n _ (π.orbit_mem hB n hn) (prod n + 1) hodd h3 (hB n) hcast
  rw [seq_succ, euclid_minFac_eq_nat_minFac _ hge]
  exact hav

/-- Graded proofs lift along modulus divisibility, exactly as ungraded ones do. -/
def lift {m' : ℕ} (h : m ∣ m') (π : GradedInductionProof q m B) :
    GradedInductionProof q m' B where
  inv := fun n => (ZMod.castHom h (ZMod m)) ⁻¹' π.inv n
  N₀ := π.N₀
  base := by
    show (ZMod.castHom h (ZMod m)) ((prod π.N₀ : ℕ) : ZMod m') ∈ π.inv π.N₀
    rw [map_natCast]
    exact π.base
  step := by
    intro n r hr N hodd h3 hB hcast
    show (ZMod.castHom h (ZMod m)) (r * (Nat.minFac N : ZMod m')) ∈ π.inv (n + 1)
    rw [map_mul, map_natCast]
    refine π.step n _ hr N hodd h3 hB ?_
    have := congrArg (ZMod.castHom h (ZMod m)) hcast
    rwa [map_natCast, map_add, map_one] at this
  avoid := by
    intro n r hr N hodd h3 hB hcast
    refine π.avoid n _ hr N hodd h3 hB ?_
    have := congrArg (ZMod.castHom h (ZMod m)) hcast
    rwa [map_natCast, map_add, map_one] at this

end GradedInductionProof

/-- Every ungraded proof is a graded one, for *any* size guard: the extra hypotheses are
simply discarded.  So the widened fragment really is wider. -/
def CongruenceInductionProof.toGraded {q m : ℕ} (B : ℕ → ℕ)
    (π : CongruenceInductionProof q m) : GradedInductionProof q m B where
  inv := fun _ => π.inv
  N₀ := π.N₀
  base := π.base
  step := fun _ r hr N ho h3 _ hc => π.step r hr N ho h3 hc
  avoid := fun _ r hr N ho h3 _ hc => π.avoid r hr N ho h3 hc

/-! ### The `ω` guard

A third relaxation: the proof may additionally assume the candidate has at least `K n`
distinct prime factors.  It dies too, and for a reason that sharpens the boundary — a
prime `p ≡ 1 (mod m)` taken above the current value changes neither the residue class nor
the least factor while raising `ω` by one (`CvdP.exists_class_omega`), so `ω` is free to
push arbitrarily high without disturbing anything the congruence machinery sees.

So **`ω` is not the surviving part of anatomy.**  What survives is the opposite
direction: every construction here produces candidates with huge prime cofactors, so a
fragment demanding that `N` be `y`-smooth, or bounding its largest prime factor, is never
reached.  Smoothness is the boundary, and it is exactly the max-side ingredient of
Cox–van der Poorten. -/

/-- A **graded, size- and `ω`-guarded** induction proof: the step and conclusion clauses
are required only for candidates with `N ≥ B n` and at least `K n` distinct prime
factors. -/
structure OmegaGradedInductionProof (q m : ℕ) (B K : ℕ → ℕ) where
  /-- The induction hypothesis at each stage. -/
  inv : ℕ → Set (ZMod m)
  /-- The stage from which the invariant is maintained. -/
  N₀ : ℕ
  /-- The invariant holds on the actual orbit at stage `N₀`. -/
  base : ((prod N₀ : ℕ) : ZMod m) ∈ inv N₀
  /-- The induction step, for large candidates with many prime factors. -/
  step : ∀ n, ∀ r ∈ inv n, ∀ N : ℕ, Odd N → 3 ≤ N → B n ≤ N → K n ≤ N.primeFactors.card →
    (N : ZMod m) = r + 1 → r * (Nat.minFac N : ZMod m) ∈ inv (n + 1)
  /-- The conclusion, for large candidates with many prime factors. -/
  avoid : ∀ n, ∀ r ∈ inv n, ∀ N : ℕ, Odd N → 3 ≤ N → B n ≤ N → K n ≤ N.primeFactors.card →
    (N : ZMod m) = r + 1 → Nat.minFac N ≠ q

namespace OmegaGradedInductionProof

variable {q m : ℕ} {B K : ℕ → ℕ}

/-- The invariant follows the orbit, provided both guards admit the orbit's own
candidates.  The `ω` guard is admissible exactly when `K n ≤ ω(Pₙ + 1)` — an *anatomy*
condition on the actual Euclid numbers. -/
theorem orbit_mem (π : OmegaGradedInductionProof q m B K) (hB : ∀ n, B n ≤ prod n + 1)
    (hK : ∀ n, K n ≤ (prod n + 1).primeFactors.card) :
    ∀ n ≥ π.N₀, ((prod n : ℕ) : ZMod m) ∈ π.inv n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact π.base
  | succ n hn ih =>
    have hge : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
    have hodd : Odd (prod n + 1) := by
      have h2 : (2 : ℕ) ∣ prod n := by
        have := seq_dvd_prod 0 n (Nat.zero_le n)
        rwa [seq_zero] at this
      obtain ⟨k, hk⟩ := h2
      exact Nat.odd_iff.mpr (by omega)
    have hcast : ((prod n + 1 : ℕ) : ZMod m) = ((prod n : ℕ) : ZMod m) + 1 := by
      push_cast; ring
    have h3 : 3 ≤ prod n + 1 := by have := prod_ge_two n; omega
    have hmem := π.step n _ ih (prod n + 1) hodd h3 (hB n) (hK n) hcast
    have hstep : prod (n + 1) = prod n * Nat.minFac (prod n + 1) := by
      rw [prod_succ, seq_succ, euclid_minFac_eq_nat_minFac _ hge]
    rw [hstep]
    push_cast
    exact hmem

/-- **Soundness** of the doubly-guarded fragment. -/
theorem eventually_avoids (π : OmegaGradedInductionProof q m B K)
    (hB : ∀ n, B n ≤ prod n + 1) (hK : ∀ n, K n ≤ (prod n + 1).primeFactors.card) :
    ∀ n ≥ π.N₀, seq (n + 1) ≠ q := by
  intro n hn
  have hge : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
  have hodd : Odd (prod n + 1) := by
    have h2 : (2 : ℕ) ∣ prod n := by
      have := seq_dvd_prod 0 n (Nat.zero_le n)
      rwa [seq_zero] at this
    obtain ⟨k, hk⟩ := h2
    exact Nat.odd_iff.mpr (by omega)
  have hcast : ((prod n + 1 : ℕ) : ZMod m) = ((prod n : ℕ) : ZMod m) + 1 := by
    push_cast; ring
  have h3 : 3 ≤ prod n + 1 := by have := prod_ge_two n; omega
  have hav := π.avoid n _ (π.orbit_mem hB hK n hn) (prod n + 1) hodd h3 (hB n) (hK n) hcast
  rw [seq_succ, euclid_minFac_eq_nat_minFac _ hge]
  exact hav

/-- Doubly-guarded proofs lift along modulus divisibility. -/
def lift {m' : ℕ} (h : m ∣ m') (π : OmegaGradedInductionProof q m B K) :
    OmegaGradedInductionProof q m' B K where
  inv := fun n => (ZMod.castHom h (ZMod m)) ⁻¹' π.inv n
  N₀ := π.N₀
  base := by
    show (ZMod.castHom h (ZMod m)) ((prod π.N₀ : ℕ) : ZMod m') ∈ π.inv π.N₀
    rw [map_natCast]
    exact π.base
  step := by
    intro n r hr N hodd h3 hB hK hcast
    show (ZMod.castHom h (ZMod m)) (r * (Nat.minFac N : ZMod m')) ∈ π.inv (n + 1)
    rw [map_mul, map_natCast]
    refine π.step n _ hr N hodd h3 hB hK ?_
    have := congrArg (ZMod.castHom h (ZMod m)) hcast
    rwa [map_natCast, map_add, map_one] at this
  avoid := by
    intro n r hr N hodd h3 hB hK hcast
    refine π.avoid n _ hr N hodd h3 hB hK ?_
    have := congrArg (ZMod.castHom h (ZMod m)) hcast
    rwa [map_natCast, map_add, map_one] at this

end OmegaGradedInductionProof

/-- Dropping the `ω` obligation: a proof that handles *all* large candidates certainly
handles the ones with many prime factors.  So the `ω`-guarded fragment is the wider one. -/
def GradedInductionProof.toOmega {q m : ℕ} {B : ℕ → ℕ} (K : ℕ → ℕ)
    (π : GradedInductionProof q m B) : OmegaGradedInductionProof q m B K where
  inv := π.inv
  N₀ := π.N₀
  base := π.base
  step := fun n r hr N ho h3 hb _ hc => π.step n r hr N ho h3 hb hc
  avoid := fun n r hr N ho h3 hb _ hc => π.avoid n r hr N ho h3 hb hc

/-- **The widened Unprovability Theorem.**  For a missing prime `q`, no
congruence-invariant induction proof of `q`'s eventual avoidance exists at any odd
modulus — *even if* the invariant depends on the step index, *and* the proof may assume
the candidate is as large as the Euclid number itself, *and* the proof may assume the
candidate has as many prime factors as the Euclid number actually has.

The proof is the two-step form of Eviction / Fullness / Reach: at a late free orbit state
`congruence_reaches_forcing` supplies a CRT-chosen unit `u` with `Pₙ · u` forcing;
`free_transition_omega` realizes the transition with a candidate meeting both guards, so
the graded `step` places `Pₙ · u` in `inv (n+1)`; and `exists_large_odd_in_class_omega`
supplies a candidate in the forcing class meeting both guards at stage `n+1`, whose least
factor is `q` — contradicting `avoid`. -/
theorem no_omega_graded_induction_proof {q m : ℕ} {B K : ℕ → ℕ} (hq : q ∈ MissingPrimes)
    (hmodd : Odd m) (hB : ∀ n, B n ≤ prod n + 1)
    (hK : ∀ n, K n ≤ (prod n + 1).primeFactors.card) :
    IsEmpty (OmegaGradedInductionProof q m B K) := by
  constructor
  intro π
  -- lift to a rich modulus, where forcing states exist
  set m' : ℕ := m * forcingModulus q with hm'
  have hm'odd : Odd m' := hmodd.mul (odd_forcingModulus hq)
  have hm'ne : m' ≠ 0 := by have := Nat.odd_iff.mp hm'odd; omega
  have hrich : RichEnough q m' := richEnough_of_forcingModulus_dvd (dvd_mul_left _ m)
  have π' := π.lift (dvd_mul_right m (forcingModulus q))
  obtain ⟨N₁, hforce⟩ := congruence_reaches_forcing hq hm'ne hrich
  set n := max π'.N₀ N₁ with hn
  have hmem : ((prod n : ℕ) : ZMod m') ∈ π'.inv n := π'.orbit_mem hB hK n (le_max_left _ _)
  obtain ⟨hunit, u, hu⟩ := hforce n (le_max_right _ _)
  -- Fullness meeting both guards
  obtain ⟨N, hNgt, hNodd, hN3, hNcast, hNminfac, hNom⟩ :=
    CvdP.free_transition_omega hm'ne ((prod n : ℕ) : ZMod m') hunit u (B n) (K n)
  have hstep := π'.step n _ hmem N hNodd hN3 (le_of_lt hNgt) hNom hNcast
  rw [hNminfac] at hstep
  -- a candidate in the forcing class meeting both guards
  obtain ⟨N₂, hN₂gt, hN₂odd, hN₂3, hN₂cast, hN₂om⟩ :=
    CvdP.exists_large_odd_in_class_omega hm'odd
      (((prod n : ℕ) : ZMod m') * (u : ZMod m') + 1) (B (n + 1)) (K (n + 1))
  obtain ⟨hqN, hsmall⟩ := hu N₂ hN₂cast
  -- its least factor is exactly `q`
  have hNne1 : N₂ ≠ 1 := by omega
  have hpr : (Nat.minFac N₂).Prime := Nat.minFac_prime hNne1
  have hdvd : Nat.minFac N₂ ∣ N₂ := Nat.minFac_dvd N₂
  have hne2 : Nat.minFac N₂ ≠ 2 := by
    intro h2
    rw [h2] at hdvd
    have := Nat.odd_iff.mp hN₂odd
    omega
  have hle : Nat.minFac N₂ ≤ q := Nat.minFac_le_of_dvd hq.1.two_le hqN
  have hgeq : q ≤ Nat.minFac N₂ := by
    by_contra hcon
    exact hsmall _ hpr (hpr.odd_of_ne_two hne2) (by omega) hdvd
  exact π'.avoid (n + 1) _ hstep N₂ hN₂odd hN₂3 (le_of_lt hN₂gt) hN₂om hN₂cast (by omega)

/-- The size-guarded fragment is the `K ≡ 0` case. -/
theorem no_graded_induction_proof {q m : ℕ} {B : ℕ → ℕ} (hq : q ∈ MissingPrimes)
    (hmodd : Odd m) (hB : ∀ n, B n ≤ prod n + 1) :
    IsEmpty (GradedInductionProof q m B) :=
  ⟨fun π => (no_omega_graded_induction_proof (K := fun _ => 0) hq hmodd hB
    (fun _ => Nat.zero_le _)).false (π.toOmega _)⟩

/-- **Coherence**: the widened theorem subsumes Part 2's. -/
theorem no_congruence_induction_proof_of_graded {q m : ℕ} (hq : q ∈ MissingPrimes)
    (hmodd : Odd m) : IsEmpty (CongruenceInductionProof q m) :=
  ⟨fun π => (no_graded_induction_proof (B := fun _ => 0) hq hmodd
    (fun _ => Nat.zero_le _)).false (π.toGraded _)⟩

/-- **The provability equivalence survives the widening.**  For a prime `q`, an odd
modulus `m` divisible by `q`, and any admissible size guard `B`: the widened fragment
proves "`q` eventually avoided" if and only if `q` appears.  Widening the proof system
along both axes changes nothing — provability still decides membership. -/
theorem graded_provability_iff {q m : ℕ} (B : ℕ → ℕ) (hqp : Nat.Prime q) (hmodd : Odd m)
    (hqm : q ∣ m) (hB : ∀ n, B n ≤ prod n + 1) :
    Nonempty (GradedInductionProof q m B) ↔ ∃ k, seq k = q := by
  constructor
  · intro hπ
    by_contra hcon
    have hmiss : q ∈ MissingPrimes := ⟨hqp, fun k hk => hcon ⟨k, hk⟩⟩
    exact (no_graded_induction_proof hmiss hmodd hB).false hπ.some
  · rintro ⟨k, hk⟩
    exact ⟨(appearedProof hqp hk hqm).toGraded B⟩

/-- **Provability still decides appearance, with both guards.** -/
theorem omega_graded_provability_iff {q m : ℕ} (B K : ℕ → ℕ) (hqp : Nat.Prime q)
    (hmodd : Odd m) (hqm : q ∣ m) (hB : ∀ n, B n ≤ prod n + 1)
    (hK : ∀ n, K n ≤ (prod n + 1).primeFactors.card) :
    Nonempty (OmegaGradedInductionProof q m B K) ↔ ∃ k, seq k = q := by
  constructor
  · intro hπ
    by_contra hcon
    have hmiss : q ∈ MissingPrimes := ⟨hqp, fun k hk => hcon ⟨k, hk⟩⟩
    exact (no_omega_graded_induction_proof hmiss hmodd hB hK).false hπ.some
  · rintro ⟨k, hk⟩
    exact ⟨((appearedProof hqp hk hqm).toGraded B).toOmega K⟩

/-- **The widened dichotomy, as one statement.**  Adds to `proof_theoretic_dichotomy`:
the fragment stays sound and stays empty under three relaxations at once — the invariant
may depend on the step index, the proof may assume the candidate is as large as the Euclid
number, and it may assume the candidate has as many prime factors as the Euclid number
actually has.  The provability-equals-appearance equivalence survives all three.

The clause that is *missing* is the point: no relaxation here bounds the candidate from
**above**, or constrains its smoothness / largest prime factor.  That is the one axis the
constructions cannot supply, and it is exactly the ingredient the max-side
Cox–van der Poorten proof runs on. -/
theorem graded_proof_theoretic_dichotomy :
    -- soundness of the widened fragment
    (∀ (q m : ℕ) (B : ℕ → ℕ) (π : GradedInductionProof q m B),
      (∀ n, B n ≤ prod n + 1) → ∀ n ≥ π.N₀, seq (n + 1) ≠ q) ∧
    -- it is strictly wider: every ungraded proof embeds, at every guard
    (∀ (q m : ℕ) (B : ℕ → ℕ), Nonempty (CongruenceInductionProof q m) →
      Nonempty (GradedInductionProof q m B)) ∧
    -- and still empty for every missing prime
    (∀ (q m : ℕ) (B : ℕ → ℕ), q ∈ MissingPrimes → Odd m → (∀ n, B n ≤ prod n + 1) →
      IsEmpty (GradedInductionProof q m B)) ∧
    -- provability still decides appearance
    (∀ (q m : ℕ) (B : ℕ → ℕ), Nat.Prime q → Odd m → q ∣ m → (∀ n, B n ≤ prod n + 1) →
      (Nonempty (GradedInductionProof q m B) ↔ ∃ k, seq k = q)) ∧
    -- the `ω` guard changes none of it: sound, wider still, empty, and provability
    -- still decides appearance
    (∀ (q m : ℕ) (B K : ℕ → ℕ) (π : OmegaGradedInductionProof q m B K),
      (∀ n, B n ≤ prod n + 1) → (∀ n, K n ≤ (prod n + 1).primeFactors.card) →
      ∀ n ≥ π.N₀, seq (n + 1) ≠ q) ∧
    (∀ (q m : ℕ) (B K : ℕ → ℕ), Nonempty (GradedInductionProof q m B) →
      Nonempty (OmegaGradedInductionProof q m B K)) ∧
    (∀ (q m : ℕ) (B K : ℕ → ℕ), q ∈ MissingPrimes → Odd m → (∀ n, B n ≤ prod n + 1) →
      (∀ n, K n ≤ (prod n + 1).primeFactors.card) →
      IsEmpty (OmegaGradedInductionProof q m B K)) ∧
    (∀ (q m : ℕ) (B K : ℕ → ℕ), Nat.Prime q → Odd m → q ∣ m → (∀ n, B n ≤ prod n + 1) →
      (∀ n, K n ≤ (prod n + 1).primeFactors.card) →
      (Nonempty (OmegaGradedInductionProof q m B K) ↔ ∃ k, seq k = q)) :=
  ⟨fun _ _ _ π hB => π.eventually_avoids hB,
    fun _ _ B hπ => ⟨hπ.some.toGraded B⟩,
    fun _ _ _ hq hm hB => no_graded_induction_proof hq hm hB,
    fun _ _ B hqp hm hqm hB => graded_provability_iff B hqp hm hqm hB,
    fun _ _ _ _ π hB hK => π.eventually_avoids hB hK,
    fun _ _ _ K hπ => ⟨hπ.some.toOmega K⟩,
    fun _ _ _ _ hq hm hB hK => no_omega_graded_induction_proof hq hm hB hK,
    fun _ _ B K hqp hm hqm hB hK => omega_graded_provability_iff B K hqp hm hqm hB hK⟩

/-! ## Part 7: The smoothness axis, and completeness of the fragment analysis

Part 6 widened the fragment along every axis that bounds the candidate from *below* —
stage-dependence, size, number of prime factors — and it stayed empty.  The one axis left
open was the opposite direction: a guard demanding the candidate be `y`-smooth, or
bounding its largest prime factor.  That is the axis on which the max-side proofs run,
since `maxFac N = q` *is* a smoothness condition.

It closes here, and not by another killing argument.  A guard is only meaningful if the
orbit's own candidates satisfy it, and the Euclid numbers are eventually `y`-rough for
every `y` (`CvdP.eventually_rough`): each prime either enters the accumulator or has a
finite hitting set, so past some stage *every* prime factor of `Pₙ + 1` exceeds `y`.  A
`y`-smooth fragment therefore excludes the orbit's own candidates and proves nothing about
the orbit — its soundness contract is unmeetable
(`CvdP.smooth_guard_inadmissible`).

Together with Part 6 this completes the analysis for guards with a fixed threshold.  What
remains is a *growing* guard `y(n)`: admissible only if `P⁺(Pₙ + 1) ≤ y(n)`, an anatomy
statement about the Euclid numbers.  A guard loose enough to be admissible is vacuous; one
tight enough to be useful asserts that the Euclid numbers have controlled largest prime
factors, which is unknown and at least as strong as (C∞) — and in the extreme case puts
one on the branch where `Pₙ + 1` is eventually prime, on which MC is false anyway
(Dead End~#146).  The net statement: **any proof that a prime is omitted must first
establish an unproven anatomy property of the Euclid numbers.** -/

/-- A **smoothness-guarded** induction proof: the step and conclusion clauses are required
only for `y`-smooth candidates. -/
structure SmoothGuardedInductionProof (q m y : ℕ) where
  /-- The induction hypothesis at each stage. -/
  inv : ℕ → Set (ZMod m)
  /-- The stage from which the invariant is maintained. -/
  N₀ : ℕ
  /-- The invariant holds on the actual orbit at stage `N₀`. -/
  base : ((prod N₀ : ℕ) : ZMod m) ∈ inv N₀
  /-- The induction step, for `y`-smooth candidates only. -/
  step : ∀ n, ∀ r ∈ inv n, ∀ N : ℕ, Odd N → 3 ≤ N →
    (∀ p : ℕ, Nat.Prime p → p ∣ N → p ≤ y) → (N : ZMod m) = r + 1 →
    r * (Nat.minFac N : ZMod m) ∈ inv (n + 1)
  /-- The conclusion, for `y`-smooth candidates only. -/
  avoid : ∀ n, ∀ r ∈ inv n, ∀ N : ℕ, Odd N → 3 ≤ N →
    (∀ p : ℕ, Nat.Prime p → p ∣ N → p ≤ y) → (N : ZMod m) = r + 1 →
    Nat.minFac N ≠ q

namespace SmoothGuardedInductionProof

variable {q m y : ℕ}

/-- The soundness contract: the invariant follows the orbit *provided* the orbit's own
candidates are `y`-smooth.  `smooth_fragment_never_sound` shows that hypothesis is false
for every `y`, which is the whole point of this part. -/
theorem orbit_mem (π : SmoothGuardedInductionProof q m y)
    (hsm : ∀ n ≥ π.N₀, ∀ p : ℕ, Nat.Prime p → p ∣ (prod n + 1) → p ≤ y) :
    ∀ n ≥ π.N₀, ((prod n : ℕ) : ZMod m) ∈ π.inv n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact π.base
  | succ n hn ih =>
    have hge : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
    have hodd : Odd (prod n + 1) := by
      have h2 : (2 : ℕ) ∣ prod n := by
        have := seq_dvd_prod 0 n (Nat.zero_le n)
        rwa [seq_zero] at this
      obtain ⟨k, hk⟩ := h2
      exact Nat.odd_iff.mpr (by omega)
    have hcast : ((prod n + 1 : ℕ) : ZMod m) = ((prod n : ℕ) : ZMod m) + 1 := by
      push_cast; ring
    have h3 : 3 ≤ prod n + 1 := by have := prod_ge_two n; omega
    have hmem := π.step n _ ih (prod n + 1) hodd h3 (hsm n hn) hcast
    have hstep : prod (n + 1) = prod n * Nat.minFac (prod n + 1) := by
      rw [prod_succ, seq_succ, euclid_minFac_eq_nat_minFac _ hge]
    rw [hstep]
    push_cast
    exact hmem

/-- Soundness, under the unmeetable hypothesis. -/
theorem eventually_avoids (π : SmoothGuardedInductionProof q m y)
    (hsm : ∀ n ≥ π.N₀, ∀ p : ℕ, Nat.Prime p → p ∣ (prod n + 1) → p ≤ y) :
    ∀ n ≥ π.N₀, seq (n + 1) ≠ q := by
  intro n hn
  have hge : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
  have hodd : Odd (prod n + 1) := by
    have h2 : (2 : ℕ) ∣ prod n := by
      have := seq_dvd_prod 0 n (Nat.zero_le n)
      rwa [seq_zero] at this
    obtain ⟨k, hk⟩ := h2
    exact Nat.odd_iff.mpr (by omega)
  have hcast : ((prod n + 1 : ℕ) : ZMod m) = ((prod n : ℕ) : ZMod m) + 1 := by
    push_cast; ring
  have h3 : 3 ≤ prod n + 1 := by have := prod_ge_two n; omega
  have hav := π.avoid n _ (π.orbit_mem hsm n hn) (prod n + 1) hodd h3 (hsm n hn) hcast
  rw [seq_succ, euclid_minFac_eq_nat_minFac _ hge]
  exact hav

end SmoothGuardedInductionProof

/-- **The smoothness axis is closed.**  For every threshold `y`, the soundness hypothesis
of the `y`-smooth fragment is false: the Euclid numbers are eventually `y`-rough, so no
stage past which they are `y`-smooth exists.  A fixed smoothness guard therefore cannot
be used at all — not because the fragment is empty, but because nothing it proves is
about the orbit. -/
theorem smooth_fragment_never_sound (y : ℕ) :
    ¬ ∃ T, ∀ n ≥ T, ∀ p : ℕ, Nat.Prime p → p ∣ (prod n + 1) → p ≤ y :=
  CvdP.smooth_guard_inadmissible y

/-- **Completeness of the fragment analysis.**  Assembling Parts 6 and 7.

Guards bounding the candidate from below — stage-dependence, size, number of prime
factors — are free: the fragment carrying all of them is still empty for every missing
prime.  The guard bounding it from above is unusable: no fixed smoothness threshold is
admissible, because the orbit is eventually rough past every bound.

What is left is a *growing* smoothness guard, whose admissibility is an unproven anatomy
statement about the Euclid numbers.  That is the residue of the whole programme. -/
theorem fragment_analysis_complete :
    -- below-guards are free: the triply-widened fragment is still empty
    (∀ (q m : ℕ) (B K : ℕ → ℕ), q ∈ MissingPrimes → Odd m →
      (∀ n, B n ≤ prod n + 1) → (∀ n, K n ≤ (prod n + 1).primeFactors.card) →
      IsEmpty (OmegaGradedInductionProof q m B K)) ∧
    -- and provability still decides appearance there
    (∀ (q m : ℕ) (B K : ℕ → ℕ), Nat.Prime q → Odd m → q ∣ m →
      (∀ n, B n ≤ prod n + 1) → (∀ n, K n ≤ (prod n + 1).primeFactors.card) →
      (Nonempty (OmegaGradedInductionProof q m B K) ↔ ∃ k, seq k = q)) ∧
    -- the above-guard is unusable: the orbit is eventually rough past every bound
    (∀ y : ℕ, ∃ N₀, ∀ n ≥ N₀, ∀ p : ℕ, Nat.Prime p → p ∣ (prod n + 1) → y < p) ∧
    (∀ y : ℕ, ¬ ∃ T, ∀ n ≥ T, ∀ p : ℕ, Nat.Prime p → p ∣ (prod n + 1) → p ≤ y) :=
  ⟨fun _ _ _ _ hq hm hB hK => no_omega_graded_induction_proof hq hm hB hK,
    fun _ _ B K hqp hm hqm hB hK => omega_graded_provability_iff B K hqp hm hqm hB hK,
    fun y => CvdP.eventually_rough y,
    fun y => CvdP.smooth_guard_inadmissible y⟩

/-! ## Part 8: The smoothness axis closes outright

Part 7 showed that a *fixed* smoothness threshold is inadmissible.  A **growing** one
`y(n)` looked like a genuine residue: its admissibility, `P⁺(Pₙ+1) ≤ y(n)`, is an anatomy
statement, and the constructions of Part 6 make candidates with large prime factors.

The residue is illusory, and the reason is an order-of-quantifiers point.  The killing
construction does not need candidates tailored to the stage: by pigeonhole the orbit
returns to some residue `r₀` mod `m'` infinitely often, and at *every* such stage the same
two candidates work, because their defining conditions mention the stage only through that
residue.  So one may **choose the candidates first and the stage afterwards**.  Having
fixed them, they are two specific naturals with some largest prime factor `C`; and
admissibility together with `CvdP.eventually_rough` forces `y(n) > C` for all large `n`.
Every admissible growing guard therefore admits the constructed candidates.

The smoothness axis is thus closed in the same sense as the others, and the fragment
analysis leaves no guard direction open. -/

/-- A stage-dependent invariant with a **growing** smoothness guard: the step and
conclusion clauses are required only for candidates all of whose prime factors are at
most `y n`. -/
structure SmoothGradedInductionProof (q m : ℕ) (y : ℕ → ℕ) where
  /-- The invariant at each stage. -/
  inv : ℕ → Set (ZMod m)
  /-- The stage from which the invariant is maintained. -/
  N₀ : ℕ
  /-- The invariant holds on the actual orbit at stage `N₀`. -/
  base : ((prod N₀ : ℕ) : ZMod m) ∈ inv N₀
  /-- The induction step, for `y n`-smooth candidates. -/
  step : ∀ n, ∀ r ∈ inv n, ∀ N : ℕ, Odd N → 3 ≤ N →
    (∀ p : ℕ, Nat.Prime p → p ∣ N → p ≤ y n) → (N : ZMod m) = r + 1 →
    r * (Nat.minFac N : ZMod m) ∈ inv (n + 1)
  /-- The conclusion, for `y n`-smooth candidates. -/
  avoid : ∀ n, ∀ r ∈ inv n, ∀ N : ℕ, Odd N → 3 ≤ N →
    (∀ p : ℕ, Nat.Prime p → p ∣ N → p ≤ y n) → (N : ZMod m) = r + 1 →
    Nat.minFac N ≠ q

namespace SmoothGradedInductionProof

variable {q m : ℕ} {y : ℕ → ℕ}

/-- Lifting along modulus divisibility, as for the other fragments. -/
def lift {m' : ℕ} (h : m ∣ m') (π : SmoothGradedInductionProof q m y) :
    SmoothGradedInductionProof q m' y where
  inv := fun n => (ZMod.castHom h (ZMod m)) ⁻¹' π.inv n
  N₀ := π.N₀
  base := by
    show (ZMod.castHom h (ZMod m)) ((prod π.N₀ : ℕ) : ZMod m') ∈ π.inv π.N₀
    rw [map_natCast]; exact π.base
  step := by
    intro n r hr N hodd h3 hsm hcast
    show (ZMod.castHom h (ZMod m)) (r * (Nat.minFac N : ZMod m')) ∈ π.inv (n + 1)
    rw [map_mul, map_natCast]
    refine π.step n _ hr N hodd h3 hsm ?_
    have := congrArg (ZMod.castHom h (ZMod m)) hcast
    rwa [map_natCast, map_add, map_one] at this
  avoid := by
    intro n r hr N hodd h3 hsm hcast
    refine π.avoid n _ hr N hodd h3 hsm ?_
    have := congrArg (ZMod.castHom h (ZMod m)) hcast
    rwa [map_natCast, map_add, map_one] at this

/-- The invariant follows the orbit, given that the guard admits the orbit's candidates. -/
theorem orbit_mem (π : SmoothGradedInductionProof q m y)
    (hadm : ∀ n, ∀ p : ℕ, Nat.Prime p → p ∣ (prod n + 1) → p ≤ y n) :
    ∀ n ≥ π.N₀, ((prod n : ℕ) : ZMod m) ∈ π.inv n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact π.base
  | succ n hn ih =>
    have hge : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
    have hodd : Odd (prod n + 1) := by
      have h2 : (2 : ℕ) ∣ prod n := by
        have := seq_dvd_prod 0 n (Nat.zero_le n)
        rwa [seq_zero] at this
      obtain ⟨k, hk⟩ := h2
      exact Nat.odd_iff.mpr (by omega)
    have hcast : ((prod n + 1 : ℕ) : ZMod m) = ((prod n : ℕ) : ZMod m) + 1 := by
      push_cast; ring
    have h3 : 3 ≤ prod n + 1 := by have := prod_ge_two n; omega
    have hmem := π.step n _ ih (prod n + 1) hodd h3 (hadm n) hcast
    have hstep : prod (n + 1) = prod n * Nat.minFac (prod n + 1) := by
      rw [prod_succ, seq_succ, euclid_minFac_eq_nat_minFac _ hge]
    rw [hstep]; push_cast; exact hmem

end SmoothGradedInductionProof

/-- Pigeonhole: the orbit returns to some residue mod `M` cofinally often. -/
theorem exists_recurrent_residue (M : ℕ) [NeZero M] :
    ∃ r₀ : ZMod M, ∀ B : ℕ, ∃ n, B ≤ n ∧ ((prod n : ℕ) : ZMod M) = r₀ := by
  classical
  by_contra hcon
  push Not at hcon
  choose B hB using hcon
  set Bmax := Finset.univ.sup B with hBmax
  exact hB (((prod Bmax : ℕ) : ZMod M)) Bmax
    (Finset.le_sup (Finset.mem_univ _)) rfl

/-- **The smoothness axis closes.**  For a missing prime `q`, an odd modulus and any
admissible growing smoothness guard, the fragment is empty.

The candidates are chosen at a recurrent residue *before* the stage is chosen; having
fixed them, `CvdP.eventually_rough` forces the guard above their largest prime factor at
all late stages. -/
theorem no_smooth_graded_induction_proof {q m : ℕ} {y : ℕ → ℕ}
    (hq : q ∈ MissingPrimes) (hmodd : Odd m)
    (hadm : ∀ n, ∀ p : ℕ, Nat.Prime p → p ∣ (prod n + 1) → p ≤ y n) :
    IsEmpty (SmoothGradedInductionProof q m y) := by
  constructor
  intro π₀
  -- lift to a rich modulus
  set m' : ℕ := m * forcingModulus q with hm'def
  have hm'odd : Odd m' := hmodd.mul (odd_forcingModulus hq)
  have hm'ne : m' ≠ 0 := by have := Nat.odd_iff.mp hm'odd; omega
  have : NeZero m' := ⟨hm'ne⟩
  have hrich : RichEnough q m' := richEnough_of_forcingModulus_dvd (dvd_mul_left _ m)
  have π := π₀.lift (dvd_mul_right m (forcingModulus q))
  obtain ⟨N₁, hforce⟩ := congruence_reaches_forcing hq hm'ne hrich
  -- a recurrent residue, and a stage at which to read off the forcing data
  obtain ⟨r₀, hrec⟩ := exists_recurrent_residue m'
  obtain ⟨n₀, hn₀, hn₀eq⟩ := hrec (max π.N₀ N₁)
  obtain ⟨hunit₀, u, hu₀⟩ := hforce n₀ (le_trans (le_max_right _ _) hn₀)
  rw [hn₀eq] at hunit₀ hu₀
  -- the two candidates, fixed once and for all
  obtain ⟨N, _, hNodd, hN3, hNcast, hNmf⟩ :=
    CvdP.free_transition_large hm'ne r₀ hunit₀ u 2
  obtain ⟨N', hN'gt, hN'odd, hN'3, hN'cast⟩ :=
    CvdP.exists_large_odd_in_class hm'odd (r₀ * (u : ZMod m') + 1) 3
  -- their prime factors are bounded by a constant
  set C : ℕ := max N N' with hC
  obtain ⟨N₂, hN₂⟩ := CvdP.eventually_rough C
  -- now pick a late stage at the same residue
  obtain ⟨n, hn, hneq⟩ := hrec (max π.N₀ N₂)
  have hnπ : π.N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hnr : N₂ ≤ n := le_trans (le_max_right _ _) hn
  -- the guard is above `C` at this stage
  have hyC : ∀ k : ℕ, N₂ ≤ k → C < y k := by
    intro k hk
    have h3 : 2 ≤ prod k + 1 := by have := prod_ge_two k; omega
    have hne1 : prod k + 1 ≠ 1 := by omega
    have hpr : Nat.Prime (Nat.minFac (prod k + 1)) := Nat.minFac_prime hne1
    have hdvd : Nat.minFac (prod k + 1) ∣ prod k + 1 := Nat.minFac_dvd _
    have hgt := hN₂ k hk _ hpr hdvd
    have hle := hadm k _ hpr hdvd
    omega
  have hyn : C < y n := hyC n hnr
  have hyn1 : C < y (n + 1) := hyC (n + 1) (by omega)
  -- the step, with the guard satisfied
  have hmem : ((prod n : ℕ) : ZMod m') ∈ π.inv n := π.orbit_mem hadm n hnπ
  rw [hneq] at hmem
  have hNsm : ∀ p : ℕ, Nat.Prime p → p ∣ N → p ≤ y n := by
    intro p hp hpd
    have : p ≤ N := Nat.le_of_dvd (by omega) hpd
    omega
  have hstep := π.step n _ hmem N hNodd hN3 hNsm hNcast
  rw [hNmf] at hstep
  -- the conclusion, with the guard satisfied
  have hN'sm : ∀ p : ℕ, Nat.Prime p → p ∣ N' → p ≤ y (n + 1) := by
    intro p hp hpd
    have : p ≤ N' := Nat.le_of_dvd (by omega) hpd
    omega
  obtain ⟨hqN, hsmall⟩ := hu₀ N' hN'cast
  have hne1 : N' ≠ 1 := by omega
  have hpr : (Nat.minFac N').Prime := Nat.minFac_prime hne1
  have hdvd : Nat.minFac N' ∣ N' := Nat.minFac_dvd N'
  have hne2 : Nat.minFac N' ≠ 2 := by
    intro h2
    rw [h2] at hdvd
    have := Nat.odd_iff.mp hN'odd
    omega
  have hle : Nat.minFac N' ≤ q := Nat.minFac_le_of_dvd hq.1.two_le hqN
  have hgeq : q ≤ Nat.minFac N' := by
    by_contra hcon
    exact hsmall _ hpr (hpr.odd_of_ne_two hne2) (by omega) hdvd
  exact π.avoid (n + 1) _ hstep N' hN'odd hN'3 hN'sm hN'cast (by omega)

/-- **No guard direction remains open.**  The full statement of the guard analysis:
every guard bounding the candidate from below is free, and every guard bounding it from
above — fixed or growing — leaves the fragment empty or is inadmissible.

Combined with `Reciprocity.no_reciprocity_induction_proof`, which handles invariants built
from symbols against a growing modulus, this exhausts the invariant-induction genre.  What
lies outside it is only the class of *exact-value* arguments, which use `Pₙ + 1` as an
integer identity rather than a congruence. -/
theorem guard_analysis_complete :
    -- below-guards (stage, size, factor count) are free
    (∀ (q m : ℕ) (B K : ℕ → ℕ), q ∈ MissingPrimes → Odd m →
      (∀ n, B n ≤ prod n + 1) → (∀ n, K n ≤ (prod n + 1).primeFactors.card) →
      IsEmpty (OmegaGradedInductionProof q m B K)) ∧
    -- a fixed above-guard is inadmissible
    (∀ y : ℕ, ¬ ∃ T, ∀ n ≥ T, ∀ p : ℕ, Nat.Prime p → p ∣ (prod n + 1) → p ≤ y) ∧
    -- and a growing above-guard, however chosen, still leaves the fragment empty
    (∀ (q m : ℕ) (y : ℕ → ℕ), q ∈ MissingPrimes → Odd m →
      (∀ n, ∀ p : ℕ, Nat.Prime p → p ∣ (prod n + 1) → p ≤ y n) →
      IsEmpty (SmoothGradedInductionProof q m y)) :=
  ⟨fun _ _ _ _ hq hm hB hK => no_omega_graded_induction_proof hq hm hB hK,
    fun y => CvdP.smooth_guard_inadmissible y,
    fun _ _ _ hq hm hadm => no_smooth_graded_induction_proof hq hm hadm⟩

end Obstruction
