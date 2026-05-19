import EM.Obstruction.NoInvariant
import EM.Obstruction.MaxVariant
import EM.SDDS.Bridge

/-!
# The Obstruction Calculus

This file abstracts the No-Invariant machinery of `EM/Obstruction/NoInvariant.lean`
into a calculus of **enrichments** and **certificates**, discharging the
reconciliation TODO at the end of `EM/Obstruction/MaxVariant.lean` one level up.

## The design, and why this object

Run R-Inverse produced two poles:

* the **min** pole (`no_cvdp_obstruction`): no propagating congruence invariant
  blocks a prime in the min Euclid–Mullin sequence; and
* the **max** pole (`max_cvdp_obstruction_five`): the very same kind of invariant
  exists for the max sequence and machine-verifies Cox–van der Poorten.

The killing proof (Eviction / Fullness / Reach) barely used the fact that the
certificate tracks *residues*.  So the real object is one level up: an
`Enrichment` is *any* state space a would-be avoidance certificate is allowed to
track, together with what the certificate may see of the orbit and which
transitions it must be closed under.  A `Certificate` is a propagating,
tail-containing, forcing-free set of enriched states — the common shape of every
omission proof ever given in this family.

The three-step killing argument factors through a single semantic condition,
`Killable`: *from every late orbit state, a forcing state is reachable inside
the transition relation*.  Eviction + Fullness + Reach are exactly a proof
method for `Killable`; the generic emptiness theorem `no_certificate` is then
ten lines.

## Honesty about completeness

`TraceComplete` (every missing prime admits a certificate in the family) is
**equivalent** to `MullinConjecture` over any killable family — just as
`IC_min ↔ MullinConjecture` (`CvdP.ic_min_network`).  The calculus therefore
does not produce a new *weaker* route to MC.  Its value is the growing **no-go
content**: every enrichment proved `Killable` removes one more possible shape of
an omission proof (equivalently, of a disproof of MC), and the max side shows
the framework is not vacuous — `Killable` *provably fails* for the max
transition system (`max_not_killable`), which is why CvdP's proof can exist.

The frontier this file makes precise: classify the **tame** enrichments — those
whose Fullness input is a Dirichlet/Chebotarev density statement — and grow the
killed class (congruence: done here; quadratic reciprocity: the EXTENDS verdict
of `docs/analysis/reciprocity_invariants.md`, formalization pending).

## Main definitions

* `Obstruction.Enrichment` — state space, orbit shadow, transition, forcing.
* `Obstruction.Certificate` — propagating + contains tail + blocks forcing.
* `Obstruction.Killable` — forcing states reachable from every late orbit state.
* `Obstruction.Refines` — comparison of enrichments; certificates pull back,
  killability pushes forward.
* `Obstruction.TraceComplete` — the completeness Prop, per-prime family.

## Main results

* `Obstruction.no_certificate` — the generic Emptiness Theorem.
* `Obstruction.certificate_omits` — certificates really certify omission
  (the max-side semantics, abstractly).
* `Obstruction.congruence_killable` — the congruence enrichment is killable
  (the CRT/Dirichlet core of `no_cvdp_obstruction`, re-packaged).
* `Obstruction.no_cvdp_obstruction'` — the No-Invariant Theorem re-derived
  *inside* the calculus.
* `Obstruction.maxCertificate_five` / `Obstruction.max_not_killable` — the max
  pole: the CvdP certificate is a `Certificate`, hence max is *not* killable.
* `Obstruction.traceComplete_congruence_iff_ic_min` — `IC_min` *is* the
  completeness statement of the congruence family.
* `Obstruction.mc_of_traceComplete` / `Obstruction.traceComplete_iff_mullin`.
-/

open Mullin Euclid MullinGroup RotorRouter
open Classical

namespace Obstruction

/-! ## Part 1: Enrichments and certificates -/

/-- An **enrichment**: a state space that an avoidance certificate is allowed to
track.  `observe n` is what the certificate sees of the orbit at step `n`;
`Trans` is the transition relation the certificate must be closed under —
deliberately allowed to be *larger* than the true dynamics (the skeptic's-favor
rule of `CvdP.Transition`), which makes nonexistence of certificates stronger;
`Forcing q s` marks the states at which capture of the prime `q` is at issue. -/
structure Enrichment where
  /-- The states a certificate may distinguish. -/
  State : Type
  /-- The enriched shadow of the orbit. -/
  observe : ℕ → State
  /-- The transition relation; an over-approximation of the true dynamics. -/
  Trans : State → State → Prop
  /-- The actual orbit steps are transitions. -/
  observe_trans : ∀ n, Trans (observe n) (observe (n + 1))
  /-- Forcing states for a target prime. -/
  Forcing : ℕ → State → Prop

/-- A **certificate** that `q` is avoided, in the enrichment `E`: a set of
states closed under transitions, containing the orbit tail, and containing no
forcing state for `q`.  This is the common shape of every known omission proof
in the Euclid–Mullin family. -/
structure Certificate (E : Enrichment) (q : ℕ) where
  /-- The invariant set of enriched states. -/
  S : Set E.State
  /-- Closure under the transition relation. -/
  propagating : ∀ ⦃r⦄, r ∈ S → ∀ ⦃r'⦄, E.Trans r r' → r' ∈ S
  /-- The orbit tail lies in `S`. -/
  containsTail : ∃ N₀, ∀ n ≥ N₀, E.observe n ∈ S
  /-- No forcing state for `q` lies in `S`. -/
  blocks : ∀ r ∈ S, ¬ E.Forcing q r

/-- A propagating set is closed under the reflexive-transitive closure of the
transition relation. -/
theorem Certificate.mem_of_reaches {E : Enrichment} {q : ℕ} (C : Certificate E q)
    {r s : E.State} (hr : r ∈ C.S) (h : Relation.ReflTransGen E.Trans r s) :
    s ∈ C.S := by
  induction h with
  | refl => exact hr
  | tail _ hstep ih => exact C.propagating ih hstep

/-! ## Part 2: Semantics — what a certificate proves

The blocking condition acquires meaning through the relation between `Forcing`
and actual capture.  The two directions play different roles on the two sides
of the dichotomy:

* `CaptureImpliesForcing` (capture only happens at forcing states) makes a
  certificate a genuine **omission proof** — this is the *max*-side hook, the
  abstract content of `MaxVariant.missing_of_obstruction`.
* `ForcingImpliesCapture` (at a forcing state capture is compulsory) makes
  `blocks` a *necessary* feature of any avoidance certificate — this is the
  *min*-side hook (`CvdP.forcingState_captures`), the reason emptiness has
  bite. -/

/-- Capture events are recorded by `Forcing`: whenever `capture q n` holds, the
observed state at `n` is forcing for `q`. -/
def CaptureImpliesForcing (E : Enrichment) (capture : ℕ → ℕ → Prop) : Prop :=
  ∀ q n, capture q n → E.Forcing q (E.observe n)

/-- At a forcing state, capture is compulsory. -/
def ForcingImpliesCapture (E : Enrichment) (capture : ℕ → ℕ → Prop) : Prop :=
  ∀ q, Nat.Prime q → ∀ n, E.Forcing q (E.observe n) → capture q n

/-- **Certificates certify omission.**  If capture only happens at forcing
states, then a certificate for `q` shows `q` is eventually never captured. -/
theorem certificate_omits {E : Enrichment} {capture : ℕ → ℕ → Prop}
    (hsem : CaptureImpliesForcing E capture) {q : ℕ} (C : Certificate E q) :
    ∃ N₀, ∀ n ≥ N₀, ¬ capture q n := by
  obtain ⟨N₀, htail⟩ := C.containsTail
  exact ⟨N₀, fun n hn hcap =>
    C.blocks _ (htail n hn) (hsem q n hcap)⟩

/-! ## Part 3: Killability and the generic Emptiness Theorem -/

/-- An enrichment is **killable at `q`** if from every late orbit state a
forcing state for `q` is reachable inside the transition relation.  The
Eviction / Fullness / Reach argument of `no_cvdp_obstruction` is exactly a
proof method for this condition. -/
structure Killable (E : Enrichment) (q : ℕ) : Prop where
  reach_forcing : ∃ N₀, ∀ n ≥ N₀,
    ∃ s, Relation.ReflTransGen E.Trans (E.observe n) s ∧ E.Forcing q s

/-- **The Emptiness Theorem.**  A killable enrichment admits no certificate:
the tail meets the certificate, forcing is reachable from there, and
propagation drags the certificate onto a forcing state, contradicting
`blocks`. -/
theorem no_certificate {E : Enrichment} {q : ℕ} (hk : Killable E q) :
    IsEmpty (Certificate E q) := by
  constructor
  intro C
  obtain ⟨N₀, hreach⟩ := hk.reach_forcing
  obtain ⟨N₁, htail⟩ := C.containsTail
  obtain ⟨s, hs, hforce⟩ := hreach (max N₀ N₁) (le_max_left _ _)
  exact C.blocks s
    (C.mem_of_reaches (htail (max N₀ N₁) (le_max_right _ _)) hs) hforce

/-! ## Part 3b: Graded certificates — time-dependent invariants

`Certificate` fixes one invariant set for all time.  Every omission proof in the
Cox–van der Poorten genre has that shape, but it is a real restriction, and
`EM/Obstruction/Fragment.lean` disclaims it explicitly ("it does NOT cover:
time-dependent invariants `inv n`").  A **graded** certificate lets the invariant depend
on the step index, propagating from level `n` to level `n + 1`.

The emptiness argument survives verbatim once killability is stated with a step count
(`KillableIn`), because a `k`-step reach from `observe n` lands in `S (n + k)` and the
blocking condition is imposed at every level.  The congruence enrichment satisfies the
counted form — its killability witness is a *single* transition — so nothing is lost
(`congruence_killableIn`). -/

/-- Reachability in exactly `k` transitions. -/
def ReachesIn (E : Enrichment) : ℕ → E.State → E.State → Prop
  | 0 => fun r s => r = s
  | k + 1 => fun r s => ∃ t, E.Trans r t ∧ ReachesIn E k t s

theorem ReachesIn.toReflTransGen {E : Enrichment} :
    ∀ (k : ℕ) {r s : E.State}, ReachesIn E k r s → Relation.ReflTransGen E.Trans r s := by
  intro k
  induction k with
  | zero => intro r s h; have h' : r = s := h; exact h' ▸ Relation.ReflTransGen.refl
  | succ k ih =>
    rintro r s ⟨t, hrt, hts⟩
    exact Relation.ReflTransGen.head hrt (ih hts)

/-- A **graded certificate**: an avoidance certificate whose invariant is allowed to
depend on the step index.  Strictly more general than `Certificate`, which is the
constant family (`Certificate.toGraded`). -/
structure GradedCertificate (E : Enrichment) (q : ℕ) where
  /-- The invariant at each stage. -/
  S : ℕ → Set E.State
  /-- One transition advances the stage by one. -/
  propagating : ∀ n ⦃r⦄, r ∈ S n → ∀ ⦃r'⦄, E.Trans r r' → r' ∈ S (n + 1)
  /-- The orbit tail lies in the invariant, stage by stage. -/
  containsTail : ∃ N₀, ∀ n ≥ N₀, E.observe n ∈ S n
  /-- No stage contains a forcing state. -/
  blocks : ∀ n, ∀ r ∈ S n, ¬ E.Forcing q r

/-- A plain certificate is the constant graded family. -/
def Certificate.toGraded {E : Enrichment} {q : ℕ} (C : Certificate E q) :
    GradedCertificate E q where
  S := fun _ => C.S
  propagating := fun _ _ hr _ h => C.propagating hr h
  containsTail := C.containsTail
  blocks := fun _ => C.blocks

theorem GradedCertificate.mem_of_reachesIn {E : Enrichment} {q : ℕ}
    (C : GradedCertificate E q) :
    ∀ (k n : ℕ) {r s : E.State}, r ∈ C.S n → ReachesIn E k r s → s ∈ C.S (n + k) := by
  intro k
  induction k with
  | zero =>
    intro n r s hr h
    have h' : r = s := h
    simpa [← h'] using hr
  | succ k ih =>
    rintro n r s hr ⟨t, hrt, hts⟩
    have hmem := ih (n + 1) (C.propagating n hr hrt) hts
    have heq : n + 1 + k = n + (k + 1) := by omega
    rwa [heq] at hmem

/-- Killability with an explicit step count.  This is what the graded emptiness theorem
consumes; `Killable` forgets the count and is too weak to drive a graded invariant. -/
structure KillableIn (E : Enrichment) (q : ℕ) : Prop where
  reach_forcing : ∃ N₀, ∀ n ≥ N₀, ∃ (k : ℕ) (s : E.State),
    ReachesIn E k (E.observe n) s ∧ E.Forcing q s

theorem KillableIn.toKillable {E : Enrichment} {q : ℕ} (hk : KillableIn E q) :
    Killable E q := by
  obtain ⟨N₀, h⟩ := hk.reach_forcing
  refine ⟨⟨N₀, fun n hn => ?_⟩⟩
  obtain ⟨k, s, hs, hf⟩ := h n hn
  exact ⟨s, ReachesIn.toReflTransGen k hs, hf⟩

/-- **The graded Emptiness Theorem.**  A counted-killable enrichment admits no graded
certificate — so allowing the invariant to depend on the step index does not help. -/
theorem no_graded_certificate {E : Enrichment} {q : ℕ} (hk : KillableIn E q) :
    IsEmpty (GradedCertificate E q) := by
  constructor
  intro C
  obtain ⟨N₀, hreach⟩ := hk.reach_forcing
  obtain ⟨N₁, htail⟩ := C.containsTail
  obtain ⟨k, s, hs, hforce⟩ := hreach (max N₀ N₁) (le_max_left _ _)
  exact C.blocks _ s (C.mem_of_reachesIn k _ (htail _ (le_max_right _ _)) hs) hforce

/-! ## Part 4: Refinement — comparing enrichments

`Refines E' E` says `E'` is a finer enrichment projecting onto `E`.
Certificates pull back from coarse to fine (`Certificate.pullback`), and
killability pushes forward from fine to coarse (`Killable.of_refines`) — the
two statements are contrapositives of each other through `no_certificate`.

CAVEAT (inherited from `EM/Obstruction/NoInvariant.lean` Part 6): for congruence
enrichments the `forcing_map` axiom **fails** along the modulus projection,
because `ForcingState q m'` quantifies over a smaller residue class than
`ForcingState q m`.  The repair there is the death-avoiding form `BlocksDeath`;
its abstract version can be added as a `Death` field when the reciprocity
enrichment is formalized and actually needs it. -/

/-- `E'` refines `E`: states project, the orbit shadows agree, transitions and
forcing map forward. -/
structure Refines (E' E : Enrichment) where
  proj : E'.State → E.State
  observe_comm : ∀ n, proj (E'.observe n) = E.observe n
  trans_map : ∀ ⦃r r'⦄, E'.Trans r r' → E.Trans (proj r) (proj r')
  forcing_map : ∀ q ⦃r⦄, E'.Forcing q r → E.Forcing q (proj r)

/-- Certificates pull back along a refinement: a coarse certificate yields a
fine one on the preimage set.  (The abstract Lifting Lemma.) -/
def Certificate.pullback {E' E : Enrichment} (ρ : Refines E' E) {q : ℕ}
    (C : Certificate E q) : Certificate E' q where
  S := ρ.proj ⁻¹' C.S
  propagating := fun _ hr _ hstep => C.propagating hr (ρ.trans_map hstep)
  containsTail := by
    obtain ⟨N₀, h⟩ := C.containsTail
    refine ⟨N₀, fun n hn => ?_⟩
    show ρ.proj (E'.observe n) ∈ C.S
    rw [ρ.observe_comm n]
    exact h n hn
  blocks := fun r hr hf => C.blocks _ hr (ρ.forcing_map q hf)

/-- Killability pushes forward along a refinement: if the fine enrichment is
killable, so is the coarse one. -/
theorem Killable.of_refines {E' E : Enrichment} (ρ : Refines E' E) {q : ℕ}
    (hk : Killable E' q) : Killable E q := by
  obtain ⟨N₀, h⟩ := hk.reach_forcing
  refine ⟨⟨N₀, fun n hn => ?_⟩⟩
  obtain ⟨s, hs, hf⟩ := h n hn
  refine ⟨ρ.proj s, ?_, ρ.forcing_map q hf⟩
  -- `ReflTransGen.lift` now returns a relation inequality (stated with `Function.onFun`),
  -- so apply it to the endpoints and unfold before rewriting
  have := Relation.ReflTransGen.lift ρ.proj (fun _ _ h => ρ.trans_map h) _ _ hs
  simp only [Function.onFun] at this
  rwa [ρ.observe_comm n] at this

/-! ## Part 5: The congruence enrichment (the min pole)

The canonical family: states are residues mod `m`, the transition is
`CvdP.Transition`, forcing is `CvdP.ForcingState`.  `observe_trans` is where the
true orbit is checked against the over-approximated transition (this fact was
not needed in `NoInvariant.lean`, whose proof only used tail-containment; here
it is part of the enrichment's contract). -/

open CvdP

/-- The candidate at step `n` is odd (the accumulator is even). -/
private theorem prod_succ_odd' (n : ℕ) : Odd (prod n + 1) := by
  have h2 : (2 : ℕ) ∣ prod n := by
    have := seq_dvd_prod 0 n (Nat.zero_le n)
    rwa [seq_zero] at this
  obtain ⟨k, hk⟩ := h2
  exact Nat.odd_iff.mpr (by omega)

/-- The congruence enrichment at modulus `m`. -/
def congruence (m : ℕ) : Enrichment where
  State := ZMod m
  observe n := ((prod n : ℕ) : ZMod m)
  Trans := Transition m
  observe_trans n := by
    have hp2 := prod_ge_two n
    have hge : 2 ≤ prod n + 1 := by omega
    refine ⟨prod n + 1, prod_succ_odd' n, by omega, by push_cast; ring, ?_⟩
    have hstep : prod (n + 1) = prod n * Nat.minFac (prod n + 1) := by
      rw [prod_succ, seq_succ, euclid_minFac_eq_nat_minFac _ hge]
    rw [hstep]
    push_cast
    ring
  Forcing q r := ForcingState q m r

/-- Certificates in the congruence enrichment are exactly CvdP obstructions. -/
theorem certificate_congruence_iff_cvdp {q m : ℕ} :
    Nonempty (Certificate (congruence m) q) ↔
      ∃ S : Set (ZMod m), CvdPObstruction q m S := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.S, fun r hr r' h => C.propagating hr h, C.blocks, C.containsTail⟩
  · rintro ⟨S, hprop, hblock, htail⟩
    exact ⟨⟨S, fun r hr r' h => hprop r hr r' h, htail, hblock⟩⟩

/-- Forcing states in the congruence enrichment compulsorily capture:
the min-side semantics. -/
theorem congruence_forcing_captures (m : ℕ) :
    ForcingImpliesCapture (congruence m) (fun q n => seq (n + 1) = q) :=
  fun _ hq _ hf => forcingState_captures hq hf

/-- **Eviction + Fullness + Reach, extracted.**  From every late orbit state the state is
*free* (`Pₙ + 1` is a unit mod `m`), and there is a CRT-chosen unit `u` — congruent to
`-Pₙ⁻¹` mod `q` and to `1` at every other prime of `m` — for which `Pₙ · u` is a forcing
state for `q`.

This is the arithmetic core of `no_cvdp_obstruction`, stated *without* committing to how
the transition to `Pₙ · u` is realized.  `congruence_killable` realizes it with
`free_transition`; the size-guarded fragment of `EM/Obstruction/Fragment.lean` realizes it
with `free_transition_large`, which is why the two share this lemma. -/
theorem congruence_reaches_forcing {q m : ℕ} (hq : q ∈ MissingPrimes) (hm : m ≠ 0)
    (hrich : RichEnough q m) :
    ∃ N₀, ∀ n ≥ N₀, IsUnit (((prod n : ℕ) : ZMod m) + 1) ∧
      ∃ u : (ZMod m)ˣ, ForcingState q m (((prod n : ℕ) : ZMod m) * (u : ZMod m)) := by
  have : NeZero m := ⟨hm⟩
  have hqp : Nat.Prime q := hq.1
  have : NeZero q := ⟨hqp.pos.ne'⟩
  have : Fact (Nat.Prime q) := ⟨hqp⟩
  obtain ⟨N₀, hfree⟩ := exists_tail_coprime m hm
  refine ⟨N₀, fun n hn => ?_⟩
  have hcop : Nat.Coprime (prod n + 1) m := hfree n hn
  -- freeness of the tail state
  have hunit : IsUnit (((prod n : ℕ) : ZMod m) + 1) := by
    have hc : ((prod n + 1 : ℕ) : ZMod m) = ((prod n : ℕ) : ZMod m) + 1 := by push_cast; ring
    rw [← hc]
    exact (ZMod.isUnit_iff_coprime _ _).mpr hcop
  -- q divides no running product
  have hqnd : ¬ q ∣ prod n :=
    prime_not_in_seq_not_dvd_prod ((isPrime_iff_natPrime q).mpr hqp) hq.2 n
  -- the local correction c at the prime q
  have hu : ((prod n : ℕ) : ZMod q) ≠ 0 := fun h => hqnd ((ZMod.natCast_eq_zero_iff _ _).mp h)
  set cz : ZMod q := -(((prod n : ℕ) : ZMod q))⁻¹ with hcz
  set c : ℕ := cz.val with hcdef
  have hcast_c : ((c : ℕ) : ZMod q) = cz := by
    simp [hcdef, ZMod.natCast_val, ZMod.cast_id]
  have hczne : cz ≠ 0 := by
    simp only [hcz, neg_ne_zero]
    exact inv_ne_zero hu
  have hqc : Nat.Coprime q c := by
    refine (Nat.Prime.coprime_iff_not_dvd hqp).mpr ?_
    intro hdvd
    exact hczne (by rw [← hcast_c]; exact (ZMod.natCast_eq_zero_iff _ _).mpr hdvd)
  have hqdvd : q ∣ prod n * c + 1 := by
    refine (ZMod.natCast_eq_zero_iff _ _).mp ?_
    push_cast
    rw [hcast_c, hcz]
    field_simp
    ring
  -- the complementary modulus D
  set D : ℕ := ∏ p ∈ m.primeFactors.erase q, p with hD
  have hqD : Nat.Coprime q D := by
    refine (Nat.Prime.coprime_iff_not_dvd hqp).mpr ?_
    intro hdvd
    obtain ⟨p, hp, hpd⟩ := (hqp.prime.dvd_finsetProd_iff (fun p => p)).mp hdvd
    have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
    have : q = p := (Nat.prime_dvd_prime_iff_eq hqp hpprime).mp hpd
    exact (Finset.ne_of_mem_erase hp) this.symm
  -- CRT: the multiplier s
  obtain ⟨s, hsq, hsD⟩ := Nat.chineseRemainder hqD c 1
  have hsm : Nat.Coprime s m := by
    apply coprime_of_no_common_prime
    intro p hp hps hpm
    by_cases hpq : p = q
    · subst hpq
      have h0 : c ≡ 0 [MOD p] := hsq.symm.trans (Nat.modEq_zero_iff_dvd.mpr hps)
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp hqc (Nat.modEq_zero_iff_dvd.mp h0)
    · have hmemp : p ∈ m.primeFactors.erase q :=
        Finset.mem_erase.mpr ⟨hpq, Nat.mem_primeFactors.mpr ⟨hp, hpm, hm⟩⟩
      have hpD : p ∣ D := Finset.dvd_prod_of_mem _ hmemp
      have h1 : s ≡ 1 [MOD p] := Nat.ModEq.of_dvd hpD hsD
      have h0 : (0 : ℕ) ≡ 1 [MOD p] := (Nat.modEq_zero_iff_dvd.mpr hps).symm.trans h1
      have hd1 : p ∣ 1 := (Nat.modEq_iff_dvd' (by omega)).mp h0
      have h1' := hp.one_lt
      have := Nat.dvd_one.mp hd1
      omega
  -- the CRT-chosen unit, and the verification that `Pₙ · u` is forcing
  refine ⟨hunit, ZMod.unitOfCoprime s hsm, ?_⟩
  rw [ZMod.coe_unitOfCoprime]
  intro N hN
  have hNmod : N ≡ prod n * s + 1 [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff, hN]
    push_cast
    ring
  constructor
  · -- q ∣ N
    have h1 : N ≡ prod n * s + 1 [MOD q] := Nat.ModEq.of_dvd hrich.1 hNmod
    have h2 : prod n * s + 1 ≡ prod n * c + 1 [MOD q] := Nat.ModEq.add_right 1 (hsq.mul_left _)
    have h3 : prod n * c + 1 ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr hqdvd
    exact Nat.modEq_zero_iff_dvd.mp ((h1.trans h2).trans h3)
  · -- no odd prime below q divides N
    intro p hp hodd hlt hcon
    have hpm : p ∣ m := hrich.2 p hp hodd hlt
    have hpq : p ≠ q := by omega
    have hmemp : p ∈ m.primeFactors.erase q :=
      Finset.mem_erase.mpr ⟨hpq, Nat.mem_primeFactors.mpr ⟨hp, hpm, hm⟩⟩
    have hpD : p ∣ D := Finset.dvd_prod_of_mem _ hmemp
    have h1 : N ≡ prod n * s + 1 [MOD p] := Nat.ModEq.of_dvd hpm hNmod
    have h2 : prod n * s + 1 ≡ prod n * 1 + 1 [MOD p] :=
      Nat.ModEq.add_right 1 ((Nat.ModEq.of_dvd hpD hsD).mul_left _)
    have h3 : N ≡ prod n + 1 [MOD p] := by simpa using h1.trans h2
    have h4 : prod n + 1 ≡ 0 [MOD p] :=
      (h3.symm).trans (Nat.modEq_zero_iff_dvd.mpr hcon)
    have h5 : p ∣ prod n + 1 := Nat.modEq_zero_iff_dvd.mp h4
    have hd1 : p ∣ 1 := hcop ▸ Nat.dvd_gcd h5 hpm
    have h1' := hp.one_lt
    have := Nat.dvd_one.mp hd1
    omega

/-- **The congruence enrichment is killable** at every missing prime, for every rich
modulus: from every late (hence free) orbit state, ONE transition — multiply by the
CRT-chosen unit — reaches a forcing state. -/
theorem congruence_killable {q m : ℕ} (hq : q ∈ MissingPrimes) (hm : m ≠ 0)
    (hrich : RichEnough q m) : Killable (congruence m) q := by
  obtain ⟨N₀, h⟩ := congruence_reaches_forcing hq hm hrich
  refine ⟨⟨N₀, fun n hn => ?_⟩⟩
  obtain ⟨hunit, u, hforce⟩ := h n hn
  exact ⟨_, Relation.ReflTransGen.single (free_transition hm _ hunit u), hforce⟩

/-- **The congruence enrichment is killable in ONE step.**  The strengthening that makes
the graded (time-dependent) emptiness theorem apply: `Killable` only asks that a forcing
state be reachable, `KillableIn` records that a single transition suffices. -/
theorem congruence_killableIn {q m : ℕ} (hq : q ∈ MissingPrimes) (hm : m ≠ 0)
    (hrich : RichEnough q m) : KillableIn (congruence m) q := by
  obtain ⟨N₀, h⟩ := congruence_reaches_forcing hq hm hrich
  refine ⟨⟨N₀, fun n hn => ?_⟩⟩
  obtain ⟨hunit, u, hforce⟩ := h n hn
  exact ⟨1, _, ⟨_, free_transition hm _ hunit u, rfl⟩, hforce⟩

/-- **No graded certificate for the congruence enrichment**: time-dependent congruence
invariants do not block a missing prime either. -/
theorem no_graded_certificate_congruence {q m : ℕ} (hq : q ∈ MissingPrimes) (hm : m ≠ 0)
    (hrich : RichEnough q m) : IsEmpty (GradedCertificate (congruence m) q) :=
  no_graded_certificate (congruence_killableIn hq hm hrich)

/-- **The No-Invariant Theorem, re-derived inside the calculus**: killability of
the congruence enrichment plus the generic Emptiness Theorem give back
`no_cvdp_obstruction`.  This is the abstraction test: the specific theorem is
recovered from the general machinery with no additional argument. -/
theorem no_cvdp_obstruction' {q m : ℕ} (hq : q ∈ MissingPrimes) (hm : m ≠ 0)
    (hrich : RichEnough q m) (S : Set (ZMod m)) : ¬ CvdPObstruction q m S := by
  intro hS
  exact (no_certificate (congruence_killable hq hm hrich)).false
    (certificate_congruence_iff_cvdp.mpr ⟨S, hS⟩).some

/-! ## Part 6: The max pole — the framework is not vacuous

The max transition system fits the same `Enrichment` shape, and the machine
verified Cox–van der Poorten obstruction `{6} ⊆ ZMod 12` is a `Certificate` in
it.  Consequently `Killable` **fails** for the max enrichment — derived, not
asserted: this is the formal statement that Fullness is min-specific, and it is
exactly the room in which CvdP's omission proof lives. -/

open MaxVariant

/-- The actual max-orbit step is an instance of the abstract max transition, at
every modulus (generalizes `MaxVariant.mprod_step_maxR` from `12`). -/
theorem mprod_step_maxR' (m n : ℕ) :
    MaxR m ((mprod n : ℕ) : ZMod m) ((mprod (n + 1) : ℕ) : ZMod m) := by
  refine ⟨mprod n + 1, Nat.odd_iff.mpr (mprod_succ_odd n),
    by have := mprod_ge_two n; omega, by push_cast; ring, ?_⟩
  rw [mprod_succ, mseq_succ]
  push_cast
  ring

/-- The max-side congruence enrichment at modulus `m`. -/
def maxCongruence (m : ℕ) : Enrichment where
  State := ZMod m
  observe n := ((mprod n : ℕ) : ZMod m)
  Trans := MaxR m
  observe_trans n := mprod_step_maxR' m n
  Forcing q r := MaxForcingState m q r

/-- On the max side, capture *implies* forcing (the candidate `mprod n + 1`
itself is the forcing witness).  This is the semantics that makes a max
certificate an omission proof. -/
theorem maxCongruence_capture_implies_forcing (m : ℕ) :
    CaptureImpliesForcing (maxCongruence m) (fun q n => mseq (n + 1) = q) := by
  intro q n hcap
  refine ⟨mprod n + 1, Nat.odd_iff.mpr (mprod_succ_odd n),
    by have := mprod_ge_two n; omega, ?_, by rw [← mseq_succ]; exact hcap⟩
  show ((mprod n + 1 : ℕ) : ZMod m) = ((mprod n : ℕ) : ZMod m) + 1
  push_cast
  ring

/-- **The CvdP obstruction, as a `Certificate` of the calculus.** -/
def maxCertificate_five : Certificate (maxCongruence 12) 5 where
  S := {(6 : ZMod 12)}
  propagating := fun r hr r' h => maxPropagating_six r hr r' h
  containsTail := ⟨1, fun _ hn => mprod_mem_six hn⟩
  blocks := maxBlocks_six_five

/-- Cox–van der Poorten, re-derived through the calculus: `5` is eventually
never captured by the max rule.  (Abstract version of
`MaxVariant.five_not_mem_mseq'`.) -/
theorem max_omits_five : ∃ N₀, ∀ n ≥ N₀, mseq (n + 1) ≠ 5 :=
  certificate_omits (maxCongruence_capture_implies_forcing 12) maxCertificate_five

/-- **Killability fails for the max enrichment** — derived from the existence
of the certificate.  This is the formal home of "Fullness is min-specific":
the very theorem that is *provable* for `congruence m` (`congruence_killable`)
is *refutable* for `maxCongruence 12`. -/
theorem max_not_killable : ¬ Killable (maxCongruence 12) 5 :=
  fun hk => (no_certificate hk).false maxCertificate_five

/-! ## Part 7: Trace completeness

The completeness Prop, stated per-prime because killability of the congruence
enrichment is per-modulus rich.  HONESTY: over a killable family this is
*equivalent* to `MullinConjecture` (`traceComplete_iff_mullin`), exactly as
`IC_min ↔ MullinConjecture`.  The calculus does not weaken MC; it organizes the
no-go content and makes "grow the killed class" the precise frontier. -/

/-- A **trace family**: for each prime, a set of enrichments in which avoidance
would be required to leave a trace. -/
def TraceFamily : Type 1 := ℕ → Set Enrichment

/-- The family is **killable**: every member enrichment is killable at its
missing prime. -/
def KillableFamily (F : TraceFamily) : Prop :=
  ∀ q ∈ MissingPrimes, ∀ E ∈ F q, Killable E q

/-- **Trace completeness**: every missing prime admits a certificate somewhere
in its family.  "Avoidance must leave a trace." -/
def TraceComplete (F : TraceFamily) : Prop :=
  ∀ q ∈ MissingPrimes, ∃ E ∈ F q, Nonempty (Certificate E q)

/-- Trace completeness over a killable family implies Mullin's Conjecture. -/
theorem mc_of_traceComplete {F : TraceFamily} (hkill : KillableFamily F)
    (h : TraceComplete F) : MullinConjecture := by
  intro p hp
  by_contra hcon
  have hmiss : p ∈ MissingPrimes :=
    ⟨(isPrime_iff_natPrime p).mp hp, fun k hk => hcon ⟨k, hk⟩⟩
  obtain ⟨E, hE, ⟨C⟩⟩ := h p hmiss
  exact (no_certificate (hkill p hmiss E hE)).false C

/-- Conversely MC makes any trace completeness vacuous: over a killable family,
trace completeness is *equivalent* to Mullin's Conjecture. -/
theorem traceComplete_iff_mullin {F : TraceFamily} (hkill : KillableFamily F) :
    TraceComplete F ↔ MullinConjecture := by
  refine ⟨mc_of_traceComplete hkill, fun h q hq => ?_⟩
  obtain ⟨n, hn⟩ := h q ((isPrime_iff_natPrime q).mpr hq.1)
  exact absurd hn (hq.2 n)

/-- The congruence trace family: all rich congruence enrichments for `q`. -/
def congruenceFamily : TraceFamily :=
  fun q => {E | ∃ m : ℕ, m ≠ 0 ∧ RichEnough q m ∧ E = congruence m}

/-- The congruence family is killable — the calculus form of the No-Invariant
Theorem. -/
theorem congruenceFamily_killable : KillableFamily congruenceFamily := by
  rintro q hq E ⟨m, hm, hrich, rfl⟩
  exact congruence_killable hq hm hrich

/-- **`IC_min` is exactly the trace completeness of the congruence family.**
The certificate language and the obstruction language coincide. -/
theorem traceComplete_congruence_iff_ic_min :
    TraceComplete congruenceFamily ↔ IC_min := by
  constructor
  · intro h q hq
    obtain ⟨E, ⟨m, hm, hrich, rfl⟩, hC⟩ := h q hq
    obtain ⟨S, hS⟩ := certificate_congruence_iff_cvdp.mp hC
    exact ⟨m, hm, hrich, S, hS⟩
  · intro h q hq
    obtain ⟨m, hm, hrich, S, hS⟩ := h q hq
    exact ⟨congruence m, ⟨m, hm, hrich, rfl⟩,
      certificate_congruence_iff_cvdp.mpr ⟨S, hS⟩⟩

/-! ## Part 8: Landscape -/

/-- The obstruction calculus, as one statement:
1. killable enrichments admit no certificates (Emptiness);
2. the congruence family is killable (the No-Invariant Theorem, calculus form);
3. the No-Invariant Theorem is recovered from the calculus;
4. the max pole is a genuine certificate, so max is not killable
   (Fullness is min-specific — derived, not asserted);
5. trace completeness of the congruence family is `IC_min`, and over any
   killable family trace completeness is exactly Mullin's Conjecture. -/
theorem obstruction_calculus_landscape :
    (∀ (E : Enrichment) (q : ℕ), Killable E q → IsEmpty (Certificate E q)) ∧
    KillableFamily congruenceFamily ∧
    (∀ q m : ℕ, q ∈ MissingPrimes → m ≠ 0 → RichEnough q m →
      ∀ S : Set (ZMod m), ¬ CvdPObstruction q m S) ∧
    (Nonempty (Certificate (maxCongruence 12) 5) ∧ ¬ Killable (maxCongruence 12) 5) ∧
    (TraceComplete congruenceFamily ↔ IC_min) ∧
    (∀ F : TraceFamily, KillableFamily F → (TraceComplete F ↔ MullinConjecture)) :=
  ⟨fun _ _ hk => no_certificate hk,
    congruenceFamily_killable,
    fun _ _ hq hm hrich S => no_cvdp_obstruction' hq hm hrich S,
    ⟨⟨maxCertificate_five⟩, max_not_killable⟩,
    traceComplete_congruence_iff_ic_min,
    fun _ hkill => traceComplete_iff_mullin hkill⟩

end Obstruction
