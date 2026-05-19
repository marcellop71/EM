import EM.Population.HittingSetStructure
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# No Congruence Invariant Can Block a Prime in the Min Euclid–Mullin Sequence

## The two Euclid–Mullin sequences

There are two Euclid–Mullin sequences.

* The **min** sequence (the one formalized in this repository): `P₀ = 2`,
  `pₙ = minFac (Pₙ + 1)`, `P_{n+1} = Pₙ · pₙ`.  Mullin's Conjecture (`MullinConjecture`)
  asserts every prime occurs.
* The **max** sequence: same recursion with `maxFac` in place of `minFac`.  It
  *provably* omits primes: Cox–van der Poorten (1968) showed `5` never occurs, and
  Booker showed infinitely many primes are omitted.

Every known omission proof for the max sequence works by exhibiting a **propagating
congruence invariant**: a set `S` of residues modulo some `m`, closed under the
transition dynamics, containing the orbit tail, and containing no state from which the
target prime is compulsorily captured.  Call such a certificate a *CvdP obstruction*.

This file proves that **no CvdP obstruction can ever exist for the min sequence**
(`no_cvdp_obstruction`).  That is the min/max asymmetry, made formal.

## The dichotomy (why min and max differ)

The whole argument hinges on two ingredients that are *false for `maxFac`*:

* `hittingSet_finite` (Step 0).  For a missing prime `ℓ`, the set of steps where
  `ℓ ∣ Pₙ + 1` is finite, because at such a step the *smallest* factor of `Pₙ + 1` is
  a prime `< ℓ`, and no prime repeats.  Under `maxFac` the chosen factor is `≥ ℓ`, the
  guardian bound `seq (n+1) < ℓ` fails outright, and the hitting set may well be
  infinite.
* `forcingState_captures`, i.e. the very definition of `ForcingState`.  For `minFac`
  the capture condition "`minFac N = q`" is equivalent to "`q ∣ N` and no odd prime
  `< q` divides `N`" — a *congruence* condition on `N`, satisfiable modulo the rich
  modulus `forcingModulus q`.  Forcing states therefore exist, and `Blocks` is a
  genuine constraint that a certificate has to meet.  Under `maxFac` the capture
  condition "`maxFac N = q`" reads "`q ∣ N` and `N / q` is `q`-smooth" — a *smoothness*
  (anatomy) condition, which is not a congruence condition at any fixed modulus, since
  every residue class contains numbers with arbitrarily large prime factors.  The
  max-side analogue of `ForcingState` is consequently essentially never satisfied,
  `Blocks` degenerates into a vacuous condition, and obstructions exist trivially.
  This is exactly where Booker-type omissions live.

Step 3 (`free_transition`) is by contrast **rule-symmetric** and is *not* a source of
asymmetry: for `maxFac` one merely picks the two primes in the other order — first a
prime `π ≡ (r+1)·s⁻¹`, then a prime `M > π` with `M ≡ s`, so that again `N = π·M ≡ r+1`
while now `maxFac N = M ≡ s`.  Free-state fullness holds under both rules.

The even part behaves the same way (`no_cvdp_obstruction_two_part`): the frozen 2-adic
data (`Pₙ ≡ 2 mod 4`, candidate `≡ 3 mod 4`) is harmless for the min sequence because
"`q ∣ N` and `N ≡ 3 (mod 4)`" is satisfiable for every odd `q`; our Dirichlet
construction takes place modulo the *whole* modulus `m`, so the mod-4 constraint is
absorbed automatically.  In exact contrast, for the max sequence the appearance
condition for `5` is `N = 5^c`, which forces `N ≡ 1 (mod 4)` and is *killed* by the
frozen `3 mod 4`.  A congruence obstruction can only bite when the appearance condition
is not itself a full-freedom congruence condition.  For `minFac` it always is.

## Main definitions

* `Transition m r r'` : the (over-approximated) transition relation on `ZMod m`.
* `Propagating`, `ForcingState`, `Blocks`, `ContainsTail`, `CvdPObstruction`.
* `RichEnough q m`, `forcingModulus q` : the modulus must see `q` and all odd primes `< q`.
* `IC_min` : the open Prop "every missing prime admits a CvdP obstruction".

## Main results

* `hittingSet_finite`, `hittingSet_ncard_le` : Step 0 (finite hitting).
* `exists_tail_coprime` : Step 1+2 (the orbit is eventually free forever).
* `free_transition` : Step 3 (free states reach the full translated unit orbit).
* `no_cvdp_obstruction` : Steps 4+5 — the No-Invariant Theorem.
* `no_finite_prime_covering`, `no_covering_family_obstruction` : covering-system style
  certificates are already covered (Part 6b).
* `ic_min_implies_mullin` : `IC_min → MullinConjecture`.
-/

open Mullin Euclid MullinGroup RotorRouter
open Classical

namespace CvdP

/-! ## Part 0: Two small arithmetic helpers -/

/-- If no prime divides both `a` and `b`, they are coprime. -/
theorem coprime_of_no_common_prime {a b : ℕ}
    (h : ∀ p, Nat.Prime p → p ∣ a → p ∣ b → False) : Nat.Coprime a b := by
  by_contra hg
  have hne : Nat.gcd a b ≠ 1 := hg
  have hp : Nat.Prime (Nat.minFac (Nat.gcd a b)) := Nat.minFac_prime hne
  exact h _ hp ((Nat.minFac_dvd _).trans (Nat.gcd_dvd_left a b))
    ((Nat.minFac_dvd _).trans (Nat.gcd_dvd_right a b))

/-- `minFac (π * M) = π` when `π < M` are both prime.  For `maxFac` the answer would be
`M` instead — but that costs no generality, since one may reorder the two primes; see
the "rule-symmetric" remark on `free_transition`. -/
theorem minFac_mul_of_lt {p₁ p₂ : ℕ} (h₁ : Nat.Prime p₁) (h₂ : Nat.Prime p₂)
    (hlt : p₁ < p₂) : Nat.minFac (p₁ * p₂) = p₁ := by
  have hne : p₁ * p₂ ≠ 1 := by
    have := h₁.two_le
    have := h₂.two_le
    nlinarith
  have hle : Nat.minFac (p₁ * p₂) ≤ p₁ :=
    Nat.minFac_le_of_dvd h₁.two_le ⟨p₂, rfl⟩
  have hpr := Nat.minFac_prime hne
  have hdvd := Nat.minFac_dvd (p₁ * p₂)
  rcases (Nat.Prime.dvd_mul hpr).mp hdvd with h | h
  · exact (Nat.prime_dvd_prime_iff_eq hpr h₁).mp h
  · have : Nat.minFac (p₁ * p₂) = p₂ := (Nat.prime_dvd_prime_iff_eq hpr h₂).mp h
    omega

/-! ## Part 1 (Step 0): Finite hitting for missing primes

For a missing prime `q`, every step `n` with `q ∣ Pₙ + 1` is *shielded*: the captured
factor `seq (n+1) = minFac (Pₙ + 1)` is a prime `< q`.  Since primes never repeat, the
map `n ↦ seq (n+1)` injects `HittingSet q` into the primes below `q`. -/

/-- **Step 0 (Finite Hitting).**  For a missing prime `q`, the hitting set is finite.

Min-specific: the guardian bound `seq (n+1) < q` is exactly `minFac (Pₙ+1) < q`, which
fails for `maxFac`.

The proof now lives in its natural home, `EM/Population/HittingSetStructure.lean`
(Part 2b), next to `hitting_step_guardian`; this is an alias so that the `CvdP`-qualified
name keeps working. -/
theorem hittingSet_finite {q : ℕ} (hq : q ∈ MissingPrimes) : (HittingSet q).Finite :=
  _root_.hittingSet_finite hq

/-- Explicit cardinality bound: a missing prime `q` is hit at most `q` times
(indeed only at steps whose guardian is one of the primes below `q`).
Alias for `_root_.hittingSet_ncard_le`. -/
theorem hittingSet_ncard_le {q : ℕ} (hq : q ∈ MissingPrimes) :
    (HittingSet q).ncard ≤ q :=
  _root_.hittingSet_ncard_le hq

/-! ## Part 2 (Steps 1+2): The orbit is eventually free forever -/

/-- For every prime `ℓ`, eventually `ℓ ∤ Pₙ + 1`.

Two cases, the **A/B split**: if `ℓ` occurs in the sequence (case A) then `ℓ ∣ Pₙ`
from that point on, so `ℓ ∤ Pₙ + 1`; if `ℓ` never occurs (case B) then `ℓ`'s hitting set
is finite by `hittingSet_finite`. -/
theorem eventually_not_dvd_succ (l : ℕ) (hl : Nat.Prime l) :
    ∃ N₀, ∀ n ≥ N₀, ¬ (l ∣ prod n + 1) := by
  by_cases h : ∃ k, seq k = l
  · obtain ⟨k, hk⟩ := h
    refine ⟨k, fun n hn hdvd => ?_⟩
    have h1 : l ∣ prod n := hk ▸ seq_dvd_prod k n hn
    have h2 : l ∣ 1 := by simpa using Nat.dvd_sub hdvd h1
    have := Nat.dvd_one.mp h2
    have := hl.one_lt
    omega
  · have hmiss : l ∈ MissingPrimes := ⟨hl, fun k hk => h ⟨k, hk⟩⟩
    obtain ⟨b, hb⟩ := (hittingSet_finite hmiss).bddAbove
    refine ⟨b + 1, fun n hn hdvd => ?_⟩
    have hn' : n ∈ HittingSet l := hdvd
    have := hb hn'
    omega

/-- **Steps 1+2 (Eviction Lemma).**  For any modulus `m ≠ 0` the orbit is eventually
*free* forever: `Pₙ + 1` is coprime to `m` for all large `n`.

Note this is unconditional — no missing-prime assumption is needed, because each prime
`ℓ ∣ m` is evicted either by having occurred (case A) or by finite hitting (case B). -/
theorem exists_tail_coprime (m : ℕ) (hm : m ≠ 0) :
    ∃ N₀, ∀ n ≥ N₀, Nat.Coprime (prod n + 1) m := by
  have key : ∀ l : ℕ, ∃ N₀, ∀ n ≥ N₀, Nat.Prime l → ¬ (l ∣ prod n + 1) := by
    intro l
    by_cases hl : Nat.Prime l
    · obtain ⟨N, hN⟩ := eventually_not_dvd_succ l hl
      exact ⟨N, fun n hn _ => hN n hn⟩
    · exact ⟨0, fun _ _ hcon => absurd hcon hl⟩
  choose F hF using key
  refine ⟨m.primeFactors.sup F, fun n hn => ?_⟩
  apply coprime_of_no_common_prime
  intro p hp hpa hpm
  have hmem : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpm, hm⟩
  have hle : F p ≤ n := le_trans (Finset.le_sup hmem) hn
  exact hF p n hle hp hpa

/-! ## Part 3: The transition relation and congruence obstructions -/

/-- The **transition relation** on `ZMod m`: `r → r'` iff there is an odd candidate
`N ≥ 3` in the residue class `r + 1` with `r' = r · minFac N`.

DESIGN CHOICE: `Transition` admits *any* natural number `N` in the residue class as a
candidate, not merely those integers actually realizable as Euclid–Mullin candidates.
Hence `Transition` is strictly **larger** than the true orbit dynamics.  This makes an
invariant's job strictly **easier**, so the nonexistence statement proved below is
strictly **stronger** than nonexistence for the true dynamics. -/
def Transition (m : ℕ) (r r' : ZMod m) : Prop :=
  ∃ N : ℕ, Odd N ∧ 3 ≤ N ∧ (N : ZMod m) = r + 1 ∧ r' = r * (Nat.minFac N : ZMod m)

/-- A set of residues is **propagating** if it is closed under `Transition`. -/
def Propagating (m : ℕ) (S : Set (ZMod m)) : Prop :=
  ∀ r ∈ S, ∀ r', Transition m r r' → r' ∈ S

/-- `r` is a **forcing state for `q`** if every candidate `N` in the class `r + 1` is
divisible by `q` and by no odd prime below `q`.  At such a state the capture of `q` is
compulsory: `minFac N = q`.

This is a congruence condition on `r` as soon as `RichEnough q m` holds (`q` and all
odd primes `< q` divide `m`). -/
def ForcingState (q m : ℕ) (r : ZMod m) : Prop :=
  ∀ N : ℕ, (N : ZMod m) = r + 1 →
    q ∣ N ∧ ∀ p : ℕ, Nat.Prime p → Odd p → p < q → ¬ p ∣ N

/-- `S` **blocks** `q` if it contains no forcing state for `q`. -/
def Blocks (q m : ℕ) (S : Set (ZMod m)) : Prop := ∀ r ∈ S, ¬ ForcingState q m r

/-- `S` **contains the orbit tail**. -/
def ContainsTail (m : ℕ) (S : Set (ZMod m)) : Prop :=
  ∃ N₀, ∀ n ≥ N₀, ((prod n : ℕ) : ZMod m) ∈ S

/-- A **Cox–van der Poorten obstruction**: a propagating set of residues containing the
orbit tail and blocking `q`.  This is the shape of every known omission certificate for
the max Euclid–Mullin sequence. -/
def CvdPObstruction (q m : ℕ) (S : Set (ZMod m)) : Prop :=
  Propagating m S ∧ Blocks q m S ∧ ContainsTail m S

/-- The modulus is **rich enough** for `q` if it sees `q` and every odd prime `< q`. -/
def RichEnough (q m : ℕ) : Prop :=
  q ∣ m ∧ ∀ p : ℕ, Nat.Prime p → Odd p → p < q → p ∣ m

/-- `M(q) = q · ∏_{odd p < q} p`, the minimal rich modulus. -/
def forcingModulus (q : ℕ) : ℕ :=
  q * ∏ p ∈ (Finset.range q).filter (fun p => Nat.Prime p ∧ Odd p), p

/-- `M(q) ∣ m` implies `RichEnough q m`. -/
theorem richEnough_of_forcingModulus_dvd {q m : ℕ} (h : forcingModulus q ∣ m) :
    RichEnough q m := by
  refine ⟨dvd_trans (dvd_mul_right q _) h, fun p hp hodd hlt => ?_⟩
  refine dvd_trans (dvd_trans ?_ (dvd_mul_left _ q)) h
  exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hp, hodd⟩)

/-- **Semantics of `ForcingState`**: at a forcing state the prime `q` really is
captured at the next step.  This is what makes `Blocks` the right notion of "the
certificate proves `q` never appears". -/
theorem forcingState_captures {q m : ℕ} (hq : Nat.Prime q) {n : ℕ}
    (hf : ForcingState q m ((prod n : ℕ) : ZMod m)) : seq (n + 1) = q := by
  have hcast : ((prod n + 1 : ℕ) : ZMod m) = ((prod n : ℕ) : ZMod m) + 1 := by push_cast; ring
  obtain ⟨hqd, hsmall⟩ := hf (prod n + 1) hcast
  -- the candidate is odd
  have h2 : (2 : ℕ) ∣ prod n := by
    have : seq 0 ∣ prod n := seq_dvd_prod 0 n (Nat.zero_le n)
    rwa [seq_zero] at this
  have hodd : ¬ (2 ∣ prod n + 1) := by omega
  have hge : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
  have hpr : Nat.Prime (Euclid.minFac (prod n + 1)) :=
    (isPrime_iff_natPrime _).mp (minFac_isPrime (prod n + 1) hge)
  have hdvd : Euclid.minFac (prod n + 1) ∣ prod n + 1 := minFac_dvd (prod n + 1) hge
  have hne2 : Euclid.minFac (prod n + 1) ≠ 2 := by
    intro h; exact hodd (h ▸ hdvd)
  have hle : Euclid.minFac (prod n + 1) ≤ q := minFac_min' _ q hge hq.two_le hqd
  have hgeq : q ≤ Euclid.minFac (prod n + 1) := by
    by_contra hcon
    exact hsmall _ hpr (hpr.odd_of_ne_two hne2) (by omega) hdvd
  rw [seq_succ]
  omega

/-! ## Part 4 (Step 3): Free states reach the full translated unit orbit -/

/-- **Step 3 (Free-state Fullness).**  From a free state `r` (i.e. `r + 1` is a unit
mod `m`) there is a transition to `r · s` for **every** unit `s`.

Construction: by Dirichlet pick a prime `π > 2` with `π ≡ s`, then a prime `M > π`
with `M ≡ (r+1)·s⁻¹` (a unit class, since `r+1` and `s` are units), and take
`N = π · M`.  Then `N ≡ r + 1`, `N` is odd, and `minFac N = π ≡ s`.

**Rule-symmetric.**  This lemma is *not* where min and max part company.  For `maxFac`
one is free to choose a different candidate: pick the prime `π ≡ (r+1)·s⁻¹` first and
then a prime `M > π` with `M ≡ s`; again `N = π·M ≡ r + 1`, and now `maxFac N = M ≡ s`.
So the reachable set is full under both rules.  (It is true, but irrelevant, that the
*particular* `N` used below yields `maxFac N = M`.)  The genuine break point is
`ForcingState`: see the module docstring. -/
theorem free_transition {m : ℕ} (hm : m ≠ 0) (r : ZMod m) (hr : IsUnit (r + 1))
    (s : (ZMod m)ˣ) : Transition m r (r * (s : ZMod m)) := by
  have : NeZero m := ⟨hm⟩
  obtain ⟨p₁, hp₁gt, hp₁prime, hp₁eq⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (a := (s : ZMod m)) s.isUnit 2
  obtain ⟨p₂, hp₂gt, hp₂prime, hp₂eq⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (a := (r + 1) * ((s⁻¹ : (ZMod m)ˣ) : ZMod m))
      (hr.mul (s⁻¹ : (ZMod m)ˣ).isUnit) p₁
  have hodd₁ : Odd p₁ := hp₁prime.odd_of_ne_two (by omega)
  have hodd₂ : Odd p₂ := hp₂prime.odd_of_ne_two (by omega)
  have hminfac : Nat.minFac (p₁ * p₂) = p₁ := minFac_mul_of_lt hp₁prime hp₂prime hp₂gt
  refine ⟨p₁ * p₂, hodd₁.mul hodd₂, ?_, ?_, ?_⟩
  · calc 3 ≤ p₁ := by omega
      _ ≤ p₁ * p₂ := Nat.le_mul_of_pos_right _ (by omega)
  · rw [Nat.cast_mul, hp₁eq, hp₂eq, ← mul_assoc, mul_comm ((s : ZMod m)) (r + 1),
      mul_assoc, Units.mul_inv, mul_one]
  · rw [hminfac, hp₁eq]

/-! ## Part 5 (Steps 4+5): The No-Invariant Theorem -/

/-- **No-Invariant Theorem.**  If `q` is a prime that never occurs in the (min)
Euclid–Mullin sequence, then for **every** modulus `m ≠ 0` rich enough to express the
capture condition for `q`, there is **no** CvdP obstruction for `q` modulo `m`.

Proof.  By `exists_tail_coprime` the tail is free forever, and by `ContainsTail` some
free tail state `r = Pₙ` lies in `S`.  By `free_transition` and `Propagating`, `S`
contains `r · s` for every unit `s`.  Choose, by CRT, a unit `s` with `s ≡ -Pₙ⁻¹`
mod `q` and `s ≡ 1` modulo every other prime factor of `m`.  Then `r·s + 1 ≡ 0 mod q`,
while for every odd prime `p < q` we get `r·s + 1 ≡ r + 1 ≢ 0 mod p` **by freeness** —
so the A/B split is not even needed at this stage.  Thus `r · s ∈ S` is a forcing
state, contradicting `Blocks`.

No parity hypothesis on `m` is required: the odd part and the (frozen) 2-part are
handled uniformly, because the candidate `N = π·M` is automatically odd and its class
mod `m` — including its class mod `2^a` — is prescribed by Dirichlet. -/
theorem no_cvdp_obstruction {q m : ℕ} (hq : q ∈ MissingPrimes) (hm : m ≠ 0)
    (hrich : RichEnough q m) (S : Set (ZMod m)) : ¬ CvdPObstruction q m S := by
  rintro ⟨hprop, hblock, N₁, htail⟩
  have : NeZero m := ⟨hm⟩
  have hqp : Nat.Prime q := hq.1
  have : NeZero q := ⟨hqp.pos.ne'⟩
  have : Fact (Nat.Prime q) := ⟨hqp⟩
  obtain ⟨N₀, hfree⟩ := exists_tail_coprime m hm
  set n := max N₀ N₁ with hn
  have hcop : Nat.Coprime (prod n + 1) m := hfree n (le_max_left _ _)
  have hmem : ((prod n : ℕ) : ZMod m) ∈ S := htail n (le_max_right _ _)
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
  -- S contains the translated state
  have htrans := free_transition hm ((prod n : ℕ) : ZMod m) hunit (ZMod.unitOfCoprime s hsm)
  have hmem2 : ((prod n : ℕ) : ZMod m) * ((s : ℕ) : ZMod m) ∈ S := by
    have h := hprop _ hmem _ htrans
    rwa [ZMod.coe_unitOfCoprime] at h
  -- and it is a forcing state, contradicting Blocks
  refine hblock _ hmem2 ?_
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

/-- **Step 5 (even part).**  Specialisation to a modulus with a nontrivial 2-part.
The frozen 2-adic data of the min sequence (`Pₙ ≡ 2 mod 4`, candidate `≡ 3 mod 4`)
blocks nothing: for every odd `q`, "`q ∣ N` and `N ≡ 3 (mod 4)`" is satisfiable, and
our Dirichlet construction realises it automatically since the candidate class is
prescribed modulo the full modulus.

Contrast with max: there the appearance condition for `5` is `N = 5^c`, forcing
`N ≡ 1 (mod 4)`, which the frozen `3 mod 4` kills.  **That is the dichotomy.** -/
theorem no_cvdp_obstruction_two_part {q a m₀ : ℕ} (hq : q ∈ MissingPrimes) (hm₀ : m₀ ≠ 0)
    (hrich : RichEnough q (2 ^ a * m₀)) (S : Set (ZMod (2 ^ a * m₀))) :
    ¬ CvdPObstruction q (2 ^ a * m₀) S :=
  no_cvdp_obstruction hq (by positivity) hrich S

/-! ## Part 6 (Step A1): The Lifting Lemma

An invariant modulo `m` pulls back along the projection `ZMod m' → ZMod m` whenever
`m ∣ m'`.  Propagation and tail-containment always lift.

CAVEAT (recorded honestly): the *forcing* form of `Blocks` does **not** lift, because
`ForcingState q m'` is a weaker condition than `ForcingState q m` on the projected
state (the residue class mod `m'` is smaller, so quantifying over it is weaker).  What
does lift is the stronger *death-avoiding* form `BlocksDeath` (`S` avoids `r+1 ≡ 0`
mod `q` altogether), which implies `Blocks`.  This is why the main theorem takes
`RichEnough q m` as a hypothesis rather than deriving it by lifting. -/

/-- Preimage of a residue set along the projection `ZMod m' → ZMod m`. -/
def liftSet {m m' : ℕ} (h : m ∣ m') (S : Set (ZMod m)) : Set (ZMod m') :=
  (ZMod.castHom h (ZMod m)) ⁻¹' S

/-- Propagation lifts. -/
theorem propagating_lift {m m' : ℕ} (h : m ∣ m') {S : Set (ZMod m)}
    (hS : Propagating m S) : Propagating m' (liftSet h S) := by
  rintro r hr r' ⟨N, hodd, h3, hcast, hmul⟩
  refine hS _ hr _ ⟨N, hodd, h3, ?_, ?_⟩
  · have := congrArg (ZMod.castHom h (ZMod m)) hcast
    rwa [map_natCast, map_add, map_one] at this
  · have := congrArg (ZMod.castHom h (ZMod m)) hmul
    rwa [map_mul, map_natCast] at this

/-- Tail containment lifts. -/
theorem containsTail_lift {m m' : ℕ} (h : m ∣ m') {S : Set (ZMod m)}
    (hS : ContainsTail m S) : ContainsTail m' (liftSet h S) := by
  obtain ⟨N₀, hN₀⟩ := hS
  refine ⟨N₀, fun n hn => ?_⟩
  show (ZMod.castHom h (ZMod m)) ((prod n : ℕ) : ZMod m') ∈ S
  rw [map_natCast]
  exact hN₀ n hn

/-- The strong, *death-avoiding* form of blocking: `S` contains no state whose
successor class is divisible by `q` at all. -/
def BlocksDeath (q m : ℕ) (S : Set (ZMod m)) : Prop :=
  ∀ r ∈ S, ∀ N : ℕ, (N : ZMod m) = r + 1 → ¬ q ∣ N

/-- Every residue class mod `m ≠ 0` contains a natural number, so `ForcingState` is
never vacuously true. -/
theorem exists_nat_in_class {m : ℕ} (hm : m ≠ 0) (r : ZMod m) :
    ∃ N : ℕ, (N : ZMod m) = r := by
  have : NeZero m := ⟨hm⟩
  exact ⟨r.val, ZMod.natCast_rightInverse r⟩

/-- Death-avoidance is stronger than blocking. -/
theorem blocks_of_blocksDeath {q m : ℕ} (hm : m ≠ 0) {S : Set (ZMod m)}
    (hS : BlocksDeath q m S) : Blocks q m S := by
  intro r hr hf
  obtain ⟨N, hN⟩ := exists_nat_in_class hm (r + 1)
  exact hS r hr N hN (hf N hN).1

/-- Death-avoidance lifts. -/
theorem blocksDeath_lift {q m m' : ℕ} (h : m ∣ m') {S : Set (ZMod m)}
    (hS : BlocksDeath q m S) : BlocksDeath q m' (liftSet h S) := by
  intro r hr N hN
  refine hS _ hr N ?_
  have := congrArg (ZMod.castHom h (ZMod m)) hN
  rwa [map_natCast, map_add, map_one] at this

/-- **Lifting Lemma (A1).**  A death-avoiding obstruction modulo `m` lifts to one
modulo any multiple `m'`; in particular one may always assume `RichEnough q m`. -/
theorem cvdpObstruction_lift {q m m' : ℕ} (h : m ∣ m') {S : Set (ZMod m)}
    (hprop : Propagating m S) (hdeath : BlocksDeath q m S) (htail : ContainsTail m S)
    (hm' : m' ≠ 0) :
    CvdPObstruction q m' (liftSet h S) :=
  ⟨propagating_lift h hprop, blocks_of_blocksDeath hm' (blocksDeath_lift h hdeath),
    containsTail_lift h htail⟩

/-! ## Part 6b: Covering families are already covered

`no_cvdp_obstruction` kills an obstruction at a *single* modulus.  A referee may
reasonably ask whether an Erdős **covering-system** style certificate — a whole
*family* `(mᵢ, Sᵢ)` of congruence obstructions, no one of which need work alone —
escapes.  It does not, for two independent reasons.

1. **Set-genericity.**  `no_cvdp_obstruction` quantifies over `∀ S : Set (ZMod m)` with
   no structural hypothesis whatsoever.  A *finite* family assembles at any common
   multiple `M` of the `mᵢ` (in practice `M = lcm(mᵢ) · forcingModulus q`, to get
   `RichEnough q M`) as the single set `S = ⋃ i, liftSet (hdvd i) (Sᵢ)`.  Propagation
   and tail-containment survive both the lift (`propagating_lift`, `containsTail_lift`)
   and the union (`propagating_iUnion`, `containsTail_iUnion`), so the assembled object
   is a bona fide candidate obstruction at the single modulus `M` — and
   `no_cvdp_obstruction` refutes it.

   Honest caveat: `Blocks` itself does **not** lift (only `BlocksDeath` does; see the
   caveat in Part 6).  But coarse-modulus blocking does not *certify* omission anyway:
   the candidate's class modulo `M` is finer than its class modulo `mᵢ`, so a valid
   congruential certificate must block at `M`.  The situation is therefore "unsound",
   not "uncovered": a family that only blocks at each `mᵢ` proves nothing, and a family
   that does block at `M` is refuted.

2. **Covering by small primes is unconditionally impossible.**  Covering systems are
   finite by definition, so a Sierpiński-style obstruction would need a fixed finite
   set `T` of primes with some `p ∈ T` dividing `Pₙ + 1` for *every* `n`.
   `no_finite_prime_covering` rules this out in one line from `exists_tail_coprime`.

**Scope statement.**  Together with `no_cvdp_obstruction`, this kills every obstruction
expressible as a congruence condition at *some finite* modulus.  Two escapes remain,
and we do not claim otherwise: (i) families with **unbounded** moduli, which have no
finite lcm and are genuinely profinite/adelic objects; and (ii) **non-congruence**
(anatomy) invariants — of which the eventually-prime branch is the known live example,
and smoothness, the max-side mechanism, is the archetype. -/

/-- No finite set of primes can cover the candidates: for any finite set `T` of primes,
all sufficiently late candidates `Pₙ + 1` are coprime to every element of `T`.

This single lemma disposes of the entire Sierpiński/covering-system class of
obstructions, which by definition uses only finitely many moduli. -/
theorem no_finite_prime_covering (T : Finset ℕ) (hT : ∀ p ∈ T, Nat.Prime p) :
    ∃ N₀, ∀ n, N₀ ≤ n → ∀ p ∈ T, ¬ (p ∣ prod n + 1) := by
  have hm0 : (∏ p ∈ T, p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp => (hT p hp).pos.ne'
  obtain ⟨N₀, hN₀⟩ := exists_tail_coprime _ hm0
  refine ⟨N₀, fun n hn p hp hdvd => ?_⟩
  have hpm : p ∣ ∏ p ∈ T, p := Finset.dvd_prod_of_mem _ hp
  have hd1 : p ∣ 1 := (hN₀ n hn) ▸ Nat.dvd_gcd hdvd hpm
  have := (hT p hp).one_lt
  have := Nat.dvd_one.mp hd1
  omega

/-- Propagation survives arbitrary unions. -/
theorem propagating_iUnion {m : ℕ} {ι : Sort*} {S : ι → Set (ZMod m)}
    (hS : ∀ i, Propagating m (S i)) : Propagating m (⋃ i, S i) := by
  rintro r hr r' htr
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hr
  exact Set.mem_iUnion.mpr ⟨i, hS i r hi r' htr⟩

/-- Tail containment survives arbitrary unions: one member suffices. -/
theorem containsTail_iUnion {m : ℕ} {ι : Sort*} {S : ι → Set (ZMod m)} (i : ι)
    (hS : ContainsTail m (S i)) : ContainsTail m (⋃ j, S j) := by
  obtain ⟨N₀, hN₀⟩ := hS
  exact ⟨N₀, fun n hn => Set.mem_iUnion.mpr ⟨i, hN₀ n hn⟩⟩

/-- Assembling a covering family at a common multiple `M`: the union of the lifted
member sets is propagating, and it contains the orbit tail as soon as one member
does. -/
theorem covering_family_assembles {ι : Sort*} {m : ι → ℕ} {M : ℕ}
    (hdvd : ∀ i, m i ∣ M) {S : ∀ i, Set (ZMod (m i))}
    (hprop : ∀ i, Propagating (m i) (S i)) {i₀ : ι} (htail : ContainsTail (m i₀) (S i₀)) :
    Propagating M (⋃ i, liftSet (hdvd i) (S i)) ∧
      ContainsTail M (⋃ i, liftSet (hdvd i) (S i)) :=
  ⟨propagating_iUnion fun i => propagating_lift (hdvd i) (hprop i),
    containsTail_iUnion i₀ (containsTail_lift (hdvd i₀) htail)⟩

/-- **A finite covering family of congruence obstructions needs no separate treatment.**
Assembling the family at a common multiple `M` produces a single set of residues at the
single modulus `M`, and `no_cvdp_obstruction` — which is *set-generic*, imposing no
structural hypothesis on `S` — already refutes it.

The proof really is `no_cvdp_obstruction hq hM hrich _`, and that is the point: the
content here is the *observation* that covering families are not a new phenomenon, and
the lemma exists to make that explicit and referee-proof.  See `covering_family_assembles`
for the fact that the assembled union is a legitimate candidate obstruction (propagating,
tail-containing), and the Part 6b docstring for the honest scope statement. -/
theorem no_covering_family_obstruction {q : ℕ} (hq : q ∈ MissingPrimes)
    {ι : Type*} [Fintype ι] (m : ι → ℕ) (S : ∀ i, Set (ZMod (m i)))
    (M : ℕ) (hM : M ≠ 0) (hdvd : ∀ i, m i ∣ M) (hrich : RichEnough q M) :
    ¬ CvdPObstruction q M (⋃ i, liftSet (hdvd i) (S i)) :=
  no_cvdp_obstruction hq hM hrich _

/-! ## Part 7 (A7): `IC_min` and the reduction to Mullin's Conjecture -/

/-- **`IC_min` (Invariant Certificate hypothesis for the min sequence).**

*If a prime `q` never occurs in the first Euclid–Mullin sequence, then its omission is
certified by a propagating congruence invariant.*

This is the exact analogue of what is TRUE for the max sequence (Cox–van der Poorten,
Booker).  By `no_cvdp_obstruction` it is equivalent to Mullin's Conjecture — i.e. the
min sequence admits no congruence certificate of omission whatsoever. -/
def IC_min : Prop :=
  ∀ q : ℕ, q ∈ MissingPrimes →
    ∃ m : ℕ, m ≠ 0 ∧ RichEnough q m ∧ ∃ S : Set (ZMod m), CvdPObstruction q m S

/-- **`IC_min → MullinConjecture`.**  All the content is in `no_cvdp_obstruction`. -/
theorem ic_min_implies_mullin (h : IC_min) : MullinConjecture := by
  intro p hp
  by_contra hcon
  have hmiss : p ∈ MissingPrimes := ⟨(isPrime_iff_natPrime p).mp hp, fun k hk => hcon ⟨k, hk⟩⟩
  obtain ⟨m, hm, hrich, S, hS⟩ := h p hmiss
  exact no_cvdp_obstruction hmiss hm hrich S hS

/-- Conversely Mullin's Conjecture makes `IC_min` vacuously true, so `IC_min` is in
fact *equivalent* to `MullinConjecture`: the congruence-certificate route is neither
stronger nor weaker, it is exactly the conjecture. -/
theorem mullin_implies_ic_min (h : MullinConjecture) : IC_min := by
  intro q hq
  obtain ⟨n, hn⟩ := h q ((isPrime_iff_natPrime q).mpr hq.1)
  exact absurd hn (hq.2 n)

/-! ## Part 8: Position in the reduction network

`IC_min` is *equivalent* to `MullinConjecture` (`mullin_implies_ic_min` +
`ic_min_implies_mullin`), hence it sits at the **top** of the reduction network,
strictly above `DynamicalHitting` and `SingleHitHypothesis`.  It is therefore NOT a new
weakening of MC and gives no new route to a proof.

Its value is the **no-go content** carried by `no_cvdp_obstruction`: the entire class of
Cox–van der Poorten style certificates — the only mechanism by which omission has ever
been *proved*, for the max sequence — is unavailable for the min sequence, at every
modulus, odd or even.  Any disproof of Mullin's Conjecture must therefore be
non-congruential. -/

/-- `SingleHitHypothesis` (hence `DynamicalHitting`) makes `IC_min` vacuously true. -/
theorem singleHit_implies_ic_min (h : SingleHitHypothesis) : IC_min :=
  mullin_implies_ic_min (single_hit_implies_mc h)

/-- `DynamicalHitting` makes `IC_min` vacuously true. -/
theorem dynamicalHitting_implies_ic_min (h : DynamicalHitting) : IC_min :=
  singleHit_implies_ic_min (dh_implies_single_hit h)

/-- Placement of `IC_min` in the reduction network. -/
theorem ic_min_network :
    (DynamicalHitting → IC_min) ∧ (SingleHitHypothesis → IC_min) ∧
      (IC_min ↔ MullinConjecture) :=
  ⟨dynamicalHitting_implies_ic_min, singleHit_implies_ic_min,
    ⟨ic_min_implies_mullin, mullin_implies_ic_min⟩⟩

/-! ## Part 8: Arbitrarily large candidates

Everything above is size-blind: `Transition` and `ForcingState` quantify over candidates
`N` in a residue class with no lower bound on `N`.  The two lemmas here supply candidates
*above any prescribed bound*, which is what lets the no-go results extend to invariant
families allowed to use the size of `Pₙ` — Dirichlet hands out arbitrarily large primes,
so an archimedean lower bound on the candidate costs the argument nothing.

The upper direction is genuinely different and is NOT covered: a fragment constraining
`N` to be `y`-smooth, or bounding its largest prime factor, escapes both constructions
(the cofactors below are huge primes).  That is the boundary recorded in
`docs/analysis/reciprocity_invariants.md` §6 and as the anatomy facet of Dead End #146. -/

/-- **Free-state fullness, with a size bound.**  `free_transition` with the candidate
taken above any prescribed `B`: choose the prime `π ≡ s` above `B` rather than above `2`.
The transition it witnesses is the same, `r → r · s`. -/
theorem free_transition_large {m : ℕ} (hm : m ≠ 0) (r : ZMod m) (hr : IsUnit (r + 1))
    (s : (ZMod m)ˣ) (B : ℕ) :
    ∃ N : ℕ, B < N ∧ Odd N ∧ 3 ≤ N ∧ (N : ZMod m) = r + 1 ∧
      ((Nat.minFac N : ℕ) : ZMod m) = (s : ZMod m) := by
  have : NeZero m := ⟨hm⟩
  obtain ⟨p₁, hp₁gt, hp₁prime, hp₁eq⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (a := (s : ZMod m)) s.isUnit (B + 2)
  obtain ⟨p₂, hp₂gt, hp₂prime, hp₂eq⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (a := (r + 1) * ((s⁻¹ : (ZMod m)ˣ) : ZMod m))
      (hr.mul (s⁻¹ : (ZMod m)ˣ).isUnit) p₁
  have hodd₁ : Odd p₁ := hp₁prime.odd_of_ne_two (by omega)
  have hodd₂ : Odd p₂ := hp₂prime.odd_of_ne_two (by omega)
  have hminfac : Nat.minFac (p₁ * p₂) = p₁ := minFac_mul_of_lt hp₁prime hp₂prime hp₂gt
  have hp₂pos : 0 < p₂ := by omega
  have hle : p₁ ≤ p₁ * p₂ := Nat.le_mul_of_pos_right _ hp₂pos
  refine ⟨p₁ * p₂, by omega, hodd₁.mul hodd₂, by omega, ?_, ?_⟩
  · rw [Nat.cast_mul, hp₁eq, hp₂eq, ← mul_assoc, mul_comm ((s : ZMod m)) (r + 1),
      mul_assoc, Units.mul_inv, mul_one]
  · rw [hminfac, hp₁eq]

/-- **Arbitrarily large odd representatives.**  For an odd modulus `m`, every residue
class contains odd naturals above any prescribed bound: add a suitable multiple of `m`,
choosing its parity to make the result odd (possible exactly because `m` is odd).

This is the size-bounded form of the representative chosen in
`CongruenceInductionProof.toCertificate`, and it is what lets the `avoid` clause of a
size-guarded fragment still be reached. -/
theorem exists_large_odd_in_class {m : ℕ} (hmodd : Odd m) (r : ZMod m) (B : ℕ) :
    ∃ N : ℕ, B < N ∧ Odd N ∧ 3 ≤ N ∧ (N : ZMod m) = r := by
  have hmm : m % 2 = 1 := Nat.odd_iff.mp hmodd
  have hm : m ≠ 0 := by omega
  have hm1 : 1 ≤ m := by omega
  obtain ⟨N₁, hN₁⟩ := exists_nat_in_class hm r
  set j : ℕ := B + 3 with hj
  set t : ℕ := j * m with ht
  have ht1 : j ≤ t := by
    calc j = j * 1 := (Nat.mul_one j).symm
      _ ≤ j * m := Nat.mul_le_mul_left j hm1
  have hcast : ∀ k : ℕ, ((N₁ + k * m : ℕ) : ZMod m) = r := by
    intro k
    push_cast [ZMod.natCast_self]
    simp [hN₁]
  rcases Nat.even_or_odd (N₁ + 2 * t) with he | ho
  · have hev : (N₁ + 2 * t) % 2 = 0 := Nat.even_iff.mp he
    refine ⟨N₁ + 2 * t + m, by omega, Nat.odd_iff.mpr (by omega), by omega, ?_⟩
    have heq : N₁ + 2 * t + m = N₁ + (2 * j + 1) * m := by rw [ht]; ring
    rw [heq]; exact hcast _
  · refine ⟨N₁ + 2 * t, by omega, ho, by omega, ?_⟩
    have heq : N₁ + 2 * t = N₁ + (2 * j) * m := by rw [ht]; ring
    rw [heq]; exact hcast _

/-! ## Part 9: Candidates with many prime factors

The size guards of Part 8 are one anatomy dimension; the number of prime factors is
another.  It also costs the argument nothing, for a reason worth isolating: **multiplying
by a prime `p ≡ 1 (mod m)` changes neither the residue class nor the least factor**
(when `p` is taken larger than the number itself), while raising `ω` by one.  Dirichlet
supplies such primes above any bound, so `ω` can be pushed as high as one likes without
disturbing anything the congruence machinery sees.

Consequently a fragment allowed to assume `ω(N) ≥ K` — however large `K` — is no harder
to kill than the unguarded one.  The `ω` axis is *not* the surviving part of anatomy.
What survives is the **opposite** direction: the primes supplied here are huge, so a
fragment demanding that `N` be `y`-smooth, or bounding its largest prime factor, is not
reached by any of these constructions.  Smoothness, not `ω`, is the boundary. -/

/-- **Raising `ω` for free.**  Any odd `N ≥ 3` can be multiplied up to a `Q` in the same
residue class mod `m`, still odd, with the same least prime factor, at least as large,
and with at least `k` prime factors.

The multipliers are primes `≡ 1 (mod m)` chosen above the current value, so: the class is
unchanged (`p·Q ≡ 1·Q`), the least factor is unchanged (the new primes are larger than
`Q`, hence than `minFac Q`), and each multiplication adds a genuinely new prime factor. -/
theorem exists_class_omega {m : ℕ} (hm : m ≠ 0) {N : ℕ} (h3 : 3 ≤ N) (hodd : Odd N) :
    ∀ k : ℕ, ∃ Q : ℕ, (Q : ZMod m) = (N : ZMod m) ∧ Odd Q ∧ N ≤ Q ∧
      Nat.minFac Q = Nat.minFac N ∧ k ≤ Q.primeFactors.card := by
  have : NeZero m := ⟨hm⟩
  intro k
  induction k with
  | zero => exact ⟨N, rfl, hodd, le_rfl, rfl, Nat.zero_le _⟩
  | succ k ih =>
    obtain ⟨Q, hQclass, hQodd, hQle, hQmf, hQcard⟩ := ih
    have hQ3 : 3 ≤ Q := le_trans h3 hQle
    have hQpos : 0 < Q := by omega
    -- a prime `p ≡ 1 (mod m)` above `Q`
    obtain ⟨p, hpgt, hpprime, hpeq⟩ :=
      Nat.forall_exists_prime_gt_and_eq_mod (a := (1 : ZMod m)) isUnit_one (Q + 2)
    have hp2 : 2 < p := by omega
    have hpQ : Q < p := by omega
    have hppos : 0 < p := by omega
    refine ⟨p * Q, ?_, (hpprime.odd_of_ne_two (by omega)).mul hQodd, ?_, ?_, ?_⟩
    · rw [Nat.cast_mul, hpeq, one_mul]; exact hQclass
    · calc N ≤ Q := hQle
        _ ≤ p * Q := Nat.le_mul_of_pos_left _ hppos
    · -- the least factor is unchanged: every new prime factor exceeds `Q`
      have hmfQ : Nat.minFac Q ≤ Q := Nat.minFac_le hQpos
      have hmfQ2 : 2 ≤ Nat.minFac Q := (Nat.minFac_prime (by omega)).two_le
      have hdvd : Nat.minFac (p * Q) ∣ p * Q := Nat.minFac_dvd _
      have hne1 : p * Q ≠ 1 := by
        have : 3 ≤ p * Q := le_trans hQ3 (Nat.le_mul_of_pos_left _ hppos)
        omega
      have hpr : (Nat.minFac (p * Q)).Prime := Nat.minFac_prime hne1
      have hle : Nat.minFac (p * Q) ≤ Nat.minFac Q :=
        Nat.minFac_le_of_dvd hmfQ2 (Dvd.dvd.mul_left (Nat.minFac_dvd Q) p)
      rw [← hQmf]
      rcases (Nat.Prime.dvd_mul hpr).mp hdvd with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hpr hpprime).mp h ▸ hle) (by omega)
      · exact le_antisymm hle (Nat.minFac_le_of_dvd hpr.two_le h)
    · -- one new prime factor
      have hunion : (p * Q).primeFactors = {p} ∪ Q.primeFactors := by
        rw [Nat.primeFactors_mul (by omega) (by omega), hpprime.primeFactors]
      have hnotmem : p ∉ Q.primeFactors := by
        intro hmem
        exact absurd (Nat.le_of_dvd hQpos (Nat.dvd_of_mem_primeFactors hmem)) (by omega)
      rw [hunion, Finset.singleton_union, Finset.card_insert_of_notMem hnotmem]
      omega

/-- `free_transition_large`, additionally with as many prime factors as required. -/
theorem free_transition_omega {m : ℕ} (hm : m ≠ 0) (r : ZMod m) (hr : IsUnit (r + 1))
    (s : (ZMod m)ˣ) (B k : ℕ) :
    ∃ N : ℕ, B < N ∧ Odd N ∧ 3 ≤ N ∧ (N : ZMod m) = r + 1 ∧
      ((Nat.minFac N : ℕ) : ZMod m) = (s : ZMod m) ∧ k ≤ N.primeFactors.card := by
  obtain ⟨N, hNgt, hNodd, hN3, hNcast, hNmf⟩ := free_transition_large hm r hr s B
  obtain ⟨Q, hQclass, hQodd, hQle, hQmf, hQcard⟩ := exists_class_omega hm hN3 hNodd k
  exact ⟨Q, by omega, hQodd, by omega, by rw [hQclass]; exact hNcast,
    by rw [hQmf]; exact hNmf, hQcard⟩

/-- `exists_large_odd_in_class`, additionally with as many prime factors as required. -/
theorem exists_large_odd_in_class_omega {m : ℕ} (hmodd : Odd m) (r : ZMod m) (B k : ℕ) :
    ∃ N : ℕ, B < N ∧ Odd N ∧ 3 ≤ N ∧ (N : ZMod m) = r ∧ k ≤ N.primeFactors.card := by
  have hm : m ≠ 0 := by have := Nat.odd_iff.mp hmodd; omega
  obtain ⟨N, hNgt, hNodd, hN3, hNcast⟩ := exists_large_odd_in_class hmodd r B
  obtain ⟨Q, hQclass, hQodd, hQle, _, hQcard⟩ := exists_class_omega hm hN3 hNodd k
  exact ⟨Q, by omega, hQodd, by omega, by rw [hQclass]; exact hNcast, hQcard⟩

/-! ## Part 10: The orbit is eventually rough — smoothness guards are inadmissible

Parts 8 and 9 showed that guards bounding the candidate from *below* (in size, or in
number of prime factors) cost the killing argument nothing.  The one axis they left open
is the opposite direction: a guard demanding that the candidate be `y`-smooth, or bounding
its largest prime factor.  That axis closes here, and for a reason that has nothing to do
with the constructions of Parts 8--9: **the orbit's own candidates violate every fixed
smoothness guard.**

`no_finite_prime_covering` says that any finite set of primes eventually stops dividing
the Euclid numbers---each prime either enters the accumulator or has a finite hitting set.
Applied to the primes below `y`, it says `Pₙ + 1` is eventually `y`-rough, hence *all* of
its prime factors exceed `y`.  A fragment that only undertakes to handle `y`-smooth
candidates therefore excludes the orbit's own candidates from some point on, and proves
nothing about the orbit. -/

/-- **The Euclid numbers are eventually `y`-rough**, for every `y`: past some stage, every
prime factor of `Pₙ + 1` exceeds `y`. -/
theorem eventually_rough (y : ℕ) :
    ∃ N₀, ∀ n ≥ N₀, ∀ p : ℕ, Nat.Prime p → p ∣ (prod n + 1) → y < p := by
  obtain ⟨N₀, hN₀⟩ :=
    no_finite_prime_covering ((Finset.range (y + 1)).filter Nat.Prime)
      (fun p hp => (Finset.mem_filter.mp hp).2)
  refine ⟨N₀, fun n hn p hp hdvd => ?_⟩
  by_contra hle
  exact hN₀ n hn p (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩) hdvd

/-- The largest prime factor of the Euclid number eventually exceeds any bound. -/
theorem eventually_largePrimeFactor (y : ℕ) :
    ∃ N₀, ∀ n ≥ N₀, ∃ p : ℕ, Nat.Prime p ∧ p ∣ (prod n + 1) ∧ y < p := by
  obtain ⟨N₀, hN₀⟩ := eventually_rough y
  refine ⟨N₀, fun n hn => ?_⟩
  have h3 : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
  have hne : prod n + 1 ≠ 1 := by omega
  exact ⟨Nat.minFac _, Nat.minFac_prime hne, Nat.minFac_dvd _,
    hN₀ n hn _ (Nat.minFac_prime hne) (Nat.minFac_dvd _)⟩

/-- **Fixed smoothness guards are inadmissible.**  There is no threshold `y` and no stage
past which the Euclid numbers are `y`-smooth.  Consequently a proof fragment that
undertakes to handle only `y`-smooth candidates says nothing about the orbit: the
soundness contract, which requires the orbit's own candidate to satisfy the guard, cannot
be met.

This is the exact complement of Parts 8--9.  There, guards bounding the candidate from
below were free because Dirichlet supplies arbitrarily large primes.  Here, the guard
bounding it from above is unusable because the orbit refuses to be smooth. -/
theorem smooth_guard_inadmissible (y : ℕ) :
    ¬ ∃ T, ∀ n ≥ T, ∀ p : ℕ, Nat.Prime p → p ∣ (prod n + 1) → p ≤ y := by
  rintro ⟨T, hT⟩
  obtain ⟨N₀, hN₀⟩ := eventually_rough y
  set n := max T N₀ with hn
  have h3 : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
  have hne : prod n + 1 ≠ 1 := by omega
  have hp : Nat.Prime (Nat.minFac (prod n + 1)) := Nat.minFac_prime hne
  have hdvd : Nat.minFac (prod n + 1) ∣ prod n + 1 := Nat.minFac_dvd _
  have hle := hT n (le_max_left _ _) _ hp hdvd
  have hgt := hN₀ n (le_max_right _ _) _ hp hdvd
  omega

/-- The landscape of this file, as one statement. -/
theorem no_invariant_landscape :
    (∀ q : ℕ, q ∈ MissingPrimes → (HittingSet q).Finite) ∧
    (∀ m : ℕ, m ≠ 0 → ∃ N₀, ∀ n ≥ N₀, Nat.Coprime (prod n + 1) m) ∧
    (∀ (m : ℕ), m ≠ 0 → ∀ (r : ZMod m), IsUnit (r + 1) → ∀ s : (ZMod m)ˣ,
      Transition m r (r * (s : ZMod m))) ∧
    (∀ q m : ℕ, q ∈ MissingPrimes → m ≠ 0 → RichEnough q m →
      ∀ S : Set (ZMod m), ¬ CvdPObstruction q m S) ∧
    (∀ T : Finset ℕ, (∀ p ∈ T, Nat.Prime p) →
      ∃ N₀, ∀ n, N₀ ≤ n → ∀ p ∈ T, ¬ (p ∣ prod n + 1)) ∧
    (IC_min ↔ MullinConjecture) :=
  ⟨fun _ hq => hittingSet_finite hq, fun m hm => exists_tail_coprime m hm,
    fun _ hm r hr s => free_transition hm r hr s,
    fun _ _ hq hm hrich S => no_cvdp_obstruction hq hm hrich S,
    fun T hT => no_finite_prime_covering T hT,
    ⟨ic_min_implies_mullin, mullin_implies_ic_min⟩⟩

end CvdP
