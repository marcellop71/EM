import EM.Population.HittingSetStructure
import EM.FunctionField.AutonomousMap
import Mathlib.NumberTheory.Bertrand

/-!
# The Autonomous Branch: a Conditional Failure Mode for Mullin's Conjecture

This file transports the *autonomous map* obstruction of
`EM/FunctionField/AutonomousMap.lean` from the function-field analogue back to the
integers, producing what is — as far as this project is concerned — the first
**concrete, internally consistent mechanism by which Mullin's Conjecture could fail**.

## The mechanism

Suppose **Perpetual Primality** (ω1) holds from some step `N₁` on:

  `∀ n ≥ N₁, Nat.Prime (prod n + 1)`.

Then `minFac (prod n + 1) = prod n + 1`, so `seq (n+1) = prod n + 1` and the
accumulator recurrence degenerates to

  `prod (n+1) = prod n * (prod n + 1)`.

Reducing mod a prime `q` and writing `W n = walkZ q n`, the walk becomes
**autonomous** — its next value depends only on its current value:

  `W (n+1) = W n * (W n + 1) = ffAutonomousMap q (W n)`.

Now `W (n+1) = -1` iff `W n ^ 2 + W n + 1 = 0`, i.e. iff `Φ₃` has a root mod `q`.
By `FunctionFieldAnalog.phi3_no_roots`, for `q ≡ 2 (mod 3)` and `q ≥ 5` there is no
such root: a root would be a unit of multiplicative order `3`, forcing `3 ∣ q - 1`,
which contradicts `q ≡ 2 (mod 3)`.

Hence for every prime `q ≡ 2 (mod 3)`, `q ≥ 5`, which has not yet appeared and does
not already divide `prod N₁ + 1`, we get `q ∤ prod n + 1` for **all** `n ≥ N₁`, so `q`
is missing forever. The primes `q ≡ 2 (mod 3)` have natural density `1/2` among all
primes, so on this branch Mullin's Conjecture fails on a density-`1/2` set.

## Significance

* This is the first **concrete, consistent mechanism** by which MC could fail,
  transported from the function-field setting to the integers. It is *conditional* on
  (ω1), which is itself wildly implausible, but it is not self-contradictory: nothing in
  the current infrastructure rules it out.

* The mechanism is **invisible to congruence obstructions**, which is exactly what the
  No-Invariant Theorem (`CvdP.no_cvdp_obstruction`) predicts. `CvdP.Transition`
  deliberately over-approximates the true dynamics: it admits composite candidates
  `N = π · M`, and `free_transition` exploits precisely that freedom. The autonomous
  tail `{w ↦ w * (w+1)}` is therefore *not* a propagating set for `CvdP.Transition`, so
  no congruential invariant can see it. This instantiates the remark of
  `EM/Obstruction/NoInvariant.lean` Part 8 that any disproof of MC must be
  non-congruential.

* On this branch the *consumption receptacle* is vacuous: `ω(prod n + 1) - 1 = 0`, i.e.
  each Euclid candidate is prime and the orbit "spends" nothing. Detection and Gap fail
  together, which is why receptacle-style arguments cannot rule the branch out.

* Consequently `InfinitelyManyComposite` (C∞) — infinitely many Euclid candidates are
  composite — is elevated to a **named open hypothesis gating this failure mode**: it is
  the exact negation of (ω1) holding from any step.

## Two routes to the refutation

There are two independent arguments here, and they say different things.

* **Bertrand route** (`eventually_prime_implies_not_mullin`): perpetual primality from
  *any* threshold refutes MC outright, with no side conditions. Under (ω1) the primes
  ever appearing lie in `{d : d ∣ prod T} ∪ {prod n + 1 : n ≥ T}`, and the candidate
  values leap from `prod T + 1` past `2 * (prod T + 1)`; Bertrand's postulate supplies a
  prime in the gap. Clean, but non-constructive about *which* primes are lost.

* **Φ₃ / mod-3 route** (`perpetual_primality_excludes_two_mod_three`): identifies
  *exactly which* primes are excluded — every `q ≡ 2 (mod 3)`, `q ≥ 5`, that is fresh and
  not at `-1` at step `N₁`, a set of natural density `1/2` among the primes. This is the
  mathematically informative content, and it is the part that transports the
  function-field picture (`EM/FunctionField/AutonomousMap.lean`) to `ℤ`.

## Relation to existing perpetual-primality infrastructure

`EM/Stochastic/EpsilonRandomMC.lean` already contains `perpetual_prime_recurrence`,
`perpetual_prime_cyclotomic` and `perpetual_prime_excludes_mod3_one`. Those are stated
for the **mixed** walk `mixedWalkProd acc minFacMixed`, and they prove a constraint on
the *walk's own residue* (it never sits at `1 mod 3`, since `Φ₃(P)` would then be
divisible by `3` and composite). They exclude **no prime from the sequence**. The results
here are for the **standard** `prod`/`seq`, and their conclusion is missingness of
primes, hence a refutation of MC. So the two developments are disjoint in content.

## Main results

* `PerpetualPrimality`, `InfinitelyManyComposite` — the two hypotheses.
* `perpetual_seq_succ`, `perpetual_prod_succ` — the degenerate recurrence.
* `perpetual_walkZ_succ`, `perpetual_walkZ_eq_ffAutonomousMap` — the autonomous walk.
* `perpetual_walkZ_orbit` — the tail is an `ffAutonomousOrbit`.
* `perpetual_primality_excludes_two_mod_three` — the exclusion theorem.
* `perpetual_primality_missing`, `perpetual_primality_mem_missingPrimes` — missingness.
* `perpetual_primality_refutes_mullin` — the Φ₃-route corollary.
* `eventually_prime_implies_not_mullin` — the unconditional Bertrand-route corollary.
* `mullin_implies_infinitelyManyComposite` — MC forces (C∞).
* `infinitelyManyComposite_iff_no_perpetual_primality` — the contrapositive framing.
-/

open Mullin Euclid MullinGroup RotorRouter

namespace AutonomousBranch

/-! ## Part 1: The two hypotheses -/

/-- **Perpetual Primality (ω1)**: from step `N₁` on, every Euclid candidate
    `prod n + 1` is prime. -/
def PerpetualPrimality (N₁ : Nat) : Prop := ∀ n, N₁ ≤ n → Nat.Prime (prod n + 1)

/-- **Infinitely Many Composite (C∞)**: infinitely many Euclid candidates
    `prod n + 1` are composite. This is the exact negation of (ω1) holding
    from some step onward. -/
def InfinitelyManyComposite : Prop := ∀ N, ∃ n, N ≤ n ∧ ¬ Nat.Prime (prod n + 1)

/-! ## Part 2: The degenerate recurrence

Under (ω1) the Euclid candidate is its own least prime factor, so the sequence step
consumes the whole candidate. -/

/-- This project's `Euclid.minFac` fixes primes. (Note `Nat.minFac_le_of_dvd` does not
    apply to `Euclid.minFac`; we argue from `minFac_dvd` plus primality directly.) -/
theorem euclid_minFac_self_of_prime {m : Nat} (hm : Nat.Prime m) : minFac m = m := by
  have hm2 : 2 ≤ m := hm.two_le
  have hdvd : minFac m ∣ m := minFac_dvd m hm2
  have hge : 2 ≤ minFac m := (minFac_isPrime m hm2).1
  rcases (Nat.Prime.eq_one_or_self_of_dvd hm _ hdvd) with h1 | hself
  · omega
  · exact hself

/-- Under (ω1), the sequence term at step `n+1` is the *entire* Euclid candidate. -/
theorem perpetual_seq_succ {N₁ : Nat} (hpp : PerpetualPrimality N₁) {n : Nat}
    (hn : N₁ ≤ n) : seq (n + 1) = prod n + 1 := by
  rw [seq_succ]
  exact euclid_minFac_self_of_prime (hpp n hn)

/-- Under (ω1), the accumulator recurrence degenerates to `P ↦ P * (P + 1)`. -/
theorem perpetual_prod_succ {N₁ : Nat} (hpp : PerpetualPrimality N₁) {n : Nat}
    (hn : N₁ ≤ n) : prod (n + 1) = prod n * (prod n + 1) := by
  rw [prod_succ, perpetual_seq_succ hpp hn]

/-! ## Part 3: The autonomous walk mod q -/

/-- Under (ω1), the residue walk mod `q` becomes **autonomous**: the next position is a
    function of the current position alone. -/
theorem perpetual_walkZ_succ {N₁ : Nat} (q : Nat) (hpp : PerpetualPrimality N₁)
    {n : Nat} (hn : N₁ ≤ n) :
    walkZ q (n + 1) = walkZ q n * (walkZ q n + 1) := by
  have h := perpetual_prod_succ hpp hn
  simp only [walkZ, h]
  push_cast
  ring

/-- The autonomous walk step is literally `FunctionFieldAnalog.ffAutonomousMap`. -/
theorem perpetual_walkZ_eq_ffAutonomousMap {N₁ : Nat} (q : Nat) [Fact (Nat.Prime q)]
    (hpp : PerpetualPrimality N₁) {n : Nat} (hn : N₁ ≤ n) :
    walkZ q (n + 1) = FunctionFieldAnalog.ffAutonomousMap q (walkZ q n) :=
  perpetual_walkZ_succ q hpp hn

/-- **Tail orbit identification**: under (ω1) the walk from step `N₁` on is exactly the
    `ffAutonomousOrbit` of the map `w ↦ w * (w + 1)` started at `walkZ q N₁`.
    Stated with the offset `N₁ + k` to avoid truncated subtraction. -/
theorem perpetual_walkZ_orbit {N₁ : Nat} (q : Nat) [Fact (Nat.Prime q)]
    (hpp : PerpetualPrimality N₁) :
    ∀ k, walkZ q (N₁ + k) =
      FunctionFieldAnalog.ffAutonomousOrbit q (walkZ q N₁) k := by
  intro k
  induction k with
  | zero => simp [FunctionFieldAnalog.ffAutonomousOrbit]
  | succ m ih =>
    have hstep : walkZ q (N₁ + m + 1) = walkZ q (N₁ + m) * (walkZ q (N₁ + m) + 1) :=
      perpetual_walkZ_succ q hpp (Nat.le_add_right _ _)
    have hidx : N₁ + (m + 1) = N₁ + m + 1 := by omega
    rw [hidx, hstep, ih]
    rfl

/-! ## Part 4: The exclusion theorem

For `q ≡ 2 (mod 3)`, `q ≥ 5`, the polynomial `Φ₃(w) = w² + w + 1` has no root in
`ZMod q`, so `-1` has no preimage under the autonomous map. Hence once the walk is
autonomous and not already at `-1`, it can never reach `-1`. -/

/-- **Exclusion theorem** (headline). Under (ω1) from step `N₁`, if `q ≡ 2 (mod 3)` is a
    prime `≥ 5` whose walk position at step `N₁` is not `-1`, then `q` never divides a
    Euclid candidate again. -/
theorem perpetual_primality_excludes_two_mod_three
    {N₁ q : Nat} (hq : Nat.Prime q) (hq3 : q % 3 = 2) (hq5 : 5 ≤ q)
    (hpp : PerpetualPrimality N₁) (hne : walkZ q N₁ ≠ -1) :
    ∀ n, N₁ ≤ n → ¬ (q ∣ prod n + 1) := by
  have : Fact (Nat.Prime q) := ⟨hq⟩
  intro n hn hdvd
  have hw : walkZ q n = -1 := (walkZ_eq_neg_one_iff n).mpr hdvd
  obtain ⟨k, hk⟩ : ∃ k, n = N₁ + k := ⟨n - N₁, by omega⟩
  subst hk
  rw [perpetual_walkZ_orbit q hpp k] at hw
  exact FunctionFieldAnalog.ff_neg_one_unreachable q hq3 hq5 (walkZ q N₁) hne k hw

/-- Restatement: the hitting set of such a `q` is contained in the initial segment
    `{n | n < N₁}`. -/
theorem perpetual_primality_hittingSet_subset
    {N₁ q : Nat} (hq : Nat.Prime q) (hq3 : q % 3 = 2) (hq5 : 5 ≤ q)
    (hpp : PerpetualPrimality N₁) (hne : walkZ q N₁ ≠ -1) :
    HittingSet q ⊆ {n | n < N₁} := by
  intro n hn
  by_contra hlt
  exact perpetual_primality_excludes_two_mod_three hq hq3 hq5 hpp hne n
    (by simpa using Nat.not_lt.mp hlt) hn

/-! ## Part 5: Missingness -/

/-- Under (ω1), a fresh prime `q ≡ 2 (mod 3)`, `q ≥ 5`, with `walkZ q N₁ ≠ -1`
    **never appears** in the Euclid–Mullin sequence. -/
theorem perpetual_primality_missing
    {N₁ q : Nat} (hq : Nat.Prime q) (hq3 : q % 3 = 2) (hq5 : 5 ≤ q)
    (hpp : PerpetualPrimality N₁) (hne : walkZ q N₁ ≠ -1)
    (hfresh : ∀ k, k ≤ N₁ → seq k ≠ q) :
    ∀ k, seq k ≠ q := by
  intro k hk
  by_cases hle : k ≤ N₁
  · exact hfresh k hle hk
  · -- k > N₁, so k = m + 1 with m ≥ N₁
    obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    subst hm
    have hmN : N₁ ≤ m := by omega
    have h2 : 2 ≤ prod m + 1 := by have := prod_ge_two m; omega
    have hdvd : minFac (prod m + 1) ∣ prod m + 1 := minFac_dvd _ h2
    rw [seq_succ] at hk
    rw [hk] at hdvd
    exact perpetual_primality_excludes_two_mod_three hq hq3 hq5 hpp hne m hmN hdvd

/-- The same conclusion phrased as membership in `MissingPrimes`. -/
theorem perpetual_primality_mem_missingPrimes
    {N₁ q : Nat} (hq : Nat.Prime q) (hq3 : q % 3 = 2) (hq5 : 5 ≤ q)
    (hpp : PerpetualPrimality N₁) (hne : walkZ q N₁ ≠ -1)
    (hfresh : ∀ k, k ≤ N₁ → seq k ≠ q) :
    q ∈ MissingPrimes :=
  ⟨hq, perpetual_primality_missing hq hq3 hq5 hpp hne hfresh⟩

/-! ## Part 6: The headline corollary -/

/-- **(ω1) refutes Mullin's Conjecture.** Given any witness prime `q ≡ 2 (mod 3)`,
    `q ≥ 5`, that is fresh at step `N₁` and whose walk position there is not `-1`,
    perpetual primality from `N₁` makes Mullin's Conjecture false. -/
theorem perpetual_primality_refutes_mullin
    {N₁ q : Nat} (hq : Nat.Prime q) (hq3 : q % 3 = 2) (hq5 : 5 ≤ q)
    (hpp : PerpetualPrimality N₁) (hne : walkZ q N₁ ≠ -1)
    (hfresh : ∀ k, k ≤ N₁ → seq k ≠ q) :
    ¬ MullinConjecture := by
  intro hmc
  obtain ⟨n, hn⟩ := hmc q hq.toIsPrime
  exact perpetual_primality_missing hq hq3 hq5 hpp hne hfresh n hn

/-- A packaged form: under (ω1) plus a witness, `MissingPrimes` is nonempty. -/
theorem perpetual_primality_missingPrimes_nonempty
    {N₁ q : Nat} (hq : Nat.Prime q) (hq3 : q % 3 = 2) (hq5 : 5 ≤ q)
    (hpp : PerpetualPrimality N₁) (hne : walkZ q N₁ ≠ -1)
    (hfresh : ∀ k, k ≤ N₁ → seq k ≠ q) :
    (MissingPrimes).Nonempty :=
  ⟨q, perpetual_primality_mem_missingPrimes hq hq3 hq5 hpp hne hfresh⟩

/-! ## Part 7: The Bertrand route — perpetual primality refutes MC outright

The Φ₃ route of Parts 4–6 identifies *which* primes are excluded (a natural-density-`1/2`
set), but needs a witness with `walkZ q N₁ ≠ -1` and freshness. A Bertrand argument
removes all side conditions: under (ω1) the set of primes ever appearing is contained in
`{d : d ∣ prod T} ∪ {prod n + 1 : n ≥ T}`, and the values `prod n + 1` jump from
`prod T + 1` straight past `2 * (prod T + 1)`. Bertrand's postulate supplies a prime in
the gap. -/

/-- The accumulator is divisibility-monotone. -/
theorem prod_dvd_prod_of_le {m n : Nat} (h : m ≤ n) : prod m ∣ prod n := by
  induction n with
  | zero => have : m = 0 := by omega
            subst this; exact dvd_rfl
  | succ k ih =>
    rcases Nat.lt_or_ge m (k + 1) with hlt | hge
    · exact dvd_trans (ih (by omega)) ⟨seq (k + 1), prod_succ k⟩
    · have : m = k + 1 := by omega
      subst this; exact dvd_rfl

/-- The accumulator is monotone. -/
theorem prod_le_prod_of_le {m n : Nat} (h : m ≤ n) : prod m ≤ prod n :=
  Nat.le_of_dvd (by have := prod_ge_two n; omega) (prod_dvd_prod_of_le h)

/-- Under (ω1) from `T`, every Euclid candidate strictly beyond step `T` already
    exceeds `2 * (prod T + 1)`. -/
theorem perpetual_candidate_jump {T : Nat} (hpp : PerpetualPrimality T)
    {m : Nat} (hm : T < m) : 2 * (prod T + 1) < prod m + 1 := by
  have h2 : 2 ≤ prod T := prod_ge_two T
  have hstep : prod (T + 1) = prod T * (prod T + 1) := perpetual_prod_succ hpp le_rfl
  have hmono : prod (T + 1) ≤ prod m := prod_le_prod_of_le (by omega)
  have hbig : 2 * (prod T + 1) ≤ prod T * (prod T + 1) :=
    Nat.mul_le_mul_right _ h2
  omega

/-- **Bertrand route (headline).** Perpetual primality from *any* threshold outright
    refutes Mullin's Conjecture — no congruence condition, no freshness hypothesis,
    no witness needed. -/
theorem eventually_prime_implies_not_mullin
    (h : ∃ T, ∀ n, T ≤ n → Nat.Prime (prod n + 1)) : ¬ MullinConjecture := by
  obtain ⟨T, hpp⟩ := h
  have hpp' : PerpetualPrimality T := hpp
  have hP2 : 2 ≤ prod T := prod_ge_two T
  -- Bertrand: a prime r with prod T + 1 < r ≤ 2 * (prod T + 1)
  obtain ⟨r, hr, hrlt, hrle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (prod T + 1) (by omega)
  intro hmc
  obtain ⟨k, hk⟩ := hmc r hr.toIsPrime
  by_cases hkT : k ≤ T
  · -- early terms all divide prod T, hence are ≤ prod T < r
    have hdvd : seq k ∣ prod T := seq_dvd_prod k T hkT
    have hle : seq k ≤ prod T := Nat.le_of_dvd (by omega) hdvd
    omega
  · -- late terms are exactly the Euclid candidates prod m + 1 with m ≥ T
    obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    subst hm
    have hmT : T ≤ m := by omega
    have hval : seq (m + 1) = prod m + 1 := perpetual_seq_succ hpp' hmT
    rcases Nat.eq_or_lt_of_le hmT with heq | hlt
    · -- m = T: the candidate is prod T + 1 < r
      subst heq
      omega
    · -- m > T: the candidate already exceeds 2 * (prod T + 1) ≥ r
      have := perpetual_candidate_jump hpp' hlt
      omega

/-- Packaged form on `PerpetualPrimality`. -/
theorem perpetual_primality_refutes_mullin_unconditional {T : Nat}
    (hpp : PerpetualPrimality T) : ¬ MullinConjecture :=
  eventually_prime_implies_not_mullin ⟨T, hpp⟩

/-- Contrapositive: Mullin's Conjecture forces (C∞). -/
theorem mullin_implies_infinitelyManyComposite (hmc : MullinConjecture) :
    InfinitelyManyComposite := by
  intro N
  by_contra hcon
  exact perpetual_primality_refutes_mullin_unconditional
    (fun n hn => not_not.mp (fun hnp => hcon ⟨n, hn, hnp⟩)) hmc

/-! ## Part 8: Contrapositive framing and landscape -/

/-- (C∞) rules out (ω1) at every threshold. -/
theorem infinitelyManyComposite_implies_no_perpetual_primality
    (hC : InfinitelyManyComposite) : ∀ N₁, ¬ PerpetualPrimality N₁ := by
  intro N₁ hpp
  obtain ⟨n, hn, hnp⟩ := hC N₁
  exact hnp (hpp n hn)

/-- Conversely, if (ω1) fails at every threshold then (C∞) holds. -/
theorem no_perpetual_primality_implies_infinitelyManyComposite
    (h : ∀ N₁, ¬ PerpetualPrimality N₁) : InfinitelyManyComposite := by
  intro N
  by_contra hcon
  exact h N (fun n hn => not_not.mp (fun hnp => hcon ⟨n, hn, hnp⟩))

/-- (C∞) is *exactly* the negation of (ω1) at every threshold. -/
theorem infinitelyManyComposite_iff_no_perpetual_primality :
    InfinitelyManyComposite ↔ ∀ N₁, ¬ PerpetualPrimality N₁ :=
  ⟨infinitelyManyComposite_implies_no_perpetual_primality,
   no_perpetual_primality_implies_infinitelyManyComposite⟩

/-- Consequently, Mullin's Conjecture forces (C∞) for every witness configuration:
    if MC holds, no threshold can support perpetual primality alongside a fresh
    `q ≡ 2 (mod 3)` witness. -/
theorem mullin_implies_no_perpetual_primality_with_witness
    (hmc : MullinConjecture) {N₁ q : Nat}
    (hq : Nat.Prime q) (hq3 : q % 3 = 2) (hq5 : 5 ≤ q)
    (hne : walkZ q N₁ ≠ -1) (hfresh : ∀ k, k ≤ N₁ → seq k ≠ q) :
    ¬ PerpetualPrimality N₁ :=
  fun hpp => perpetual_primality_refutes_mullin hq hq3 hq5 hpp hne hfresh hmc

/-- **Autonomous branch landscape.** Under perpetual primality from `N₁` and a witness
    prime `q ≡ 2 (mod 3)`, `q ≥ 5`, fresh at `N₁` with `walkZ q N₁ ≠ -1`:

    1. the sequence step consumes the whole candidate, `seq (n+1) = prod n + 1`;
    2. the accumulator recurrence degenerates to `P ↦ P * (P + 1)`;
    3. the residue walk mod `q` is the autonomous orbit of `w ↦ w * (w + 1)`;
    4. `q` never divides a Euclid candidate from step `N₁` on;
    5. `q` is a missing prime;
    6. Mullin's Conjecture is false;
    7. equivalently, (C∞) is exactly the negation of (ω1) at every threshold. -/
theorem autonomous_branch_landscape
    {N₁ q : Nat} (hq : Nat.Prime q) (hq3 : q % 3 = 2) (hq5 : 5 ≤ q)
    (hpp : PerpetualPrimality N₁) (hne : walkZ q N₁ ≠ -1)
    (hfresh : ∀ k, k ≤ N₁ → seq k ≠ q) :
    (∀ n, N₁ ≤ n → seq (n + 1) = prod n + 1) ∧
    (∀ n, N₁ ≤ n → prod (n + 1) = prod n * (prod n + 1)) ∧
    (∀ n, N₁ ≤ n → walkZ q (n + 1) = walkZ q n * (walkZ q n + 1)) ∧
    (∀ n, N₁ ≤ n → ¬ (q ∣ prod n + 1)) ∧
    q ∈ MissingPrimes ∧
    ¬ MullinConjecture ∧
    (InfinitelyManyComposite ↔ ∀ N, ¬ PerpetualPrimality N) :=
  ⟨fun _ hn => perpetual_seq_succ hpp hn,
   fun _ hn => perpetual_prod_succ hpp hn,
   fun _ hn => perpetual_walkZ_succ q hpp hn,
   perpetual_primality_excludes_two_mod_three hq hq3 hq5 hpp hne,
   perpetual_primality_mem_missingPrimes hq hq3 hq5 hpp hne hfresh,
   perpetual_primality_refutes_mullin hq hq3 hq5 hpp hne hfresh,
   infinitelyManyComposite_iff_no_perpetual_primality⟩

/-- **Unconditional landscape** for the autonomous branch: the Bertrand route needs no
    witness at all, so the following three statements hold outright.

    1. perpetual primality from any threshold refutes Mullin's Conjecture;
    2. Mullin's Conjecture forces (C∞), infinitely many composite Euclid candidates;
    3. (C∞) is exactly the failure of (ω1) at every threshold.

    Thus `InfinitelyManyComposite` is a *necessary* condition for MC, and is precisely
    the hypothesis gating this failure mode. -/
theorem autonomous_branch_unconditional_landscape :
    (∀ T, PerpetualPrimality T → ¬ MullinConjecture) ∧
    (MullinConjecture → InfinitelyManyComposite) ∧
    (InfinitelyManyComposite ↔ ∀ T, ¬ PerpetualPrimality T) :=
  ⟨fun _ hpp => perpetual_primality_refutes_mullin_unconditional hpp,
   mullin_implies_infinitelyManyComposite,
   infinitelyManyComposite_iff_no_perpetual_primality⟩

end AutonomousBranch
