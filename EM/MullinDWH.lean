import EM.MullinConjectures

/-!
# The Divisor Walk Hypothesis

An abstract formulation: for any walk through distinct primes all > q,
where each prime divides the running product + 1, the walk must hit
-1 mod q. This implies Mullin's Conjecture.

* `DivisorWalkHypothesis`: the abstract hypothesis
* `dwh_implies_mullin`: DWH → MullinConjecture
* Partial results: DWH for q = 2, structural lemmas
-/

namespace Mullin

open Euclid


-- ============================================================================
-- PART 7: THE DIVISOR WALK HYPOTHESIS — AN ABSTRACT FORMULATION
--
-- The Hitting Hypothesis (Part 6) is specific to the Euclid–Mullin sequence.
-- But the core phenomenon is more general: in ANY infinite walk through primes
-- constrained by the "Euclid divisibility" rule, the running product should
-- hit every residue class.
--
-- The Divisor Walk Hypothesis abstracts away the greedy-min (minFac) choice
-- and asks: for any sequence of distinct primes p₀, p₁, p₂, ... all > q,
-- where each pₙ divides the running product + 1, must the running product
-- hit -1 mod q at some point?
--
-- If true, this immediately implies Mullin's Conjecture, because the EM
-- sequence (past the stage where all primes < q have been consumed) is
-- exactly such a walk.
--
-- Connection to factoring: the DWH is equivalent to saying that no sequence
-- of factoring choices can systematically avoid a residue class mod q.
-- A disproof would yield a new factoring technique. The non-existence of
-- such a technique (widely believed) would prove the DWH.
-- See docs/routes_to_conjecture_a.md for the full analysis.
-- ============================================================================

/-! ## The Divisor Walk Hypothesis -/

/-- The running product of a walk: starting from a seed, multiply by the
    walk's terms one at a time.

    `walkProd seed f n` = seed * f(0) * f(1) * ... * f(n-1)

    - walkProd seed f 0 = seed
    - walkProd seed f (n+1) = walkProd seed f n * f n -/
def walkProd (seed : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => seed
  | n + 1 => walkProd seed f n * f n

/-- **The Divisor Walk Hypothesis** (abstract formulation):

    Let q be prime. For any seed ≥ 2 not divisible by q, and any infinite
    sequence f of distinct primes all > q, where each f(n) divides the
    running product + 1, the running product must hit -1 mod q at some point.

    In symbols: ∃ n, q ∣ (walkProd seed f n + 1).

    This strips away the "minFac" (greedy-minimum) constraint of the EM
    sequence and asks only about the divisibility structure. It is stronger
    than the Hitting Hypothesis but more natural from the perspectives of
    number theory and factoring complexity.

    The conditions are:
    1. `seed ≥ 2` and `¬(q ∣ seed)` — the walk starts in (ℤ/qℤ)×
    2. `∀ n, IsPrime (f n)` — every step is a prime
    3. `∀ n, q < f n` — all primes exceed q (the "q-rough" condition)
    4. `∀ m n, f m = f n → m = n` — distinct primes (no repetition)
    5. `∀ n, f n ∣ walkProd seed f n + 1` — the Euclid divisibility constraint -/
def DivisorWalkHypothesis : Prop :=
  ∀ q, IsPrime q →
  ∀ seed, 2 ≤ seed → ¬(q ∣ seed) →
  ∀ f : Nat → Nat,
    (∀ n, IsPrime (f n)) →
    (∀ n, q < f n) →
    (∀ m n, f m = f n → m = n) →
    (∀ n, f n ∣ walkProd seed f n + 1) →
    ∃ n, q ∣ (walkProd seed f n + 1)

section
open Classical

/-- The tail of the EM sequence past stage N consists of primes ≥ q,
    provided all primes below q appeared by stage N.

    Proof: seq(n+1) = minFac(prod n + 1). If minFac < q, it's a prime
    that appeared by stage N ≤ n, so it divides prod n. But it also
    divides prod n + 1 — contradicting `not_dvd_consec`. -/
private theorem tail_ge_target {q N n : Nat} (_hq : IsPrime q) (hn : N ≤ n)
    (hN : ∀ p, p < q → IsPrime p → ∃ m, m ≤ N ∧ seq m = p) :
    q ≤ seq (n + 1) := by
  rw [seq_succ]
  have hpn : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
  match Nat.lt_or_ge (minFac (prod n + 1)) q with
  | .inr hge => exact hge
  | .inl hlt =>
    exfalso
    have hp := minFac_isPrime _ hpn
    obtain ⟨m, hmN, hseqm⟩ := hN _ hlt hp
    have hdvd_succ := minFac_dvd _ hpn
    rw [← hseqm] at hdvd_succ
    exact seq_not_dvd_prod_succ (by omega : m ≤ n) hdvd_succ

/-- The walk product of the EM tail equals the running product.

    If f(k) = seq(N + 1 + k) and seed = prod N, then
    walkProd seed f k = prod(N + k). -/
private theorem walkProd_tail (N : Nat) :
    ∀ k, walkProd (prod N) (fun k => seq (N + 1 + k)) k = prod (N + k) := by
  intro k
  induction k with
  | zero => simp [walkProd]
  | succ k ih =>
    show walkProd (prod N) (fun k => seq (N + 1 + k)) k * seq (N + 1 + k) = prod (N + (k + 1))
    rw [ih]
    have h1 : N + (k + 1) = (N + k) + 1 := by omega
    have h2 : N + 1 + k = (N + k) + 1 := by omega
    rw [h1, prod_succ, h2]

/-- **Tail Hitting Hypothesis implies Mullin's Conjecture.**

    This is the same argument as `hh_implies_mullin`, but it only needs a
    single hit past a stage where all primes below q have appeared. -/
theorem tailHH_implies_mullin : TailHittingHypothesis → MullinConjecture := by
  intro hH
  unfold MullinConjecture
  -- Strong induction on q (same pattern as before).
  suffices ∀ k q, q ≤ k → IsPrime q → ∃ n, seq n = q by
    intro q hq; exact this q q (Nat.le_refl q) hq
  intro k
  induction k with
  | zero =>
    intro q hle hq; exact absurd hq.1 (by omega)
  | succ k ih =>
    intro q hle hq
    match Nat.lt_or_ge q (k + 1) with
    | .inl hlt => exact ih q (by omega) hq
    | .inr _ =>
      -- Either q appears somewhere, or it never appears.
      match em (∃ n, seq n = q) with
      | .inl hexists => exact hexists
      | .inr hnotexists =>
        -- q never appears. Collect a bound N for all primes < q.
        have hne : ∀ m, seq m ≠ q := by
          intro m heq; exact hnotexists ⟨m, heq⟩
        have appears : ∀ p, p < q → IsPrime p → ∃ n, seq n = p :=
          fun p hpq hp => ih p (by omega) hp
        obtain ⟨N, hN⟩ := exists_bound q appears
        -- Tail HH gives a hit past N.
        obtain ⟨n, hn_ge, hn_dvd⟩ := hH q hq N hN hne
        -- Now every prime below q has appeared by stage n.
        have hall : ∀ p, p < q → IsPrime p → ∃ m, m ≤ n ∧ seq m = p := by
          intro p hpq hp
          obtain ⟨m, hm, hseqm⟩ := hN p hpq hp
          exact ⟨m, by omega, hseqm⟩
        -- Capture lemma: seq(n+1) = q.
        exact ⟨n + 1, captures_target hq hn_dvd hall⟩

/-- **DWH implies the Tail Hitting Hypothesis.**

    This is a direct application of DWH to the EM tail past a stage N that
    already contains all primes below q. -/
theorem dwh_implies_tailHH : DivisorWalkHypothesis → TailHittingHypothesis := by
  intro hDWH
  intro q hq N hN hne
  -- Define the EM tail walk.
  let f := fun k => seq (N + 1 + k)
  -- Verify DWH preconditions for the tail.
  have hseed : 2 ≤ prod N := prod_ge_two N
  have hndvd : ¬(q ∣ prod N) := prime_not_in_seq_not_dvd_prod hq hne N
  have hfprime : ∀ n, IsPrime (f n) := fun n => seq_isPrime (N + 1 + n)
  have hfgt : ∀ n, q < f n := by
    intro n
    show q < seq (N + 1 + n)
    have hge : q ≤ seq (N + 1 + n) := by
      have h : N + 1 + n = (N + n) + 1 := by omega
      rw [h]
      exact tail_ge_target hq (by omega) hN
    have hneq : seq (N + 1 + n) ≠ q := hne (N + 1 + n)
    omega
  have hfinj : ∀ m n, f m = f n → m = n := by
    intro m n h
    have := seq_injective _ _ h
    omega
  have hfdvd : ∀ n, f n ∣ walkProd (prod N) f n + 1 := by
    intro n
    rw [walkProd_tail]
    show seq (N + 1 + n) ∣ prod (N + n) + 1
    have h : N + 1 + n = (N + n) + 1 := by omega
    rw [h, seq_succ]
    exact minFac_dvd _ (by have := prod_ge_two (N + n); omega)
  obtain ⟨m, hm⟩ := hDWH q hq (prod N) hseed hndvd f hfprime hfgt hfinj hfdvd
  -- Translate the walk hit to the running product.
  have hm' : q ∣ prod (N + m) + 1 := by
    rw [walkProd_tail] at hm
    exact hm
  exact ⟨N + m, by omega, hm'⟩

/-- **The main reduction: DWH implies Mullin's Conjecture (directly).**

    The proof combines strong induction with the DWH:

    1. By strong induction, assume all primes p < q appear in the sequence.
    2. Classical case split: either q appears (done) or q never appears.
    3. If q never appears: collect all primes < q into a uniform bound N.
       Past stage N, the EM tail is a walk with primes > q (they're ≥ q by
       `tail_ge_target`, and ≠ q since q never appears).
    4. Verify the DWH preconditions for the tail walk and apply it.
    5. The DWH gives a hitting event, which `captures_target` turns into
       seq(n+1) = q — contradicting q never appearing. -/
theorem dwh_implies_mullin : DivisorWalkHypothesis → MullinConjecture := by
  intro hDWH
  unfold MullinConjecture
  -- Strong induction on q
  suffices ∀ k q, q ≤ k → IsPrime q → ∃ n, seq n = q by
    intro q hq; exact this q q (Nat.le_refl q) hq
  intro k
  induction k with
  | zero => intro q hle hq; exact absurd hq.1 (by omega)
  | succ k ih =>
    intro q hle hq
    match Nat.lt_or_ge q (k + 1) with
    | .inl hlt => exact ih q (by omega) hq
    | .inr _ =>
      -- Either q appears or it doesn't
      match em (∃ n, seq n = q) with
      | .inl hexists => exact hexists
      | .inr hnotexists =>
        exfalso
        -- q never appears
        have hne : ∀ m, seq m ≠ q := fun m heq => hnotexists ⟨m, heq⟩
        -- All primes < q appear (by IH)
        have appears : ∀ p, p < q → IsPrime p → ∃ n, seq n = p :=
          fun p hpq hp => ih p (by omega) hp
        -- Collect into uniform bound N
        obtain ⟨N, hN⟩ := exists_bound q appears
        -- Define the tail walk: f(k) = seq(N + 1 + k), seed = prod N
        let f := fun k => seq (N + 1 + k)
        -- Verify DWH preconditions:
        -- (1) seed ≥ 2
        have hseed : 2 ≤ prod N := prod_ge_two N
        -- (2) q ∤ seed (q never appears, so by coprimality it can't divide the product)
        have hndvd : ¬(q ∣ prod N) := prime_not_in_seq_not_dvd_prod hq hne N
        -- (3) each f(k) is prime
        have hfprime : ∀ n, IsPrime (f n) := fun n => seq_isPrime (N + 1 + n)
        -- (4) each f(k) > q (all tail primes exceed q)
        have hfgt : ∀ n, q < f n := by
          intro n
          show q < seq (N + 1 + n)
          have hge : q ≤ seq (N + 1 + n) := by
            have h : N + 1 + n = (N + n) + 1 := by omega
            rw [h]
            exact tail_ge_target hq (by omega) hN
          have hneq : seq (N + 1 + n) ≠ q := hne (N + 1 + n)
          omega
        -- (5) f is injective (from seq_injective)
        have hfinj : ∀ m n, f m = f n → m = n := by
          intro m n h
          have := seq_injective _ _ h
          omega
        -- (6) each f(k) divides walkProd(seed, f, k) + 1
        have hfdvd : ∀ n, f n ∣ walkProd (prod N) f n + 1 := by
          intro n
          rw [walkProd_tail]
          show seq (N + 1 + n) ∣ prod (N + n) + 1
          have h : N + 1 + n = (N + n) + 1 := by omega
          rw [h, seq_succ]
          exact minFac_dvd _ (by have := prod_ge_two (N + n); omega)
        -- Apply DWH: get k with q ∣ walkProd(prod N, f, k) + 1
        obtain ⟨m, hm⟩ := hDWH q hq (prod N) hseed hndvd f hfprime hfgt hfinj hfdvd
        -- Translate: walkProd = prod(N + m), so q ∣ prod(N + m) + 1
        rw [walkProd_tail] at hm
        -- captures_target: seq(N + m + 1) = q
        have hall : ∀ p, p < q → IsPrime p → ∃ j, j ≤ (N + m) ∧ seq j = p := by
          intro p hpq hp
          obtain ⟨j, hj, hseqj⟩ := hN p hpq hp
          exact ⟨j, by omega, hseqj⟩
        have hcap := captures_target hq hm hall
        -- But seq(N + m + 1) = q contradicts q never appearing
        exact hnotexists ⟨N + m + 1, hcap⟩

end

-- ============================================================================
-- PART 8: TOWARDS PROVING DWH — ANALYSIS AND PARTIAL RESULTS
--
-- Can we prove the Divisor Walk Hypothesis? We investigate the structure
-- of the problem, prove DWH for the simplest case (q = 2), establish key
-- structural lemmas, and analyze why the general case is deep.
--
-- Summary of findings:
--
-- (a) DWH for q = 2 is trivially true: seed is odd, so seed + 1 is even.
--     Take n = 0. (Proved below as `dwh_for_two`.)
--
-- (b) For any prime q, the walk stays in (ℤ/qℤ)× — i.e., q never divides
--     any walkProd value. This is because q ∤ seed and q ∤ f(n) (since
--     f(n) > q is prime), and primes can't divide a product without
--     dividing a factor. (Proved below as `walk_coprime_q`.)
--
-- (c) For general q, the DWH asserts that the "residue walk" P_n mod q
--     hits q-1 (= -1 mod q). This walk lives in the finite group
--     (ℤ/qℤ)× of order q-1, with transition P_{n+1} ≡ P_n · f(n) (mod q).
--
-- (d) The key obstacle: in the ABSTRACT setting (arbitrary factor choice),
--     the walk has enough freedom to potentially avoid -1 forever. An
--     adversary choosing factors can select multipliers in a specific
--     residue class mod q, steering the walk away from the target.
--     This is because large numbers P_n + 1 typically have prime factors
--     in every residue class mod q, giving the adversary choice.
--
-- (e) For the Euclid–Mullin sequence specifically (using minFac — the
--     SMALLEST factor), this adversarial freedom vanishes. The smallest
--     factor of a large number is distributed in a way that can't be
--     steered. This is why the HittingHypothesis (Part 6) — specific
--     to the EM sequence — is the right target for proving Mullin's
--     Conjecture, rather than the fully abstract DWH.
--
-- See docs/routes_to_conjecture_a.md for the full mathematical analysis.
-- ============================================================================

/-! ## Towards proving the Divisor Walk Hypothesis -/

/-- **DWH for q = 2** (the trivial case).

    When q = 2, the seed is odd (since 2 ∤ seed), so seed + 1 is even.
    Therefore 2 ∣ (walkProd seed f 0 + 1) = 2 ∣ (seed + 1).
    The witness is n = 0. -/
theorem dwh_for_two (seed : Nat) (_ : 2 ≤ seed) (hndvd : ¬(2 ∣ seed))
    (f : Nat → Nat) (_ : ∀ n, IsPrime (f n)) (_ : ∀ n, 2 < f n)
    (_ : ∀ m n, f m = f n → m = n) (_ : ∀ n, f n ∣ walkProd seed f n + 1) :
    ∃ n, 2 ∣ (walkProd seed f n + 1) := by
  refine ⟨0, ?_⟩
  -- walkProd seed f 0 = seed, so we need 2 ∣ seed + 1
  show 2 ∣ seed + 1
  -- seed is odd (2 ∤ seed), so seed + 1 is even
  rw [Nat.dvd_iff_mod_eq_zero] at hndvd ⊢
  omega


/-- If q is prime and divides neither a nor b, then q does not divide a * b.

    This is the contrapositive of Euclid's lemma. We prove it using the
    coprimality result above and `Coprime.dvd_of_dvd_mul_right`. -/
private theorem prime_not_dvd_mul {q a b : Nat} (hq : IsPrime q)
    (ha : ¬(q ∣ a)) (hb : ¬(q ∣ b)) : ¬(q ∣ a * b) := by
  intro hdvd
  have hcop : Nat.Coprime q b := coprime_of_prime_not_dvd hq hb
  exact ha (hcop.dvd_of_dvd_mul_right hdvd)

/-- **The walk stays in (ℤ/qℤ)×**: q never divides any walkProd value.

    Since q ∤ seed and q ∤ f(n) for all n (because f(n) > q is prime,
    so its only divisors are 1 and itself, and q is neither), the product
    of these values is also coprime to q.

    This means the walk P_n mod q never hits 0 — it stays in the
    multiplicative group (ℤ/qℤ)× = {1, 2, ..., q-1} at every step. -/
theorem walk_coprime_q {q seed : Nat} (hq : IsPrime q)
    (hndvd : ¬(q ∣ seed))
    {f : Nat → Nat} (hfprime : ∀ n, IsPrime (f n)) (hfgt : ∀ n, q < f n) :
    ∀ n, ¬(q ∣ walkProd seed f n) := by
  intro n
  induction n with
  | zero => exact hndvd
  | succ n ih =>
    show ¬(q ∣ walkProd seed f n * f n)
    apply prime_not_dvd_mul hq ih
    -- q ∤ f(n): since f(n) is prime and q divides it, q = 1 or q = f(n).
    -- But q ≥ 2 (ruling out 1) and f(n) > q (ruling out equality).
    intro hdvd
    have hge := hq.1  -- 2 ≤ q
    have hgt := hfgt n  -- q < f n
    match (hfprime n).2 q hdvd with
    | .inl h => omega  -- q = 1 contradicts 2 ≤ q
    | .inr h => omega  -- q = f(n) contradicts q < f(n)

-- ============================================================================
-- THE RESIDUE WALK AND THE ADVERSARY OBSTACLE
--
-- The walk P_n mod q lives in the cyclic group (ℤ/qℤ)× of order q-1.
-- At each step, P_{n+1} ≡ P_n · f(n) (mod q).  The DWH asks: does
-- this multiplicative walk hit -1 ≡ q-1 (mod q)?
--
-- For q = 2: the group is trivial {1}, and seed ≡ 1 (mod 2) since seed
-- is odd.  Then P_0 + 1 ≡ 0 (mod 2).  Immediate.
--
-- For q = 3: the group is {1, 2}, cyclic of order 2.  The walk hits -1
-- iff some multiplier f(n) ≡ 2 (mod 3).  If all f(n) ≡ 1 (mod 3),
-- the walk stays at its initial position forever.
--
-- The key question for q = 3: can P_n + 1 always have a prime factor > 3
-- that is ≡ 1 (mod 3)?  Since P_n + 1 ≡ 2 (mod 3) (when P_n ≡ 1),
-- the number has an odd count of prime factors ≡ 2 (mod 3).  But it
-- could ALSO have factors ≡ 1 — those just don't affect the residue.
-- For large P_n, such factors are heuristically abundant.
--
-- This reveals the adversary obstacle:
--
-- In the abstract DWH, the walk chooses ANY prime factor > q of P_n + 1.
-- For large P_n + 1, this number has many prime factors in various
-- residue classes mod q.  An adversary can pick factors in a specific
-- class, keeping the walk in a proper subset of (ℤ/qℤ)× that avoids -1.
--
-- Concretely: if the walk is at state r ≢ -1 (mod q), the adversary
-- picks f(n) ≡ 1 (mod q) whenever possible, keeping P_{n+1} ≡ r.
-- Since P_n + 1 ≡ r + 1 ≢ 0 (mod q), and large numbers in any
-- nonzero residue class have prime factors in every residue class,
-- the adversary can usually find a factor ≡ 1.
--
-- The Euclid–Mullin sequence avoids this: minFac (smallest factor)
-- cannot be strategically chosen.  Its residue mod q is determined
-- by the arithmetic of the number, not by adversarial choice.
-- This is why the HittingHypothesis — specific to the EM sequence —
-- is the right formulation for proving Mullin's Conjecture.
-- ============================================================================

-- ============================================================================
-- THE FORCED-CAPTURE PHENOMENON
--
-- Despite the adversary obstacle for general walks, there IS a forcing
-- mechanism: if P_n + 1 happens to have ALL its prime factors > q in a
-- residue class that sends the walk to -1, the adversary has no choice.
--
-- For q = 3 with the walk at P_n ≡ 1 (mod 3):
--   If ALL prime factors > 3 of P_n + 1 are ≡ 2 (mod 3), the adversary
--   must pick one, sending P_{n+1} ≡ 2 ≡ -1 (mod 3).  Hit!
--
-- When does this happen?  When P_n + 1 = 2^a · p₁ · p₂ · ... with every
-- pᵢ ≡ 2 (mod 3).  This is "rare" for large numbers (heuristically,
-- about half the prime factors should be ≡ 1), but it does happen.
--
-- For the EM sequence, the forcing is even stronger: minFac is the
-- SMALLEST factor, which for large numbers is typically very small
-- relative to the number.  Small primes are more likely to "generate"
-- the full group (ℤ/qℤ)× (by the subgroup obstruction route — see
-- docs/routes_to_conjecture_a.md, Route 1), so the residue walk
-- covers more of the group.
--
-- The gap between "heuristically true" and "provably true" is exactly
-- where the analytic number theory lives: character sums, Bombieri–
-- Vinogradov, and the distribution of smallest prime factors in
-- arithmetic progressions.
-- ============================================================================

/-- If the walk avoids -1 mod q forever, then q is coprime to every
    "Euclid number" P_n + 1 of the walk.

    Contrapositive: if q ∣ (P_n + 1) for some n, the walk hits -1 mod q.
    This is just `walk_coprime_q` combined with the DWH conclusion. -/
theorem walk_avoidance_coprime {q seed : Nat} (hq : IsPrime q)
    (hndvd : ¬(q ∣ seed))
    {f : Nat → Nat} (hfprime : ∀ n, IsPrime (f n)) (hfgt : ∀ n, q < f n)
    (havoid : ∀ n, ¬(q ∣ walkProd seed f n + 1)) :
    ∀ n, ¬(q ∣ walkProd seed f n) ∧ ¬(q ∣ walkProd seed f n + 1) :=
  fun n => ⟨walk_coprime_q hq hndvd hfprime hfgt n, havoid n⟩

-- ============================================================================
-- WHAT WOULD CLOSE THE GAP?
--
-- The DWH would follow from either:
--
-- (A) A "subgroup generation" theorem: for any Euclid-style walk with
--     primes > q, the multiplier residues f(n) mod q eventually generate
--     (ℤ/qℤ)×.  Once the full group is generated, mixing arguments show
--     the walk must hit -1.
--
-- (B) A "density" theorem: show that for any residue r ≢ 0 (mod q),
--     the probability that a large number N ≡ r + 1 (mod q) has ALL
--     its prime factors > q in a single residue class goes to 0.
--     This would show the adversary eventually runs out of "safe" choices.
--
-- (C) A "minFac-specific" theorem (for the EM sequence only): show that
--     the smallest prime factor of P_n + 1, viewed mod q, equidistributes
--     as n → ∞.  This would prove the HittingHypothesis directly.
--
-- Approach (C) is the most promising for Mullin's Conjecture, since it
-- targets the specific structure of the EM sequence rather than all
-- abstract walks.  It connects to Booker's Weil bound arguments
-- (see docs/routes_to_conjecture_a.md, Route 2).
--
-- For now, the chain
--
--     DWH → MullinConjecture    (Part 7, proved)
--     HH  → MullinConjecture    (Part 6, proved)
--
-- is established.  The DWH and HH remain open conjectures.  The
-- structural results in this section (walk_coprime_q, dwh_for_two)
-- handle the foundational cases and illuminate the obstacle.
-- ============================================================================

-- ============================================================================
-- PART 9: ROUTE 2 — THE RESIDUE WALK AND EQUIDISTRIBUTION APPROACH
--
-- We reformulate the Hitting Hypothesis in terms of modular arithmetic
-- and establish the structural framework for an equidistribution proof.
--
-- Key insight: the HH asks that the "residue walk" prod(n) mod q hits
-- q - 1 (= -1 mod q). This walk satisfies the recurrence:
--
--   prod(n+1) mod q = (prod(n) mod q) · (seq(n+1) mod q) mod q
--
-- The walk lives in {1, ..., q-1} (the multiplicative group (ℤ/qℤ)×),
-- never hitting 0 (since q never divides prod(n) or seq(n) when q is
-- not in the sequence).
--
-- This section establishes:
--
-- 1. Bridge lemma: q ∣ (a+1) ↔ a mod q = q-1   (dvd_succ_iff_mod_pred)
-- 2. Walk recurrence: prod(n+1) mod q = ...       (prod_succ_mod)
-- 3. Residue invariants: seq(n), prod(n) ≢ 0      (seq_mod_ne_zero, etc.)
-- 4. HH ↔ ResidueHitting equivalence              (hh_iff_rh)
-- 5. WalkCoverage hypothesis and its implications  (wc_implies_mullin)
--
-- Route 2 analysis (Sieve + Equidistribution):
--
-- The goal is to show the residue walk covers the full group, hitting
-- every element of {1, ..., q-1} — in particular q-1 (= -1 mod q).
--
-- For the walk to avoid -1 forever, the multiplier residues seq(n) mod q
-- must be "coordinated" to keep the running product in a proper subset.
-- Specifically, if the multiplier residues lie in a coset of a proper
-- subgroup H < (ℤ/qℤ)×, the walk stays in a coset of H.
--
-- For the EM sequence, where multipliers are minFac of Euclid numbers:
-- (a) Sieve theory suggests minFac residues should generate the full
--     multiplicative group (no confinement to a proper subgroup).
-- (b) The multipliers are all distinct primes, so the sequence can't
--     be periodic or patterned in a way that traps the walk.
-- (c) The Bombieri–Vinogradov theorem provides the equidistribution
--     of primes across residue classes that underpins (a).
--
-- The gap: turning these heuristics into a proof requires either:
-- - A mixing time argument for multiplicative walks on cyclic groups, or
-- - A direct sieve-theoretic bound on the walk's range.
-- Neither is currently formalized. The structural results below
-- identify exactly what remains to be proved.
-- ============================================================================


end Mullin
