import EM.MullinDefs

/-!
# Mullin's Conjecture, Conjecture A, and the Hitting Hypothesis

Definitions and reductions for the Euclid–Mullin sequence:
* `MullinConjecture`: every prime appears in the sequence
* `ConjectureA`: the running product hits -1 mod q infinitely often (FALSE)
* `HittingHypothesis`: corrected version requiring q ∉ seq
* `hh_implies_mullin`: HH → MullinConjecture (strong induction on q)
-/

namespace Mullin

open Euclid

/-! ## Mullin's Conjecture -/

/-- **Mullin's Conjecture** (1963, open).

    *Every prime number appears in the Euclid–Mullin sequence.*

    Equivalently: for every prime p, there exists an index n such that
    the n-th term of the sequence equals p.

    In symbols: `∀ p, IsPrime p → ∃ n, seq n = p`.

    This is one of the most famous open questions in elementary number theory.
    We state it here as a proposition (a mathematical statement whose truth
    value is unknown), not as a theorem.  If it were ever proved, one could
    write:

        theorem mullinConjecture_proof : MullinConjecture := ...

    Conversely, if it were disproved (by exhibiting a prime that provably
    never appears), one could write:

        theorem mullinConjecture_false : ¬MullinConjecture := ... -/
def MullinConjecture : Prop :=
  ∀ p, IsPrime p → ∃ n, seq n = p

-- ============================================================================
-- PART 5: THE REDUCTION — CONJECTURE A IMPLIES MULLIN'S CONJECTURE
--
-- Conjecture A says: for every prime q, the running product Pₙ hits −1 mod q
-- infinitely often. That is, q ∣ (Pₙ + 1) for arbitrarily large n.
--
-- We show: Conjecture A ⟹ Mullin's Conjecture (every prime appears).
--
-- The argument (strong induction on q):
--   Assume all primes p < q already appear in the sequence.
--   Then past some stage N, every prime below q divides the running product,
--   so none of them can divide (prod n + 1) for n ≥ N.
--   By Conjecture A, pick n ≥ N with q ∣ (prod n + 1).
--   Then minFac(prod n + 1) ≥ q (no smaller prime divides it)
--     and minFac(prod n + 1) ≤ q (since q is a factor).
--   So seq(n+1) = minFac(prod n + 1) = q.
--
-- This part uses classical logic (for extracting witnesses from existential
-- hypotheses via strong induction). All definitions and basic properties
-- in Parts 1–4 above remain fully constructive.
-- ============================================================================

/-! ## Conjecture A and the Reduction -/

/-- **Conjecture A** (the "infinitary hitting hypothesis"):
    for every prime q and every bound N, there exists n ≥ N such that
    q divides (prod n + 1).

    Equivalently: the running product Pₙ hits −1 mod q infinitely often.

    This is weaker than Mullin's Conjecture (it doesn't say q *appears*
    in the sequence, only that q divides the "Euclid number" at infinitely
    many stages). But combined with the Euclid argument, it implies
    Mullin's Conjecture — see `conjectureA_implies_mullin` below.

    Conjecture A itself is a natural target for analytic number theory:
    it would follow from equidistribution of the partial products mod q
    in (ℤ/qℤ)×, which in turn would follow from the sequence of primes
    generating the full multiplicative group mod q. -/
def ConjectureA : Prop :=
  ∀ q, IsPrime q → ∀ N, ∃ n, N ≤ n ∧ q ∣ (prod n + 1)

/-- No number ≥ 2 can divide two consecutive naturals.

    If p ∣ a and p ∣ (a + 1), then p divides their difference
    (a + 1) − a = 1, so p ≤ 1, contradicting p ≥ 2.

    This is the same argument Euclid used in `isPrime_not_dvd_one`,
    just stated more generally. -/
theorem not_dvd_consec {p a : Nat} (hp : 2 ≤ p)
    (h1 : p ∣ a) (h2 : p ∣ a + 1) : False := by
  -- p divides (a + 1) and p divides a, so p divides (a + 1) - a = 1
  have h3 : p ∣ (a + 1 - a) := Nat.dvd_sub h2 h1
  have h4 : a + 1 - a = 1 := by omega
  rw [h4] at h3
  -- p ∣ 1 implies p ≤ 1 (since 1 > 0), contradicting p ≥ 2
  have := Nat.le_of_dvd Nat.one_pos h3
  omega

/-- Once a term has entered the sequence, it cannot divide the next
    "Euclid number" (running product + 1).

    If seq m appeared at stage m ≤ n, then seq m ∣ prod n (it's one of
    the factors). So seq m divides both prod n and prod n + 1, which
    contradicts `not_dvd_consec` since seq m ≥ 2 (it's prime). -/
theorem seq_not_dvd_prod_succ {m n : Nat} (hmn : m ≤ n) :
    ¬(seq m ∣ prod n + 1) := by
  -- seq m divides prod n (it's one of the factors in the product)
  have hdvd := seq_dvd_prod m n hmn
  -- seq m is prime, hence ≥ 2
  have hge := (seq_isPrime m).1
  -- If seq m also divided prod n + 1, it would divide two consecutive
  -- naturals, which is impossible for any number ≥ 2.
  intro h
  exact not_dvd_consec hge hdvd h

/-- **The capture lemma**: if q ∣ (prod n + 1) and all primes below q
    have already appeared by stage n, then seq (n + 1) = q.

    This is the core of the reduction. At stage n:
    - q divides prod n + 1, so minFac(prod n + 1) ≤ q (by minimality).
    - Every prime p < q already appeared at some stage m ≤ n, so
      p ∣ prod n, hence p ∤ (prod n + 1). In particular, minFac(prod n + 1)
      cannot be any prime below q.
    - Therefore minFac(prod n + 1) = q, i.e., seq(n + 1) = q. -/
theorem captures_target {q n : Nat} (hq : IsPrime q)
    (hdvd : q ∣ prod n + 1)
    (hall : ∀ p, p < q → IsPrime p → ∃ m, m ≤ n ∧ seq m = p) :
    seq (n + 1) = q := by
  -- seq(n+1) = minFac(prod n + 1) by definition
  rw [seq_succ]
  -- prod n + 1 ≥ 3 ≥ 2, so minFac is well-defined and prime
  have hpn : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
  -- Upper bound: minFac(prod n + 1) ≤ q, because q ≥ 2 and q divides it
  have hle : minFac (prod n + 1) ≤ q := minFac_min' _ _ hpn hq.1 hdvd
  -- Lower bound: minFac(prod n + 1) ≥ q.
  -- Suppose minFac(prod n + 1) < q. Then let p = minFac(prod n + 1).
  -- p is prime and p < q, so by `hall`, p = seq m for some m ≤ n.
  -- But then p ∣ prod n (by seq_dvd_prod), and p ∣ prod n + 1 (since
  -- p = minFac(prod n + 1)). This contradicts `not_dvd_consec`.
  have hge : q ≤ minFac (prod n + 1) := by
    -- Case split: either minFac(prod n + 1) < q or ≥ q.
    match Nat.lt_or_ge (minFac (prod n + 1)) q with
    | .inr hge =>
      -- minFac ≥ q: exactly what we need.
      exact hge
    | .inl hlt =>
      -- minFac(prod n + 1) < q: we derive a contradiction.
      exfalso
      -- minFac(prod n + 1) is prime and < q.
      have hp := minFac_isPrime _ hpn
      -- By hall, this prime appeared at some stage m ≤ n.
      obtain ⟨m, hmn, hseqm⟩ := hall _ hlt hp
      -- minFac(prod n + 1) divides prod n + 1 (by definition of minFac).
      have hdvd_succ : minFac (prod n + 1) ∣ prod n + 1 := minFac_dvd _ hpn
      -- But seq m = minFac(...), and m ≤ n, so seq m ∣ prod n.
      -- A number can't divide both prod n and prod n + 1.
      rw [← hseqm] at hdvd_succ
      exact seq_not_dvd_prod_succ hmn hdvd_succ
  -- Combining: q ≤ minFac(prod n + 1) ≤ q, so they're equal
  omega

section
open Classical

/-- Helper lemma (classical): if every prime below q appears in the sequence,
    then there exists a uniform bound N such that they all appear by stage N.

    This is the step that requires classical logic: we extract a concrete
    witness nₚ from each existential `∃ n, seq n = p` (via `Classical.choice`)
    and take the maximum over all primes p < q.

    The proof is by induction on q:
    - q = 0: vacuously true (no primes below 0).
    - q = q' + 1: extend the bound for primes below q' with one more case:
      if q' is prime, take the max of the old bound and q's witness;
      if q' is not prime, the old bound suffices. -/
theorem exists_bound (q : Nat)
    (h : ∀ p, p < q → IsPrime p → ∃ n, seq n = p) :
    ∃ N, ∀ p, p < q → IsPrime p → ∃ m, m ≤ N ∧ seq m = p := by
  induction q with
  | zero =>
    -- No primes below 0: the statement is vacuously true.
    exact ⟨0, fun p hp _ => absurd hp (by omega)⟩
  | succ q' ih =>
    -- Primes below q' + 1 = primes below q' plus possibly q' itself.
    -- Get the bound N' for primes below q'.
    have h' : ∀ p, p < q' → IsPrime p → ∃ n, seq n = p :=
      fun p hp hprime => h p (by omega) hprime
    obtain ⟨N', hN'⟩ := ih h'
    -- Is q' itself prime? (Classical decidability via `open Classical`.)
    if hprime : IsPrime q' then
      -- q' is prime and < q' + 1, so by h it appears at some stage m.
      obtain ⟨m, hm⟩ := h q' (by omega) hprime
      -- New bound: max(N', m). Covers all primes ≤ q'.
      refine ⟨Nat.max N' m, fun p hp hprim => ?_⟩
      -- Either p < q' (use the old bound) or p = q' (use m).
      match Nat.lt_or_ge p q' with
      | .inl hlt =>
        obtain ⟨j, hj, hjseq⟩ := hN' p hlt hprim
        exact ⟨j, Nat.le_trans hj (Nat.le_max_left N' m), hjseq⟩
      | .inr hge =>
        have : p = q' := by omega
        subst this
        exact ⟨m, Nat.le_max_right N' m, hm⟩
    else
      -- q' is not prime, so primes < q' + 1 are exactly primes < q'.
      refine ⟨N', fun p hp hprim => ?_⟩
      -- p < q' + 1 and IsPrime p, but q' is not prime, so p ≠ q', so p < q'.
      match Nat.lt_or_ge p q' with
      | .inl hlt => exact hN' p hlt hprim
      | .inr hge =>
        -- p ≥ q' and p < q' + 1 forces p = q', but q' isn't prime: contradiction.
        exfalso
        have : p = q' := by omega
        subst this
        exact hprime hprim
end

/-- **The main reduction: Conjecture A implies Mullin's Conjecture.**

    The proof proceeds by strong induction on the prime q:

    1. **Inductive hypothesis**: every prime p < q appears in the sequence.
    2. **Collect witnesses**: by `exists_bound`, extract a uniform stage N
       beyond which all primes below q have appeared (uses classical choice).
    3. **Apply Conjecture A**: obtain n ≥ N with q ∣ (prod n + 1).
    4. **Invoke `captures_target`**: at stage n, all primes < q have appeared
       (since n ≥ N ≥ mₚ for each p), so seq(n + 1) = q.

    The only non-constructive ingredient is step 2 (extracting witnesses
    from existential hypotheses via classical choice). Everything else —
    the definitions, the sequence properties, and the Euclid argument at
    the heart of `captures_target` — is fully constructive. -/
theorem conjectureA_implies_mullin : ConjectureA → MullinConjecture := by
  intro hA
  -- We prove ∀ q, IsPrime q → ∃ n, seq n = q by strong induction on q.
  --
  -- Technique: prove the stronger ∀ k q, q ≤ k → IsPrime q → ∃ n, seq n = q
  -- by ordinary induction on k. This gives strong induction on q by taking k = q.
  unfold MullinConjecture
  suffices ∀ k q, q ≤ k → IsPrime q → ∃ n, seq n = q by
    intro q hq; exact this q q (Nat.le_refl q) hq
  intro k
  induction k with
  | zero =>
    -- q ≤ 0 but IsPrime q requires q ≥ 2: contradiction.
    intro q hle hq; exact absurd hq.1 (by omega)
  | succ k ih =>
    intro q hle hq
    -- Either q ≤ k (handled directly by ih) or q = k + 1 (interesting case).
    match Nat.lt_or_ge q (k + 1) with
    | .inl hlt =>
      -- q < k + 1, i.e., q ≤ k: apply the induction hypothesis directly.
      exact ih q (by omega) hq
    | .inr _ =>
      -- q ≥ k + 1 and q ≤ k + 1, so q = k + 1. This is the real case.
      -- Step 1: By ih, every prime p < q appears in the sequence.
      have appears : ∀ p, p < q → IsPrime p → ∃ n, seq n = p := by
        intro p hpq hp; exact ih p (by omega) hp
      -- Step 2: Collect witnesses into a uniform bound N (classical step).
      obtain ⟨N, hN⟩ := exists_bound q appears
      -- Step 3: By Conjecture A, there exists n ≥ N with q ∣ (prod n + 1).
      obtain ⟨n, hn_ge, hn_dvd⟩ := hA q hq N
      -- Step 4: At stage n, all primes < q have appeared (n ≥ N ≥ each witness).
      have hall : ∀ p, p < q → IsPrime p → ∃ m, m ≤ n ∧ seq m = p := by
        intro p hpq hp
        obtain ⟨m, hm, hseqm⟩ := hN p hpq hp
        exact ⟨m, by omega, hseqm⟩
      -- By the capture lemma, seq(n + 1) = q. Done!
      exact ⟨n + 1, captures_target hq hn_dvd hall⟩

-- Axiom usage: 'conjectureA_implies_mullin' depends on propext, Quot.sound,
-- Classical.choice.  Classical.choice comes from `exists_bound`, where we
-- extract witnesses from existential hypotheses and decide `IsPrime q'`.
-- All definitions (seq, prod, aux) and their basic properties (seq_isPrime,
-- seq_injective) remain fully constructive — see Parts 1–4.

-- ============================================================================
-- PART 6: CONJECTURE A IS FALSE — AND THE CORRECTED HITTING HYPOTHESIS
--
-- A surprising discovery during formalization: Conjecture A as stated above
-- is *provably false*. The problem: it requires q ∣ (prod n + 1) for every
-- prime q, including q = 2. But 2 = seq 0 divides every prod n (since prod n
-- is a product starting with 2), so 2 can never divide prod n + 1 (a number
-- can't divide two consecutive naturals).
--
-- This means `conjectureA_implies_mullin` is vacuously true (False → anything).
--
-- The fix: condition on q *not appearing* in the sequence. If q never appears,
-- then q doesn't divide any prod n (we prove this), so the "consecutive
-- divisibility" obstruction vanishes, and the hitting requirement becomes
-- meaningful. This gives the corrected **Hitting Hypothesis**, which we show
-- implies Mullin's Conjecture via the same capture-lemma argument.
-- ============================================================================

/-! ## Conjecture A is false -/

/-- **Conjecture A is provably false.**

    The counterexample is q = 2. Since 2 = seq 0 divides every running product
    prod n (it's the first factor), 2 divides prod n for all n. But then
    prod n + 1 is odd, so 2 ∤ (prod n + 1). This contradicts Conjecture A's
    requirement that 2 ∣ (prod n + 1) for arbitrarily large n.

    The implication `conjectureA_implies_mullin` is therefore vacuously true:
    it says "if False then Mullin's Conjecture", which is trivially valid. -/
theorem conjectureA_false : ¬ConjectureA := by
  unfold ConjectureA
  intro hA
  -- 2 is prime (it's seq 0)
  have h2_prime : IsPrime 2 := by rw [← seq_zero]; exact seq_isPrime 0
  -- Apply Conjecture A with q = 2, N = 0 to get some n with 2 ∣ (prod n + 1)
  obtain ⟨n, _, hdvd⟩ := hA 2 h2_prime 0
  -- But 2 = seq 0 divides prod n (since 0 ≤ n)
  have h2_dvd : 2 ∣ prod n := by
    have := seq_dvd_prod 0 n (by omega)
    rw [seq_zero] at this
    exact this
  -- A number ≥ 2 can't divide two consecutive naturals
  exact not_dvd_consec (by omega : 2 ≤ 2) h2_dvd hdvd

/-! ## The corrected Hitting Hypothesis -/

/-- Two distinct primes are coprime.

    If p and q are both prime and p ≠ q, then gcd(p, q) = 1.

    Proof: let d = gcd(p, q). Then d ∣ p (so d = 1 or d = p, since p is prime)
    and d ∣ q (so d = 1 or d = q, since q is prime). If d = p and d = q then
    p = q, contradicting our hypothesis. So d = 1. -/
private theorem coprime_of_distinct_primes {p q : Nat} (hp : IsPrime p) (hq : IsPrime q)
    (hne : p ≠ q) : Nat.Coprime p q := by
  unfold Nat.Coprime
  -- d = gcd(p, q) divides both p and q
  have hd_dvd_p := Nat.gcd_dvd_left p q
  have hd_dvd_q := Nat.gcd_dvd_right p q
  -- Since p is prime, d = 1 or d = p
  have h1 := hp.2 _ hd_dvd_p
  -- Since q is prime, d = 1 or d = q
  have h2 := hq.2 _ hd_dvd_q
  -- If d = p and d = q then p = q, contradiction
  match h1, h2 with
  | .inl h, _ => exact h
  | _, .inl h => exact h
  | .inr hp', .inr hq' =>
    -- d = p and d = q, so p = q
    exfalso; exact hne (hp'.symm ▸ hq')

/-- If a prime q never appears in the Euclid–Mullin sequence,
    then q does not divide any running product prod n.

    By induction on n:
    - Base: prod 0 = 2. If q ∣ 2, then q = 2, but seq 0 = 2 = q: contradiction.
    - Step: prod(n+1) = prod n * seq(n+1). If q ∣ prod n * seq(n+1):
      since q ≠ seq(n+1) (q never appears) and both are prime, they are coprime.
      By the coprime divisibility lemma, q ∣ prod n, contradicting the IH. -/
theorem prime_not_in_seq_not_dvd_prod {q : Nat} (hq : IsPrime q)
    (hne : ∀ m, seq m ≠ q) : ∀ n, ¬(q ∣ prod n) := by
  intro n
  induction n with
  | zero =>
    -- prod 0 = 2. If q ∣ 2 then q ≤ 2 and q ≥ 2, so q = 2 = seq 0.
    intro hdvd
    have hle : q ≤ 2 := Nat.le_of_dvd (by omega) hdvd
    have hge : 2 ≤ q := hq.1
    have : q = 2 := by omega
    exact hne 0 (by rw [seq_zero]; exact this.symm)
  | succ n ih =>
    -- prod(n+1) = prod n * seq(n+1)
    rw [prod_succ]
    intro hdvd
    -- q and seq(n+1) are distinct primes (q ≠ seq(n+1) since q never appears)
    have hne_succ : q ≠ seq (n + 1) := fun h => hne (n + 1) h.symm
    have hcop := coprime_of_distinct_primes hq (seq_isPrime (n + 1)) hne_succ
    -- Since gcd(q, seq(n+1)) = 1 and q ∣ prod n * seq(n+1), we get q ∣ prod n
    have := hcop.dvd_of_dvd_mul_right hdvd
    exact ih this

/-- **The Hitting Hypothesis** (corrected version of Conjecture A):
    for every prime q that *never appears* in the Euclid–Mullin sequence,
    and for every bound N, there exists n ≥ N such that q ∣ (prod n + 1).

    The condition "q never appears" removes the obstruction that killed
    Conjecture A: consumed primes divide the running product, blocking them
    from dividing prod n + 1. Non-appearing primes face no such obstruction.

    Combined with the observation that Mullin's Conjecture is equivalent to
    "every prime either appears or doesn't" (with the "doesn't" case being
    impossible if HH holds), this implies Mullin's Conjecture.

    See `docs/routes_to_conjecture_a.md` for strategies to prove this. -/
def HittingHypothesis : Prop :=
  ∀ q, IsPrime q → (∀ m, seq m ≠ q) → ∀ N, ∃ n, N ≤ n ∧ q ∣ (prod n + 1)

/-! ## A weaker, tail-only hitting hypothesis -/

/-- **Tail Hitting Hypothesis** (weaker than HH):
    once all primes below q have appeared by some stage N, if q never appears
    then q divides a later Euclid number.

    This is strictly weaker than `HittingHypothesis`, which asks for hits
    beyond *every* bound N. Here we only require a hit past a stage that already
    contains all primes below q — which is all that the capture lemma needs. -/
def TailHittingHypothesis : Prop :=
  ∀ q, IsPrime q → ∀ N,
    (∀ p, p < q → IsPrime p → ∃ m, m ≤ N ∧ seq m = p) →
    (∀ m, seq m ≠ q) →
    ∃ n, N ≤ n ∧ q ∣ (prod n + 1)

/-! ## Relations between hitting hypotheses -/

/-- **HH implies TailHH.**

    `HittingHypothesis` already guarantees a hit past *every* bound N for any
    prime that never appears, so it immediately implies the tail-only version. -/
theorem hh_implies_tailHH : HittingHypothesis → TailHittingHypothesis := by
  intro hH q hq N _ hne
  exact hH q hq hne N

section
open Classical

/-- **The corrected reduction: Hitting Hypothesis implies Mullin's Conjecture.**

    For any prime q, either q appears in the sequence (and we're done) or
    q never appears. In the latter case, the Hitting Hypothesis gives us
    n with q ∣ (prod n + 1), and the capture lemma (from Part 5) gives
    seq(n+1) = q — contradicting the assumption that q never appears.

    The proof uses Classical.em (excluded middle) for the case split
    "either q appears or it doesn't", plus the same strong induction and
    capture lemma from Part 5. -/
theorem hh_implies_mullin : HittingHypothesis → MullinConjecture := by
  intro hH
  unfold MullinConjecture
  -- Strong induction on q (same technique as conjectureA_implies_mullin)
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
      -- Classical.em gives us this case split.
      match em (∃ n, seq n = q) with
      | .inl hexists => exact hexists
      | .inr hnotexists =>
        -- q never appears. Extract "∀ m, seq m ≠ q" from ¬∃.
        have hne : ∀ m, seq m ≠ q := by
          intro m heq; exact hnotexists ⟨m, heq⟩
        -- By IH, every prime p < q appears.
        have appears : ∀ p, p < q → IsPrime p → ∃ n, seq n = p :=
          fun p hpq hp => ih p (by omega) hp
        -- Collect into a uniform bound N.
        obtain ⟨N, hN⟩ := exists_bound q appears
        -- By HH, pick n ≥ N with q ∣ (prod n + 1).
        obtain ⟨n, hn_ge, hn_dvd⟩ := hH q hq hne N
        -- All primes < q appeared by stage n.
        have hall : ∀ p, p < q → IsPrime p → ∃ m, m ≤ n ∧ seq m = p := by
          intro p hpq hp
          obtain ⟨m, hm, hseqm⟩ := hN p hpq hp
          exact ⟨m, by omega, hseqm⟩
        -- Capture lemma: seq(n+1) = q.
        have := captures_target hq hn_dvd hall
        -- But we assumed q never appears — contradiction!
        exact absurd ⟨n + 1, this⟩ hnotexists

end

/-- If q is prime and q does not divide b, then q and b are coprime.

    gcd(q, b) divides q, so (since q is prime) it's 1 or q.
    If it were q, then q ∣ b, contradicting our hypothesis. So it's 1. -/
theorem coprime_of_prime_not_dvd {q b : Nat} (hq : IsPrime q)
    (hndvd : ¬(q ∣ b)) : Nat.Coprime q b := by
  unfold Nat.Coprime
  have hd_dvd_q := Nat.gcd_dvd_left q b
  have hd_dvd_b := Nat.gcd_dvd_right q b
  match hq.2 _ hd_dvd_q with
  | .inl h => exact h
  | .inr h => exact absurd (h ▸ hd_dvd_b) hndvd

end Mullin
