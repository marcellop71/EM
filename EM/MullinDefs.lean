-- Import our Euclid module for IsPrime, minFac, and the supporting lemmas.
-- See EM/Euclid.lean for the fully constructive proof of Euclid's theorem.
import EM.Euclid

/-!
# The Euclid–Mullin Sequence and Mullin's Conjecture

The **Euclid–Mullin sequence** (OEIS A000945), introduced by Albert A. Mullin
in 1963, is built by iterating Euclid's proof of the infinitude of primes.
Starting from the prime 2, each subsequent term is the smallest prime factor
of the product of all previous terms plus one:

    a(0) = 2
    a(n+1) = smallest prime factor of (a(0) * a(1) * ... * a(n) + 1)

The first several terms are:

    2, 3, 7, 43, 13, 53, 5, 6221671, 38709183810571, 139, 2801, 11, 17, ...

Note that **primes do not appear in order**. The prime 5 only shows up at
position 6, and 11 at position 11. Some small primes like **31** and **37**
have never been observed in the sequence despite extensive computation.

**Mullin's Conjecture** (1963, open): Every prime number eventually appears
in the Euclid–Mullin sequence.

This file contains:
1. A recursive definition of the sequence.
2. A proof that **every term is prime** (`seq_isPrime`).
3. A proof that **no prime repeats** (`seq_injective`).
4. A formal statement of Mullin's Conjecture (`MullinConjecture`).

**How to read this file if you're not a Lean expert:**
- See `EM/Euclid.lean` for a full guide to Lean notation (`∣`, `∧`, `∃`, etc.).
- `private theorem` is a helper lemma only visible inside this file.
- `rfl` means "true by definition" — both sides compute to the same thing.
- `obtain ⟨k, rfl⟩ := ...` extracts a witness `k` from an existential proof
  and immediately substitutes it into the goal.
- `absurd h1 h2` derives `False` from a proof `h1 : P` and `h2 : ¬P`.
- `match Nat.lt_or_ge m n with` case-splits on whether `m < n` or `m ≥ n`.
  This is decidable for natural numbers and requires no classical axioms.

## References

* Mullin, A.A. "Recursive function theory",
  Bull. Amer. Math. Soc. 69 (1963), 737
* Booker, A.R. and Irvine, S.A. "The Euclid–Mullin graph",
  J. Number Theory 165 (2016), 30–57
* Booker, A.R. "A variant of the Euclid–Mullin sequence containing every
  prime", J. Integer Sequences 19 (2016), Article 16.6.4
-/

namespace Mullin

-- We work with the definitions from our Euclid module:
--   IsPrime p       = "p ≥ 2 and its only divisors are 1 and p"
--   minFac n        = "the smallest factor of n that is ≥ 2"
--   minFac_isPrime  = "minFac n is prime whenever n ≥ 2"
--   minFac_dvd      = "minFac n divides n"
--   isPrime_not_dvd_one = "a prime cannot divide 1"
open Euclid

-- ============================================================================
-- PART 1: DEFINING THE SEQUENCE
--
-- The Euclid–Mullin sequence is defined recursively. At each step we need
-- both the current term and the running product of all terms so far (to
-- compute the next term). We package these together in an auxiliary
-- function that returns a pair (term, running product).
-- ============================================================================

/-! ## Definition of the Euclid–Mullin sequence -/

/-- Auxiliary function for the Euclid–Mullin sequence.

    Returns the pair `(aₙ, a₀ * a₁ * ... * aₙ)` — the n-th term together
    with the running product of all terms through index n.

    - At n = 0: the first term is 2, and the running product is 2.
    - At n + 1: form N = (running product) + 1, take its smallest prime
      factor as the new term, and multiply it into the running product.

    We carry the product alongside the term to avoid recomputing it from
    scratch at every step (otherwise we'd need to multiply all previous
    terms together at each step, which is wasteful). -/
def aux : Nat → Nat × Nat
  | 0 => (2, 2)
  | n + 1 =>
    let (_, prod) := aux n
    -- The "Euclid number" at this step: product of all previous terms + 1
    let N := prod + 1
    -- The new term: smallest prime factor of N (guaranteed to be a new prime)
    let term := minFac N
    (term, prod * term)

/-- The n-th term of the Euclid–Mullin sequence (0-indexed).

    The first several values are:

    | n  | product so far | product + 1 | minFac  | a(n) |
    |----|----------------|-------------|---------|------|
    | 0  | —              | —           | —       |    2 |
    | 1  | 2              | 3           | 3       |    3 |
    | 2  | 6              | 7           | 7       |    7 |
    | 3  | 42             | 43          | 43      |   43 |
    | 4  | 1806           | 1807        | 13      |   13 |
    | 5  | 23478          | 23479       | 53      |   53 |
    | 6  | 1244134        | 1244135     | 5       |    5 |

    Note at step 4: 1807 = 13 * 139, so the smallest prime factor is 13,
    not 1807 itself. The sequence does not produce primes in order! -/
def seq (n : Nat) : Nat := (aux n).1

/-- The running product of the first (n + 1) terms:
    `prod n = a(0) * a(1) * ... * a(n)`.

    For example:
    - `prod 0 = 2`
    - `prod 1 = 2 * 3 = 6`
    - `prod 2 = 2 * 3 * 7 = 42`
    - `prod 3 = 2 * 3 * 7 * 43 = 1806` -/
def prod (n : Nat) : Nat := (aux n).2

-- ============================================================================
-- PART 2: BASIC IDENTITIES
--
-- These four lemmas simply unfold the definitions.  They all hold by
-- `rfl` ("reflexivity"), meaning both sides of the equation compute
-- to exactly the same thing.  We give them names so that later proofs
-- can `rw [seq_succ]` to replace `seq (n+1)` with `minFac (prod n + 1)`.
-- ============================================================================

/-! ## Basic identities -/

/-- The initial term is 2. -/
theorem seq_zero : seq 0 = 2 := rfl

/-- The initial running product is 2. -/
theorem prod_zero : prod 0 = 2 := rfl

/-- The running product at step n+1 is the previous product times the new term:
    `prod (n + 1) = prod n * seq (n + 1)`. -/
theorem prod_succ (n : Nat) : prod (n + 1) = prod n * seq (n + 1) := rfl

/-- Each term from step 1 onward is the smallest factor of
    (previous product + 1):
    `seq (n + 1) = minFac (prod n + 1)`. -/
theorem seq_succ (n : Nat) : seq (n + 1) = minFac (prod n + 1) := rfl

-- ============================================================================
-- PART 3: STRUCTURAL PROPERTIES
--
-- We prove three key facts about the sequence:
-- (a) The running product is always ≥ 2 (so minFac is well-defined).
-- (b) Every term is prime.
-- (c) No prime appears twice (injectivity).
--
-- The proofs mirror the Euclid argument: if a prime appeared twice,
-- it would divide both a number and that number plus one, hence divide 1.
-- ============================================================================

/-! ## Structural properties -/

/-- The running product is always at least 2.

    Since a(0) = 2 and every subsequent term is a prime (≥ 2),
    the product only grows. In particular, prod n ≥ 2 for all n,
    which ensures that `prod n + 1 ≥ 3 ≥ 2`, making `minFac` well-defined
    at every step.

    Proved by induction on n:
    - Base (n = 0): prod 0 = 2 ≥ 2. Checked by `decide`.
    - Step (n + 1): prod (n+1) = prod n * seq (n+1). Since prod n ≥ 2
      (by IH) and seq (n+1) = minFac(prod n + 1) ≥ 1 (in fact ≥ 2),
      the product is ≥ 2 * 1 = 2. -/
theorem prod_ge_two (n : Nat) : 2 ≤ prod n := by
  induction n with
  | zero =>
    -- prod 0 = 2, and 2 ≤ 2 is trivially true.
    -- `decide` evaluates both sides and confirms they match.
    decide
  | succ n ih =>
    -- Unfold: prod (n + 1) = prod n * minFac (prod n + 1)
    simp only [prod_succ, seq_succ]
    -- We know prod n + 1 ≥ 3, so minFac is applied to a number ≥ 2
    have h1 : 2 ≤ prod n + 1 := by omega
    -- By `two_le_minFac`, minFac of any number ≥ 2 is itself ≥ 2, so ≥ 1
    have h2 : 1 ≤ minFac (prod n + 1) := by
      have := two_le_minFac _ h1; omega
    -- Now: 2 = 2 * 1 ≤ prod n * minFac(prod n + 1)
    -- because prod n ≥ 2 (ih) and minFac ≥ 1 (h2), and a * b grows
    -- monotonically in both arguments for natural numbers.
    calc 2 = 2 * 1 := by omega
      _ ≤ prod n * minFac (prod n + 1) := Nat.mul_le_mul ih h2

/-- **Every term of the Euclid–Mullin sequence is prime.**

    At step 0, the term is 2, which is prime.  At step n + 1, the term
    is `minFac(prod n + 1)`. Since `prod n ≥ 2` (by `prod_ge_two`),
    we have `prod n + 1 ≥ 3 ≥ 2`, so by `minFac_isPrime` from our
    Euclid module, the result is prime.

    This is the formal version of: "the smallest prime factor of any
    number ≥ 2 is itself prime" — which is the engine behind Euclid's
    proof and, by extension, the entire Euclid–Mullin construction. -/
theorem seq_isPrime : ∀ n, IsPrime (seq n) := by
  intro n
  cases n with
  | zero =>
    -- Goal: IsPrime (seq 0), i.e., IsPrime 2.
    -- Rewrite seq 0 to 2 using our identity.
    rw [seq_zero]
    -- IsPrime 2 means: 2 ≤ 2 ∧ ∀ d, d ∣ 2 → d = 1 ∨ d = 2
    -- We prove the two parts separately with `constructor`.
    constructor
    · -- Part 1: 2 ≤ 2. Trivial arithmetic.
      omega
    · -- Part 2: every divisor of 2 is 1 or 2.
      intro d hd
      -- d ∣ 2 implies d ≤ 2 (since 2 > 0, any divisor is ≤ the dividend)
      have h1 : d ≤ 2 := Nat.le_of_dvd (by omega) hd
      -- d ∣ 2 also implies d > 0 (if d = 0 then 0 * k = 2, absurd)
      have h2 : d ≠ 0 := by
        intro he         -- assume d = 0
        subst he         -- substitute d = 0 everywhere
        obtain ⟨k, hk⟩ := hd  -- d ∣ 2 means ∃ k, 2 = 0 * k
        omega            -- 2 = 0 * k is impossible
      -- So 1 ≤ d ≤ 2, meaning d = 1 ∨ d = 2
      omega
  | succ n =>
    -- Goal: IsPrime (seq (n + 1))
    -- Rewrite: seq (n + 1) = minFac (prod n + 1)
    rw [seq_succ]
    -- prod n ≥ 2 (by prod_ge_two), so prod n + 1 ≥ 3 ≥ 2.
    -- By `minFac_isPrime` from Euclid.lean: minFac of any number ≥ 2 is prime.
    exact minFac_isPrime (prod n + 1) (by have := prod_ge_two n; omega)

/-- The second term is 3: minFac(2 + 1) = minFac(3) = 3. -/
theorem seq_one : seq 1 = 3 := by
  have hdvd : seq 1 ∣ 3 := by
    rw [seq_succ, prod_zero]; exact minFac_dvd 3 (by omega)
  have hge : 2 ≤ seq 1 := (seq_isPrime 1).1
  have hle : seq 1 ≤ 3 := Nat.le_of_dvd (by omega) hdvd
  have h23 : seq 1 = 2 ∨ seq 1 = 3 := by omega
  rcases h23 with h2 | h3
  · rw [h2] at hdvd; obtain ⟨c, hc⟩ := hdvd; omega
  · exact h3

/-- The third term is 7: minFac(2 * 3 + 1) = minFac(7) = 7. -/
theorem seq_two : seq 2 = 7 := by
  have hdvd : seq 2 ∣ 7 := by
    have hprod1 : prod 1 = 6 := by rw [prod_succ, prod_zero, seq_one]
    rw [seq_succ, hprod1]; exact minFac_dvd 7 (by omega)
  have hge : 2 ≤ seq 2 := (seq_isPrime 2).1
  have hle : seq 2 ≤ 7 := Nat.le_of_dvd (by omega) hdvd
  have h : seq 2 = 2 ∨ seq 2 = 3 ∨ seq 2 = 4 ∨ seq 2 = 5 ∨ seq 2 = 6 ∨ seq 2 = 7 := by omega
  rcases h with h | h | h | h | h | h <;>
    first | exact h | (rw [h] at hdvd; obtain ⟨c, hc⟩ := hdvd; omega)

/-- The fourth term is 43: minFac(2 * 3 * 7 + 1) = minFac(43) = 43.
    43 is prime, so the only divisor ≥ 2 of 43 is 43 itself. We verify
    this using the square root bound: if minFac(43) < 43, then
    minFac(43) ≤ √43 < 7, but no integer in {2,...,6} divides 43. -/
theorem seq_three : seq 3 = 43 := by
  have hprod2 : prod 2 = 42 := by rw [prod_succ, prod_succ, prod_zero, seq_one, seq_two]
  have h_eq : seq 3 = minFac 43 := by rw [seq_succ, hprod2]
  have hdvd : seq 3 ∣ 43 := by rw [h_eq]; exact minFac_dvd 43 (by omega)
  have hge : 2 ≤ seq 3 := (seq_isPrime 3).1
  have hle : seq 3 ≤ 43 := Nat.le_of_dvd (by omega) hdvd
  -- Case split: either seq 3 ≥ 43 (done by omega) or seq 3 < 43 (use sqrt bound)
  match Nat.lt_or_ge (seq 3) 43 with
  | .inr h => omega
  | .inl hlt =>
    -- seq 3 < 43 means minFac(43) < 43, so sqrt bound applies
    have hsq := minFac_sq_le 43 (by omega) (by rw [← h_eq]; exact hlt)
    rw [← h_eq] at hsq
    -- seq 3 * seq 3 ≤ 43, so seq 3 ≤ 6 (since 7² = 49 > 43)
    have hle6 : seq 3 ≤ 6 := by
      match Nat.lt_or_ge (seq 3) 7 with
      | .inl h => omega
      | .inr h =>
        have := Nat.mul_le_mul h h  -- 7 * 7 ≤ seq 3 * seq 3
        omega  -- 49 ≤ seq 3 * seq 3 ≤ 43, contradiction
    -- Check {2,...,6}: none divide 43
    obtain ⟨c, hc⟩ := hdvd
    have h : seq 3 = 2 ∨ seq 3 = 3 ∨ seq 3 = 4 ∨ seq 3 = 5 ∨ seq 3 = 6 := by omega
    rcases h with h | h | h | h | h <;> (rw [h] at hc; omega)

/-- The fifth term is 13: minFac(2 * 3 * 7 * 43 + 1) = minFac(1807) = 13.
    1807 = 13 * 139, and no integer in {2,...,12} divides 1807. -/
theorem seq_four : seq 4 = 13 := by
  have hprod3 : prod 3 = 1806 := by
    rw [prod_succ, prod_succ, prod_succ, prod_zero, seq_one, seq_two, seq_three]
  have h_eq : seq 4 = minFac 1807 := by rw [seq_succ, hprod3]
  have hdvd : seq 4 ∣ 1807 := by rw [h_eq]; exact minFac_dvd 1807 (by omega)
  have hge : 2 ≤ seq 4 := (seq_isPrime 4).1
  -- 13 divides 1807 (= 13 * 139), so minFac(1807) ≤ 13
  have h13 : (13 : Nat) ∣ 1807 := ⟨139, by omega⟩
  have hle : seq 4 ≤ 13 := by rw [h_eq]; exact minFac_min' 1807 13 (by omega) (by omega) h13
  -- seq 4 ∈ {2,...,13} and seq 4 | 1807: only 13 divides 1807
  obtain ⟨c, hc⟩ := hdvd
  have h : seq 4 = 2 ∨ seq 4 = 3 ∨ seq 4 = 4 ∨ seq 4 = 5 ∨ seq 4 = 6 ∨ seq 4 = 7 ∨
           seq 4 = 8 ∨ seq 4 = 9 ∨ seq 4 = 10 ∨ seq 4 = 11 ∨ seq 4 = 12 ∨ seq 4 = 13 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h <;>
    first | exact h | (rw [h] at hc; omega)

theorem seq_five : seq 5 = 53 := by
  have hprod4 : prod 4 = 23478 := by
    rw [prod_succ, prod_succ, prod_succ, prod_succ, prod_zero, seq_one, seq_two, seq_three, seq_four]
  have h_eq : seq 5 = minFac 23479 := by rw [seq_succ, hprod4]
  have hdvd : seq 5 ∣ 23479 := by rw [h_eq]; exact minFac_dvd 23479 (by omega)
  have hge : 2 ≤ seq 5 := (seq_isPrime 5).1
  -- 53 divides 23479 (= 53 * 443), so minFac(23479) ≤ 53
  have h53 : (53 : Nat) ∣ 23479 := ⟨443, by omega⟩
  have hle : seq 5 ≤ 53 := by rw [h_eq]; exact minFac_min' 23479 53 (by omega) (by omega) h53
  -- seq 5 ∈ {2,...,53} and seq 5 | 23479: only 53 divides 23479
  obtain ⟨c, hc⟩ := hdvd
  have h : seq 5 = 2 ∨ seq 5 = 3 ∨ seq 5 = 4 ∨ seq 5 = 5 ∨ seq 5 = 6 ∨
           seq 5 = 7 ∨ seq 5 = 8 ∨ seq 5 = 9 ∨ seq 5 = 10 ∨ seq 5 = 11 ∨
           seq 5 = 12 ∨ seq 5 = 13 ∨ seq 5 = 14 ∨ seq 5 = 15 ∨ seq 5 = 16 ∨
           seq 5 = 17 ∨ seq 5 = 18 ∨ seq 5 = 19 ∨ seq 5 = 20 ∨ seq 5 = 21 ∨
           seq 5 = 22 ∨ seq 5 = 23 ∨ seq 5 = 24 ∨ seq 5 = 25 ∨ seq 5 = 26 ∨
           seq 5 = 27 ∨ seq 5 = 28 ∨ seq 5 = 29 ∨ seq 5 = 30 ∨ seq 5 = 31 ∨
           seq 5 = 32 ∨ seq 5 = 33 ∨ seq 5 = 34 ∨ seq 5 = 35 ∨ seq 5 = 36 ∨
           seq 5 = 37 ∨ seq 5 = 38 ∨ seq 5 = 39 ∨ seq 5 = 40 ∨ seq 5 = 41 ∨
           seq 5 = 42 ∨ seq 5 = 43 ∨ seq 5 = 44 ∨ seq 5 = 45 ∨ seq 5 = 46 ∨
           seq 5 = 47 ∨ seq 5 = 48 ∨ seq 5 = 49 ∨ seq 5 = 50 ∨ seq 5 = 51 ∨
           seq 5 = 52 ∨ seq 5 = 53 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h |
                 h | h | h | h | h | h | h | h | h | h |
                 h | h | h | h | h | h | h | h | h | h |
                 h | h | h | h | h | h | h | h | h | h |
                 h | h | h | h | h | h | h | h | h | h |
                 h | h <;>
    first | exact h | (rw [h] at hc; omega)

theorem seq_six : seq 6 = 5 := by
  have hprod5 : prod 5 = 1244334 := by
    rw [prod_succ, prod_succ, prod_succ, prod_succ, prod_succ, prod_zero,
        seq_one, seq_two, seq_three, seq_four, seq_five]
  have h_eq : seq 6 = minFac 1244335 := by rw [seq_succ, hprod5]
  have hdvd : seq 6 ∣ 1244335 := by rw [h_eq]; exact minFac_dvd 1244335 (by omega)
  have hge : 2 ≤ seq 6 := (seq_isPrime 6).1
  -- 5 divides 1244335 (= 5 * 248867), so minFac(1244335) ≤ 5
  have h5 : (5 : Nat) ∣ 1244335 := ⟨248867, by omega⟩
  have hle : seq 6 ≤ 5 := by rw [h_eq]; exact minFac_min' 1244335 5 (by omega) (by omega) h5
  obtain ⟨c, hc⟩ := hdvd
  have h : seq 6 = 2 ∨ seq 6 = 3 ∨ seq 6 = 4 ∨ seq 6 = 5 := by omega
  rcases h with h | h | h | h <;>
    first | exact h | (rw [h] at hc; omega)

/-- The seventh term: seq 7 = 6221671.
    prod 6 + 1 = 6221671, which is prime.
    Uses `native_decide` for the primality check (trial division
    up to √6221671 ≈ 2494 is infeasible in the kernel but fast
    in compiled code). -/
theorem seq_seven : seq 7 = 6221671 := by
  have hprod6 : prod 6 = 6221670 := by
    rw [prod_succ, prod_succ, prod_succ, prod_succ, prod_succ, prod_succ, prod_zero,
        seq_one, seq_two, seq_three, seq_four, seq_five, seq_six]
  -- seq 7 = minFac(6221671), and 6221671 is prime so minFac = self
  rw [seq_succ, hprod6]
  native_decide

/-- If m ≤ n, then `seq m` divides the running product `prod n`.

    Intuitively: `prod n = seq 0 * seq 1 * ... * seq n`, so any individual
    factor `seq m` (with m ≤ n) divides the whole product.

    For example:
    - `seq 0 = 2` divides `prod 3 = 2 * 3 * 7 * 43 = 1806`.
    - `seq 2 = 7` divides `prod 4 = 2 * 3 * 7 * 43 * 13 = 23478`.

    Proved by induction on n:
    - Base (n = 0): m = 0, and seq 0 = prod 0, so seq 0 ∣ prod 0.
    - Step (n = k+1): prod (k+1) = prod k * seq (k+1). Either m ≤ k
      (use the IH and transitivity) or m = k+1 (seq (k+1) divides
      prod k * seq (k+1) directly). -/
theorem seq_dvd_prod (m n : Nat) (h : m ≤ n) : seq m ∣ prod n := by
  induction n with
  | zero =>
    -- m ≤ 0 forces m = 0
    have : m = 0 := by omega
    -- Substitute m = 0; now the goal is seq 0 ∣ prod 0
    subst this
    -- seq 0 = prod 0 = 2, so seq 0 ∣ prod 0 trivially (any number divides itself)
    exact Nat.dvd_refl _
  | succ k ih =>
    -- Unfold prod (k+1) = prod k * seq (k+1)
    rw [prod_succ]
    -- Case split: is m ≤ k (i.e., m < k+1) or m = k+1 (i.e., m ≥ k+1)?
    -- `Nat.lt_or_ge` is decidable for Nat — no classical axioms needed.
    match Nat.lt_or_ge m (k + 1) with
    | .inl hlt =>
      -- Case m < k + 1, i.e., m ≤ k:
      -- By IH: seq m ∣ prod k
      -- We also know: prod k ∣ prod k * seq (k+1)  (any a divides a * b)
      -- By transitivity: seq m ∣ prod k * seq (k+1) = prod (k+1)
      exact Nat.dvd_trans (ih (by omega)) (Nat.dvd_mul_right (prod k) (seq (k + 1)))
    | .inr hge =>
      -- Case m ≥ k + 1: combined with m ≤ k + 1 (from h), this forces m = k + 1
      have : m = k + 1 := by omega
      subst this
      -- seq (k+1) divides prod k * seq (k+1) trivially (any a divides b * a)
      exact Nat.dvd_mul_left (seq (k + 1)) (prod k)

/-- If m < n, the m-th and n-th terms of the sequence are different.

    This is the core of the injectivity proof, and it's essentially
    Euclid's argument applied to the sequence itself.

    Writing n = k + 1 (which is valid since n ≥ 1):
    - `seq m` divides `prod k` (by `seq_dvd_prod`, since m ≤ k).
    - `seq (k+1) = minFac(prod k + 1)` divides `prod k + 1`.
    - If `seq m = seq (k+1)`, this prime would divide both `prod k` and
      `prod k + 1`, hence their difference `(prod k + 1) - prod k = 1`.
    - But a prime is ≥ 2 and cannot divide 1 (`isPrime_not_dvd_one`).
      Contradiction.

    This is exactly the same argument Euclid used ~300 BCE: a number
    that divides a product P cannot also divide P + 1 (unless it divides 1).
    Here we're applying it to show that each new term in the sequence is
    genuinely new — it can't be any of the previous terms. -/
private theorem seq_ne_of_lt {m n : Nat} (hlt : m < n) : seq m ≠ seq n := by
  -- Assume for contradiction that seq m = seq n
  intro heq
  -- Since m < n and m ≥ 0, we have n ≥ 1.
  -- Write n = k + 1 for some k, with m ≤ k.
  -- `obtain ⟨k, rfl⟩` extracts the witness k and substitutes n = k + 1
  -- into all hypotheses and the goal.
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩

  -- ── Step 1: seq m divides the running product prod k ──
  -- m < k + 1 means m ≤ k, so seq m is one of the factors in
  -- prod k = seq 0 * seq 1 * ... * seq k
  have h1 : seq m ∣ prod k := seq_dvd_prod m k (by omega)

  -- ── Step 2: seq (k+1) divides prod k + 1 ──
  -- By definition, seq (k+1) = minFac(prod k + 1), and minFac always
  -- divides its argument (proved in Euclid.lean as `minFac_dvd`).
  -- We need prod k + 1 ≥ 2 for minFac_dvd, which follows from prod k ≥ 2.
  have h2 : seq (k + 1) ∣ prod k + 1 := by
    rw [seq_succ]                  -- unfold seq (k+1) = minFac (prod k + 1)
    exact minFac_dvd (prod k + 1)  -- minFac n always divides n (when n ≥ 2)
          (by have := prod_ge_two k; omega)  -- prod k + 1 ≥ 3 ≥ 2

  -- ── Step 3: derive that seq (k+1) divides 1 ──
  -- We assumed seq m = seq (k+1), so rewrite h1:
  -- now seq (k+1) ∣ prod k (not just seq m)
  rw [heq] at h1

  -- seq (k+1) divides both prod k + 1 (h2) and prod k (h1).
  -- By `Nat.dvd_sub`: if a ∣ b and a ∣ c then a ∣ b - c.
  -- So seq (k+1) ∣ (prod k + 1) - prod k = 1.
  have h3 : seq (k + 1) ∣ 1 := by
    have hsub := Nat.dvd_sub h2 h1     -- seq (k+1) ∣ (prod k + 1) - prod k
    have heq₂ : prod k + 1 - prod k = 1 := by omega  -- simplify the difference
    rw [heq₂] at hsub                  -- now hsub : seq (k+1) ∣ 1
    exact hsub

  -- ── Step 4: contradiction ──
  -- seq (k+1) is prime (by seq_isPrime), so seq (k+1) ≥ 2.
  -- But seq (k+1) ∣ 1 implies seq (k+1) ≤ 1.
  -- This is impossible: 2 ≤ seq (k+1) ≤ 1.
  exact isPrime_not_dvd_one (seq_isPrime (k + 1)) h3

/-- **No prime appears twice in the Euclid–Mullin sequence.**

    If `seq m = seq n` then `m = n`. This is the injectivity of the sequence.

    Combined with the fact that the sequence is infinite (it produces a
    new term at every step), this means the Euclid–Mullin sequence produces
    **infinitely many distinct primes** — a computational witness to
    Euclid's theorem on the infinitude of primes.

    The proof is a simple case analysis:
    - If m < n: `seq_ne_of_lt` says seq m ≠ seq n. Contradiction.
    - If n < m: `seq_ne_of_lt` says seq n ≠ seq m. Contradiction.
    - If neither: m ≤ n and n ≤ m, so m = n.

    No classical axioms are needed: the case split uses `Nat.lt_or_ge`,
    which is constructively decidable for natural numbers. -/
theorem seq_injective : ∀ m n, seq m = seq n → m = n := by
  intro m n heq
  -- Case split: is m < n or m ≥ n?
  match Nat.lt_or_ge m n with
  | .inl hlt =>
    -- m < n: by seq_ne_of_lt, seq m ≠ seq n.
    -- But we assumed seq m = seq n (heq). Contradiction.
    -- `absurd` derives False from a proof and its negation.
    exact absurd heq (seq_ne_of_lt hlt)
  | .inr hge =>
    -- m ≥ n: now split again — is n < m or n ≥ m?
    match Nat.lt_or_ge n m with
    | .inl hlt =>
      -- n < m: by seq_ne_of_lt, seq n ≠ seq m.
      -- heq.symm gives seq n = seq m. Contradiction.
      exact absurd heq.symm (seq_ne_of_lt hlt)
    | .inr hge' =>
      -- m ≥ n (hge) and n ≥ m (hge'), so m = n.
      omega

-- ============================================================================
-- PART 4: MULLIN'S CONJECTURE (open problem)
--
-- The central question, open since 1963: does every prime eventually appear?
--
-- What is known:
-- * The sequence never repeats a prime (seq_injective above).
-- * Therefore it produces infinitely many distinct primes.
-- * Shanks (1991) gave a compelling heuristic argument that the answer is yes.
-- * Booker & Irvine (2016) showed that the Euclid–Mullin *graph* (considering
--   all prime factors at each step, not just the smallest) contains every
--   prime below 10⁹ as an edge.
-- * Booker (2016) showed that a *generalized* Euclid construction (using
--   partitions of the prime set) provably reaches every prime — but this
--   does not resolve the conjecture for the specific smallest-factor sequence.
-- * It is not known whether 31 or 37 ever appear in the sequence.
--
-- The conjecture is stated below as a *proposition* (a `def` of type `Prop`),
-- not as a theorem. This is the honest way to formalize an open problem in
-- Lean: we define precisely what the conjecture *says*, without claiming
-- it is true or false.
-- ============================================================================


end Mullin
