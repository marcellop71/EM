-- We only need Lean's built-in core library — no Mathlib, no external dependencies.
import Init

/-!
# Euclid's Theorem — Fully Constructive Proof

A formalization of Euclid's original theorem (Elements, Book IX, Proposition 20):
given any finite collection of prime numbers, there exists a prime not in
that collection.

This is the classic "there are infinitely many primes" result, stated in its
original constructive form: we don't just prove more primes *exist* abstractly,
we *construct* a new one from any given list.

**What "fully constructive" means:** this proof avoids the `Classical.choice`
axiom entirely. Every existential witness is computed, not assumed. The only
axioms used are `propext` (propositions that are logically equivalent are equal)
and `Quot.sound` (quotient soundness), both of which are part of Lean's
trusted core and are not "classical" in the logic sense.

**How to read this file if you're not a Lean expert:**
- `def` introduces a definition (a function or value).
- `theorem` introduces a statement we prove. Everything after `by` is the proof.
- `∣` means "divides" (e.g., `d ∣ n` means "d divides n").
- `∧` means "and", `∨` means "or", `¬` means "not".
- `∃ x, P x` means "there exists an x such that P(x)".
- `∀ x, P x` means "for all x, P(x)".
- `omega` is a tactic that solves linear arithmetic goals automatically.
- Lines starting with `--` are comments (like this one!).

## References

* Hardy, M., Woodgold, C. "Prime Simplicity",
  Mathematical Intelligencer 31 (2009), 44–52
* Euclid, Elements, Book IX, Proposition 20
-/

namespace Euclid

-- ============================================================================
-- PART 1: DEFINITIONS
-- We need three things: a notion of "prime", a way to multiply a list of
-- numbers together, and a way to find the smallest factor of a number.
-- ============================================================================

/-! ## Definitions -/

/-- A natural number is prime if it is at least 2 and its only divisors are
    1 and itself.

    For example, 7 is prime because `2 ≤ 7` and the only numbers that
    divide 7 are 1 and 7. Meanwhile, 6 is not prime because 2 divides 6
    (and 2 is neither 1 nor 6). -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

/-- Product of a list of natural numbers.

    Examples:
    - `listProd [2, 3, 5] = 2 * 3 * 5 = 30`
    - `listProd [] = 1` (the empty product is 1, by convention)

    This is defined recursively: the product of an empty list is 1,
    and the product of `x :: xs` is `x * listProd xs`. -/
def listProd : List Nat → Nat
  | [] => 1
  | x :: xs => x * listProd xs

/-- Find the smallest factor of `n` starting the search from `k`.

    This does trial division: it checks k, k+1, k+2, ... in order.
    - If `k` divides `n`, return `k` (found a factor!).
    - If `k` doesn't divide `n`, try `k + 1`.
    - If `k ≥ n`, give up and return `n` itself (n is its own smallest factor).

    The `termination_by n - k` tells Lean this function terminates because
    `n - k` strictly decreases at each recursive call (k increases toward n).

    For example:
    - `minFacFrom 15 2` tries 2 (no), then 3 (yes!) → returns 3.
    - `minFacFrom 7 2` tries 2 (no), 3 (no), 4 (no), 5 (no), 6 (no),
       then k=7 ≥ n=7 → returns 7 (it's prime!). -/
def minFacFrom (n k : Nat) : Nat :=
  if h : k < n then
    if k ∣ n then k
    else minFacFrom n (k + 1)
  else n
termination_by n - k

/-- The smallest factor of `n` that is at least 2.

    We simply start the search from 2. If n ≥ 2, this will always return
    a factor of n between 2 and n (inclusive). When n is prime, it returns n. -/
def minFac (n : Nat) : Nat := minFacFrom n 2

-- ============================================================================
-- PART 2: PROPERTIES OF listProd
-- We prove two key facts about our list product:
-- (a) If every number in the list is positive, the product is positive.
-- (b) Every element of the list divides the product.
-- ============================================================================

/-! ## Properties of listProd -/

/-- If every number in a list is positive (> 0), then their product is positive.

    This is proved by induction on the list:
    - Base case (empty list): the product is 1, which is positive.
    - Inductive case (p :: ps'): the product is p * listProd ps'.
      Since p > 0 (by hypothesis) and listProd ps' > 0 (by induction),
      their product is positive. -/
theorem listProd_pos (ps : List Nat) (hp : ∀ p ∈ ps, 0 < p) : 0 < listProd ps := by
  induction ps with
  | nil =>
    -- Empty list: listProd [] = 1 > 0
    exact Nat.one_pos
  | cons p ps' ih =>
    -- listProd (p :: ps') = p * listProd ps'
    show 0 < p * listProd ps'
    -- p > 0 because p is in the list; listProd ps' > 0 by induction hypothesis
    exact Nat.mul_pos (hp p (.head ps')) (ih (fun q hq => hp q (.tail p hq)))

/-- If `a` is in the list `ps`, then `a` divides `listProd ps`.

    Intuitively obvious: if a is one of the factors, it divides the product.

    Proved by induction on the list:
    - Base case: `a ∈ []` is impossible.
    - Inductive case: `ps = p :: ps'`, and `a ∈ p :: ps'` in two ways:
      - `a` is the head (a = p): then a divides p * listProd ps' trivially.
      - `a` is in the tail (a ∈ ps'): by induction, a ∣ listProd ps',
        and listProd ps' divides p * listProd ps', so by transitivity a
        divides the whole product. -/
theorem dvd_listProd_of_mem {a : Nat} {ps : List Nat} (h : a ∈ ps) : a ∣ listProd ps := by
  induction ps with
  | nil =>
    -- a ∈ [] is impossible — this case is vacuously true
    exact absurd h (List.not_mem_nil)
  | cons p ps' ih =>
    -- Need to show: a ∣ p * listProd ps'
    show a ∣ p * listProd ps'
    cases h with
    | head =>
      -- Case a = p: a divides a * (anything)
      exact Nat.dvd_mul_right a (listProd ps')
    | tail _ h' =>
      -- Case a ∈ ps': by IH a ∣ listProd ps', and listProd ps' ∣ p * listProd ps'
      exact Nat.dvd_trans (ih h') (Nat.dvd_mul_left (listProd ps') p)

-- ============================================================================
-- PART 3: PROPERTIES OF minFacFrom
-- We prove three fundamental properties of our trial-division search:
-- (a) The result actually divides n.
-- (b) The result is at least k (the starting point).
-- (c) The result is minimal: no divisor of n in [k, ...) is smaller.
--
-- All three proofs follow the same pattern: unfold the definition of
-- minFacFrom and case-split on the two `if` branches, using recursion
-- for the case where we increment k.
-- ============================================================================

/-! ## Properties of minFacFrom -/

/-- The value returned by `minFacFrom n k` actually divides `n`.

    Proof by well-founded recursion on `n - k`:
    - If `k ≥ n`: we return `n`, which trivially divides itself.
    - If `k < n` and `k ∣ n`: we return `k`, which divides `n` by assumption.
    - If `k < n` and `k ∤ n`: we recurse with `k + 1`, and by induction
      the result still divides `n`. -/
theorem minFacFrom_dvd (n k : Nat) (_hkn : k ≤ n) : minFacFrom n k ∣ n := by
  unfold minFacFrom
  split
  case isTrue hlt =>
    -- k < n: we check if k divides n
    split
    case isTrue hdvd =>
      -- k ∣ n: we return k, which divides n
      exact hdvd
    case isFalse =>
      -- k ∤ n: recurse with k + 1
      exact minFacFrom_dvd n (k + 1) (by omega)
  case isFalse =>
    -- k ≥ n: we return n, and n ∣ n
    exact Nat.dvd_refl n
termination_by n - k

/-- The value returned by `minFacFrom n k` is at least `k`.

    We never return anything smaller than where we started searching.

    Proof by well-founded recursion on `n - k`:
    - If `k ≥ n`: we return `n ≥ k`.
    - If `k < n` and `k ∣ n`: we return `k` itself.
    - If `k < n` and `k ∤ n`: we recurse with `k + 1`, and the result
      is ≥ k + 1 > k. -/
theorem k_le_minFacFrom (n k : Nat) (hkn : k ≤ n) : k ≤ minFacFrom n k := by
  unfold minFacFrom
  split
  case isTrue hlt =>
    split
    case isTrue =>
      -- Return k: clearly k ≤ k
      exact Nat.le_refl k
    case isFalse =>
      -- Recurse with k+1: result ≥ k+1 ≥ k
      have := k_le_minFacFrom n (k + 1) (by omega); omega
  case isFalse =>
    -- Return n: and k ≤ n
    omega
termination_by n - k

/-- Minimality: if `m ≥ k` and `m` divides `n`, then `minFacFrom n k ≤ m`.

    In other words, minFacFrom finds the *smallest* divisor in [k, n].

    Proof by well-founded recursion on `n - k`:
    - If `k ≥ n`: we return `n`, and `n ≤ m` because `m ∣ n` and `m > 0`.
    - If `k < n` and `k ∣ n`: we return `k`, and `k ≤ m` by hypothesis.
    - If `k < n` and `k ∤ n`: since `k ∤ n` but `m ∣ n`, we know `k ≠ m`,
      so `m ≥ k + 1`. We recurse with `k + 1` and the result is still ≤ m. -/
theorem minFacFrom_min (n k m : Nat) (hkn : k ≤ n) (hkm : k ≤ m) (hm : m ∣ n) :
    minFacFrom n k ≤ m := by
  unfold minFacFrom
  split
  case isTrue hlt =>
    split
    case isTrue =>
      -- Return k: and k ≤ m by hypothesis
      exact hkm
    case isFalse hndvd =>
      -- k ∤ n but m ∣ n, so k ≠ m, meaning m ≥ k + 1; recurse
      have : k ≠ m := fun h => hndvd (h ▸ hm)
      exact minFacFrom_min n (k + 1) m (by omega) (by omega) hm
  case isFalse =>
    -- Return n: since m ∣ n and m ≥ k ≥ 1, we have n ≤ m... wait,
    -- actually m ∣ n means m ≤ n, and we return n. But we need n ≤ m.
    -- Since k ≥ n (from `isFalse`) and k ≤ m, we get n ≤ m.
    omega
termination_by n - k

-- ============================================================================
-- PART 4: minFac IS PRIME
-- The key insight: the smallest factor ≥ 2 of any number ≥ 2 must be prime.
-- Why? If it had a nontrivial divisor, that divisor would be an even smaller
-- factor, contradicting minimality.
-- ============================================================================

/-! ## minFac is prime -/

/-- `minFac n` divides `n` (just a convenient wrapper around `minFacFrom_dvd`
    with k = 2). -/
theorem minFac_dvd (n : Nat) (hn : 2 ≤ n) : minFac n ∣ n :=
  minFacFrom_dvd n 2 (by omega)

/-- `minFac n ≥ 2` when `n ≥ 2` (wrapper around `k_le_minFacFrom` with k = 2). -/
theorem two_le_minFac (n : Nat) (hn : 2 ≤ n) : 2 ≤ minFac n :=
  k_le_minFacFrom n 2 (by omega)

/-- `minFac n` is minimal: any divisor of `n` that is ≥ 2 is ≥ minFac n. -/
theorem minFac_min' (n m : Nat) (hn : 2 ≤ n) (hm : 2 ≤ m) (hmd : m ∣ n) :
    minFac n ≤ m :=
  minFacFrom_min n 2 m (by omega) hm hmd

/-- **The smallest factor ≥ 2 of any n ≥ 2 is prime.**

    This is the heart of the proof machinery. The argument:

    Let q = minFac(n). We know q ≥ 2 and q ∣ n. We must show q is prime,
    i.e., every divisor d of q satisfies d = 1 or d = q.

    Take any d with d ∣ q. We split into two cases:

    - **d < 2:** Since d divides q and q > 0, we have d > 0, so d = 1.
    - **d ≥ 2:** Since d ∣ q and q ∣ n, by transitivity d ∣ n. But q is the
      *smallest* divisor of n that is ≥ 2, so q ≤ d. Combined with d ≤ q
      (since d ∣ q), we get d = q. -/
theorem minFac_isPrime (n : Nat) (hn : 2 ≤ n) : IsPrime (minFac n) := by
  -- First, establish that minFac n ≥ 2
  have h2 := two_le_minFac n hn
  -- Now prove both parts of IsPrime: (1) 2 ≤ minFac n, (2) divisors are 1 or self
  refine ⟨h2, fun d hd => ?_⟩
  -- d ∣ minFac n implies d ≤ minFac n (since minFac n > 0)
  have hd_le : d ≤ minFac n := Nat.le_of_dvd (by omega) hd
  -- Case split: is d < 2 or d ≥ 2?
  match Nat.lt_or_ge d 2 with
  | .inl hd_small =>
    -- Case d < 2:
    -- d divides minFac n which is ≥ 2 > 0, so d ≠ 0, meaning d ≥ 1.
    -- Combined with d < 2, we get d = 1.
    left
    have hd_pos : d ≠ 0 := by
      intro he; subst he         -- assume d = 0
      obtain ⟨k, hk⟩ := hd      -- then 0 * k = minFac n, i.e., 0 = minFac n
      omega                      -- contradicts minFac n ≥ 2
    omega                        -- d ≠ 0 and d < 2, so d = 1
  | .inr hd_ge =>
    -- Case d ≥ 2:
    -- d ∣ minFac n and minFac n ∣ n, so d ∣ n (by transitivity)
    right
    have hd_dvd_n : d ∣ n := Nat.dvd_trans hd (minFac_dvd n hn)
    -- By minimality of minFac: since d ≥ 2 and d ∣ n, minFac n ≤ d
    have := minFac_min' n d hn hd_ge hd_dvd_n
    -- But we also know d ≤ minFac n, so d = minFac n
    omega

/-- **Square root bound**: if minFac n < n (i.e., n is composite), then
    (minFac n)² ≤ n. This is because n = minFac(n) * e where e ≥ minFac(n)
    (by minimality), so minFac(n)² ≤ minFac(n) * e = n.

    This is extremely useful for primality checking: to verify that n is prime,
    it suffices to check that no integer from 2 to √n divides n. -/
theorem minFac_sq_le (n : Nat) (hn : 2 ≤ n) (hlt : minFac n < n) :
    minFac n * minFac n ≤ n := by
  have hdvd := minFac_dvd n hn
  obtain ⟨e, he⟩ := hdvd
  -- he : n = minFac n * e
  -- We need e ≥ 2 (e = 0 gives n = 0; e = 1 gives n = minFac n, contradicting hlt)
  have he_ge : 2 ≤ e := by
    match e with | 0 => omega | 1 => omega | _ + 2 => omega
  -- e divides n: n = minFac n * e, so e ∣ n
  have he_dvd : e ∣ n := by rw [he]; exact Nat.dvd_mul_left e (minFac n)
  -- By minimality of minFac: minFac n ≤ e
  have h_le := minFac_min' n e hn he_ge he_dvd
  -- Therefore minFac n * minFac n ≤ minFac n * e = n
  calc minFac n * minFac n
      ≤ minFac n * e := Nat.mul_le_mul_left (minFac n) h_le
    _ = n := he.symm

/-- **Primality criterion via square root bound**: if `n ≥ 2` and no integer
    `k` with `2 ≤ k` and `k * k ≤ n` divides `n`, then `n` is prime in the
    sense that `minFac n = n`.  Proved constructively (no `by_contra`). -/
theorem minFac_eq_self_of_no_small_dvd (n : Nat) (hn : 2 ≤ n)
    (h : ∀ k : Nat, 2 ≤ k → k * k ≤ n → ¬(k ∣ n)) : minFac n = n := by
  -- minFac n ≤ n since it divides n
  have hle : minFac n ≤ n := Nat.le_of_dvd (by omega) (minFac_dvd n hn)
  -- Either minFac n = n (done) or minFac n < n (derive contradiction)
  match Nat.eq_or_lt_of_le hle with
  | .inl heq => exact heq
  | .inr hlt =>
    exact absurd (minFac_dvd n hn)
      (h (minFac n) (two_le_minFac n hn) (minFac_sq_le n hn hlt))

-- ============================================================================
-- PART 5: EUCLID'S THEOREM
-- The grand finale. Given any list of primes, we construct a new prime
-- not in the list. The idea (from Euclid, ~300 BCE):
--
--   Take primes p₁, p₂, ..., pₙ. Form the number N = p₁ * p₂ * ... * pₙ + 1.
--   N has some prime factor q. But q cannot be any of the pᵢ, because each pᵢ
--   divides the product p₁ * ... * pₙ, while q divides N = product + 1. If q
--   were some pᵢ, it would divide both product and product + 1, hence divide
--   their difference 1 — impossible for a prime.
--
-- NOTE: Euclid did NOT claim that N itself is prime! He only claimed that N
-- has a prime factor not in the original list. (N = 2*3*5*7*11*13 + 1 = 30031
-- = 59 * 509 is a classic counterexample to the common misstatement.)
-- ============================================================================

/-! ## Euclid's Theorem -/

/-- A prime number cannot divide 1.

    Proof: if p ∣ 1 then p ≤ 1 (since 1 is the dividend), but p ≥ 2
    (since p is prime). Contradiction. -/
theorem isPrime_not_dvd_one {p : Nat} (hp : IsPrime p) : ¬(p ∣ 1) := by
  intro h
  have h1 := hp.1                          -- 2 ≤ p (p is prime)
  have h2 := Nat.le_of_dvd Nat.one_pos h   -- p ≤ 1 (p divides 1)
  omega                                     -- 2 ≤ p and p ≤ 1: contradiction!

/-- **Euclid's theorem** (original constructive form): for any finite list of
primes, there exists a prime not in the list.

Given primes p₁, ..., pₙ, the witness is the smallest prime factor of
p₁ * ... * pₙ + 1. The proof is fully constructive and uses no classical
axioms. -/
theorem euclid (ps : List Nat) (hp : ∀ p ∈ ps, IsPrime p) :
    ∃ q, IsPrime q ∧ q ∉ ps := by

  -- ── Step 1: Form the "Euclid number" N = p₁ * p₂ * ... * pₙ + 1 ──
  let N := listProd ps + 1

  -- ── Step 2: Show N ≥ 2, so its smallest factor is a well-defined prime ──
  -- First, the product is positive (all primes are ≥ 2 > 0)
  have hprod_pos := listProd_pos ps (fun p hp' => by have := (hp p hp').1; omega)
  -- Therefore N = product + 1 ≥ 1 + 1 = 2
  have hN : 2 ≤ N := by omega
  -- So minFac(N) is prime (by our earlier theorem)
  have hq_prime := minFac_isPrime N hN

  -- ── Step 3: Show minFac(N) is NOT in the original list ──
  -- We provide minFac(N) as our witness, with its primality already proved
  refine ⟨minFac N, hq_prime, ?_⟩
  -- Now we must prove: minFac N ∉ ps
  -- We do this by contradiction: assume minFac(N) ∈ ps and derive absurdity
  intro hq_mem

  -- Since minFac(N) is in the list, it divides the product p₁ * ... * pₙ
  have hq_dvd_prod : minFac N ∣ listProd ps := dvd_listProd_of_mem hq_mem

  -- Since minFac(N) is a factor of N, it divides N
  have hq_dvd_N : minFac N ∣ N := minFac_dvd N hN

  -- If minFac(N) divides both N and the product, it divides their difference:
  -- N - product = (product + 1) - product = 1
  have hq_dvd_one : minFac N ∣ 1 := by
    have h := Nat.dvd_sub hq_dvd_N hq_dvd_prod
    have heq : N - listProd ps = 1 := by omega
    rw [heq] at h
    exact h

  -- But minFac(N) is prime, and a prime cannot divide 1. Contradiction!
  exact isPrime_not_dvd_one hq_prime hq_dvd_one

-- Axiom usage: 'Euclid.euclid' depends on [propext, Quot.sound] only.
-- propext : (a ↔ b) → a = b     (proposition extensionality)
-- Quot.sound : a ≈ b → ⟦a⟧ = ⟦b⟧  (quotient soundness)
--
-- Notably ABSENT: Classical.choice. This proof is fully constructive —
-- every existential claim comes with a computed witness.

end Euclid
