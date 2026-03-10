import EM.LargeSieve

open Mullin Euclid MullinGroup RotorRouter

section StructuralLemmas

/-- **The running product is strictly increasing**: `prod m < prod n` for `m < n`.

    This is immediate from `prod_strictMono` (proved in EquidistSelfAvoidance.lean
    by induction: each `seq(n+1)` is prime hence ≥ 2, so multiplying by it
    strictly increases the product). -/
theorem prod_strictly_increasing {m n : ℕ} (h : m < n) : prod m < prod n :=
  prod_strictMono h

/-- **Euclid numbers are coprime to prior sequence terms**: if `k ≤ n`
    then `Nat.Coprime (seq k) (prod n + 1)`.

    Since `seq k ∣ prod n` (by `seq_dvd_prod`) and `seq k` is prime,
    if `seq k` also divided `prod n + 1` it would divide their difference 1.
    So `seq k ∤ prod n + 1`, and since `seq k` is prime this gives coprimality. -/
theorem euclid_number_coprime_seq (k n : ℕ) (h : k ≤ n) :
    Nat.Coprime (seq k) (prod n + 1) := by
  apply coprime_of_prime_not_dvd (seq_isPrime k)
  exact seq_not_dvd_prod_succ h

/-- **Sequence terms are pairwise distinct on any range**: the elements
    `{seq 0, seq 1, ..., seq n}` are pairwise distinct.

    This follows directly from `seq_injective`: the Euclid-Mullin sequence
    is injective, so distinct indices give distinct values. -/
theorem seq_pairwise_distinct :
    ∀ i j : ℕ, seq i = seq j → i = j :=
  seq_injective

/-- **The number of distinct sequence terms up to index n**: the image of
    `seq` on `Finset.range n` has cardinality exactly `n`, since `seq` is
    injective. This is useful for counting arguments in the sieve. -/
theorem seq_image_card (n : ℕ) :
    (Finset.image seq (Finset.range n)).card = n := by
  rw [Finset.card_image_of_injective _ (fun _ _ h => seq_injective _ _ h)]
  exact Finset.card_range n

/-- **Euclid number coprimality to all prior terms simultaneously**:
    `prod n + 1` is coprime to the running product `prod n`.

    This is a restatement of `aux_coprime_prod` with the arguments in the
    conventional order for sieve applications: gcd(prod n + 1, prod n) = 1. -/
theorem euclid_coprime_running_prod (n : ℕ) :
    Nat.Coprime (prod n + 1) (prod n) :=
  aux_coprime_prod n

/-- **Every prime factor of prod(n)+1 is new**: if `p` is prime and
    `p ∣ prod n + 1`, then `p ∉ {seq 0, ..., seq n}`.

    This is the key structural fact making the EM sequence infinite and
    supporting the sieve: each Euclid number introduces genuinely new
    prime factors that have never appeared before. -/
theorem prime_factor_of_euclid_not_in_range {p n : ℕ}
    (_hp : Nat.Prime p) (hdvd : p ∣ prod n + 1) :
    ∀ k ≤ n, seq k ≠ p := by
  intro k hk heq
  have : seq k ∣ prod n + 1 := heq ▸ hdvd
  exact seq_not_dvd_prod_succ hk this

/-- **Product lower bound for sieve applications**: `prod n ≥ 2^n`,
    which means for any modulus Q, the range [1, prod n] contains at
    least `2^n` integers — more than enough for the large sieve to
    produce nontrivial bounds once `n` is large relative to `Q`.

    This is a restatement of `prod_exponential_lower` highlighting
    the sieve-theoretic significance. -/
theorem prod_lower_bound_for_sieve (n : ℕ) : 2 ^ n ≤ prod n :=
  prod_exponential_lower n

end StructuralLemmas

/-! ## Summary (S49)

### New definitions (S49):
- `GaussConductorTransfer` : ALS → ArithLS (absorbing proved Farey spacing)

### Proved theorems (S49):
- `gct_implies_als_farey` : GCT implies ALSFareyImpliesArithLS
- `gauss_conductor_chain_mc` : GCT + ALS + ArithLSImpliesMMCSB → MC
- `gauss_conductor_small_threshold_mc` : above with Q₀ ≤ 11 → MC unconditionally
- `prod_strictly_increasing` : prod m < prod n for m < n
- `euclid_number_coprime_seq` : Coprime (seq k) (prod n + 1) for k ≤ n
- `seq_pairwise_distinct` : seq i = seq j → i = j
- `seq_image_card` : |image of seq on range(n)| = n
- `euclid_coprime_running_prod` : Coprime (prod n + 1) (prod n)
- `prime_factor_of_euclid_not_in_range` : prime factors of Euclid numbers are new
- `prod_lower_bound_for_sieve` : 2^n ≤ prod n

### Key insight (S49):
The `ALSFareyImpliesArithLS` open Prop decomposes into:
1. `GaussConductorTransfer` (open) — the Gauss sum + conductor argument
2. `farey_spacing_proved` (proved) — Farey separation ≥ 1/Q²
Since (2) is proved, only `GaussConductorTransfer` remains open, giving a cleaner
chain: `ALS →[GCT]→ ArithLS →[open]→ MMCSB →[proved]→ MC`.

### Structural lemmas for sieve (S49):
The sequence's built-in coprimality structure (consecutive integers share no
common factor) means every Euclid number introduces genuinely new primes.
Combined with the exponential growth of `prod n`, this makes the EM sequence
a natural input for sieve methods.
-/

-- ============================================================================
-- S50. DIVISIBILITY AND COPRIMALITY STRUCTURAL LEMMAS
-- ============================================================================

/-! ## S50: Running product divisibility and coprimality

This section proves foundational structural lemmas about the EM sequence's
divisibility and coprimality properties:

1. `prod_dvd_prod` : running product divisibility is monotone (m <= n => prod m | prod n)
2. `seq_succ_coprime_prod` : new EM terms are coprime to the running product
3. `seq_le_euclid_number` : sequence terms bounded by Euclid numbers
4. `euclid_coprime_factor_of_prod` : Euclid numbers coprime to factors of earlier products

These are structural consequences of the EM construction and require no
analytic input. They strengthen the sieve-theoretic toolkit from S49. -/

section DivisibilityCoprimality

/-- Running product divisibility: `prod m | prod n` for `m <= n`.
    By induction: `prod(n+1) = prod(n) * seq(n+1)`, so `prod(m) | prod(n)`
    implies `prod(m) | prod(n) * seq(n+1) = prod(n+1)`. -/
theorem prod_dvd_prod (m n : ℕ) (h : m ≤ n) : prod m ∣ prod n := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst this
    exact Nat.dvd_refl _
  | succ k ih =>
    rw [prod_succ]
    match Nat.lt_or_ge m (k + 1) with
    | .inl hlt =>
      exact Nat.dvd_trans (ih (by omega)) (Nat.dvd_mul_right (prod k) (seq (k + 1)))
    | .inr hge =>
      have : m = k + 1 := by omega
      subst this
      exact dvd_refl _

/-- New EM term is coprime to running product: `Nat.Coprime (seq (n+1)) (prod n)`.
    Since `seq(n+1) | prod(n)+1` and `seq(n+1)` is prime, if also `seq(n+1) | prod(n)`,
    then `seq(n+1) | 1`, contradicting primality. -/
theorem seq_succ_coprime_prod (n : ℕ) : Nat.Coprime (seq (n + 1)) (prod n) := by
  apply coprime_of_prime_not_dvd (seq_isPrime (n + 1))
  intro hdvd
  have hdvd_succ : seq (n + 1) ∣ (prod n + 1) := seq_dvd_succ_prod n
  have hge2 : 2 ≤ seq (n + 1) := (seq_isPrime (n + 1)).1
  -- seq(n+1) | prod n and seq(n+1) | prod n + 1
  -- gcd(prod n + 1, prod n) = 1 by aux_coprime_prod
  -- So seq(n+1) | gcd(prod n + 1, prod n) = 1
  have hcop := aux_coprime_prod n  -- Nat.gcd (prod n + 1) (prod n) = 1
  have : seq (n + 1) ∣ Nat.gcd (prod n + 1) (prod n) :=
    Nat.dvd_gcd hdvd_succ hdvd
  rw [hcop] at this
  exact absurd (Nat.le_of_dvd (by omega) this) (by omega)

/-- Sequence terms are bounded by Euclid numbers: `seq (n+1) <= prod n + 1`.
    Since `seq(n+1) = minFac(prod(n)+1)` and minFac divides its argument,
    `seq(n+1) <= prod(n)+1`. -/
theorem seq_le_euclid_number (n : ℕ) : seq (n + 1) ≤ prod n + 1 := by
  rw [seq_succ]
  have h2 : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
  exact Nat.le_of_dvd (by omega) (minFac_dvd (prod n + 1) h2)

/-- Euclid numbers are coprime to factors of earlier running products:
    if `q | prod m` and `m <= n`, then `Nat.Coprime q (prod n + 1)`. -/
theorem euclid_coprime_factor_of_prod {q m n : ℕ}
    (hq_dvd : q ∣ prod m) (hmn : m ≤ n) :
    Nat.Coprime q (prod n + 1) := by
  have hq_dvd_n : q ∣ prod n := Nat.dvd_trans hq_dvd (prod_dvd_prod m n hmn)
  have hcop := aux_coprime_prod n  -- Nat.Coprime (prod n + 1) (prod n)
  -- hcop : Nat.gcd (prod n + 1) (prod n) = 1
  -- We need: Nat.gcd q (prod n + 1) = 1
  -- Since q | prod n and gcd(prod n + 1, prod n) = 1, we get gcd(q, prod n + 1) = 1
  exact hcop.symm.coprime_dvd_left hq_dvd_n

end DivisibilityCoprimality

/-! ## Summary (S50)

### Proved theorems (S50):
- `prod_dvd_prod` : prod m | prod n for m <= n (induction)
- `seq_succ_coprime_prod` : Coprime (seq (n+1)) (prod n) (prime not dividing consecutive)
- `seq_le_euclid_number` : seq (n+1) <= prod n + 1 (minFac bound)
- `euclid_coprime_factor_of_prod` : q | prod m and m <= n => Coprime q (prod n + 1)

### Key insight (S50):
The running product `prod n` is monotone under divisibility, forming a divisibility
chain `prod 0 | prod 1 | prod 2 | ...`. Combined with the coprimality of consecutive
integers (`prod n + 1` coprime to `prod n`), this gives a strong structural framework:
any factor of any earlier running product is automatically coprime to any later Euclid
number. This is the algebraic backbone underlying all sieve applications to the EM sequence.
-/

/-! ## §51 Congruence and coprimality of EM sequence terms

Building on the divisibility chain from §50, we derive two further structural properties:

1. **Modular congruence**: The Euclid number `prod n + 1` is congruent to 1 modulo any
   earlier running product `prod m` (for `m ≤ n`). This is an immediate consequence of
   `prod_dvd_prod`.

2. **Pairwise coprimality**: Distinct terms `seq i` and `seq j` are coprime. This uses
   the fact that earlier terms divide the running product, while later terms are coprime
   to it (by `seq_succ_coprime_prod`).
-/

section CongruenceAndCoprimality

/-- Euclid numbers are congruent to 1 modulo earlier running products:
    `prod n + 1 ≡ 1 [MOD prod m]` for `m ≤ n`.
    Since `prod m ∣ prod n` (by `prod_dvd_prod`), we have
    `prod n + 1 - 1 = prod n` is divisible by `prod m`. -/
theorem euclid_cong_one_mod_earlier_prod (m n : ℕ) (h : m ≤ n) :
    Nat.ModEq (prod m) (prod n + 1) 1 := by
  rw [Nat.ModEq.comm]
  rw [Nat.modEq_iff_dvd' (by omega : 1 ≤ prod n + 1)]
  simp only [Nat.add_sub_cancel]
  exact prod_dvd_prod m n h

/-- Distinct EM sequence terms are coprime: `Nat.Coprime (seq i) (seq j)` for `i ≠ j`.
    WLOG `i < j`. Write `j = k + 1` with `i ≤ k`. Then:
    - `seq i ∣ prod k` (by `seq_dvd_prod`)
    - `Coprime (seq (k+1)) (prod k)` (by `seq_succ_coprime_prod`)
    So `Coprime (seq i) (seq j)` via `Nat.Coprime.coprime_dvd_right`. -/
theorem seq_coprime_of_distinct {i j : ℕ} (h : i ≠ j) :
    Nat.Coprime (seq i) (seq j) := by
  -- Reduce to i < j or j < i
  rcases Nat.lt_or_gt_of_ne h with hij | hji
  · -- Case i < j: write j = k + 1 with i ≤ k
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    -- seq i ∣ prod k since i ≤ k
    have hi_dvd : seq i ∣ prod k := seq_dvd_prod i k (by omega)
    -- Coprime (seq (k+1)) (prod k)
    have hcop : Nat.Coprime (seq (k + 1)) (prod k) := seq_succ_coprime_prod k
    -- Since seq i ∣ prod k and Coprime (seq (k+1)) (prod k),
    -- we get Coprime (seq (k+1)) (seq i)
    exact (hcop.coprime_dvd_right hi_dvd).symm
  · -- Case j < i: symmetric, swap and use commutativity
    exact (seq_coprime_of_distinct (Ne.symm h)).symm

end CongruenceAndCoprimality

/-! ## Summary (S51)

### Proved theorems (S51):
- `euclid_cong_one_mod_earlier_prod` : prod n + 1 ≡ 1 [MOD prod m] for m ≤ n
- `seq_coprime_of_distinct` : Coprime (seq i) (seq j) for i ≠ j

### Key insight (S51):
The Euclid-Mullin sequence has a remarkably rigid arithmetic structure: not only is
each term prime and distinct, but all terms are **pairwise coprime**. This means
distinct EM primes can never share a common factor — they live in independent parts
of the factorization lattice. The modular congruence `prod n + 1 ≡ 1 [MOD prod m]`
is the quantitative form of Euclid's argument: adding 1 to a product ensures the
result is coprime to every factor of that product.
-/

-- ============================================================================
-- S52. BVImpliesMMCSB DECOMPOSITION
-- ============================================================================

/-! ## §52 BVImpliesMMCSB Decomposition

The transfer `BombieriVinogradov -> MultiModularCSB` faces three independent
obstacles. We articulate each as a separate open Prop and prove that their
sequential composition yields `BVImpliesMMCSB`.

The three obstacles are:

1. **Population-to-Subsequence Transfer**: BV controls all primes in arithmetic
   progressions; we need the specific EM multipliers `seq(n+1) = minFac(prod(n)+1)`
   to inherit equidistribution of residues. This requires transferring from the full
   set of primes to the thin subsequence of least prime factors of Euclid numbers.

2. **Multiplier-to-Walk Bridge**: Even if individual multiplier character sums
   `sum_{n<N} chi(m(n))` cancel, the walk character sums `sum_{n<N} chi(w(n))`
   involve products `w(n) = prod_{k<n} m(k)`, making cancellation harder.
   This is a multiplicative random walk analysis.

3. **Averaged-to-Pointwise Lift**: BV gives averaged bounds (sum over q of errors);
   we need pointwise bounds for EACH q >= Q_0 individually. The doubly-exponential
   growth of `prod(N)` helps (any fixed q is eventually tiny relative to prod(N)),
   but the argument must be uniform in N.

We decompose `BVImpliesMMCSB` as:
```
BV ->[Obstacle 1]-> EMMultCharSumBound ->[Obstacles 2+3]-> MultiModularCSB
```

The first obstacle (BV to multiplier character sum bounds) is the sieve-theoretic
content. The second and third (multiplier sums to walk sums, with pointwise control)
are the harmonic analysis content.
-/

section BVDecomposition

/-- **EM Multiplier Character Sum Bound**: the EM multipliers `emMultUnit q n`
    satisfy character sum cancellation for all sufficiently large prime moduli.

    This is the natural intermediate between BV and MMCSB: it says that for
    non-trivial characters chi on `(ZMod q)^x`, the multiplier sums
    `sum_{n<N} chi(m(n))` are o(N).

    This is WEAKER than MMCSB (which bounds walk sums, not multiplier sums)
    and STRONGER than SieveEquidistribution (which gives counting bounds,
    not character sum bounds).

    The key point: multiplier character sums are LINEAR sums of chi-values,
    while walk character sums involve products. Linear sums are what BV/sieve
    methods naturally produce. -/
def EMMultCharSumBound : Prop :=
  ∃ Q₀ : ℕ, ∀ (q : Nat) [Fact (Nat.Prime q)], q ≥ Q₀ →
  ∀ (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ‖∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ)‖ ≤ ε * N

/-- **Obstacle 1: BV implies EM Multiplier Character Sum Bound**.

    The Bombieri-Vinogradov theorem controls the error in the prime counting
    function pi(x; q, a) for almost all moduli q <= sqrt(x)/(log x)^A.
    This Prop transfers that to character sum cancellation for the specific
    EM multipliers seq(n+1) = minFac(prod(n)+1).

    The transfer requires:
    (a) Relating the EM multipliers (least prime factors of Euclid numbers)
        to the set of all primes counted by pi(x; q, a).
    (b) Using the BV averaged bound to extract pointwise bounds for individual q.
        The doubly-exponential growth of prod(N) helps: for fixed q, eventually
        q << sqrt(prod(N)), placing q well within the BV range.
    (c) Converting from prime-counting equidistribution (pi(x; q, a) ~ pi(x)/phi(q))
        to character sum cancellation (sum chi(m(n)) = o(N)) via Fourier inversion
        on the group (ZMod q)^x.

    **Open Prop**: this is the sieve-theoretic heart of the BV approach.
    It requires tools from analytic number theory (Selberg sieve, Alladi's
    theorem on least prime factors) that are not in Mathlib. -/
def BVImpliesEMMultCSB : Prop :=
  BombieriVinogradov → EMMultCharSumBound

/-- **Obstacles 2+3: Multiplier Character Sum Bound implies MultiModularCSB**.

    Given cancellation of multiplier character sums (sum chi(m(n)) = o(N)),
    derive cancellation of walk character sums (sum chi(w(n)) = o(N)).

    Since `w(n+1) = w(n) * m(n)`, we have `chi(w(n)) = prod_{k<n} chi(m(k))`.
    The walk character sum is thus a sum of partial products of unit complex
    numbers. Even if the individual factors chi(m(n)) are equidistributed,
    the partial products can fail to cancel (this is the multiplicative
    random walk problem).

    However, the telescoping identity (proved in S37) gives:
    `sum_{n<N} chi(w(n)) * (chi(m(n)) - 1) = chi(w(N)) - chi(w(0))`

    This means: if chi(m(n)) != 1 often enough (which follows from multiplier
    equidistribution), the walk character sums cannot grow linearly.

    More precisely, this Prop combines:
    - The walk-multiplier telescoping bound (algebraic, proved in S37)
    - A pointwise extraction argument (from the averaged multiplier bound
      to a pointwise walk bound)

    **Open Prop**: the telescope gives norm <= 2, but we need the ratio
    sum chi(w(n)) / (sum of (chi(m(n))-1) terms) to be bounded. This
    requires showing that the denominator grows linearly, which needs
    quantitative equidistribution of multipliers away from ker(chi). -/
def MultCSBImpliesMMCSB : Prop :=
  EMMultCharSumBound → MultiModularCSB

/-- **Decomposition theorem**: the two sub-Props compose to give BVImpliesMMCSB.

    ```
    BV ->[BVImpliesEMMultCSB]-> EMMultCharSumBound ->[MultCSBImpliesMMCSB]-> MMCSB
    ```

    This is a trivial function composition: given BV, first apply the sieve
    transfer to get multiplier character sum bounds, then apply the walk
    bridge to get walk character sum bounds (= MMCSB). -/
theorem bv_decomposition_implies_mmcsb
    (h1 : BVImpliesEMMultCSB)
    (h2 : MultCSBImpliesMMCSB) :
    BVImpliesMMCSB :=
  fun hbv => h2 (h1 hbv)

/-- **Decomposed BV chain to MC**: BV + the two decomposed transfers + finite
    verification → Mullin's Conjecture.

    ```
    BV ->[h1]-> EMMultCSB ->[h2]-> MMCSB ->[mmcsb_implies_mc]-> MC
    ``` -/
theorem bv_decomposed_chain_mc
    (hbv : BombieriVinogradov)
    (h1 : BVImpliesEMMultCSB)
    (h2 : MultCSBImpliesMMCSB)
    (hfin : FiniteMCBelow (h2 (h1 hbv)).choose) :
    MullinConjecture :=
  mmcsb_implies_mc (h2 (h1 hbv)) hfin

/-- **Decomposed BV chain for small threshold**: if the decomposed transfers
    yield Q_0 <= 11, MC follows unconditionally. -/
theorem bv_decomposed_small_threshold_mc
    (hbv : BombieriVinogradov)
    (h1 : BVImpliesEMMultCSB)
    (h2 : MultCSBImpliesMMCSB)
    (hsmall : (h2 (h1 hbv)).choose ≤ 11) :
    MullinConjecture :=
  mmcsb_small_threshold_mc (h2 (h1 hbv)) hsmall

/-- **EMMultCSB is implied by StrongSieveEquidist** (modulo a Fourier bridge).

    StrongSieveEquidist gives window equidistribution of multiplier residues.
    Character sum cancellation follows by the Weyl criterion: if the fraction
    of multipliers hitting each unit a in (ZMod q)^x converges to 1/phi(q),
    then sum chi(m(n)) = o(N) for non-trivial chi (by orthogonality of characters).

    This connects the sieve route (S36-S39) with the BV decomposition route. -/
def StrongSieveImpliesMultCSB : Prop :=
  StrongSieveEquidist → EMMultCharSumBound

open Classical in
/-- **StrongSieveEquidist implies SieveEquidistribution**: window equidistribution
    (controlling every window of sufficient length) implies cumulative equidistribution
    (controlling the single window [0, N)).

    Proof: given ε > 0, apply SSE with ε' = ε/2, L₀ = 1. Get N₀ such that for all
    n₀ ≥ N₀ and L ≥ 1, the window [n₀, n₀+L) has hit count ≥ L·(1/φ − ε/2).
    The cumulative count on [0, N) is at least the count on [N₀, N), which by SSE
    is ≥ (N−N₀)·(1/φ − ε/2). For N large enough, this exceeds N·(1/φ − ε). -/
theorem strongSieveEquidist_implies_sieveEquidist (hsse : StrongSieveEquidist) :
    SieveEquidistribution := by
  intro q inst hq hne a ε hε
  haveI : Fact (Nat.Prime q) := inst
  set φ := (Finset.univ (α := (ZMod q)ˣ)).card with hφ_def
  -- Apply SSE with ε' = ε/2, L₀ = 1
  set ε' := ε / 2 with hε'_def
  have hε'_pos : 0 < ε' := by positivity
  obtain ⟨N₀, hN₀⟩ := hsse q hq hne a ε' hε'_pos 1 Nat.one_pos
  -- For N ≥ N₀, the window [N₀, N₀ + (N - N₀)) has count ≥ (N-N₀)·(1/φ - ε/2).
  -- The cumulative [0,N) count is at least as large.
  -- We need: (N-N₀)·(1/φ - ε/2) ≥ N·(1/φ - ε), i.e., N₀·(1/φ-ε/2) ≤ N·ε/2.
  -- Since 1/φ-ε/2 ≤ 1, it suffices to take N ≥ 2·N₀/ε.
  -- Choose N₁ so that both N₁ ≥ N₀ and N₀ ≤ N₁·(ε/2).
  -- Use N₁ = max(N₀, ⌈2·N₀/ε⌉ + 1).
  -- Simpler: pick N₁ = N₀ + ⌈N₀/ε⌉ · 2 + 1, but ceiling is complex.
  -- Just pick N₁ such that N₁ ≥ N₀ and N₁ · (ε/2) ≥ N₀ (real arithmetic).
  -- A clean choice: N₁ = N₀ + ⌈2·N₀/ε⌉.
  -- Actually, let's just existentially pick a large enough N₁ and do real arithmetic.
  refine ⟨N₀ + Nat.ceil (2 * N₀ / ε) + 1, fun N hN => ?_⟩
  -- Key: N ≥ N₀
  have hN_ge_N₀ : N₀ ≤ N := by omega
  -- Key: N > 0
  have hN_pos : 0 < N := by omega
  -- L = N - N₀ ≥ 1
  set L := N - N₀ with hL_def
  have hL_ge_1 : L ≥ 1 := by omega
  -- Apply SSE: window [N₀, N₀ + L) = [N₀, N)
  have hsse_app := hN₀ N₀ le_rfl L hL_ge_1
  -- The hit count in [N₀, N₀+L) ≥ L·(1/φ - ε')
  -- The cumulative hit count in [0,N) ≥ hit count in [N₀, N)
  -- Build injective map from window filter to cumulative filter
  have hcumul_ge_window :
      ((Finset.range L).filter (fun k => emMultUnit q hq hne (N₀ + k) = a)).card ≤
      ((Finset.range N).filter (fun n => emMultUnit q hq hne n = a)).card := by
    apply Finset.card_le_card_of_injOn (fun k => N₀ + k)
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk ⊢
      exact ⟨by rw [hL_def] at hk; omega, hk.2⟩
    · intro k₁ _ k₂ _ (h : N₀ + k₁ = N₀ + k₂); omega
  -- Now do the real arithmetic
  -- cumulative_hit ≥ hitW ≥ L·(1/φ - ε') ≥ N·(1/φ - ε)
  -- Step 1: cast cumulative ≥ window
  have h_ge_window : (((Finset.range N).filter (fun n => emMultUnit q hq hne n = a)).card : ℝ) ≥
      (((Finset.range L).filter (fun k => emMultUnit q hq hne (N₀ + k) = a)).card : ℝ) := by
    exact_mod_cast hcumul_ge_window
  -- Step 2: window bound from SSE
  have h_window_bound :
      (((Finset.range L).filter (fun k => emMultUnit q hq hne (N₀ + k) = a)).card : ℝ) ≥
      (L : ℝ) * (1 / ↑φ - ε') := hsse_app
  -- Step 3: show L·(1/φ - ε') ≥ N·(1/φ - ε)
  -- Goal: cumulative hit count ≥ N · (1/φ - ε)
  -- Chain: cumulative ≥ hitW ≥ L·(1/φ - ε/2) ≥ N·(1/φ - ε)
  -- For the last step: L·(1/φ - ε/2) = (N-N₀)·(1/φ-ε/2) ≥ N·(1/φ-ε)
  -- ⟺ N·(ε/2) ≥ N₀·(1/φ - ε/2), which holds since N₀·(1/φ-ε/2) ≤ N₀ ≤ N·(ε/2).
  have hL_cast : (L : ℝ) = (N : ℝ) - N₀ := by
    have : N = N₀ + L := by omega
    rw [this]; push_cast; ring
  have hφ_pos : (0 : ℝ) < φ := by
    have : 0 < φ := Finset.card_pos.mpr ⟨1, Finset.mem_univ _⟩
    exact Nat.cast_pos.mpr this
  have hinv_le_one : 1 / (φ : ℝ) ≤ 1 := by
    rw [div_le_one hφ_pos]; exact_mod_cast Finset.one_le_card.mpr ⟨1, Finset.mem_univ _⟩
  have hN_large : (N : ℝ) * ε ≥ 2 * N₀ := by
    have hceil : (Nat.ceil (2 * ↑N₀ / ε) : ℝ) ≥ 2 * N₀ / ε := Nat.le_ceil _
    have hN_ge_ceil : N ≥ Nat.ceil (2 * ↑N₀ / ε) + 1 := by omega
    have hN_cast : (N : ℝ) ≥ (Nat.ceil (2 * ↑N₀ / ε) : ℝ) + 1 := by exact_mod_cast hN_ge_ceil
    calc (N : ℝ) * ε ≥ (2 * ↑N₀ / ε + 1) * ε := by nlinarith
      _ = 2 * ↑N₀ + ε := by field_simp
      _ ≥ 2 * ↑N₀ := by linarith
  -- Final inequality chain
  calc (((Finset.range N).filter (fun n => emMultUnit q hq hne n = a)).card : ℝ)
      ≥ (((Finset.range L).filter (fun k => emMultUnit q hq hne (N₀ + k) = a)).card : ℝ) :=
        h_ge_window
    _ ≥ (L : ℝ) * (1 / ↑φ - ε') := h_window_bound
    _ ≥ (N : ℝ) * (1 / ↑φ - ε) := by rw [hL_cast, hε'_def]; nlinarith

/-- **The walk telescope bound from S37 constrains walk sums in terms of
    multiplier escape frequency**.

    For any non-trivial character chi, the telescoping identity gives:
    `|sum_{n<N} chi(w(n)) * (chi(m(n)) - 1)| <= 2`

    If the multiplier character values chi(m(n)) are not all 1 (i.e., not all
    in ker(chi)), then the terms (chi(m(n)) - 1) provide non-zero weights.
    The walk character sum is thus constrained by the inverse of the
    "escape density" (frequency of m(n) outside ker(chi)).

    This is the algebraic content already proved in `walk_telescope_norm_bound`
    (S37). The quantitative extraction from this bound to MMCSB requires the
    open `MultCSBImpliesMMCSB`. -/
theorem telescope_constrains_walk :
    ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    ∀ (χ : (ZMod q)ˣ →* ℂˣ),
    ∀ (N : ℕ),
    ‖∑ n ∈ Finset.range N,
      ((χ (emWalkUnit q hq hne n) : ℂ) * ((χ (emMultUnit q hq hne n) : ℂ) - 1))‖ ≤ 2 :=
  walk_telescope_norm_bound

/-! ### Sieve Equidistribution implies Multiplier Character Sum Bound

    The counting form of multiplier equidistribution (SieveEquidistribution) implies
    the character sum form (EMMultCharSumBound) by a Weyl-type argument.
    We decompose ∑ χ(m(n)) by fiber, use character orthogonality to subtract the
    mean, and bound the deviation via the triangle inequality. -/

/-- Auxiliary: for a nontrivial MonoidHom χ : (ZMod q)ˣ →* ℂˣ, the sum ∑ a, (χ a : ℂ) = 0.
    Uses the standard trick: pick b with χ(b) ≠ 1, then χ(b) · S = S implies S = 0. -/
private theorem unit_char_sum_eq_zero {q : ℕ} [Fact (Nat.Prime q)]
    (χ : (ZMod q)ˣ →* ℂˣ) (hχ : χ ≠ 1) :
    ∑ a : (ZMod q)ˣ, (χ a : ℂ) = 0 := by
  -- Since χ ≠ 1, there exists b with χ(b) ≠ 1
  have ⟨b, hb⟩ : ∃ b : (ZMod q)ˣ, χ b ≠ 1 := by
    by_contra h; push_neg at h; apply hχ
    ext a; simp [h a]
  -- The sum S satisfies χ(b) · S = S (by reindexing a ↦ b·a)
  set S := ∑ a : (ZMod q)ˣ, (χ a : ℂ)
  have hmul : (χ b : ℂ) * S = S := by
    simp only [S, Finset.mul_sum]
    exact Fintype.sum_bijective (b * ·) (Group.mulLeft_bijective b) _ _ (fun a => by
      simp only [map_mul, Units.val_mul])
  -- χ(b) ≠ 1 as complex, so (χ(b) - 1) · S = 0 gives S = 0
  have hb_ne : (χ b : ℂ) ≠ 1 := by
    intro h; apply hb; exact Units.val_injective h
  have hsub : ((χ b : ℂ) - 1) * S = 0 := by
    have : (χ b : ℂ) * S - S = 0 := sub_eq_zero.mpr hmul
    linear_combination this
  rcases mul_eq_zero.mp hsub with h | h
  · exact absurd (sub_eq_zero.mp h) hb_ne
  · exact h

/-- Auxiliary: the multiplier character sum decomposes as ∑_a χ(a) · V_N(a)
    where V_N(a) = #{n < N : m(n) = a}. -/
private theorem mult_char_sum_fiber {q : ℕ} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ) =
    ∑ a : (ZMod q)ˣ,
      (χ a : ℂ) * ((Finset.range N).filter (fun n => emMultUnit q hq hne n = a)).card := by
  rw [← Finset.sum_fiberwise (Finset.range N) (emMultUnit q hq hne)
      (fun n => (χ (emMultUnit q hq hne n) : ℂ))]
  congr 1; ext a
  rw [Finset.sum_filter]
  conv_lhs =>
    arg 2; ext n
    rw [show (if emMultUnit q hq hne n = a then (χ (emMultUnit q hq hne n) : ℂ) else 0) =
      (if emMultUnit q hq hne n = a then (χ a : ℂ) else 0) from by
        split_ifs with h
        · rw [h]
        · rfl]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- Auxiliary: the total multiplier hit count sums to N. -/
private theorem mult_hit_count_sum {q : ℕ} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (N : ℕ) :
    ∑ a : (ZMod q)ˣ,
      ((Finset.range N).filter (fun n => emMultUnit q hq hne n = a)).card = N := by
  -- Use card_eq_sum_card_fiberwise: #s = ∑ b ∈ t, #{a ∈ s | f a = b}
  have h := Finset.card_eq_sum_card_fiberwise
    (f := emMultUnit q hq hne) (s := Finset.range N) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_range] at h
  simpa using h.symm

/-- Auxiliary: ‖(χ a : ℂ)‖ = 1 for a MonoidHom χ : (ZMod q)ˣ →* ℂˣ. -/
private theorem unit_monoidHom_norm_one {q : ℕ} [Fact (Nat.Prime q)]
    (χ : (ZMod q)ˣ →* ℂˣ) (a : (ZMod q)ˣ) :
    ‖(χ a : ℂ)‖ = 1 := by
  have hfin : IsOfFinOrder a := isOfFinOrder_of_finite a
  have hfin' : IsOfFinOrder (χ a) := χ.isOfFinOrder hfin
  rw [isOfFinOrder_iff_pow_eq_one] at hfin'
  obtain ⟨n, hn, hpow⟩ := hfin'
  have hne : NeZero n := ⟨by omega⟩
  have hmem : (χ a) ∈ rootsOfUnity n ℂ := by
    rw [_root_.mem_rootsOfUnity]; exact hpow
  exact Complex.norm_eq_one_of_mem_rootsOfUnity hmem

/-- **SieveEquidistribution implies EMMultCharSumBound** (multiplier Weyl criterion).

    The counting form of multiplier equidistribution (SieveEquidistribution) implies
    the character sum form (EMMultCharSumBound) by Fourier decomposition on (ZMod q)ˣ.

    Proof: decompose ∑ χ(m(n)) = ∑_a χ(a) · V_N(a) where V_N(a) counts multipliers
    equal to a. Using χ nontrivial gives ∑ χ(a) = 0, so the sum equals
    ∑ χ(a) · (V_N(a) - N/φ(q)), which is bounded by triangle inequality. -/
theorem sieve_equidist_implies_mult_csb :
    SieveEquidistribution → EMMultCharSumBound := by
  intro hsieve
  -- Use Q₀ = 0 (SieveEquidistribution covers all primes)
  refine ⟨0, fun q inst hq_ge hq hne χ hχ ε hε => ?_⟩
  -- Let φ = number of units in (ZMod q)ˣ
  set φ := (Finset.univ : Finset (ZMod q)ˣ).card with hφ_def
  have hφ_pos : (0 : ℝ) < φ := by positivity
  -- Pick ε' = ε / φ² for SieveEquidistribution
  set ε' := ε / ((φ : ℝ) * φ) with hε'_def
  have hε'_pos : 0 < ε' := div_pos hε (mul_pos hφ_pos hφ_pos)
  -- Get N₀ for each unit a from SieveEquidistribution, take max
  have hN₀_exists : ∀ a : (ZMod q)ˣ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (((Finset.range N).filter (fun n => emMultUnit q hq hne n = a)).card : ℝ) ≥
      (N : ℝ) * (1 / φ - ε') := by
    intro a; exact hsieve q hq hne a ε' hε'_pos
  choose N₀_fn hN₀_fn using hN₀_exists
  refine ⟨Finset.univ.sup N₀_fn + 1, fun N hN_ge => ?_⟩
  -- For each a, N ≥ N₀(a)
  have hN_ge_a : ∀ a : (ZMod q)ˣ, N ≥ N₀_fn a := by
    intro a; have := Finset.le_sup (f := N₀_fn) (Finset.mem_univ a); omega
  -- Lower bound on hit count for each a
  set V := fun a => ((Finset.range N).filter (fun n => emMultUnit q hq hne n = a)).card
  have hlb : ∀ a : (ZMod q)ˣ, (V a : ℝ) ≥ (N : ℝ) * (1 / (φ : ℝ) - ε') :=
    fun a => hN₀_fn a N (hN_ge_a a)
  -- Total hit count = N
  have htotal : (∑ b : (ZMod q)ˣ, (V b : ℝ)) = (N : ℝ) := by
    have := mult_hit_count_sum hq hne N; exact_mod_cast this
  -- Use fiber decomposition
  rw [mult_char_sum_fiber hq hne χ N]
  -- Character orthogonality: ∑ χ(a) = 0
  have horth : ∑ a : (ZMod q)ˣ, (χ a : ℂ) = 0 := unit_char_sum_eq_zero χ hχ
  -- Rewrite: ∑ χ(a) · V(a) = ∑ χ(a) · (V(a) - N/φ) (mean subtraction)
  -- First, rewrite the sum using subtraction + remainder
  have hmean_eq : ∑ a : (ZMod q)ˣ,
      (χ a : ℂ) * ((V a : ℕ) : ℂ) =
      ∑ a : (ZMod q)ˣ,
        ((χ a : ℂ) * (((V a : ℝ) - (N : ℝ) / (φ : ℝ) : ℝ) : ℂ) +
         (χ a : ℂ) * (((N : ℝ) / (φ : ℝ) : ℝ) : ℂ)) := by
    congr 1; ext a; push_cast; ring
  rw [hmean_eq, Finset.sum_add_distrib]
  have hmean_zero : ∑ a : (ZMod q)ˣ, (χ a : ℂ) * (((N : ℝ) / (φ : ℝ) : ℝ) : ℂ) = 0 := by
    rw [← Finset.sum_mul, horth, zero_mul]
  rw [hmean_zero, add_zero]
  -- Triangle inequality + character norm = 1
  calc ‖∑ a : (ZMod q)ˣ, (χ a : ℂ) * (((V a : ℝ) - (N : ℝ) / (φ : ℝ) : ℝ) : ℂ)‖
      ≤ ∑ a : (ZMod q)ˣ, ‖(χ a : ℂ) * (((V a : ℝ) - (N : ℝ) / (φ : ℝ) : ℝ) : ℂ)‖ :=
        norm_sum_le _ _
    _ = ∑ a : (ZMod q)ˣ, |(V a : ℝ) - (N : ℝ) / (φ : ℝ)| := by
        congr 1; ext a
        rw [norm_mul, unit_monoidHom_norm_one χ a, one_mul, Complex.norm_real,
            Real.norm_eq_abs]
    _ ≤ ∑ _a : (ZMod q)ˣ, ((φ : ℝ) * ε' * N) := by
        apply Finset.sum_le_sum; intro a _
        -- Two-sided bound: V(a) ≥ N/φ - ε'N and V(a) ≤ N/φ + (φ-1)ε'N
        have hVlb : (V a : ℝ) - (N : ℝ) / (φ : ℝ) ≥ -(ε' * N) := by
          have h1 := hlb a
          -- N * (1/φ - ε') = N/φ - ε'*N
          have h2 : (N : ℝ) * (1 / (φ : ℝ) - ε') = (N : ℝ) / (φ : ℝ) - ε' * (N : ℝ) := by ring
          linarith
        have hVub : (V a : ℝ) - (N : ℝ) / (φ : ℝ) ≤ ((φ : ℝ) - 1) * ε' * N := by
          -- V(a) = N - ∑_{b≠a} V(b) ≤ N - (φ-1)·N·(1/φ - ε')
          have hVa_eq : (V a : ℝ) = (N : ℝ) - ∑ b ∈ Finset.univ.erase a, (V b : ℝ) := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at htotal; linarith
          have hφ_ge_one : (1 : ℝ) ≤ (φ : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨a, Finset.mem_univ _⟩
          have hcard_nat : (Finset.univ.erase a : Finset (ZMod q)ˣ).card = φ - 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ a)]
          have hφ_nat : 1 ≤ φ := Finset.card_pos.mpr ⟨a, Finset.mem_univ _⟩
          have hcard : ((Finset.univ.erase a : Finset (ZMod q)ˣ).card : ℝ) = (φ : ℝ) - 1 := by
            rw [hcard_nat, Nat.cast_sub hφ_nat]; simp
          have hsum_lb : ∑ b ∈ Finset.univ.erase a, (V b : ℝ) ≥
              ((φ : ℝ) - 1) * ((N : ℝ) * (1 / (φ : ℝ) - ε')) := by
            rw [← hcard]
            have h := Finset.card_nsmul_le_sum (Finset.univ.erase a)
              (fun b => (V b : ℝ)) ((N : ℝ) * (1 / (φ : ℝ) - ε'))
              (fun b _ => hlb b)
            rw [nsmul_eq_mul] at h; exact_mod_cast h
          -- N - (φ-1)*(N*(1/φ - ε')) = N/φ + (φ-1)*ε'*N
          have key : (N : ℝ) - ((φ : ℝ) - 1) * ((N : ℝ) * (1 / (φ : ℝ) - ε')) =
              (N : ℝ) / (φ : ℝ) + ((φ : ℝ) - 1) * ε' * (N : ℝ) := by
            field_simp; ring
          linarith
        -- |V(a) - N/φ| ≤ max(ε'·N, (φ-1)·ε'·N) ≤ φ·ε'·N
        rw [abs_le]
        have hφ_ge_one : (1 : ℝ) ≤ (φ : ℝ) := by
          exact_mod_cast Finset.card_pos.mpr ⟨a, Finset.mem_univ _⟩
        have hεN_nn : 0 ≤ ε' * (N : ℝ) := mul_nonneg (le_of_lt hε'_pos) (Nat.cast_nonneg N)
        constructor
        · -- -(φ·ε'·N) ≤ -(ε'·N) ≤ V(a) - N/φ
          have : -(↑φ * ε' * ↑N) ≤ -(ε' * ↑N) := by nlinarith
          linarith
        · -- V(a) - N/φ ≤ (φ-1)·ε'·N ≤ φ·ε'·N
          nlinarith
    _ = (φ : ℝ) * ((φ : ℝ) * ε' * N) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ε * N := by
        -- φ * (φ * (ε/(φ*φ)) * N) = ε * N
        have : (φ : ℝ) * ((φ : ℝ) * ε' * (N : ℝ)) = (φ : ℝ) * (φ : ℝ) * ε' * (N : ℝ) := by ring
        rw [this, hε'_def, mul_div_cancel₀]
        exact ne_of_gt (mul_pos hφ_pos hφ_pos)

/-- **StrongSieveImpliesMultCSB holds**: StrongSieveEquidist → EMMultCharSumBound.

    This follows by composing `strongSieveEquidist_implies_sieveEquidist` (SSE → SE)
    with `sieve_equidist_implies_mult_csb` (SE → EMMultCSB). -/
theorem strongSieve_implies_multCSB : StrongSieveImpliesMultCSB :=
  fun hsse => sieve_equidist_implies_mult_csb (strongSieveEquidist_implies_sieveEquidist hsse)

end BVDecomposition

/-! ## S79. Sieve-to-Harmonic Bridge Theorems

The proved `sieve_equidist_implies_mult_csb` yields `EMMultCharSumBound` with
`Q_0 = 0`, which means multiplier character sums cancel for ALL primes q (not
just q >= Q_0).  This is exactly the `DecorrelationHypothesis` from S31.

We formalize this connection and compose it with the downstream harmonic chain:
- `SieveEquidistribution` -> `DecorrelationHypothesis` (extract Q_0 = 0)
- `SieveEquidistribution` -> `PositiveEscapeDensity` (compose with `decorrelation_implies_ped`)
- Chain theorems to MC (requiring `PEDImpliesComplexCSB` as the sole remaining bridge)

### Key insight:
The sieve hierarchy (S36-S39) and the harmonic hierarchy (S30-S35) converge:
both produce `DecorrelationHypothesis` as output.  The sieve route achieves
this via counting-to-character-sum bridge (`sieve_equidist_implies_mult_csb`);
the harmonic route states it directly.  This means ANY proof of
`SieveEquidistribution` (e.g., from PNT in APs + Alladi's theorem) immediately
gives `DecorrelationHypothesis` and `PositiveEscapeDensity` for free.

### Chains:
```
SieveEquidistribution ->[proved]-> DecorrelationHypothesis
  ->[proved]-> PositiveEscapeDensity ->[PEDImpliesCSB, open]-> CCSB ->[proved]-> MC
```
-/

section SieveHarmonicBridge

/-- **SieveEquidistribution implies DecorrelationHypothesis**: the counting form of
    multiplier equidistribution (SieveEquidistribution) implies the character-sum
    form (DecorrelationHypothesis) for ALL primes q.

    Proof: `sieve_equidist_implies_mult_csb` produces `EMMultCharSumBound` with
    `Q_0 = 0`. For Q_0 = 0, the condition `q >= Q_0` is trivially satisfied,
    so the bound holds for all primes — which is exactly `DecorrelationHypothesis`. -/
theorem sieve_equidist_implies_decorrelation :
    SieveEquidistribution → DecorrelationHypothesis := by
  intro hsieve q inst hq hne χ hχ ε hε
  haveI : Fact (Nat.Prime q) := inst
  -- Prove the Weyl bound directly from hsieve for this specific q.
  -- This applies the same Fourier decomposition as sieve_equidist_implies_mult_csb
  -- but targets DecorrelationHypothesis directly (avoiding the ∃ Q₀ wrapper of
  -- EMMultCharSumBound, whose witness is opaque after existential packaging).
  set φ := (Finset.univ : Finset (ZMod q)ˣ).card with hφ_def
  have hφ_pos : (0 : ℝ) < φ := by positivity
  set ε' := ε / ((φ : ℝ) * φ) with hε'_def
  have hε'_pos : 0 < ε' := div_pos hε (mul_pos hφ_pos hφ_pos)
  have hN₀_exists : ∀ a : (ZMod q)ˣ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (((Finset.range N).filter (fun n => emMultUnit q hq hne n = a)).card : ℝ) ≥
      (N : ℝ) * (1 / φ - ε') :=
    fun a => hsieve q hq hne a ε' hε'_pos
  choose N₀_fn hN₀_fn using hN₀_exists
  refine ⟨Finset.univ.sup N₀_fn + 1, fun N hN_ge => ?_⟩
  have hN_ge_a : ∀ a : (ZMod q)ˣ, N ≥ N₀_fn a := by
    intro a; have := Finset.le_sup (f := N₀_fn) (Finset.mem_univ a); omega
  set V := fun a => ((Finset.range N).filter (fun n => emMultUnit q hq hne n = a)).card
  have hlb : ∀ a, (V a : ℝ) ≥ (N : ℝ) * (1 / (φ : ℝ) - ε') := fun a => hN₀_fn a N (hN_ge_a a)
  have htotal : (∑ b : (ZMod q)ˣ, (V b : ℝ)) = (N : ℝ) := by
    have := mult_hit_count_sum hq hne N; exact_mod_cast this
  rw [mult_char_sum_fiber hq hne χ N]
  have horth : ∑ a : (ZMod q)ˣ, (χ a : ℂ) = 0 := unit_char_sum_eq_zero χ hχ
  have hmean_eq : ∑ a : (ZMod q)ˣ, (χ a : ℂ) * ((V a : ℕ) : ℂ) =
      ∑ a : (ZMod q)ˣ, ((χ a : ℂ) * (((V a : ℝ) - (N : ℝ) / (φ : ℝ) : ℝ) : ℂ) +
       (χ a : ℂ) * (((N : ℝ) / (φ : ℝ) : ℝ) : ℂ)) := by congr 1; ext a; push_cast; ring
  rw [hmean_eq, Finset.sum_add_distrib,
      show ∑ a : (ZMod q)ˣ, (χ a : ℂ) * (((N : ℝ) / (φ : ℝ) : ℝ) : ℂ) = 0 from by
        rw [← Finset.sum_mul, horth, zero_mul],
      add_zero]
  calc ‖∑ a : (ZMod q)ˣ, (χ a : ℂ) * (((V a : ℝ) - (N : ℝ) / (φ : ℝ) : ℝ) : ℂ)‖
      ≤ ∑ a : (ZMod q)ˣ, ‖(χ a : ℂ) * (((V a : ℝ) - (N : ℝ) / (φ : ℝ) : ℝ) : ℂ)‖ :=
        norm_sum_le _ _
    _ = ∑ a : (ZMod q)ˣ, |(V a : ℝ) - (N : ℝ) / (φ : ℝ)| := by
        congr 1; ext a
        rw [norm_mul, unit_monoidHom_norm_one χ a, one_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ _a : (ZMod q)ˣ, ((φ : ℝ) * ε' * N) := by
        apply Finset.sum_le_sum; intro a _
        rw [abs_le]; constructor
        · -- Lower bound: -(φ·ε'·N) ≤ V(a) - N/φ
          -- From hlb: V(a) ≥ N/φ - ε'·N, so V(a) - N/φ ≥ -ε'·N ≥ -(φ·ε'·N)
          have h1 := hlb a
          have hφ_ge_one' : (1 : ℝ) ≤ (φ : ℝ) :=
            by exact_mod_cast Finset.card_pos.mpr ⟨a, Finset.mem_univ _⟩
          have hεN_nn : 0 ≤ ε' * (N : ℝ) := mul_nonneg (le_of_lt hε'_pos) (Nat.cast_nonneg N)
          have h2 : (N : ℝ) * (1 / (φ : ℝ) - ε') = (N : ℝ) / (φ : ℝ) - ε' * (N : ℝ) := by ring
          have h3 : -(↑φ * ε' * ↑N) ≤ -(ε' * ↑N) := by nlinarith
          linarith
        · -- Upper bound: V(a) - N/φ ≤ (φ-1)·ε'·N ≤ φ·ε'·N
          have hφ_ge_one : (1 : ℝ) ≤ (φ : ℝ) :=
            by exact_mod_cast Finset.card_pos.mpr ⟨a, Finset.mem_univ _⟩
          have hVa_eq : (V a : ℝ) = (N : ℝ) - ∑ b ∈ Finset.univ.erase a, (V b : ℝ) := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at htotal; linarith
          have hcard : ((Finset.univ.erase a : Finset (ZMod q)ˣ).card : ℝ) = (φ : ℝ) - 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ a),
                Nat.cast_sub (Finset.card_pos.mpr ⟨a, Finset.mem_univ _⟩)]
            simp [hφ_def]
          have hsum_lb : ∑ b ∈ Finset.univ.erase a, (V b : ℝ) ≥
              ((φ : ℝ) - 1) * ((N : ℝ) * (1 / (φ : ℝ) - ε')) := by
            rw [← hcard]
            have h := Finset.card_nsmul_le_sum (Finset.univ.erase a)
              (fun b => (V b : ℝ)) ((N : ℝ) * (1 / (φ : ℝ) - ε')) (fun b _ => hlb b)
            rw [nsmul_eq_mul] at h; exact_mod_cast h
          nlinarith [hVa_eq, hsum_lb, (show (N : ℝ) - ((φ : ℝ) - 1) * ((N : ℝ) * (1 / (φ : ℝ) - ε')) =
            (N : ℝ) / (φ : ℝ) + ((φ : ℝ) - 1) * ε' * (N : ℝ) from by field_simp; ring)]
    _ = (φ : ℝ) * ((φ : ℝ) * ε' * N) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ε * N := by
        have : (φ : ℝ) * ((φ : ℝ) * ε' * (N : ℝ)) = (φ : ℝ) * (φ : ℝ) * ε' * (N : ℝ) := by ring
        rw [this, hε'_def, mul_div_cancel₀]
        exact ne_of_gt (mul_pos hφ_pos hφ_pos)

/-- **SieveEquidistribution implies PositiveEscapeDensity**: composing the
    sieve-to-decorrelation bridge with `decorrelation_implies_ped`.

    For every prime q not in the EM sequence and every non-trivial character chi,
    a positive fraction of the multipliers escape ker(chi). -/
theorem sieve_equidist_implies_ped :
    SieveEquidistribution → PositiveEscapeDensity :=
  fun hsieve => decorrelation_implies_ped (sieve_equidist_implies_decorrelation hsieve)

/-- **Sieve equidistribution chain to MC**: SieveEquidistribution, combined with
    the (open) PED-to-CCSB bridge, implies Mullin's Conjecture.

    ```
    SieveEquidist ->[proved]-> Dec ->[proved]-> PED
      ->[PEDImpliesCSB, open]-> CCSB ->[proved]-> MC
    ```

    The sole remaining open hypothesis is `PEDImpliesComplexCSB`. -/
theorem sieve_equidist_chain_mc (hsieve : SieveEquidistribution)
    (hped_csb : PEDImpliesComplexCSB) :
    MullinConjecture :=
  complex_csb_mc' (hped_csb (sieve_equidist_implies_ped hsieve))

/-- **StrongSieveEquidist implies DecorrelationHypothesis**: composing
    SSE -> SE with SE -> Dec. -/
theorem strongSieve_implies_decorrelation :
    StrongSieveEquidist → DecorrelationHypothesis :=
  fun hsse => sieve_equidist_implies_decorrelation
    (strongSieveEquidist_implies_sieveEquidist hsse)

/-- **StrongSieveEquidist implies PositiveEscapeDensity**: composing
    SSE -> SE with SE -> PED. -/
theorem strongSieve_implies_ped :
    StrongSieveEquidist → PositiveEscapeDensity :=
  fun hsse => sieve_equidist_implies_ped
    (strongSieveEquidist_implies_sieveEquidist hsse)

/-- **StrongSieveEquidist chain to MC**: SSE + PEDImpliesCSB -> MC. -/
theorem strongSieve_chain_mc (hsse : StrongSieveEquidist)
    (hped_csb : PEDImpliesComplexCSB) :
    MullinConjecture :=
  sieve_equidist_chain_mc (strongSieveEquidist_implies_sieveEquidist hsse) hped_csb

end SieveHarmonicBridge

/-! ## Summary (S52)

### New definitions (S52):
- `EMMultCharSumBound` : multiplier character sums are o(N) for q >= Q_0 (intermediate Prop)
- `BVImpliesEMMultCSB` : BV -> EMMultCharSumBound (open -- sieve transfer)
- `MultCSBImpliesMMCSB` : EMMultCharSumBound -> MultiModularCSB (open -- walk bridge)
- `StrongSieveImpliesMultCSB` : StrongSieveEquidist -> EMMultCharSumBound (open -- Weyl bridge)

### Proved theorems (S52):
- `bv_decomposition_implies_mmcsb` : BVImpliesEMMultCSB + MultCSBImpliesMMCSB -> BVImpliesMMCSB
- `bv_decomposed_chain_mc` : BV + both transfers + finite check -> MC
- `bv_decomposed_small_threshold_mc` : above with Q_0 <= 11 -> MC unconditionally
- `telescope_constrains_walk` : walk telescope norm bound <= 2 (restatement from S37)

### Key insight (S52):
The frontier `BVImpliesMMCSB` decomposes into two independent obstacles at a
natural intermediate: **EMMultCharSumBound** (multiplier character sums cancel).

1. **BV -> EMMultCSB** (sieve-theoretic): Transfer from the universal prime
   counting function to the specific EM multipliers. This is where Alladi's
   theorem, the Selberg sieve, and the BV averaged bound interact.

2. **EMMultCSB -> MMCSB** (harmonic-analytic): Transfer from multiplier character
   sums (linear) to walk character sums (product walk). The algebraic backbone
   is the walk telescoping identity from S37, but the quantitative extraction
   (showing escape density implies walk cancellation) remains open.

This decomposition separates NUMBER THEORY (obstacle 1: which primes appear as
EM multipliers?) from DYNAMICS (obstacle 2: how do partial products of
equidistributed unit complex numbers behave?). Each obstacle can be attacked
independently with different mathematical tools.

### New chains:
```
BV ->[open]-> EMMultCSB ->[open]-> MMCSB ->[proved]-> MC
StrongSieveEquidist ->[proved]-> EMMultCSB ->[open]-> MMCSB ->[proved]-> MC
```

### Proved theorems (S79):
- `sieve_equidist_implies_decorrelation` : SE -> DecorrelationHypothesis (Weyl criterion)
- `sieve_equidist_implies_ped` : SE -> PositiveEscapeDensity (compose with Dec -> PED)
- `sieve_equidist_chain_mc` : SE + PEDImpliesCSB -> MC
- `strongSieve_implies_decorrelation` : SSE -> DecorrelationHypothesis
- `strongSieve_implies_ped` : SSE -> PositiveEscapeDensity
- `strongSieve_chain_mc` : SSE + PEDImpliesCSB -> MC

### Key insight (S79):
The sieve hierarchy and harmonic hierarchy converge at DecorrelationHypothesis.
SieveEquidistribution (a counting statement about minFac equidistribution) implies
DecorrelationHypothesis (a character-sum cancellation statement) via the Weyl criterion.
This means any proof of SieveEquidistribution (e.g., PNT in APs + Alladi) immediately
gives Dec and PED for free.  The sole remaining gap to MC is PEDImpliesComplexCSB.

### New chains (S79):
```
SieveEquidist ->[proved]-> Dec ->[proved]-> PED ->[open]-> CCSB ->[proved]-> MC
SSE ->[proved]-> Dec ->[proved]-> PED ->[open]-> CCSB ->[proved]-> MC
```
-/


