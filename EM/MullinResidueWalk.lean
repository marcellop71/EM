import EM.MullinConjectures

/-!
# The Residue Walk and Walk Coverage

Route 2 analysis of the Euclid–Mullin sequence via residue arithmetic:
* Bridge lemma: `dvd_succ_iff_mod_pred` (q ∣ a+1 ↔ a%q = q-1)
* Walk recurrence in residue form
* `WalkCoverage`: the walk hits every residue class
* Pigeonhole principle for walk collisions
* Concrete Mullin Conjecture instances for small primes
-/

namespace Mullin

open Euclid

/-! ## Route 2: The Residue Walk -/

/-- **Bridge lemma**: divisibility by q at a+1 corresponds to the
    residue of a being q-1 (= -1 mod q).

    q ∣ (a + 1) ↔ a % q = q - 1

    Forward: if q ∣ (a+1), then (a+1) % q = 0, so (a%q + 1) % q = 0.
    Since 0 ≤ a%q < q, we get q ∣ (a%q + 1) and q ≤ a%q + 1 ≤ q,
    forcing a%q = q-1.

    Backward: if a%q = q-1, then (a+1) % q = (q-1+1) % q = q%q = 0. -/
private theorem dvd_succ_iff_mod_pred {q a : Nat} (hq : 2 ≤ q) :
    q ∣ (a + 1) ↔ a % q = q - 1 := by
  constructor
  · intro h
    have hlt := Nat.mod_lt a (show 0 < q by omega)
    have h1 : (1 : Nat) % q = 1 := Nat.mod_eq_of_lt (by omega)
    -- Key step: (a + 1) % q = (a % q + 1) % q
    have key : (a % q + 1) % q = 0 := by
      have h2 := Nat.add_mod a 1 q
      rw [h1] at h2
      -- h2 : (a + 1) % q = (a % q + 1) % q
      rw [← h2]
      exact Nat.mod_eq_zero_of_dvd h
    -- From (a%q + 1) % q = 0: q divides a%q + 1, so q ≤ a%q + 1.
    -- Combined with a%q < q: a%q + 1 = q, i.e., a%q = q-1.
    have hdvd := Nat.dvd_of_mod_eq_zero key
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega
  · intro h
    apply Nat.dvd_of_mod_eq_zero
    have h1 : (1 : Nat) % q = 1 := Nat.mod_eq_of_lt (by omega)
    have h2 := Nat.add_mod a 1 q
    rw [h1] at h2
    -- h2 : (a + 1) % q = (a % q + 1) % q
    -- Rewrite goal using h2, then substitute a % q = q - 1
    rw [h2, h, show q - 1 + 1 = q from by omega, Nat.mod_self]

/-- **Walk recurrence**: the residue walk satisfies the multiplicative
    transition rule.

    prod(n+1) % q = (prod(n) % q * seq(n+1) % q) % q

    This follows directly from `prod_succ` and `Nat.mul_mod`. -/
theorem prod_succ_mod (q n : Nat) :
    prod (n + 1) % q = (prod n % q * (seq (n + 1) % q)) % q := by
  rw [prod_succ, Nat.mul_mod]

/-- The multiplier residue seq(n) % q is nonzero when q is prime and
    q never appears in the sequence.

    If q ∣ seq(n), then since seq(n) is prime, q = 1 or q = seq(n).
    Both contradict our hypotheses. -/
theorem seq_mod_ne_zero {q : Nat} (hq : IsPrime q)
    (hne : ∀ m, seq m ≠ q) (n : Nat) : seq n % q ≠ 0 := by
  intro h
  have hdvd : q ∣ seq n := Nat.dvd_of_mod_eq_zero h
  match (seq_isPrime n).2 q hdvd with
  | .inl heq => exact absurd heq (by have := hq.1; omega)
  | .inr heq => exact hne n heq.symm

/-- The walk position prod(n) % q is nonzero when q is prime and
    q never appears in the sequence.

    This follows from `prime_not_in_seq_not_dvd_prod` (Part 6). -/
private theorem prod_mod_ne_zero {q : Nat} (hq : IsPrime q)
    (hne : ∀ m, seq m ≠ q) (n : Nat) : prod n % q ≠ 0 := by
  intro h
  exact prime_not_in_seq_not_dvd_prod hq hne n (Nat.dvd_of_mod_eq_zero h)

/-- The multiplier residue lies in {1, ..., q-1}. -/
theorem seq_mod_range {q : Nat} (hq : IsPrime q)
    (hne : ∀ m, seq m ≠ q) (n : Nat) :
    1 ≤ seq n % q ∧ seq n % q < q := by
  have hqpos : 0 < q := by have := hq.1; omega
  exact ⟨by have := seq_mod_ne_zero hq hne n; omega,
         Nat.mod_lt _ hqpos⟩

/-- The walk position lies in {1, ..., q-1}. -/
theorem prod_mod_range {q : Nat} (hq : IsPrime q)
    (hne : ∀ m, seq m ≠ q) (n : Nat) :
    1 ≤ prod n % q ∧ prod n % q < q := by
  have hqpos : 0 < q := by have := hq.1; omega
  exact ⟨by have := prod_mod_ne_zero hq hne n; omega,
         Nat.mod_lt _ hqpos⟩

/-! ## Residue formulation of the Hitting Hypothesis -/

/-- **ResidueHitting**: the Hitting Hypothesis reformulated in terms of
    modular arithmetic.

    Instead of asking q ∣ (prod n + 1), we equivalently ask
    prod n % q = q - 1 (i.e., the walk hits -1 mod q). -/
def ResidueHitting : Prop :=
  ∀ q, IsPrime q → (∀ m, seq m ≠ q) → ∀ N, ∃ n, N ≤ n ∧ prod n % q = q - 1

/-- **HH ↔ ResidueHitting**: the two formulations are equivalent,
    connected by the bridge lemma. -/
theorem hh_iff_rh : HittingHypothesis ↔ ResidueHitting := by
  unfold HittingHypothesis ResidueHitting
  constructor
  · intro hH q hq hne N
    obtain ⟨n, hn, hdvd⟩ := hH q hq hne N
    exact ⟨n, hn, (dvd_succ_iff_mod_pred hq.1).mp hdvd⟩
  · intro hR q hq hne N
    obtain ⟨n, hn, hmod⟩ := hR q hq hne N
    exact ⟨n, hn, (dvd_succ_iff_mod_pred hq.1).mpr hmod⟩

/-! ## Walk Coverage Hypothesis -/

/-- **WalkCoverage**: the multiplicative walk prod(n) mod q visits every
    nonzero residue class infinitely often.

    This is strictly stronger than HH (which only requires the walk
    to hit q-1). It is the natural "equidistribution" assertion for
    the residue walk.

    WalkCoverage says: for every prime q not in the EM sequence, and
    every target residue r ∈ {1, ..., q-1}, and every bound N, there
    exists n ≥ N with prod(n) ≡ r (mod q). -/
def WalkCoverage : Prop :=
  ∀ q, IsPrime q → (∀ m, seq m ≠ q) →
  ∀ r, 1 ≤ r → r < q → ∀ N, ∃ n, N ≤ n ∧ prod n % q = r

/-- **WalkCoverage → HH**: specialize to the target r = q - 1. -/
theorem wc_implies_hh : WalkCoverage → HittingHypothesis := by
  intro hWC q hq hne N
  have hge : 2 ≤ q := hq.1
  obtain ⟨n, hn_ge, hn_mod⟩ := hWC q hq hne (q - 1) (by omega) (by omega) N
  exact ⟨n, hn_ge, (dvd_succ_iff_mod_pred hq.1).mpr hn_mod⟩

/-- **WalkCoverage → Mullin's Conjecture**: via the chain
    WalkCoverage → HH → MullinConjecture. -/
theorem wc_implies_mullin : WalkCoverage → MullinConjecture :=
  fun hWC => hh_implies_mullin (wc_implies_hh hWC)

/-! ## Walk dynamics: cancellation and non-stationarity -/

/-- **Cancellation in the residue walk**: if the walk doesn't move from
    step n to step n+1, the multiplier must have residue 1 mod q.

    From prod(n) % q = prod(n+1) % q and the walk recurrence
    (c·m) % q = c, we derive q ∣ c·(m−1). Since gcd(q,c) = 1
    (q is prime and doesn't divide c), we get q ∣ (m−1). Since
    0 ≤ m−1 < q, we conclude m = 1.

    This means: the only way the walk can "stay still" is if the
    multiplier seq(n+1) is ≡ 1 (mod q). Any multiplier NOT ≡ 1
    forces the walk to a new position. -/
private theorem walk_step_one_of_eq {q : Nat} (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (n : Nat)
    (heq : prod n % q = prod (n + 1) % q) :
    seq (n + 1) % q = 1 := by
  -- Shorthands for the range facts
  have ⟨hc_pos, hc_lt⟩ := prod_mod_range hq hne n
  have ⟨hm_pos, hm_lt⟩ := seq_mod_range hq hne (n + 1)
  -- Walk recurrence + heq give: c = (c · m) % q
  -- (where c = prod n % q, m = seq(n+1) % q)
  have hstep : prod n % q = (prod n % q * (seq (n + 1) % q)) % q := by
    have h := prod_succ_mod q n
    -- h : prod (n + 1) % q = (prod n % q * (seq (n + 1) % q)) % q
    rw [← heq] at h
    exact h
  -- From hstep and Nat.div_add_mod: q divides (c·m - c)
  have hge : prod n % q ≤ prod n % q * (seq (n + 1) % q) := by
    calc prod n % q = prod n % q * 1 := (Nat.mul_one _).symm
      _ ≤ prod n % q * (seq (n + 1) % q) := Nat.mul_le_mul_left _ (by omega)
  have hdm := Nat.div_add_mod (prod n % q * (seq (n + 1) % q)) q
  rw [← hstep] at hdm
  have hdvd : q ∣ (prod n % q * (seq (n + 1) % q) - prod n % q) :=
    ⟨(prod n % q * (seq (n + 1) % q)) / q, by omega⟩
  -- Factor: c·m - c = c·(m - 1)
  have hfac : prod n % q * (seq (n + 1) % q) - prod n % q =
              prod n % q * (seq (n + 1) % q - 1) := by
    have h := Nat.mul_add (prod n % q) (seq (n + 1) % q - 1) 1
    rw [Nat.mul_one, Nat.sub_add_cancel (show 1 ≤ seq (n + 1) % q by omega)] at h
    omega
  rw [hfac] at hdvd
  -- q and prod n % q are coprime (q prime, q ∤ it since it's < q and > 0)
  have hcop : Nat.Coprime q (prod n % q) :=
    coprime_of_prime_not_dvd hq (fun h => by
      have := Nat.le_of_dvd (by omega) h; omega)
  -- q ∣ (m - 1): commute factors, then coprime cancellation
  have hdvd_comm : q ∣ (seq (n + 1) % q - 1) * (prod n % q) := by
    rwa [Nat.mul_comm]
  have hdvd_m1 : q ∣ (seq (n + 1) % q - 1) := hcop.dvd_of_dvd_mul_right hdvd_comm
  -- m - 1 < q and q ∣ (m - 1), so m - 1 = 0, hence m = 1
  rcases hdvd_m1 with ⟨k, hk⟩
  match k with
  | 0 => omega
  | k + 1 =>
    -- q * (k+1) ≥ q, but seq(n+1) % q - 1 < q: contradiction
    have hle : q ≤ q * (k + 1) :=
      calc q = q * 1 := (Nat.mul_one q).symm
        _ ≤ q * (k + 1) := Nat.mul_le_mul_left q (by omega)
    omega

/-- **Constant walk implies all multipliers ≡ 1 (mod q).**

    If the walk is stuck at position c (same residue from step N onward),
    then every multiplier from step N+1 onward has residue 1 mod q.

    This is the "non-stationarity" result: if the walk doesn't hit -1,
    it can only avoid -1 by having ALL future multipliers ≡ 1 mod q.
    Since Dirichlet's theorem says only 1/(q-1) of primes are ≡ 1 mod q,
    this represents an extreme (heuristically impossible) conspiracy. -/
theorem constant_walk_all_units {q : Nat} (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q)
    (N : Nat) (hconst : ∀ n, N ≤ n → prod n % q = prod N % q) :
    ∀ n, N < n → seq n % q = 1 := by
  intro n hn
  -- n ≥ N + 1, so n = (n - 1) + 1 with n - 1 ≥ N
  have hn1 : N ≤ n - 1 := by omega
  have hn2 : n = (n - 1) + 1 := by omega
  rw [hn2]
  apply walk_step_one_of_eq hq hne
  -- Need: prod (n - 1) % q = prod ((n - 1) + 1) % q
  rw [← hn2]
  exact (hconst (n - 1) hn1).trans (hconst n (by omega)).symm

/-! ## Fundamental EM properties and the auto-hit phenomenon -/

/-- Each EM term divides the previous Euclid number:
    seq(n+1) = minFac(prod(n) + 1), so seq(n+1) ∣ (prod(n) + 1).

    This is the defining property that makes the EM sequence a
    "Euclid-style walk": each new prime is a factor of the previous
    product + 1. -/
theorem seq_dvd_succ_prod (n : Nat) : seq (n + 1) ∣ (prod n + 1) := by
  rw [seq_succ]
  exact minFac_dvd _ (by have := prod_ge_two n; omega)

/-- **The auto-hit property**: the walk automatically hits -1 mod each
    new EM prime.

    Since seq(n+1) ∣ (prod(n) + 1), we have
    prod(n) ≡ -1 (mod seq(n+1)), i.e., prod(n) % seq(n+1) = seq(n+1) - 1.

    At every step n, the walk "hits" -1 relative to the prime that will
    be chosen at the next step. The EM sequence is a machine that
    produces a new prime by finding where the walk is currently at -1.

    For Mullin's Conjecture, the question is: does the walk also hit -1
    mod primes that are NOT chosen — specifically, mod primes that never
    appear in the sequence? -/
theorem auto_hit_mod (n : Nat) : prod n % seq (n + 1) = seq (n + 1) - 1 :=
  (dvd_succ_iff_mod_pred (seq_isPrime (n + 1)).1).mp (seq_dvd_succ_prod n)

/-- **Co-hitting**: if any prime q divides prod(n) + 1, the walk hits
    -1 mod q at step n.

    This applies to ALL prime factors of prod(n) + 1, not just the
    smallest (which is seq(n+1)). At each step n, the walk simultaneously
    hits -1 modulo EVERY prime factor of prod(n) + 1. The EM sequence
    "sees" only the smallest factor, but the walk is hitting -1 mod
    many primes at once.

    The Hitting Hypothesis asks: for a prime q not in the sequence, is
    q ever among these "co-hit" primes? -/
theorem co_hit {q n : Nat} (hq : IsPrime q) (hdvd : q ∣ prod n + 1) :
    prod n % q = q - 1 :=
  (dvd_succ_iff_mod_pred hq.1).mp hdvd

/-- **When a prime is captured, the walk was at -1 mod that prime.**

    If q enters the sequence at position k+1 (i.e., seq(k+1) = q),
    then prod(k) ≡ -1 (mod q).

    This is the mechanism by which primes are "captured": the walk being
    at -1 mod q means q ∣ (prod(k) + 1), and if q is the smallest such
    factor, then seq(k+1) = q. -/
theorem hit_before_capture {q k : Nat} (hk : seq (k + 1) = q) :
    prod k % q = q - 1 := by
  rw [← hk]; exact auto_hit_mod k

/-- **If the multiplier residue is not 1, the walk must move.**

    Contrapositive of `walk_step_one_of_eq`: if seq(n+1) % q ≠ 1,
    then prod(n) % q ≠ prod(n+1) % q.

    Any multiplier not in the "identity" residue class forces the walk
    to a new position. The walk can only "stay still" when the multiplier
    is ≡ 1 (mod q). -/
theorem walk_moves_of_neq_one {q : Nat} (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (n : Nat)
    (hm : seq (n + 1) % q ≠ 1) :
    prod n % q ≠ prod (n + 1) % q :=
  fun heq => hm (walk_step_one_of_eq hq hne n heq)

/-! ## Concrete non-constancy of the walk -/

/-- The walk visits at least two distinct positions for any prime q not
    in the sequence.

    The proof uses `walk_moves_of_neq_one`: the walk moves if the multiplier
    residue is not 1. The first multiplier is seq(1), which divides
    prod(0) + 1 = 3. Since seq(1) is prime (≥ 2) and divides 3, it must be
    3 itself (2 doesn't divide 3). Since q ∉ seq and seq(1) = 3, we have
    q ≠ 3. Combined with q ≠ 2 (= seq 0), q ≥ 4, so 3 % q = 3 ≠ 1.

    This is the first concrete structural result: the EM walk is never
    trivially stationary. -/
theorem walk_nonconstant_start {q : Nat} (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) :
    prod 0 % q ≠ prod 1 % q := by
  apply walk_moves_of_neq_one hq hne 0
  -- Goal: seq 1 % q ≠ 1
  -- Step 1: seq 1 ∣ prod 0 + 1 = 3
  have hs_dvd : seq 1 ∣ (prod 0 + 1) := seq_dvd_succ_prod 0
  rw [prod_zero] at hs_dvd  -- hs_dvd : seq 1 ∣ 3
  -- Step 2: seq 1 ≥ 2 (prime) and seq 1 ≤ 3 (divides 3)
  have hs_ge : 2 ≤ seq 1 := (seq_isPrime 1).1
  have hs_le : seq 1 ≤ 3 := Nat.le_of_dvd (by omega) hs_dvd
  -- Step 3: seq 1 = 3 (can't be 2 since 2 ∤ 3)
  have hs_eq : seq 1 = 3 := by
    rcases (show seq 1 = 2 ∨ seq 1 = 3 by omega) with h | h
    · rw [h] at hs_dvd; obtain ⟨k, hk⟩ := hs_dvd; omega
    · exact h
  -- Step 4: q ≠ 3 (since seq 1 = 3 and q ∉ seq) and q ≠ 2 (= seq 0)
  have hq3 : q ≠ 3 := fun h => hne 1 (by rw [hs_eq]; omega)
  have hq2 : q ≠ 2 := fun h => hne 0 (by rw [seq_zero]; omega)
  -- Step 5: 3 % q = 3 (since q ≥ 4 > 3) and 3 ≠ 1
  have hge : 2 ≤ q := hq.1
  rw [hs_eq, Nat.mod_eq_of_lt (show (3 : Nat) < q by omega)]
  omega

/-- **The walk is never constant from the start.**

    Corollary of `walk_nonconstant_start`: no prime q ∉ seq can have the
    residue walk stuck at a single position from step 0 onward. -/
theorem walk_not_constant_from_zero {q : Nat} (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) :
    ¬(∀ n, prod n % q = prod 0 % q) := by
  intro hconst
  exact walk_nonconstant_start hq hne (hconst 1).symm

/-! ## Pigeonhole principle and walk collisions -/

section
open Classical

/-- **Pigeonhole principle**: n+1 values in {1,...,n} contain a duplicate. -/
private theorem pigeonhole :
    ∀ (n : Nat) (f : Nat → Nat),
    (∀ i, i ≤ n → 1 ≤ f i ∧ f i ≤ n) →
    ∃ i j, i < j ∧ j ≤ n ∧ f i = f j := by
  intro n
  induction n with
  | zero =>
    intro f hrange; exfalso; have := hrange 0 (Nat.le_refl 0); omega
  | succ k ih =>
    intro f hrange
    by_cases hmatch : ∃ i, i ≤ k ∧ f i = f (k + 1)
    · obtain ⟨i, hi, hfi⟩ := hmatch
      exact ⟨i, k + 1, by omega, Nat.le_refl _, hfi⟩
    · have hno : ∀ i, i ≤ k → f i ≠ f (k + 1) :=
        fun i hi heq => hmatch ⟨i, hi, heq⟩
      let g := fun i => if f i < f (k + 1) then f i else f i - 1
      have grange : ∀ i, i ≤ k → 1 ≤ g i ∧ g i ≤ k := by
        intro i hi
        have ⟨hlo, hhi⟩ := hrange i (by omega)
        have hne := hno i hi
        have ⟨_, hfkhi⟩ := hrange (k + 1) (Nat.le_refl _)
        show 1 ≤ (if f i < f (k + 1) then f i else f i - 1) ∧
             (if f i < f (k + 1) then f i else f i - 1) ≤ k
        split
        · exact ⟨hlo, by omega⟩
        · rename_i hge; exact ⟨by omega, by omega⟩
      obtain ⟨i, j, hij, hjk, hgij⟩ := ih g grange
      have hfi_lo := (hrange i (by omega)).1
      have hfj_lo := (hrange j (by omega)).1
      have hne_i := hno i (by omega)
      have hne_j := hno j (by omega)
      change (if f i < f (k + 1) then f i else f i - 1) =
             (if f j < f (k + 1) then f j else f j - 1) at hgij
      split at hgij
      · rename_i hlt_i
        split at hgij
        · exact ⟨i, j, hij, by omega, hgij⟩
        · exfalso; rename_i hge_j; omega
      · rename_i hge_i
        split at hgij
        · exfalso; rename_i hlt_j; omega
        · rename_i hge_j; exact ⟨i, j, hij, by omega, by omega⟩

/-- **Walk collision**: within any q consecutive steps, some position is visited twice. -/
theorem walk_has_collision {q : Nat} (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (N : Nat) :
    ∃ i j, N ≤ i ∧ i < j ∧ j < N + q ∧ prod i % q = prod j % q := by
  have hge : 2 ≤ q := hq.1
  obtain ⟨i, j, hij, hjn, hfij⟩ :=
    pigeonhole (q - 1) (fun i => prod (N + i) % q) (by
      intro i hi
      show 1 ≤ prod (N + i) % q ∧ prod (N + i) % q ≤ q - 1
      have ⟨hlo, hhi⟩ := prod_mod_range hq hne (N + i)
      exact ⟨hlo, by omega⟩)
  exact ⟨N + i, N + j, by omega, by omega, by omega, hfij⟩

/-- **Range product**: product of seq values from index `lo+1` to `hi`. -/
private def rangeProd (lo hi : Nat) : Nat :=
  match hi with
  | 0 => 1
  | n + 1 => if lo < n + 1 then rangeProd lo n * seq (n + 1) else 1

private theorem rangeProd_self (n : Nat) : rangeProd n n = 1 := by
  cases n with
  | zero => rfl
  | succ m =>
    unfold rangeProd
    simp [show ¬(m + 1 < m + 1) from by omega]

private theorem rangeProd_succ {lo hi : Nat} (h : lo < hi + 1) :
    rangeProd lo (hi + 1) = rangeProd lo hi * seq (hi + 1) := by
  show (if lo < hi + 1 then rangeProd lo hi * seq (hi + 1) else 1) = _
  rw [if_pos h]

private theorem rangeProd_succ_ge {lo hi : Nat} (h : ¬(lo < hi + 1)) :
    rangeProd lo (hi + 1) = 1 := by
  show (if lo < hi + 1 then rangeProd lo hi * seq (hi + 1) else 1) = 1
  rw [if_neg h]

/-- **Product decomposition**: prod(j) = prod(i) * rangeProd(i, j) for i ≤ j. -/
private theorem prod_eq_mul_rangeProd :
    ∀ (i j : Nat), i ≤ j → prod j = prod i * rangeProd i j := by
  intro i j hij
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; simp [rangeProd_self, Nat.mul_one]
  | succ n ih =>
    by_cases hi : i = n + 1
    · subst hi; rw [rangeProd_self, Nat.mul_one]
    · have hle : i ≤ n := by omega
      have hlt : i < n + 1 := by omega
      rw [rangeProd_succ hlt, prod_succ, ih hle, Nat.mul_assoc]

/-- **Cycle product identity**: when the walk returns to the same residue,
    the product of intermediate multipliers is ≡ 1 mod q. -/
theorem cycle_product_one {q : Nat} (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) {i j : Nat} (hij : i < j)
    (hcycle : prod i % q = prod j % q) :
    rangeProd i j % q = 1 := by
  have hge : 2 ≤ q := hq.1
  have hle : i ≤ j := by omega
  have hdecomp := prod_eq_mul_rangeProd i j hle
  -- prod(i) % q = prod(j) % q = (prod(i) * rangeProd(i,j)) % q
  have hstep : prod i % q = (prod i % q * (rangeProd i j % q)) % q := by
    rw [← Nat.mul_mod, ← hdecomp]; exact hcycle
  -- Same coprime cancellation as in walk_step_one_of_eq
  have hc_ne : prod i % q ≠ 0 := prod_mod_ne_zero hq hne i
  have hc_lt : prod i % q < q := Nat.mod_lt _ (by omega)
  have hr_lt : rangeProd i j % q < q := Nat.mod_lt _ (by omega)
  -- rangeProd i j % q ≥ 1 (if it were 0, then c = (c*0)%q = 0, contradiction)
  have hr_pos : 1 ≤ rangeProd i j % q := by
    match h : rangeProd i j % q with
    | 0 => rw [h, Nat.mul_zero, Nat.zero_mod] at hstep; exact absurd hstep hc_ne
    | _ + 1 => omega
  -- From c = (c * r) % q, derive c * r - c ≡ 0 (mod q)
  have hdm := Nat.div_add_mod (prod i % q * (rangeProd i j % q)) q
  rw [← hstep] at hdm
  have hdvd : q ∣ (prod i % q * (rangeProd i j % q) - prod i % q) :=
    ⟨(prod i % q * (rangeProd i j % q)) / q, by omega⟩
  -- Factor: c * r - c = c * (r - 1)
  have hfac : prod i % q * (rangeProd i j % q) - prod i % q =
              prod i % q * (rangeProd i j % q - 1) := by
    have h := Nat.mul_add (prod i % q) (rangeProd i j % q - 1) 1
    rw [Nat.mul_one, Nat.sub_add_cancel (show 1 ≤ rangeProd i j % q by omega)] at h
    omega
  rw [hfac] at hdvd
  -- Coprime cancellation
  have hcop : Nat.Coprime q (prod i % q) :=
    coprime_of_prime_not_dvd hq (fun h => by
      have := Nat.le_of_dvd (by omega) h; omega)
  have hdvd_comm : q ∣ (rangeProd i j % q - 1) * (prod i % q) := by
    rwa [Nat.mul_comm]
  have hdvd_r1 : q ∣ (rangeProd i j % q - 1) := hcop.dvd_of_dvd_mul_right hdvd_comm
  -- r - 1 < q and q ∣ (r - 1), so r - 1 = 0
  rcases hdvd_r1 with ⟨k, hk⟩
  match k with
  | 0 => omega
  | k + 1 =>
    have hle' : q ≤ q * (k + 1) :=
      calc q = q * 1 := (Nat.mul_one q).symm
        _ ≤ q * (k + 1) := Nat.mul_le_mul_left q (by omega)
    omega

/-- **Walk cycle exists**: for any starting index N, there exist i < j within
    N ≤ i < j < N + q such that the product of multipliers seq(i+1)...seq(j)
    is ≡ 1 mod q. This follows from pigeonhole (collision) + coprime cancellation
    (cycle product identity). -/
theorem walk_cycle_exists {q : Nat} (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (N : Nat) :
    ∃ i j, N ≤ i ∧ i < j ∧ j < N + q ∧ rangeProd i j % q = 1 := by
  obtain ⟨i, j, hNi, hij, hjN, hcycle⟩ := walk_has_collision hq hne N
  exact ⟨i, j, hNi, hij, hjN, cycle_product_one hq hne hij hcycle⟩

/-- **Infinitely many unit cycles**: the walk produces unit-product cycles
    starting from arbitrarily late indices. This is the "pumping" phenomenon:
    the walk must repeatedly loop in (ℤ/qℤ)×. -/
theorem walk_infinitely_many_cycles {q : Nat} (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) :
    ∀ N, ∃ i j, N ≤ i ∧ i < j ∧ rangeProd i j % q = 1 := by
  intro N
  obtain ⟨i, j, hNi, hij, _, hunit⟩ := walk_cycle_exists hq hne N
  exact ⟨i, j, hNi, hij, hunit⟩

end

-- ============================================================================
-- THE REDUCTION CHAIN (summary)
--
-- We have established the following chain of implications:
--
--     WalkCoverage → HH → MullinConjecture
--                    DWH → MullinConjecture   (Part 7)
--
-- All arrows are proved, sorry-free, in this file. The open conjectures
-- are WalkCoverage, HH, and DWH. The DWH is likely too strong (Part 8
-- adversary obstacle). The HH is the right target. WalkCoverage would
-- imply HH and is the natural equidistribution statement.
--
-- STRUCTURAL RESULTS PROVED (Part 9):
--
-- (1) Bridge lemma: q ∣ (a+1) ↔ a % q = q-1   (dvd_succ_iff_mod_pred)
-- (2) Walk recurrence: prod(n+1) % q = ...       (prod_succ_mod)
-- (3) Residue invariants: seq(n), prod(n) ≢ 0    (seq_mod_ne_zero, etc.)
-- (4) HH ↔ ResidueHitting equivalence            (hh_iff_rh)
-- (5) WalkCoverage → HH → MullinConjecture       (wc_implies_mullin)
-- (6) Walk cancellation: stationary ⟹ mult ≡ 1  (walk_step_one_of_eq)
-- (7) Non-stationarity: constant walk ⟹ all ≡ 1 (constant_walk_all_units)
-- (8) Auto-hit: prod(n) ≡ -1 (mod seq(n+1))      (auto_hit_mod)
-- (9) Co-hitting: q ∣ (prod n + 1) ⟹ walk at -1 (co_hit)
-- (10) Capture trigger: seq(k+1) = q ⟹ was at -1 (hit_before_capture)
-- (11) Forced motion: mult ≢ 1 ⟹ walk moves     (walk_moves_of_neq_one)
-- (12) Walk non-constant from start                 (walk_nonconstant_start)
-- (13) Pigeonhole principle: n+1 values in {1..n}   (pigeonhole)
-- (14) Walk collision: ∃ repeat in q steps          (walk_has_collision)
-- (15) Range product decomposition                   (prod_eq_mul_rangeProd)
-- (16) Cycle product ≡ 1: collision ⟹ unit cycle   (cycle_product_one)
-- (17) Walk cycle exists: collision + unit cycle     (walk_cycle_exists)
-- (18) Infinitely many cycles: pumping phenomenon    (walk_infinitely_many_cycles)
--
-- WHAT REMAINS: the hard number-theoretic core.
--
-- The structural framework reduces HH to: for every prime q not in the
-- sequence, eventually some Euclid number prod(n) + 1 is divisible by q.
-- Equivalently, the residue walk prod(n) % q eventually hits q-1.
--
-- The auto-hit property shows the walk DOES hit -1 mod seq(n+1) at every
-- step n — but mod the WRONG prime. The question is whether q can be
-- "co-hit" along with seq(n+1) at some step.
--
-- Three approaches to proving this (see docs/routes_to_conjecture_a.md):
--
-- (A) SIEVE + EQUIDISTRIBUTION (Route 2): show the multiplier residues
--     seq(n) mod q equidistribute, forcing the walk to cover (ℤ/qℤ)×.
--     Requires Bombieri–Vinogradov or related sieve bounds.
--
-- (B) SUBGROUP ESCAPE + MIXING (Route 1+3): show multiplier residues
--     generate (ℤ/qℤ)×, then prove the walk mixes. Mixing requires
--     care: even full generation doesn't guarantee coverage (the
--     alternating-multipliers counterexample shows this). The EM
--     sequence's ALL-DISTINCT-PRIMES constraint prevents exact
--     periodicity but formalizing this is essentially as hard as HH.
--
-- (C) FACTORING CONNECTION (Route 4): HH failing would mean minFac
--     has a systematic bias mod q — which would yield a new factoring
--     technique. The non-existence of such bias (widely believed)
--     would prove HH.
--
-- The precise interface between sieve theory and formal proof is the
-- main obstacle. The structural results in this file reduce the
-- problem to its essential number-theoretic core.
-- ============================================================================

/-! ## Concrete Mullin Conjecture instances

Direct verification that specific primes appear in the EM sequence.
Each follows immediately from the computed sequence values. -/

theorem mullin_for_two : ∃ n, seq n = 2 := ⟨0, rfl⟩
theorem mullin_for_three : ∃ n, seq n = 3 := ⟨1, seq_one⟩
theorem mullin_for_five : ∃ n, seq n = 5 := ⟨6, seq_six⟩
theorem mullin_for_seven : ∃ n, seq n = 7 := ⟨2, seq_two⟩
theorem mullin_for_thirteen : ∃ n, seq n = 13 := ⟨4, seq_four⟩
theorem mullin_for_fortythree : ∃ n, seq n = 43 := ⟨3, seq_three⟩
theorem mullin_for_fiftythree : ∃ n, seq n = 53 := ⟨5, seq_five⟩

end Mullin
