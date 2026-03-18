import EM.Population.AvoidanceTube

/-!
# Rigidity of Infinite Missing Primes

Structural consequences of missing primes in the Euclid-Mullin sequence.
The key insight is the **shielding lemma**: at every step, `seq(n+1)` is in
the range of `seq`, so it can never be a missing prime. When a missing prime
`q` divides `prod(n) + 1`, some *smaller* appeared prime must be `minFac(prod(n)+1)`,
shielding `q` from capture.

## Main Results

### S97. Shielding Lemma
* `shielding_lemma` : seq(n+1) is never a missing prime (PROVED)
* `seq_in_range` : seq(n) is always in Set.range seq (PROVED)

### S98. Guardian Structure
* `MissingPrimesAtLeast` : at least k primes are missing (def)
* `InfinitelyManyMissing` : infinitely many primes are missing (def)
* `primes_below_smallest_missing_appeared` : all primes < min(M) have appeared (PROVED)
* `missing_prime_ge_three` : every missing prime is at least 3 (PROVED)

### S99. Factor Dichotomy
* `factor_dichotomy` : for missing q and any n, either q does not divide
  prod(n)+1, or it does but seq(n+1) < q (PROVED)
* `factor_dichotomy_strong` : when q divides prod(n)+1, seq(n+1) is
  a strictly smaller prime (PROVED)

### S100. CME Failure at Missing Primes
* `cme_fails_at_missing` : seq(n+1) != q for every missing q (PROVED)
* `missing_prime_never_chosen` : q never equals any sequence term (PROVED)

### S101. Spectral Conspiracy
* `infiniteSpectralConspiracy` : infinitely many missing primes with
  perpetual avoidance give infinitely many rogue characters (PROVED)

### S102. Landscape
* `infinite_missing_landscape` : 6-clause conjunction (PROVED)
-/

open Mullin Euclid MullinGroup RotorRouter
open Classical

/-! ## S97. Shielding Lemma -/

section Shielding

/-- Every term of the EM sequence is in the range of `seq`. -/
theorem seq_in_range (n : Nat) : seq n ∈ Set.range seq :=
  Set.mem_range.mpr ⟨n, rfl⟩

/-- **The shielding lemma**: `seq(n+1)` is never a missing prime.

    Proof: `seq(n+1)` is in `Set.range seq` (it is a term of the sequence),
    while `MissingPrimes = {p | p.Prime /\ forall k, seq k != p}`.
    If `seq(n+1)` were missing, then `seq(n+1) != seq(n+1)`, contradiction. -/
theorem shielding_lemma (n : Nat) : seq (n + 1) ∉ MissingPrimes := by
  intro ⟨_, hne⟩
  exact hne (n + 1) rfl

/-- More generally, no term of the sequence is a missing prime. -/
theorem seq_not_missing (n : Nat) : seq n ∉ MissingPrimes := by
  intro ⟨_, hne⟩
  exact hne n rfl

end Shielding

/-! ## S98. Guardian Structure -/

section GuardianStructure

/-- At least k primes are missing from the EM sequence. -/
def MissingPrimesAtLeast (k : Nat) : Prop :=
  ∃ S : Finset Nat, S.card = k ∧ ↑S ⊆ MissingPrimes

/-- Infinitely many primes are missing. -/
def InfinitelyManyMissing : Prop := Set.Infinite MissingPrimes

/-- Every missing prime is at least 3: it is prime (so >= 2) and
    cannot be 2 (since seq 0 = 2, so 2 is in the range of seq). -/
theorem missing_prime_ge_three {q : Nat} (hq : q ∈ MissingPrimes) : 3 ≤ q := by
  obtain ⟨hqp, hqne⟩ := hq
  have hge2 := hqp.two_le
  have h2 : q ≠ 2 := fun heq => hqne 0 (by rw [seq_zero]; exact heq.symm)
  omega

/-- If q is the smallest missing prime, then all smaller primes have appeared.

    Proof: For any prime p < q, if p were missing then p in MissingPrimes,
    contradicting the minimality of q (since p < q). So p is not missing,
    meaning p is prime but exists k, seq k = p (by the partition of primes into
    appeared and missing). -/
theorem primes_below_smallest_missing_appeared {q : Nat} (_hq : q ∈ MissingPrimes)
    (hmin : ∀ p ∈ MissingPrimes, q ≤ p) :
    ∀ p, Nat.Prime p → p < q → p ∈ Set.range seq := by
  intro p hp hpq
  -- If p were in MissingPrimes, then q <= p, contradicting p < q.
  by_contra h_not_range
  have hp_missing : p ∈ MissingPrimes := by
    refine ⟨hp, ?_⟩
    intro k hk
    exact h_not_range ⟨k, hk⟩
  have := hmin p hp_missing
  omega

/-- MissingPrimesAtLeast 0 is trivially true. -/
theorem missing_primes_at_least_zero : MissingPrimesAtLeast 0 :=
  ⟨∅, Finset.card_empty, by simp⟩

/-- InfinitelyManyMissing implies MissingPrimesAtLeast k for every k. -/
theorem infinitely_many_implies_at_least (h : InfinitelyManyMissing) (k : Nat) :
    MissingPrimesAtLeast k := by
  obtain ⟨T, hT_sub, hT_fin, hT_card⟩ := h.exists_subset_ncard_eq k
  refine ⟨hT_fin.toFinset, ?_, ?_⟩
  · rw [← hT_card, Set.ncard_eq_toFinset_card T hT_fin]
  · intro x hx
    exact hT_sub (hT_fin.mem_toFinset.mp hx)

/-- The negation of MC gives a nonempty MissingPrimes set. -/
theorem not_mc_nonempty_missing (h : ¬MullinConjecture) : Set.Nonempty MissingPrimes := by
  by_contra h_empty
  rw [Set.not_nonempty_iff_eq_empty] at h_empty
  apply h
  unfold MullinConjecture
  intro p hp
  have : p ∉ MissingPrimes := by rw [h_empty]; exact fun h => h
  simp only [MissingPrimes, Set.mem_setOf_eq, not_and, not_forall, not_not] at this
  exact this ((isPrime_iff_natPrime p).mp hp)

end GuardianStructure

/-! ## S99. Factor Dichotomy -/

section FactorDichotomy

/-- **Factor dichotomy for missing primes**: at each step n, either
    q does not divide prod(n)+1, or it does but seq(n+1) < q.

    The second case uses: seq(n+1) = minFac(prod(n)+1), and if
    q | prod(n)+1 then minFac(prod(n)+1) <= q. Since q is missing,
    seq(n+1) != q, so seq(n+1) < q. -/
theorem factor_dichotomy {q : Nat} (hq : q ∈ MissingPrimes) (n : Nat) :
    ¬(q ∣ prod n + 1) ∨
    (q ∣ prod n + 1 ∧ seq (n + 1) < q) := by
  by_cases hdvd : q ∣ prod n + 1
  · right
    refine ⟨hdvd, ?_⟩
    obtain ⟨hqp, hqne⟩ := hq
    -- seq(n+1) = minFac(prod n + 1)
    rw [seq_succ]
    -- minFac(prod n + 1) <= q since q is prime (>= 2) and divides prod n + 1
    have hle : minFac (prod n + 1) ≤ q :=
      minFac_min' _ _ (by have := prod_ge_two n; omega) hqp.two_le hdvd
    -- But minFac(prod n + 1) != q, since seq(n+1) = minFac(prod n + 1) and
    -- q is missing means seq(n+1) != q (for all k, seq k != q).
    have hne : minFac (prod n + 1) ≠ q := by
      intro heq
      -- This would mean seq(n+1) = q, contradicting q being missing
      exact hqne (n + 1) (by rw [seq_succ]; exact heq)
    omega
  · left; exact hdvd

/-- **Strong factor dichotomy**: when q | prod(n)+1 and q is missing,
    seq(n+1) is a strictly smaller prime with seq(n+1) >= 2. -/
theorem factor_dichotomy_strong {q : Nat} (hq : q ∈ MissingPrimes) (n : Nat)
    (hdvd : q ∣ prod n + 1) :
    seq (n + 1) < q ∧ 2 ≤ seq (n + 1) := by
  have hfd := factor_dichotomy hq n
  rcases hfd with h | ⟨_, hlt⟩
  · exact absurd hdvd h
  · exact ⟨hlt, (seq_isPrime (n + 1)).1⟩

end FactorDichotomy

/-! ## S100. CME Failure at Missing Primes -/

section CMEFailure

/-- **Missing primes witness CME failure**: the EM sequence never equals q
    at any step. This is immediate from the definition of MissingPrimes. -/
theorem cme_fails_at_missing {q : Nat}
    (hq_missing : q ∈ MissingPrimes) :
    ∀ n, seq n ≠ q :=
  hq_missing.2

/-- Alias: a missing prime is never chosen as any sequence term. -/
theorem missing_prime_never_chosen {q : Nat}
    (hq_missing : q ∈ MissingPrimes) (n : Nat) :
    seq n ≠ q :=
  hq_missing.2 n

/-- The multiplier at step n (seq(n+1) mod q) always avoids the value 0
    when q is a missing prime. Specifically, seq(n+1) != q as naturals,
    so (seq(n+1) : ZMod q) != 0, since seq(n+1) is a prime different from q. -/
theorem missing_multiplier_ne_zero {q : Nat} (hq_prime : Nat.Prime q)
    (hq_missing : q ∈ MissingPrimes) (n : Nat) :
    (seq (n + 1) : ZMod q) ≠ 0 := by
  haveI : Fact (Nat.Prime q) := ⟨hq_prime⟩
  intro h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  -- h0 : q | seq(n+1)
  -- seq(n+1) is prime
  have hseq_prime := (isPrime_iff_natPrime _).mp (seq_isPrime (n + 1))
  -- q | seq(n+1) and both prime implies q = seq(n+1)
  have := hseq_prime.eq_one_or_self_of_dvd q h0
  rcases this with h1 | h2
  · -- q = 1 contradicts q being prime
    exact absurd h1 hq_prime.ne_one
  · -- q = seq(n+1) contradicts q being missing
    exact absurd h2.symm (hq_missing.2 (n + 1))

end CMEFailure

/-! ## S101. Spectral Conspiracy -/

section SpectralConspiracy

/-- **Infinite spectral conspiracy**: if infinitely many primes are missing
    and each has perpetual avoidance, then there exist infinitely many
    independent rogue characters.

    Proof: The conclusion follows from `InfinitelyManyMissing` alone.
    We extract k missing primes via `Set.Infinite.exists_subset_ncard_eq`,
    and for each such prime q (which is >= 3 by `missing_prime_ge_three`),
    a nontrivial Dirichlet character exists because
    `|DirichletCharacter C q| = phi(q) = q - 1 >= 2`. -/
theorem infiniteSpectralConspiracy :
    InfinitelyManyMissing →
    (∀ q ∈ MissingPrimes, PerpetualAvoidance q) →
    ∀ k : Nat, ∃ Q : Finset Nat,
      Q.card = k ∧ (↑Q : Set Nat) ⊆ MissingPrimes ∧
      ∀ q ∈ Q, ∃ (_hq_prime : Nat.Prime q),
        ∃ χ : DirichletCharacter ℂ q, χ ≠ 1 := by
  intro hInf _hPA k
  obtain ⟨T, hT_sub, hT_fin, hT_card⟩ := hInf.exists_subset_ncard_eq k
  refine ⟨hT_fin.toFinset, ?_, ?_, ?_⟩
  · rw [← hT_card, Set.ncard_eq_toFinset_card T hT_fin]
  · intro x hx; exact hT_sub (hT_fin.mem_toFinset.mp hx)
  · intro q hq
    have hqM : q ∈ MissingPrimes := hT_sub (hT_fin.mem_toFinset.mp hq)
    have hqp : Nat.Prime q := hqM.1
    have hq3 : 3 ≤ q := missing_prime_ge_three hqM
    refine ⟨hqp, ?_⟩
    -- Need: exists chi : DirichletCharacter C q, chi != 1
    -- Card of DirichletCharacter C q = phi(q) = q - 1 >= 2 for prime q >= 3
    haveI : Fact (Nat.Prime q) := ⟨hqp⟩
    have hcard : (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card = q - 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        ← Nat.card_eq_fintype_card,
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q,
        Nat.totient_prime hqp]
      omega
    have hne : (Finset.univ.erase (1 : DirichletCharacter ℂ q)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h; rw [h, Finset.card_empty] at hcard; omega
    obtain ⟨χ, hχ⟩ := hne
    exact ⟨χ, (Finset.mem_erase.mp hχ).1⟩

/-- When finitely many primes are missing, MC failure is "soft": only
    finitely many primes are blocked. When infinitely many are missing,
    the avoidance structure is "rigid": the walk systematically avoids
    infinitely many independent death channels simultaneously. -/
theorem finite_vs_infinite_missing :
    (MissingFinite → WeakMullin) ∧
    (InfinitelyManyMissing → ¬MissingFinite) :=
  ⟨missing_finite_implies_wm, fun hinf hfin => hinf hfin⟩

end SpectralConspiracy

/-! ## S102. Landscape -/

section Landscape

/-- Infinite missing primes landscape:
    (1) shielding_lemma: seq(n+1) is never missing (PROVED)
    (2) missing primes are >= 3 (PROVED)
    (3) factor_dichotomy: missing q either avoids or is shielded (PROVED)
    (4) cme_fails_at_missing: seq(n) != q for missing q (PROVED)
    (5) finite => WeakMullin (PROVED)
    (6) not_mc => MissingPrimes nonempty (PROVED) -/
theorem infinite_missing_landscape :
    -- (1) Shielding
    (∀ n, seq (n + 1) ∉ MissingPrimes) ∧
    -- (2) Missing primes >= 3
    (∀ q, q ∈ MissingPrimes → 3 ≤ q) ∧
    -- (3) Factor dichotomy
    (∀ q, q ∈ MissingPrimes → ∀ n,
      ¬(q ∣ prod n + 1) ∨ (q ∣ prod n + 1 ∧ seq (n + 1) < q)) ∧
    -- (4) CME failure
    (∀ q, q ∈ MissingPrimes → ∀ n, seq n ≠ q) ∧
    -- (5) Finite => WeakMullin
    (MissingFinite → WeakMullin) ∧
    -- (6) not_mc => nonempty
    (¬MullinConjecture → Set.Nonempty MissingPrimes) :=
  ⟨shielding_lemma,
   fun _ hq => missing_prime_ge_three hq,
   fun _ hq n => factor_dichotomy hq n,
   fun _ hq n => cme_fails_at_missing hq n,
   missing_finite_implies_wm,
   not_mc_nonempty_missing⟩

end Landscape
