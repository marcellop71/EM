import EM.Population.GrandOrbit
import EM.Population.WeakErgodicity

/-!
# The gap principle for missed primes

2026-09-24.  A missed prime is not one bad seed but a whole infinite family of them.  If a seed
`m` misses the prime `q`, so does every point `genProd m k` of its forward orbit
(`GrowingRange.misses_genProd_iff`).  The orbit points are distinct and grow at most doubly
exponentially, `genProd m k + 1 ≤ (m+1)^(2^k)`.  Hence:

* `card_misses_ge` — if `m ≥ 1` misses `q`, then for every `k` at least `k + 1` seeds in
  `[1, (m+1)^(2^k)]` miss `q`;
* `card_misses_ge_of_squarefree` — for squarefree `m` also the halves `genProd m j / 2`
  (`1 ≤ j ≤ k`) miss `q`: they are odd `T`-preimages of the even orbit points, so at least
  `2k` seeds;
* `misses_eq_empty_or` — **gap principle**: for every prime `q` the set of seeds missing `q`
  is either empty, or has at least `k + 1` elements below `3^(2^k)` for every `k`
  (roughly `log₂ log X` below `X`);
* `mem_seq_of_card_misses_lt` — the Euclid–Mullin form: if for some `k` fewer than `2k` seeds in
  `[1, 3^(2^k)]` miss `q`, then `q` appears in the Euclid–Mullin sequence.

**Scope.**  The seed-average law gives `#{m ≤ X : m misses q} = o(X)` with no rate; the gap
principle asks for `o(log log X)`.  Nothing bridges the two, so this is a precise statement of
how much "few" must mean, not progress on MC.  See
`docs/analysis/euclid_systems_theory_2026-09-23.md` §7.
-/

noncomputable section
open Classical

namespace GapPrinciple

open GrowingRange (Misses misses_genProd_iff misses_genProd_one_iff)

/-- One greedy step at most squares `P + 1`. -/
theorem genProd_succ_add_one_le_sq (m k : ℕ) :
    genProd m (k + 1) + 1 ≤ (genProd m k + 1) ^ 2 := by
  rw [genProd_succ, genSeq_def]
  have h : Nat.minFac (genProd m k + 1) ≤ genProd m k + 1 :=
    Nat.minFac_le (Nat.succ_pos _)
  have := Nat.mul_le_mul_left (genProd m k) h
  nlinarith

/-- Doubly exponential growth bound: `genProd m k + 1 ≤ (m+1)^(2^k)`. -/
theorem genProd_add_one_le_pow (m k : ℕ) : genProd m k + 1 ≤ (m + 1) ^ (2 ^ k) := by
  induction k with
  | zero => simp [genProd]
  | succ k ih =>
    calc genProd m (k + 1) + 1 ≤ (genProd m k + 1) ^ 2 := genProd_succ_add_one_le_sq m k
      _ ≤ ((m + 1) ^ (2 ^ k)) ^ 2 := Nat.pow_le_pow_left ih 2
      _ = (m + 1) ^ (2 ^ (k + 1)) := by rw [← pow_mul, pow_succ]

theorem genProd_strictMono {m : ℕ} (hm : 1 ≤ m) : StrictMono (genProd m) :=
  strictMono_nat_of_lt_succ (genProd_strict_mono hm)

/-- The seeds in `[1, X]` missing `q`. -/
def missSet (q X : ℕ) : Finset ℕ := (Finset.Icc 1 X).filter (fun m => Misses q m)

/-- **Forward-orbit count.**  If `m ≥ 1` misses the prime `q`, the `k + 1` orbit points
`genProd m 0, …, genProd m k` are distinct seeds in `[1, (m+1)^(2^k)]` missing `q`. -/
theorem card_misses_ge {q m : ℕ} (hq : q.Prime) (hm : 1 ≤ m) (hmiss : Misses q m) (k : ℕ) :
    k + 1 ≤ (missSet q ((m + 1) ^ (2 ^ k))).card := by
  have hinj : Set.InjOn (genProd m) (Finset.range (k + 1) : Set ℕ) :=
    (genProd_strictMono hm).injective.injOn
  have hsub : (Finset.range (k + 1)).image (genProd m) ⊆ missSet q ((m + 1) ^ (2 ^ k)) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨genProd_pos hm j, ?_⟩,
      (misses_genProd_iff hq j).mpr hmiss⟩
    calc genProd m j ≤ genProd m k := (genProd_strictMono hm).monotone hj'
      _ ≤ (m + 1) ^ (2 ^ k) := by have := genProd_add_one_le_pow m k; omega
  calc k + 1 = ((Finset.range (k + 1)).image (genProd m)).card := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    _ ≤ _ := Finset.card_le_card hsub

/-! ## The free backward branch: halves of the orbit points -/

/-- After one step the accumulator is even. -/
theorem two_dvd_genProd {m k : ℕ} (hk : 1 ≤ k) : 2 ∣ genProd m k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = 1 + j := ⟨k - 1, by omega⟩
  rw [← genProd_restart]
  have h := genProd_dvd_genProd (genProd m 1) 0 j
  rw [Nat.zero_add] at h
  exact (ProfiniteAttractor.two_dvd_genProd_one m).trans h

/-- If `N` is even and `N/2` is odd, then `N/2` is a `T`-preimage of `N`: `N/2 + 1` is even,
so its least prime factor is `2`. -/
theorem genProd_half {N : ℕ} (h2 : 2 ∣ N) (hodd : ¬ 2 ∣ N / 2) : genProd (N / 2) 1 = N := by
  have hmin : Nat.minFac (N / 2 + 1) = 2 := by
    have : 2 ∣ N / 2 + 1 := by omega
    exact (Nat.minFac_eq_two_iff _).mpr this
  show N / 2 * Nat.minFac (N / 2 + 1) = N
  rw [hmin]
  exact Nat.div_mul_cancel h2

/-- For a squarefree seed, the half of every later orbit point is odd. -/
theorem half_odd {m k : ℕ} (hsq : Squarefree m) (hk : 1 ≤ k) : ¬ 2 ∣ genProd m k / 2 := by
  intro h
  have h2 := two_dvd_genProd (m := m) hk
  have h4 : 2 * 2 ∣ genProd m k := by
    obtain ⟨a, ha⟩ := h2
    obtain ⟨b, hb⟩ := h
    exact ⟨b, by rw [ha] at hb ⊢; omega⟩
  have := (genProd_squarefree hsq k) 2 h4
  simp at this

/-- The halves miss `q` whenever the seed does. -/
theorem misses_half {q m k : ℕ} (hq : q.Prime) (hsq : Squarefree m) (hk : 1 ≤ k)
    (hmiss : Misses q m) : Misses q (genProd m k / 2) := by
  have hT := genProd_half (two_dvd_genProd (m := m) hk) (half_odd hsq hk)
  rw [← misses_genProd_one_iff hq, hT]
  exact (misses_genProd_iff hq k).mpr hmiss

/-- **Orbit plus halves.**  For squarefree `m ≥ 1` missing `q`, at least `2k` seeds in
`[1, (m+1)^(2^k)]` miss `q`: the even orbit points `genProd m j` (`1 ≤ j ≤ k`) and their odd
halves.  (For odd `m` the seed itself is the half of `genProd m 1`, which is why index `0` is
left out.) -/
theorem card_misses_ge_of_squarefree {q m : ℕ} (hq : q.Prime) (hm : 1 ≤ m)
    (hsq : Squarefree m) (hmiss : Misses q m) (k : ℕ) :
    2 * k ≤ (missSet q ((m + 1) ^ (2 ^ k))).card := by
  set X := (m + 1) ^ (2 ^ k)
  have hmono := genProd_strictMono hm
  have hbound : ∀ j ≤ k, genProd m j ≤ X := fun j hj => by
    have := genProd_add_one_le_pow m k
    exact (hmono.monotone hj).trans (by omega)
  set A := (Finset.Icc 1 k).image (genProd m)
  set B := (Finset.Icc 1 k).image (fun j => genProd m j / 2)
  have hA : A.card = k := by
    rw [Finset.card_image_of_injOn (hmono.injective.injOn), Nat.card_Icc, Nat.add_sub_cancel]
  have hB : B.card = k := by
    rw [Finset.card_image_of_injOn, Nat.card_Icc, Nat.add_sub_cancel]
    intro i hi j hj hij
    have hi2 := Nat.div_mul_cancel (two_dvd_genProd (m := m) (Finset.mem_Icc.mp hi).1)
    have hj2 := Nat.div_mul_cancel (two_dvd_genProd (m := m) (Finset.mem_Icc.mp hj).1)
    have hij' : genProd m i / 2 = genProd m j / 2 := hij
    exact hmono.injective (by rw [← hi2, ← hj2, hij'])
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxA
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hxB
    have hodd := half_odd hsq (Finset.mem_Icc.mp hj).1
    rw [hji] at hodd
    exact hodd (two_dvd_genProd (Finset.mem_Icc.mp hi).1)
  have hsub : A ∪ B ⊆ missSet q X := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨genProd_pos hm j,
        hbound j (Finset.mem_Icc.mp hj).2⟩, (misses_genProd_iff hq j).mpr hmiss⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      have hj1 := (Finset.mem_Icc.mp hj).1
      have hmiss' := misses_half hq hsq hj1 hmiss
      have hpos : 1 ≤ genProd m j / 2 := by
        have h2 := two_dvd_genProd (m := m) hj1
        have := genProd_pos hm j
        omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpos,
        (Nat.div_le_self _ _).trans (hbound j (Finset.mem_Icc.mp hj).2)⟩, hmiss'⟩
  calc 2 * k = (A ∪ B).card := by rw [Finset.card_union_of_disjoint hdisj, hA, hB]; ring
    _ ≤ _ := Finset.card_le_card hsub

/-! ## The gap principle -/

/-- **Gap principle.**  For a prime `q`, the seeds missing `q` either do not exist, or every
missing seed `m ≥ 1` forces at least `k + 1` of them below `(m+1)^(2^k)`, for every `k`.  So a
nonempty missing set has at least about `log₂ log X` elements below `X`. -/
theorem misses_eq_empty_or {q : ℕ} (hq : q.Prime) :
    (∀ m, 1 ≤ m → ¬ Misses q m) ∨
      ∃ m, 1 ≤ m ∧ ∀ k, k + 1 ≤ (missSet q ((m + 1) ^ (2 ^ k))).card := by
  by_cases h : ∃ m, 1 ≤ m ∧ Misses q m
  · obtain ⟨m, hm, hmiss⟩ := h
    exact Or.inr ⟨m, hm, card_misses_ge hq hm hmiss⟩
  · exact Or.inl fun m hm hmiss => h ⟨m, hm, hmiss⟩

/-- **The Euclid–Mullin form.**  If for some `k` fewer than `2k` seeds in `[1, 3^(2^k)]`
miss the prime `q`, then `q` appears in the Euclid–Mullin sequence. -/
theorem mem_seq_of_card_misses_lt {q : ℕ} (hq : q.Prime) {k : ℕ}
    (hfew : (missSet q (3 ^ (2 ^ k))).card < 2 * k) : ∃ n, Mullin.seq n = q := by
  by_contra hne
  push Not at hne
  have h2 : Misses q 2 := (GrandOrbit.misses_two_iff hq).mpr hne
  have := card_misses_ge_of_squarefree hq (by norm_num) Nat.squarefree_two h2 k
  norm_num at this
  omega

/-! ## Backward branches of the orbit: the deleted walks

An ancestor of `P_n` other than `P_{n-1}` is `P_n / p` for a bag prime `p` with
`lpf (P_n/p + 1) = p`.  When every prime below `p` is in the bag this is one congruence,
`P_n / p ≡ −1 (mod p)`: the **`p`-deleted walk** — the walk of the product of the other bag
primes — hits `−1`.  Amplifying a missed prime into more missing seeds is therefore a hitting
problem for *captured* primes.  For `p = 3` it is a parity: the branch exists iff an even number
of the primes `seq 2, …, seq n` are `≡ 2 (mod 3)`. -/

/-- **Branch criterion.**  If `p ∣ N` and every prime below `p` divides `N`, then `N / p` is a
`T`-preimage of `N` iff `N / p ≡ −1 (mod p)`. -/
theorem isPreimage_div_iff {N p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (hN : 0 < N)
    (hbelow : ∀ r, r.Prime → r < p → r ∣ N) :
    GrandOrbit.IsPreimage (N / p) N ↔ p ∣ N / p + 1 := by
  have hpos : 0 < N / p := Nat.div_pos (Nat.le_of_dvd hN hpN) hp.pos
  rw [GrandOrbit.preimage_iff]
  constructor
  · rintro ⟨-, q, hq, hqN, hdiv, hmin⟩
    have hpq : p = q := by
      have h1 := Nat.div_mul_cancel hpN
      have h2 := Nat.div_mul_cancel hqN
      rw [← hdiv] at h2
      have : N / p * p = N / p * q := by rw [h1, h2]
      exact Nat.eq_of_mul_eq_mul_left hpos this
    subst hpq
    have := Nat.minFac_dvd (N / p + 1)
    rwa [hmin] at this
  · intro hdvd
    refine ⟨hpos, p, hp, hpN, rfl, ?_⟩
    apply le_antisymm
    · exact Nat.minFac_le_of_dvd hp.two_le hdvd
    · by_contra hlt
      push Not at hlt
      have hr : (Nat.minFac (N / p + 1)).Prime := Nat.minFac_prime (by omega)
      have hrN : Nat.minFac (N / p + 1) ∣ N := hbelow _ hr hlt
      have hrp : Nat.minFac (N / p + 1) ≠ p := hlt.ne
      have hrNp : Nat.minFac (N / p + 1) ∣ N / p := by
        have : Nat.minFac (N / p + 1) ∣ p * (N / p) := by
          rwa [Nat.mul_div_cancel' hpN]
        rcases (Nat.Prime.dvd_mul hr).mp this with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hr hp).mp h) hrp
        · exact h
      have := (Nat.dvd_add_right hrNp).mp (Nat.minFac_dvd (N / p + 1))
      exact hr.one_lt.ne' (Nat.dvd_one.mp this)

open Mullin in
/-- Along the Euclid–Mullin orbit, for `n ≥ 1`: `prod n / 3` is a `T`-preimage of `prod n`
iff `prod n / 3 ≡ −1 (mod 3)`. -/
theorem isPreimage_prod_div_three_iff {n : ℕ} (hn : 1 ≤ n) :
    GrandOrbit.IsPreimage (prod n / 3) (prod n) ↔ 3 ∣ prod n / 3 + 1 := by
  apply isPreimage_div_iff Nat.prime_three
  · have := seq_dvd_prod 1 n hn
    rwa [seq_one] at this
  · have := prod_ge_two n; omega
  · intro r hr hr3
    have : r = 2 := by
      interval_cases r <;> simp_all (config := {decide := true})
    subst this
    have := seq_dvd_prod 0 n (Nat.zero_le _)
    rwa [seq_zero] at this

open Mullin in
/-- The number of primes among `seq 2, …, seq n` that are `≡ 2 (mod 3)`. -/
def twoModThreeCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun i => 2 ≤ i ∧ seq i % 3 = 2)).card

open Mullin in
theorem seq_mod_three {i : ℕ} (hi : 2 ≤ i) : seq i % 3 = 1 ∨ seq i % 3 = 2 := by
  have hprime := (MullinGroup.isPrime_iff_natPrime _).mp (seq_isPrime i)
  have hne : seq i ≠ 3 := by
    intro h
    have := seq_injective i 1 (by rw [h, seq_one])
    omega
  have h3 : ¬ 3 ∣ seq i := fun h =>
    hne ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hprime).mp h).symm
  omega

open Mullin in
/-- **The `3`-deleted walk is a parity.**  For `n ≥ 1`, `3 ∣ prod n / 3 + 1` iff an even number
of the primes `seq 2, …, seq n` are `≡ 2 (mod 3)`. -/
theorem three_dvd_prod_div_three_succ_iff {n : ℕ} (hn : 1 ≤ n) :
    3 ∣ prod n / 3 + 1 ↔ Even (twoModThreeCount n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · -- `prod 1 = 6`
      have h6 : prod 1 = 6 := by rw [prod_succ, prod_zero, seq_one]
      rw [h6]
      have hempty : (Finset.range 2).filter (fun i => 2 ≤ i ∧ seq i % 3 = 2) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro i hi
        rw [Finset.mem_range] at hi
        omega
      simp only [twoModThreeCount, zero_add, Nat.reduceAdd]
      rw [hempty]
      simp
    · have h3 : 3 ∣ prod n := by have := seq_dvd_prod 1 n hn'; rwa [seq_one] at this
      have hdiv : prod (n + 1) / 3 = prod n / 3 * seq (n + 1) := by
        rw [prod_succ, Nat.mul_div_right_comm h3]
      have hcount : twoModThreeCount (n + 1)
          = twoModThreeCount n + if (2 ≤ n + 1 ∧ seq (n + 1) % 3 = 2) then 1 else 0 := by
        unfold twoModThreeCount
        rw [Finset.range_add_one, Finset.filter_insert]
        split_ifs with h
        · rw [Finset.card_insert_of_notMem (by simp)]
        · rfl
      have hu : ¬ 3 ∣ prod n / 3 := by
        intro h
        have h9 : 3 * 3 ∣ prod n := by
          obtain ⟨k, hk⟩ := h
          exact ⟨k, by rw [← Nat.div_mul_cancel h3, hk]; ring⟩
        have := (prod_squarefree n) 3 h9
        simp at this
      have hs := seq_mod_three (i := n + 1) (by omega)
      have ih' := ih hn'
      have e1 : 3 ∣ prod n / 3 + 1 ↔ prod n / 3 % 3 = 2 := by omega
      have e2 : 3 ∣ prod n / 3 * seq (n + 1) + 1 ↔ (prod n / 3 * seq (n + 1)) % 3 = 2 := by
        omega
      have key : (prod n / 3 * seq (n + 1)) % 3 = ((prod n / 3) % 3 * (seq (n + 1) % 3)) % 3 :=
        Nat.mul_mod _ _ _
      have hu' : prod n / 3 % 3 = 1 ∨ prod n / 3 % 3 = 2 := by omega
      have h2 : 2 ≤ n + 1 := by omega
      rw [hdiv, hcount, e2, key]
      rw [e1] at ih'
      rcases hs with hs | hs <;> rcases hu' with hu' | hu' <;>
        simp [hs, hu', h2, Nat.even_add_one] at ih' ⊢ <;> tauto

end GapPrinciple

end
