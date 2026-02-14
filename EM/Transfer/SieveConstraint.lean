import EM.Transfer.IntegerDioph
import EM.Ensemble.Structure

/-!
# Sieve Constraint Infrastructure: Prime Support of EM Accumulators

The prime support of `prod(n)` (resp. `genProd(m, k)`) is the finite set of
primes appearing in steps 0..n (resp. 0..k-1) of the (generalized) EM sequence.
Every prime in this support divides the accumulator, and therefore does NOT
divide the accumulator + 1. This "+1 shift" is the fundamental sieve constraint
that drives the EM construction.

## Main Definitions

* `emSupport n` -- the set {seq(0), ..., seq(n)} of primes dividing prod(n)
* `genSupport m k` -- the set {genSeq(m, 0), ..., genSeq(m, k-1)}

## Main Theorems

### Phase 1: emSupport basics
* `emSupport_prime` -- every element of emSupport is prime
* `emSupport_card` -- emSupport has n+1 elements
* `emSupport_dvd_prod` -- support elements divide prod(n)
* `emSupport_not_dvd_succ` -- support elements do not divide prod(n)+1
* `prod_succ_mod_emSupport` -- prod(n)+1 mod p = 1 for support primes

### Phase 2: Boundary
* `seq_succ_not_mem_emSupport` -- seq(n+1) is not in emSupport n
* `emSupport_mono` -- emSupport grows monotonically
* `emSupport_ssubset` -- emSupport is strictly monotone

### Phase 3: Generalized sequences
* `genSupport_mono` -- genSupport grows monotonically in k
* `genSupport_card` -- genSupport has exactly k elements
* `genSupport_prime` -- every element of genSupport is prime
* `genSupport_dvd_genProd` -- support elements divide genProd(m, k)
* `genSupport_not_dvd_succ` -- support elements do not divide genProd(m, k)+1

### Phase 4: Specialization
* `genSupport_two_shift` -- genSupport 2 k = image of seq over {1,...,k}
* `emSupport_eq_insert` -- emSupport n = {seq 0} union (image of genSeq 2 over {0,...,n-1})
-/

open Mullin Euclid

/-! ## Phase 1: emSupport definition and basic properties -/

section EmSupport

/-- The prime support of prod(n): the set {seq(0), ..., seq(n)}. -/
def emSupport (n : Nat) : Finset Nat := (Finset.range (n + 1)).image Mullin.seq

/-- Every element of emSupport is prime. -/
theorem emSupport_prime (n : Nat) (p : Nat) (hp : p ∈ emSupport n) : p.Prime := by
  simp only [emSupport, Finset.mem_image, Finset.mem_range] at hp
  obtain ⟨i, _, rfl⟩ := hp
  exact seq_natPrime i

/-- emSupport has n+1 elements (by seq injectivity). -/
theorem emSupport_card (n : Nat) : (emSupport n).card = n + 1 := by
  rw [emSupport, Finset.card_image_of_injective _ (fun _ _ h => seq_injective _ _ h),
      Finset.card_range]

/-- Every prime in the support divides prod(n). -/
theorem emSupport_dvd_prod (n : Nat) (p : Nat) (hp : p ∈ emSupport n) : p ∣ Mullin.prod n := by
  simp only [emSupport, Finset.mem_image, Finset.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  exact seq_dvd_prod i n (by omega)

/-- No prime in the support divides prod(n)+1. -/
theorem emSupport_not_dvd_succ (n : Nat) (p : Nat) (hp : p ∈ emSupport n) :
    ¬(p ∣ Mullin.prod n + 1) := by
  simp only [emSupport, Finset.mem_image, Finset.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  exact seq_not_dvd_prod_succ (by omega : i ≤ n)

/-- prod(n)+1 mod p = 1 for every prime p in the support.
    Since p | prod(n), we have prod(n) + 1 = p * k + 1 for some k,
    so (prod(n) + 1) % p = 1. -/
theorem prod_succ_mod_emSupport (n : Nat) (p : Nat) (hp : p ∈ emSupport n) (hp' : p.Prime) :
    (Mullin.prod n + 1) % p = 1 := by
  have hdvd := emSupport_dvd_prod n p hp
  rw [Nat.add_mod, Nat.dvd_iff_mod_eq_zero.mp hdvd, Nat.zero_add,
      Nat.mod_mod, Nat.mod_eq_of_lt hp'.one_lt]

end EmSupport

/-! ## Phase 2: Boundary properties -/

section Boundary

/-- The next prime in the sequence is NOT in the current support. -/
theorem seq_succ_not_mem_emSupport (n : Nat) : Mullin.seq (n + 1) ∉ emSupport n := by
  intro h
  simp only [emSupport, Finset.mem_image, Finset.mem_range] at h
  obtain ⟨i, hi, heq⟩ := h
  -- seq(i) = seq(n+1) with i < n+1, contradicting injectivity
  have := seq_injective _ _ heq
  omega

/-- emSupport grows monotonically. -/
theorem emSupport_mono {m n : Nat} (h : m ≤ n) : emSupport m ⊆ emSupport n := by
  intro p hp
  simp only [emSupport, Finset.mem_image, Finset.mem_range] at hp ⊢
  obtain ⟨i, hi, rfl⟩ := hp
  exact ⟨i, by omega, rfl⟩

/-- emSupport is strictly monotone: emSupport m is a proper subset of emSupport (m+1). -/
theorem emSupport_ssubset (m : Nat) : emSupport m ⊂ emSupport (m + 1) := by
  constructor
  · exact emSupport_mono (by omega)
  · intro h
    have : Mullin.seq (m + 1) ∈ emSupport (m + 1) := by
      simp only [emSupport, Finset.mem_image, Finset.mem_range]
      exact ⟨m + 1, by omega, rfl⟩
    have := h this
    exact seq_succ_not_mem_emSupport m this

end Boundary

/-! ## Phase 3: Generalized sequences -/

noncomputable section GenSupport

open Classical

/-- For the generalized sequence starting from m, the set of primes appearing
    in the first k steps. -/
def genSupport (m k : Nat) : Finset Nat :=
  (Finset.range k).image (fun i => genSeq m i)

/-- genSupport grows monotonically in k. -/
theorem genSupport_mono (m : Nat) {j k : Nat} (h : j ≤ k) :
    genSupport m j ⊆ genSupport m k := by
  intro p hp
  simp only [genSupport, Finset.mem_image, Finset.mem_range] at hp ⊢
  obtain ⟨i, hi, rfl⟩ := hp
  exact ⟨i, by omega, rfl⟩

/-- genSupport has exactly k elements (by genSeq injectivity) when m is squarefree. -/
theorem genSupport_card {m : Nat} (hm : Squarefree m) (k : Nat) :
    (genSupport m k).card = k := by
  rw [genSupport, Finset.card_image_of_injective _ (genSeq_injective hm), Finset.card_range]

/-- Every element of genSupport is prime. -/
theorem genSupport_prime {m : Nat} (hm : 1 ≤ m) {k : Nat} {p : Nat} (hp : p ∈ genSupport m k) :
    p.Prime := by
  simp only [genSupport, Finset.mem_image, Finset.mem_range] at hp
  obtain ⟨i, _, rfl⟩ := hp
  exact genSeq_prime hm i

/-- Every prime in genSupport(m, k) divides genProd(m, k). -/
theorem genSupport_dvd_genProd {m : Nat} (_hm : 1 ≤ m) {k : Nat} {p : Nat}
    (hp : p ∈ genSupport m k) : p ∣ genProd m k := by
  simp only [genSupport, Finset.mem_image, Finset.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  -- genSeq m i divides genProd m (i+1) which divides genProd m k
  have h1 : genSeq m i ∣ genProd m (i + 1) := by
    rw [genProd_succ]; exact dvd_mul_left _ _
  have h2 : genProd m (i + 1) ∣ genProd m k := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (by omega : i + 1 ≤ k)
    rw [hd]; exact genProd_dvd_genProd m (i + 1) d
  exact dvd_trans h1 h2

/-- No prime in genSupport(m, k) divides genProd(m, k)+1. -/
theorem genSupport_not_dvd_succ {m : Nat} (hm : 1 ≤ m) {k : Nat} {p : Nat}
    (hp : p ∈ genSupport m k) : ¬(p ∣ genProd m k + 1) := by
  intro hdvd_succ
  have hdvd := genSupport_dvd_genProd hm hp
  have hprime := genSupport_prime hm hp
  -- p divides both genProd m k and genProd m k + 1, so p | 1
  have h1 : p ∣ genProd m k + 1 - genProd m k := Nat.dvd_sub hdvd_succ hdvd
  have h2 : genProd m k + 1 - genProd m k = 1 := by omega
  rw [h2] at h1
  exact absurd (Nat.le_of_dvd Nat.one_pos h1) (by have := hprime.two_le; omega)

/-- genProd(m, k) + 1 mod p = 1 for every prime p in genSupport. -/
theorem genProd_succ_mod_genSupport {m : Nat} (hm : 1 ≤ m) {k : Nat} {p : Nat}
    (hp : p ∈ genSupport m k) (hp' : p.Prime) :
    (genProd m k + 1) % p = 1 := by
  have hdvd := genSupport_dvd_genProd hm hp
  rw [Nat.add_mod, Nat.dvd_iff_mod_eq_zero.mp hdvd, Nat.zero_add,
      Nat.mod_mod, Nat.mod_eq_of_lt hp'.one_lt]

/-- The next generalized prime is NOT in the current support. -/
theorem genSeq_not_mem_genSupport {m : Nat} (hm : Squarefree m) (k : Nat) :
    genSeq m k ∉ genSupport m k := by
  intro h
  simp only [genSupport, Finset.mem_image, Finset.mem_range] at h
  obtain ⟨i, hi, heq⟩ := h
  -- genSeq m i = genSeq m k with i < k, contradicting injectivity
  have := (genSeq_injective hm) heq
  omega

/-- genSupport is strictly monotone when m is squarefree. -/
theorem genSupport_ssubset {m : Nat} (hm : Squarefree m) (k : Nat) :
    genSupport m k ⊂ genSupport m (k + 1) := by
  constructor
  · exact genSupport_mono m (by omega)
  · intro h
    have : genSeq m k ∈ genSupport m (k + 1) := by
      simp only [genSupport, Finset.mem_image, Finset.mem_range]
      exact ⟨k, by omega, rfl⟩
    have := h this
    exact genSeq_not_mem_genSupport hm k this

end GenSupport

/-! ## Phase 4: Specialization to standard EM -/

section Specialization

/-- The image of genSeq 2 over {0,...,k-1} equals the image of seq over {1,...,k}.
    This is because genSeq 2 i = seq(i+1) for all i (genSeq_two_eq_seq_succ). -/
theorem genSupport_two_eq_seq_image (k : Nat) :
    genSupport 2 k = ((Finset.range k).image (fun i => Mullin.seq (i + 1))) := by
  ext p
  simp only [genSupport, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, heq⟩
    -- heq : genSeq 2 i = p, goal: ∃ j < k, seq (j+1) = p
    refine ⟨i, hi, ?_⟩
    rw [← heq, genSeq_two_eq_seq_succ]
  · rintro ⟨i, hi, heq⟩
    -- heq : seq (i+1) = p, goal: ∃ j < k, genSeq 2 j = p
    refine ⟨i, hi, ?_⟩
    rw [genSeq_two_eq_seq_succ, heq]

/-- seq(n+1) belongs to genSupport 2 (n+1). -/
theorem seq_succ_mem_genSupport_two (n : Nat) :
    Mullin.seq (n + 1) ∈ genSupport 2 (n + 1) := by
  simp only [genSupport, Finset.mem_image, Finset.mem_range]
  exact ⟨n, by omega, genSeq_two_eq_seq_succ n⟩

/-- emSupport n contains seq 0 = 2. -/
theorem seq_zero_mem_emSupport (n : Nat) : Mullin.seq 0 ∈ emSupport n := by
  simp only [emSupport, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by omega, rfl⟩

/-- emSupport (n+1) = emSupport n with seq(n+1) added.
    Since seq(n+1) is not in emSupport n (by seq_succ_not_mem_emSupport),
    this is a disjoint insertion. -/
theorem emSupport_succ (n : Nat) :
    emSupport (n + 1) = insert (Mullin.seq (n + 1)) (emSupport n) := by
  ext p
  simp only [emSupport, Finset.mem_image, Finset.mem_range, Finset.mem_insert]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases h : i = n + 1
    · left; exact congrArg _ h
    · right; exact ⟨i, by omega, rfl⟩
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨n + 1, by omega, rfl⟩
    · exact ⟨i, by omega, rfl⟩

/-- emSupport grows by one element at each step. -/
theorem emSupport_card_succ (n : Nat) :
    (emSupport (n + 1)).card = (emSupport n).card + 1 := by
  rw [emSupport_succ, Finset.card_insert_of_notMem (seq_succ_not_mem_emSupport n)]

end Specialization
