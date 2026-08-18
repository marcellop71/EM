import EM.Population.SeedTypes
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Seed capture: the `q`-free greedy dynamics and the coupling/capture lemma

This file supplies **Lemma C** of the seed-average program, in purely finitary
form (no densities, no limits).

Fix a prime `q`.  The *`q`-free greedy dynamics* is the variant of the
generalized Euclid–Mullin recursion in which, at every step, the prime `q` is
surgically removed from the Euclid number before taking its least prime factor:

```
genProdAvoid q m 0       = m
genProdAvoid q m (k + 1) = genProdAvoid q m k * genSeqAvoid q m k
genSeqAvoid  q m k       = minFac (qfreePart q (genProdAvoid q m k + 1))
```

where `qfreePart q N = ordCompl[q] N` is `N` with all its factors of `q`
divided out.  So `genSeqAvoid q m k` is the least prime `≠ q` dividing
`genProdAvoid q m k + 1` (`minFac_qfreePart_least`), and the `q`-free orbit
*never* selects `q` (`genSeqAvoid_ne_avoided`).

The point of this dynamics is that it is a *seed-residue-blind* reference
trajectory: it depends on the seed `m` only through the ordinary CRT data, and
it can be run without knowing anything about `m mod q`.  **Lemma C** says that
a genuine orbit (of a seed `m'` congruent to `m` modulo a suitable modulus `M`)
tracks the `q`-free orbit *exactly*, until the first moment at which `q` is
captured — and that the capture moment is determined by a single algebraic
condition on `m' mod q`:

* `genSeq_prefix_of_no_capture` (**coupling half**): if the seed residue
  `m' mod q` never hits `-c_j⁻¹` at a `q`-exposed step `j < n`, the two orbits
  agree on `[0, n)`.
* `genSeq_capture_at` (**capture half**): at the *first* exposed step `k` where
  `m' · c_k = -1` in `ZMod q`, the genuine orbit agrees below `k` and selects
  exactly `q` at step `k`.
* `captured_iff_mem_visited` (**capture identity**): `q` occurs among the first
  `n` multipliers of the genuine orbit **iff** the seed residue `m' mod q` lies
  in `-(visitedSetAvoid q m n)⁻¹`, the (pointwise inverted, negated) set of
  cofactor residues at the `q`-exposed steps of the `q`-free orbit.

The capture identity is the finitary heart of the seed-average program: it
converts "the orbit of `m'` sees `q`" — a dynamical statement about a single
orbit — into membership of `m' mod q` in an explicitly enumerated set of size
at most `n`, computed from a *single* reference orbit.

The degenerate case is genuine and is handled by hypothesis, never by fiat: if
`genProdAvoid q m k + 1` happens to be a power of `q`, then `qfreePart` is `1`
and `minFac 1 = 1`, so the dynamics stalls.  Every substantive statement below
therefore carries a nondegeneracy hypothesis `2 ≤ genSeqAvoid q m j`.
-/

noncomputable section
open Classical

namespace SeedCapture

open SeedTypes

/-! ## 1. The `q`-free part -/

/-- `qfreePart q N` is `N` with all of its factors of `q` removed. -/
def qfreePart (q N : ℕ) : ℕ := ordCompl[q] N

theorem qfreePart_dvd (q N : ℕ) : qfreePart q N ∣ N := Nat.ordCompl_dvd N q

theorem qfreePart_pos {N : ℕ} (q : ℕ) (hN : N ≠ 0) : 0 < qfreePart q N :=
  Nat.ordCompl_pos q hN

/-- The avoided prime does not divide the `q`-free part. -/
theorem not_dvd_qfreePart {q N : ℕ} (hq : q.Prime) (hN : N ≠ 0) :
    ¬ q ∣ qfreePart q N := Nat.not_dvd_ordCompl hq hN

/-- For a prime `r ≠ q`, dividing the `q`-free part is the same as dividing `N`. -/
theorem prime_dvd_qfreePart_iff {q r N : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hrq : r ≠ q) (_hN : N ≠ 0) : r ∣ qfreePart q N ↔ r ∣ N := by
  refine ⟨fun h => h.trans (qfreePart_dvd q N), fun h => ?_⟩
  have hsplit : q ^ N.factorization q * qfreePart q N = N :=
    Nat.ordProj_mul_ordCompl_eq_self N q
  have h' : r ∣ q ^ N.factorization q * qfreePart q N := by rw [hsplit]; exact h
  have hcop : Nat.Coprime r (q ^ N.factorization q) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hr hq).mpr hrq)
  exact hcop.dvd_of_dvd_mul_left h'

/-- **The `q`-free minimal factor is the least prime `≠ q` dividing `N`.**
Under nondegeneracy `2 ≤ qfreePart q N`, the number
`p := minFac (qfreePart q N)` is prime, divides `N`, differs from `q`, and is
minimal with those properties. -/
theorem minFac_qfreePart_spec {q N : ℕ} (hq : q.Prime) (hN : N ≠ 0)
    (h2 : 2 ≤ qfreePart q N) :
    Nat.Prime (qfreePart q N).minFac ∧ (qfreePart q N).minFac ∣ N ∧
      (qfreePart q N).minFac ≠ q := by
  have hne1 : qfreePart q N ≠ 1 := by omega
  refine ⟨Nat.minFac_prime hne1, (Nat.minFac_dvd _).trans (qfreePart_dvd q N), ?_⟩
  intro hcontra
  have hd : (qfreePart q N).minFac ∣ qfreePart q N := Nat.minFac_dvd _
  rw [hcontra] at hd
  exact not_dvd_qfreePart hq hN hd

/-- Minimality half of `minFac_qfreePart_spec`: any prime `≠ q` dividing `N` is
at least `minFac (qfreePart q N)`. -/
theorem minFac_qfreePart_least {q r N : ℕ} (hq : q.Prime) (hN : N ≠ 0)
    (hr : r.Prime) (hrq : r ≠ q) (hrN : r ∣ N) :
    (qfreePart q N).minFac ≤ r :=
  Nat.minFac_le_of_dvd hr.two_le ((prime_dvd_qfreePart_iff hq hr hrq hN).mpr hrN)

/-! ## 2. The `q`-free greedy dynamics -/

/-- The accumulator of the `q`-free greedy dynamics started at seed `m`. -/
def genProdAvoid (q m : ℕ) : ℕ → ℕ
  | 0 => m
  | k + 1 => genProdAvoid q m k * (qfreePart q (genProdAvoid q m k + 1)).minFac

/-- The multiplier of the `q`-free greedy dynamics: the least prime `≠ q`
dividing the current Euclid number (or `1` in the degenerate case). -/
def genSeqAvoid (q m k : ℕ) : ℕ := (qfreePart q (genProdAvoid q m k + 1)).minFac

@[simp] theorem genProdAvoid_zero (q m : ℕ) : genProdAvoid q m 0 = m := rfl

@[simp] theorem genProdAvoid_succ (q m k : ℕ) :
    genProdAvoid q m (k + 1) = genProdAvoid q m k * genSeqAvoid q m k := rfl

theorem genSeqAvoid_def (q m k : ℕ) :
    genSeqAvoid q m k = (qfreePart q (genProdAvoid q m k + 1)).minFac := rfl

theorem genProdAvoid_pos {m : ℕ} (q : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    1 ≤ genProdAvoid q m k := by
  induction k with
  | zero => exact hm
  | succ k ih =>
    rw [genProdAvoid_succ]
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (Nat.minFac_pos _).ne')

/-- Nondegeneracy of the multiplier transfers to nondegeneracy of the
`q`-free part. -/
theorem two_le_qfreePart_of_two_le {m : ℕ} {q k : ℕ} (hm : 1 ≤ m)
    (h2 : 2 ≤ genSeqAvoid q m k) :
    2 ≤ qfreePart q (genProdAvoid q m k + 1) := by
  have hpos : 0 < qfreePart q (genProdAvoid q m k + 1) :=
    qfreePart_pos q (by have := genProdAvoid_pos q hm k; omega)
  by_contra hcon
  have h1 : qfreePart q (genProdAvoid q m k + 1) = 1 := by omega
  rw [genSeqAvoid_def, h1, Nat.minFac_one] at h2
  omega

/-- **Structure (A).**  A nondegenerate `q`-free multiplier is prime. -/
theorem genSeqAvoid_prime {m : ℕ} {q k : ℕ} (h2 : 2 ≤ genSeqAvoid q m k) :
    Nat.Prime (genSeqAvoid q m k) := by
  rw [genSeqAvoid_def]
  refine Nat.minFac_prime ?_
  intro hcontra
  rw [genSeqAvoid_def, hcontra] at h2
  simp [Nat.minFac_one] at h2

/-- **Structure (A).**  The `q`-free dynamics never selects the avoided prime. -/
theorem genSeqAvoid_ne_avoided {m : ℕ} {q k : ℕ} (hq : q.Prime) (hm : 1 ≤ m)
    (h2 : 2 ≤ genSeqAvoid q m k) : genSeqAvoid q m k ≠ q := by
  have hN : genProdAvoid q m k + 1 ≠ 0 := by
    have := genProdAvoid_pos q hm k; omega
  exact (minFac_qfreePart_spec hq hN (two_le_qfreePart_of_two_le hm h2)).2.2

/-- The `q`-free multiplier divides the current Euclid number. -/
theorem genSeqAvoid_dvd_succ {m : ℕ} {q k : ℕ} (hq : q.Prime) (hm : 1 ≤ m)
    (h2 : 2 ≤ genSeqAvoid q m k) :
    genSeqAvoid q m k ∣ genProdAvoid q m k + 1 := by
  have hN : genProdAvoid q m k + 1 ≠ 0 := by
    have := genProdAvoid_pos q hm k; omega
  exact (minFac_qfreePart_spec hq hN (two_le_qfreePart_of_two_le hm h2)).2.1

/-- **Structure (A).**  The avoided prime never divides the `q`-free
accumulator, provided it does not divide the seed. -/
theorem not_dvd_genProdAvoid {m : ℕ} {q : ℕ} (hq : q.Prime) (hm : 1 ≤ m)
    (hqm : ¬ q ∣ m) (k : ℕ) : ¬ q ∣ genProdAvoid q m k := by
  induction k with
  | zero => exact hqm
  | succ k ih =>
    rw [genProdAvoid_succ]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
    · exact ih h
    · -- `q ∣ genSeqAvoid q m k`, so `genSeqAvoid q m k = q`, contradicting (A).
      by_cases h2 : 2 ≤ genSeqAvoid q m k
      · exact genSeqAvoid_ne_avoided hq hm h2
          ((Nat.prime_dvd_prime_iff_eq hq (genSeqAvoid_prime h2)).mp h).symm
      · have hle : genSeqAvoid q m k ≤ 1 := by omega
        have hqle : q ≤ genSeqAvoid q m k :=
          Nat.le_of_dvd (by rw [genSeqAvoid_def]; exact Nat.minFac_pos _) h
        have := hq.two_le
        omega

/-! ## 3. The `q`-free cofactor and the exposed visited set -/

/-- The cofactor accumulated by the first `k` multipliers of the `q`-free
dynamics. -/
def seedCofactorAvoid (q m k : ℕ) : ℕ := ∏ j ∈ Finset.range k, genSeqAvoid q m j

@[simp] theorem seedCofactorAvoid_zero (q m : ℕ) : seedCofactorAvoid q m 0 = 1 := by
  simp [seedCofactorAvoid]

theorem seedCofactorAvoid_succ (q m k : ℕ) :
    seedCofactorAvoid q m (k + 1) = seedCofactorAvoid q m k * genSeqAvoid q m k := by
  simp [seedCofactorAvoid, Finset.prod_range_succ]

/-- **Seed/cofactor factorization** for the `q`-free dynamics. -/
theorem genProdAvoid_eq_seed_mul_cofactor (q m k : ℕ) :
    genProdAvoid q m k = m * seedCofactorAvoid q m k := by
  induction k with
  | zero => simp
  | succ k ih => rw [genProdAvoid_succ, ih, seedCofactorAvoid_succ, mul_assoc]

theorem seedCofactorAvoid_pos (q m k : ℕ) : 1 ≤ seedCofactorAvoid q m k :=
  Nat.one_le_iff_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr fun _ _ => (Nat.minFac_pos _).ne')

/-- The avoided prime does not divide a nondegenerate `q`-free cofactor. -/
theorem not_dvd_seedCofactorAvoid {m : ℕ} {q k : ℕ} (hq : q.Prime) (hm : 1 ≤ m)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) : ¬ q ∣ seedCofactorAvoid q m k := by
  induction k with
  | zero =>
    simp only [seedCofactorAvoid_zero]
    exact fun h => hq.one_lt.ne' (Nat.dvd_one.mp h)
  | succ k ih =>
    rw [seedCofactorAvoid_succ]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
    · exact ih (fun j hj => hnd j (Nat.lt_succ_of_lt hj)) h
    · have h2 := hnd k (Nat.lt_succ_self k)
      exact genSeqAvoid_ne_avoided hq hm h2
        ((Nat.prime_dvd_prime_iff_eq hq (genSeqAvoid_prime h2)).mp h).symm

/-- **Structure (A), corollary.**  A nondegenerate `q`-free cofactor reduces to
a unit modulo `q`. -/
theorem seedCofactorAvoid_isUnit {m : ℕ} {q k : ℕ} (hq : q.Prime) (hm : 1 ≤ m)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) :
    IsUnit ((seedCofactorAvoid q m k : ℕ) : ZMod q) := by
  have : Fact q.Prime := ⟨hq⟩
  refine IsUnit.mk0 _ ?_
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact not_dvd_seedCofactorAvoid hq hm hnd

theorem seedCofactorAvoid_ne_zero_zmod {m : ℕ} {q k : ℕ} (hq : q.Prime)
    (hm : 1 ≤ m) (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) :
    ((seedCofactorAvoid q m k : ℕ) : ZMod q) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact not_dvd_seedCofactorAvoid hq hm hnd

/-- The residues mod `q` of the `q`-free cofactors at the `q`-exposed steps
`j < k` (steps at which the `q`-free multiplier exceeded `q`, i.e. at which `q`
was "available and declined" in the `q`-free run). -/
def visitedSetAvoid (q m k : ℕ) : Finset (ZMod q) :=
  ((Finset.range k).filter (fun j => q < genSeqAvoid q m j)).image
    (fun j => ((seedCofactorAvoid q m j : ℕ) : ZMod q))

/-- Membership unfolding for `visitedSetAvoid`. -/
theorem mem_visitedSetAvoid {q m k : ℕ} {v : ZMod q}
    (hv : v ∈ visitedSetAvoid q m k) :
    ∃ j, j < k ∧ q < genSeqAvoid q m j ∧
      ((seedCofactorAvoid q m j : ℕ) : ZMod q) = v := by
  rw [visitedSetAvoid, Finset.mem_image] at hv
  obtain ⟨j, hj, hveq⟩ := hv
  rw [Finset.mem_filter, Finset.mem_range] at hj
  exact ⟨j, hj.1, hj.2, hveq⟩

theorem mem_visitedSetAvoid_of {q m k j : ℕ} (hj : j < k)
    (hexp : q < genSeqAvoid q m j) :
    ((seedCofactorAvoid q m j : ℕ) : ZMod q) ∈ visitedSetAvoid q m k := by
  rw [visitedSetAvoid, Finset.mem_image]
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hexp⟩, rfl⟩

/-- The exposed visited set has at most one element per step. -/
theorem visitedSetAvoid_card_le (q m k : ℕ) : (visitedSetAvoid q m k).card ≤ k := by
  refine le_trans Finset.card_image_le ?_
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp

/-! ## 4. The one-step coupling engine -/

/-- Translation of the capture condition: `m' · c = -1` in `ZMod q` is exactly
divisibility of the Euclid number `m' * c + 1` by `q`. -/
theorem hit_iff_dvd {q m' c : ℕ} :
    ((m' : ZMod q) * (c : ZMod q) = -1) ↔ q ∣ m' * c + 1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  exact ⟨fun h => by rw [h]; ring, fun h => eq_neg_of_add_eq_zero_left h⟩

/-- **Lemma C, one-step engine.**  Let `A = m * c + 1` and `B = m' * c + 1` with
`m ≡ m' [MOD M]`, where `M` is divisible by every prime `≤ y` other than `q`.
If the least prime `≠ q` dividing `A` is nondegenerate and `≤ y`, and — in the
`q`-exposed case — `q` does not divide `B`, then the *genuine* least prime
factor of `B` equals the `q`-free least prime factor of `A`. -/
theorem minFac_eq_qfree_minFac {q m m' M y c : ℕ} (hq : q.Prime) (hm : 1 ≤ m)
    (hm' : 1 ≤ m') (hc : 1 ≤ c)
    (hM : ∀ r : ℕ, r.Prime → r ≤ y → r ≠ q → r ∣ M)
    (hmod : m ≡ m' [MOD M])
    (h2 : 2 ≤ qfreePart q (m * c + 1))
    (hle : (qfreePart q (m * c + 1)).minFac ≤ y)
    (hnc : q < (qfreePart q (m * c + 1)).minFac → ¬ q ∣ m' * c + 1) :
    Nat.minFac (m' * c + 1) = (qfreePart q (m * c + 1)).minFac := by
  set A := m * c + 1 with hA_def
  set B := m' * c + 1 with hB_def
  set p := (qfreePart q A).minFac with hp_def
  have hA2 : 2 ≤ A := by
    have : 1 ≤ m * c := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega
  have hB2 : 2 ≤ B := by
    have : 1 ≤ m' * c := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega
  have hAne : A ≠ 0 := by omega
  obtain ⟨hp_prime, hpA, hpq⟩ := minFac_qfreePart_spec hq hAne h2
  -- Congruence of the shifted products.
  have hmodc : m * c ≡ m' * c [MOD M] := Nat.ModEq.mul_right c hmod
  -- `p` divides `M`, hence `p ∣ B`.
  have hpM : p ∣ M := hM p hp_prime hle hpq
  have hmodp : m * c % p = m' * c % p := Nat.ModEq.of_dvd hpM hmodc
  have hpB : p ∣ B := (MullinCRT.dvd_succ_iff_of_mod_eq hmodp).mp hpA
  -- The genuine minimal factor `s` of `B`.
  set s := Nat.minFac B with hs_def
  have hs_prime : Nat.Prime s := Nat.minFac_prime (by omega)
  have hsp : s ≤ p := Nat.minFac_le_of_dvd hp_prime.two_le hpB
  have hsB : s ∣ B := Nat.minFac_dvd B
  by_cases hsq : s = q
  · -- `q ∣ B`; but then `q = s ≤ p` and `p ≠ q`, so the step is `q`-exposed.
    exfalso
    exact hnc (by omega) (hsq ▸ hsB)
  · -- `s ≠ q`: symmetric minimality forces `p ≤ s`.
    have hsy : s ≤ y := le_trans hsp hle
    have hsM : s ∣ M := hM s hs_prime hsy hsq
    have hmods : m * c % s = m' * c % s := Nat.ModEq.of_dvd hsM hmodc
    have hsA : s ∣ A := (MullinCRT.dvd_succ_iff_of_mod_eq hmods).mpr hsB
    have := minFac_qfreePart_least hq hAne hs_prime hsq hsA
    omega

/-! ## 5. Lemma C, coupling half -/

/-- **Lemma C (coupling half).**  Suppose `M` is divisible by every prime `≤ y`
other than `q`, that `m ≡ m' [MOD M]`, that the first `n` multipliers of the
`q`-free orbit of `m` are nondegenerate and `≤ y`, and that the seed residue
`m' mod q` performs **no capture**: at every `q`-exposed step `j < n` one has
`m' · c_j ≠ -1` in `ZMod q`.  Then the genuine orbit of `m'` coincides with the
`q`-free orbit of `m` throughout `[0, n)`. -/
theorem genSeq_prefix_of_no_capture {q m m' M y n : ℕ} (hq : q.Prime)
    (hm : 1 ≤ m) (hm' : 1 ≤ m') (_hqm' : ¬ q ∣ m')
    (hM : ∀ r : ℕ, r.Prime → r ≤ y → r ≠ q → r ∣ M)
    (hmod : m ≡ m' [MOD M])
    (hy : ∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ y)
    (hnc : ∀ j < n, q < genSeqAvoid q m j →
      ¬ ((m' : ZMod q) * ((seedCofactorAvoid q m j : ℕ) : ZMod q) = -1)) :
    ∀ j < n, genSeq m' j = genSeqAvoid q m j := by
  induction n with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
    have ihpref : ∀ j < n, genSeq m' j = genSeqAvoid q m j :=
      ih (fun j hj => hy j (Nat.lt_succ_of_lt hj))
        (fun j hj => hnc j (Nat.lt_succ_of_lt hj))
    -- The cofactors agree below `n`, hence so do the accumulators.
    have hcof : seedCofactor m' n = seedCofactorAvoid q m n := by
      unfold seedCofactor seedCofactorAvoid
      exact Finset.prod_congr rfl fun j hj => ihpref j (Finset.mem_range.mp hj)
    have hstep : genSeq m' n = genSeqAvoid q m n := by
      obtain ⟨h2, hle⟩ := hy n (Nat.lt_succ_self n)
      have hqf2 : 2 ≤ qfreePart q (m * seedCofactorAvoid q m n + 1) := by
        rw [← genProdAvoid_eq_seed_mul_cofactor]
        exact two_le_qfreePart_of_two_le hm h2
      have hgen : genSeq m' n = Nat.minFac (m' * seedCofactorAvoid q m n + 1) := by
        rw [genSeq_def, genProd_eq_seed_mul_cofactor, hcof]
      rw [hgen]
      have hgoal : genSeqAvoid q m n
          = (qfreePart q (m * seedCofactorAvoid q m n + 1)).minFac := by
        rw [genSeqAvoid_def, genProdAvoid_eq_seed_mul_cofactor]
      rw [hgoal]
      refine minFac_eq_qfree_minFac hq hm hm' (seedCofactorAvoid_pos q m n) hM hmod
        hqf2 ?_ ?_
      · rw [← hgoal]; exact hle
      · intro hexp hdvd
        refine hnc n (Nat.lt_succ_self n) (by rw [hgoal]; exact hexp) ?_
        exact hit_iff_dvd.mpr hdvd
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · exact ihpref j h
    · subst h; exact hstep

/-- The accumulator form of the coupling half. -/
theorem genProd_eq_of_no_capture {q m m' M y n : ℕ} (hq : q.Prime)
    (hm : 1 ≤ m) (hm' : 1 ≤ m') (hqm' : ¬ q ∣ m')
    (hM : ∀ r : ℕ, r.Prime → r ≤ y → r ≠ q → r ∣ M)
    (hmod : m ≡ m' [MOD M])
    (hy : ∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ y)
    (hnc : ∀ j < n, q < genSeqAvoid q m j →
      ¬ ((m' : ZMod q) * ((seedCofactorAvoid q m j : ℕ) : ZMod q) = -1)) :
    ∀ j ≤ n, genProd m' j = m' * seedCofactorAvoid q m j := by
  have hpref := genSeq_prefix_of_no_capture hq hm hm' hqm' hM hmod hy hnc
  intro j hj
  rw [genProd_eq_seed_mul_cofactor]
  congr 1
  unfold seedCofactor seedCofactorAvoid
  exact Finset.prod_congr rfl fun i hi =>
    hpref i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj)

/-! ## 6. Lemma C, capture half -/

/-- **Lemma C (capture half).**  At the *first* `q`-exposed step `k < n` at
which the seed residue satisfies `m' · c_k = -1` in `ZMod q`, the genuine orbit
of `m'` agrees with the `q`-free orbit of `m` below `k`, and selects exactly the
avoided prime `q` at step `k`. -/
theorem genSeq_capture_at {q m m' M y n k : ℕ} (hq : q.Prime)
    (hm : 1 ≤ m) (hm' : 1 ≤ m') (hqm' : ¬ q ∣ m')
    (hM : ∀ r : ℕ, r.Prime → r ≤ y → r ≠ q → r ∣ M)
    (hmod : m ≡ m' [MOD M])
    (hy : ∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ y)
    (hkn : k < n) (hk : q < genSeqAvoid q m k)
    (hhit : (m' : ZMod q) * ((seedCofactorAvoid q m k : ℕ) : ZMod q) = -1)
    (hmin : ∀ j < k, q < genSeqAvoid q m j →
      ¬ ((m' : ZMod q) * ((seedCofactorAvoid q m j : ℕ) : ZMod q) = -1)) :
    (∀ j < k, genSeq m' j = genSeqAvoid q m j) ∧ genSeq m' k = q := by
  have hykk : ∀ j < k, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ y :=
    fun j hj => hy j (lt_trans hj hkn)
  have hpref := genSeq_prefix_of_no_capture hq hm hm' hqm' hM hmod hykk hmin
  refine ⟨hpref, ?_⟩
  -- The accumulators agree at step `k`.
  set c := seedCofactorAvoid q m k with hc_def
  have hcof : seedCofactor m' k = c := by
    unfold seedCofactor
    rw [hc_def]
    unfold seedCofactorAvoid
    exact Finset.prod_congr rfl fun j hj => hpref j (Finset.mem_range.mp hj)
  have hc1 : 1 ≤ c := seedCofactorAvoid_pos q m k
  have hgen : genSeq m' k = Nat.minFac (m' * c + 1) := by
    rw [genSeq_def, genProd_eq_seed_mul_cofactor, hcof]
  have hB2 : 2 ≤ m' * c + 1 := by
    have : 1 ≤ m' * c := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega
  have hqB : q ∣ m' * c + 1 := hit_iff_dvd.mp hhit
  rw [hgen]
  -- `minFac (m' c + 1) ≤ q`, and any strictly smaller prime divisor is excluded.
  set s := Nat.minFac (m' * c + 1) with hs_def
  have hs_prime : Nat.Prime s := Nat.minFac_prime (by omega)
  have hsq : s ≤ q := Nat.minFac_le_of_dvd hq.two_le hqB
  by_contra hne
  have hslt : s < q := by omega
  -- Then `s` is a small prime `≠ q` dividing `m' c + 1`, hence divides `m c + 1`.
  obtain ⟨h2k, hlek⟩ := hy k hkn
  have hsy : s ≤ y := by omega
  have hsne : s ≠ q := by omega
  have hsM : s ∣ M := hM s hs_prime hsy hsne
  have hmodc : m * c ≡ m' * c [MOD M] := Nat.ModEq.mul_right c hmod
  have hmods : m * c % s = m' * c % s := Nat.ModEq.of_dvd hsM hmodc
  have hsA : s ∣ m * c + 1 :=
    (MullinCRT.dvd_succ_iff_of_mod_eq hmods).mpr (Nat.minFac_dvd _)
  have hAne : m * c + 1 ≠ 0 := by omega
  have hle := minFac_qfreePart_least hq hAne hs_prime hsne hsA
  have hgoal : genSeqAvoid q m k = (qfreePart q (m * c + 1)).minFac := by
    rw [genSeqAvoid_def, genProdAvoid_eq_seed_mul_cofactor]
  omega

/-! ## 7. The capture identity -/

/-- Inversion glue: for a unit `c` in `ZMod q`, `m' · c = -1` is equivalent to
`m' = -c⁻¹`. -/
theorem hit_iff_eq_neg_inv {q : ℕ} (hq : q.Prime) {x c : ZMod q} (hc : c ≠ 0) :
    x * c = -1 ↔ x = -c⁻¹ := by
  have : Fact q.Prime := ⟨hq⟩
  constructor
  · intro h
    have := congrArg (· * c⁻¹) h
    simpa [mul_assoc, mul_inv_cancel₀ hc] using this
  · intro h
    rw [h, neg_mul, inv_mul_cancel₀ hc]

/-- **Capture identity, forward direction.**  If the genuine orbit of `m'`
selects the avoided prime `q` somewhere in `[0, n)`, then the seed residue
`m' mod q` is the negated inverse of a `q`-free cofactor residue recorded at a
`q`-exposed step. -/
theorem mem_visited_of_captured {q m m' M y n : ℕ} (hq : q.Prime)
    (hm : 1 ≤ m) (hm' : 1 ≤ m') (hqm' : ¬ q ∣ m')
    (hM : ∀ r : ℕ, r.Prime → r ≤ y → r ≠ q → r ∣ M)
    (hmod : m ≡ m' [MOD M])
    (hy : ∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ y)
    (hcap : ∃ j < n, genSeq m' j = q) :
    ∃ v ∈ visitedSetAvoid q m n, (m' : ZMod q) = -v⁻¹ := by
  by_contra hcon
  -- No capture: turn the failure of membership into the hypothesis of Lemma C.
  have hnc : ∀ j < n, q < genSeqAvoid q m j →
      ¬ ((m' : ZMod q) * ((seedCofactorAvoid q m j : ℕ) : ZMod q) = -1) := by
    intro j hj hexp hhit
    refine hcon ⟨((seedCofactorAvoid q m j : ℕ) : ZMod q),
      mem_visitedSetAvoid_of hj hexp, ?_⟩
    have hcne : ((seedCofactorAvoid q m j : ℕ) : ZMod q) ≠ 0 :=
      seedCofactorAvoid_ne_zero_zmod hq hm
        (fun i hi => (hy i (lt_trans hi hj)).1)
    exact (hit_iff_eq_neg_inv hq hcne).mp hhit
  -- Then the orbits couple, and the `q`-free orbit never selects `q`.
  have hpref := genSeq_prefix_of_no_capture hq hm hm' hqm' hM hmod hy hnc
  obtain ⟨j, hj, hjq⟩ := hcap
  exact genSeqAvoid_ne_avoided hq hm (hy j hj).1 ((hpref j hj) ▸ hjq)

/-- **Capture identity, backward direction.**  If the seed residue `m' mod q`
is the negated inverse of some recorded `q`-free cofactor residue, then the
genuine orbit of `m'` selects `q` at some step `< n`. -/
theorem captured_of_mem_visited {q m m' M y n : ℕ} (hq : q.Prime)
    (hm : 1 ≤ m) (hm' : 1 ≤ m') (hqm' : ¬ q ∣ m')
    (hM : ∀ r : ℕ, r.Prime → r ≤ y → r ≠ q → r ∣ M)
    (hmod : m ≡ m' [MOD M])
    (hy : ∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ y)
    (hmem : ∃ v ∈ visitedSetAvoid q m n, (m' : ZMod q) = -v⁻¹) :
    ∃ j < n, genSeq m' j = q := by
  -- The set of exposed hitting steps is nonempty; take its least element.
  have hnonempty : ∃ j, j < n ∧ q < genSeqAvoid q m j ∧
      (m' : ZMod q) * ((seedCofactorAvoid q m j : ℕ) : ZMod q) = -1 := by
    obtain ⟨v, hv, hmv⟩ := hmem
    obtain ⟨j, hj, hexp, hveq⟩ := mem_visitedSetAvoid hv
    have hcne : ((seedCofactorAvoid q m j : ℕ) : ZMod q) ≠ 0 :=
      seedCofactorAvoid_ne_zero_zmod hq hm (fun i hi => (hy i (lt_trans hi hj)).1)
    exact ⟨j, hj, hexp, (hit_iff_eq_neg_inv hq hcne).mpr (hveq ▸ hmv)⟩
  classical
  set P : ℕ → Prop := fun j => j < n ∧ q < genSeqAvoid q m j ∧
      (m' : ZMod q) * ((seedCofactorAvoid q m j : ℕ) : ZMod q) = -1 with hP_def
  have hex : ∃ j, P j := hnonempty
  set k := Nat.find hex with hk_def
  obtain ⟨hkn, hkexp, hkhit⟩ : P k := Nat.find_spec hex
  have hmin : ∀ j < k, q < genSeqAvoid q m j →
      ¬ ((m' : ZMod q) * ((seedCofactorAvoid q m j : ℕ) : ZMod q) = -1) := by
    intro j hj hexp hhit
    exact Nat.find_min hex hj ⟨lt_trans hj hkn, hexp, hhit⟩
  exact ⟨k, hkn, (genSeq_capture_at hq hm hm' hqm' hM hmod hy hkn hkexp hkhit hmin).2⟩

/-! ## 6. The coupling lemma for orbits that miss `q`

The coupling half of Lemma C (`genSeq_prefix_of_no_capture`) is conditioned on
the *seed residue* `m' mod q` avoiding the death classes `-c_j⁻¹` at the
`q`-exposed steps of the reference orbit; that is what makes it usable for a
population argument, where the reference orbit is run once and the seeds vary.

The lemma below is the complementary, purely orbit-local statement: it is
conditioned directly on the genuine orbit of `m` *never selecting* `q` before
depth `n`, and concludes that the `q`-free reference dynamics started at the
same seed reproduces that orbit exactly.  No CRT data, no auxiliary seed, and
no exposure hypothesis are involved.

This is hygiene for anyone reasoning about `genSeqAvoid`: it says that the
`q`-free dynamics is a genuine *reference* trajectory, agreeing with the truth
for as long as `q` is not the greedy choice.  It is **not** a step towards
Mullin's conjecture — nothing here constrains the missed set of an orbit — and
must not be advertised as one.  It was identified as missing in
`docs/analysis/sure_layer_missed_primes.md` §1 (Session 313). -/

/-- If `q` is prime and the least prime factor of `N ≥ 2` is not `q`, then
deleting the `q`-part of `N` does not change its least prime factor.

This is the one-step engine of the coupling lemma: the two inequalities are
`minFac_qfreePart_least` (applied to the prime `N.minFac`) and minimality of
`N.minFac` against the prime `(qfreePart q N).minFac`, which divides `N`. -/
theorem minFac_qfreePart_eq_minFac {q N : ℕ} (hq : q.Prime) (hN : 2 ≤ N)
    (hne : N.minFac ≠ q) : (qfreePart q N).minFac = N.minFac := by
  have hN0 : N ≠ 0 := by omega
  have hN1 : N ≠ 1 := by omega
  have hprime : Nat.Prime N.minFac := Nat.minFac_prime hN1
  -- `N.minFac` is a prime `≠ q` dividing `N`, hence divides the `q`-free part.
  have hdvd : N.minFac ∣ qfreePart q N :=
    (prime_dvd_qfreePart_iff hq hprime hne hN0).mpr (Nat.minFac_dvd N)
  -- In particular the `q`-free part is nondegenerate.
  have h2 : 2 ≤ qfreePart q N :=
    le_trans hprime.two_le (Nat.le_of_dvd (qfreePart_pos q hN0) hdvd)
  refine Nat.le_antisymm (minFac_qfreePart_least hq hN0 hprime hne (Nat.minFac_dvd N)) ?_
  obtain ⟨hp', hd', -⟩ := minFac_qfreePart_spec hq hN0 h2
  exact Nat.minFac_le_of_dvd hp'.two_le hd'

/-- **Coupling lemma (accumulators).**  If the genuine orbit of the seed `m`
never selects the prime `q` at a step `< n`, then the `q`-free reference
accumulator agrees with the genuine accumulator throughout `[0, n]`. -/
theorem genProdAvoid_eq_genProd_of_missed {q m n : ℕ} (hq : q.Prime) (hm : 1 ≤ m)
    (hmiss : ∀ j < n, genSeq m j ≠ q) :
    ∀ j ≤ n, genProdAvoid q m j = genProd m j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hkn : k < n := by omega
    have hprev : genProdAvoid q m k = genProd m k := ih (by omega)
    have hstep : (qfreePart q (genProd m k + 1)).minFac = genSeq m k := by
      rw [genSeq_def]
      exact minFac_qfreePart_eq_minFac hq
        (by have := genProd_pos hm k; omega) (genSeq_def m k ▸ hmiss k hkn)
    rw [genProdAvoid_succ, genProd_succ, genSeqAvoid_def, hprev, hstep]

/-- **Coupling lemma (multipliers).**  If the genuine orbit of the seed `m`
never selects the prime `q` at a step `< n`, then the `q`-free reference
multipliers agree with the genuine multipliers throughout `[0, n)`. -/
theorem genSeqAvoid_eq_genSeq_of_missed {q m n : ℕ} (hq : q.Prime) (hm : 1 ≤ m)
    (hmiss : ∀ j < n, genSeq m j ≠ q) :
    ∀ j < n, genSeqAvoid q m j = genSeq m j := by
  intro j hj
  rw [genSeqAvoid_def,
    genProdAvoid_eq_genProd_of_missed hq hm hmiss j (le_of_lt hj), genSeq_def]
  exact minFac_qfreePart_eq_minFac hq (by have := genProd_pos hm j; omega)
    (genSeq_def m j ▸ hmiss j hj)

/-- If the genuine orbit of `m` never selects `q` at all, then the `q`-free
reference dynamics *is* the genuine dynamics, at every depth. -/
theorem genSeqAvoid_eq_genSeq_of_never {q m : ℕ} (hq : q.Prime) (hm : 1 ≤ m)
    (hmiss : ∀ j, genSeq m j ≠ q) (k : ℕ) :
    genProdAvoid q m k = genProd m k ∧ genSeqAvoid q m k = genSeq m k :=
  ⟨genProdAvoid_eq_genProd_of_missed hq hm (fun j _ => hmiss j) k (Nat.le_succ k),
   genSeqAvoid_eq_genSeq_of_missed hq hm (n := k + 1) (fun j _ => hmiss j) k
     (Nat.lt_succ_self k)⟩

/-- **Lemma C (capture identity).**  Under the CRT hypotheses of Lemma C, the
genuine orbit of the seed `m'` captures the prime `q` within its first `n` steps
**iff** the seed residue `m' mod q` lies in the negated inverse of the
`q`-exposed visited set of the (seed-residue-blind) `q`-free reference orbit.

This is the finitary heart of the seed-average program: dynamical capture is
converted into membership of a single residue in an explicitly enumerated set
of size at most `n` (`visitedSetAvoid_card_le`). -/
theorem captured_iff_mem_visited {q m m' M y n : ℕ} (hq : q.Prime)
    (hm : 1 ≤ m) (hm' : 1 ≤ m') (hqm' : ¬ q ∣ m')
    (hM : ∀ r : ℕ, r.Prime → r ≤ y → r ≠ q → r ∣ M)
    (hmod : m ≡ m' [MOD M])
    (hy : ∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ y) :
    (∃ j < n, genSeq m' j = q) ↔
      ∃ v ∈ visitedSetAvoid q m n, (m' : ZMod q) = -v⁻¹ :=
  ⟨mem_visited_of_captured hq hm hm' hqm' hM hmod hy,
   captured_of_mem_visited hq hm hm' hqm' hM hmod hy⟩

end SeedCapture

end
