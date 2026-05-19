import EM.Obstruction.Fragment
import EM.Reciprocity.SymbolAlgebra

/-!
# No Reciprocity Invariant Blocks a Prime

`EM/Obstruction/Fragment.lean` kills congruence-invariant induction proofs at a *fixed*
modulus, and widens the fragment along stage-dependence, size and `ω`.  Its remaining
disclaimer is the Booker genre: proofs that track **reciprocity data between sequence
elements** — Jacobi symbols `J(pᵢ | ·)` whose denominator is the *new* multiplier, so that
the modulus grows with the orbit.

This file removes that disclaimer.  The route is the one identified in
`docs/analysis/reciprocity_invariants.md` §2 and already formalized as (R1):
`symbolModulus_spec` says that two odd candidates agreeing modulo
`Πₙ = 8·m·Pₙ` carry *identical* level-`n` reciprocity data — every symbol `J(pᵢ | ·)` for
`i ≤ n`, the class mod `8`, and the class mod `m`.  So a reciprocity invariant is not a
new kind of object: it is a congruence invariant whose modulus is allowed to grow along
the orbit, with old coordinates never rewritten.

`ReciprocityInductionProof` is that object, stated without dependent types: the invariant
at stage `n` is a predicate on accumulators that is closed under congruence mod `Πₙ`.

## Why the three moves survive, concretely

* **Eviction is automatic.**  `Πₙ` contains `Pₙ` as a factor, and `Pₙ + 1` is coprime
  to `Pₙ`; it contains `8`, and `Pₙ + 1` is odd.  So the Euclid unit law
  (`N ≡ 1 mod pᵢ`) and the mod-`4` law (`N ≡ 3 mod 4`) are *consequences* of taking the
  candidate in the class `Pₙ + 1` mod `Πₙ`, not extra hypotheses.  The orbit primes evict
  themselves.
* **Fullness is `free_transition_large` at the modulus `Πₙ`.**  `free_transition` was
  proved for an *arbitrary* modulus, so no new analytic input is needed: Dirichlet at
  `Πₙ` supplies the new multiplier in any prescribed class, and the cofactor realizes the
  candidate's class.
* **Reach is unchanged.**  Forcing is a condition modulo `m` alone, and `m ∣ Πₙ`, so the
  forcing states of the fixed-modulus theory are still forcing at every stage.

## Main results

* `ReciprocityInductionProof` — the fragment: stage-indexed, congruence-closed mod `Πₙ`.
* `ReciprocityInductionProof.eventually_avoids` — soundness.
* `no_reciprocity_induction_proof` — **the fragment is empty for every missing prime**.
* `reciprocity_provability_iff` — provability of avoidance still decides appearance.

The `EXTENDS` verdict of `docs/analysis/reciprocity_invariants.md` is thereby a theorem
rather than an assessment, and Dead End~#144 acquires its witness.
-/

open Mullin Euclid MullinGroup CvdP Obstruction

namespace Reciprocity

/-! ## Part 1: Elementary facts about the symbol modulus -/

theorem symbolModulus_ne_zero {m : ℕ} (hm : m ≠ 0) (n : ℕ) : symbolModulus m n ≠ 0 := by
  have := prod_ge_two n
  simp only [symbolModulus]
  positivity

theorem dvd_symbolModulus {m : ℕ} (n : ℕ) : m ∣ symbolModulus m n :=
  ⟨8 * prod n, by simp only [symbolModulus]; ring⟩

theorem two_dvd_symbolModulus {m : ℕ} (n : ℕ) : 2 ∣ symbolModulus m n :=
  ⟨4 * m * prod n, by simp only [symbolModulus]; ring⟩

theorem symbolModulus_dvd_succ {m : ℕ} (n : ℕ) :
    symbolModulus m n ∣ symbolModulus m (n + 1) := by
  simp only [symbolModulus, prod_succ]
  exact mul_dvd_mul_left _ (Dvd.intro _ rfl)

/-- Arbitrarily large representatives of a residue class. -/
theorem exists_large_in_class {M : ℕ} (hM : M ≠ 0) (c B : ℕ) :
    ∃ N : ℕ, B < N ∧ N ≡ c [MOD M] := by
  refine ⟨c + (B + 1) * M, ?_, ?_⟩
  · have : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM
    nlinarith
  · simp [Nat.ModEq]

/-- In a class modulo an even modulus, parity is constant. -/
theorem odd_of_class_odd {M c N : ℕ} (hM : 2 ∣ M) (hc : Odd c) (h : N ≡ c [MOD M]) :
    Odd N := by
  have h2 : N ≡ c [MOD 2] := h.of_dvd hM
  rw [Nat.odd_iff] at hc ⊢
  simpa [Nat.ModEq, hc] using h2

/-! ## Part 2: The fragment -/

/-- A **reciprocity-invariant induction proof** that `q` is eventually never captured.

The invariant at stage `n` is a predicate on accumulators closed under congruence modulo
the symbol modulus `Πₙ = 8·m·Pₙ`.  By `symbolModulus_spec` this is exactly the closure
property a set of level-`n` reciprocity states pulls back to, so the fragment covers the
Booker genre: symbols against moduli that grow with the orbit, with the level-`n`
coordinates immutable.

As in `Obstruction.CongruenceInductionProof`, the step and conclusion clauses must hold
for *every* admissible candidate in the class: the proof's knowledge of the orbit is
exactly its reciprocity data, so it cannot separate candidates that data identifies. -/
structure ReciprocityInductionProof (q m : ℕ) where
  /-- The stage-indexed invariant, as a predicate on accumulators. -/
  inv : ℕ → ℕ → Prop
  /-- It is a reciprocity condition: closed under congruence mod `Πₙ`. -/
  respects : ∀ n a b : ℕ, a ≡ b [MOD symbolModulus m n] → inv n a → inv n b
  /-- The stage from which the invariant is maintained. -/
  N₀ : ℕ
  /-- The invariant holds on the actual orbit at stage `N₀`. -/
  base : inv N₀ (prod N₀)
  /-- The induction step, uniform over admissible candidates in the class. -/
  step : ∀ n a : ℕ, inv n a → ∀ N : ℕ, Odd N → 3 ≤ N →
    N ≡ a + 1 [MOD symbolModulus m n] → inv (n + 1) (a * Nat.minFac N)
  /-- The conclusion: at an invariant state no admissible candidate is captured by `q`. -/
  avoid : ∀ n a : ℕ, inv n a → ∀ N : ℕ, Odd N → 3 ≤ N →
    N ≡ a + 1 [MOD symbolModulus m n] → Nat.minFac N ≠ q

namespace ReciprocityInductionProof

variable {q m : ℕ}

/-- The invariant follows the actual orbit.  The Euclid unit law and the mod-`4` law are
not needed as hypotheses here: the orbit's own candidate is `Pₙ + 1`, which lies in its
own class trivially. -/
theorem orbit_mem (π : ReciprocityInductionProof q m) :
    ∀ n ≥ π.N₀, π.inv n (prod n) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact π.base
  | succ n hn ih =>
    have hge : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
    have hodd : Odd (prod n + 1) := by
      have h2 : (2 : ℕ) ∣ prod n := by
        have := seq_dvd_prod 0 n (Nat.zero_le n)
        rwa [seq_zero] at this
      obtain ⟨k, hk⟩ := h2
      exact Nat.odd_iff.mpr (by omega)
    have h3 : 3 ≤ prod n + 1 := by have := prod_ge_two n; omega
    have hmem := π.step n _ ih (prod n + 1) hodd h3 (Nat.ModEq.refl _)
    have hstep : prod (n + 1) = prod n * Nat.minFac (prod n + 1) := by
      rw [prod_succ, seq_succ, euclid_minFac_eq_nat_minFac _ hge]
    rwa [← hstep] at hmem

/-- **Soundness**: an inhabitant genuinely proves that `q` is eventually never captured. -/
theorem eventually_avoids (π : ReciprocityInductionProof q m) :
    ∀ n ≥ π.N₀, seq (n + 1) ≠ q := by
  intro n hn
  have hge : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
  have hodd : Odd (prod n + 1) := by
    have h2 : (2 : ℕ) ∣ prod n := by
      have := seq_dvd_prod 0 n (Nat.zero_le n)
      rwa [seq_zero] at this
    obtain ⟨k, hk⟩ := h2
    exact Nat.odd_iff.mpr (by omega)
  have h3 : 3 ≤ prod n + 1 := by have := prod_ge_two n; omega
  have hav := π.avoid n _ (π.orbit_mem n hn) (prod n + 1) hodd h3 (Nat.ModEq.refl _)
  rw [seq_succ, euclid_minFac_eq_nat_minFac _ hge]
  exact hav

/-- Proofs lift along modulus divisibility.  The lift is the *identity* family: enlarging
`m` only enlarges `Πₙ`, so the congruence-closure and the clauses are inherited. -/
def lift {m' : ℕ} (h : m ∣ m') (π : ReciprocityInductionProof q m) :
    ReciprocityInductionProof q m' where
  inv := π.inv
  respects := fun n a b hab => π.respects n a b
    (hab.of_dvd (mul_dvd_mul_right (mul_dvd_mul_left 8 h) (prod n)))
  N₀ := π.N₀
  base := π.base
  step := fun n a ha N hodd h3 hc => π.step n a ha N hodd h3
    (hc.of_dvd (mul_dvd_mul_right (mul_dvd_mul_left 8 h) (prod n)))
  avoid := fun n a ha N hodd h3 hc => π.avoid n a ha N hodd h3
    (hc.of_dvd (mul_dvd_mul_right (mul_dvd_mul_left 8 h) (prod n)))

end ReciprocityInductionProof

/-! ## Part 3: The fragment is empty

The argument of `Obstruction.no_graded_induction_proof`, run at the *growing* modulus.
Two points make it go through unchanged.

First, `free_transition` was proved for an arbitrary modulus, so applying it at `Πₙ`
needs no new analytic input — Dirichlet at `Πₙ` is the same theorem.  Second, the unit
class supplied by `congruence_reaches_forcing` lives mod `m'`, and lifts to a unit mod
`Πₙ` because `ZMod.unitsMap` is surjective along divisibility. -/

open Obstruction in
/-- **No reciprocity invariant blocks a prime.**  For a missing prime `q` and any nonzero
modulus `m`, the reciprocity-induction fragment is empty: no propagating invariant closed
under congruence modulo the growing symbol modulus `Πₙ = 8·m·Pₙ`, containing the orbit
tail, can exclude capture of `q`.

This is the `EXTENDS` verdict of `docs/analysis/reciprocity_invariants.md`, as a theorem. -/
theorem no_reciprocity_induction_proof {q m : ℕ} (hq : q ∈ MissingPrimes) (hm : m ≠ 0) :
    IsEmpty (ReciprocityInductionProof q m) := by
  constructor
  intro π₀
  -- lift to a rich modulus
  set m' : ℕ := m * forcingModulus q with hm'def
  have hFne : forcingModulus q ≠ 0 := by
    simp only [forcingModulus]
    refine Nat.mul_ne_zero hq.1.pos.ne' ?_
    exact Finset.prod_ne_zero_iff.mpr fun p hp => (Finset.mem_filter.mp hp).2.1.pos.ne'
  have hm'ne : m' ≠ 0 := by simp only [hm'def]; exact Nat.mul_ne_zero hm hFne
  have hrich : RichEnough q m' := richEnough_of_forcingModulus_dvd (dvd_mul_left _ m)
  have π := π₀.lift (dvd_mul_right m (forcingModulus q))
  have : NeZero m' := ⟨hm'ne⟩
  -- a late orbit stage that is free at `m'`
  obtain ⟨N₁, hforce⟩ := congruence_reaches_forcing hq hm'ne hrich
  obtain ⟨N₂, hcop⟩ := exists_tail_coprime m' hm'ne
  set n := max π.N₀ (max N₁ N₂) with hndef
  have hn0 : π.N₀ ≤ n := le_max_left _ _
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) (le_max_right _ _)
  have hn2 : N₂ ≤ n := le_trans (le_max_right _ _) (le_max_right _ _)
  have hmem : π.inv n (prod n) := π.orbit_mem n hn0
  obtain ⟨_, u, hu⟩ := hforce n hn1
  -- the candidate is coprime to the whole symbol modulus
  have hprodeven : (2 : ℕ) ∣ prod n := by
    have := seq_dvd_prod 0 n (Nat.zero_le n); rwa [seq_zero] at this
  have hoddcand : Odd (prod n + 1) := by
    obtain ⟨k, hk⟩ := hprodeven; exact Nat.odd_iff.mpr (by omega)
  have hcop8 : Nat.Coprime (prod n + 1) 8 := by
    have h2 : Nat.Coprime (prod n + 1) 2 := by
      rw [Nat.coprime_two_right]; exact hoddcand
    simpa using h2.pow_right 3
  have hcopP : Nat.Coprime (prod n + 1) (prod n) := by
    simp [Nat.coprime_comm]
  have hcopPi : Nat.Coprime (prod n + 1) (symbolModulus m' n) := by
    simp only [symbolModulus]
    exact (hcop8.mul_right (hcop n hn2)).mul_right hcopP
  have hPine : symbolModulus m' n ≠ 0 := symbolModulus_ne_zero hm'ne n
  have : NeZero (symbolModulus m' n) := ⟨hPine⟩
  have hunit : IsUnit (((prod n : ℕ) : ZMod (symbolModulus m' n)) + 1) := by
    have hc : ((prod n + 1 : ℕ) : ZMod (symbolModulus m' n))
        = ((prod n : ℕ) : ZMod (symbolModulus m' n)) + 1 := by push_cast; ring
    rw [← hc]
    exact (ZMod.isUnit_iff_coprime _ _).mpr hcopPi
  -- lift the CRT unit from `m'` to the symbol modulus
  obtain ⟨s, hs⟩ := ZMod.unitsMap_surjective (m := symbolModulus m' n) (n := m')
    (dvd_symbolModulus n) u
  -- Fullness at the symbol modulus
  obtain ⟨N, hNgt, hNodd, hN3, hNcast, hNmf⟩ :=
    free_transition_large hPine ((prod n : ℕ) : ZMod (symbolModulus m' n)) hunit s 2
  have hNmod : N ≡ prod n + 1 [MOD symbolModulus m' n] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    exact hNcast
  have hstep := π.step n _ hmem N hNodd hN3 hNmod
  -- the reached accumulator is forcing mod `m'`
  have hcastmf : ((Nat.minFac N : ℕ) : ZMod m') = (u : ZMod m') := by
    have := congrArg (ZMod.castHom (dvd_symbolModulus (m := m') n) (ZMod m')) hNmf
    rwa [map_natCast, ZMod.castHom_apply, ← ZMod.unitsMap_val (dvd_symbolModulus n) s,
      hs] at this
  set a' : ℕ := prod n * Nat.minFac N with ha'def
  have ha'cast : ((a' : ℕ) : ZMod m')
      = ((prod n : ℕ) : ZMod m') * (u : ZMod m') := by
    simp only [ha'def, Nat.cast_mul, hcastmf]
  -- a large candidate in the forcing class at the next stage
  have hPine' : symbolModulus m' (n + 1) ≠ 0 := symbolModulus_ne_zero hm'ne (n + 1)
  obtain ⟨N', hN'gt, hN'mod⟩ := exists_large_in_class hPine' (a' + 1) 3
  have ha'even : (2 : ℕ) ∣ a' := Dvd.dvd.mul_right hprodeven _
  have hN'odd : Odd N' :=
    odd_of_class_odd (two_dvd_symbolModulus (n + 1))
      (by obtain ⟨k, hk⟩ := ha'even; exact Nat.odd_iff.mpr (by omega)) hN'mod
  have hN'cast : ((N' : ℕ) : ZMod m') = ((prod n : ℕ) : ZMod m') * (u : ZMod m') + 1 := by
    have h1 : N' ≡ a' + 1 [MOD m'] :=
      hN'mod.of_dvd (dvd_trans (dvd_symbolModulus (n + 1)) dvd_rfl)
    rw [← ZMod.natCast_eq_natCast_iff] at h1
    rw [h1]
    push_cast [ha'cast]
    ring
  obtain ⟨hqN, hsmall⟩ := hu N' hN'cast
  -- its least factor is exactly `q`, contradicting `avoid`
  have hne1 : N' ≠ 1 := by omega
  have hpr : (Nat.minFac N').Prime := Nat.minFac_prime hne1
  have hdvd : Nat.minFac N' ∣ N' := Nat.minFac_dvd N'
  have hne2 : Nat.minFac N' ≠ 2 := by
    intro h2
    rw [h2] at hdvd
    have := Nat.odd_iff.mp hN'odd
    omega
  have hle : Nat.minFac N' ≤ q := Nat.minFac_le_of_dvd hq.1.two_le hqN
  have hgeq : q ≤ Nat.minFac N' := by
    by_contra hcon
    exact hsmall _ hpr (hpr.odd_of_ne_two hne2) (by omega) hdvd
  exact π.avoid (n + 1) a' hstep N' hN'odd (by omega) hN'mod (by omega)

/-! ## Part 4: Completeness on appeared primes, and the equivalence -/

/-- For a prime that HAS appeared, the reciprocity fragment is inhabited, by Euclid's own
argument: once `q ∣ Pₙ` it divides every later accumulator, so it can never divide a
candidate.  The invariant `q ∣ a` is in particular a congruence condition mod `Πₙ`, since
`q ∣ m ∣ Πₙ`. -/
def appearedReciprocityProof {q m k : ℕ} (hqp : Nat.Prime q) (hk : seq k = q)
    (hqm : q ∣ m) : ReciprocityInductionProof q m where
  inv := fun _ a => q ∣ a
  respects := fun n a b hab ha => by
    have hd : q ∣ symbolModulus m n := dvd_trans hqm (dvd_symbolModulus n)
    have hab' : a ≡ b [MOD q] := hab.of_dvd hd
    exact Nat.modEq_zero_iff_dvd.mp (hab'.symm.trans (Nat.modEq_zero_iff_dvd.mpr ha))
  N₀ := k
  base := hk ▸ seq_dvd_prod k k le_rfl
  step := fun _ a ha N _ _ _ => Dvd.dvd.mul_right ha _
  avoid := fun n a ha N _ _ hc hmf => by
    -- `q ∣ a` and `N ≡ a + 1 (mod q)` give `q ∣ 1`
    have hd : q ∣ symbolModulus m n := dvd_trans hqm (dvd_symbolModulus n)
    have hNq : N ≡ a + 1 [MOD q] := hc.of_dvd hd
    have hqN : q ∣ N := by rw [← hmf]; exact Nat.minFac_dvd N
    have hN0 : N ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr hqN
    have ha0 : a ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr ha
    have h1 : (0 : ℕ) ≡ 1 [MOD q] := by
      calc (0 : ℕ) ≡ N [MOD q] := hN0.symm
        _ ≡ a + 1 [MOD q] := hNq
        _ ≡ 0 + 1 [MOD q] := Nat.ModEq.add_right 1 ha0
      
    have hd1 : q ∣ 1 := (Nat.modEq_iff_dvd' (by omega)).mp h1
    have := Nat.le_of_dvd one_pos hd1
    have := hqp.two_le
    omega

/-- **Provability decides appearance, in the reciprocity fragment too.**  Widening the
proof system from fixed-modulus congruences to symbols against the growing modulus `Πₙ`
changes nothing: it can certify an avoidance only for the trivial reason. -/
theorem reciprocity_provability_iff {q m : ℕ} (hqp : Nat.Prime q) (hm : m ≠ 0)
    (hqm : q ∣ m) :
    Nonempty (ReciprocityInductionProof q m) ↔ ∃ k, seq k = q := by
  constructor
  · intro hπ
    by_contra hcon
    have hmiss : q ∈ MissingPrimes := ⟨hqp, fun k hk => hcon ⟨k, hk⟩⟩
    exact (no_reciprocity_induction_proof hmiss hm).false hπ.some
  · rintro ⟨k, hk⟩
    exact ⟨appearedReciprocityProof hqp hk hqm⟩

/-- **The reciprocity frontier, as one statement.**  The `EXTENDS` verdict of
`docs/analysis/reciprocity_invariants.md`, proved. -/
theorem reciprocity_no_invariant_landscape :
    -- soundness: an inhabitant really proves the omission
    (∀ (q m : ℕ) (π : ReciprocityInductionProof q m), ∀ n ≥ π.N₀, seq (n + 1) ≠ q) ∧
    -- emptiness for every missing prime, at every nonzero modulus
    (∀ q m : ℕ, q ∈ MissingPrimes → m ≠ 0 →
      IsEmpty (ReciprocityInductionProof q m)) ∧
    -- provability decides appearance
    (∀ q m : ℕ, Nat.Prime q → m ≠ 0 → q ∣ m →
      (Nonempty (ReciprocityInductionProof q m) ↔ ∃ k, seq k = q)) :=
  ⟨fun _ _ π => π.eventually_avoids,
    fun _ _ hq hm => no_reciprocity_induction_proof hq hm,
    fun _ _ hqp hm hqm => reciprocity_provability_iff hqp hm hqm⟩

end Reciprocity
