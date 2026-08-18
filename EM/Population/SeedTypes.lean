import EM.Ensemble.GenEM
import EM.Group.CRT

/-!
# Seed Types: the deterministic core of the seed-average program

This file isolates the two purely deterministic ingredients of the
seed-average program for the generalized Euclid-Mullin recursion
`P(0) = m`, `P(k+1) = P(k) * minFac(P(k)+1)` (see `EM/Ensemble/GenEM.lean`).

Throughout, the orbit factors as `genProd m k = m * seedCofactor m k`, where
`seedCofactor m k = ∏_{j < k} genSeq m j` is the *cofactor* accumulated by the
first `k` multipliers.  The cofactor does not depend on the residue of the seed
modulo anything: it is a function of the seed only through the multipliers it
produced.

## Lemma A (revisit-freeness)

`not_dvd_succ_of_revisit`.  Fix a prime `r`.  Call step `j` *`r`-exposed* if
`r < genSeq m j`, i.e. the multiplier chosen at step `j` was larger than `r`;
at an exposed step `r` was available and declined, so `r ∤ P(j) + 1`
(`not_dvd_succ_of_exposed`).  The **visited set** `visitedSet r m k` collects
the residues `seedCofactor m j mod r` over the exposed steps `j < k`.  If the
current cofactor residue `seedCofactor m k mod r` has already been visited,
then `r ∤ P(k) + 1`.  This holds with **no hypotheses whatsoever on the seed**:
it is a purely algebraic consequence of `P = m * c` — the seed factor `m`
multiplies both residues equally, so a revisit of the cofactor residue is a
revisit of the full orbit residue, and the earlier visit was exposed.

Consequently the exposed cofactor residues of a genuine capture-free run are
pairwise distinct, and moreover avoid both `0` and `-(m mod r)⁻¹`, giving the
uncaptured bound `card_visitedSet_le_sub_two`: at most `r - 2` exposed steps
before `r` is forced.

## Lemma B (finite orbits are CRT functions of the seed)

`genSeq_prefix_of_modEq`.  If `M` is divisible by every prime `p ≤ y`, and two
seeds `m ≡ m' [MOD M]` both produce first `n` multipliers that stay `≤ y`, then
the two orbits agree: `genSeq m' j = genSeq m j` for all `j < n`, and the
accumulators stay congruent mod `M`.  The one-step engine is
`minFac_eq_of_modEq_of_le`, a *one-sided* symmetric-minimality argument: it
assumes only that the multiplier of the *first* orbit is `≤ y`, and derives the
bound for the second.  (This is deliberately not
`MullinCRT.crt_multiplier_invariance_finset`, whose polarity — a hypothesis on
both sides — is wrong for the seed-average use, where only one side is known.)
-/

noncomputable section
open Classical

namespace SeedTypes

/-! ## 1. The seed / cofactor factorization -/

/-- The cofactor accumulated by the first `k` multipliers of the orbit of `m`. -/
def seedCofactor (m k : ℕ) : ℕ := ∏ j ∈ Finset.range k, genSeq m j

@[simp] theorem seedCofactor_zero (m : ℕ) : seedCofactor m 0 = 1 := by
  simp [seedCofactor]

theorem seedCofactor_succ (m k : ℕ) :
    seedCofactor m (k + 1) = seedCofactor m k * genSeq m k := by
  simp [seedCofactor, Finset.prod_range_succ]

/-- **Seed/cofactor factorization:** `genProd m k = m * seedCofactor m k`. -/
theorem genProd_eq_seed_mul_cofactor (m k : ℕ) :
    genProd m k = m * seedCofactor m k := by
  induction k with
  | zero => simp [genProd]
  | succ k ih =>
    rw [genProd_succ, ih, seedCofactor_succ, mul_assoc]

/-- Cofactors are monotone under divisibility. -/
theorem seedCofactor_dvd_of_le {m j k : ℕ} (hjk : j ≤ k) :
    seedCofactor m j ∣ seedCofactor m k :=
  Finset.prod_dvd_prod_of_subset _ _ _
    (fun _x hx => Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hx) hjk))

/-- The cofactor divides the accumulator. -/
theorem seedCofactor_dvd_genProd (m k : ℕ) : seedCofactor m k ∣ genProd m k :=
  ⟨m, by rw [genProd_eq_seed_mul_cofactor]; ring⟩

/-- The seed divides the accumulator. -/
theorem seed_dvd_genProd (m k : ℕ) : m ∣ genProd m k :=
  ⟨seedCofactor m k, genProd_eq_seed_mul_cofactor m k⟩

/-! ## 2. Exposedness -/

/-- **Exposedness.**  If the multiplier chosen at step `k` exceeds the prime
`r`, then `r` was available and was not chosen, so `r ∤ P(k) + 1`. -/
theorem not_dvd_succ_of_exposed {r m k : ℕ} (hr : Nat.Prime r)
    (hexp : r < genSeq m k) : ¬ r ∣ genProd m k + 1 := by
  intro hdvd
  have : genSeq m k ≤ r := Nat.minFac_le_of_dvd hr.two_le hdvd
  omega

/-! ## 3. The visited set -/

/-- The residues mod `r` of the cofactors at the `r`-exposed steps `j < k`. -/
def visitedSet (r m k : ℕ) : Finset (ZMod r) :=
  ((Finset.range k).filter (fun j => r < genSeq m j)).image
    (fun j => ((seedCofactor m j : ℕ) : ZMod r))

theorem card_visitedSet_le (r m k : ℕ) : (visitedSet r m k).card ≤ k := by
  refine le_trans (Finset.card_image_le) ?_
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp

/-- Membership unfolding for `visitedSet`. -/
theorem mem_visitedSet {r m k : ℕ} {v : ZMod r} (hv : v ∈ visitedSet r m k) :
    ∃ j, j < k ∧ r < genSeq m j ∧ ((seedCofactor m j : ℕ) : ZMod r) = v := by
  rw [visitedSet, Finset.mem_image] at hv
  obtain ⟨j, hj, hveq⟩ := hv
  rw [Finset.mem_filter, Finset.mem_range] at hj
  exact ⟨j, hj.1, hj.2, hveq⟩

/-! ## 4. Lemma A: revisit-freeness -/

/-- **Lemma A (revisit-freeness).**  If the current cofactor residue mod `r`
has already occurred at an `r`-exposed earlier step, then `r ∤ P(k) + 1`.

No hypothesis on the seed beyond positivity is needed: the seed factor `m`
multiplies both cofactor residues equally, so the full orbit residues agree,
and the earlier step was exposed. -/
theorem not_dvd_succ_of_revisit {r m k : ℕ} (_hm : 1 ≤ m) (hr : Nat.Prime r)
    (hmem : ((seedCofactor m k : ℕ) : ZMod r) ∈ visitedSet r m k) :
    ¬ r ∣ genProd m k + 1 := by
  obtain ⟨j, _hj, hexp, hcj⟩ := mem_visitedSet hmem
  intro hdvd
  -- The orbit residues at steps `j` and `k` coincide.
  have hcast : ((genProd m j + 1 : ℕ) : ZMod r) = ((genProd m k + 1 : ℕ) : ZMod r) := by
    rw [genProd_eq_seed_mul_cofactor, genProd_eq_seed_mul_cofactor]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, hcj]
  have hk0 : ((genProd m k + 1 : ℕ) : ZMod r) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  have hj0 : r ∣ genProd m j + 1 :=
    (ZMod.natCast_eq_zero_iff _ _).mp (hcast.trans hk0)
  exact not_dvd_succ_of_exposed hr hexp hj0

/-! ## 5. The uncaptured bound -/

/-- **Uncaptured bound.**  As long as `r` does not divide the accumulator, the
visited cofactor residues avoid both `0` and `-(m)⁻¹`, hence there are at most
`r - 2` of them. -/
theorem card_visitedSet_le_sub_two {r m k : ℕ} (_hm : 1 ≤ m) (hr : Nat.Prime r)
    (hndvd : ¬ r ∣ genProd m k) : (visitedSet r m k).card ≤ r - 2 := by
  have : Fact (Nat.Prime r) := ⟨hr⟩
  have : NeZero r := ⟨hr.ne_zero⟩
  have hm0 : (m : ZMod r) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hndvd (h.trans (seed_dvd_genProd m k))
  set t : ZMod r := -(m : ZMod r)⁻¹ with ht
  have ht0 : t ≠ 0 := by
    rw [ht, neg_ne_zero, Ne, inv_eq_zero]
    exact hm0
  have hsub : visitedSet r m k ⊆ (Finset.univ.erase (0 : ZMod r)).erase t := by
    intro v hv
    obtain ⟨j, hj, hexp, hveq⟩ := mem_visitedSet hv
    -- The visited residue is nonzero.
    have hcj_dvd : seedCofactor m j ∣ genProd m k :=
      (seedCofactor_dvd_of_le (Nat.le_of_lt hj)).trans (seedCofactor_dvd_genProd m k)
    have hv0 : v ≠ 0 := by
      rw [← hveq, Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => hndvd (h.trans hcj_dvd)
    -- The visited residue is not `-(m)⁻¹`, since step `j` was exposed.
    have hjne : ((genProd m j + 1 : ℕ) : ZMod r) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact not_dvd_succ_of_exposed hr hexp
    have hjval : ((genProd m j + 1 : ℕ) : ZMod r) = (m : ZMod r) * v + 1 := by
      rw [genProd_eq_seed_mul_cofactor, ← hveq]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    have hvt : v ≠ t := by
      intro hcontra
      apply hjne
      rw [hjval, hcontra, ht, mul_neg, mul_inv_cancel₀ hm0, neg_add_cancel]
    exact Finset.mem_erase.mpr ⟨hvt, Finset.mem_erase.mpr ⟨hv0, Finset.mem_univ v⟩⟩
  have htmem : t ∈ Finset.univ.erase (0 : ZMod r) :=
    Finset.mem_erase.mpr ⟨ht0, Finset.mem_univ t⟩
  have hcard : ((Finset.univ.erase (0 : ZMod r)).erase t).card = r - 2 := by
    rw [Finset.card_erase_of_mem htmem,
        Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod r)),
        Finset.card_univ, ZMod.card]
    omega
  calc (visitedSet r m k).card
      ≤ ((Finset.univ.erase (0 : ZMod r)).erase t).card := Finset.card_le_card hsub
    _ = r - 2 := hcard

/-! ## 6. Lemma B, one step: CRT invariance of a small multiplier -/

/-- **One-step CRT prefix invariance.**  Suppose `M` is divisible by every
prime `p ≤ y`, that `P ≡ P' [MOD M]`, and that the multiplier of `P` is `≤ y`.
Then the two multipliers agree.

The hypothesis is one-sided: nothing is assumed about `minFac (P' + 1)`; its
smallness is *derived*.  (`MullinCRT.crt_multiplier_invariance_finset` assumes
a condition on both sides, which is the wrong polarity here.) -/
theorem minFac_eq_of_modEq_of_le {P P' M y : ℕ} (hP : 1 ≤ P) (hP' : 1 ≤ P')
    (hMy : ∀ p, Nat.Prime p → p ≤ y → p ∣ M) (hmod : P ≡ P' [MOD M])
    (hle : Nat.minFac (P + 1) ≤ y) :
    Nat.minFac (P + 1) = Nat.minFac (P' + 1) := by
  have hp : Nat.Prime (Nat.minFac (P + 1)) := Nat.minFac_prime (by omega)
  have hpM : Nat.minFac (P + 1) ∣ M := hMy _ hp hle
  have hmodp : P % Nat.minFac (P + 1) = P' % Nat.minFac (P + 1) :=
    Nat.ModEq.of_dvd hpM hmod
  have h1 : Nat.minFac (P + 1) ∣ P' + 1 :=
    (MullinCRT.dvd_succ_iff_of_mod_eq hmodp).mp (Nat.minFac_dvd _)
  have hle1 : Nat.minFac (P' + 1) ≤ Nat.minFac (P + 1) :=
    Nat.minFac_le_of_dvd hp.two_le h1
  have hp' : Nat.Prime (Nat.minFac (P' + 1)) := Nat.minFac_prime (by omega)
  have hp'M : Nat.minFac (P' + 1) ∣ M := hMy _ hp' (le_trans hle1 hle)
  have hmodp' : P % Nat.minFac (P' + 1) = P' % Nat.minFac (P' + 1) :=
    Nat.ModEq.of_dvd hp'M hmod
  have h2 : Nat.minFac (P' + 1) ∣ P + 1 :=
    (MullinCRT.dvd_succ_iff_of_mod_eq hmodp').mpr (Nat.minFac_dvd _)
  have hle2 : Nat.minFac (P + 1) ≤ Nat.minFac (P' + 1) :=
    Nat.minFac_le_of_dvd hp'.two_le h2
  omega

/-! ## 7. Lemma B: a finite orbit is a CRT function of the seed -/

/-- **Lemma B.**  If `M` is divisible by every prime `≤ y` and the first `n`
multipliers of the orbit of `m` all stay `≤ y`, then any seed `m' ≡ m [MOD M]`
produces exactly the same first `n` multipliers, and the accumulators remain
congruent mod `M`. -/
theorem genSeq_prefix_of_modEq {m m' M y n : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (hMy : ∀ p, Nat.Prime p → p ≤ y → p ∣ M) (hmod : m ≡ m' [MOD M])
    (hsmall : ∀ j < n, genSeq m j ≤ y) :
    (∀ j < n, genSeq m' j = genSeq m j) ∧ genProd m n ≡ genProd m' n [MOD M] := by
  revert hsmall
  induction n with
  | zero =>
    intro _
    exact ⟨fun j hj => absurd hj (Nat.not_lt_zero j), hmod⟩
  | succ n ih =>
    intro hsmall
    obtain ⟨ihpref, ihmod⟩ := ih (fun j hj => hsmall j (Nat.lt_succ_of_lt hj))
    have hstep : genSeq m n = genSeq m' n :=
      minFac_eq_of_modEq_of_le (genProd_pos hm n) (genProd_pos hm' n) hMy ihmod
        (hsmall n (Nat.lt_succ_self n))
    refine ⟨?_, ?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact ihpref j h
      · subst h; exact hstep.symm
    · simp only [genProd_succ]
      rw [hstep]
      exact Nat.ModEq.mul ihmod (Nat.ModEq.refl _)

/-- The multiplier-prefix half of Lemma B. -/
theorem genSeq_prefix_eq_of_modEq {m m' M y n : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (hMy : ∀ p, Nat.Prime p → p ≤ y → p ∣ M) (hmod : m ≡ m' [MOD M])
    (hsmall : ∀ j < n, genSeq m j ≤ y) :
    ∀ j < n, genSeq m' j = genSeq m j :=
  (genSeq_prefix_of_modEq hm hm' hMy hmod hsmall).1

end SeedTypes

end
