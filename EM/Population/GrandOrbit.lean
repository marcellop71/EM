import EM.Population.ProfiniteAttractor

/-!
# Grand orbits of the greedy map and the transfer principle

Session 318 (2026-08-20).  Theory only: definitions, theorems and the argument that
connects them.  No numerical verification of any particular seed is performed here.

## The relation

`T m = m · minFac (m+1) = genProd m 1` generates the **grand-orbit** relation

  `m ≈ m'  ⟺  ∃ a b, genProd m a = genProd m' b`,

"the forward orbits of `m` and `m'` eventually coincide".  It is an equivalence relation
(`GrandOrbit.equivalence`), the forward orbit of every seed lies in its class
(`genProd_grandOrbit`), and the per-prime failure predicate `Misses q` and hence
`GenMullinConjecture` are **class invariants** (`misses_congr`, `genMC_congr`).  The orbit of
a seed in the class of `2` is, from some point on, the classical Euclid–Mullin sequence.

## The transfer principle

The seed-average law says that for each prime `q` the seeds missing `q` have upper natural
density `0` (`AlmostAllDensity.never_captures_limsup_eq_zero`).  A class invariant turns
this population statement into an orbit statement **exactly when the class is fat**:

* `transfer_principle` — for *any* relation `R` under which `Misses q` is invariant, if the
  `R`-class of `2` has positive upper density then Mullin's conjecture holds.
* `grandOrbit_transfer` — the instance `R = (≈)`: if the ancestors of the Euclid–Mullin
  orbit (the seeds whose orbit merges with it) have positive upper density, MC holds.

This is the precise form of the "cross-seed coupling" demanded by the Heath-Brown analogy
(`docs/analysis/analogy_map_2026-08-20.md`): a GenMC-preserving equivalence relation with a
positive-density class of `2` *is* a proof of MC.  The question "descent relation beyond
`T`" becomes "find such a relation", and the grand orbit is the canonical candidate.

## Why the grand orbit is (presumably) thin — the structure of preimages

The backward structure of `T` is explicit:

* `preimage_iff` — `m'` is a `T`-preimage of `N` (with `m' ≥ 1`) iff `m' = N / p` for a
  prime `p ∣ N` with `minFac (N/p + 1) = p`; so the preimages of `N` inject into the prime
  divisors of `N` (`preimage_multiplier_injective`), and `N` has at most `ω(N)` of them;
* `preimage_cond_iff_sq` — the condition `p ∣ N/p + 1` is the **square condition**
  `p² ∣ N + p`: a `T`-preimage of the accumulator `P_b` other than `P_{b−1}` exists only
  when the orbit mod `p²` sits at `−p` for some orbit prime `p`.

So every ancestor of `P_b` divides `P_b` (`grandOrbit_two_dvd_prod`), and an extra branch at
`P_b` is a mod-`p²` coincidence of heuristic probability `1/p` for each of the `b+1` orbit
primes.  The backward tree of the Euclid–Mullin orbit is therefore expected to be
`O(Σ 1/p_j)`-branching and the class of `2` of polylogarithmic size — density `0`, which
would make `grandOrbit_transfer` vacuous.  None of that is proved, and proving the class
thin would require knowledge of the orbit mod `p²` (a CME-type statement one level up).
The transfer principle itself is unconditional; the open question it isolates is whether
*any* GenMC-preserving relation has a fat class of `2`.

## Scope

Population ⇒ orbit transfer is *conditional* on a density hypothesis about a class of
seeds; nothing here constrains the orbit of `2` unconditionally.  #90/#117 untouched.
-/

noncomputable section
open Classical Filter

namespace GrandOrbit

open GrowingRange (Misses)

/-! ## 1. The relation -/

/-- Two seeds are grand-orbit equivalent when their forward orbits eventually coincide. -/
def Rel (m m' : ℕ) : Prop := ∃ a b : ℕ, genProd m a = genProd m' b

theorem rel_refl (m : ℕ) : Rel m m := ⟨0, 0, rfl⟩

theorem rel_symm {m m' : ℕ} (h : Rel m m') : Rel m' m := by
  obtain ⟨a, b, h⟩ := h
  exact ⟨b, a, h.symm⟩

theorem rel_trans {m m' m'' : ℕ} (h₁ : Rel m m') (h₂ : Rel m' m'') : Rel m m'' := by
  obtain ⟨a, b, h₁⟩ := h₁
  obtain ⟨c, d, h₂⟩ := h₂
  refine ⟨a + c, d + b, ?_⟩
  rw [← genProd_restart, h₁, genProd_restart, ← genProd_restart m'' d b, h₂.symm,
    genProd_restart, Nat.add_comm]

theorem equivalence : Equivalence Rel :=
  ⟨rel_refl, rel_symm, rel_trans⟩

/-- The forward orbit of a seed lies in its class. -/
theorem genProd_grandOrbit (m a : ℕ) : Rel (genProd m a) m := ⟨0, a, rfl⟩

/-- Seeds with the same `T`-image are equivalent. -/
theorem rel_of_image_eq {m m' : ℕ} (h : genProd m 1 = genProd m' 1) : Rel m m' := ⟨1, 1, h⟩

/-! ## 2. Class invariants -/

/-- `Misses q` is a grand-orbit invariant. -/
theorem misses_congr {q : ℕ} (hq : q.Prime) {m m' : ℕ} (h : Rel m m') :
    Misses q m ↔ Misses q m' := by
  obtain ⟨a, b, h⟩ := h
  rw [← GrowingRange.misses_genProd_iff hq a, h, GrowingRange.misses_genProd_iff hq b]

/-- `GenMullinConjecture` is a grand-orbit invariant. -/
theorem genMC_congr {m m' : ℕ} (h : Rel m m') :
    GenMullinConjecture m ↔ GenMullinConjecture m' := by
  obtain ⟨a, b, h⟩ := h
  rw [← GrowingRange.genMC_genProd_iff m a, h, GrowingRange.genMC_genProd_iff m' b]

/-- Every seed in the class of `2` satisfies `GenMC` iff MC holds. -/
theorem genMC_of_rel_two {m : ℕ} (h : Rel m 2) :
    GenMullinConjecture m ↔ Mullin.MullinConjecture := by
  rw [genMC_congr h, gen_mc_two_iff_mc]

/-! ## 3. The transfer principle -/

/-- The failure of MC at `q` is the statement `Misses q 2`. -/
theorem misses_two_iff {q : ℕ} (hq : q.Prime) :
    Misses q 2 ↔ ∀ k, Mullin.seq k ≠ q := by
  constructor
  · rintro ⟨hndvd, hnever⟩ k hk
    cases k with
    | zero =>
      exact hndvd (by rw [← hk, Mullin.seq_zero])
    | succ k =>
      exact hnever k (by rw [genSeq_two_eq_seq_succ, hk])
  · intro h
    refine ⟨fun hdvd => ?_, fun k hk => h (k + 1) (by rw [← genSeq_two_eq_seq_succ, hk])⟩
    have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdvd
    exact h 0 (by rw [Mullin.seq_zero, this])

/-- Counting function of a set of seeds on `[1, X]`, normalised by `X`. -/
def densityRatio (C : Set ℕ) (X : ℕ) : ℝ :=
  (((Finset.Icc 1 X).filter (fun m => m ∈ C)).card : ℝ) / (X : ℝ)

theorem densityRatio_nonneg (C : Set ℕ) (X : ℕ) : 0 ≤ densityRatio C X := by
  unfold densityRatio; positivity

theorem densityRatio_le_one (C : Set ℕ) (X : ℕ) : densityRatio C X ≤ 1 := by
  unfold densityRatio
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simp
  · rw [div_le_one (by exact_mod_cast hX)]
    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)

theorem densityRatio_mono {C D : Set ℕ} (h : C ⊆ D) (X : ℕ) :
    densityRatio C X ≤ densityRatio D X := by
  unfold densityRatio
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg X)
  exact_mod_cast Finset.card_le_card (fun m hm => by
    simp only [Finset.mem_filter] at hm ⊢
    exact ⟨hm.1, h hm.2⟩)

/-- A set of seeds has **positive upper density** if some `δ > 0` is attained by its
counting ratio at arbitrarily large scales. -/
def PositiveUpperDensity (C : Set ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ X in atTop, δ ≤ densityRatio C X

/-- The seeds missing `q` do not have positive upper density
(restatement of `AlmostAllDensity.never_captures_limsup_eq_zero`). -/
theorem not_positiveUpperDensity_misses {q : ℕ} (hq : q.Prime) :
    ¬ PositiveUpperDensity {m | Misses q m} := by
  rintro ⟨δ, hδ, hfreq⟩
  have hlim := AlmostAllDensity.never_captures_limsup_eq_zero q hq
  have heq : (fun X : ℕ => (((Finset.Icc 1 X).filter
      (fun m => ¬ q ∣ m ∧ ∀ j, genSeq m j ≠ q)).card : ℝ) / (X : ℝ))
      = densityRatio {m | Misses q m} := by
    funext X
    unfold densityRatio
    have hfil : (Finset.Icc 1 X).filter (fun m => ¬ q ∣ m ∧ ∀ j, genSeq m j ≠ q)
        = (Finset.Icc 1 X).filter (fun m => m ∈ {m | Misses q m}) :=
      Finset.filter_congr (fun m _ => Iff.rfl)
    rw [hfil]
  rw [heq] at hlim
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (densityRatio {m | Misses q m}) :=
    isBoundedUnder_of ⟨1, fun X => densityRatio_le_one {m | Misses q m} X⟩
  have hle := le_limsup_of_frequently_le hfreq hbdd
  rw [hlim] at hle
  exact absurd hle (not_le.mpr hδ)

/-- **The transfer principle.**  Let `R` be any relation on seeds under which `Misses q` is
invariant for every prime `q`.  If the `R`-class of `2` has positive upper natural density,
then Mullin's conjecture holds.

*Argument.*  If MC failed at `q`, then `2` misses `q` (`misses_two_iff`), hence by
invariance every seed in the class of `2` misses `q`, so the class sits inside the
density-zero set of the seed-average law.  Population ⇒ orbit, along the relation. -/
theorem transfer_principle (R : ℕ → ℕ → Prop)
    (hinv : ∀ q, q.Prime → ∀ m m', R m m' → (Misses q m ↔ Misses q m'))
    (hfat : PositiveUpperDensity {m | R m 2}) :
    Mullin.MullinConjecture := by
  by_contra hmc
  obtain ⟨q, hq, hnever⟩ : ∃ q, Euclid.IsPrime q ∧ ∀ k, Mullin.seq k ≠ q := by
    by_contra hno
    exact hmc fun q hq => by
      by_contra hk
      exact hno ⟨q, hq, fun k hk' => hk ⟨k, hk'⟩⟩
  have hq' : q.Prime := MullinGroup.IsPrime.toNatPrime hq
  have h2 : Misses q 2 := (misses_two_iff hq').mpr hnever
  have hsub : {m | R m 2} ⊆ {m | Misses q m} := fun m hm =>
    (hinv q hq' m 2 hm).mpr h2
  obtain ⟨δ, hδ, hfreq⟩ := hfat
  refine not_positiveUpperDensity_misses hq' ⟨δ, hδ, ?_⟩
  exact hfreq.mono fun X hX => le_trans hX (densityRatio_mono hsub X)

/-- **Grand-orbit transfer.**  If the seeds whose orbit merges with the Euclid–Mullin orbit
have positive upper density, Mullin's conjecture holds. -/
theorem grandOrbit_transfer (hfat : PositiveUpperDensity {m | Rel m 2}) :
    Mullin.MullinConjecture :=
  transfer_principle Rel (fun _ hq _ _ h => misses_congr hq h) hfat

/-! ## 4. The structure of preimages -/

/-- `m'` is a `T`-preimage of `N`. -/
def IsPreimage (m' N : ℕ) : Prop := 1 ≤ m' ∧ genProd m' 1 = N

/-- **Preimages are `N / p` for a prime `p ∣ N` with `minFac (N/p + 1) = p`.** -/
theorem preimage_iff {m' N : ℕ} :
    IsPreimage m' N ↔ 1 ≤ m' ∧ ∃ p, p.Prime ∧ p ∣ N ∧ m' = N / p ∧ Nat.minFac (N / p + 1) = p := by
  constructor
  · rintro ⟨hm', hN⟩
    have hstep : genProd m' 1 = m' * genSeq m' 0 := rfl
    have hp : (genSeq m' 0).Prime := Nat.minFac_prime (by show m' + 1 ≠ 1; omega)
    refine ⟨hm', genSeq m' 0, hp, ⟨m', by rw [← hN, hstep, mul_comm]⟩, ?_, ?_⟩
    · rw [← hN, hstep, Nat.mul_div_cancel _ hp.pos]
    · rw [← hN, hstep, Nat.mul_div_cancel _ hp.pos]; rfl
  · rintro ⟨hm', p, hp, hdvd, rfl, hmin⟩
    refine ⟨hm', ?_⟩
    show N / p * genSeq (N / p) 0 = N
    have : genSeq (N / p) 0 = p := hmin
    rw [this, Nat.div_mul_cancel hdvd]

/-- The first multiplier recovers the preimage: `m' = N / genSeq m' 0`. -/
theorem preimage_eq_div {m' N : ℕ} (h : IsPreimage m' N) : m' = N / genSeq m' 0 := by
  have hstep : genProd m' 1 = m' * genSeq m' 0 := rfl
  have hp : (genSeq m' 0).Prime := Nat.minFac_prime (by show m' + 1 ≠ 1; have := h.1; omega)
  rw [← h.2, hstep, Nat.mul_div_cancel _ hp.pos]

/-- **Preimages inject into prime divisors.**  Two preimages of `N` with the same first
multiplier coincide; hence `N` has at most `ω(N)` preimages. -/
theorem preimage_multiplier_injective {m₁ m₂ N : ℕ} (h₁ : IsPreimage m₁ N)
    (h₂ : IsPreimage m₂ N) (h : genSeq m₁ 0 = genSeq m₂ 0) : m₁ = m₂ := by
  rw [preimage_eq_div h₁, preimage_eq_div h₂, h]

/-- **The square condition.**  For `p ∣ N`, the preimage condition `p ∣ N/p + 1` says
`p² ∣ N + p`: an extra branch of the backward tree at `N` is a mod-`p²` event. -/
theorem preimage_cond_iff_sq {p N : ℕ} (hp : 0 < p) (hdvd : p ∣ N) :
    p ∣ N / p + 1 ↔ p ^ 2 ∣ N + p := by
  obtain ⟨k, rfl⟩ := hdvd
  rw [Nat.mul_div_cancel_left k hp, pow_two, ← mul_add_one]
  exact (Nat.mul_dvd_mul_iff_left hp).symm

/-- Every ancestor of the Euclid–Mullin orbit divides an accumulator: the class of `2` is
contained in the divisors of the `prod b`. -/
theorem grandOrbit_two_dvd_prod {m : ℕ} (h : Rel m 2) : ∃ b, m ∣ Mullin.prod b := by
  obtain ⟨a, b, h⟩ := h
  exact ⟨b, by rw [← genProd_two_eq_prod, ← h]; exact start_dvd_genProd m a⟩

end GrandOrbit

end
