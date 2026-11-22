import EM.FunctionField.ExitLevel

/-!
# The prime as the seed: the degree law at the exit from the tower

2026-11-22.

Over `ℤ` the family is the set of seeds `m`, and the seed-average theorems are densities of
sets of seeds. Over `𝔽_p[X]` the sequence starts at `X` for every `p`, and the first Euclid
polynomials are reductions of fixed polynomials with integer coefficients (the tower levels
`T_k`). So the prime `p` plays the role of the seed: a statement "the sequence over `𝔽_p[X]`
has such-and-such a shape" defines a set of primes, and that set has a density.

This file records the first complete instance. If `p` leaves the tower at level `K + 1`
(levels `0, …, K` irreducible, level `K + 1` reducible), then for *every* sequence over
`𝔽_p[X]`

* the terms at stages `1, …, K + 1` are the levels `T_0, …, T_K`, of degrees `1, 2, …, 2^K`;
* the term at stage `K + 2` has degree exactly `2^K`: the reducible level `T_{K+1}` is a
  product of two irreducible polynomials of degree `2^K`.

The set of such primes has analytic density `2^{-(K+1)}` (`ExitLevel.exit_analytic_density`).
So, in analytic density over the primes: with probability `1/2` the degrees of the first terms
are `1, 1, 1` (this is `p ≡ 1 (mod 3)`, where the factor is linear), with probability `1/4`
they are `1, 1, 2, 2`, with probability `1/8` they are `1, 1, 2, 4, 4`, and so on; the
remaining set, the stable primes, has density `0`.

## Main results

* `natDegree_of_dvd_level_succ` — if `T_K` is irreducible and `T_{K+1}` is not, every
  irreducible factor of `T_{K+1}` has degree `2^K`.
* `ffProd_eq_iter`, `ffSeq_succ_eq_level` — while the levels are irreducible, every sequence
  is the tower.
* `exit_degree` — the degree of the first term off the tower.
* `exit_degree_law` — the same for the set `surviveSet K \ surviveSet (K + 1)`.
-/

namespace FunctionFieldAnalog

namespace DegreeLaw

open Polynomial FrobeniusOrbit TowerClassification StabilityCriterion CompositeFloors ExitLevel

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- If `T_K` is irreducible and `T_{K+1}` is not, every irreducible factor of `T_{K+1}` has
degree `2^K`. -/
theorem natDegree_of_dvd_level_succ {K : ℕ} (hK : Irreducible (level p K))
    (hnot : ¬ Irreducible (level p (K + 1))) {f : (ZMod p)[X]} (hf : Irreducible f)
    (hdvd : f ∣ level p (K + 1)) : f.natDegree = 2 ^ K := by
  obtain ⟨α, hα⟩ := exists_aeval_eq_zero p hf
  have hαG : aeval α (level p (K + 1)) = 0 := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, map_mul, hα, zero_mul]
  have hθroot : aeval (aeval α (X * (X + 1) : (ZMod p)[X])) (level p K) = 0 := by
    rw [← aeval_comp, ← level_succ_comp]; exact hαG
  have hαfix : Φ p f.natDegree α = α := by
    rw [Φ_apply]; exact pow_p_pow_natDegree_eq_self p hf hα
  have hm : 2 ^ K ∣ f.natDegree := by
    have := natDegree_dvd_of_fixed hK hθroot (e := f.natDegree)
      (by rw [← Φ_apply, Φ_aeval, hαfix])
    rwa [level_natDegree] at this
  have hG0 : level p (K + 1) ≠ 0 := (level_monic (K + 1)).ne_zero
  have hle : f.natDegree ≤ 2 ^ (K + 1) := by
    have := natDegree_le_of_dvd hdvd hG0
    rwa [level_natDegree] at this
  have hpos : 0 < f.natDegree := hf.natDegree_pos
  obtain ⟨t, ht⟩ := hm
  have ht2 : t ≤ 2 := by
    rw [ht, pow_succ] at hle
    exact Nat.le_of_mul_le_mul_left hle (by positivity)
  have ht0 : t ≠ 0 := by rintro rfl; omega
  rcases Nat.lt_or_ge t 2 with h1 | h2
  · have : t = 1 := by omega
    rw [ht, this, mul_one]
  · exfalso
    have ht' : t = 2 := le_antisymm ht2 h2
    have hdeg : f.natDegree = (level p (K + 1)).natDegree := by
      rw [level_natDegree, ht, ht', pow_succ]
    obtain ⟨c, hc⟩ := hdvd
    have hc0 : c ≠ 0 := by rintro rfl; exact hG0 (by rw [hc, mul_zero])
    have hcdeg : c.natDegree = 0 := by
      have := congrArg natDegree hc
      rw [natDegree_mul hf.ne_zero hc0] at this
      omega
    have hcu : IsUnit c := by
      rw [eq_C_of_natDegree_eq_zero hcdeg] at hc0 ⊢
      exact isUnit_C.mpr (IsUnit.mk0 _ (by simpa using hc0))
    apply hnot
    rw [hc]
    exact (irreducible_mul_isUnit hcu).mpr hf

/-- While the levels are irreducible, the accumulator of every sequence is the iterate. -/
theorem ffProd_eq_iter {K : ℕ} (hK : ∀ k ≤ K, Irreducible (level p k)) (d : FFEMData p) :
    ∀ k ≤ K + 1, d.ffProd k = iter p k := by
  intro k
  induction k with
  | zero => intro _; rw [d.ffProd_zero]; rfl
  | succ k ih =>
    intro hk
    have hk' : k ≤ K := by omega
    have hprev := ih (by omega)
    have hirr : Irreducible (d.ffProd k + 1) := by rw [hprev]; exact hK k hk'
    rw [ffProd_succ_of_irreducible d k hirr, hprev]
    rfl

/-- While the levels are irreducible, the terms of every sequence are the levels. -/
theorem ffSeq_succ_eq_level {K : ℕ} (hK : ∀ k ≤ K, Irreducible (level p k)) (d : FFEMData p)
    {k : ℕ} (hk : k ≤ K) : d.ffSeq (k + 1) = level p k := by
  have hprod := ffProd_eq_iter hK d k (by omega)
  have hirr : Irreducible (d.ffProd k + 1) := by rw [hprod]; exact hK k hk
  rw [ffSeq_succ_eq_of_irreducible d k hirr, hprod]
  rfl

/-- **The degree at the exit.** If the levels `0, …, K` are irreducible over `𝔽_p` and the
level `K + 1` is not, then for every sequence over `𝔽_p[X]` the terms at stages `1, …, K+1`
are the levels, of degrees `1, 2, …, 2^K`, and the term at stage `K + 2` has degree `2^K`. -/
theorem exit_degree {K : ℕ} (hK : ∀ k ≤ K, Irreducible (level p k))
    (hnot : ¬ Irreducible (level p (K + 1))) (d : FFEMData p) :
    (∀ k ≤ K, d.ffSeq (k + 1) = level p k ∧ (d.ffSeq (k + 1)).natDegree = 2 ^ k) ∧
      (d.ffSeq (K + 2)).natDegree = 2 ^ K := by
  refine ⟨fun k hk => ?_, ?_⟩
  · have h := ffSeq_succ_eq_level hK d hk
    exact ⟨h, by rw [h, level_natDegree]⟩
  · obtain ⟨-, hirr, hdvd⟩ := d.ffSeq_succ (K + 1)
    have hE : d.ffProd (K + 1) + 1 = level p (K + 1) := by
      rw [ffProd_eq_iter hK d (K + 1) le_rfl]; rfl
    rw [hE] at hdvd
    exact natDegree_of_dvd_level_succ (hK K le_rfl) hnot hirr hdvd

/-- **The degree law at the exit, as a set of primes.** For every prime in
`surviveSet K \ surviveSet (K + 1)` — a set of analytic density `2^{-(K+1)}` by
`ExitLevel.exit_analytic_density` — every sequence over `𝔽_p[X]` has terms of degrees
`1, 2, …, 2^K` at stages `1, …, K + 1` and a term of degree `2^K` at stage `K + 2`. -/
theorem exit_degree_law (K : ℕ) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ surviveSet K \ surviveSet (K + 1)) (d : FFEMData p) :
    (∀ k ≤ K, (d.ffSeq (k + 1)).natDegree = 2 ^ k) ∧ (d.ffSeq (K + 2)).natDegree = 2 ^ K := by
  obtain ⟨⟨h, hK⟩, hnotmem⟩ := hp
  have hnot : ¬ Irreducible (level p (K + 1)) := by
    intro hirr
    apply hnotmem
    refine ⟨h, fun k hk => ?_⟩
    rcases Nat.lt_or_ge k (K + 1) with hlt | hge
    · exact hK k (by omega)
    · obtain rfl : k = K + 1 := le_antisymm hk hge
      exact hirr
  obtain ⟨h1, h2⟩ := exit_degree hK hnot d
  exact ⟨fun k hk => (h1 k hk).2, h2⟩

end DegreeLaw

end FunctionFieldAnalog
