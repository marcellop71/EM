import EM.FunctionField.CriticalValues
import EM.FunctionField.Finiteness
import EM.FunctionField.Bootstrap

/-!
# What the `𝔽_5` counterexample forces: primes enter at composite stages

The function-field Mullin conjecture is false over `𝔽_5` because every Euclid polynomial
there is irreducible (`StableTower.lean`). This file states the mechanism for every `p`, as
a necessary condition on any proof.

Call stage `n` *prime* if `P_n + 1` is irreducible. Then the next term is `P_n + 1`, of
degree `deg P_n`, and `deg P_n` is strictly increasing. Hence:

* `eq_of_natDegree_eq_of_irreducible` — two terms entering at prime stages have different
  degrees: **prime stages supply at most one prime per degree**.
* `not_irreducible_of_natDegree_eq` — of two different primes of the same degree in the
  sequence, at least one entered at a composite stage.
* `exists_missed_of_perpetual` — if all stages from `N` on are prime, some monic irreducible
  never appears (any `p`). This is the `𝔽_5` argument without the explicit tower.
* `infinitelyManyReducible_of_ffMullinConjecture` — the conjecture over `𝔽_p` implies that
  every sequence has infinitely many composite stages.

## Reading

There are about `p^D / D` primes of degree `D`. At most one of them can enter at a prime
stage, so the conjecture is a statement about composite stages: about which of several
factors of `P_n + 1` has least degree. Over `𝔽_5` there are no composite stages at all.
Over `𝔽_2` there is one in every four consecutive stages
(`CompositeFloors.not_four_consecutive_irreducible`), for the reason that fails over `𝔽_5`:
`g = X² + X` is additive in characteristic 2, so the tower of prime stages has no
discriminant to keep it irreducible.
-/

namespace FunctionFieldAnalog

namespace CompositeEntry

open Polynomial CompositeFloors FFDegreeTelescope

variable {p : ℕ} [Fact (Nat.Prime p)]

theorem euclid_natDegree (d : FFEMData p) (n : ℕ) :
    (d.ffProd n + 1).natDegree = (d.ffProd n).natDegree :=
  natDegree_add_eq_left_of_natDegree_lt (by rw [natDegree_one]; exact ffProd_natDegree_pos d n)

/-- At a prime stage the next term has the degree of the current product. -/
theorem ffSeq_succ_natDegree_of_irreducible (d : FFEMData p) (n : ℕ)
    (h : Irreducible (d.ffProd n + 1)) :
    (d.ffSeq (n + 1)).natDegree = (d.ffProd n).natDegree := by
  rw [ffSeq_succ_eq_of_irreducible d n h, euclid_natDegree]

/-- At a prime stage the degree of the product doubles. -/
theorem ffProd_succ_natDegree_of_irreducible (d : FFEMData p) (n : ℕ)
    (h : Irreducible (d.ffProd n + 1)) :
    (d.ffProd (n + 1)).natDegree = 2 * (d.ffProd n).natDegree := by
  rw [ffProd_succ_of_irreducible d n h, (ffProd_monic p d n).natDegree_mul (euclid_monic d n),
    euclid_natDegree, two_mul]

/-- **Prime stages supply at most one prime per degree.** -/
theorem eq_of_natDegree_eq_of_irreducible (d : FFEMData p) {n m : ℕ}
    (hn : Irreducible (d.ffProd n + 1)) (hm : Irreducible (d.ffProd m + 1))
    (hdeg : (d.ffSeq (n + 1)).natDegree = (d.ffSeq (m + 1)).natDegree) : n = m := by
  rw [ffSeq_succ_natDegree_of_irreducible d n hn,
    ffSeq_succ_natDegree_of_irreducible d m hm] at hdeg
  exact (ffProd_natDegree_strict_mono p d).injective hdeg

/-- Of two different terms of the same degree, at least one entered at a composite stage. -/
theorem not_irreducible_of_natDegree_eq (d : FFEMData p) {n m : ℕ}
    (hne : d.ffSeq (n + 1) ≠ d.ffSeq (m + 1))
    (hdeg : (d.ffSeq (n + 1)).natDegree = (d.ffSeq (m + 1)).natDegree) :
    ¬ Irreducible (d.ffProd n + 1) ∨ ¬ Irreducible (d.ffProd m + 1) := by
  by_contra hcon
  push Not at hcon
  exact hne (by rw [eq_of_natDegree_eq_of_irreducible d hcon.1 hcon.2 hdeg])

/-- A term has degree at most that of the product at its index. -/
theorem ffSeq_natDegree_le_ffProd (d : FFEMData p) (n : ℕ) :
    (d.ffSeq n).natDegree ≤ (d.ffProd n).natDegree :=
  natDegree_le_of_dvd (ffSeq_dvd_own_prod d n) (ffProd_monic p d n).ne_zero

/-- **Perpetual irreducibility misses a prime (any `p`).** If every stage from `N` on is
    prime, some monic irreducible polynomial never appears in the sequence. -/
theorem exists_missed_of_perpetual (d : FFEMData p) (N : ℕ)
    (h : FFPerpetualIrreducibility d N) :
    ∃ Q : (ZMod p)[X], Q.Monic ∧ Irreducible Q ∧ ∀ n, d.ffSeq n ≠ Q := by
  have hmono := (ffProd_natDegree_strict_mono p d).monotone
  have hD0 : 0 < (d.ffProd N).natDegree := ffProd_natDegree_pos d N
  obtain ⟨Q, hQm, hQi, hQd⟩ :=
    ffExistsIrreducibleOfDegree (p := p) (2 * (d.ffProd N).natDegree + 1) (by omega)
  refine ⟨Q, hQm, hQi, fun n hn => ?_⟩
  have hdeg : (d.ffSeq n).natDegree = 2 * (d.ffProd N).natDegree + 1 := by rw [hn, hQd]
  rcases Nat.lt_or_ge N n with hlt | hle
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hmN : N ≤ m := by omega
    rw [ffSeq_succ_natDegree_of_irreducible d m (h m hmN)] at hdeg
    have h1 : (d.ffProd (N + 1)).natDegree = 2 * (d.ffProd N).natDegree :=
      ffProd_succ_natDegree_of_irreducible d N (h N le_rfl)
    have h2 : (d.ffProd (N + 2)).natDegree = 2 * (d.ffProd (N + 1)).natDegree :=
      ffProd_succ_natDegree_of_irreducible d (N + 1) (h (N + 1) (by omega))
    rcases Nat.lt_or_ge m (N + 2) with hm | hm
    · have : m = N ∨ m = N + 1 := by omega
      rcases this with rfl | rfl <;> omega
    · have := hmono hm
      simp only at this
      omega
  · have h1 := ffSeq_natDegree_le_ffProd d n
    have h2 := hmono hle
    simp only at h2
    omega

/-- **The conjecture needs composite stages.** Over any `𝔽_p`, the function-field Mullin
    conjecture implies that every sequence has infinitely many composite stages. -/
theorem infinitelyManyReducible_of_ffMullinConjecture (hmc : FFMullinConjecture p)
    (d : FFEMData p) : FFInfinitelyManyReducible d := by
  rw [ffInfinitelyManyReducible_iff]
  intro N hN
  obtain ⟨Q, hQm, hQi, hQ⟩ := exists_missed_of_perpetual d N hN
  obtain ⟨n, hn⟩ := hmc d Q hQm hQi
  exact hQ n hn

end CompositeEntry

end FunctionFieldAnalog
