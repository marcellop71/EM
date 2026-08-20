import EM.Population.GrandOrbit
import EM.Population.DefectTelescope

/-!
# The adelic shadow of the greedy orbit

Session 318 (2026-08-20).  Development of the "one apt angle" of the condensed-mathematics
assessment: the greedy step is multiplication by a **principal idele** `λ_n = p_{n+1}`,
dilating the archimedean coordinate and contracting the `p_{n+1}`-adic one, with the product
formula balancing the two.  This file records what that bookkeeping proves about a single
orbit — honestly little, but two of the facts are new to the repository and one of them is the
right way to state the failure of MC at a prime.

## The local side: every finite place is eventually a unit

For a prime `q` and a seed `m ≥ 1`, the Euclid numbers `E_n = genProd m n + 1` are divisible
by `q` for only **finitely many** `n` (`hits_finite`).  The argument is the adelic shadow of
distinctness: at a hit, the multiplier `minFac E_n` is a prime `≤ q`; multipliers are pairwise
distinct (`genSeq_ne_of_lt`); so the hits inject into the primes `≤ q`.  Consequently:

* `captured_of_many_hits` — more than `π(q−1)` hits force `q` itself to be chosen: the
  "hit but outranked" failure mode can occur at most `π(q−1)` times in a whole orbit;
* `eventually_unit` — for every finite place `q`, `|E_n|_q = 1` for all large `n`,
  whether `q` is captured (then `q ∣ P_n`, so `q ∤ E_n`) or missed (then `q ∤ E_n` from some
  point on by `hits_finite`).

So the failure of MC at `q` is *exactly* "`E_n ∈ ℤ_q^×` for all large `n` and `q ∤ P_n`": the
two classical failure modes (walk avoids `−1 mod q` forever; walk hits `−1` but a smaller
prime is chosen) collapse, up to finitely many steps, into the first.

## The archimedean side: the defect is the degree of the discarded divisor

`DefectTelescope.defect n = log P_n − log p_{n+1}` governs the growth constant.  Adelically
it is, up to `log(1 + 1/P_n)`, the logarithm of the **cofactor** `E_n / p_{n+1}`
(`defect_eq_log_cofactor`): the archimedean size of the part of the divisor of `E_n` that the
greedy rule discards.  The telescope `L_N = 2^N (L_0 − Σ 2^{−1−n} δ_n)` is thus the product
formula summed along the orbit with the chosen place removed at each step.

## What the angle would need, and why the two available theories do not supply it

A height argument for capture needs an inequality that **localises** archimedean size at a
*fixed small* prime `q` along the orbit.  The product formula gives only totals,
`Σ_{p ∣ E_n} v_p(E_n) log p = log E_n ≈ 2^n`, dominated by huge primes.  The `S`-unit /
subspace theorems (Mahler, Størmer, Corvaja–Zannier) localise height at finitely many places,
but for a *fixed* support `S`; here `P_n` is an `S_n`-unit with `S_n = {p_0, …, p_n}` growing,
and every statement with fixed `S` is exhausted after finitely many `n` — the same technique
mismatch as the Tauberian one (#134).  Formally, `eventually_unit` is the strongest local
statement the bookkeeping yields, and it is symmetric between capture and failure.

## Scope

Population-free and orbit-level, but every theorem here is a finiteness or an identity; none
constrains *which* branch of the dichotomy the orbit of `2` takes.  #90/#117 untouched.
-/

noncomputable section
open Classical

namespace AdelicShadow

/-! ## 1. Distinct multipliers -/

/-- Multipliers are pairwise distinct: `genSeq m k ∣ genProd m n` for `k < n`, while
`genSeq m n` is coprime to `genProd m n`. -/
theorem genSeq_ne_of_lt {m k n : ℕ} (hm : 1 ≤ m) (hkn : k < n) : genSeq m n ≠ genSeq m k := by
  intro heq
  have hp : (genSeq m n).Prime :=
    Nat.minFac_prime (by have := genProd_pos hm n; show genProd m n + 1 ≠ 1; omega)
  have h1 : genSeq m n ∣ genProd m n + 1 := Nat.minFac_dvd _
  have h2 : genSeq m n ∣ genProd m n :=
    (ProfiniteAttractor.prime_dvd_genProd_iff hp m n).mpr (Or.inr ⟨k, hkn, heq.symm⟩)
  have : genSeq m n ∣ 1 := by
    have := (Nat.dvd_add_right h2).mp h1
    exact this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-! ## 2. Hits at a fixed place are finite -/

/-- The set of steps at which `q` divides the Euclid number. -/
def hits (q m : ℕ) : Set ℕ := {n | q ∣ genProd m n + 1}

/-- At a hit the multiplier is at most `q`. -/
theorem genSeq_le_of_mem_hits {q m n : ℕ} (hq : q.Prime) (h : n ∈ hits q m) :
    genSeq m n ≤ q :=
  Nat.minFac_le_of_dvd hq.two_le h

/-- **Every finite place is hit only finitely often.**  The multiplier map is injective on
the hits and lands in `[2, q]`. -/
theorem hits_finite (q m : ℕ) (hq : q.Prime) (hm : 1 ≤ m) : (hits q m).Finite := by
  refine Set.Finite.of_finite_image (f := genSeq m) ?_ ?_
  · refine (Set.finite_Icc 2 q).subset ?_
    rintro _ ⟨n, hn, rfl⟩
    exact Set.mem_Icc.mpr ⟨(Nat.minFac_prime (by
      have := genProd_pos hm n; show genProd m n + 1 ≠ 1; omega)).two_le,
      genSeq_le_of_mem_hits hq hn⟩
  · intro a _ b _ hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact genSeq_ne_of_lt hm h hab.symm
    · exact genSeq_ne_of_lt hm h hab

/-- **Many hits force capture.**  If `q` divides the Euclid number at more than `π(q−1)`
steps, then `q` is selected: the "hit but outranked" mode happens at most `π(q−1)` times. -/
theorem captured_of_many_hits (q m : ℕ) (hq : q.Prime) (hm : 1 ≤ m)
    (h : ((Finset.range q).filter Nat.Prime).card < (hits_finite q m hq hm).toFinset.card) :
    ∃ n, genSeq m n = q := by
  by_contra hno
  have hno' : ∀ n, genSeq m n ≠ q := fun n h => hno ⟨n, h⟩
  have hinj : Set.InjOn (genSeq m) ↑(hits_finite q m hq hm).toFinset := by
    intro a _ b _ hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h' | h'
    · exact genSeq_ne_of_lt hm h' hab.symm
    · exact genSeq_ne_of_lt hm h' hab
  have himg : (hits_finite q m hq hm).toFinset.image (genSeq m) ⊆
      (Finset.range q).filter Nat.Prime := by
    intro p hp
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
    have hn' : n ∈ hits q m := (Set.Finite.mem_toFinset _).mp hn
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,
      Nat.minFac_prime (by have := genProd_pos hm n; show genProd m n + 1 ≠ 1; omega)⟩
    exact lt_of_le_of_ne (genSeq_le_of_mem_hits hq hn') (hno' n)
  have := Finset.card_le_card himg
  rw [Finset.card_image_of_injOn hinj] at this
  omega

/-- **Every finite place is eventually a unit on the Euclid numbers**, whether or not `q` is
ever selected. -/
theorem eventually_unit (q m : ℕ) (hq : q.Prime) (hm : 1 ≤ m) :
    ∃ n₀, ∀ n, n₀ ≤ n → ¬ q ∣ genProd m n + 1 := by
  obtain ⟨N, hN⟩ := (hits_finite q m hq hm).bddAbove
  refine ⟨N + 1, fun n hn hdvd => ?_⟩
  have : n ≤ N := hN hdvd
  omega

/-- **The failure of MC at `q`, adelically.**  For `q ∤ m`: `q` is missed iff `q` is never
selected iff `E_n ∈ ℤ_q^×` for all large `n` *and* `q ∤ P_n` for all `n` — i.e. the orbit is
eventually a `q`-adic unit on both `P_n` and `E_n`. -/
theorem misses_iff_eventually_unit_both {q m : ℕ} (hq : q.Prime) (hm : 1 ≤ m) (hqm : ¬ q ∣ m) :
    GrowingRange.Misses q m ↔
      (∀ n, ¬ q ∣ genProd m n) ∧ ∃ n₀, ∀ n, n₀ ≤ n → ¬ q ∣ genProd m n + 1 := by
  constructor
  · rintro ⟨-, hnever⟩
    refine ⟨fun n hdvd => ?_, eventually_unit q m hq hm⟩
    rcases (ProfiniteAttractor.prime_dvd_genProd_iff hq m n).mp hdvd with h | ⟨k, _, hk⟩
    · exact hqm h
    · exact hnever k hk
  · rintro ⟨hP, -⟩
    refine ⟨hqm, fun k hk => ?_⟩
    exact hP (k + 1) ((ProfiniteAttractor.prime_dvd_genProd_iff hq m (k + 1)).mpr
      (Or.inr ⟨k, Nat.lt_succ_self k, hk⟩))

/-! ## 3. The archimedean shadow: defect = log of the discarded cofactor -/

open Mullin DefectTelescope in
/-- The defect of `DefectTelescope` is the logarithm of the discarded cofactor
`(P_n + 1) / p_{n+1}`, corrected by `log(1 + 1/P_n)`. -/
theorem defect_eq_log_cofactor (n : ℕ) :
    defect n = Real.log (((prod n : ℝ) + 1) / (seq (n + 1) : ℝ)) - Real.log (1 + 1 / (prod n : ℝ)) := by
  have hP : (0 : ℝ) < (prod n : ℝ) := by
    have := prod_ge_two n; exact_mod_cast (by omega : 0 < prod n)
  have hs : (0 : ℝ) < (seq (n + 1) : ℝ) := by
    have := (seq_isPrime (n + 1)).1; exact_mod_cast (by omega : 0 < seq (n + 1))
  have h1 : (1 : ℝ) + 1 / (prod n : ℝ) = ((prod n : ℝ) + 1) / (prod n : ℝ) := by
    field_simp
  rw [defect, logProd, h1, Real.log_div (by positivity) hs.ne', Real.log_div (by positivity) hP.ne']
  ring

end AdelicShadow

end
