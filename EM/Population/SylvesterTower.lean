import EM.Population.CompositeFloor
import EM.Equidist.WeakHitting

/-!
# (C∞) Identified: the Sylvester Tower

`EM/Population/CompositeFloor.lean` shows that every statement asserting the missing set
is small rests on

> **(C∞)** `prod n + 1` is composite for infinitely many `n`.

This file identifies (C∞) with a classical question and extends the floor down to the
weakest rung of the target ladder.

## The identification

On the perpetual-primality branch the accumulator recurrence degenerates to
`P ↦ P (P + 1)`, so the *Euclid numbers* satisfy

    (prod (n+1) + 1) = (prod n + 1) ^ 2 - (prod n + 1) + 1,

which is **Sylvester's recursion** `s ↦ s² - s + 1`.  Indeed `prod n + 1` for
`n = 0, 1, 2, 3` is `3, 7, 43, 1807`, which is Sylvester's sequence `2, 3, 7, 43, 1807,
3263443, …` from its second term: the Euclid–Mullin sequence *is* Sylvester's sequence
for exactly as long as the Euclid numbers remain prime, and it broke away at
`1807 = 13 · 139`, which is why `seq 4 = 13`.

`perpetualPrimality_iff_tower_prime` makes this exact: perpetual primality from `N` holds
iff every term of the Sylvester tower seeded at `prod N + 1` is prime.  So

> (C∞) ⟺ for every `N`, the Sylvester tower seeded at `prod N + 1` contains a composite.

Whether Sylvester's own sequence has only finitely many prime terms is, to the best of
the author's knowledge, an open problem (Guy–Nowakowski); **this attribution has not been
verified inside the present offline environment.**  What is verified here is the
identification, not the literature claim.

This also closes a loop with the take-all selection rule: banking *every* prime factor of
`P + 1` gives `P ↦ P (P+1)` outright, i.e. Sylvester's sequence.  The `minFac` rule
degenerates to the take-all rule precisely on the perpetual-primality branch.

## Why the two elementary attacks are dead here

*Congruence.*  Forcing a small prime `ℓ` into `prod n + 1` requires steering
`prod n mod ℓ` into one of the two roots of `Φ₆`, which exist iff `ℓ ≡ 1 (mod 6)`.  That
is a statement about the position of the orbit modulo a prime outside the bag — the
orbit-specificity barrier (Dead End #90), and `CvdP.free_transition` says congruence data
does not constrain it.

*Reciprocity.*  The available symbol data is automatically consistent and yields no
contradiction: `prod n ≡ 2 (mod 4)`, so `p = prod n + 1 ≡ 3 (mod 4)` and `(p-1)/2` is
odd; since `p ≡ 1 (mod seq k)` for every `k ≤ n`, quadratic reciprocity gives
`(seq k / p) = (-1) ^ ((seq k - 1) / 2)`, hence
`(prod n / p) = (2 / p) · (-1) ^ t` with `t = #{k ≤ n : seq k ≡ 3 (mod 4)}`.  But
`(prod n / p) = (-1 / p) = -1`, and `(2 / p)` is determined by `prod n mod 8`, which is
determined by the *same* parity `t`.  The two sides agree identically.  This is the
concrete instance of `Reciprocity.no_reciprocity_induction_proof`.

## The branch is not exotic — the sequence has been on it

`prod 6 + 1 = 6221671` and `prod 7 + 1 = 38709183810571` are both prime, so the
accumulator took the autonomous step `P ↦ P (P+1)` twice in a row, at stages `6` and `7`.
It broke out at stage `8`, where `139` divides the Euclid number.  That single divisibility
refutes the branch at every threshold `N ≤ 7`
(`not_perpetualPrimality_of_le_seven`), and needs no primality certificate: the hypothesis
supplies the autonomous step itself.

## The floor extends to the whole ladder

`infinitelyManyComposite_of_everyPrimeDividesEuclid`: even (V) — the weakest orbit target
of `EM/Equidist/WeakHitting.lean`, which asks only that every odd prime *divide* some
Euclid number — forces (C∞).  On the perpetual branch, Bertrand supplies a prime strictly
between `prod T + 1` and the next Euclid number; it is too large to divide the earlier
ones and too small to equal any later one, which are all prime.  So (C∞) sits beneath
every rung of the ladder `HH → MC → V`, as well as beneath the reciprocal-sum family.
-/

noncomputable section

open Mullin Euclid MullinGroup AutonomousBranch

namespace SylvesterTower

/-! ## Part 1: the tower -/

/-- The **Sylvester tower** seeded at `s`: `T (k+1) = T k ^ 2 - T k + 1`, written with
truncated subtraction as `T k * (T k - 1) + 1` so that no coercion is needed. -/
def tower (s : ℕ) : ℕ → ℕ
  | 0 => s
  | k + 1 => tower s k * (tower s k - 1) + 1

@[simp] theorem tower_zero (s : ℕ) : tower s 0 = s := rfl

theorem tower_succ (s k : ℕ) :
    tower s (k + 1) = tower s k * (tower s k - 1) + 1 := rfl

/-! ## Part 2: the Euclid numbers follow the tower exactly on the branch -/

/-- Under perpetual primality from `N`, the Euclid numbers from stage `N` on *are* the
Sylvester tower seeded at `prod N + 1`. -/
theorem prod_add_one_eq_tower {N : ℕ} (hpp : PerpetualPrimality N) (k : ℕ) :
    prod (N + k) + 1 = tower (prod N + 1) k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : prod (N + k + 1) = prod (N + k) * (prod (N + k) + 1) :=
        perpetual_prod_succ hpp (Nat.le_add_right N k)
      rw [tower_succ, ← ih, Nat.add_sub_cancel, show N + (k + 1) = N + k + 1 from rfl,
        hstep, Nat.mul_comm]

/-- **The identification.**  Perpetual primality from `N` is exactly the primality of
every term of the Sylvester tower seeded at `prod N + 1`. -/
theorem perpetualPrimality_iff_tower_prime {N : ℕ} :
    PerpetualPrimality N ↔ ∀ k, Nat.Prime (tower (prod N + 1) k) := by
  constructor
  · intro hpp k
    rw [← prod_add_one_eq_tower hpp k]
    exact hpp (N + k) (Nat.le_add_right N k)
  · intro htow
    -- rebuild the branch step by step, reading primality off the tower
    have key : ∀ k, prod (N + k) + 1 = tower (prod N + 1) k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          have hprime : Nat.Prime (prod (N + k) + 1) := by rw [ih]; exact htow k
          have hseq : seq (N + k + 1) = prod (N + k) + 1 := by
            rw [seq_succ]; exact euclid_minFac_self_of_prime hprime
          have hstep : prod (N + k + 1) = prod (N + k) * (prod (N + k) + 1) := by
            rw [prod_succ, hseq]
          rw [tower_succ, ← ih, Nat.add_sub_cancel,
            show N + (k + 1) = N + k + 1 from rfl, hstep, Nat.mul_comm]
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = N + k := ⟨n - N, by omega⟩
    rw [key k]
    exact htow k

/-- **(C∞) restated.**  Infinitely many composite Euclid numbers is exactly the failure of
Sylvester-tower primality at every seed `prod N + 1`. -/
theorem infinitelyManyComposite_iff_tower_composite :
    InfinitelyManyComposite ↔ ∀ N : ℕ, ∃ k, ¬ Nat.Prime (tower (prod N + 1) k) := by
  rw [infinitelyManyComposite_iff_no_perpetual_primality]
  constructor
  · intro h N
    by_contra hcon
    push Not at hcon
    exact h N (perpetualPrimality_iff_tower_prime.mpr hcon)
  · intro h N hpp
    obtain ⟨k, hk⟩ := h N
    exact hk (perpetualPrimality_iff_tower_prime.mp hpp k)

/-! ## Part 3: the floor reaches the weakest rung of the ladder -/

/-- **(V) forces (C∞).**  Even the weakest orbit target — every odd prime *divides* some
Euclid number, without any requirement that it be selected — cannot hold on the
perpetual-primality branch.  Bertrand supplies a prime `r` with
`prod T + 1 < r ≤ 2 (prod T + 1)`; it exceeds every earlier Euclid number, and every later
one is prime and already larger than `r`, so `r` divides none of them. -/
theorem infinitelyManyComposite_of_everyPrimeDividesEuclid
    (h : WeakHitting.EveryPrimeDividesEuclid) : InfinitelyManyComposite := by
  rw [infinitelyManyComposite_iff_no_perpetual_primality]
  intro T hpp
  have hP2 : 2 ≤ prod T := prod_ge_two T
  obtain ⟨r, hr, hrlt, hrle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (prod T + 1) (by omega)
  have hr2 : r ≠ 2 := by omega
  obtain ⟨n, hn⟩ := h r hr hr2
  rcases Nat.lt_or_ge T n with hTn | hnT
  · -- late: `prod n + 1` is prime and already exceeds `r`
    have hprime : Nat.Prime (prod n + 1) := hpp n (le_of_lt hTn)
    have hjump : 2 * (prod T + 1) < prod n + 1 := perpetual_candidate_jump hpp hTn
    have : r = prod n + 1 := ((Nat.prime_dvd_prime_iff_eq hr hprime).mp hn)
    omega
  · -- early: `prod n + 1 ≤ prod T + 1 < r`, so `r` is too large to divide it
    have hmono : prod n ≤ prod T := prod_le_prod_of_le hnT
    have hle : r ≤ prod n + 1 := Nat.le_of_dvd (by omega) hn
    omega

/-! ## Part 4: the branch is refuted at every threshold the data reaches

The autonomous branch is not an exotic hypothesis: the sequence has **been** on it.  The
Euclid numbers `prod 6 + 1 = 6221671` and `prod 7 + 1 = 38709183810571` are both prime, so
`seq 7` and `seq 8` are the whole Euclid numbers and the accumulator took the autonomous
step `P ↦ P (P+1)` twice in a row.  It broke out at the next stage:
`prod 8 + 1 = 1498400911280533294827535471 = 139 · 10779862671083836653435507`.
(The primality of `prod 7 + 1` was checked numerically; it is not used below.)

That last fact refutes the branch at every threshold up to `7`, and it does so without any
primality certificate, because the perpetual-primality hypothesis *supplies* the autonomous
step itself: from `N ≤ 7` it gives primality at stage `7`, hence
`prod 8 = prod 7 · (prod 7 + 1)`, and then demands that `prod 8 + 1` be prime — which `139`
refutes. -/

theorem prod_one : prod 1 = 6 := by simpa [prod_zero, seq_one] using prod_succ 0
theorem prod_two : prod 2 = 42 := by simpa [prod_one, seq_two] using prod_succ 1
theorem prod_three : prod 3 = 1806 := by simpa [prod_two, seq_three] using prod_succ 2
theorem prod_four : prod 4 = 23478 := by simpa [prod_three, seq_four] using prod_succ 3
theorem prod_five : prod 5 = 1244334 := by simpa [prod_four, seq_five] using prod_succ 4
theorem prod_six : prod 6 = 6221670 := by simpa [prod_five, seq_six] using prod_succ 5
theorem prod_seven : prod 7 = 38709183810570 := by
  simpa [prod_six, seq_seven] using prod_succ 6

/-- **The sequence really did visit the autonomous branch.**  `prod 6 + 1` is prime, so the
least factor is the whole Euclid number. -/
theorem euclid_prime_at_six : Nat.Prime (prod 6 + 1) := by
  have hge : 2 ≤ prod 6 + 1 := by have := prod_ge_two 6; omega
  have hmf : Euclid.minFac (prod 6 + 1) = prod 6 + 1 := by
    have h := seq_succ 6
    rw [seq_seven, prod_six] at h
    rw [prod_six]
    omega
  have := minFac_isPrime (prod 6 + 1) hge
  rw [hmf] at this
  exact (isPrime_iff_natPrime _).mp this

/-- The accumulator took the autonomous step at stage `6`. -/
theorem autonomous_step_at_six : prod 7 = prod 6 * (prod 6 + 1) := by
  rw [prod_seven, prod_six]

/-- **The autonomous branch cannot begin at or before stage `7`.**

No primality certificate is needed: perpetual primality from `N ≤ 7` itself forces the
step `prod 8 = prod 7 · (prod 7 + 1)`, and then requires `prod 8 + 1` to be prime.  But
`139` divides it, and `prod 8 + 1` is far larger than `139`. -/
theorem not_perpetualPrimality_of_le_seven {N : ℕ} (hN : N ≤ 7) :
    ¬ PerpetualPrimality N := by
  intro hpp
  have hstep : prod 8 = prod 7 * (prod 7 + 1) :=
    perpetual_prod_succ hpp (by omega : N ≤ 7)
  have h8 : Nat.Prime (prod 8 + 1) := hpp 8 (by omega)
  rw [hstep, prod_seven] at h8
  have hdvd : (139 : ℕ) ∣ 38709183810570 * (38709183810570 + 1) + 1 := by norm_num
  rcases h8.eq_one_or_self_of_dvd 139 hdvd with h | h <;> norm_num at h

/-- Equivalently: some Euclid number beyond any stage `≤ 7` is composite. -/
theorem exists_composite_beyond_seven {N : ℕ} (hN : N ≤ 7) :
    ∃ n, N ≤ n ∧ ¬ Nat.Prime (prod n + 1) := by
  by_contra hcon
  push Not at hcon
  exact not_perpetualPrimality_of_le_seven hN (fun n hn => hcon n hn)

/-! ## Landscape -/

/-- **(C∞), identified and universally required.**  It is exactly the failure of
Sylvester-tower primality at every seed on the orbit; it is implied by the whole target
ladder down to (V), and by every smallness statement about the missing set. -/
theorem sylvester_tower_landscape :
    (∀ N : ℕ, PerpetualPrimality N ↔ ∀ k, Nat.Prime (tower (prod N + 1) k)) ∧
    (InfinitelyManyComposite ↔ ∀ N : ℕ, ∃ k, ¬ Nat.Prime (tower (prod N + 1) k)) ∧
    (MullinConjecture → InfinitelyManyComposite) ∧
    (WeakHitting.EveryPrimeDividesEuclid → InfinitelyManyComposite) ∧
    (WeakMullin → InfinitelyManyComposite) ∧
    (ReciprocalDivergence → InfinitelyManyComposite) ∧
    (∀ N : ℕ, N ≤ 7 → ¬ PerpetualPrimality N) :=
  ⟨fun _ => perpetualPrimality_iff_tower_prime,
    infinitelyManyComposite_iff_tower_composite,
    CompositeFloor.infinitelyManyComposite_of_mullin,
    infinitelyManyComposite_of_everyPrimeDividesEuclid,
    CompositeFloor.infinitelyManyComposite_of_weakMullin,
    CompositeFloor.infinitelyManyComposite_of_reciprocalDivergence,
    fun _ hN => not_perpetualPrimality_of_le_seven hN⟩

end SylvesterTower

end
