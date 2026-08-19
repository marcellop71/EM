import EM.Ensemble.GenEM
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Lattice.Nat

/-!
# The Euclid-Mullin greedy dynamics on a profinite point

This file is **definitional plus one agreement theorem**.  It introduces **no
new mathematics**.  The profinite dynamics defined here is a repackaging of the
integer recursion `P(0) = m`, `P(k+1) = P(k) * minFac (P(k) + 1)` whose only
job is to make the population events of the seed-average program *cylinder
events*: after the repackaging, "the first `n` multipliers of the orbit of the
seed are such-and-such" becomes a condition on finitely many prime coordinates
of a point of

`Om = Π (r : Nat.Primes), ZMod r`.

## What is defined

* `Om`, the profinite space of residue vectors, and the diagonal embedding
  `iota : ℕ → Om`, `iota m r = (m : ZMod r)`.
* `vanishSet w`, the set of primes `r` whose `r`-coordinate of `w + 1` vanishes,
  and `leastVanishing w`, its infimum (junk value `1` when the set is empty).
* `profProd x : ℕ → Om` and `profSeq x : ℕ → ℕ`, the profinite orbit and its
  multiplier sequence.  A profinite point has no `minFac`; the greedy choice is
  therefore *not* transported from `Nat.minFac` but re-expressed coordinatewise:
  the multiplier is the **least prime whose coordinate of the current Euclid
  element vanishes**.

## What is proved

* `profProd_iota`, `profSeq_iota`: along the diagonal the profinite dynamics
  **is** the integer dynamics.  Unconditional apart from `1 ≤ m`.
* `leastVanishing_eq_of_agree` and `profProd_agree_of_agree`: the band-local
  refinement.  If two points agree on all prime coordinates `≤ Y` and the first
  `n` multipliers of one of them lie in `[2, Y]`, then the two orbits agree on
  the band `≤ Y` for `n` steps and have the same multipliers.
* `genSeq_eq_profSeq_of_agree`: the load-bearing specialization, with the second
  point a diagonal point `iota m`.

## Scope caveat

Nothing here says anything about the orbit of the seed `2`, i.e. about the
classical Euclid-Mullin sequence.  These are statements about the dynamics as a
*map*, and about population/seed-average arguments that quantify over seeds.
Dead ends #90 (orbit-specificity) and #117 are untouched by this file.
-/

noncomputable section
open Classical

namespace ProfiniteDynamics

/-! ## 1. The profinite space -/

/-- The profinite space of residue vectors: one residue per prime modulus. -/
abbrev Om := ∀ (r : Nat.Primes), ZMod (r : ℕ)

instance instNeZeroPrimeVal (r : Nat.Primes) : NeZero (r : ℕ) := ⟨r.2.ne_zero⟩

/-- The diagonal embedding of the integers into the profinite space. -/
def iota (m : ℕ) : Om := fun r => (m : ZMod (r : ℕ))

@[simp] theorem iota_apply (m : ℕ) (r : Nat.Primes) :
    iota m r = (m : ZMod (r : ℕ)) := rfl

/-! ## 2. The greedy choice, coordinatewise

A profinite point has no `minFac`.  The greedy Euclid-Mullin choice is instead
read off the coordinates: the multiplier is the least prime `r` at which the
`r`-coordinate of the *Euclid element* `w + 1` vanishes.  Along the diagonal
this is exactly `Nat.minFac (N + 1)` (`leastVanishing_iota`). -/

/-- The set of primes at which the Euclid element of `w` vanishes. -/
def vanishSet (w : Om) : Set ℕ := {r : ℕ | ∃ hr : Nat.Prime r, w ⟨r, hr⟩ + 1 = 0}

theorem mem_vanishSet_iff {w : Om} {r : ℕ} :
    r ∈ vanishSet w ↔ ∃ hr : Nat.Prime r, w ⟨r, hr⟩ + 1 = 0 := Iff.rfl

theorem prime_of_mem_vanishSet {w : Om} {r : ℕ} (h : r ∈ vanishSet w) :
    Nat.Prime r := h.choose

/-- The greedy multiplier of a profinite point: the least prime at which the
Euclid element vanishes, with the junk value `1` if there is no such prime. -/
def leastVanishing (w : Om) : ℕ :=
  if (vanishSet w).Nonempty then sInf (vanishSet w) else 1

theorem leastVanishing_of_nonempty {w : Om} (h : (vanishSet w).Nonempty) :
    leastVanishing w = sInf (vanishSet w) := if_pos h

theorem leastVanishing_of_empty {w : Om} (h : ¬ (vanishSet w).Nonempty) :
    leastVanishing w = 1 := if_neg h

/-- If the greedy multiplier is at least `2`, the vanishing set is nonempty. -/
theorem vanishSet_nonempty_of_two_le {w : Om} (h : 2 ≤ leastVanishing w) :
    (vanishSet w).Nonempty := by
  by_contra hcon
  rw [leastVanishing_of_empty hcon] at h
  omega

/-- The greedy multiplier is a vanishing prime, when there is one. -/
theorem leastVanishing_mem {w : Om} (h : (vanishSet w).Nonempty) :
    leastVanishing w ∈ vanishSet w := by
  rw [leastVanishing_of_nonempty h]; exact Nat.sInf_mem h

/-- The greedy multiplier is minimal among the vanishing primes. -/
theorem leastVanishing_le {w : Om} {r : ℕ} (h : r ∈ vanishSet w) :
    leastVanishing w ≤ r := by
  rw [leastVanishing_of_nonempty ⟨r, h⟩]; exact Nat.sInf_le h

/-! ## 3. The profinite orbit -/

/-- The profinite Euclid-Mullin orbit: `profProd x 0 = x` and each step
multiplies coordinatewise by the cast of the greedy multiplier. -/
def profProd (x : Om) : ℕ → Om
  | 0 => x
  | k + 1 => fun r => profProd x k r * ((leastVanishing (profProd x k) : ℕ) : ZMod (r : ℕ))

/-- The profinite multiplier sequence. -/
def profSeq (x : Om) (k : ℕ) : ℕ := leastVanishing (profProd x k)

@[simp] theorem profProd_zero (x : Om) : profProd x 0 = x := rfl

@[simp] theorem profProd_succ (x : Om) (k : ℕ) (r : Nat.Primes) :
    profProd x (k + 1) r = profProd x k r * ((profSeq x k : ℕ) : ZMod (r : ℕ)) := rfl

theorem profSeq_def (x : Om) (k : ℕ) :
    profSeq x k = leastVanishing (profProd x k) := rfl

/-! ## 4. The diagonal: `vanishSet` is the set of prime divisors of `N + 1` -/

theorem mem_vanishSet_iota {N r : ℕ} :
    r ∈ vanishSet (iota N) ↔ Nat.Prime r ∧ r ∣ N + 1 := by
  constructor
  · rintro ⟨hr, h⟩
    refine ⟨hr, ?_⟩
    have h' : ((N : ℕ) : ZMod r) + 1 = 0 := h
    have h'' : ((N + 1 : ℕ) : ZMod r) = 0 := by push_cast; exact h'
    exact (ZMod.natCast_eq_zero_iff _ _).mp h''
  · rintro ⟨hr, hdvd⟩
    refine ⟨hr, ?_⟩
    have h'' : ((N + 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    have h' : ((N : ℕ) : ZMod r) + 1 = 0 := by push_cast at h''; exact h''
    exact h'

/-- **The greedy choice on the diagonal is `Nat.minFac`.** -/
theorem leastVanishing_iota {N : ℕ} (hN : 1 ≤ N) :
    leastVanishing (iota N) = Nat.minFac (N + 1) := by
  have hp : Nat.Prime (Nat.minFac (N + 1)) := Nat.minFac_prime (by omega)
  have hmem : Nat.minFac (N + 1) ∈ vanishSet (iota N) :=
    mem_vanishSet_iota.mpr ⟨hp, Nat.minFac_dvd _⟩
  have hne : (vanishSet (iota N)).Nonempty := ⟨_, hmem⟩
  refine le_antisymm (leastVanishing_le hmem) ?_
  obtain ⟨hq, hqd⟩ := mem_vanishSet_iota.mp (leastVanishing_mem hne)
  exact Nat.minFac_le_of_dvd hq.two_le hqd

/-! ## 5. WP-3: agreement of the profinite and integer dynamics -/

/-- **Agreement of the accumulators.**  Along the diagonal, the profinite orbit
is the image of the integer orbit. -/
theorem profProd_iota {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    profProd (iota m) k = iota (genProd m k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hs : leastVanishing (profProd (iota m) k) = genSeq m k := by
      rw [ih, leastVanishing_iota (genProd_pos hm k), genSeq_def]
    funext r
    show profProd (iota m) k r * ((leastVanishing (profProd (iota m) k) : ℕ) : ZMod (r : ℕ))
        = iota (genProd m (k + 1)) r
    rw [hs, ih, genProd_succ]
    simp only [iota_apply]
    push_cast
    ring

/-- **Agreement of the multipliers.**  Along the diagonal, the profinite greedy
multiplier is the integer greedy multiplier. -/
theorem profSeq_iota {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    profSeq (iota m) k = genSeq m k := by
  rw [profSeq_def, profProd_iota hm k, leastVanishing_iota (genProd_pos hm k), genSeq_def]

/-! ## 6. WP-3b: band-local agreement

The multiplier at a step is determined by the coordinates `r ≤ Y` *provided the
multiplier itself is `≤ Y`*: the smallness of the true multiplier certifies that
no prime outside the band could have been selected earlier. -/

/-- Two profinite points agree on the band of primes `≤ Y`. -/
def AgreeUpTo (Y : ℕ) (x y : Om) : Prop := ∀ r : Nat.Primes, (r : ℕ) ≤ Y → x r = y r

theorem AgreeUpTo.symm {Y : ℕ} {x y : Om} (h : AgreeUpTo Y x y) : AgreeUpTo Y y x :=
  fun r hr => (h r hr).symm

/-- **One-step band locality.**  If `w` and `w'` agree on all prime coordinates
`≤ Y` and the greedy multiplier of `w` is a genuine prime lying in the band,
then the greedy multiplier of `w'` is the same. -/
theorem leastVanishing_eq_of_agree {Y : ℕ} {w w' : Om} (hag : AgreeUpTo Y w w')
    (h2 : 2 ≤ leastVanishing w) (hY : leastVanishing w ≤ Y) :
    leastVanishing w' = leastVanishing w := by
  obtain ⟨hprime, hzero⟩ := leastVanishing_mem (vanishSet_nonempty_of_two_le h2)
  -- The multiplier of `w` is a vanishing prime of `w'` too.
  have hmem' : leastVanishing w ∈ vanishSet w' := by
    refine ⟨hprime, ?_⟩
    rw [← hag ⟨leastVanishing w, hprime⟩ hY]
    exact hzero
  have hle : leastVanishing w' ≤ leastVanishing w := leastVanishing_le hmem'
  -- Conversely, the multiplier of `w'` lies in the band, hence is visible to `w`.
  obtain ⟨hprime', hzero'⟩ := leastVanishing_mem ⟨_, hmem'⟩
  have hmem : leastVanishing w' ∈ vanishSet w := by
    refine ⟨hprime', ?_⟩
    rw [hag ⟨leastVanishing w', hprime'⟩ (le_trans hle hY)]
    exact hzero'
  exact le_antisymm hle (leastVanishing_le hmem)

/-- **Band-local agreement of the orbits.**  If `x` and `y` agree on all prime
coordinates `≤ Y`, and the first `n` profinite multipliers of `x` lie in
`[2, Y]`, then the orbit of `y` agrees with the orbit of `x` on the band for
`n` steps, with the same multipliers. -/
theorem profProd_agree_of_agree {Y : ℕ} {x y : Om} (hag : AgreeUpTo Y x y) :
    ∀ n : ℕ, (∀ j < n, 2 ≤ profSeq x j ∧ profSeq x j ≤ Y) →
      (∀ j ≤ n, AgreeUpTo Y (profProd x j) (profProd y j)) ∧
      (∀ j < n, profSeq y j = profSeq x j) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    intro j hj
    have : j = 0 := Nat.le_zero.mp hj
    subst this
    exact hag
  | succ n ih =>
    intro hsmall
    obtain ⟨ihag, ihmul⟩ := ih (fun j hj => hsmall j (Nat.lt_succ_of_lt hj))
    obtain ⟨h2, hY⟩ := hsmall n (Nat.lt_succ_self n)
    have hstep : profSeq y n = profSeq x n :=
      leastVanishing_eq_of_agree (ihag n le_rfl) h2 hY
    refine ⟨?_, ?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hj) with h | h
      · exact ihag j (Nat.lt_succ_iff.mp h)
      · subst h
        intro r hr
        rw [profProd_succ, profProd_succ, hstep, ihag n le_rfl r hr]
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact ihmul j h
      · subst h; exact hstep

/-- **The load-bearing corollary for the population transfer.**  If the seed `m`
agrees with the profinite point `x` on every prime coordinate `≤ Y`, and the
first `n` profinite multipliers of `x` lie in `[2, Y]`, then the integer orbit of
`m` reproduces those multipliers exactly. -/
theorem genSeq_eq_profSeq_of_agree {Y n m : ℕ} {x : Om} (hm : 1 ≤ m)
    (hag : ∀ r : Nat.Primes, (r : ℕ) ≤ Y → x r = (m : ZMod (r : ℕ)))
    (hsmall : ∀ j < n, 2 ≤ profSeq x j ∧ profSeq x j ≤ Y) :
    ∀ j < n, genSeq m j = profSeq x j := by
  have hag' : AgreeUpTo Y x (iota m) := hag
  intro j hj
  rw [← profSeq_iota hm j]
  exact (profProd_agree_of_agree hag' n hsmall).2 j hj

/-- The accumulator half of the corollary: the band coordinates of the integer
orbit are the band coordinates of the profinite orbit. -/
theorem genProd_agree_of_agree {Y n m : ℕ} {x : Om} (hm : 1 ≤ m)
    (hag : ∀ r : Nat.Primes, (r : ℕ) ≤ Y → x r = (m : ZMod (r : ℕ)))
    (hsmall : ∀ j < n, 2 ≤ profSeq x j ∧ profSeq x j ≤ Y) :
    ∀ j ≤ n, ∀ r : Nat.Primes, (r : ℕ) ≤ Y →
      profProd x j r = ((genProd m j : ℕ) : ZMod (r : ℕ)) := by
  have hag' : AgreeUpTo Y x (iota m) := hag
  intro j hj r hr
  have := (profProd_agree_of_agree hag' n hsmall).1 j hj r hr
  rw [this, profProd_iota hm j, iota_apply]

end ProfiniteDynamics

end
