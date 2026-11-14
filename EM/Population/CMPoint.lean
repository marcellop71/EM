import EM.Population.Confinement
import EM.Population.ClassInfinitude

/-!
# The Euclid step as a CM point: the principal form, its representation bound, and the
tower as the constant point `j = 0`

Session 322 (2026-10-25).  Memo: `docs/analysis/euclid_systems_theory_2026-09-23.md` §15.

`QuadraticStep.lean` writes the step as a norm, `E_{n+1} = N(p ω − 1)` in the order of
discriminant `D_n = 1 − 4 c_n`.  Here the same identity is read as the value of the
**principal binary quadratic form** of that discriminant,

    E_{n+1} = Q_n(−1, p_{n+1}),   Q_n(x, y) = x² + x y + c_n y²,

i.e. the Euclid number is *represented* by the principal form at the point `(−1, p_{n+1})`.
This is the object the step is linked to: the imaginary quadratic order `O_n` of discriminant
`D_n`, equivalently the CM point of discriminant `D_n` on the `j`-line, whose automorphic side
is the weight-one theta series of the forms of discriminant `D_n`.

## Main results

* `euclid_succ_eq_principalForm` — the representation `E_{n+1} = Q_n(−1, p_{n+1})`.
* `four_mul_principalForm` — `4 Q(x,y) = (2x + y)² − D y²`, the discriminant identity.
* `principalForm_ge_of_ne_zero`, `not_represents_of_lt` — **the principal form represents
  nothing below `c_n` except squares**: every integer `m < c_n` with a representation `y ≠ 0`
  is impossible.  In ideal language, a prime ideal of norm `q < c_n` is non-principal, and
  `represents_pow_imp_le` gives the class-order bound `q^k ≥ c_n` for `𝔮^k` principal.
* `disc_eq_neg_three_iff` — **a stage is prime iff its CM point is `ρ`** (`D_n = −3`, the
  elliptic point of order three, `j = 0`); `perpetual_disc_eq_neg_three` — a Sylvester tower
  is the *constant* CM point `j = 0`; `confined_iff_disc_eq_neg_three_mul_sq` — a confined
  stage is a CM point of `j`-invariant `0` with conductor `s`, i.e. a point of the Hecke orbit
  of `ρ`.
* `mullin_implies_nonprincipal_least_factor` — the class-group reading of MC: every prime
  `q ≥ 5` is at some stage the least norm among the prime ideals in the principal relation
  `(p_{n+1} ω_n − 1) = ∏ 𝔮_i`, and when `q < c_n` the ideal `𝔮` of norm `q` is non-principal.

Nothing here is a route; it is the dictionary.  The correspondence is one step deep: the
order changes at every stage and its discriminant has the size of the Euclid number.
-/

open Classical Mullin QuadraticStep

namespace CMPoint

/-- The principal form of discriminant `1 − 4c`: `Q(x, y) = x² + x y + c y²`. -/
def principalForm (c x y : ℤ) : ℤ := x ^ 2 + x * y + c * y ^ 2

/-- `m` is represented by the principal form of discriminant `1 − 4c` with `y ≠ 0`
(representations with `y = 0` are the squares and carry no arithmetic). -/
def Represents (c m : ℤ) : Prop := ∃ x y : ℤ, y ≠ 0 ∧ principalForm c x y = m

/-- The discriminant identity `4 Q(x, y) = (2x + y)² − (1 − 4c) y²`. -/
theorem four_mul_principalForm (c x y : ℤ) :
    4 * principalForm c x y = (2 * x + y) ^ 2 - (1 - 4 * c) * y ^ 2 := by
  unfold principalForm; ring

/-- **The Euclid number is a value of the principal form**: `E_{n+1} = Q_n(−1, p_{n+1})`. -/
theorem euclid_succ_eq_principalForm (n : ℕ) :
    ((prod (n + 1) + 1 : ℕ) : ℤ) = principalForm (cofactor n) (-1) (Mullin.seq (n + 1)) := by
  rw [euclid_succ_eq_norm, principalForm]; ring

/-- The discriminant of the step's form is `disc n`. -/
theorem four_mul_euclid_succ_eq (n : ℕ) :
    4 * ((prod (n + 1) + 1 : ℕ) : ℤ)
      = (2 * (-1) + (Mullin.seq (n + 1) : ℤ)) ^ 2 - disc n * (Mullin.seq (n + 1) : ℤ) ^ 2 := by
  rw [euclid_succ_eq_principalForm, four_mul_principalForm, disc]

/-- `E_{n+1}` is represented by the principal form of discriminant `D_n`, at `(−1, p_{n+1})`. -/
theorem represents_euclid_succ (n : ℕ) :
    Represents (cofactor n) ((prod (n + 1) + 1 : ℕ) : ℤ) :=
  ⟨-1, Mullin.seq (n + 1), by exact_mod_cast (seq_succ_pos n).ne', (euclid_succ_eq_principalForm n).symm⟩

/-- **The representation bound.**  With `c > 0` and `y ≠ 0`, `Q(x, y) ≥ c`: the principal form
takes no value below `c` away from the axis `y = 0`. -/
theorem principalForm_ge_of_ne_zero {c x y : ℤ} (hc : 0 < c) (hy : y ≠ 0) :
    c ≤ principalForm c x y := by
  have h4 := four_mul_principalForm c x y
  have hy2 : 1 ≤ y ^ 2 := by
    have : 0 < y ^ 2 := by positivity
    omega
  have hsq : 0 ≤ (2 * x + y) ^ 2 := sq_nonneg _
  nlinarith

/-- No integer below `c` is represented with `y ≠ 0`.  In ideal language: a prime ideal of
norm `q < c_n` in the order of discriminant `1 − 4c_n` is **non-principal**. -/
theorem not_represents_of_lt {c m : ℤ} (hc : 0 < c) (hm : m < c) : ¬ Represents c m := by
  rintro ⟨x, y, hy, rfl⟩
  exact absurd (principalForm_ge_of_ne_zero hc hy) (not_le.mpr hm)

/-- **Class-order bound.**  If `q^k` is represented with `y ≠ 0` (the ideal `𝔮^k` is principal),
then `q^k ≥ c`; so the class of a prime ideal of norm `q` has order at least `log c / log q`.

Note (2026-11-10): the theorem is the inequality `c ≤ q ^ k` for a represented `q ^ k` and
nothing more.  The class-order gloss is a heuristic reading that needs hypotheses not present
here: `D = 1 − 4c` is in general *not* a fundamental discriminant, so the order is non-maximal,
and "the class of the prime ideal of norm `q`" makes sense only for `q` prime to the conductor
(invertible ideals) and split, with `q ∤ D`.  At a ramified `q` (or `q` dividing the conductor)
a representation of `q ^ k` with `y ≠ 0` does not translate into "`𝔮^k` is principal" in the
form class group, and conversely a non-primitive representation of `q ^ k` corresponds to a
product `𝔮^a 𝔮̄^b`, not to `𝔮^k`.  No class group is defined in this file. -/
theorem represents_pow_imp_le {c q : ℤ} (hc : 0 < c) {k : ℕ} (h : Represents c (q ^ k)) :
    c ≤ q ^ k := by
  obtain ⟨x, y, hy, hxy⟩ := h
  rw [← hxy]; exact principalForm_ge_of_ne_zero hc hy

/-! ## The tower is the constant CM point `j = 0` -/

/-- `D_n = −3` iff `c_n = 1`. -/
theorem disc_eq_neg_three_iff_cofactor (n : ℕ) : disc n = -3 ↔ cofactor n = 1 := by
  unfold disc; omega

/-- **A stage is prime iff its CM point is `ρ`**: `D_n = −3` iff `E_n` is prime. -/
theorem disc_eq_neg_three_iff (n : ℕ) : disc n = -3 ↔ Nat.Prime (prod n + 1) := by
  refine ⟨fun h => ?_, disc_eq_neg_three_of_prime⟩
  have hc := (disc_eq_neg_three_iff_cofactor n).mp h
  have := seq_mul_cofactor n
  rw [hc, mul_one] at this
  rw [← this]; exact EuclidClasses.seq_nat_prime (n + 1)

/-- **A Sylvester tower is the constant CM point `j = 0`**: under perpetual primality from
`N`, `D_n = −3` for every `n ≥ N`. -/
theorem perpetual_disc_eq_neg_three {N : ℕ} (hpp : AutonomousBranch.PerpetualPrimality N)
    {n : ℕ} (hn : N ≤ n) : disc n = -3 :=
  (disc_eq_neg_three_iff n).mpr (hpp n hn)

/-- Conversely, if the CM point is constant at `ρ` from `N` on, the orbit is a tower. -/
theorem perpetual_of_disc_eq_neg_three {N : ℕ} (h : ∀ n, N ≤ n → disc n = -3) :
    AutonomousBranch.PerpetualPrimality N :=
  fun n hn => (disc_eq_neg_three_iff n).mp (h n hn)

/-- `(C∞)` in CM language: the CM point leaves `ρ` infinitely often. -/
theorem infinitelyManyComposite_iff_disc_ne_neg_three_io :
    AutonomousBranch.InfinitelyManyComposite ↔ ∀ N, ∃ n, N ≤ n ∧ disc n ≠ -3 := by
  unfold AutonomousBranch.InfinitelyManyComposite
  constructor
  · rintro h N
    obtain ⟨n, hn, hc⟩ := h N
    exact ⟨n, hn, fun e => hc ((disc_eq_neg_three_iff n).mp e)⟩
  · rintro h N
    obtain ⟨n, hn, hd⟩ := h N
    exact ⟨n, hn, fun e => hd ((disc_eq_neg_three_iff n).mpr e)⟩

/-- **A confined stage is a point of the Hecke orbit of `ρ`**: `D_n = −3 s²`, the order
`ℤ[s ω]` of conductor `|s|` in `ℚ(√−3)`, `j`-invariant `0`.  (This is `Confinement.Confined`
by definition; recorded here to fix the dictionary.) -/
theorem confined_iff_disc_eq_neg_three_mul_sq (n : ℕ) :
    Confinement.Confined n ↔ ∃ s : ℤ, disc n = -3 * s ^ 2 := Iff.rfl

/-- The conductor of a confined stage is odd and `4 c_n = 3 s² + 1`. -/
theorem four_cofactor_of_confined {n : ℕ} {s : ℤ} (h : disc n = -3 * s ^ 2) :
    4 * (cofactor n : ℤ) = 3 * s ^ 2 + 1 := by
  unfold disc at h; linarith

/-! ## The class-group reading of MC -/

/-- Every prime other than `2` and `3` that appears does so as `seq (n + 2)` for some `n`, i.e.
as the least prime factor of `E_{n+1} = Q_n(−1, p_{n+1})`. -/
theorem exists_eq_seq_add_two_of_mem {q : ℕ} (h2 : q ≠ 2) (h3 : q ≠ 3)
    (h : ∃ k, Mullin.seq k = q) : ∃ n, Mullin.seq (n + 2) = q := by
  obtain ⟨k, hk⟩ := h
  rcases k with _ | _ | n
  · exact absurd (by rw [← hk]; exact seq_zero) h2
  · exact absurd (by rw [← hk]; exact seq_one) h3
  · exact ⟨n, hk⟩

/-- **MC in class-group language.**  For every prime `q ≥ 5` there is a stage `n` at which
`q` is the least prime factor of `E_{n+1} = Q_n(−1, p_{n+1})` — the least norm among the prime
ideals in the principal relation `(p_{n+1} ω_n − 1) = ∏ 𝔮_i` of the order of discriminant
`D_n` — and, whenever `q < c_n`, the ideal of norm `q` is non-principal.

Note (2026-11-10): only the first conjunct uses MC.  The second, `q ∣ E_{n+1}`, follows from
the first (`seq (n + 2)` is the least prime factor of `E_{n+1}`), and the third is
`not_represents_of_lt`, which holds for every integer below `c_n` with no reference to `q`
being prime, to the sequence, or to MC.  So the content of this theorem is
"MC ⟹ every prime `q ≥ 5` is `seq (n + 2)` for some `n`"
(`exists_eq_seq_add_two_of_mem`), dressed in the vocabulary of the form; the "non-principal"
reading is subject to the caveats at `represents_pow_imp_le` (it is literal only for `q`
unramified and prime to the conductor of the order of discriminant `D_n`). -/
theorem mullin_implies_nonprincipal_least_factor (hmc : MullinConjecture) {q : ℕ}
    (hq : q.Prime) (h2 : q ≠ 2) (h3 : q ≠ 3) :
    ∃ n, Mullin.seq (n + 2) = q ∧ (q : ℤ) ∣ ((prod (n + 1) + 1 : ℕ) : ℤ) ∧
      ((q : ℤ) < cofactor n → ¬ Represents (cofactor n) q) := by
  obtain ⟨n, hn⟩ := exists_eq_seq_add_two_of_mem h2 h3
    (hmc q ((MullinGroup.isPrime_iff_natPrime q).mpr hq))
  refine ⟨n, hn, ?_, fun hlt => not_represents_of_lt (by exact_mod_cast cofactor_pos n) hlt⟩
  rw [← hn]
  exact_mod_cast seq_succ_dvd_euclid (n + 1)

end CMPoint
