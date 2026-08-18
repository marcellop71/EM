import EM.Population.AlmostAllDensity
import EM.Ensemble.WeylChain

/-!
# The growing-range form of the seed-average law, and the shape of what is missing

Session 317 (2026-08-20).  Three short results placed by **analogy** with problems of the
same shape (see `docs/analysis/analogy_map_2026-08-20.md`).

## 1. Growing-range simultaneity (the Tao–Collatz shape)

The finite-union law `AlmostAllDensity.finite_simultaneous_density` fixes a finite set of
primes *before* the scale `X`.  Its analogue for the Collatz map is Tao's theorem
"almost all orbits attain almost bounded values": not the per-orbit statement, not the
*bounded* statement, but a bound `f(N)` that is allowed to grow.  The same shape is available
here and, because the per-range density is exactly `0` (not merely small), a diagonal argument
is enough:

* `growing_range_density` — there are nondecreasing `Q N : ℕ → ℕ` with `Q → ∞` such that for
  every `X ≥ X₀` the seeds `m ≤ X` which, for some prime `q ≤ Q X` with `q ∤ m`, fail to
  select `q` within `N X` steps number at most `X / (Q X + 1)`;
* `seed_range_never_density` — the seed-dependent form: the seeds `m` that never select some
  prime `q ≤ Q m`, `q ∤ m`, have natural density `0`.

**Scope.**  Population only; `Q` is *ineffective* (its growth is governed by the Karamata
threshold of `LemmaD`, (K2) of the §G scoping), and nothing here constrains any single seed.
The analogy also says what the next honest target is: an *effective* `Q`, which is the
Mertens-in-APs-with-`O(1)` question, not a new idea about the dynamics.

## 2. `GenMC` is invariant under the greedy map

`T m = m · minFac (m+1) = genProd m 1`.  The orbit of `T m` is the tail of the orbit of `m`,
and the primes dividing `T m` are those dividing `m` together with the first multiplier, so
`GenMullinConjecture (genProd m M) ↔ GenMullinConjecture m` for every `M`
(`genMC_genProd_iff`), and likewise for the per-prime failure sets (`misses_genProd_iff`).
This is the only coupling between seeds the project owns.  By analogy with Heath-Brown's
unconditional Artin theorem — where failures of *different bases at the same prime* are
coupled through `(ℤ/p)^×` and a sieve turns "almost all" into "all but two" — the missing
ingredient for any existence statement `∃ m, GenMullinConjecture m` would be a coupling of
failures across *distinct `T`-orbits*.  None is visible; `T`-invariance alone gives nothing,
because the `T`-orbit of `2` has density `0`.

## 3. The §G input "(N2)" as written is an orbit statement

`docs/analysis/simultaneous_in_q_scoping.md` §2.5 names the missing input for the
simultaneous-in-`q` law as

> (N2) for every `δ` a `Q` with `#{m ≤ X : ∃ q > Q, m misses q} ≤ δ X` **for all `X`**.

"For all `X`" is fatal: at `X = m` with `δ < 1/m` the bound forces the seed `m` itself to miss
no prime `> Q`.  So (N2) implies that **every** seed misses only finitely many of the primes
coprime to it (`scaleUniformTail_cofinite`), in particular that the Euclid–Mullin sequence
contains every sufficiently large prime (`scaleUniformTail_cofinite_mc`).  That is far beyond
MC's known floor (it implies RD, (S), (C∞)).  The correct input has a threshold `X₀(δ)`:

> (N2′) for every `δ` there are `Q` and `X₀` with the bound for all `X ≥ X₀`,

and (N2′) together with `finite_simultaneous_density` gives §G.  (N2′) concerns, at scale `X`,
the primes `q > X` — for which the seeds `m ≤ X` are `X` distinct points of `ℤ/q` and no
period `M ≤ X` sees the event — so it is population-blind in exactly the sense of #90.
Recorded as dead end #176.
-/

noncomputable section
open Classical Filter

namespace GrowingRange

/-! ## 1. Growing-range simultaneity -/

/-- The seeds `m ∈ [1, X]` which, for some prime `q ≤ K` not dividing `m`, fail to select `q`
within the first `n` steps of their greedy orbit. -/
def badSet (X K n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter
    (fun m => ∃ q, q ≤ K ∧ q.Prime ∧ ¬ q ∣ m ∧ ¬ ∃ j < n, genSeq m j = q)

theorem badSet_mono_range {X K K' n : ℕ} (h : K ≤ K') : badSet X K n ⊆ badSet X K' n := by
  intro m hm
  simp only [badSet, Finset.mem_filter] at hm ⊢
  obtain ⟨hI, q, hqK, hq⟩ := hm
  exact ⟨hI, q, le_trans hqK h, hq⟩

theorem badSet_anti_horizon {X K n n' : ℕ} (h : n ≤ n') : badSet X K n' ⊆ badSet X K n := by
  intro m hm
  simp only [badSet, Finset.mem_filter] at hm ⊢
  obtain ⟨hI, q, hqK, hqp, hqm, hcap⟩ := hm
  refine ⟨hI, q, hqK, hqp, hqm, ?_⟩
  rintro ⟨j, hj, hjq⟩
  exact hcap ⟨j, lt_of_lt_of_le hj h, hjq⟩

/-- The per-range input: for every range `K` there is a horizon and a threshold beyond which
the bad set has density `≤ 1/(K+1)`.  Direct from `finite_simultaneous_density` applied to
the primes `≤ K`. -/
theorem per_range (K : ℕ) : ∃ n X₀ : ℕ, ∀ X, X₀ ≤ X →
    ((badSet X K n).card : ℝ) ≤ (X : ℝ) / ((K : ℝ) + 1) := by
  have hε : (0 : ℝ) < 1 / ((K : ℝ) + 1) := by positivity
  obtain ⟨n, X₀, h⟩ := AlmostAllDensity.finite_simultaneous_density
    ((Finset.range (K + 1)).filter Nat.Prime) (fun q hq => (Finset.mem_filter.mp hq).2) hε
  refine ⟨n, X₀, fun X hX => ?_⟩
  have h' := h X hX
  have hset : badSet X K n = (Finset.Icc 1 X).filter
      (fun m => ∃ q ∈ (Finset.range (K + 1)).filter Nat.Prime,
        ¬ q ∣ m ∧ ¬ ∃ j < n, genSeq m j = q) := by
    ext m
    simp only [badSet, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hI, q, hqK, hqp, hq⟩
      exact ⟨hI, q, ⟨by omega, hqp⟩, hq⟩
    · rintro ⟨hI, q, ⟨hqK, hqp⟩, hq⟩
      exact ⟨hI, q, by omega, hqp, hq⟩
  rw [hset]
  have hK : (1 : ℝ) / ((K : ℝ) + 1) * (X : ℝ) = (X : ℝ) / ((K : ℝ) + 1) := by ring
  rw [← hK]
  refine le_trans (le_of_eq ?_) h'
  congr 1
  exact Finset.card_bij (fun m _ => m) (fun m hm => by simpa using hm)
    (fun _ _ _ _ h => h) (fun m hm => ⟨m, by simpa using hm, rfl⟩)

/-- **Growing-range simultaneity.**  There are nondecreasing `Q N : ℕ → ℕ` with `Q → ∞`
(and `Q ≤ N`) such that, for all `X ≥ X₀`, the seeds `m ≤ X` missing some prime
`q ≤ Q X`, `q ∤ m`, within `N X` steps number at most `X / (Q X + 1)`.

*Proof.*  Choose per-range horizons and thresholds (`per_range`), make them nondecreasing by
running maxima, and let `Q X` be the largest range whose threshold is `≤ X`.

**Scope.**  Population, unconditional, `Q` ineffective.  Nothing is asserted about any
individual seed. -/
theorem growing_range_density : ∃ Q N : ℕ → ℕ, Monotone Q ∧ Monotone N ∧
    Tendsto Q atTop atTop ∧ (∀ X, Q X ≤ N X) ∧
    ∃ X₀ : ℕ, ∀ X, X₀ ≤ X →
      ((badSet X (Q X) (N X)).card : ℝ) ≤ (X : ℝ) / ((Q X : ℝ) + 1) := by
  choose n B hnB using per_range
  -- running maxima, dominating the index so that both tend to infinity
  let B' : ℕ → ℕ := fun K => (Finset.range (K + 1)).sup B ⊔ K
  let n' : ℕ → ℕ := fun K => (Finset.range (K + 1)).sup n ⊔ K
  have hB'mono : Monotone B' := fun K K' h =>
    sup_le_sup (Finset.sup_mono (Finset.range_mono (Nat.succ_le_succ h))) h
  have hn'mono : Monotone n' := fun K K' h =>
    sup_le_sup (Finset.sup_mono (Finset.range_mono (Nat.succ_le_succ h))) h
  have hBB' : ∀ K, B K ≤ B' K := fun K =>
    le_trans (Finset.le_sup (f := B) (Finset.mem_range.mpr (Nat.lt_succ_self K))) le_sup_left
  have hnn' : ∀ K, n K ≤ n' K := fun K =>
    le_trans (Finset.le_sup (f := n) (Finset.mem_range.mpr (Nat.lt_succ_self K))) le_sup_left
  have hKB' : ∀ K, K ≤ B' K := fun K => le_sup_right
  have hKn' : ∀ K, K ≤ n' K := fun K => le_sup_right
  -- the admissible ranges at scale `X`, and the largest of them
  let S : ℕ → Finset ℕ := fun X => (Finset.range (X + 1)).filter (fun K => B' K ≤ X)
  let Q : ℕ → ℕ := fun X => (S X).sup id
  have hSmono : ∀ {X X'}, X ≤ X' → S X ⊆ S X' := by
    intro X X' h K hK
    simp only [S, Finset.mem_filter, Finset.mem_range] at hK ⊢
    exact ⟨by omega, le_trans hK.2 h⟩
  have hQmono : Monotone Q := fun X X' h => Finset.sup_mono (hSmono h)
  have hmemS : ∀ K X, B' K ≤ X → K ∈ S X := by
    intro K X h
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := hKB' K; omega, h⟩
  have hQge : ∀ K X, B' K ≤ X → K ≤ Q X := fun K X h =>
    Finset.le_sup (f := id) (hmemS K X h)
  have hQtend : Tendsto Q atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun K => ⟨B' K, fun X hX => hQge K X hX⟩
  -- at scale `X ≥ B' 0` the maximum is attained, so its threshold is `≤ X`
  have hQadm : ∀ X, B' 0 ≤ X → B' (Q X) ≤ X := by
    intro X hX
    obtain ⟨K, hKS, hK⟩ := Finset.exists_mem_eq_sup (S X) ⟨0, hmemS 0 X hX⟩ id
    have hK' : Q X = K := hK
    rw [hK']
    exact (Finset.mem_filter.mp hKS).2
  refine ⟨Q, fun X => n' (Q X), hQmono, fun X X' h => hn'mono (hQmono h), hQtend,
    fun X => hKn' (Q X), B' 0, fun X hX => ?_⟩
  have hthr : B (Q X) ≤ X := le_trans (hBB' (Q X)) (hQadm X hX)
  have hbound := hnB (Q X) X hthr
  have hsub : badSet X (Q X) (n' (Q X)) ⊆ badSet X (Q X) (n (Q X)) :=
    badSet_anti_horizon (hnn' (Q X))
  calc ((badSet X (Q X) (n' (Q X))).card : ℝ)
      ≤ ((badSet X (Q X) (n (Q X))).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ _ := hbound

/-- The `ε`-form of `growing_range_density`: the bad set at range `Q X`, horizon `N X` has
natural density `0`. -/
theorem growing_range_density_eps : ∃ Q N : ℕ → ℕ, Monotone Q ∧ Monotone N ∧
    Tendsto Q atTop atTop ∧ (∀ X, Q X ≤ N X) ∧
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X, X₀ ≤ X →
      ((badSet X (Q X) (N X)).card : ℝ) ≤ ε * (X : ℝ) := by
  obtain ⟨Q, N, hQ, hN, hQt, hQN, X₀, h⟩ := growing_range_density
  refine ⟨Q, N, hQ, hN, hQt, hQN, fun ε hε => ?_⟩
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
  obtain ⟨X₁, hX₁⟩ := tendsto_atTop_atTop.mp hQt K
  refine ⟨max X₀ X₁, fun X hX => ?_⟩
  have h1 := h X (le_trans (le_max_left _ _) hX)
  have h2 : K ≤ Q X := hX₁ X (le_trans (le_max_right _ _) hX)
  have hQpos : (0 : ℝ) < (Q X : ℝ) + 1 := by positivity
  calc ((badSet X (Q X) (N X)).card : ℝ) ≤ (X : ℝ) / ((Q X : ℝ) + 1) := h1
    _ = 1 / ((Q X : ℝ) + 1) * (X : ℝ) := by ring
    _ ≤ 1 / ((K : ℝ) + 1) * (X : ℝ) := by
        gcongr
    _ ≤ ε * (X : ℝ) := by gcongr

/-- **Seed-dependent growing range (never-capture form).**  There is a nondecreasing
`Q → ∞` such that the seeds `m` which *never* select some prime `q ≤ Q m`, `q ∤ m`, have
natural density `0`: almost every seed selects every prime up to `Q m` coprime to it.

This is the exact analogue of Tao's "almost all Collatz orbits attain almost bounded values"
(there: a bound `f(N)` growing with the seed; here: a range of primes growing with the seed),
with the difference that `Q` is not arbitrary but one specific, ineffective function.
(A seed-dependent *horizon* `N m` cannot be added: enlarging the horizon shrinks the bad set,
so `N m ≤ N X` points the wrong way; the horizon form is the scale-level
`growing_range_density`.) -/
theorem seed_range_never_density : ∃ Q : ℕ → ℕ, Monotone Q ∧ Tendsto Q atTop atTop ∧
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X, X₀ ≤ X →
      (((Finset.Icc 1 X).filter
        (fun m => ∃ q, q ≤ Q m ∧ q.Prime ∧ ¬ q ∣ m ∧ ∀ j, genSeq m j ≠ q)).card : ℝ)
        ≤ ε * (X : ℝ) := by
  obtain ⟨Q, N, hQ, -, hQt, -, h⟩ := growing_range_density_eps
  refine ⟨Q, hQ, hQt, fun ε hε => ?_⟩
  obtain ⟨X₀, hX₀⟩ := h ε hε
  refine ⟨X₀, fun X hX => le_trans ?_ (hX₀ X hX)⟩
  have hsub : (Finset.Icc 1 X).filter
      (fun m => ∃ q, q ≤ Q m ∧ q.Prime ∧ ¬ q ∣ m ∧ ∀ j, genSeq m j ≠ q) ⊆
      badSet X (Q X) (N X) := by
    intro m hm
    simp only [badSet, Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    obtain ⟨hI, q, hqQ, hqp, hqm, hnever⟩ := hm
    exact ⟨hI, q, le_trans hqQ (hQ hI.2), hqp, hqm, fun ⟨j, _, hj⟩ => hnever j hj⟩
  exact_mod_cast Finset.card_le_card hsub

/-! ## 2. `GenMC` is invariant under the greedy map -/

/-- The seed `m` misses the prime `q`: `q ∤ m` and `q` is never selected. -/
def Misses (q m : ℕ) : Prop := ¬ q ∣ m ∧ ∀ k, genSeq m k ≠ q

/-- One greedy step preserves the missed-prime relation. -/
theorem misses_genProd_one_iff {q m : ℕ} (hq : q.Prime) :
    Misses q (genProd m 1) ↔ Misses q m := by
  have hstep : genProd m 1 = m * genSeq m 0 := rfl
  have hdvd0 : genSeq m 0 ∣ genProd m 1 := ⟨m, by rw [hstep, mul_comm]⟩
  constructor
  · rintro ⟨hndvd, hnever⟩
    refine ⟨fun h => hndvd (h.trans ⟨genSeq m 0, hstep⟩), fun k hk => ?_⟩
    cases k with
    | zero => exact hndvd (hk ▸ hdvd0)
    | succ k =>
      have := hnever k
      rw [genSeq_restart, show 1 + k = k + 1 by omega] at this
      exact this hk
  · rintro ⟨hndvd, hnever⟩
    refine ⟨fun h => ?_, fun k hk => ?_⟩
    · have hm0 : m ≠ 0 := fun h0 => hndvd (h0 ▸ dvd_zero q)
      rw [hstep, hq.dvd_mul] at h
      rcases h with h | h
      · exact hndvd h
      · exact hnever 0 ((Nat.prime_dvd_prime_iff_eq hq (Nat.minFac_prime (by
          show m + 1 ≠ 1; omega))).mp h).symm
    · rw [genSeq_restart] at hk
      exact hnever _ hk

/-- Iterating: the missed-prime relation is invariant along the whole forward orbit. -/
theorem misses_genProd_iff {q m : ℕ} (hq : q.Prime) (M : ℕ) :
    Misses q (genProd m M) ↔ Misses q m := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [← ih, ← misses_genProd_one_iff hq (m := genProd m M), genProd_restart]

/-- **`GenMC` is invariant under the greedy map**: `GenMullinConjecture (genProd m M) ↔
GenMullinConjecture m`.  The failure set `{m | ¬ GenMullinConjecture m}` is therefore a union
of full `T`-orbits, `T m = m · minFac (m+1)`. -/
theorem genMC_genProd_iff (m M : ℕ) :
    GenMullinConjecture (genProd m M) ↔ GenMullinConjecture m := by
  have key : ∀ s : ℕ, GenMullinConjecture s ↔ ∀ q, q.Prime → ¬ Misses q s := by
    intro s
    unfold GenMullinConjecture Misses
    constructor
    · intro h q hq ⟨hndvd, hnever⟩
      obtain ⟨k, hk⟩ := h q hq hndvd
      exact hnever k hk
    · intro h q hq hndvd
      by_contra hne
      exact h q hq ⟨hndvd, fun k hk => hne ⟨k, hk⟩⟩
  rw [key, key]
  exact forall_congr' fun q => imp_congr_right fun hq => not_congr (misses_genProd_iff hq M)

/-! ## 3. "(N2)" as written is an orbit statement -/

/-- The scale-uniform tail bound named "(N2)" in the §G scoping: for every `δ > 0` there is a
`Q` such that **for all `X`**, the seeds `m ≤ X` missing some prime `q > Q` coprime to `m`
number at most `δ X`. -/
def ScaleUniformTail : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ Q : ℕ, ∀ X : ℕ,
    (((Finset.Icc 1 X).filter (fun m => ∃ q, Q < q ∧ Misses q m)).card : ℝ) ≤ δ * (X : ℝ)

/-- **(N2) forces every seed to miss only finitely many primes.**  Taking `X = m` and
`δ < 1/m` leaves no room for `m` itself in the bad set. -/
theorem scaleUniformTail_cofinite (h : ScaleUniformTail) (m : ℕ) (hm : 1 ≤ m) :
    ∃ Q : ℕ, ∀ q, Q < q → ¬ Misses q m := by
  have hδ : (0 : ℝ) < 1 / (2 * (m : ℝ)) := by positivity
  obtain ⟨Q, hQ⟩ := h _ hδ
  refine ⟨Q, fun q hq hmiss => ?_⟩
  have hmem : m ∈ (Finset.Icc 1 m).filter (fun m => ∃ q, Q < q ∧ Misses q m) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm, le_rfl⟩, q, hq, hmiss⟩
  have hcard : (1 : ℝ) ≤ (((Finset.Icc 1 m).filter
      (fun m => ∃ q, Q < q ∧ Misses q m)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨m, hmem⟩
  have hbound := hQ m
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have : (1 : ℝ) ≤ 1 / (2 * (m : ℝ)) * (m : ℝ) := le_trans hcard hbound
  have h2 : 1 / (2 * (m : ℝ)) * (m : ℝ) = 1 / 2 := by field_simp
  linarith

/-- **(N2) implies that the Euclid–Mullin sequence contains every sufficiently large prime.**
So the "scale-uniform tail bound" is not a population statement at all: it contains a
cofinite form of MC for the orbit of `2`.  The honest §G input carries a threshold `X₀(δ)`. -/
theorem scaleUniformTail_cofinite_mc (h : ScaleUniformTail) :
    ∃ Q : ℕ, ∀ q, Q < q → q.Prime → ∃ k, Mullin.seq k = q := by
  obtain ⟨Q, hQ⟩ := scaleUniformTail_cofinite h 2 (by norm_num)
  refine ⟨Q, fun q hq hqp => ?_⟩
  by_cases h2 : q ∣ 2
  · exact ⟨0, by rw [Mullin.seq_zero]; exact ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp h2).symm⟩
  · have hnm : ¬ Misses q 2 := hQ q hq
    by_contra hno
    exact hnm ⟨h2, fun k hk => hno ⟨k + 1, by rw [← genSeq_two_eq_seq_succ, hk]⟩⟩

end GrowingRange

end
