import EM.Population.HeadDynamics
import EM.Population.HittingSetStructure
import EM.Population.UniformFreezing
import EM.Population.BackwardOrbit

/-!
# Second chances: primes that are hit, outranked, and captured later

Session 322 (2026-10-25).  Memo: `docs/analysis/second_chance_2026-10-25.md` (namespace `SecondChances`).

A prime `r` is **hit** at stage `n` when `r ∣ E_n = P_n + 1`.  It is **captured** at stage
`m + 1` when `r = seq (m+1) = lpf E_m`.  The hitting-set theory of
`EM/Population/HittingSetStructure.lean` studies hits of *missed* primes: every such hit is
shielded by a smaller prime (the guardian), and a missed prime is hit only finitely often.
This file studies the mirror image: a prime that is hit at some stage `n`, outranked by a
smaller factor, and nevertheless captured at a strictly later stage.  We call this a
**second chance** (`SecondChance r`).

The example in the orbit of `2` is `r = 139`: `E_3 = 1807 = 13 · 139`, the rule takes `13`, and
`139 = seq 9` is captured six stages later, because `13 · 53 · 5 · 6221671 · 38709183810571 ≡ 1
(mod 139)` (`secondChance_window` is the general form of this congruence).

## Main results

* `missingFinite_implies_secondChance_io` — **if only finitely many primes are missed, then
  infinitely many primes `≡ 3 (mod 4)` get a second chance.**  Mechanism: all but finitely
  many primes `≡ 1 (mod 4)` are captured (Dirichlet); at such a capture stage the cofactor is
  `≡ 3 (mod 4)` and carries a prime factor `r ≡ 3 (mod 4)` other than the multiplier; `r` is
  hit now and, being captured eventually, is captured later.
* `mc_implies_secondChance_io` — the same under MC.  So **MC cannot hold "on first sight"**:
  `FirstHitCapture` (only finitely many second chances) refutes `MissingFinite` and MC
  (`not_missingFinite_of_firstHitCapture`, `not_mc_of_firstHitCapture`).
* `secondChance_window` — a second chance is a *return of the multiplier product to the
  identity*: `seq (n+1) ⋯ seq m ≡ 1 (mod r)` with `r ∣ E_n` and `seq (m+1) = r`.
* `exists_window_prod_eq_one` — pigeonhole (the Davenport constant of a cyclic group) gives,
  for every missed `r` and every start `a`, a window of length `< r` inside `[a, a + r)` on
  which the multiplier product is `≡ 1 (mod r)`.  Such windows are free; what MC needs is a
  window **anchored** at a hit, and that is the whole difficulty (Dead End #90 in this
  language).
* `euclid_eq_phi6_iter_of_prime_run`, `secondChance_tower_criterion` — along a run of prime
  Euclid numbers after a hit of `r` at stage `n`, the Euclid numbers mod `r` follow the
  autonomous Sylvester map `Φ₆` from the value `1 − seq (n+1)`; a second chance inside the run
  is therefore a `PreZero` event for that residue.
* `not_classInfinitude_three_mod_four_implies_missing_io` — if the multipliers are eventually
  `≡ 1 (mod 4)`, infinitely many primes `≡ 3 (mod 4)` are missed; hence
  `missingFinite_implies_classInfinitude_three_mod_four`.

Everything here is unconditional arithmetic of the greedy orbit plus Dirichlet's theorem.
-/

open Mullin Euclid EuclidClasses HeadDynamics
open scoped Classical

namespace SecondChances

/-! ## 1. Hits of captured primes are finite -/

/-- A captured prime never divides a later Euclid number: `seq k ∣ prod n` for `k ≤ n`. -/
theorem not_dvd_euclid_of_captured {k n : ℕ} (hkn : k ≤ n) : ¬ seq k ∣ prod n + 1 := by
  intro h
  have h1 : seq k ∣ 1 := (Nat.dvd_add_right (seq_dvd_prod k n hkn)).mp h
  exact (seq_nat_prime k).one_lt.ne' (Nat.dvd_one.mp h1)

/-- A hit of a captured prime `seq k` happens strictly before stage `k`. -/
theorem lt_of_mem_hittingSet_captured {k n : ℕ} (h : n ∈ HittingSet (seq k)) : n < k := by
  by_contra hnk
  exact not_dvd_euclid_of_captured (Nat.le_of_not_lt hnk) h

/-- The hitting set of a captured prime is finite. -/
theorem hittingSet_finite_of_captured {r : ℕ} (h : r ∈ Set.range seq) :
    (HittingSet r).Finite := by
  obtain ⟨k, rfl⟩ := h
  exact (Set.finite_Iio k).subset fun n hn => lt_of_mem_hittingSet_captured hn

/-- **Every prime has a finite hitting set**: captured primes by `not_dvd_euclid_of_captured`,
missed primes by `hittingSet_finite` (the guardian argument). -/
theorem hittingSet_finite_of_prime {r : ℕ} (hr : r.Prime) : (HittingSet r).Finite := by
  by_cases h : ∀ k, seq k ≠ r
  · exact hittingSet_finite ⟨hr, h⟩
  · push Not at h
    exact hittingSet_finite_of_captured h

/-- A finite set of primes is hit only finitely often in total. -/
theorem exists_stage_no_hit {S : Set ℕ} (hS : S.Finite) :
    ∃ N₀, ∀ n, N₀ ≤ n → ∀ r ∈ S, r.Prime → ¬ r ∣ prod n + 1 := by
  have hT : (⋃ r ∈ {r ∈ S | r.Prime}, HittingSet r).Finite := by
    refine Set.Finite.biUnion (hS.subset fun _ h => h.1) fun r hr => ?_
    exact hittingSet_finite_of_prime hr.2
  obtain ⟨B, hB⟩ := hT.bddAbove
  refine ⟨B + 1, fun n hn r hrS hr hdvd => ?_⟩
  have : n ∈ ⋃ r ∈ {r ∈ S | r.Prime}, HittingSet r :=
    Set.mem_biUnion (x := r) ⟨hrS, hr⟩ hdvd
  have := hB this
  omega

/-! ## 2. Second chances -/

/-- **Second chance**: `r` divides the Euclid number `E_n` at some stage `n` (where it is
outranked by a smaller factor) and is captured at a strictly later stage `m + 1`. -/
def SecondChance (r : ℕ) : Prop := ∃ n m, n < m ∧ r ∣ prod n + 1 ∧ seq (m + 1) = r

/-- A second-chance prime is a captured prime. -/
theorem mem_range_of_secondChance {r : ℕ} (h : SecondChance r) : r ∈ Set.range seq := by
  obtain ⟨n, m, _, _, hm⟩ := h
  exact ⟨m + 1, hm⟩

/-- A prime that divides `E_n`, is not the multiplier chosen at stage `n`, and is captured at
all, is captured strictly later: a second chance. -/
theorem secondChance_of_dvd_of_captured {r n : ℕ} (hdvd : r ∣ prod n + 1)
    (hne : r ≠ seq (n + 1)) (hcap : r ∈ Set.range seq) : SecondChance r := by
  obtain ⟨j, rfl⟩ := hcap
  have hj : n < j := lt_of_mem_hittingSet_captured hdvd
  have hj' : n + 1 < j := by
    rcases Nat.lt_or_ge (n + 1) j with h | h
    · exact h
    · exact absurd (by omega : j = n + 1) (fun e => hne (by rw [e]))
  exact ⟨n, j - 1, by omega, hdvd, by rw [show j - 1 + 1 = j by omega]⟩

/-- A capture is itself a hit: `seq (m+1) ∣ E_m`. -/
theorem seq_succ_dvd_euclid (m : ℕ) : seq (m + 1) ∣ prod m + 1 := by
  rw [seq_succ]; exact minFac_dvd _ (by have := prod_ge_two m; omega)

/-- **A second chance is a return of the multiplier product to the identity.**  With `r ∣ E_n`
and `r = seq (m+1)`, the product `seq (n+1) ⋯ seq m` is `≡ 1 (mod r)`. -/
theorem secondChance_window {r : ℕ} (h : SecondChance r) :
    ∃ n m, n < m ∧ r ∣ prod n + 1 ∧ seq (m + 1) = r ∧
      ((∏ k ∈ Finset.Ioc n m, seq k : ℕ) : ZMod r) = 1 := by
  obtain ⟨n, m, hnm, hdvd, hm⟩ := h
  refine ⟨n, m, hnm, hdvd, hm, ?_⟩
  rw [← dvd_euclid_iff_prod_mul_eq_one hdvd hnm.le, ← hm]
  exact seq_succ_dvd_euclid m

/-- `SecondChance r` is equivalent to: `r` is captured and hit at least twice (the capture
stage is one hit, an earlier stage is another). -/
theorem secondChance_iff_two_hits {r : ℕ} :
    SecondChance r ↔ r ∈ Set.range seq ∧ ∃ n n', n < n' ∧ n ∈ HittingSet r ∧ n' ∈ HittingSet r := by
  constructor
  · rintro ⟨n, m, hnm, hdvd, hm⟩
    exact ⟨⟨m + 1, hm⟩, n, m, hnm, hdvd, hm ▸ seq_succ_dvd_euclid m⟩
  · rintro ⟨hcap, n, n', hnn', hn, hn'⟩
    obtain ⟨j, rfl⟩ := hcap
    have := lt_of_mem_hittingSet_captured hn'
    exact ⟨n, j - 1, by omega, hn, by rw [show j - 1 + 1 = j by omega]⟩

/-! ## 3. The `3 (mod 4)` supply -/

/-- At a stage whose multiplier is `≡ 1 (mod 4)`, the Euclid number (which is `≡ 3 (mod 4)`)
has a prime factor `≡ 3 (mod 4)` different from the multiplier. -/
theorem exists_cofactor_prime_three_mod_four {n : ℕ} (h1 : seq (n + 1) % 4 = 1) :
    ∃ r, r.Prime ∧ r ∣ prod n + 1 ∧ r % 4 = 3 ∧ r ≠ seq (n + 1) := by
  obtain ⟨r, hr, hdvd, hr3⟩ := exists_prime_dvd_euclid_three_mod_four n
  exact ⟨r, hr, hdvd, hr3, fun e => by rw [e] at hr3; omega⟩

/-- Infinitely many primes `≡ 1 (mod 4)` are captured when only finitely many primes are
missed, and they are captured at arbitrarily late stages. -/
theorem exists_capture_one_mod_four_ge (h : MissingFinite) (N₀ : ℕ) :
    ∃ k, N₀ ≤ k ∧ seq (k + 1) % 4 = 1 := by
  obtain ⟨B₁, hB₁⟩ := h.bddAbove
  set B₂ : ℕ := (Finset.range (N₀ + 2)).sup seq with hB₂
  obtain ⟨q, hq, hqp, hq4⟩ :=
    UniformFreezing.exists_prime_gt_mod (M := 4) (a := 1) (by norm_num) (by norm_num)
      (max B₁ B₂)
  have hq1 : q % 4 = 1 := by simpa using hq4
  -- `q` is not missed, so it is captured at some stage `j`
  have hcap : ∃ j, seq j = q := by
    by_contra hno
    push Not at hno
    have : q ∈ MissingPrimes := ⟨hqp, hno⟩
    have := hB₁ this
    omega
  obtain ⟨j, hj⟩ := hcap
  -- the stage is late because `q` exceeds every early term
  have hjN : N₀ + 2 ≤ j := by
    by_contra hlt
    push Not at hlt
    have : seq j ≤ B₂ := Finset.le_sup (f := seq) (Finset.mem_range.mpr hlt)
    omega
  exact ⟨j - 1, by omega, by rw [show j - 1 + 1 = j by omega, hj, hq1]⟩

/-- **Main theorem.  If only finitely many primes are missed, infinitely many primes
`≡ 3 (mod 4)` get a second chance**: they divide a Euclid number, are outranked by a smaller
factor, and are captured at a later stage. -/
theorem missingFinite_implies_secondChance_io (h : MissingFinite) (N : ℕ) :
    ∃ r, N ≤ r ∧ r.Prime ∧ r % 4 = 3 ∧ SecondChance r := by
  -- primes that are missed or small are hit only finitely often
  obtain ⟨N₀, hN₀⟩ := exists_stage_no_hit (S := MissingPrimes ∪ Set.Iio N)
    (h.union (Set.finite_Iio N))
  obtain ⟨k, hk, hk4⟩ := exists_capture_one_mod_four_ge h N₀
  obtain ⟨r, hr, hdvd, hr3, hne⟩ := exists_cofactor_prime_three_mod_four hk4
  have hrS : r ∉ MissingPrimes ∪ Set.Iio N := fun hmem => hN₀ k hk r hmem hr hdvd
  have hrN : N ≤ r := by
    by_contra hlt
    exact hrS (Or.inr (Set.mem_Iio.mpr (by omega)))
  have hcap : r ∈ Set.range seq := by
    by_contra hno
    exact hrS (Or.inl ⟨hr, fun k hk => hno ⟨k, hk⟩⟩)
  exact ⟨r, hrN, hr, hr3, secondChance_of_dvd_of_captured hdvd hne hcap⟩

/-- **MC forces infinitely many second chances** (among primes `≡ 3 (mod 4)`). -/
theorem mc_implies_secondChance_io (hmc : MullinConjecture) (N : ℕ) :
    ∃ r, N ≤ r ∧ r.Prime ∧ r % 4 = 3 ∧ SecondChance r :=
  missingFinite_implies_secondChance_io (mc_implies_missing_finite hmc) N

/-- The set of second-chance primes is infinite under `MissingFinite`. -/
theorem secondChance_infinite_of_missingFinite (h : MissingFinite) :
    {r | SecondChance r}.Infinite := by
  refine Set.infinite_of_not_bddAbove fun ⟨B, hB⟩ => ?_
  obtain ⟨r, hr, _, _, hsc⟩ := missingFinite_implies_secondChance_io h (B + 1)
  have := hB hsc
  omega

/-! ## 4. First-hit capture refutes MC -/

/-- **First-hit capture**: all but finitely many captured primes are captured at their first
hit, i.e. only finitely many primes get a second chance. -/
def FirstHitCapture : Prop := {r | SecondChance r}.Finite

theorem not_missingFinite_of_firstHitCapture (h : FirstHitCapture) : ¬ MissingFinite :=
  fun hfin => secondChance_infinite_of_missingFinite hfin h

/-- **MC is incompatible with capture on first sight.** -/
theorem not_mc_of_firstHitCapture (h : FirstHitCapture) : ¬ MullinConjecture :=
  fun hmc => not_missingFinite_of_firstHitCapture h (mc_implies_missing_finite hmc)

/-! ## 5. Free windows versus anchored windows -/

/-- **Pigeonhole (Davenport) windows.**  For a missed prime `r` and any start `a`, some window
`(i, j] ⊆ (a, a + r)` has multiplier product `≡ 1 (mod r)`.  Such windows exist for every
missed prime; a second chance needs the window anchored at a hit (`i` with `r ∣ E_i`). -/
theorem exists_window_prod_eq_one {r : ℕ} (hr : r ∈ MissingPrimes) (a : ℕ) :
    ∃ i j, a ≤ i ∧ i < j ∧ j ≤ a + (r - 1) ∧
      ((∏ k ∈ Finset.Ioc i j, seq k : ℕ) : ZMod r) = 1 := by
  have : Fact r.Prime := ⟨hr.1⟩
  -- the walk on `[a, a + r)` takes `r` values among the `r − 1` nonzero residues
  have hmaps : ∀ i ∈ Finset.Icc a (a + (r - 1)),
      ((prod i : ℕ) : ZMod r) ∈ (Finset.univ : Finset (ZMod r)).erase 0 := by
    intro i _
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact missing_not_dvd_prod hr i
  have hcard : ((Finset.univ : Finset (ZMod r)).erase 0).card < (Finset.Icc a (a + (r - 1))).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card, Nat.card_Icc]
    have := hr.1.two_le
    omega
  obtain ⟨i, hi, j, hj, hij, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rw [Finset.mem_Icc] at hi hj
  -- order the collision
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨i, j, hi.1, hlt, hj.2, ?_⟩
    have hunit : ((prod i : ℕ) : ZMod r) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; exact missing_not_dvd_prod hr i
    have h2 : ((prod j : ℕ) : ZMod r) = ((prod i : ℕ) : ZMod r) *
        ((∏ k ∈ Finset.Ioc i j, seq k : ℕ) : ZMod r) := by
      rw [prod_eq_prod_mul_prod_Ioc hlt.le]; push_cast; ring
    rw [← heq] at h2
    exact (mul_right_eq_self₀.mp h2.symm).resolve_right hunit
  · refine ⟨j, i, hj.1, hlt, hi.2, ?_⟩
    have hunit : ((prod j : ℕ) : ZMod r) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; exact missing_not_dvd_prod hr j
    have h2 : ((prod i : ℕ) : ZMod r) = ((prod j : ℕ) : ZMod r) *
        ((∏ k ∈ Finset.Ioc j i, seq k : ℕ) : ZMod r) := by
      rw [prod_eq_prod_mul_prod_Ioc hlt.le]; push_cast; ring
    rw [heq] at h2
    exact (mul_right_eq_self₀.mp h2.symm).resolve_right hunit

/-! ## 6. Second chances along a run of prime Euclid numbers are `Φ₆`-events -/

/-- If `E_j` is prime then `E_{j+1} = Φ₆(E_j)` in any commutative ring. -/
theorem euclid_succ_eq_phi6_of_prime {j : ℕ} (h : Nat.Prime (prod j + 1)) {R : Type*}
    [CommRing R] :
    ((prod (j + 1) + 1 : ℕ) : R) = BackwardOrbit.phi6 ((prod j + 1 : ℕ) : R) := by
  rw [euclid_succ_of_prime h, BackwardOrbit.phi6]; push_cast; ring

/-- Along a run of prime Euclid numbers `E_{n+1}, …, E_{j-1}`, the Euclid number `E_j` is the
`(j − (n+1))`-fold `Φ₆`-iterate of `E_{n+1}`. -/
theorem euclid_eq_phi6_iter_of_prime_run {n j : ℕ} (hnj : n + 1 ≤ j)
    (hrun : ∀ i, n + 1 ≤ i → i < j → Nat.Prime (prod i + 1)) {R : Type*} [CommRing R] :
    ((prod j + 1 : ℕ) : R) = (BackwardOrbit.phi6)^[j - (n + 1)] ((prod (n + 1) + 1 : ℕ) : R) := by
  induction j, hnj using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    rw [show j + 1 - (n + 1) = (j - (n + 1)) + 1 by omega, Function.iterate_succ_apply',
      ← ih (fun i hi hij => hrun i hi (by omega)),
      euclid_succ_eq_phi6_of_prime (hrun j hj (by omega))]

/-- After a hit `r ∣ E_n`, the next Euclid number is `≡ 1 − seq (n+1) (mod r)`. -/
theorem euclid_succ_eq_one_sub_seq_of_dvd {r n : ℕ} (h : r ∣ prod n + 1) :
    ((prod (n + 1) + 1 : ℕ) : ZMod r) = 1 - (seq (n + 1) : ZMod r) := by
  have hPn : ((prod n : ℕ) : ZMod r) = -1 := by
    have := (ZMod.natCast_eq_zero_iff _ _).mpr h
    push_cast at this
    linear_combination this
  rw [prod_succ]; push_cast; rw [hPn]; ring

/-- **Tower criterion for a second chance.**  If `r ∣ E_n` and the Euclid numbers
`E_{n+1}, …, E_{m-1}` are all prime, then `r ∣ E_m` iff the `Φ₆`-orbit of `1 − seq (n+1)`
modulo `r` reaches `0` in exactly `m − (n+1)` steps; in particular the residue
`1 − seq (n+1)` lies in `PreZero r`. -/
theorem secondChance_tower_criterion {r n m : ℕ} (hdvd : r ∣ prod n + 1) (hnm : n + 1 ≤ m)
    (hrun : ∀ i, n + 1 ≤ i → i < m → Nat.Prime (prod i + 1)) :
    r ∣ prod m + 1 ↔
      (BackwardOrbit.phi6)^[m - (n + 1)] (1 - (seq (n + 1) : ZMod r)) = 0 := by
  rw [← ZMod.natCast_eq_zero_iff, euclid_eq_phi6_iter_of_prime_run hnm hrun,
    euclid_succ_eq_one_sub_seq_of_dvd hdvd]

theorem mem_preZero_of_dvd_of_prime_run {r n m : ℕ} (hdvd : r ∣ prod n + 1) (hnm : n + 1 ≤ m)
    (hrun : ∀ i, n + 1 ≤ i → i < m → Nat.Prime (prod i + 1)) (hm : r ∣ prod m + 1) :
    (1 - (seq (n + 1) : ZMod r)) ∈ BackwardOrbit.PreZero r :=
  ⟨m - (n + 1), (secondChance_tower_criterion hdvd hnm hrun).mp hm⟩

/-! ## 7. Eventually `≡ 1 (mod 4)` multipliers leave infinitely many `3 (mod 4)` primes missed -/

/-- Late multipliers are odd primes, so their residue mod `4` is `1` or `3`. -/
theorem seq_succ_mod_four (n : ℕ) : seq (n + 1) % 4 = 1 ∨ seq (n + 1) % 4 = 3 := by
  have hodd := seq_odd (k := n + 1) (by omega)
  rcases hodd with ⟨t, ht⟩
  omega

/-- If the multipliers are eventually `≡ 1 (mod 4)`, every late Euclid number carries a
prime factor `≡ 3 (mod 4)` that is missed forever; infinitely many distinct such primes
occur. -/
theorem not_classInfinitude_three_mod_four_implies_missing_io
    (h : ¬ ClassInfinitude 4 3) (N : ℕ) :
    ∃ r, N ≤ r ∧ r ∈ MissingPrimes ∧ r % 4 = 3 := by
  unfold ClassInfinitude at h
  push Not at h
  obtain ⟨N₁, hN₁⟩ := h
  obtain ⟨N₀, hN₀⟩ := exists_stage_no_hit (S := Set.Iio N) (Set.finite_Iio N)
  set n := max N₀ N₁ with hn
  have h1 : seq (n + 1) % 4 = 1 := by
    rcases seq_succ_mod_four n with h | h
    · exact h
    · exact absurd h (hN₁ (n + 1) (by omega))
  obtain ⟨r, hr, hdvd, hr3, _⟩ := exists_cofactor_prime_three_mod_four h1
  have hmiss : r ∈ MissingPrimes := by
    refine ⟨hr, fun j hj => ?_⟩
    rcases Nat.lt_or_ge n j with hlt | hle
    · have := hN₁ j (by omega); rw [hj] at this; exact this hr3
    · exact not_dvd_euclid_of_captured hle (hj ▸ hdvd)
  refine ⟨r, ?_, hmiss, hr3⟩
  by_contra hlt
  exact hN₀ n (by omega) r (Set.mem_Iio.mpr (by omega)) hr hdvd

/-- **`MissingFinite ⟹ CI(3 mod 4)`.**  (The direct route via Dirichlet is also available:
all but finitely many primes `≡ 3 (mod 4)` are captured.  This proof goes through the
cofactor supply instead, which is the mechanism behind `missingFinite_implies_secondChance_io`.) -/
theorem missingFinite_implies_classInfinitude_three_mod_four (h : MissingFinite) :
    ClassInfinitude 4 3 := by
  by_contra hci
  obtain ⟨B, hB⟩ := h.bddAbove
  obtain ⟨r, hr, hmiss, _⟩ := not_classInfinitude_three_mod_four_implies_missing_io hci (B + 1)
  have := hB hmiss
  omega

end SecondChances
