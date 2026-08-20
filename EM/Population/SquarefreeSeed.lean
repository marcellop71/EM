import EM.Population.AlmostAllDensity
import EM.Ensemble.FirstMoment

/-!
# Every prime is selected by some squarefree seed

Session 318 (2026-08-20).  The question "is every prime `q` hit sooner or later by *some*
Euclid–Mullin sequence started at a squarefree integer?" has a positive, unconditional
answer, and the answer is a corollary of the seed-average law rather than a construction:
almost every seed selects `q`, and squarefree seeds have positive density, so some squarefree
seed selects `q` (`exists_squarefree_seed_selects`).

## The argument

* For `q = 2` any odd seed selects `2` at step `0` (`minFac (m+1) = 2`); take `m = 1`.
* For `q ≥ 3`: by `AlmostAllDensity.almost_all_genmc_density` with `ε = 1/12`, for large
  `X` at most `X/12` seeds `m ≤ X` coprime to `q` fail to select `q` within some horizon.
  The multiples of `q` number `≤ X/3`, and the non-squarefree `m ≤ X` number `≤ X/2`
  (`card_not_squarefree_le`: they lie in `⋃_p p²ℤ`, and
  `Σ_p 1/p² ≤ 1/4 + Σ_{k≥1} 1/(4k(k+1)) = 1/2`).  Since `1/2 + 1/3 + 1/12 < 1`, some
  squarefree seed coprime to `q` selects `q`.

No particular seed is exhibited and nothing is computed: the squarefree seed is produced by
counting.  A constructive seed (`m = q − 1` when that is squarefree, or `m = qℓ − 1` with `ℓ`
a prime `≥ q`) would need a sieve statement about squarefree values in a progression, which
the counting argument sidesteps.

## Extensions

The same count gives the two natural strengthenings:

* `almost_all_squarefree_select` — **almost all** squarefree seeds coprime to `q` select `q`:
  the failing ones are at most `ε` times all of them, for every `ε > 0` and all large `X`.
  For `q ≥ 3` the squarefree seeds coprime to `q` in `[1, X]` number at least `X/6`
  (`card_squarefree_coprime_ge`), and the failing coprime seeds at most `(ε/6)X`; for
  `q = 2` every odd seed selects `2` at step `0`, so nothing fails.
* `infinite_squarefree_seeds_select` — **infinitely many** squarefree seeds coprime to `q`
  select `q`.

## Scope

Population-level existence.  It says nothing about which seeds select `q`, nor about the
orbit of `2`.  It is the weakest nontrivial orbit-existence statement: one seed per prime
(indeed almost all of them), not one seed for all primes (the latter is
`∃ m, GenMullinConjecture m`, open; see `docs/analysis/analogy_map_2026-08-20.md`).
-/

noncomputable section
open Classical

namespace SquarefreeSeed

/-! ## 1. Non-squarefree numbers have density at most `1/2` -/

/-- Telescoping: `Σ_{k=1}^{X} 1/(k(k+1)) = 1 − 1/(X+1)`. -/
theorem sum_inv_mul_succ (X : ℕ) :
    ∑ k ∈ Finset.Icc 1 X, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) = 1 - 1 / ((X : ℝ) + 1) := by
  induction X with
  | zero => simp
  | succ X ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    field_simp
    ring

theorem sum_inv_mul_succ_le (X : ℕ) :
    ∑ k ∈ Finset.Icc 1 X, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) ≤ 1 := by
  rw [sum_inv_mul_succ]
  have : (0 : ℝ) ≤ 1 / ((X : ℝ) + 1) := by positivity
  linarith

/-- `Σ_{p prime ≤ X} 1/p² ≤ 1/2`: the prime `2` contributes `1/4`, and an odd prime
`p = 2k+1` contributes `1/p² < 1/(4k(k+1))`, whose sum telescopes to `< 1/4`. -/
theorem sum_prime_inv_sq_le (X : ℕ) :
    ∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) ^ 2) ≤ 1 / 2 := by
  set S := (Finset.Icc 2 X).filter Nat.Prime
  set S₃ := S.filter (fun p => 3 ≤ p)
  -- split off `p = 2`
  have hsplit : ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) ^ 2)
      ≤ 1 / 4 + ∑ p ∈ S₃, (1 : ℝ) / ((p : ℝ) ^ 2) := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun p => 3 ≤ p)]
    have h2 : ∑ p ∈ S.filter (fun p => ¬ 3 ≤ p), (1 : ℝ) / ((p : ℝ) ^ 2) ≤ 1 / 4 := by
      have hsub : S.filter (fun p => ¬ 3 ≤ p) ⊆ {2} := by
        intro p hp
        simp only [S, Finset.mem_filter, Finset.mem_Icc] at hp
        simp only [Finset.mem_singleton]; omega
      calc ∑ p ∈ S.filter (fun p => ¬ 3 ≤ p), (1 : ℝ) / ((p : ℝ) ^ 2)
          ≤ ∑ p ∈ ({2} : Finset ℕ), (1 : ℝ) / ((p : ℝ) ^ 2) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
        _ = 1 / 4 := by norm_num
    linarith
  -- odd primes: `p ↦ (p-1)/2` is injective into `Icc 1 X`
  have hodd : ∑ p ∈ S₃, (1 : ℝ) / ((p : ℝ) ^ 2)
      ≤ ∑ k ∈ Finset.Icc 1 X, (1 : ℝ) / (4 * ((k : ℝ) * ((k : ℝ) + 1))) := by
    have hterm : ∀ p ∈ S₃, (1 : ℝ) / ((p : ℝ) ^ 2)
        ≤ (1 : ℝ) / (4 * ((((p - 1) / 2 : ℕ) : ℝ) * ((((p - 1) / 2 : ℕ) : ℝ) + 1))) := by
      intro p hp
      simp only [S₃, S, Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨-, hprime⟩, h3⟩ := hp
      have hoddp : p % 2 = 1 := hprime.eq_one_or_self_of_dvd 2 |> fun h => by
        rcases Nat.even_or_odd p with he | ho
        · exact absurd (h (even_iff_two_dvd.mp he)) (by omega)
        · exact Nat.odd_iff.mp ho
      set k := (p - 1) / 2 with hk
      have hpk : p = 2 * k + 1 := by omega
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
      rw [hpk]; push_cast
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    calc ∑ p ∈ S₃, (1 : ℝ) / ((p : ℝ) ^ 2)
        ≤ ∑ p ∈ S₃, (1 : ℝ) / (4 * ((((p - 1) / 2 : ℕ) : ℝ) * ((((p - 1) / 2 : ℕ) : ℝ) + 1))) :=
          Finset.sum_le_sum hterm
      _ = ∑ k ∈ S₃.image (fun p : ℕ => ((p - 1) / 2 : ℕ)),
            (1 : ℝ) / (4 * ((k : ℝ) * ((k : ℝ) + 1))) := by
          refine (Finset.sum_image (g := fun p : ℕ => ((p - 1) / 2 : ℕ))
            (f := fun k : ℕ => (1 : ℝ) / (4 * ((k : ℝ) * ((k : ℝ) + 1)))) ?_).symm
          intro a ha b hb hab
          have hab' : (a - 1) / 2 = (b - 1) / 2 := hab
          obtain ⟨haS, ha3⟩ := Finset.mem_filter.mp ha
          obtain ⟨hbS, hb3⟩ := Finset.mem_filter.mp hb
          have hap : a.Prime := (Finset.mem_filter.mp haS).2
          have hbp : b.Prime := (Finset.mem_filter.mp hbS).2
          have ha2 : a % 2 = 1 := by
            rcases Nat.even_or_odd a with he | ho
            · exact absurd (hap.eq_one_or_self_of_dvd 2 (even_iff_two_dvd.mp he)) (by omega)
            · exact Nat.odd_iff.mp ho
          have hb2 : b % 2 = 1 := by
            rcases Nat.even_or_odd b with he | ho
            · exact absurd (hbp.eq_one_or_self_of_dvd 2 (even_iff_two_dvd.mp he)) (by omega)
            · exact Nat.odd_iff.mp ho
          omega
      _ ≤ ∑ k ∈ Finset.Icc 1 X, (1 : ℝ) / (4 * ((k : ℝ) * ((k : ℝ) + 1))) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
            simp only [S₃, S, Finset.mem_filter, Finset.mem_Icc] at hp
            simp only [Finset.mem_Icc]; omega
          · intro k _ _; positivity
  have htel : ∑ k ∈ Finset.Icc 1 X, (1 : ℝ) / (4 * ((k : ℝ) * ((k : ℝ) + 1))) ≤ 1 / 4 := by
    have : ∑ k ∈ Finset.Icc 1 X, (1 : ℝ) / (4 * ((k : ℝ) * ((k : ℝ) + 1)))
        = (1 / 4) * ∑ k ∈ Finset.Icc 1 X, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      field_simp
    rw [this]
    have := sum_inv_mul_succ_le X
    linarith
  linarith

/-- Multiples of `d ≥ 1` in `[1, X]` number exactly `X / d`. -/
theorem card_multiples_Icc (d X : ℕ) :
    ((Finset.Icc 1 X).filter (fun m => d ∣ m)).card = X / d := by
  have h : Finset.Icc 1 X = Finset.Ioc 0 X := Finset.Icc_add_one_left_eq_Ioc 0 X
  rw [h, Nat.Ioc_filter_dvd_card_eq_div]

/-- **Non-squarefree numbers in `[1, X]` number at most `X / 2`.** -/
theorem card_not_squarefree_le (X : ℕ) :
    (((Finset.Icc 1 X).filter (fun m => ¬ Squarefree m)).card : ℝ) ≤ (X : ℝ) / 2 := by
  -- every non-squarefree `m ≤ X` is a multiple of `p²` for a prime `p ≤ X`
  have hsub : (Finset.Icc 1 X).filter (fun m => ¬ Squarefree m) ⊆
      ((Finset.Icc 2 X).filter Nat.Prime).biUnion
        (fun p => (Finset.Icc 1 X).filter (fun m => p * p ∣ m)) := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, hmX⟩, hnsf⟩ := hm
    rw [Nat.squarefree_iff_prime_squarefree] at hnsf
    obtain ⟨p, hp', hdvd⟩ : ∃ p, Nat.Prime p ∧ p * p ∣ m := by
      by_contra hno
      exact hnsf fun p hp hdvd => hno ⟨p, hp, hdvd⟩
    have hpm : p ≤ m := le_trans (Nat.le_mul_self p) (Nat.le_of_dvd (by omega) hdvd)
    refine Finset.mem_biUnion.mpr ⟨p, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hp'.two_le, le_trans hpm hmX⟩, hp'⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hm1, hmX⟩, hdvd⟩
  have h1 : (((Finset.Icc 1 X).filter (fun m => ¬ Squarefree m)).card : ℝ)
      ≤ ∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
          (((Finset.Icc 1 X).filter (fun m => p * p ∣ m)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : ∀ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
      (((Finset.Icc 1 X).filter (fun m => p * p ∣ m)).card : ℝ) ≤ (X : ℝ) * (1 / ((p : ℝ) ^ 2)) := by
    intro p hp
    rw [card_multiples_Icc]
    have hpos : (0 : ℝ) < (p : ℝ) ^ 2 := by
      have := (Finset.mem_filter.mp hp).2.pos; positivity
    calc ((X / (p * p) : ℕ) : ℝ) ≤ (X : ℝ) / ((p * p : ℕ) : ℝ) := Nat.cast_div_le
      _ = (X : ℝ) * (1 / ((p : ℝ) ^ 2)) := by push_cast; ring
  calc (((Finset.Icc 1 X).filter (fun m => ¬ Squarefree m)).card : ℝ)
      ≤ ∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime, (X : ℝ) * (1 / ((p : ℝ) ^ 2)) :=
        h1.trans (Finset.sum_le_sum h2)
    _ = (X : ℝ) * ∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ (X : ℝ) * (1 / 2) := by
        gcongr
        exact sum_prime_inv_sq_le X
    _ = (X : ℝ) / 2 := by ring

/-! ## 2. The existence theorem -/

/-- **Every prime is selected by some squarefree seed coprime to it.**  For `q = 2` the seed
`1` works; for `q ≥ 3` the seed is produced by counting: almost all seeds select `q`, while
multiples of `q` and non-squarefree numbers together have density `≤ 1/3 + 1/2 < 1`. -/
theorem exists_squarefree_seed_selects (q : ℕ) (hq : q.Prime) :
    ∃ m : ℕ, Squarefree m ∧ ¬ q ∣ m ∧ ∃ k, genSeq m k = q := by
  by_cases hq2 : q = 2
  · subst hq2
    refine ⟨1, squarefree_one, by omega, 0, ?_⟩
    show Nat.minFac (1 + 1) = 2
    exact Nat.prime_two.minFac_eq
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  by_contra hno
  have hno : ∀ m, Squarefree m → ¬ q ∣ m → ∀ k, genSeq m k ≠ q :=
    fun m hsf hqm k hk => hno ⟨m, hsf, hqm, k, hk⟩
  -- every squarefree seed coprime to `q` never selects `q`
  have hε : (0 : ℝ) < 1 / 12 := by norm_num
  obtain ⟨n, X₀, hX₀⟩ := AlmostAllDensity.almost_all_genmc_density q hq hε
  set X := max X₀ 1 with hXdef
  have hXge : X₀ ≤ X := le_max_left _ _
  have hX1 : 1 ≤ X := le_max_right _ _
  have hbad := hX₀ X hXge
  -- the three covering pieces
  set A := (Finset.Icc 1 X).filter (fun m => ¬ Squarefree m)
  set B := (Finset.Icc 1 X).filter (fun m => q ∣ m)
  set C := (Finset.Icc 1 X).filter (fun m => ¬ q ∣ m ∧ ¬ ∃ j < n, genSeq m j = q)
  have hcover : Finset.Icc 1 X ⊆ A ∪ B ∪ C := by
    intro m hm
    simp only [A, B, C, Finset.mem_union, Finset.mem_filter]
    by_cases hsf : Squarefree m
    · by_cases hqm : q ∣ m
      · exact Or.inl (Or.inr ⟨hm, hqm⟩)
      · refine Or.inr ⟨hm, hqm, ?_⟩
        rintro ⟨j, -, hj⟩
        exact hno m hsf hqm j hj
    · exact Or.inl (Or.inl ⟨hm, hsf⟩)
  have hA : (A.card : ℝ) ≤ (X : ℝ) / 2 := card_not_squarefree_le X
  have hB : (B.card : ℝ) ≤ (X : ℝ) / 3 := by
    simp only [B]
    rw [card_multiples_Icc]
    have hq3' : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
    calc ((X / q : ℕ) : ℝ) ≤ (X : ℝ) / (q : ℝ) := Nat.cast_div_le
      _ ≤ (X : ℝ) / 3 := by
          apply div_le_div_of_nonneg_left (Nat.cast_nonneg X) (by norm_num) hq3'
  have hC : (C.card : ℝ) ≤ 1 / 12 * (X : ℝ) := hbad
  have hcard : ((Finset.Icc 1 X).card : ℝ) ≤ (A.card : ℝ) + (B.card : ℝ) + (C.card : ℝ) := by
    have h := Finset.card_le_card hcover
    have h' := (Finset.card_union_le (A ∪ B) C).trans
      (Nat.add_le_add_right (Finset.card_union_le A B) _)
    exact_mod_cast h.trans h'
  have hIcc : ((Finset.Icc 1 X).card : ℝ) = (X : ℝ) := by
    rw [Nat.card_Icc]; push_cast; ring
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX1
  rw [hIcc] at hcard
  linarith

/-! ## 3. Almost all squarefree seeds, and infinitely many -/

/-- For `q ≥ 3`, the squarefree seeds coprime to `q` in `[1, X]` number at least `X/6`. -/
theorem card_squarefree_coprime_ge (q : ℕ) (hq3 : 3 ≤ q) (X : ℕ) :
    (X : ℝ) / 6 ≤ (((Finset.Icc 1 X).filter (fun m => Squarefree m ∧ ¬ q ∣ m)).card : ℝ) := by
  set A := (Finset.Icc 1 X).filter (fun m => ¬ Squarefree m)
  set B := (Finset.Icc 1 X).filter (fun m => q ∣ m)
  set G := (Finset.Icc 1 X).filter (fun m => Squarefree m ∧ ¬ q ∣ m)
  have hcover : Finset.Icc 1 X ⊆ A ∪ B ∪ G := by
    intro m hm
    simp only [A, B, G, Finset.mem_union, Finset.mem_filter]
    by_cases hsf : Squarefree m
    · by_cases hqm : q ∣ m
      · exact Or.inl (Or.inr ⟨hm, hqm⟩)
      · exact Or.inr ⟨hm, hsf, hqm⟩
    · exact Or.inl (Or.inl ⟨hm, hsf⟩)
  have hA : (A.card : ℝ) ≤ (X : ℝ) / 2 := card_not_squarefree_le X
  have hB : (B.card : ℝ) ≤ (X : ℝ) / 3 := by
    simp only [B]
    rw [card_multiples_Icc]
    have hq3' : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
    calc ((X / q : ℕ) : ℝ) ≤ (X : ℝ) / (q : ℝ) := Nat.cast_div_le
      _ ≤ (X : ℝ) / 3 := by
          apply div_le_div_of_nonneg_left (Nat.cast_nonneg X) (by norm_num) hq3'
  have hcard : ((Finset.Icc 1 X).card : ℝ) ≤ (A.card : ℝ) + (B.card : ℝ) + (G.card : ℝ) := by
    have h := Finset.card_le_card hcover
    have h' := (Finset.card_union_le (A ∪ B) G).trans
      (Nat.add_le_add_right (Finset.card_union_le A B) _)
    exact_mod_cast h.trans h'
  have hIcc : ((Finset.Icc 1 X).card : ℝ) = (X : ℝ) := by
    rw [Nat.card_Icc]; push_cast; ring
  rw [hIcc] at hcard
  linarith

/-- **Almost all squarefree seeds coprime to `q` select `q`.**  For every `ε > 0` and all
large `X`, the squarefree seeds `m ≤ X` coprime to `q` that never select `q` are at most `ε`
times the squarefree seeds `m ≤ X` coprime to `q`. -/
theorem almost_all_squarefree_select (q : ℕ) (hq : q.Prime) {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X, X₀ ≤ X →
      (((Finset.Icc 1 X).filter
          (fun m => Squarefree m ∧ ¬ q ∣ m ∧ ∀ k, genSeq m k ≠ q)).card : ℝ)
        ≤ ε * (((Finset.Icc 1 X).filter (fun m => Squarefree m ∧ ¬ q ∣ m)).card : ℝ) := by
  by_cases hq2 : q = 2
  · -- every odd seed selects `2` at step `0`: the failing set is empty
    subst hq2
    refine ⟨0, fun X _ => ?_⟩
    have hempty : (Finset.Icc 1 X).filter
        (fun m => Squarefree m ∧ ¬ 2 ∣ m ∧ ∀ k, genSeq m k ≠ 2) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro m hm hbad
      obtain ⟨-, hodd, hnever⟩ := hbad
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      exact hnever 0 (genSeq_zero_of_odd hm1 (fun he => hodd (even_iff_two_dvd.mp he)))
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hε' : (0 : ℝ) < ε / 6 := by positivity
  obtain ⟨n, X₀, hX₀⟩ := AlmostAllDensity.almost_all_genmc_density q hq hε'
  refine ⟨X₀, fun X hX => ?_⟩
  have hbad := hX₀ X hX
  -- failing squarefree seeds are among the failing coprime seeds at horizon `n`
  have hsub : (Finset.Icc 1 X).filter (fun m => Squarefree m ∧ ¬ q ∣ m ∧ ∀ k, genSeq m k ≠ q)
      ⊆ (Finset.Icc 1 X).filter (fun m => ¬ q ∣ m ∧ ¬ ∃ j < n, genSeq m j = q) := by
    intro m hm
    simp only [Finset.mem_filter] at hm ⊢
    obtain ⟨hI, -, hqm, hnever⟩ := hm
    exact ⟨hI, hqm, fun ⟨j, _, hj⟩ => hnever j hj⟩
  have h1 : (((Finset.Icc 1 X).filter
      (fun m => Squarefree m ∧ ¬ q ∣ m ∧ ∀ k, genSeq m k ≠ q)).card : ℝ) ≤ ε / 6 * (X : ℝ) :=
    le_trans (by exact_mod_cast Finset.card_le_card hsub) hbad
  have h2 := card_squarefree_coprime_ge q hq3 X
  calc _ ≤ ε / 6 * (X : ℝ) := h1
    _ = ε * ((X : ℝ) / 6) := by ring
    _ ≤ ε * _ := by gcongr

/-- **Infinitely many squarefree seeds coprime to `q` select `q`.** -/
theorem infinite_squarefree_seeds_select (q : ℕ) (hq : q.Prime) :
    Set.Infinite {m : ℕ | Squarefree m ∧ ¬ q ∣ m ∧ ∃ k, genSeq m k = q} := by
  by_cases hq2 : q = 2
  · -- every odd prime is such a seed
    subst hq2
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨p, hap, hp⟩ := Nat.exists_infinite_primes (a + 3)
    have hodd : ¬ Even p := by
      intro he
      have := hp.eq_one_or_self_of_dvd 2 (even_iff_two_dvd.mp he)
      omega
    refine ⟨p, ⟨hp.squarefree, fun h2 => hodd (even_iff_two_dvd.mpr h2),
      0, genSeq_zero_of_odd hp.one_lt.le hodd⟩, by omega⟩
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  obtain ⟨X₀, hX₀⟩ := almost_all_squarefree_select q hq (ε := 1 / 2) (by norm_num)
  apply Set.infinite_of_forall_exists_gt
  intro a
  -- at scale `X`, good seeds number at least `X/12 > a`
  set X := max X₀ (12 * (a + 1)) with hXdef
  have hXge : X₀ ≤ X := le_max_left _ _
  have hXa : 12 * (a + 1) ≤ X := le_max_right _ _
  set G := (Finset.Icc 1 X).filter (fun m => Squarefree m ∧ ¬ q ∣ m)
  set F := (Finset.Icc 1 X).filter (fun m => Squarefree m ∧ ¬ q ∣ m ∧ ∀ k, genSeq m k ≠ q)
  set Good := (Finset.Icc 1 X).filter (fun m => Squarefree m ∧ ¬ q ∣ m ∧ ∃ k, genSeq m k = q)
  have hGF : G ⊆ F ∪ Good := by
    intro m hm
    simp only [G, F, Good, Finset.mem_union, Finset.mem_filter] at hm ⊢
    obtain ⟨hI, hsf, hqm⟩ := hm
    by_cases h : ∃ k, genSeq m k = q
    · exact Or.inr ⟨hI, hsf, hqm, h⟩
    · exact Or.inl ⟨hI, hsf, hqm, fun k hk => h ⟨k, hk⟩⟩
  have hF : (F.card : ℝ) ≤ 1 / 2 * (G.card : ℝ) := hX₀ X hXge
  have hG : (X : ℝ) / 6 ≤ (G.card : ℝ) := card_squarefree_coprime_ge q hq3 X
  have hGcard : (G.card : ℝ) ≤ (F.card : ℝ) + (Good.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hGF).trans (Finset.card_union_le F Good)
  have hGood : (a : ℝ) < (Good.card : ℝ) := by
    have hXa' : (12 : ℝ) * ((a : ℝ) + 1) ≤ (X : ℝ) := by exact_mod_cast hXa
    linarith
  have hGood' : a < Good.card := by exact_mod_cast hGood
  -- a finset with more than `a` elements has an element `> a`
  by_contra hno
  have hall : ∀ m ∈ Good, m ≤ a := by
    intro m hm
    by_contra h
    simp only [Good, Finset.mem_filter] at hm
    exact hno ⟨m, hm.2, by omega⟩
  have : Good ⊆ Finset.Icc 1 a := by
    intro m hm
    have h1 : 1 ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
    exact Finset.mem_Icc.mpr ⟨h1, hall m hm⟩
  have := Finset.card_le_card this
  rw [Nat.card_Icc] at this
  omega

end SquarefreeSeed

end
