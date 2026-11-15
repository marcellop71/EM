import EM.Population.SquareTree
import Mathlib.Tactic.Ring

/-!
# The Euclid tree with a bounded number of squared primes

`EM/Population/SquareTree.lean` proves that the Euclid tree in which every prime of the node
may be squared reaches every prime. Here the number of squared primes per step is bounded:
a node `D` is extended by any prime factor of `∏ D · ∏ T + 1`, where `T ⊆ D` has at most
`m` elements. The budget `m = 0` is the tree of `MixedMC` (open); `m = 1` is "at most one
prime squared".

## Main results

* `ReachB m D₀ D` — the tree with at most `m` squared primes per step.
* `exists_small_subset` — modulo a prime `q`, every sub-product of nonzero residues equals
  a sub-product of at most `q - 2` of them (the Davenport constant of a cyclic group).
* `exists_reachB_mem` — **if `q - 2 ≤ m`, the prime `q` is reached**, from any finite set
  of primes.

## What this says about small budgets

The proof is the one of `SquareTree.exists_reach_mem`: the set of attainable residues mod
`q` is the same for the budget `q - 2` as for an unlimited budget. It uses no information on
the prime factors of `N + 1` beyond "their residues multiply to the residue of `N + 1`".

No argument of that kind can go below a budget linear in `q`. Fix a primitive root `g` mod
`q` and a residue `a`. Consider the scenario in which every node has product `≡ a` or
`≡ a·g`, every prime adjoined from a node of the first kind is `≡ g`, and every prime
adjoined from a node of the second kind is `≡ g⁻¹`. Every nonzero residue is a power of `g`
and of `g⁻¹`, so the scenario contradicts no multiplicative relation. With budget `m` the
admissible products are `≡ a·g^j` with `-m ≤ j ≤ m + 1`; if `2m + 2 ≤ q - 2`, the residue
`a` can be chosen so that none of them is `-1`. Hence for `m ≤ (q - 4)/2`, and in particular
for `m = 1` and `q ≥ 7`, reaching `q` requires arithmetic information on the prime factors
of `N + 1` that residues mod `q` do not carry. The case `m = 1` is open.
-/

open Finset

namespace SquareTree

/-- `ReachB m D₀ D`: the set `D` is obtained from `D₀` by repeatedly adjoining a prime
    factor of `∏ D · ∏ T + 1`, where `T ⊆ D` (the squared primes) has at most `m` elements. -/
inductive ReachB (m : ℕ) (D₀ : Finset ℕ) : Finset ℕ → Prop
  | refl : ReachB m D₀ D₀
  | step {D : Finset ℕ} (hD : ReachB m D₀ D) (T : Finset ℕ) (hT : T ⊆ D) (hcard : T.card ≤ m)
      (p : ℕ) (hp : p.Prime) (hd : p ∣ (∏ r ∈ D, r) * (∏ r ∈ T, r) + 1) :
      ReachB m D₀ (insert p D)

theorem ReachB.prime {m : ℕ} {D₀ D : Finset ℕ} (h₀ : ∀ r ∈ D₀, r.Prime)
    (h : ReachB m D₀ D) : ∀ r ∈ D, r.Prime := by
  induction h with
  | refl => exact h₀
  | step hD T hT hcard p hp hd ih =>
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hp
    · exact ih r hr

theorem ReachB.subset {m : ℕ} {D₀ D : Finset ℕ} (h : ReachB m D₀ D) : D₀ ⊆ D := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step hD T hT hcard p hp hd ih => exact ih.trans (Finset.subset_insert _ _)

theorem ReachB.trans {m : ℕ} {D₀ D₁ D₂ : Finset ℕ} (h₁ : ReachB m D₀ D₁)
    (h₂ : ReachB m D₁ D₂) : ReachB m D₀ D₂ := by
  induction h₂ with
  | refl => exact h₁
  | step hD T hT hcard p hp hd ih => exact ReachB.step ih T hT hcard p hp hd

/-- A larger budget reaches at least as much. -/
theorem ReachB.mono {m m' : ℕ} (hmm : m ≤ m') {D₀ D : Finset ℕ} (h : ReachB m D₀ D) :
    ReachB m' D₀ D := by
  induction h with
  | refl => exact ReachB.refl
  | step hD T hT hcard p hp hd ih => exact ReachB.step ih T hT (hcard.trans hmm) p hp hd

/-- The bounded tree is a sub-tree of the tree with exponents `1` or `2`. -/
theorem ReachB.reach {m : ℕ} {D₀ D : Finset ℕ} (h : ReachB m D₀ D) : Reach D₀ D := by
  classical
  induction h with
  | refl => exact Reach.refl
  | @step D hD T hT hcard p hp hd ih =>
    refine Reach.step ih (fun r => if r ∈ T then 2 else 1)
      (fun r _ => by by_cases h : r ∈ T <;> simp [h]) p hp ?_
    have hprod : ∏ r ∈ D, r ^ (if r ∈ T then 2 else 1) = (∏ r ∈ D, r) * ∏ r ∈ T, r := by
      have h1 : ∀ r ∈ D, r ^ (if r ∈ T then 2 else 1) = r * (if r ∈ T then r else 1) := by
        intro r _
        by_cases h : r ∈ T <;> simp [h, pow_two]
      rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_ite_mem,
        Finset.inter_eq_right.mpr hT]
    rw [hprod]
    exact hd

/-! ## Short sub-products -/

/-- The residues mod `q` of the sub-products of `T`. -/
def SP (q : ℕ) (T : Finset ℕ) : Set (ZMod q) :=
  {x | ∃ U ⊆ T, x = ∏ r ∈ U, ((r : ℕ) : ZMod q)}

/-- Either some nonempty sub-product of `T` is `1` mod `q`, or `T` has at least
    `|T| + 1` distinct sub-products mod `q`. -/
theorem exists_unit_subprod_or_card_lt {q : ℕ} [Fact q.Prime] (T : Finset ℕ)
    (hne : ∀ r ∈ T, ((r : ℕ) : ZMod q) ≠ 0) :
    (∃ U ⊆ T, U.Nonempty ∧ ∏ r ∈ U, ((r : ℕ) : ZMod q) = 1) ∨
      T.card + 1 ≤ (SP q T).ncard := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    right
    have h1 : (1 : ZMod q) ∈ SP q ∅ := ⟨∅, Finset.Subset.refl _, by simp⟩
    have := (Set.ncard_pos (Set.toFinite _)).mpr ⟨1, h1⟩
    rw [Finset.card_empty]
    omega
  | insert a T haT ih =>
    have hsub : SP q T ⊆ SP q (insert a T) := fun x ⟨U, hU, hx⟩ =>
      ⟨U, hU.trans (Finset.subset_insert _ _), hx⟩
    rcases ih (fun r hr => hne r (Finset.mem_insert_of_mem hr)) with
      ⟨U, hU, hUn, hU1⟩ | hcard
    · exact Or.inl ⟨U, hU.trans (Finset.subset_insert _ _), hUn, hU1⟩
    · have hc0 : ((a : ℕ) : ZMod q) ≠ 0 := hne a (Finset.mem_insert_self _ _)
      by_cases hall : ∀ x ∈ SP q T, ((a : ℕ) : ZMod q) * x ∈ SP q T
      · left
        have himg : (fun y => ((a : ℕ) : ZMod q) * y) '' SP q T = SP q T := by
          apply Set.eq_of_subset_of_ncard_le
          · rintro _ ⟨y, hy, rfl⟩
            exact hall y hy
          · rw [Set.ncard_image_of_injective _ (mul_right_injective₀ hc0)]
          · exact Set.toFinite _
        have h1 : (1 : ZMod q) ∈ SP q T := ⟨∅, Finset.empty_subset _, by simp⟩
        rw [← himg] at h1
        obtain ⟨y, ⟨U, hU, rfl⟩, hy1⟩ := h1
        have haU : a ∉ U := fun h => haT (hU h)
        refine ⟨insert a U, Finset.insert_subset_insert _ hU, Finset.insert_nonempty _ _, ?_⟩
        rw [Finset.prod_insert haU]
        exact hy1
      · right
        push Not at hall
        obtain ⟨x, ⟨U, hU, rfl⟩, hxn⟩ := hall
        have haU : a ∉ U := fun h => haT (hU h)
        have hnew : ((a : ℕ) : ZMod q) * ∏ r ∈ U, ((r : ℕ) : ZMod q) ∈ SP q (insert a T) :=
          ⟨insert a U, Finset.insert_subset_insert _ hU, by rw [Finset.prod_insert haU]⟩
        rw [Finset.card_insert_of_notMem haT]
        calc T.card + 1 + 1 ≤ (SP q T).ncard + 1 := by omega
          _ = (insert (((a : ℕ) : ZMod q) * ∏ r ∈ U, ((r : ℕ) : ZMod q)) (SP q T)).ncard :=
              (Set.ncard_insert_of_notMem hxn).symm
          _ ≤ (SP q (insert a T)).ncard :=
              Set.ncard_le_ncard (Set.insert_subset hnew hsub)

/-- **Short sub-products.** Modulo a prime `q`, every sub-product of nonzero residues is
    the sub-product of at most `q - 2` of them. -/
theorem exists_small_subset {q : ℕ} [Fact q.Prime] (T : Finset ℕ)
    (hne : ∀ r ∈ T, ((r : ℕ) : ZMod q) ≠ 0) :
    ∃ T' ⊆ T, T'.card ≤ q - 2 ∧
      ∏ r ∈ T', ((r : ℕ) : ZMod q) = ∏ r ∈ T, ((r : ℕ) : ZMod q) := by
  classical
  induction T using Finset.strongInduction with
  | H T ih =>
    by_cases hc : T.card ≤ q - 2
    · exact ⟨T, Finset.Subset.refl _, hc, rfl⟩
    · have h0 : (0 : ZMod q) ∉ SP q T := by
        rintro ⟨U, hU, h⟩
        exact (Finset.prod_ne_zero_iff.mpr (fun r hr => hne r (hU hr))) h.symm
      have hle : (SP q T).ncard + 1 ≤ q := by
        calc (SP q T).ncard + 1 = (insert (0 : ZMod q) (SP q T)).ncard :=
              (Set.ncard_insert_of_notMem h0).symm
          _ ≤ (Set.univ : Set (ZMod q)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
          _ = q := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, ZMod.card]
      rcases exists_unit_subprod_or_card_lt T hne with ⟨U, hU, hUn, hU1⟩ | hcard
      · obtain ⟨T', hT', hc', hp'⟩ := ih (T \ U) (Finset.sdiff_ssubset hU hUn)
          (fun r hr => hne r (Finset.sdiff_subset hr))
        refine ⟨T', hT'.trans Finset.sdiff_subset, hc', ?_⟩
        rw [hp', ← Finset.prod_sdiff hU, hU1, mul_one]
      · omega

/-! ## Attainable residues -/

/-- The residues mod `q` of the products `∏ D · ∏ T`, `T ⊆ D` (no bound on `T`). -/
def GB (q : ℕ) (D : Finset ℕ) : Set (ZMod q) :=
  {x | ∃ T ⊆ D, x = (((∏ r ∈ D, r) * ∏ r ∈ T, r : ℕ) : ZMod q)}

/-- The nonzero residues that map `GB q D` into itself by multiplication. -/
def StabB (q : ℕ) (D : Finset ℕ) : Set (ZMod q) :=
  {h | h ≠ 0 ∧ ∀ x ∈ GB q D, h * x ∈ GB q D}

theorem mul_mem_GB_insert {q : ℕ} {D : Finset ℕ} {p : ℕ} (hpD : p ∉ D) {x : ZMod q}
    (hx : x ∈ GB q D) : ((p : ℕ) : ZMod q) * x ∈ GB q (insert p D) := by
  obtain ⟨T, hT, rfl⟩ := hx
  refine ⟨T, hT.trans (Finset.subset_insert _ _), ?_⟩
  rw [Finset.prod_insert hpD]
  push_cast
  ring

theorem sq_mul_mem_GB_insert {q : ℕ} {D : Finset ℕ} {p : ℕ} (hpD : p ∉ D) {x : ZMod q}
    (hx : x ∈ GB q D) : ((p : ℕ) : ZMod q) ^ 2 * x ∈ GB q (insert p D) := by
  obtain ⟨T, hT, rfl⟩ := hx
  refine ⟨insert p T, Finset.insert_subset_insert _ hT, ?_⟩
  rw [Finset.prod_insert hpD, Finset.prod_insert (fun h => hpD (hT h))]
  push_cast
  ring

/-! ## The theorem -/

/-- **A budget of `q - 2` squares reaches `q`.** From any finite set of primes `D₀`, the
    Euclid tree with at most `m` squared primes per step reaches a node containing the
    prime `q`, as soon as `q - 2 ≤ m`. -/
theorem exists_reachB_mem {D₀ : Finset ℕ} (h₀ : ∀ r ∈ D₀, r.Prime) {q : ℕ} (hq : q.Prime)
    {m : ℕ} (hm : q - 2 ≤ m) : ∃ D, ReachB m D₀ D ∧ q ∈ D := by
  classical
  by_contra hno
  have hno' : ∀ D, ReachB m D₀ D → q ∉ D := fun D hD hqD => hno ⟨D, hD, hqD⟩
  have : Fact q.Prime := ⟨hq⟩
  have hne : ∀ D, ReachB m D₀ D → ∀ r ∈ D, ((r : ℕ) : ZMod q) ≠ 0 := by
    intro D hD r hr
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    exact hno' D hD (((Nat.prime_dvd_prime_iff_eq hq (hD.prime h₀ r hr)).mp hd) ▸ hr)
  have hbound : ∀ D, (GB q D).ncard ≤ q := fun D => by
    calc (GB q D).ncard ≤ (Set.univ : Set (ZMod q)).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _)
      _ = q := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, ZMod.card]
  obtain ⟨D, hD, hmax⟩ : ∃ D, ReachB m D₀ D ∧
      ∀ D', ReachB m D₀ D' → (GB q D').ncard ≤ (GB q D).ncard := by
    have hP := Nat.findGreatest_spec
      (P := fun k => ∃ D, ReachB m D₀ D ∧ (GB q D).ncard = k)
      (hbound D₀) ⟨D₀, ReachB.refl, rfl⟩
    obtain ⟨D, hD, hk⟩ := hP
    refine ⟨D, hD, fun D' hD' => ?_⟩
    rw [hk]
    exact Nat.le_findGreatest (P := fun k => ∃ D, ReachB m D₀ D ∧ (GB q D).ncard = k)
      (hbound D') ⟨D', hD', rfl⟩
  -- the class of every prime factor of every admissible `N + 1` stabilises `GB q D`
  have hchild : ∀ T : Finset ℕ, T ⊆ D → T.card ≤ m → ∀ p : ℕ, p.Prime →
      p ∣ (∏ r ∈ D, r) * (∏ r ∈ T, r) + 1 → ((p : ℕ) : ZMod q) ∈ StabB q D := by
    intro T hT hcard p hp hd
    have hnode : ReachB m D₀ (insert p D) := ReachB.step hD T hT hcard p hp hd
    have hc0 : ((p : ℕ) : ZMod q) ≠ 0 := hne _ hnode p (Finset.mem_insert_self _ _)
    have hpD : p ∉ D := by
      intro hpD
      have hdvd : p ∣ (∏ r ∈ D, r) * ∏ r ∈ T, r :=
        (Finset.dvd_prod_of_mem (fun r => r) hpD).mul_right _
      exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hdvd).mp hd))
    refine ⟨hc0, fun x hx => ?_⟩
    by_contra hnot
    have himg : (fun y => ((p : ℕ) : ZMod q) * y) '' GB q D ⊆ GB q (insert p D) := by
      rintro _ ⟨y, hy, rfl⟩
      exact mul_mem_GB_insert hpD hy
    have hsq : ((p : ℕ) : ZMod q) ^ 2 * x ∈ GB q (insert p D) := sq_mul_mem_GB_insert hpD hx
    have hnew : ((p : ℕ) : ZMod q) ^ 2 * x ∉ (fun y => ((p : ℕ) : ZMod q) * y) '' GB q D := by
      rintro ⟨y, hy, hyx⟩
      have hyeq : y = ((p : ℕ) : ZMod q) * x := by
        apply mul_left_cancel₀ hc0
        have hyx' : ((p : ℕ) : ZMod q) * y = ((p : ℕ) : ZMod q) ^ 2 * x := hyx
        rw [hyx', pow_two, mul_assoc]
      exact hnot (hyeq ▸ hy)
    have hcard' : (GB q D).ncard + 1 ≤ (GB q (insert p D)).ncard := by
      calc (GB q D).ncard + 1
          = ((fun y => ((p : ℕ) : ZMod q) * y) '' GB q D).ncard + 1 := by
            rw [Set.ncard_image_of_injective _ (mul_right_injective₀ hc0)]
        _ = (insert (((p : ℕ) : ZMod q) ^ 2 * x)
              ((fun y => ((p : ℕ) : ZMod q) * y) '' GB q D)).ncard :=
            (Set.ncard_insert_of_notMem hnew).symm
        _ ≤ (GB q (insert p D)).ncard :=
            Set.ncard_le_ncard (Set.insert_subset hsq himg)
    have := hmax _ hnode
    omega
  have hT1 : (1 : ZMod q) ∈ StabB q D := ⟨one_ne_zero, fun x hx => by rwa [one_mul]⟩
  have hT0 : (0 : ZMod q) ∉ StabB q D := fun h => h.1 rfl
  have hTmul : ∀ x ∈ StabB q D, ∀ y ∈ StabB q D, x * y ∈ StabB q D := by
    intro x hx y hy
    refine ⟨mul_ne_zero hx.1 hy.1, fun z hz => ?_⟩
    rw [mul_assoc]
    exact hx.2 _ (hy.2 z hz)
  -- `x + 1` stabilises `GB q D` for every attainable `x`: realise `x` within the budget
  have hplus : ∀ x ∈ GB q D, x + 1 ∈ StabB q D := by
    rintro _ ⟨T, hT, rfl⟩
    obtain ⟨T', hT', hc', hp'⟩ := exists_small_subset (q := q) T
      (fun r hr => hne D hD r (hT hr))
    have hmem := natCast_mem_of_primeFactors (StabB q D) hT1 hTmul
      ((∏ r ∈ D, r) * (∏ r ∈ T', r) + 1) (Nat.succ_pos _)
      (fun p hp hd => hchild T' (hT'.trans hT) (hc'.trans hm) p hp hd)
    have heq : (((∏ r ∈ D, r) * (∏ r ∈ T', r) + 1 : ℕ) : ZMod q) =
        (((∏ r ∈ D, r) * ∏ r ∈ T, r : ℕ) : ZMod q) + 1 := by
      push_cast
      rw [hp']
    rwa [heq] at hmem
  have haG : (((∏ r ∈ D, r) * ∏ r ∈ (∅ : Finset ℕ), r : ℕ) : ZMod q) ∈ GB q D :=
    ⟨∅, Finset.empty_subset _, rfl⟩
  have ha0 : (((∏ r ∈ D, r) * ∏ r ∈ (∅ : Finset ℕ), r : ℕ) : ZMod q) ≠ 0 := by
    rw [Finset.prod_empty, mul_one, Nat.cast_prod]
    exact Finset.prod_ne_zero_iff.mpr (hne D hD)
  exact no_affine_stable (StabB q D) hT1 hT0 hTmul _ ha0
    (fun h hh => by rw [mul_comm]; exact hplus _ (hh.2 _ haG))

/-- Every prime `q` is reached with at most `q - 2` squared primes per step. -/
theorem exists_reachB_mem_self {D₀ : Finset ℕ} (h₀ : ∀ r ∈ D₀, r.Prime) {q : ℕ}
    (hq : q.Prime) : ∃ D, ReachB (q - 2) D₀ D ∧ q ∈ D :=
  exists_reachB_mem h₀ hq le_rfl

end SquareTree
