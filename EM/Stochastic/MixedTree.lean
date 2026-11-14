import EM.Stochastic.RandomVariant
import EM.Stochastic.MissedPrimes

/-!
# The Euclid tree from 2: canonical forms of `MixedMC`, inductive escape, the detour ladder

`MixedMC q` (`EM/Stochastic/MixedMC.lean`) says that some branch of the Euclid tree from `2`
selects the prime `q`, where a branch may multiply by **any** prime factor of `P + 1`. It is
implied by Mullin's conjecture (the greedy branch is a branch) and is open; it is the
question Booker and Irvine study on the Euclid–Mullin graph.

This file does three things. Nothing here proves `MixedMC q` for a new `q`.

## 1. One statement, five forms (all proved equivalent, `q ≥ 3` prime)

* `mixedMC_iff_reachable` — `-1 ∈ reachableEver q 2`: some node is `≡ -1 (mod q)`.
* `mixedMC_iff_failWeightK_lt_one` — for **any** selection kernel with full support, the
  probability of selecting `q` within some finite horizon is positive.
* `mixedMC_iff_eps_capture` — the same for the mixture "`ε`·uniform + `(1-ε)`·greedy", every
  `0 < ε ≤ 1`; hence `eps_capture_indep`: positive-probability capture does not depend on `ε`.
  This is the precise sense in which `MixedMC` is "`ε`·random + `(1-ε)`·Mullin": it is the
  **positive-probability** statement. Almost-sure capture (`RandomVariant.CapturesAS`) is
  stronger and is not addressed here.
* `mixedMC_iff_no_trap` — there is no **trap**: no set of integers containing `2`, closed
  under `m ↦ m·p` for primes `p ∣ m + 1`, and avoiding `m ≡ -1 (mod q)` (`IsTrap`).
* `mixedMC_iff_exists_untrapped_node` — some node of the tree is itself not trapped.

## 2. Escape from cosets, from the tree's own induction hypothesis

`ReachableSets.reachableEver_not_in_coset` needs Mullin's conjecture below `q` for the
*greedy* sequence and `q` absent from it. `reachableEver_not_in_coset_of_mixedMCBelow`
replaces both by the statement's own induction hypothesis: if `MixedMC r` holds for all
primes `r < q` and fails at `q`, the residues of the tree's nodes lie in no coset of a proper
subgroup of `(ℤ/q)ˣ`.

No unconditional version is proved, and none can come from residues alone: when every Euclid
number met is prime the residue evolves by the autonomous map `c ↦ c(c+1)`, whose orbit of
`2` avoids `-1` for many `q` (`EM/Population/FeedbackSelection.lean`). Any proof must use
that actual Euclid numbers have several prime factors in different classes.

## 3. What to assume instead of `TreeSieveDecay`

`TreeSieveDecay q` is flagged as probably false. Its weakening `TreeSieveDecayHitting q` is
not known to be false, but `treeSieveDecayHitting_iff_no_trapped_seed` shows its threshold
is illusory: it is equivalent to "**no** squarefree seed `≥ 2` coprime to `q` is trapped".
So `treeSieveDecayHitting_implies_mixedMC` is an instantiation at the seed `2`, not a
reduction.

The **detour ladder** grades `MixedMC` instead of generalising it. A *detour* is a step that
does not take the least prime factor; `HitsWithin d q` says some branch with at most `d`
detours reaches a node `≡ -1 (mod q)`.

* `hitsWithin_zero_iff` — level `0` is "`q` divides some greedy Euclid number".
* `hitsWithin_zero_of_mem_seq` — implied by `q` occurring in the Euclid–Mullin sequence.
* `mixedMC_iff_exists_hitsWithin` — `MixedMC q` is the union of the levels.
* `hitsWithin_one_of_factor` — level `1` holds as soon as one greedy Euclid number
  `prod n + 1` has a prime factor `ℓ` with `prod n · ℓ ≡ -1 (mod q)`.

Each level is still a statement about specific integers.
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

namespace MixedTree

/-! ## Part 1: canonical forms -/

section Canonical

/-- `MixedMC q` is reachability of `-1` in the Euclid tree from `2`. -/
theorem mixedMC_iff_reachable {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    MixedMC q ↔ (-1 : ZMod q) ∈ reachableEver q 2 :=
  (pure_random_mc_iff_mixed_mc q).symm.trans (pure_random_mc_iff_reachable hq hq3)

/-- **Positive-probability form.** For any selection kernel with full support, `MixedMC q`
    holds iff the probability of *not* selecting `q` within some finite horizon is `< 1`. -/
theorem mixedMC_iff_failWeightK_lt_one {w : ℕ → ℕ → ℝ} (hK : IsKernel w) {lam : ℝ}
    (hLB : LowerBounded w lam) (hlam : 0 < lam) {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    MixedMC q ↔ ∃ N, failWeightK w q 2 N < 1 := by
  rw [mixedMC_iff_reachable hq hq3]
  constructor
  · exact fun h => failWeightK_lt_one_of_reachable hK hLB hlam hq le_rfl h
  · rintro ⟨N, hN⟩
    by_contra htrap
    exact absurd (failWeightK_eq_one_of_trapped hK hq N 2 (by norm_num) htrap) hN.ne

/-- **`ε`·random + `(1-ε)`·greedy.** For every `0 < ε ≤ 1`, `MixedMC q` holds iff the mixture
    process from `2` selects `q` with positive probability. -/
theorem mixedMC_iff_eps_capture {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {q : ℕ} (hq : q.Prime)
    (hq3 : 3 ≤ q) :
    MixedMC q ↔ ∃ N, failWeightK (epsStepWeight ε) q 2 N < 1 :=
  mixedMC_iff_failWeightK_lt_one (isKernel_epsStepWeight hε.le hε1)
    (lowerBounded_epsStepWeight hε.le hε1) hε hq hq3

/-- Positive-probability capture under the mixture does not depend on `ε ∈ (0, 1]`. -/
theorem eps_capture_indep {ε ε' : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hε' : 0 < ε') (hε'1 : ε' ≤ 1)
    {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    (∃ N, failWeightK (epsStepWeight ε) q 2 N < 1) ↔
      ∃ N, failWeightK (epsStepWeight ε') q 2 N < 1 :=
  (mixedMC_iff_eps_capture hε hε1 hq hq3).symm.trans (mixedMC_iff_eps_capture hε' hε'1 hq hq3)

/-- A **trap** for `q`: a set of integers closed under the children `m ↦ m·p`
    (`p` prime, `p ∣ m + 1`) of the Euclid tree, none of whose members is `≡ -1 (mod q)`. -/
def IsTrap (q : ℕ) (S : Set ℕ) : Prop :=
  (∀ m ∈ S, ¬ q ∣ m + 1) ∧ ∀ m ∈ S, ∀ p : ℕ, p.Prime → p ∣ m + 1 → m * p ∈ S

/-- If `q ∣ m + 1` then `-1` is reachable from `m` at step `0`. -/
theorem reachable_of_dvd_succ {q m : ℕ} (h : q ∣ m + 1) :
    (-1 : ZMod q) ∈ reachableEver q m := by
  have hmod : (m : ZMod q) = -1 := by
    have hc0 : ((m + 1 : ℕ) : ZMod q) = 0 := by rwa [ZMod.natCast_eq_zero_iff]
    have hc1 : (m : ZMod q) + 1 = 0 := by push_cast at hc0; exact hc0
    exact eq_neg_of_add_eq_zero_left hc1
  apply reachableAt_subset_reachableEver q m 0
  rw [reachableAt_zero, ← hmod]
  exact Set.mem_singleton _

/-- Every node of a valid walk started inside a trap stays inside it. -/
theorem walk_mem_of_isTrap {q : ℕ} {S : Set ℕ} (hS : IsTrap q S) {m : ℕ} (hm : 2 ≤ m)
    (hmS : m ∈ S) (σ : MixedSelection) (hv : ValidMixedSelection m σ) (n : ℕ) :
    mixedWalkProd m σ n ∈ S := by
  induction n with
  | zero => exact hmS
  | succ n ih =>
    rw [mixedWalkProd_succ]
    exact hS.2 _ ih _
      (mixedWalkFactor_prime m σ hv n (mixedWalkProd_ge_two m hm σ hv n))
      (mixedWalkFactor_dvd m σ hv n)

/-- **Trapped ⟺ contained in a trap.** The set of trapped starts is the largest trap. -/
theorem not_reachable_iff_exists_trap {q m : ℕ} (hm : 2 ≤ m) :
    (-1 : ZMod q) ∉ reachableEver q m ↔ ∃ S : Set ℕ, IsTrap q S ∧ m ∈ S := by
  constructor
  · intro h
    refine ⟨{n | (-1 : ZMod q) ∉ reachableEver q n}, ⟨?_, ?_⟩, h⟩
    · intro n (hn : (-1 : ZMod q) ∉ reachableEver q n) hdvd
      exact hn (reachable_of_dvd_succ hdvd)
    · intro n (hn : (-1 : ZMod q) ∉ reachableEver q n) p hp hpd
      exact trapped_hereditary hn p hp hpd
  · rintro ⟨S, hS, hmS⟩ hreach
    rw [reachableEver, Set.mem_iUnion] at hreach
    obtain ⟨n, σ, hv, hmod⟩ := hreach
    have hdvd : q ∣ mixedWalkProd m σ n + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [hmod]; ring
    exact hS.1 _ (walk_mem_of_isTrap hS hm hmS σ hv n) hdvd

/-- **Invariant-set form.** `MixedMC q` holds iff no trap for `q` contains `2`. -/
theorem mixedMC_iff_no_trap {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    MixedMC q ↔ ¬ ∃ S : Set ℕ, IsTrap q S ∧ 2 ∈ S := by
  rw [mixedMC_iff_reachable hq hq3, ← not_reachable_iff_exists_trap le_rfl, not_not]

/-- `MixedMC q` holds iff **some** node of the tree from `2` is not trapped. -/
theorem mixedMC_iff_exists_untrapped_node {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    MixedMC q ↔ ∃ σ : MixedSelection, ValidMixedSelection 2 σ ∧
      ∃ n, (-1 : ZMod q) ∈ reachableEver q (mixedWalkProd 2 σ n) := by
  rw [mixedMC_iff_reachable hq hq3]
  constructor
  · intro h
    exact ⟨minFacMixed, minFacMixed_valid 2, 0, by rwa [mixedWalkProd_zero]⟩
  · rintro ⟨σ, hv, n, h⟩
    exact tail_reachable_implies_reachable q 2 σ hv n h

end Canonical

/-! ## Part 2: escape from cosets under the tree's own induction hypothesis -/

section Escape

/-- If `MixedMC q` fails, no node of the tree from `2` is divisible by `q`. -/
theorem node_ne_zero_of_not_mixedMC {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) (hnot : ¬ MixedMC q)
    {σ : MixedSelection} (hv : ValidMixedSelection 2 σ) (n : ℕ) :
    ((mixedWalkProd 2 σ n : ℕ) : ZMod q) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  refine walk_coprime_until_capture hq 2 le_rfl σ hv ?_ n ?_
  · intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  · intro k _ hk
    exact hnot (fun _ => Or.inr ⟨σ, hv, k, hk⟩)

/-- **Ratio escape from the tree's induction hypothesis.** If `MixedMC r` holds for every
    prime `r < q` and fails at `q`, then for every proper subgroup `H` of `(ℤ/q)ˣ` there are
    two nodes of the tree (a parent and a child) whose ratio lies outside `H`. -/
theorem reachableEver_ratio_escape_of_mixedMCBelow (q : ℕ) [Fact (Nat.Prime q)] (hq5 : 5 ≤ q)
    (hbelow : MixedMCBelow q) (hnot : ¬ MixedMC q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ u₁ u₂ : (ZMod q)ˣ, (↑u₁ : ZMod q) ∈ reachableEver q 2 ∧
      (↑u₂ : ZMod q) ∈ reachableEver q 2 ∧ u₁ * u₂⁻¹ ∉ H := by
  have hq : q.Prime := Fact.out
  obtain ⟨r, hr, hrq, hr3, hesc⟩ := prime_residue_escape q hq5 H hH
  rcases hbelow r hr hrq hr with h2 | ⟨σ, hv, k, hk⟩
  · omega
  have h0 := node_ne_zero_of_not_mixedMC hq (by omega) hnot hv k
  have h1 := node_ne_zero_of_not_mixedMC hq (by omega) hnot hv (k + 1)
  refine ⟨Units.mk0 _ h1, Units.mk0 _ h0, ?_, ?_, ?_⟩
  · exact reachableAt_subset_reachableEver q 2 (k + 1) ⟨σ, hv, rfl⟩
  · exact reachableAt_subset_reachableEver q 2 k ⟨σ, hv, rfl⟩
  · have hr0 : ((r : ℕ) : ZMod q) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun hd => absurd (Nat.le_of_dvd hr.pos hd) (by omega)
    have hratio : Units.mk0 _ h1 * (Units.mk0 _ h0)⁻¹ = Units.mk0 ((r : ℕ) : ZMod q) hr0 := by
      rw [mul_inv_eq_iff_eq_mul]
      ext
      simp only [Units.val_mul, Units.val_mk0]
      rw [mixedWalkProd_succ, hk]
      push_cast
      ring
    rw [hratio]
    exact hesc

/-- **Coset impossibility from the tree's induction hypothesis.** Under the hypotheses of
    `reachableEver_ratio_escape_of_mixedMCBelow`, the node residues are contained in no coset
    of a proper subgroup. -/
theorem reachableEver_not_in_coset_of_mixedMCBelow (q : ℕ) [Fact (Nat.Prime q)] (hq5 : 5 ≤ q)
    (hbelow : MixedMCBelow q) (hnot : ¬ MixedMC q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) (g : (ZMod q)ˣ) :
    ¬ (∀ x ∈ reachableEver q 2, ∃ h ∈ H, (x : ZMod q) = ↑(g * h)) := by
  intro hcoset
  obtain ⟨u₁, u₂, hu₁, hu₂, hratio⟩ :=
    reachableEver_ratio_escape_of_mixedMCBelow q hq5 hbelow hnot H hH
  obtain ⟨h₁, hh₁, heq₁⟩ := hcoset (↑u₁) hu₁
  obtain ⟨h₂, hh₂, heq₂⟩ := hcoset (↑u₂) hu₂
  have hu₁_eq : u₁ = g * h₁ := Units.ext heq₁
  have hu₂_eq : u₂ = g * h₂ := Units.ext heq₂
  have : u₁ * u₂⁻¹ = h₁ * h₂⁻¹ := by
    rw [hu₁_eq, hu₂_eq, mul_inv_rev, mul_comm h₂⁻¹ g⁻¹, mul_mul_mul_comm, mul_inv_cancel,
      one_mul]
  exact hratio (this ▸ H.mul_mem hh₁ (H.inv_mem hh₂))

/-- **Induction-ready form**: with `MixedMC` below `q`, either `MixedMC q` holds or the tree
    escapes every coset of every proper subgroup of `(ℤ/q)ˣ`. -/
theorem mixedMC_or_escapes_cosets (q : ℕ) [Fact (Nat.Prime q)] (hq5 : 5 ≤ q)
    (hbelow : MixedMCBelow q) :
    MixedMC q ∨ ∀ (H : Subgroup (ZMod q)ˣ), H ≠ ⊤ → ∀ g : (ZMod q)ˣ,
      ¬ (∀ x ∈ reachableEver q 2, ∃ h ∈ H, (x : ZMod q) = ↑(g * h)) := by
  by_cases h : MixedMC q
  · exact Or.inl h
  · exact Or.inr fun H hH g => reachableEver_not_in_coset_of_mixedMCBelow q hq5 hbelow h H hH g

end Escape

/-! ## Part 3: the uniform hypothesis has no threshold; the detour ladder -/

section Uniform

/-- **The threshold in `TreeSieveDecayHitting` is illusory.** Trapped seeds are closed under
    children, and children are larger, squarefree and coprime to `q`; so one trapped seed
    yields arbitrarily large ones. Hence `TreeSieveDecayHitting q` is equivalent to: no
    squarefree seed `≥ 2` coprime to `q` is trapped. -/
theorem treeSieveDecayHitting_iff_no_trapped_seed {q : ℕ} (hq : q.Prime) :
    TreeSieveDecayHitting q ↔
      ∀ P : ℕ, 2 ≤ P → Squarefree P → Nat.Coprime P q →
        (-1 : ZMod q) ∈ reachableEver q P := by
  constructor
  · rintro ⟨P₀, hP₀⟩ m hm hsf hcop
    by_cases hdeath : ∃ k, (mixedWalkProd m minFacMixed k : ZMod q) = -1
    · obtain ⟨k, hk⟩ := hdeath
      rw [reachableEver, Set.mem_iUnion]
      exact ⟨k, minFacMixed, minFacMixed_valid m, hk⟩
    · push Not at hdeath
      obtain ⟨K, hK⟩ := mixedWalkProd_eventually_large m hm minFacMixed
        (minFacMixed_valid m) P₀
      exact tail_reachable_implies_reachable q m minFacMixed (minFacMixed_valid m) K
        (hP₀ _ hK (mixedWalkProd_squarefree m hm hsf minFacMixed (minFacMixed_valid m) K)
          (mixedWalkProd_coprime_of_no_death q hq m hm hcop minFacMixed
            (minFacMixed_valid m) hdeath K))
  · intro h
    exact ⟨2, fun P hP hsf hcop => h P hP hsf hcop⟩

/-- `TreeSieveDecayHitting q` implies `MixedMC q`: the instance at the seed `2`. -/
theorem treeSieveDecayHitting_implies_mixedMC {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q)
    (h : TreeSieveDecayHitting q) : MixedMC q :=
  (mixedMC_iff_reachable hq hq3).mpr
    ((treeSieveDecayHitting_iff_no_trapped_seed hq).mp h 2 le_rfl Nat.squarefree_two
      ((Nat.coprime_primes Nat.prime_two hq).mpr (by omega)))

end Uniform

section Detours

/-- The number of **detours** among the first `n` steps: steps whose factor is not the least
    prime factor of the current Euclid number. -/
def detourCount (acc : ℕ) (σ : MixedSelection) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun k =>
    mixedWalkFactor acc σ k ≠ (mixedWalkProd acc σ k + 1).minFac).card

theorem detourCount_le (acc : ℕ) (σ : MixedSelection) (n : ℕ) : detourCount acc σ n ≤ n := by
  unfold detourCount
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem detourCount_minFacMixed (acc n : ℕ) : detourCount acc minFacMixed n = 0 := by
  unfold detourCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k _
  simp [mixedWalkFactor_minFac_eq]

/-- A walk with no detour in its first `n` steps is the greedy walk up to step `n`. -/
theorem mixedWalkProd_eq_of_detourCount_eq_zero {acc : ℕ} {σ : MixedSelection} {n : ℕ}
    (h : detourCount acc σ n = 0) :
    ∀ k, k ≤ n → mixedWalkProd acc σ k = mixedWalkProd acc minFacMixed k := by
  unfold detourCount at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hf : mixedWalkFactor acc σ k = (mixedWalkProd acc σ k + 1).minFac :=
      not_not.mp (h (Finset.mem_range.mpr (by omega)))
    rw [mixedWalkProd_succ, mixedWalkProd_succ, hf, mixedWalkFactor_minFac_eq, ih (by omega)]

/-- **Level `d` of the detour ladder**: some branch of the tree from `2` with at most `d`
    detours reaches a node `≡ -1 (mod q)`. -/
def HitsWithin (d q : ℕ) : Prop :=
  ∃ σ : MixedSelection, ValidMixedSelection 2 σ ∧
    ∃ n, q ∣ mixedWalkProd 2 σ n + 1 ∧ detourCount 2 σ n ≤ d

theorem hitsWithin_mono {d d' q : ℕ} (h : d ≤ d') : HitsWithin d q → HitsWithin d' q := by
  rintro ⟨σ, hv, n, hd, hc⟩
  exact ⟨σ, hv, n, hd, hc.trans h⟩

/-- **Level `0`** is: `q` divides some Euclid number of the greedy sequence. -/
theorem hitsWithin_zero_iff (q : ℕ) : HitsWithin 0 q ↔ ∃ n, q ∣ prod n + 1 := by
  constructor
  · rintro ⟨σ, _, n, hd, hc⟩
    refine ⟨n, ?_⟩
    rwa [← mixedWalkProd_two_minFac_eq_prod,
      ← mixedWalkProd_eq_of_detourCount_eq_zero (Nat.le_zero.mp hc) n le_rfl]
  · rintro ⟨n, hn⟩
    exact ⟨minFacMixed, minFacMixed_valid 2, n,
      by rwa [mixedWalkProd_two_minFac_eq_prod], by rw [detourCount_minFacMixed]⟩

/-- A term of the Euclid–Mullin sequence (other than the first) is at level `0`. -/
theorem hitsWithin_zero_of_mem_seq {q n : ℕ} (h : seq (n + 1) = q) : HitsWithin 0 q :=
  (hitsWithin_zero_iff q).mpr ⟨n, h ▸ seq_dvd_succ_prod n⟩

/-- **`MixedMC q` is the union of the levels.** -/
theorem mixedMC_iff_exists_hitsWithin {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    MixedMC q ↔ ∃ d, HitsWithin d q := by
  rw [mixedMC_iff_reachable hq hq3, reachableEver, Set.mem_iUnion,
    ← mixed_hitting_iff_neg_one_reachable]
  constructor
  · rintro ⟨σ, n, hv, hd⟩
    exact ⟨n, σ, hv, n, hd, detourCount_le 2 σ n⟩
  · rintro ⟨d, σ, hv, n, hd, _⟩
    exact ⟨σ, n, hv, hd⟩

/-- **A sufficient condition for level `1`**: one greedy Euclid number `prod n + 1` has a
    prime factor `ℓ` with `prod n · ℓ ≡ -1 (mod q)`. -/
theorem hitsWithin_one_of_factor {q n ℓ : ℕ} (hℓ : ℓ.Prime) (hd : ℓ ∣ prod n + 1)
    (hq : q ∣ prod n * ℓ + 1) : HitsWithin 1 q := by
  let σ : MixedSelection := fun k => if k = n then some ℓ else none
  have hpre : mixedWalkProd 2 σ n = prod n := by
    rw [← mixedWalkProd_two_minFac_eq_prod]
    exact mixedWalkProd_depends_on_prefix 2 σ minFacMixed n
      (fun i hi => by simp [σ, minFacMixed, Nat.ne_of_lt hi])
  have hσn : σ n = some ℓ := by simp [σ]
  have hσk : ∀ k, k ≠ n → σ k = none := fun k hk => by simp [σ, hk]
  have hv : ValidMixedSelection 2 σ := by
    intro k
    by_cases hk : k = n
    · rw [hk, hσn]
      exact ⟨hℓ, by rw [hpre]; exact hd⟩
    · rw [hσk k hk]
      trivial
  refine ⟨σ, hv, n + 1, ?_, ?_⟩
  · rw [mixedWalkProd_succ, mixedWalkFactor_some_eq 2 σ n ℓ hσn, hpre]
    exact hq
  · unfold detourCount
    refine (Finset.card_le_card (?_ : _ ⊆ ({n} : Finset ℕ))).trans (by simp)
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [Finset.mem_singleton]
    by_contra hne
    exact hk.2 (mixedWalkFactor_none_eq_minFac 2 σ k (hσk k hne))

end Detours

end MixedTree
