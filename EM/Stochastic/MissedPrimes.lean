import EM.Stochastic.TreeSieveDecay
import EM.Ensemble.UnconditionalPSCD

/-!
# Missed Primes: Forward Invariance and q = 3 Cofinal Capture Opportunities

## Overview

For a starting point `m ≥ 2`, define the **missed-prime set**

  `Miss(m) = {q prime : q coprime to m, (-1 : ZMod q) ∉ reachableEver q m}`

(`missedPrimes` below) — the primes that NO valid mixed walk from `m` can ever
capture. This file proves the structure theory of `Miss` along the factor tree
of `m` (root `m`, children `m·f` for the primes `f ∣ m+1`), and the
unconditional `q = 3` cofinal-opportunities theorem.

## Main results (all UNCONDITIONAL — no new hypotheses)

* `reachableAt_succ_decomp` — walk-shift decomposition: a position reachable in
  `n+1` steps from `m` is reachable in `n` steps from some child `m·f`,
  `f` prime, `f ∣ m+1`.
* `trapped_hereditary` / `missed_primes_forward_invariant` /
  `missedPrimes_child_mono` — the missed-prime set can only GROW along the
  factor tree: trapped is forward-invariant. Equivalently, goodness propagates
  UP: if ANY node of the factor tree of `m` reaches `-1` mod `q`, so does the
  root `m` (`reachableEver_child_subset`).
* `good_child_exists` — if `-1` IS reachable from `m` and `m` is not already at
  `-1`, some child `m·f` still reaches `-1`: goodness can be pushed down a level.
* `three_notMem_missedPrimes` — `3 ∉ Miss(m)` for EVERY `m ≥ 2`: the pointwise
  TSDH(3) content (`tsd_hitting_three_pointwise`), no threshold, no squarefreeness.
* `three_cofinal_capture_opportunities` — **headline**: from EVERY squarefree
  start `m ≥ 2` coprime to `3` and for EVERY horizon `K`, some valid path has a
  capture opportunity for `3` (i.e. `3 ∣ walk + 1`) at a step `≥ K` — unless
  capture is FORCED earlier: at the opportunity node every prime factor of the
  Euclid number is `3`, so ANY selection rule captures `3` there. Either
  disjunct is a win: capture opportunities for `3` are cofinal.
* `three_positive_prob_capture_pointwise` — pointwise (not merely almost-all):
  `PositiveProbCapture 3 m ε` for every `ε > 0` and every squarefree `m ≥ 2`
  coprime to `3`.

## Density companions (`EM/Ensemble/UnconditionalPSCD.lean`)

Per-`q`, the density of squarefree `m` with `q ∈ Miss(m)` tends to `0`
(`almost_all_mixed_hitting_unconditional`); diagonally over all primes
`q ≤ B X` with `B X → ∞` (`almost_all_mixed_hitting_diagonal`); and in
EXPECTATION: `expected_missed_smallprimes_diagonal` (same file) shows the
expected number of missed primes `≤ B X` of a random squarefree starting point
tends to `0`.

## What remains open

* Uniform-in-`q` sieve rates, which would upgrade the diagonal statements to
  density-one GenMixedMC itself ("almost all `m` have `Miss(m) = ∅`").
* Almost-sure (not just positive-probability) capture of `3`: along a path
  with cofinal capture opportunities, the `(1-ε)` process fails all of them
  with "probability" at most `∏ (1 - ε/ω(P_k + 1))`, which tends to `0` iff
  `Σ 1/ω(P_k + 1) = ∞`. So almost-sure capture of `3` needs ONLY an anatomy
  bound on `ω` of Euclid numbers along walks (e.g. `ω(P+1) = O(log P)` along
  a positive-density subsequence suffices) — NOT any new reachability input.
  The reachability side is closed by this file.

## Contents

* Part 1: Selection splicing — `spliceSelection`, walk and validity lemmas,
  `reachableAt_child_lift`
* Part 2: Walk-shift decomposition — `reachableAt_succ_decomp`
* Part 3: Forward invariance of missing — `missedPrimes`,
  `reachableEver_child_subset`, `trapped_hereditary`,
  `missed_primes_forward_invariant`, `missedPrimes_child_mono`
* Part 4: Good children — `good_child_exists`
* Part 5: q = 3 — `three_notMem_missedPrimes`,
  `three_cofinal_capture_opportunities`, `three_positive_prob_capture_pointwise`
* Part 6: Landscape — `missed_primes_landscape`
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Part 1: Selection Splicing

The reusable construction for everything below: given a valid walk `σ` from
`acc` reaching accumulator `P` at step `n`, a prime `f ∣ P + 1`, and a valid
walk `τ` from the child `P·f`, the **spliced selection** follows `σ` for `n`
steps, chooses `f` at step `n`, and then follows `τ`. Its walk is `σ`'s walk
up to step `n`, lands on `P·f` at step `n+1`, and is `τ`'s walk (from `P·f`)
thereafter. All facts are proved through `mixedWalkProd_depends_on_prefix` and
`mixedWalkProd_tail_restart`, never by unfolding `mixedWalkProd` globally. -/

section Splicing

/-- Splice: follow `σ` for the first `n` steps, choose `f` at step `n`, then
    follow `τ` (re-indexed to start at step `n+1`). -/
private def spliceSelection (σ : MixedSelection) (n f : ℕ) (τ : MixedSelection) :
    MixedSelection :=
  fun k => if k < n then σ k else if k = n then some f else τ (k - (n + 1))

/-- A selection satisfying the pointwise validity specification is valid.
    Converts the `match`-form of `ValidMixedSelection` into an equational form
    that is convenient for spliced/shifted selections. -/
private theorem valid_of_spec (acc : ℕ) (σ : MixedSelection)
    (h : ∀ k p, σ k = some p → p.Prime ∧ p ∣ mixedWalkProd acc σ k + 1) :
    ValidMixedSelection acc σ := by
  intro k
  cases hσk : σ k with
  | none => trivial
  | some p => exact h k p hσk

/-- The spliced selection agrees with `σ` below `n`. -/
private theorem splice_prefix (σ : MixedSelection) (n f : ℕ) (τ : MixedSelection)
    {i : ℕ} (hi : i < n) : spliceSelection σ n f τ i = σ i := by
  simp [spliceSelection, hi]

/-- The spliced selection chooses `f` at step `n`. -/
private theorem splice_at_n (σ : MixedSelection) (n f : ℕ) (τ : MixedSelection) :
    spliceSelection σ n f τ n = some f := by
  simp [spliceSelection]

/-- The spliced walk agrees with `σ`'s walk up to step `n`. -/
private theorem splice_walk_le (acc : ℕ) (σ : MixedSelection) (n f : ℕ)
    (τ : MixedSelection) {k : ℕ} (hk : k ≤ n) :
    mixedWalkProd acc (spliceSelection σ n f τ) k = mixedWalkProd acc σ k :=
  mixedWalkProd_depends_on_prefix acc _ σ k
    (fun _ hi => splice_prefix σ n f τ (by omega))

/-- The spliced walk lands on the child `P·f` at step `n+1`. -/
private theorem splice_walk_succ (acc : ℕ) (σ : MixedSelection) (n f : ℕ)
    (τ : MixedSelection) :
    mixedWalkProd acc (spliceSelection σ n f τ) (n + 1) =
    mixedWalkProd acc σ n * f := by
  rw [mixedWalkProd_succ, splice_walk_le acc σ n f τ (le_refl n),
    mixedWalkFactor_some_eq acc (spliceSelection σ n f τ) n f (splice_at_n σ n f τ)]

/-- The tail of the spliced selection from step `n+1` onward IS `τ`. -/
private theorem splice_tail_eq (σ : MixedSelection) (n f : ℕ) (τ : MixedSelection) :
    (fun i => spliceSelection σ n f τ (n + 1 + i)) = τ := by
  funext i
  simp only [spliceSelection]
  rw [if_neg (by omega : ¬(n + 1 + i < n)), if_neg (by omega : ¬(n + 1 + i = n))]
  congr 1
  omega

/-- Beyond step `n+1`, the spliced walk is `τ`'s walk from the child `P·f`. -/
private theorem splice_walk_tail (acc : ℕ) (σ : MixedSelection) (n f : ℕ)
    (τ : MixedSelection) (j : ℕ) :
    mixedWalkProd acc (spliceSelection σ n f τ) (n + 1 + j) =
    mixedWalkProd (mixedWalkProd acc σ n * f) τ j := by
  rw [mixedWalkProd_tail_restart acc (spliceSelection σ n f τ) (n + 1) j,
    splice_walk_succ, splice_tail_eq]

/-- The spliced selection is valid: below `n` by `σ`'s validity (walks agree),
    at `n` because `f` is a prime dividing `P + 1`, beyond `n` by `τ`'s
    validity from the child `P·f` (tail restart). -/
private theorem splice_valid (acc : ℕ) (σ : MixedSelection)
    (hv : ValidMixedSelection acc σ) (n f : ℕ) (hf : f.Prime)
    (hfd : f ∣ mixedWalkProd acc σ n + 1) (τ : MixedSelection)
    (hτ : ValidMixedSelection (mixedWalkProd acc σ n * f) τ) :
    ValidMixedSelection acc (spliceSelection σ n f τ) := by
  apply valid_of_spec
  intro k p hk
  rcases lt_trichotomy k n with hlt | heq | hgt
  · rw [splice_prefix σ n f τ hlt] at hk
    obtain ⟨hp, hd⟩ := valid_random_prime_dvd acc σ hv k p hk
    exact ⟨hp, by rw [splice_walk_le acc σ n f τ (le_of_lt hlt)]; exact hd⟩
  · subst heq
    rw [splice_at_n] at hk
    obtain rfl : f = p := Option.some.inj hk
    exact ⟨hf, by rw [splice_walk_le acc σ k f τ (le_refl k)]; exact hfd⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = n + 1 + j := ⟨k - (n + 1), by omega⟩
    have hk' : τ j = some p := by
      rwa [show spliceSelection σ n f τ (n + 1 + j) = τ j from
        congrFun (splice_tail_eq σ n f τ) j] at hk
    obtain ⟨hp, hd⟩ := valid_random_prime_dvd _ τ hτ j p hk'
    exact ⟨hp, by rw [splice_walk_tail]; exact hd⟩

/-- **Child-to-root lift**: anything reachable in `j` steps from the child
    `P·f` (where `P` is `σ`'s accumulator at step `n` and `f` is a prime
    dividing `P+1`) is reachable in `n + 1 + j` steps from the root. -/
theorem reachableAt_child_lift {q acc : ℕ} {n : ℕ} {σ : MixedSelection}
    (hv : ValidMixedSelection acc σ) {f : ℕ} (hf : f.Prime)
    (hfd : f ∣ mixedWalkProd acc σ n + 1) {j : ℕ} {x : ZMod q}
    (hx : x ∈ reachableAt q (mixedWalkProd acc σ n * f) j) :
    x ∈ reachableAt q acc (n + 1 + j) := by
  obtain ⟨τ, hτ, hw⟩ := hx
  exact ⟨spliceSelection σ n f τ, splice_valid acc σ hv n f hf hfd τ hτ,
    by rw [splice_walk_tail]; exact hw⟩

end Splicing

/-! ## Part 2: Walk-Shift Decomposition

The converse direction: every `(n+1)`-step reachable position from `m`
decomposes through some child `m·f`. Together with Part 1, the reachable sets
of `m` are exactly the union over children of the children's reachable sets
(shifted by one step), plus the root position itself. -/

section Decomposition

/-- **Walk-shift decomposition**: a position reachable in `n+1` steps from
    `m ≥ 2` is reachable in `n` steps from some child `m·f` with `f` prime,
    `f ∣ m+1`. The witness is the first factor of the witnessing walk; the
    shifted selection `i ↦ σ(1+i)` is valid from `m·f` by
    `mixedWalkProd_tail_restart`. -/
theorem reachableAt_succ_decomp {q m : ℕ} (hm : 2 ≤ m) {n : ℕ} {x : ZMod q}
    (hx : x ∈ reachableAt q m (n + 1)) :
    ∃ f, f.Prime ∧ f ∣ m + 1 ∧ x ∈ reachableAt q (m * f) n := by
  obtain ⟨σ, hv, hw⟩ := hx
  set f := mixedWalkFactor m σ 0 with hf_def
  have h0 : mixedWalkProd m σ 0 = m := mixedWalkProd_zero m σ
  have hfp : f.Prime := mixedWalkFactor_prime m σ hv 0 (by rw [h0]; exact hm)
  have hfd : f ∣ m + 1 := by
    have := mixedWalkFactor_dvd m σ hv 0
    rwa [h0] at this
  have h1 : mixedWalkProd m σ 1 = m * f := by
    have := mixedWalkProd_succ m σ 0
    rw [h0] at this
    exact this
  -- The shifted walk from the child agrees with the original walk, one step later
  have hshift : ∀ k, mixedWalkProd (m * f) (fun i => σ (1 + i)) k =
      mixedWalkProd m σ (1 + k) := by
    intro k
    rw [mixedWalkProd_tail_restart m σ 1 k, h1]
  have hv' : ValidMixedSelection (m * f) (fun i => σ (1 + i)) := by
    apply valid_of_spec
    intro k p hk
    obtain ⟨hp, hd⟩ := valid_random_prime_dvd m σ hv (1 + k) p hk
    exact ⟨hp, by rw [hshift k]; exact hd⟩
  refine ⟨f, hfp, hfd, fun i => σ (1 + i), hv', ?_⟩
  rw [hshift n, Nat.add_comm 1 n]
  exact hw

end Decomposition

/-! ## Part 3: Forward Invariance of Missing

The missed-prime set can only GROW along the factor tree — trapped is
forward-invariant; equivalently, goodness propagates UP: if any tree node
reaches `q`, so does the root. -/

section ForwardInvariance

/-- The **missed-prime set** of a starting point `m`: primes `q` coprime to
    `m` from which `-1` is never tree-reachable mod `q` — the primes that no
    valid mixed walk from `m` can ever capture. -/
def missedPrimes (m : ℕ) : Set ℕ :=
  {q | q.Prime ∧ Nat.Coprime m q ∧ (-1 : ZMod q) ∉ reachableEver q m}

/-- **Goodness propagates up**: everything ever-reachable from a child `m·f`
    (`f` prime, `f ∣ m+1`) is ever-reachable from `m`. -/
theorem reachableEver_child_subset (q m : ℕ) {f : ℕ} (hf : f.Prime)
    (hfd : f ∣ m + 1) :
    reachableEver q (m * f) ⊆ reachableEver q m := by
  intro x hx
  rw [reachableEver, Set.mem_iUnion] at hx ⊢
  obtain ⟨j, hj⟩ := hx
  have hfd' : f ∣ mixedWalkProd m minFacMixed 0 + 1 := by
    rw [mixedWalkProd_zero]; exact hfd
  have hj' : x ∈ reachableAt q (mixedWalkProd m minFacMixed 0 * f) j := by
    rw [mixedWalkProd_zero]; exact hj
  exact ⟨0 + 1 + j, reachableAt_child_lift (minFacMixed_valid m) hf hfd' hj'⟩

/-- **Heredity of missing**: if `-1` is not reachable mod `q` from `m`, it is
    not reachable from any child `m·f` either — trapped is forward-invariant
    along the factor tree. Contrapositive of `reachableEver_child_subset`. -/
theorem trapped_hereditary {q m : ℕ} (htrap : (-1 : ZMod q) ∉ reachableEver q m)
    (f : ℕ) (hf : f.Prime) (hfd : f ∣ m + 1) :
    (-1 : ZMod q) ∉ reachableEver q (m * f) :=
  fun hmem => htrap (reachableEver_child_subset q m hf hfd hmem)

/-- **Forward invariance of the missed-prime set**: the missed-prime set can
    only GROW along the factor tree — trapped is forward-invariant;
    equivalently, goodness propagates UP: if any tree node reaches `q`, so
    does the root.

    Packaged form: if the prime `q` is coprime to `m` and missed from `m`,
    then for every valid child `m·f` (`f` prime, `f ∣ m+1`): `q` remains
    coprime to `m·f`, and `q` is missed from `m·f`. (`f ≠ q` is automatic:
    `f = q` with `f ∣ m+1` would put `(m : ZMod q) = -1` in the reachable set
    at step `0`, contradicting trappedness.) -/
theorem missed_primes_forward_invariant {q m : ℕ} (hq : q.Prime)
    (hcop : Nat.Coprime m q) (htrap : (-1 : ZMod q) ∉ reachableEver q m)
    (f : ℕ) (hf : f.Prime) (hfd : f ∣ m + 1) :
    Nat.Coprime (m * f) q ∧ (-1 : ZMod q) ∉ reachableEver q (m * f) := by
  have hfq : f ≠ q := by
    intro hfe
    apply htrap
    have hqd : q ∣ m + 1 := hfe ▸ hfd
    have hmod : (m : ZMod q) = -1 := by
      have hc0 : ((m + 1 : ℕ) : ZMod q) = 0 := by rwa [ZMod.natCast_eq_zero_iff]
      have hc1 : (m : ZMod q) + 1 = 0 := by push_cast at hc0; exact hc0
      exact eq_neg_of_add_eq_zero_left hc1
    apply reachableAt_subset_reachableEver q m 0
    rw [reachableAt_zero, ← hmod]
    exact Set.mem_singleton _
  exact ⟨(hcop.symm.mul_right ((Nat.coprime_primes hf hq).mpr hfq).symm).symm,
    trapped_hereditary htrap f hf hfd⟩

/-- Set form of forward invariance: `Miss(m) ⊆ Miss(m·f)` for every valid
    child. The missed-prime set is monotone down the factor tree. -/
theorem missedPrimes_child_mono {m f : ℕ} (hf : f.Prime) (hfd : f ∣ m + 1) :
    missedPrimes m ⊆ missedPrimes (m * f) := by
  rintro q ⟨hq, hcop, htrap⟩
  obtain ⟨hcop', htrap'⟩ := missed_primes_forward_invariant hq hcop htrap f hf hfd
  exact ⟨hq, hcop', htrap'⟩

end ForwardInvariance

/-! ## Part 4: Good Children -/

section GoodChild

/-- **Good child exists**: if `-1` is reachable mod `q` from `m ≥ 2` and `m`
    is not already at position `-1`, then some child `m·f` (`f` prime,
    `f ∣ m+1`) still reaches `-1`. Goodness can always be pushed one level
    down the factor tree until the walk actually stands on `-1`. -/
theorem good_child_exists {q m : ℕ} (hm : 2 ≤ m)
    (hmem : (-1 : ZMod q) ∈ reachableEver q m) (hne : (m : ZMod q) ≠ -1) :
    ∃ f, f.Prime ∧ f ∣ m + 1 ∧ (-1 : ZMod q) ∈ reachableEver q (m * f) := by
  rw [reachableEver, Set.mem_iUnion] at hmem
  obtain ⟨n, hn⟩ := hmem
  cases n with
  | zero =>
    rw [reachableAt_zero] at hn
    exact absurd (Set.mem_singleton_iff.mp hn).symm hne
  | succ n' =>
    obtain ⟨f, hf, hfd, hx⟩ := reachableAt_succ_decomp hm hn
    exact ⟨f, hf, hfd, reachableAt_subset_reachableEver q (m * f) n' hx⟩

end GoodChild

/-! ## Part 5: q = 3 — Never Missed, and Cofinal Capture Opportunities -/

section ThreeCofinal

/-- **3 is never missed**: `3 ∉ Miss(m)` for every `m ≥ 2`. Pointwise, with
    no squarefreeness and no size threshold — from
    `tsd_hitting_three_pointwise`. -/
theorem three_notMem_missedPrimes (m : ℕ) (hm : 2 ≤ m) : 3 ∉ missedPrimes m := by
  rintro ⟨-, hcop, htrap⟩
  exact htrap (tsd_hitting_three_pointwise m hm hcop)

/-- From `-1 ∈ reachableAt q acc n`, extract a valid walk with
    `q ∣ walk(n) + 1` at the SAME step `n` (the step-indexed direction of
    `mixed_hitting_iff_neg_one_reachable`). -/
private theorem reachableAt_neg_one_dvd {q acc n : ℕ}
    (h : (-1 : ZMod q) ∈ reachableAt q acc n) :
    ∃ σ : MixedSelection, ValidMixedSelection acc σ ∧
      q ∣ mixedWalkProd acc σ n + 1 := by
  obtain ⟨σ, hv, hmod⟩ := h
  refine ⟨σ, hv, ?_⟩
  have h1 : (mixedWalkProd acc σ n : ZMod q) + 1 = 0 := by rw [hmod]; ring
  have h2 : ((mixedWalkProd acc σ n + 1 : ℕ) : ZMod q) = 0 := by
    push_cast
    exact h1
  rwa [ZMod.natCast_eq_zero_iff] at h2

/-- **q = 3 cofinal capture opportunities (unconditional)**: from EVERY
    squarefree start `m ≥ 2` coprime to `3`, and for EVERY horizon `K`, there
    is a valid path with a capture opportunity for `3` (i.e. `3 ∣ walk + 1`)
    at some step `≥ K` — unless capture is FORCED earlier: every prime factor
    of the opportunity's Euclid number is `3` (the candidate set is `{3}`, so
    ANY selection rule captures `3` there). Either disjunct is a win for
    capturing `3`.

    Proof by induction on `K`. Base: pointwise TSDH(3) gives an opportunity at
    some step `≥ 0`. Step: given an opportunity `(σ, n)` with `K ≤ n`, either
    every prime factor of `walk(n)+1` is `3` (forced disjunct), or some prime
    `f ≠ 3` divides `walk(n)+1`; the child `P·f` is `≥ 2` and coprime to `3`
    (`3 ∣ P+1` forces `3 ∤ P`, and `f ≠ 3` is prime), so pointwise TSDH(3)
    applies to it, and splicing the resulting walk after `(σ, n, f)` yields an
    opportunity at step `n + 1 + j ≥ K + 1`. -/
theorem three_cofinal_capture_opportunities (m : ℕ) (hm : 2 ≤ m)
    (_hsf : Squarefree m) (hcop : Nat.Coprime m 3) (K : ℕ) :
    ∃ (σ : MixedSelection) (n : ℕ), ValidMixedSelection m σ ∧
      3 ∣ mixedWalkProd m σ n + 1 ∧
      (K ≤ n ∨ ∀ f, f.Prime → f ∣ mixedWalkProd m σ n + 1 → f = 3) := by
  induction K with
  | zero =>
    have hreach := tsd_hitting_three_pointwise m hm hcop
    rw [reachableEver, Set.mem_iUnion] at hreach
    obtain ⟨n, hn⟩ := hreach
    obtain ⟨σ, hv, hdvd⟩ := reachableAt_neg_one_dvd hn
    exact ⟨σ, n, hv, hdvd, Or.inl (Nat.zero_le n)⟩
  | succ K ih =>
    obtain ⟨σ, n, hv, hdvd, hK⟩ := ih
    rcases hK with hKn | hforced
    · by_cases hall : ∀ f, f.Prime → f ∣ mixedWalkProd m σ n + 1 → f = 3
      · -- Capture is forced at the existing opportunity: reuse it.
        exact ⟨σ, n, hv, hdvd, Or.inr hall⟩
      · -- Some prime f ≠ 3 divides walk(n)+1: splice a fresh TSDH(3) walk
        -- from the child walk(n)·f after step n.
        push Not at hall
        obtain ⟨f, hf, hfd, hf3⟩ := hall
        have h3 : Nat.Prime 3 := by decide
        have hP2 : 2 ≤ mixedWalkProd m σ n := mixedWalkProd_ge_two m hm σ hv n
        have hPf2 : 2 ≤ mixedWalkProd m σ n * f := by
          have := hf.two_le
          nlinarith
        -- The child is coprime to 3: 3 | P+1 forces 3 ∤ P, and f ≠ 3 is prime.
        have hcopPf : Nat.Coprime (mixedWalkProd m σ n * f) 3 := by
          have hP3 : Nat.Coprime 3 (mixedWalkProd m σ n) :=
            h3.coprime_iff_not_dvd.mpr (fun hdvd3 => by omega)
          have hf3' : Nat.Coprime 3 f :=
            h3.coprime_iff_not_dvd.mpr (fun hdvd3 =>
              hf3 (((Nat.prime_dvd_prime_iff_eq h3 hf).mp hdvd3).symm))
          exact (hP3.mul_right hf3').symm
        have hreach := tsd_hitting_three_pointwise (mixedWalkProd m σ n * f)
          hPf2 hcopPf
        rw [reachableEver, Set.mem_iUnion] at hreach
        obtain ⟨j, hj⟩ := hreach
        obtain ⟨τ, hτ, hjdvd⟩ := reachableAt_neg_one_dvd hj
        refine ⟨spliceSelection σ n f τ, n + 1 + j,
          splice_valid m σ hv n f hf hfd τ hτ, ?_, Or.inl (by omega)⟩
        rw [splice_walk_tail]
        exact hjdvd
    · exact ⟨σ, n, hv, hdvd, Or.inr hforced⟩

/-- **Pointwise positive-probability capture of 3**: for EVERY squarefree
    `m ≥ 2` coprime to `3` and every `ε > 0`, the `(1-ε)·minFac + ε·random`
    process captures `3` with positive probability — pointwise, not merely for
    almost all starting points. Composes `tsd_hitting_three_pointwise` with
    `reachable_implies_positive_prob_capture`. -/
theorem three_positive_prob_capture_pointwise (m : ℕ) (hm : 2 ≤ m)
    (_hsf : Squarefree m) (hcop : Nat.Coprime m 3) {ε : ℝ} (hε : 0 < ε) :
    PositiveProbCapture 3 m ε :=
  reachable_implies_positive_prob_capture (by decide : Nat.Prime 3) hm hε
    (tsd_hitting_three_pointwise m hm hcop)

end ThreeCofinal

/-! ## Part 6: Landscape -/

section Landscape

/-- **Missed-primes landscape**: summary of the structure theory.

    1. missedPrimes_child_mono — Miss(m) ⊆ Miss(m·f): missing is
       forward-invariant along the factor tree (goodness propagates up)
    2. three_notMem_missedPrimes — 3 is never missed (pointwise TSDH(3))
    3. three_cofinal_capture_opportunities — capture opportunities for 3 are
       cofinal along valid paths (or capture is forced) -/
theorem missed_primes_landscape (m : ℕ) (hm : 2 ≤ m) (hsf : Squarefree m)
    (hcop : Nat.Coprime m 3) :
    -- 1. Forward invariance of the missed-prime set
    (∀ f, f.Prime → f ∣ m + 1 → missedPrimes m ⊆ missedPrimes (m * f))
    ∧
    -- 2. 3 is never missed
    (3 ∉ missedPrimes m)
    ∧
    -- 3. Cofinal capture opportunities for 3
    (∀ K, ∃ (σ : MixedSelection) (n : ℕ), ValidMixedSelection m σ ∧
      3 ∣ mixedWalkProd m σ n + 1 ∧
      (K ≤ n ∨ ∀ f, f.Prime → f ∣ mixedWalkProd m σ n + 1 → f = 3)) :=
  ⟨fun _ hf hfd => missedPrimes_child_mono hf hfd,
   three_notMem_missedPrimes m hm,
   fun K => three_cofinal_capture_opportunities m hm hsf hcop K⟩

end Landscape
