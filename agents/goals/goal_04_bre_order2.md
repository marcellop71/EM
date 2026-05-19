# Goal 04: BRE for Order-2 — Close the Full d=2 Chain

## Status: REVISITABLE (d=2 case is tractable, partially done, needs completion)

## What It Is

The **Block Rotation Estimate (BRE)** says: given positive escape density (PED),
the walk character sum is o(N). BRE is confirmed impossible for characters of
order d ≥ 3 (counterexample: all escapes concentrated on a single root of unity).
But for **order-2 characters** (values ±1), escapes always flip the sign, so the
counterexample doesn't apply.

The goal is to close the complete d=2 chain:
```
PED (for order-2 χ) → BRE (for order-2 χ) → CCSB (for order-2 χ)
```

## What's Already Proved

| Theorem | File | Line | Status |
|---------|------|------|--------|
| `BlockRotationEstimate` (def) | EquidistSelfCorrecting.lean | 432 | defined |
| `block_rotation_implies_ped_csb` | EquidistSelfCorrecting.lean | 457 | PROVED |
| BRE impossible for d≥3 | EquidistSelfCorrecting.lean | 908 | documented |
| §35 BRE for order-2 via NoLongRuns | EquidistSelfCorrecting.lean | 558 | partial |
| `bre_order2_from_noLongRuns` | EquidistSelfCorrecting.lean | ~633 | PROVED (conditional on NoLongRuns + PEDImpliesComplexCSB) |
| `PEDImpliesComplexCSB` (def) | EquidistSelfCorrecting.lean | 98 | open Prop |

### The d≥3 impossibility (line 908-914)

> Positive escape density alone does NOT imply the walk character sum is o(N)
> when the character has order d ≥ 3. Counterexample: a walk on Z/3Z that
> alternates between two of the three values (escape density = 1) can have
> walk sum ≈ N/2·(1 + ω) ≠ 0.

### The d=2 opportunity (§35, lines 558-570)

For characters of order 2, the walk character values alternate between +1 and -1
at each escape step. This sign-flip structure means:
- Each escape reverses the running sum direction
- PED guarantees escapes are frequent (at least δ·N in [0,N))
- Frequent sign flips → cancellation → sublinear sums

This is essentially the **alternating series argument**: a ±1 sequence with
positive density of sign changes has sublinear partial sums.

## What To Pursue

### For lean-formalizer

1. **Prove the alternating-series lemma.** This is the core analytic content:
   ```
   theorem alternating_sublinear (s : ℕ → Int) (hs : ∀ n, s n = 1 ∨ s n = -1)
       (δ : ℝ) (hδ : 0 < δ) (N₁ : ℕ)
       (hflip : ∀ N ≥ N₁, δ * N ≤ ((Finset.range N).filter
           (fun n => s (n+1) ≠ s n)).card) :
       ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀,
         |∑ n ∈ Finset.range N, s n| ≤ ε * N
   ```

   Proof sketch: Between consecutive sign flips, the partial sum changes by at
   most the gap length. With ≥ δN flips in [0,N), the average gap is ≤ 1/δ.
   By Cauchy-Schwarz on gap lengths:
   `|∑ s(n)| ≤ max_gap ≤ N/number_of_flips ≤ N/(δN) = 1/δ`
   Wait — that gives a constant bound, which is even better than o(N)!

   Actually: `|partial sum| ≤ max gap between consecutive flips`. If the max gap
   is L, then `|∑_{n<N} s(n)| ≤ L`. And NoLongRuns(L) gives max gap ≤ L.
   So **PED + gap control → bounded (not just sublinear) sums**.

   The subtlety: PED alone doesn't give gap control (long gaps can appear late).
   But PED + BRE for d=2 can be proved directly: the key observation is that
   `|∑_{n<N} s(n)| ≤ (number of runs of same sign) · (max run length)`.
   With δN flips, there are ≥ δN runs, so the sum involves cancellation.

   Formalize:
   ```
   theorem bre_order2 (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
       (hne : ∀ k, seq k ≠ q)
       (χ : (ZMod q)ˣ →* ℂˣ) (hχ : χ ≠ 1) (hord : orderOf χ = 2)
       (δ : ℝ) (hδ : 0 < δ) (N₁ : ℕ)
       (hesc : ∀ N ≥ N₁, δ * N ≤ ↑((Finset.filter
           (fun k => χ (emMultUnit q hq hne k) ≠ 1)
           (Finset.range N)).card)) :
       ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀,
         ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤ ε * N
   ```

2. **Connect to the walk recurrence.** The key identity is
   `χ(w(n+1)) = χ(w(n)) · χ(m(n))` (from `char_walk_recurrence`).
   For order-2 χ: `χ(m(n)) ∈ {1, -1}`. When `χ(m(n)) = -1` (escape),
   the walk character flips sign: `χ(w(n+1)) = -χ(w(n))`.
   When `χ(m(n)) = 1` (kernel), it stays: `χ(w(n+1)) = χ(w(n))`.

   Formalize this sign-flip structure:
   ```
   lemma order2_walk_flip (hord : orderOf χ = 2)
       (hesc : χ (emMultUnit q hq hne n) ≠ 1) :
       (χ (emWalkUnit q hq hne (n+1)) : ℂ) = -(χ (emWalkUnit q hq hne n) : ℂ)
   ```

3. **Derive CCSB for order-2 from BRE for order-2.** This should be a simple
   specialization of `block_rotation_implies_ped_csb` to the order-2 case,
   yielding:
   ```
   theorem ccsb_order2 (hped : PositiveEscapeDensity) : CCSB_order2
   ```
   where `CCSB_order2` restricts CCSB to quadratic characters.

### For literature-scout

1. **Alternating series with random sign changes.** This is a well-studied
   topic in probability. Search: "random sign partial sums", "alternating
   series cancellation", "Rademacher sequence partial sums".

2. **Quadratic character sums along sequences.** For order-2 characters
   (Legendre symbols), there is a rich literature. Search: "Legendre symbol
   sum subsequence", "quadratic character cancellation multiplicative walk",
   "Pólya-Vinogradov for subsequences".

3. **Weyl's inequality for ±1 sequences with positive flip density.** The
   condition "positive density of sign changes" is a form of equidistribution.
   Search: "discrepancy ±1 sequence sign changes", "van der Corput ±1 sums".

### For attack agents

1. **Verify d=2 BRE numerically.** For q ∈ {3,5,7,11,13}, find the unique
   quadratic character χ (Legendre symbol). Compute the walk character sum
   `∑_{n<N} χ(w(n))` and the escape density. Verify the sum is O(1) (or at
   least o(N)).

2. **Compare d=2 vs d≥3 empirically.** For a prime q with characters of order
   3 (e.g., q = 7), compute the same walk character sums. Show that d≥3 sums
   grow faster (confirming the d≥3 impossibility).

## Pitfalls to Avoid

- **Do NOT try to prove BRE for general d.** It's impossible for d ≥ 3
  (documented counterexample at line 908). Focus exclusively on d = 2.

- **Do NOT confuse escape density with gap control.** PED says ≥ δN escapes in
  [0,N), but doesn't bound the maximum gap between consecutive escapes.
  The alternating-series argument needs to handle potentially long gaps.

- **Be careful with the connection between `orderOf χ = 2` and `χ(m) ∈ {1,-1}`.**
  In Lean, `χ(m)` is a value in `ℂˣ`, so `χ(m) = -1` means the Units value
  equals `(-1 : ℂˣ)`. Use existing API for `orderOf` and roots of unity.

- **Do NOT create a new CCSB_order2 definition unless needed.** If CCSB for
  order-2 follows from the existing `ComplexCharSumBound` restricted to
  quadratic characters, just prove it as a theorem, not a new Prop.

## Success Criteria

- A proved `bre_order2` theorem: PED for order-2 χ implies walk character
  sum is o(N), WITHOUT requiring PEDImpliesComplexCSB as a hypothesis. This
  would partially close the open bridge for the most tractable case.
- The alternating-series lemma as a standalone mathematical result.
- Full d=2 chain: PED → BRE(d=2) → CCSB(d=2) proved in Lean with 0 sorry.
