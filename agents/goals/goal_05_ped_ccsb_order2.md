# Goal 05: PEDImpliesComplexCSB Restricted to d=2

## Status: REVISITABLE — MOST PROMISING of all 5 goals

## What It Is

`PEDImpliesComplexCSB` is the single most important open Prop in the entire
formalization. It asserts: positive escape density implies the complex character
sum bound. It is the open bridge in the chains:

```
PED → (PEDImpliesComplexCSB) → CCSB → MC
Dec → PED → (PEDImpliesComplexCSB) → CCSB → MC
NoLongRuns(L) → PED → (PEDImpliesComplexCSB) → CCSB → MC
```

For general characters (order d ≥ 3), this is equivalent to BRE, which is
blocked by the phase-alignment counterexample. But for **d = 2** (quadratic
characters), the problem reduces to: *a ±1 sequence with positive density of
sign changes has sublinear partial sums*.

This is the most promising attack because:
1. It's a clean, self-contained analytic statement
2. The d=2 case covers all quadratic characters (Legendre symbols)
3. A proof would close the bridge for roughly half the character sum problem
4. The argument is essentially combinatorial (alternating series), not deep analysis

## What's Already Proved

| Theorem | File | Line | Status |
|---------|------|------|--------|
| `PEDImpliesComplexCSB` (def) | EquidistSelfCorrecting.lean | 98 | open Prop |
| `ped_mc` | EquidistSelfCorrecting.lean | 203 | PROVED (uses PEDImpliesComplexCSB) |
| `complex_csb_mc'` | EquidistSelfCorrecting.lean | ~150 | PROVED |
| `BlockRotationEstimate` (def) | EquidistSelfCorrecting.lean | 432 | open Prop |
| `block_rotation_implies_ped_csb` | EquidistSelfCorrecting.lean | 457 | PROVED (BRE → PEDImpliesComplexCSB) |
| `DPEDImpliesComplexCSB` (def) | EquidistSieveTransfer.lean | 434 | open Prop (more tractable variant) |
| §35 order-2 section | EquidistSelfCorrecting.lean | 558 | partial results |
| Kernel confinement §72 | LargeSieveSpectral.lean | 1009 | documented boundary |

### The PED-CCSB boundary (LargeSieveSpectral.lean:1009-1018)

If `χ(m(n)) = 1` for all n ≥ N₀ (eventual kernel confinement), the walk
character sum grows linearly: `‖∑ χ(w(n))‖ ≈ N`. So CCSB *requires* infinitely
many escapes. PED provides this. The open question is whether escape density
alone gives *cancellation*, not just non-confinement.

### Why d=2 is special

For `orderOf χ = 2`, the character takes values in `{1, -1}`. The walk recurrence
`χ(w(n+1)) = χ(w(n)) · χ(m(n))` means:
- Kernel step (`χ(m(n)) = 1`): walk character unchanged
- Escape step (`χ(m(n)) = -1`): walk character flips sign

The partial sum `S_N = ∑_{n<N} χ(w(n))` is therefore a sum of ±1 values where
sign flips occur at escape steps. PED guarantees ≥ δN flips in [0,N).

**Key insight**: Between consecutive sign flips, the partial sum moves in one
direction. After a flip, it reverses. With ≥ δN flips, the sum can't drift
far — it's bounded by the maximum run length between flips.

## What To Pursue

### For lean-formalizer — PRIMARY OBJECTIVE

This is the highest-priority formalization target. The proof strategy:

#### Step 1: Sign-flip lemma

Prove that for order-2 characters, escape = sign flip:
```lean
lemma order2_escape_flips_sign
    (hord : orderOf χ = 2) (n : ℕ)
    (hesc : χ (emMultUnit q hq hne n) ≠ 1) :
    (χ (emWalkUnit q hq hne (n + 1)) : ℂ) =
    -(χ (emWalkUnit q hq hne n) : ℂ) := by
  -- χ(m(n)) ≠ 1 and orderOf χ = 2 implies χ(m(n)) = -1
  -- Then χ(w(n+1)) = χ(w(n)) · χ(m(n)) = χ(w(n)) · (-1) = -χ(w(n))
  sorry
```

#### Step 2: Run-length decomposition

Decompose [0, N) into maximal runs of consecutive kernel steps, separated by
escape steps. With ≥ δN escapes, there are ≥ δN runs.

```lean
/-- Decompose the range into runs between consecutive escapes -/
def escapePositions (q : Nat) (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => χ (emMultUnit q hq hne n) ≠ 1)
```

#### Step 3: Partial sum bound via runs

Within each run (between consecutive escapes at positions e_i and e_{i+1}),
the walk character is constant, so the contribution is ±(e_{i+1} - e_i).
After the escape, the sign flips. The total sum telescopes:

`|S_N| ≤ max_{i} (e_{i+1} - e_i)` (the longest run)

But we don't have a max-run bound from PED alone. Instead, use a weaker argument:

`|S_N| = |∑_i ±(e_{i+1} - e_i)| ≤ ∑_i |e_{i+1} - e_i| - 2·min_i(e_{i+1} - e_i)`

Actually, the cleanest argument uses Cauchy-Schwarz on the runs:

`|S_N|² ≤ (number of runs) · ∑_i (e_{i+1} - e_i)² ≤ K · ∑_i ℓ_i²`

where K ≥ δN is the number of runs and ∑ℓ_i = N. By convexity:
`∑ ℓ_i² ≥ N²/K` (equality when all runs equal), but we need an UPPER bound.

Better approach — **the key trick**: The partial sums of a ±1 sequence with K
sign changes satisfy `|S_N| ≤ N - 2·min(positive steps, negative steps)`.
With K ≥ δN sign changes and total N steps, the minority sign has ≥ δN/2 steps
(each sign change creates a new run of the minority sign). So:
`|S_N| ≤ N - 2·(δN/2) = (1-δ)N`

This gives `|S_N| ≤ (1-δ)N`, which is `≤ εN` only if `1-δ ≤ ε`, i.e., `δ ≥ 1-ε`.
That's too weak — we need `|S_N| = o(N)`, not just `≤ (1-δ)N`.

**Correct approach**: The walk character values are not independent ±1; they are
a **deterministic ±1 sequence determined by the escape positions**. The partial
sum after N steps is:

`S_N = ∑_{n<N} (-1)^{#{escapes in [0,n)}} · χ(w(0))`

So `|S_N| = |∑_{n<N} (-1)^{f(n)}|` where `f(n) = #{escapes in [0,n)}`.

Since f(n) is non-decreasing and f(N) ≥ δN, this is a sum of `(-1)^{f(n)}`
where f increases by ≥ δN over [0,N). The sum telescopes into alternating
blocks:

`S_N = ∑_{j=0}^{K-1} (-1)^j · ℓ_j`

where K ≥ δN is the number of escapes and ℓ_j is the length of the j-th run.
This is an **alternating series** with K ≥ δN terms summing to N.

By the alternating series estimate: `|S_N| ≤ max_j ℓ_j`.

So **|S_N| ≤ max run length**. If we could bound the max run length, we'd be done.
PED alone doesn't bound max run length (a single long run of length (1-δ)N is
consistent with δN escapes clustered at the end).

**Resolution**: PED gives `|S_N| ≤ max run length`, but max run length could be
Θ(N). So PED alone does NOT give o(N) for the partial sum — even for d=2!

Wait — this means PEDImpliesComplexCSB is FALSE even for d=2? No, because the
EM walk is not adversarial. The question is whether the specific EM sequence has
bounded (or sublinear) max run length. This is exactly what `NoLongRuns(L)` gives.

**So the actual target is**: Prove that PED for the EM walk implies NoLongRuns,
or find a weaker condition than NoLongRuns that still gives o(N) sums for d=2.

#### Revised Step 3: PED → sublinear sums via averaging

Even without max-run control, we can get a weaker result. The key observation:
PED holds for ALL sufficiently large N, not just a single N. If there were a run
of length ≥ εN starting at position n₀, then for N = n₀ + εN/2, the escape
density would be depressed. More precisely:

For each N, `|S_N| ≤ max_{run containing N} ℓ_{run}`. If the max run over
[0,N) has length L(N), then `|S_N| ≤ L(N)`.

Claim: If PED holds with density δ, then `L(N)/N → 0` (i.e., max run is o(N)).

Proof: Suppose not. Then there exist ε > 0 and infinitely many N with a run of
length ≥ εN in [0,N). A run of length ≥ εN means ≥ εN consecutive kernel steps.
But PED says ≥ δN escapes in [0,N). So at most N - δN = (1-δ)N kernel steps
total. A single run of ≥ εN kernel steps is consistent with (1-δ)N kernel steps
only if ε ≤ 1-δ. So runs can be at most (1-δ)N.

This gives `|S_N| ≤ (1-δ)N`, the same weak bound as before. NOT o(N).

**Conclusion**: PEDImpliesComplexCSB even for d=2 requires something beyond the
pure alternating-series argument. The missing ingredient is that the EM walk
has additional structure (the multiplicative recurrence) preventing long runs.

#### ACTUAL TARGET for formalization:

Given this analysis, the realistic targets are:

**Target A**: Prove `NoLongRuns(L) → CCSB for order-2 χ` (without PEDImpliesComplexCSB).
This may already be done via `bre_order2_from_noLongRuns`. Check and complete it.

**Target B**: Prove `PED → max run is o(N)` using EM-specific structure.
The key would be: if there's a long kernel run [n₀, n₀+L), then all multipliers
in this range are in ker(χ), meaning the walk is confined. But the walk visits
all of `(Z/qZ)×` (by PRE), so confinement can't last forever. Quantify this
using the `prime_residue_escape` machinery.

**Target C**: Define and prove a `WeakPEDImpliesComplexCSB_order2` that adds
a max-run hypothesis:
```lean
def WeakPED_CCSB_order2 : Prop :=
  PositiveEscapeDensity →
  (∀ q ... χ ... (hord : orderOf χ = 2), ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀,
    max_run_length q χ N ≤ ε * N) →
  ComplexCharSumBound_order2
```

### For literature-scout

1. **Alternating series with controlled gaps.** Search: "alternating series
   partial sums gap control", "Leibniz criterion generalization positive density",
   "cancellation ±1 sequence sign change density".

2. **Random walk on Z/2Z with drift.** The d=2 walk character is a walk on
   {+1, -1}. Search: "random walk two states partial sums", "Markov chain
   ±1 cancellation".

3. **Escape from kernel in multiplicative groups.** The EM-specific structure
   prevents long kernel runs. Search: "multiplicative group orbit escape",
   "smallest prime factor coprime sequence gap", "consecutive values in
   multiplicative subgroup".

4. **Gap bounds for multiplicative sequences mod q.** If `m(n) ∈ ker(χ)` for
   n ∈ [n₀, n₀+L), what bounds L? The kernel is a proper subgroup of `(Z/qZ)×`,
   and the multipliers `m(n) = seq(n+1) mod q` are constrained by the EM
   recurrence. Search: "consecutive smooth numbers modular arithmetic",
   "gap in multiplicative subgroup hits".

### For attack agents

1. **Compute max run lengths empirically.** For q ∈ {3,5,7,11,13} and the
   quadratic character χ, compute the escape positions and the max run length
   between consecutive escapes for N up to 10000. Plot max_run(N)/N to see
   if it → 0.

2. **Compute |S_N| vs max_run(N).** Verify that `|S_N| ≤ max_run(N)` holds
   empirically (it should, by the alternating series argument).

3. **Compare d=2 vs d=3 partial sums.** For q = 7 (which has characters of
   orders 1, 2, 3, 6), compare partial sum growth for order-2 vs order-3
   characters. The d=2 sums should be much smaller.

## Pitfalls to Avoid

- **Do NOT assume PED alone gives o(N) sums for d=2.** As analyzed above, PED
  gives `|S_N| ≤ (1-δ)N` at best. You need EM-specific structure (or NoLongRuns)
  to get o(N). The analysis above explains this in detail.

- **Do NOT try to prove PEDImpliesComplexCSB for general d.** It's equivalent
  to BRE, which is impossible for d≥3. Focus exclusively on d=2.

- **Do NOT confuse the alternating series bound `|S_N| ≤ max_run` with o(N).**
  The bound is tight, but max_run could be Θ(N). The nontrivial part is showing
  max_run = o(N).

- **Be aware of the `NoLongRuns` connection.** The existing `bre_order2_from_noLongRuns`
  already handles the case where max runs are bounded by a constant L. The new
  contribution would be either: (a) showing PED → sublinear max runs using EM
  structure, or (b) proving NoLongRuns directly from PRE or other existing results.

- **Check what's already in §35 (EquidistSelfCorrecting.lean:558-650) before
  writing new code.** Some of this may already be partially formalized.

## Success Criteria

- **Minimum**: Verify and complete `bre_order2_from_noLongRuns` as a clean,
  0-sorry theorem. Document exactly what hypotheses it requires.

- **Medium**: Prove `NoLongRuns → CCSB_order2` as a standalone theorem without
  requiring `PEDImpliesComplexCSB`.

- **Maximum**: Prove `PED → CCSB_order2` using EM-specific structure to bound
  max run lengths. This would partially close PEDImpliesComplexCSB for half the
  character sum problem.

- **Literature**: Find a result bounding consecutive kernel-confined steps in
  the EM walk, or a general result about ±1 sequences with structured sign
  changes.
