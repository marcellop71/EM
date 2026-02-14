# Main Results

## The Irreducible Core

> **DynamicalHitting → MullinConjecture** &nbsp; ([`dynamical_hitting_implies_mullin`](../EM/EquidistBootstrap.lean))
>
> If the walk hits −1 whenever the multiplier residues generate (ℤ/qℤ)×,
> then Mullin's Conjecture follows by strong induction.

DynamicalHitting is the sole remaining open hypothesis. The algebraic bootstrap (**PrimeResidueEscape**) is proved elementarily via the identity 2 = (−4)(−2)⁻¹ — no Burgess bound or Chebotarev density theorem is needed.

## The Character Sum Reduction

> **ComplexCharSumBound → MullinConjecture** &nbsp; ([`complex_csb_mc'`](../EM/EquidistSelfCorrecting.lean))
>
> If the walk character sums ∑ χ(w(n)) are o(N) for every non-trivial
> Dirichlet character, MC follows via Fourier inversion.

This single-hypothesis reduction composes three proved bridges: Fourier inversion (character orthogonality → hit count lower bound), walk equidistribution → DH, and the inductive bootstrap.

## Threshold Specialization

> **ThresholdHitting(11) → MC** &nbsp; ([`threshold_11_implies_mullin'`](../EM/EquidistThreshold.lean))
>
> The finite verification (primes 2, 3, 5, 7 from computed seq values)
> discharges FiniteMCBelow(11).

## Proved Reductions

Every arrow is machine-verified (zero sorry):

| Theorem | File | Meaning |
|---------|------|---------|
| `dynamical_hitting_implies_mullin` | EquidistBootstrap | **DH → MC (irreducible core)** |
| `complex_csb_mc'` | EquidistSelfCorrecting | **CCSB → MC (single hypothesis)** |
| `threshold_11_implies_mullin'` | EquidistThreshold | ThresholdHitting(11) → MC |
| `hh_implies_mullin` | MullinConjectures | HittingHypothesis → MC |
| `pe_implies_mullin` | EquidistPreamble | PairEquidistribution → MC |
| `se_mixing_implies_mullin` | MullinGroupCore | SubgroupEscape + Mixing → MC |
| `walk_equidist_mc` | EquidistOrbitAnalysis | WalkEquidistribution → MC |
| `empr_se_implies_mullin` | MullinRotorBridge | EMPR + SE → MC |
| `whp_implies_mullin` | EquidistSieve | WeakHittingPrinciple → MC |

Additional key results:
- `prime_residue_escape` — PRE proved elementarily (no Burgess bound)
- `conjectureA_false` — Conjecture A is **FALSE** (1807 = 13 × 139)
- `whp_iff_hh` — WHP ↔ HH equivalence
- `pre_iff_se` — PRE ↔ SE decomposition
- `concrete_mc_below_11` — MC verified for primes < 11
- `complex_csb_implies_hit_count_lb_proved` — Fourier bridge **PROVED**
- `decorrelation_implies_ped` — Decorrelation → PED **PROVED**
- `noLongRuns_implies_ped` — NoLongRuns(L) → PED **PROVED**
- `walk_telescope_identity` — telescoping identity **PROVED**
- `se_qr_obstruction` — QR obstruction (≤ 1.6% of primes)
- 30 concrete SubgroupEscape instances for primes q ≤ 157
- `scheduled_walk_covers_all` — rotor-router coverage (sorry-free)

## Open Hypotheses

Stated as `def ... : Prop` (clean propositions, not sorry'd theorems):

| Hypothesis | File | Status |
|-----------|------|--------|
| **DynamicalHitting** | EquidistBootstrap | The sole remaining hypothesis |
| **ComplexCharSumBound** | EquidistFourier | Walk char sums o(N) → MC |
| ThresholdHitting(B) | EquidistThreshold | Parametric DH (B=11 suffices) |
| DecorrelationHypothesis | EquidistSelfCorrecting | Multiplier char sums o(N) |
| PositiveEscapeDensity | EquidistSelfCorrecting | Per-char δ-density of escapes |
| BlockRotationEstimate | EquidistSelfCorrecting | Cauchy-Schwarz step |
| NoLongRuns(L) | EquidistSelfCorrecting | No L consec. kernel multipliers |

The analytic chain: Dec → PED ← NoLongRuns(L) →[BRE]→ CCSB →[proved]→ MC.
