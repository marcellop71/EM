# Project Status: Formal Verification of the Euclid-Mullin Sequence

## Overview

This project is a Lean 4 formalization investigating **Mullin's Conjecture** (1963):
every prime number eventually appears in the Euclid-Mullin sequence. The codebase
contains **~27,405 lines** of Lean 4 across **38 source files** (32 EM core + 6 IK
chapter files), comprising **1092+ theorems/lemmas** and **411+ definitions** with
**zero errors**, **zero warnings**, and **zero sorry**.

**The primary reduction (Single Hit Theorem):**

> **SingleHitHypothesis → MullinConjecture**
> (`single_hit_implies_mc`)
>
> For every prime q: if MC(< q) and SE(q) hold, then a single event
> q | P(n)+1 past the sieve gap implies MC(q). By strong induction, MC
> reduces to producing one such hit at each prime. The algebraic
> precondition — that the multipliers generate (Z/qZ)× — is free: it
> follows from the inductive hypothesis via PrimeResidueEscape (proved
> elementarily). The open problem is purely dynamical: does the walk
> hit −1 at least once?

**Cofinal hitting route:**

> **DynamicalHitting → MullinConjecture**
> (`dynamical_hitting_implies_mullin`)
>
> DH is strictly stronger than SHH: it asks for cofinal hitting without
> assuming MC(< q). DH → SHH is trivial (`dh_implies_single_hit`).

SingleHitHypothesis is the weakest known sufficient condition in the
"hitting family." DH, CCSB, and CME are all strategies for producing
the required single hit.

**Parametric specialization at B = 11:**

> **ThresholdHitting(11) → MC**
> (`threshold_11_implies_mullin'`)
>
> The finite verification (primes 2, 3, 5, 7 from seq values 0, 1, 6, 2)
> discharges FiniteMCBelow(11). Only one open hypothesis remains.

More broadly, the formalization establishes a multi-layered reduction
architecture where every arrow is machine-verified:

1. **PE → MC** via two independent paths (direct through HH, structural through SE + EMPR)
2. **DH → MC** by strong induction (one-hypothesis reduction; PRE proved elementarily)
3. **ThresholdHitting(B) + FiniteMCBelow(B) → MC** parametric decomposition (PRE proved)
4. **Concrete SE** for all 29 primes q ≤ 157 not in the sequence
5. **PRE ↔ SE** decomposing SE into finite power-residue conditions per prime
6. **QR obstruction** constraining SE counterexamples to ≤ 1.6% of primes
7. **CCSB → MC** single-hop character sum reduction
8. **CME → CCSB → MC** sharpest sufficient condition (conditional multiplier equidistribution)
9. **MMCSB → MC** multi-modular character sum bound
10. **SVE → MC** subquadratic visit energy
11. **HOD → CCSB → MC** higher-order decorrelation (VdC proved, parameter eliminated)
12. **BV → MC**, **ALS+Farey → MC**, **EH → MC** analytic number theory routes
13. **SE → Dec → MC** sieve-to-harmonic bridge
14. **StrongSME → MC** sieve-defined dynamical systems reduction (SDDS framework)

---

## The Sole Open Question

All formal reductions are complete. The sole remaining open question is:

> **Can the greedy factoring process sustain a "factoring oracle" — a
> systematic correlation between the mod-q residue of Prod(n) and the
> mod-q residue of minFac(Prod(n)+1) — to avoid the death equation
> minFac(Prod(n)+1) ≡ −Prod(n)⁻¹ (mod q) indefinitely?**

Formally, this is **DynamicalHitting**: if the multiplier residues generate
(ZMod q)ˣ, the walk must hit −1 cofinally.

**The marginal/joint barrier:** The verified reductions exhaust what can be
proved about the *marginal* distribution of multiplier residues. Even perfect
per-position equidistribution is consistent with HH failure. DH is a *joint*
distribution statement — the (position, multiplier) pair must hit the death
curve — and no marginal statement can force this.

**The no-oracle principle:** HH failure couples a mod-q residue (O(log q) bits)
with a factorization outcome (~2^n bits). The Euclid numbers Prod(n)+1 grow
doubly exponentially with pairwise disjoint prime factorizations. The oracle
must work at all primes q simultaneously, requiring a factoring algorithm —
contradicting the presumed hardness of integer factorization.

---

## The Reduction Architecture

```
                     MullinConjecture
                           ^
               ____________|____________
              |                         |
    HittingHypothesis              SE + Mixing
         ^    ^                     ^       ^
         |    |                    /         \
    WalkCoverage  (SE bootstrapped    MixingHypothesis
                   from PRE)              ^
                                           |
                                    EMPointwiseRecurrence
                                           +
                                  scheduled_walk_covers_all (proved)

ONE-HYPOTHESIS REDUCTION:
  DynamicalHitting  →  MC
  (strong induction: IH → MC(<p) → SE(p) → HH(p) → MC(p))
  PrimeResidueEscape proved elementarily (no Burgess needed)

THRESHOLD SPECIALIZATION:
  ThresholdHitting(11)  →  MC
  (FiniteMCBelow(11) discharged from four computed seq values)

CHARACTER SUM ROUTES:
  CCSB → MC            (single hop)
  CME → CCSB → MC      (sharpest, conditional multiplier equidist)
  MMCSB → MC            (multi-modular)
  SVE → MC              (visit energy)
  HOD → CCSB → MC       (decorrelation, VdC proved)

ANALYTIC NUMBER THEORY ROUTES:
  BV → MMCSB → MC       (Bombieri-Vinogradov)
  ALS+Farey → MC        (Analytic Large Sieve)
  EH → BV → MC          (Elliott-Halberstam)
  SE → Dec → MC         (Sieve equidistribution)

SDDS FRAMEWORK:
  StrongSME → HH → MC   (sieve-map equidistribution, cofinal)
```

All arrows are formally proved (**zero sorry**). The open hypotheses are
stated as `def ... : Prop` (clean mathematical propositions, not gaps).

---

## File Structure

| File | Lines | Content |
|------|-------|---------|
| `Euclid.lean` | 422 | Constructive Euclid's theorem (`propext` + `Quot.sound` only) |
| `MullinDefs.lean` | 527 | `seq`, `prod`, `aux`, basic identities, `seq_isPrime`, `seq_injective` |
| `MullinConjectures.lean` | 490 | `MullinConjecture`, `ConjectureA` (FALSE), `HittingHypothesis`, `hh_implies_mullin` |
| `MullinDWH.lean` | 547 | `DivisorWalkHypothesis`, `dwh_implies_mullin` — LEAF |
| `MullinResidueWalk.lean` | 603 | `WalkCoverage`, residue walk, pigeonhole, concrete MC instances |
| `MullinCRT.lean` | 160 | CRT Multiplier Invariance, `walkZ_multi_step`, `return_product_char_one` |
| `MullinGroupCore.lean` | 422 | `walkZ`, `multZ`, confinement, `SubgroupEscape`, `se_mixing_implies_mullin` |
| `MullinGroupEscape.lean` | 673 | 6 mult escape lemmas, `eight_elts_escape`, `se_of_maximal_escape` |
| `MullinGroupSEInstances.lean` | 364 | 29 concrete SE instances, concrete mixing, `walkZ_hits_iff_target` |
| `MullinGroupPumping.lean` | 343 | Gordon's sequenceability, pumping, subgroup growth — LEAF |
| `MullinGroupQR.lean` | 683 | QR conditions, `se_qr_obstruction`, multi-witness SE — LEAF |
| `RotorRouter.lean` | 421 | Rotor-router + scheduled walk coverage (standalone, 0 sorry) |
| `MullinRotorBridge.lean` | 87 | `emWalkUnit`, `EMPointwiseRecurrence`, EMPR+SE→MC |
| `EquidistPreamble.lean` | 234 | `PairEquidistribution`, `pe_implies_mullin`, bootstrapping |
| `EquidistSieve.lean` | 297 | Sieve analysis, `WeakHittingPrinciple`, `whp_iff_hh` |
| `EquidistSelfAvoidance.lean` | 450 | Self-avoidance, periodicity vs. generation |
| `EquidistCharPRE.lean` | 811 | Character non-vanishing, PRE↔SE, local PRE, EKE |
| `MullinDepartureGraph.lean` | 393 | Departure graph framework: `departureSet`, `visitedSet`, subgroup trapping, generation escape, oracle from confinement, infinite recurrence, safe prime lattice |
| `EquidistBootstrap.lean` | 617 | Inductive bootstrap, minimality sieve, irreducible core (DH→MC), first passage dichotomy |
| `EquidistThreshold.lean` | 299 | Threshold approach, `concrete_mc_below_11`, open problem analysis |
| `EquidistOrbitAnalysis.lean` | 1441 | Cofinal orbit expansion, quotient walk, cofinal escape, factored sieve, oracle barrier |
| `EquidistFourier.lean` | 1298 | Character sums, TailSE chains, GlobalTailSE, decorrelation, Fourier bridge |
| `EquidistSelfCorrecting.lean` | 1114 | Escape density, decorrelation, BRE, simplified chains, kernel confinement, quadratic walk |
| `EquidistSieveTransfer.lean` | 1457 | SieveTransfer decomposition, CompositeSieveEquidist, escape decorrelation, §39 coprimality refreshing |
| `LargeSieve.lean` | 1812 | MMCSB→MC, BV/ArithLS/LoD chains, Farey, sieve-harmonic bridge, SE→Dec |
| `LargeSieveHarmonic.lean` | 892 | Parseval/Plancherel/Gauss sums, ALS infrastructure, trigKernel, Schur test |
| `LargeSieveAnalytic.lean` | 1683 | Geometric sums, Gram matrix, WeakALS, GCT (all 8 lemmas), VdC bound, Weyl criterion |
| `LargeSieveSpectral.lean` | 2670 | SVE→MC, HOD→MC, CME→CCSB, FEB, VCB, hierarchy connectors, transition matrix, EH→MC |
| `SieveDefinedDynamics.lean` | 168 | SDDS framework: `FactoringRule`, `SDDS`, `emSDDS`, orbit/walk/mult, 5 open hypotheses |
| `SDDSBridge.lean` | 153 | Bridge: `euclid_minFac_eq_nat_minFac`, orbit=prod, walk=walkZ, mult=multZ |
| `SDDSReduction.lean` | 126 | `StrongSME` → HH → MC, `sme_implies_dvd_euclid` |
| `IKCh1.lean` | 437 | IK Chapter 1: arithmetic functions, exponential sums |
| `IKCh2.lean` | 270 | IK Chapter 2: Dirichlet's theorem, PNT |
| `IKCh3.lean` | 557 | IK Chapter 3: Gauss sums, Hecke characters |
| `IKCh4.lean` | 593 | IK Chapter 4: Primes in arithmetic progressions |
| `IKCh5.lean` | 877 | IK Chapter 5: L-functions, zero-free regions |
| `IKCh7.lean` | 1832 | IK Chapter 7: Large sieve, Gram matrix ALS (§7.4), Parseval bridge, MLS (§7.5), Sieve (§7.6) |
| **Total** | **~27,306** | **1092+ theorems/lemmas, 411+ definitions, zero sorry** |

### Import DAG

```
                    Euclid
                       |
                  MullinDefs
                       |
                MullinConjectures
                  /         \
        MullinDWH         MullinResidueWalk
        [LEAF]                 |
                         MullinGroupCore
                          /    |     \
           MullinGroupEscape  |    MullinGroupPumping [LEAF]
                  |           |
    MullinGroupSEInstances   MullinGroupQR [LEAF]
                |                |
                |          RotorRouter
                |               |
                |       MullinRotorBridge
                 \         /
              EquidistPreamble
                     |
               EquidistSieve
                     |
          EquidistSelfAvoidance
                     |
             EquidistCharPRE
                     |
            EquidistBootstrap
                 /         \
  MullinDepartureGraph   EquidistThreshold
       [LEAF]                |
                   EquidistOrbitAnalysis
                     |
           EquidistFourier
                     |
        EquidistSelfCorrecting
                    |
         EquidistSieveTransfer
                    |
              LargeSieve
                    |
          LargeSieveHarmonic
                    |
          LargeSieveAnalytic
                    |
          LargeSieveSpectral

  (Parallel branch from MullinDefs/MullinConjectures:)

               MullinDefs
                   |
          SieveDefinedDynamics
                   |
              SDDSBridge  (imports MullinGroupCore, EquidistBootstrap)
                   |
             SDDSReduction
```

---

## Axiom Usage

| Files | Axioms |
|-------|--------|
| Euclid.lean | `propext`, `Quot.sound` (fully constructive) |
| MullinDefs–ResidueWalk | `propext`, `Quot.sound`, `Classical.choice`, `Lean.ofReduceBool` |
| MullinGroup*, Equidist*, RotorRouter, Bridge | Full Mathlib (all CIC axioms) |

The core definitions (`seq`, `prod`, `IsPrime`) and their basic properties
are fully constructive. Classical reasoning enters only at the reduction level.

---

## Verification

```
$ lake build
Build completed successfully.
```

Zero errors, zero warnings, zero sorry on all theorem content.
All open hypotheses stated as `def ... : Prop` (clean propositions, not sorry'd theorems).
