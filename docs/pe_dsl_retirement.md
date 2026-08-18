# The retirement of PE / MFRE / DSL (Dead End #160) — full record

*2026-08-17.  This document is the memory of what happened, why, and what changed.  The
one-paragraph versions live in `paper/the_ensemble_reduction.tex` (§ant-def) and
`EM/Meta/DeadEnds.lean` (#160); the theorems live in `EM/Population/HeadDomination.lean`.*

---

## 1. What was claimed

From the project's early days the master reduction was presented as

```
ANT  ⇒  MFRE  ⇒  PE  ──DSL──▶  CME  ⇒  CCSB  ⇒  MC
```

with three population-level statements:

| Name | Lean (former home) | Statement |
|---|---|---|
| **RoughLPFEquidist q** | `Population/AlladiDensity.lean` | among `q`-rough integers `m ≤ X` (`minFac m > q`), the class `minFac m ≡ a (mod q)` has density `c/(q−1)`, `c` the density of the `q`-rough integers |
| **MinFacResidueEquidist q** (MFRE) | `Population/Proof.lean` | same, restricted to shifted-squarefree `m` (`μ²(m−1) = 1`) |
| **PopulationEquidist** (PE) | `Population/WeakErgodicity.lean` | for every prime `q`: the *ratio* form of MFRE, `→ 1/(q−1)` |

and the transfer lemma **DSL** `:= PE → CME` (`Population/TransferStrategy.lean`),
advertised as "the sole remaining hypothesis for MC modulo standard ANT".  The claimed
derivation of PE from ANT was (docstring of `PopulationEquidist`, step 4, and of
`PrimesEquidistImpliesRoughLPF`):

> Alladi/Buchstab: the density of `{minFac = p}` is `w(p)/p` with `w(p)` depending on `p`
> only through its size.  By Dirichlet's theorem, primes weighted by a size-dependent
> weight are equidistributed in residue classes: `∑_{p ≡ a} w(p)/p = (1/(q−1)) ∑_p w(p)/p`.

## 2. Why it is false

`∑_p w(p)/p` **converges**.  For a fixed prime `p`, the density of `{m : minFac m = p}` is

```
w_p = (1/p) · ∏_{r < p, r prime} (1 − 1/r)
```

(divisible by `p`, coprime to every smaller prime; periodic and CRT-independent conditions).
The class density is therefore the convergent series `∑_{p ≡ a (q), p > q} w_p`.  Dirichlet's
theorem is a statement about *counting functions* `π(x; q, a)`; it constrains only the
tail of this series, and the tail carries no mass — the weights telescope,
`w_p = c(p) − c(p+1)` with `c(n) = ∏_{r<n}(1 − 1/r) → 0`, so `∑_{p > P} w_p = c(P+1) → 0`.
The value of the series is decided by the *head*: the first few primes above `q`.

Concretely, let `p₀` be the least prime above `q` (Bertrand: `p₀ < 2q`).  Its own weight is
the fraction `1/p₀` of the whole `q`-rough mass — already nearly the full equidistributed
share `1/(q−1)`.  If the remaining mass `1 − 1/p₀` split evenly, the class of `p₀` would
receive about `2/q`, twice its share.  Equidistribution therefore requires the primes
`≡ p₀ (mod q)` to be *systematically deficient*, in the `w`-weighted sense, for ever after,
at every prime `q`.  There is no reason for that, and it does not happen: at `q = 5` the
class of `p₀ = 7` already exceeds its share on the first nineteen primes `≡ 2 (mod 5)`.

The same mechanism, one step earlier, is Dead Ends #137/#157 (small-prime domination of the
unconditioned ensemble multiplier).  Conditioning on `minFac > q` *moves* small-prime
domination to the primes just above `q`; it does not remove it.  The shifted-squarefree
versions (MFRE, PE) fail identically with the sieve weights `g(r) = r/(r²−1)` in place of
`1/r`.

**Where the informal argument went wrong**, in one sentence: it applied an equidistribution
statement about *divergent counting functions* to a *convergent weighted sum*.

## 3. What is proved in Lean (`EM/Population/HeadDomination.lean`, ≈830 lines, no `sorry`)

Notation: `Npr n`, `Apr n` = products of `r`, `r−1` over primes `r < n`; `cfun n = Apr n / Npr n`;
`w p = cfun p / p`; `classCount q a X` = the counting function inside `RoughLPFEquidist`.

| Theorem | Content |
|---|---|
| `card_minFac_eq_ge`, `card_minFac_eq_le` | `⌊X/(p·Npr p)⌋·Apr p ≤ #{m ≤ X : minFac m = p} ≤ (⌊X/(p·Npr p)⌋+1)·Apr p` (CRT block counting) |
| `w_eq_cfun_sub` | `w p = cfun p − cfun (p+1)` for prime `p` (telescoping) |
| `cfun_tendsto_zero` | `∏_{r<n}(1−1/r) → 0` (from Mathlib's divergence of `∑ 1/p`) |
| `hasSum_wq` | `∑_{p>q} w p = cfun (q+1)` |
| `tendsto_roughCount_div` | `q`-rough integers have density `cfun (q+1)` |
| `tendsto_classCount_div` | class `a` has density `∑_{p ≡ a, p>q} w p` |
| **`roughLPFEquidist_iff`** | `RoughLPFEquidist q ⟺ ∀ a coprime, ∑_{p≡a} w p = cfun (q+1)/(q−1)` |
| **`primesEquidistAsympImpliesRoughLPF_iff`** | the registered open point *is* that family of identities (its hypothesis being Karamata's theorem) |
| `not_roughLPFEquidist_of_head` | a finite set of primes of one class carrying more than the equidistributed share refutes it |
| `sum_tsum_wcls` | the class sums add to `cfun (q+1)` |
| `uce_implies_roughLPFEquidist` (`Adelic/UniformConductor.lean`) | UniformConductorEquidist at conductor `M = 1` **is** RoughLPFEquidist |

### 3a. What is deliberately *not* in Lean

The falsity of the identity at a specific `q` is a finite rational fact.  For `q = 5`, class
`a = 2`, the head `H` = the nineteen primes `≡ 2 (mod 5)` up to `347` satisfies
`∑_{p∈H} w p > 1/15 = cfun 6 / 4`; cross-multiplied it is a `Nat` inequality the kernel can
decide (`decide` with `maxRecDepth` raised; ≈10 s), and `not_roughLPFEquidist_of_head` then
gives `¬ RoughLPFEquidist 5`, hence `¬ PrimesEquidistAsympImpliesRoughLPF`.  **The user's rule
for this project is proofs, not computation, and that certificate was explicitly not run** —
neither in Lean nor outside it.  So the honest status ladder is:

| Statement | Status |
|---|---|
| RoughLPFEquidist ⟺ series identity | **machine-checked** |
| the open point `PrimesEquidistAsympImpliesRoughLPF` ⟺ that identity ∀ q | **machine-checked** |
| UCE ⇒ RoughLPFEquidist (∀ q) | **machine-checked** |
| the identity fails at q = 5 | mathematically certain; finite check; **not run** |
| `¬ RoughLPFEquidist 5`, falsity of the open points, `¬ UCE` | follows from the check; **not in Lean** |
| `¬ PE`, `¬ MFRE`, vacuity of DSL | same mechanism with sieve weights; **argued, not formalized** |

If a machine-checked refutation is ever wanted: (a) run the finite check against
`not_roughLPFEquidist_of_head` (one theorem, ~30 lines, `q = 5`, `a = 2`, `H` as above);
(b) for `¬ PE` itself, build the shifted-squarefree densities (sieve weights `g(r)`; a few
hundred lines).  Everything else is in place.

## 4. What is true instead

The correct population statement is the **double limit** `z → ∞` after `X → ∞`: among
`z`-rough integers, `minFac mod q` equidistributes as `z → ∞`, because the mass then spreads
over `p ∈ [z, z^A]` with density `≈ (log z)/(p log p)`.  Partial summation shows this needs
exactly `∑_{p ≤ x, p ≡ a} (log p)/p = (log x)/φ(q) + o(log x)` — which is
`IK.PrimeLogSumEquidistAsymp`, proved via Karamata (`EM/IK/Karamata.lean`) — and nothing more
for the unshifted version.  It is *not* what any reduction consumed, and a transfer of it to
the orbit would presuppose that the bag has captured the primes below `z`.

Also true, and now unconditional: Mertens' theorem in arithmetic progressions in asymptotic
form (`IK.weightedPNTinAP_asymp_proved`) and `∑_{p ≤ x, p ≡ a} 1/p ~ (log log x)/φ(q)`
(`IK.primesEquidistInAP_asymp_proved`).  These are the true, live outputs of the ANT work of 2026-08-17.

## 5. Consequences, and what was done about each

| Object | Verdict | Action |
|---|---|---|
| `PopulationEquidist`, `PopulationTransfer` | false / vacuous | archived (`Archive/Population/PopulationEquidistArchive.lean`) |
| `MinFacResidueEquidist`, `pe_of_mfre`, `pe_of_equidist` | false / vacuous | archived (same file; `Population/Proof.lean` deleted) |
| `DeterministicStabilityLemma`, `pe_dsl_implies_mc`, `equidist_dsl_implies_mc`, `dsl_implies_pt`, … | vacuous | archived (same file); `TransferStrategy.lean` keeps only the live ensemble-concentration content |
| `DSLHitting`, `pe_dsl_hitting_implies_mc` | vacuous | archived (same file); removed from `Ensemble/Structure.lean` |
| `full_chain_dsl`, `full_chain_dsl_hitting` | false premise | archived (same file); removed from `Reduction/Master.lean` |
| `dsl_closes_all`, `ensemble_pt_standard_em` | false premise | archived (same file); removed from `Ensemble/PT.lean` |
| `dsl_implies_crt_bridge`; DSL conjuncts of `all_routes_to_mc`, `all_routes_to_mc_with_sp`, `all_routes_to_mc_adelic` | vacuous | archived / conjuncts dropped |
| `RoughLPFEquidist`, `PrimesEquidistImpliesRoughLPF`, `RoughLPFImpliesMFRE`, `AlladiDensityFormula`, the whole Alladi chain incl. the "asymptotic entry point" theorems | false / vacuous | `AlladiDensity.lean` archived whole (`Archive/Population/AlladiDensityArchive.lean`); the definitions needed by the characterization (`roughCount`, `RoughLPFEquidist`, `PrimesEquidistAsympImpliesRoughLPF`) moved **live** into `HeadDomination.lean` |
| `DSLVariance.lean` (PCV ⇒ SMB ⇒ DSL), `FourPointPCVImpliesDSL` | endpoint vacuous | archived (`Archive/Reduction/DSLVarianceArchive.lean`); `TailIdentity.lean` re-imported from `Ensemble/PT` |
| `UniformConductorEquidist`, `UCEImpliesCME`; `uce_implies_mfre_via_crt`, `uce_alladi_implies_pe`, `uce_dsl_implies_mc` | UCE false (M = 1 clause), bridge vacuous | bridges archived (`Archive/Adelic/UniformConductorArchive.lean`); `uce_implies_roughLPFEquidist` added; open points and the `UCETheory` / `UCEViaCMERoute` strategy marked retired |
| `QuantitativeDSL`, `qdsl_implies_dsl`, `qdsl_implies_mc` (`Meta/MarkovSieve.lean`) | vacuous | archived (`Archive/Meta/MarkovSieveArchive.lean`) |
| `MFREImpliesPopulationRatioEscape` (`Ensemble/TwoPointEnsemble.lean`) | false input | archived (`Archive/Ensemble/TwoPointEnsembleArchive.lean`) |
| Registry `open_point`s: DSL, DSLHitting, PE, PT, MFRE-links, UCE, UCEImpliesCME | — | removed; `PrimesEquidistAsympImpliesRoughLPF` kept only so the equivalence can be stated |
| `Meta/Blueprint.lean` | — | `thm:full-chain-dsl`, `thm:pe-dsl-mc`, `thm:pe-dslh-mc`, `thm:dsl-closes-all` retired; `thm:roughlpf-iff` added; main chain is `thm:cme-mc` |
| Paper | — | abstract and intro headline: **CME ⇒ CCSB ⇒ MC**; §ant-def rewritten as the correction; ensemble section retitled, DSL subsection replaced by "The orbit hypothesis: CME in the ensemble picture" (the three structural arguments retained as arguments *for CME*); landscape figure without ANT/PE/DSL nodes; DSL/PE mentions removed or retargeted to CME throughout; glossary updated; appendix row #160 |

Live and unaffected: `cme_implies_mc`, `cme_implies_ccsb`, `dynamical_hitting_implies_mullin`,
`hh_implies_mullin`, all orbit-level material, all ensemble-concentration material, the
Karamata / Abel / stripping chain.

RED hypotheses #11–#13 (`EM/Archive/README.md`): PE, MFRE, RoughLPFEquidist.

## 5a. Second sweep (same day): the rest of the family

After the archive, the remaining fixed-modulus population hypotheses were audited:

| Object | Verdict | Action |
|---|---|---|
| `GenericLPFEquidist` (`Equidist/SieveTransfer.lean`, "Alladi's theorem": `minFac n mod q` equidistributed over *all* integers) | **FALSE, refuted by pure argument in Lean**: `minFac n ≡ 1 (mod 3)` forces `n` coprime to 6, so that class has density ≤ 1/3 < 1/2 (`not_genericLPFEquidist`, via `HeadDomination.card_coprime_le`) | kept as the subject of the refutation; `PrimeDensityImpliesLPFEquidist` and the GLPFE⇒MC chain archived (`Archive/Equidist/SieveTransferArchive.lean`, RED #14) |
| `SieveTransfer := GenericLPFEquidist → SieveEquidistribution` (registered open point) | vacuous — **now a theorem** (`sieveTransfer_vacuous`) | open point removed; theorem published |
| `MFREConditional` (`Ensemble/CRT.lean`: conditional class densities `1/(q−1) + O(1/q²)` uniformly in `q`) | false — odd `m` give `minFac(m+1) = 2`, so the class of `2 mod q` holds ≥ 2/3 of the conditional mass; incompatible with a uniform `O(1/q²)` | archived with `EnsembleSelectionLemma` (vacuous) and `MSIImpliesMFREConditional` (false whenever MSI holds) into `Archive/Ensemble/CRTArchive.lean`; `MinFacSelectionIndependence` (MSI, population CRT-blindness — plausible, does not assert equidistribution) kept live |
| Alladi attribution | the project misread Alladi 1977: his theorem is the **Möbius-weighted duality** `−∑_{n≤x, P⁻(n)≡a} μ(n) ~ x/φ(q)`, not unweighted equidistribution of `P⁻`; the unweighted statement fails by small-prime domination | paper's Alladi mentions corrected (spectral routes, appendix, why-its-hard "cumulative route") |

Open points afterwards: 30 (from 39 at the start of the day).

## 5b. The audit (same day, later): placeholders, hypotheses, collapses

**Placeholder audit.** 486 `Prop`-valued definitions; 141 have body `True`.  Three classes:
(A) `IK/Ch3–Ch5`, `Ch7*` reference catalogues (97) — labelled statement lists, fine;
(B) `Meta/Dobrushin`, `Meta/LFunction`, `Meta/Diamonds` dead-end markers (17) — fine as
documentation, **but they had been counted as formal witnesses** for Dead Ends #129, #131–#135
(`dobrushin_coefficient_one := trivial` etc.); reclassified as documented-not-witnessed and #130
re-pointed to the real ℤ/4 counterexample; (C) `FunctionField/*` (16), `GaussEM/*` (6),
`Stochastic/VanishingNoise` (4), `Transfer/CRTPointwise.PopulationConditionalEquidist` (1) —
cited in the paper as content.  All of (C) now carry a `-- PLACEHOLDER (audit 2026-08-17)`
marker in Lean; the paper has a `[placeholder]` badge, the FF section opens with an explicit
"what is and is not machine-checked" paragraph, "Population CCSB from Weil" is demoted from
theorem to remark, `SelectionBiasNeutral` is no longer listed as an open hypothesis (it is
`True`).  Witnessed dead ends: 28 → 22 (→ 24 after #156/#157 below).

**Hypothesis audit.** Every remaining open point read against three failure patterns
(fixed-modulus population equidistribution; uncentered character sums at `χ ≡ 1`;
placeholders).  Results: the orbit-level family (CME, CCSB, DH, HH, SHH, VE, SCD, MMCSB,
DecorrelationHypothesis, window gains) all carry `χ ≠ 1` and are genuinely open;
`EnsembleConcentration` is a.a.-orbit-level (its head bias washes out as `K → ∞`), kept;
**`StepDecorrelation`, `FourPointPCV`, `TailWindowDecorrelation` are false at `χ ≡ 1`** and,
with `CharSumVarianceBound`, `EnsembleCharSumConcentration`, `SecondMomentSquaredBound`, and
`EnsembleMultiplierEquidist` (odd seeds ⇒ multiplier 2), now **refuted in Lean by pure
argument** (`EM/Ensemble/UncenteredRefutations.lean`) — Dead Ends #156/#157 witnessed.
`TWDImpliesCCSB`, `EnsembleEquidistImpliesDecorrelation`, `DecorrelationImpliesVariance`,
`FourPointPCVImpliesSMSB` are vacuous (proved).  The chain theorems
`sd_implies_cancellation` etc. stay as valid conditionals with false antecedents; the intended
centered repair at fixed steps is itself of the #157 type and is not pursued.

**Collapse audit.** `CRTPointwiseTransferBridge ↔ CME` (its input PCE is `True`),
`SubstitutionPrinciple = CME`; both retired as separate open points.  SCD/SVE/VE are a
genuine ladder (threshold-free vs thresholded), kept.

**Open points after the audit: 24** (were 39 at the start of 2026-08-17):
`MullinConjecture`, `HittingHypothesis`, `DynamicalHitting`, `SingleHitHypothesis`,
`EveryPrimeDividesEuclid`, `OneWindowGain`, `WindowFourierGain`, `CME`, `CCSB`,
`MultiModularCSB`, `DecorrelationHypothesis`, `VisitEquidistribution`, `SelfCorrectingDrift`,
`BVImpliesMMCSB`, `EnsembleConcentration`, `WeakMullin`, `ReciprocalDivergence`,
`InfinitelyManyComposite`, `MixedDiversity`, `MixedDiversityWeak`, `MixedHitting`,
`UFDStrongImpliesMixedMC`, `IK.WeightedPNTinAP` (true, O(1) form), and the deliberately kept
false subject `PrimesEquidistAsympImpliesRoughLPF`.

## 6. Things to keep in mind

* **The FF "PE" is a different object.**  `FunctionField/Analog.lean`'s `FFPopulationEquidist`
  is a `True` placeholder for "irreducibles of large degree are equidistributed mod `Q`" — a
  counting statement (the FF prime-polynomial theorem in APs), not the head-dominated
  `minFac`-density statement.  The genuine FF analogue of PE (least-degree irreducible factor
  among `Q`-rough polynomials, fixed `Q`) fails by the same head domination; the paper's FF
  table now says "prime equidistribution mod `q` (ANT)" rather than "PE".
* **`MFREConditional`** — analysed in §5a: false, archived.  **`MSI`** kept: it asserts only that the
  conditional distribution does not depend on the conditioning class, not that it is uniform.
* **`PopulationConditionalEquidist`** (`Transfer/CRTPointwise.lean`) is a `True` placeholder;
  `CRTPointwiseTransferBridge` is therefore literally CME.  Pre-existing; noted.
* **`Reduction/DSLInfra.lean`** is orbit-level character-sum infrastructure (energy telescoping,
  cofactor identity, `feb_implies_cme`) — nothing to do with PE despite the name.  Left in
  place; renaming would only churn.
* Any future "population ⇒ orbit" framing must use the `z → ∞` version and is circular for MC
  (capturing the primes below `z` is the conjecture).

## 7. How this was found

While scoping the first Alladi link for formalization, the definitions were read instead of
the docstring proof sketch: `RoughLPFEquidist` asks a convergent series to split evenly, and
the sketch's step 4 invoked Dirichlet for that.  A three-line density computation
(`w_5`, `w_7`, …) made the bias obvious; the numerics were then set aside in favour of the
characterization theorem, per the project's rule.
