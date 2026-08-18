# Simultaneous Avoidance: can two missing primes be shown incompatible?

**Run R-Inverse, Task D (Session 298, 2026-08-12). Assessment only.**

> Provenance note: produced by the `attack-analytic` agent, which has no Write tool;
> transcribed to disk verbatim by the coordinator. Claims about existing declarations were
> spot-checked by the coordinator; the Finite Hitting theorem below was independently proved
> in Lean the same session by Task A as `CvdP.hittingSet_finite`
> (`EM/Reduction/NoInvariant.lean`).

**Verdict: NO-MECHANISM.** One genuinely new unconditional theorem fell out of the analysis
(§1.1) and is recommended for formalization; the incompatibility itself does not exist as
stated, for a sharp and paper-worthy reason.

## 0. Setup

`P_0 = 2`, `M_n = minFac(P_n + 1)`, `P_{n+1} = P_n · M_n`. In repo terms `P_n = prod n`,
`M_n = seq (n+1)`. `E_n = P_n + 1`; `Im(M)` = present primes. Two standing facts, both already
in the repo:

- **(F1) Injectivity.** `Mullin.seq_injective` (`EM/Core/Defs.lean:483`): if `M_m = M_n`,
  `m<n`, then `M_m` divides `P_n` and `P_n+1`.
- **(F2) Guardian.** `hitting_step_guardian` (`EM/Population/HittingSetStructure.lean:94`):
  `q` missing and `q ∣ E_n` ⟹ `M_n < q`.

## 1. D1 — Mechanism inventory

### 1.1 Finite Hitting Theorem (new, unconditional)

> **Theorem.** For every missing prime `q`, `HittingSet q = {n : q ∣ E_n}` is finite, with
> `|HittingSet q| ≤ π(q) − 2`.

*Proof.* By (F2), `n ↦ M_n` maps `HittingSet q` into the primes `< q`; every `M_n` is odd
(`P_n` even ⟹ `E_n` odd), so into the `π(q) − 2` odd primes `< q`. By (F1) the map is
injective. ∎

Three unconditional consequences:

- **`ShieldedHitting q` is FALSE for every `q`.** The dichotomy `perpetual_avoidance_dichotomy`
  in `EM/Population/HittingSetStructure.lean` is degenerate;
  `shielded_hitting_implies_infinitely_many_active` and clause (1) of `hitting_set_landscape`
  are vacuously conditioned.
- **`EventualPerpetualAvoidance q` holds for every missing `q` without `MCBelow q`.** This
  strictly strengthens `mcBelow_missing_walk_ne_neg_one` (`EM/Equidist/Threshold.lean:201`),
  which currently pays MC-below-`q` for the same conclusion.
- **`PerpetualAvoidance` is removable from `EM/Population/AvoidanceTube.lean`.** That file
  (line 441) carries it as an extra hypothesis; the asymptotic energy bounds only need
  `walkVisitCount(−1) = O(1)`, which Finite Hitting supplies. So `perpetual_avoidance_rogue`
  becomes hypothesis-free: every missing prime yields `‖S_χ(N)‖ ≳ (N − π(q))/(q−2)`.

### 1.2 The deflation: the tail constraint is avoidance-blind

Drop missingness: if `q = M_m` is present, a hit at `n ≠ m` still forces `M_n < q`. So **for
every prime `q`, present or missing, `|HittingSet q| ≤ π(q) − 1`**. Equivalently `M_n → ∞`
(distinct primes) and `E_n` is `M_n`-rough.

Therefore the tail picture the task asked me to quantify — after a finite prefix, `E_n` coprime
to `q_1⋯q_k` forever, walk vector confined to `∏_i ((ℤ/q_iℤ)^× \ {−1})` — is **literally
unconditional**. It is a theorem about min-EM, not a consequence of avoidance.

"Coprime to a growing product forever" is in tension with nothing, because of quantifier order:
the prefix `N_0(k)` grows with `k`; for fixed `n` the missing primes hitting at `n` are the
missing prime divisors of `E_n` (all `> M_n`, up to `log_2 E_n` of them). No uniform
coprimality, no budget to exhaust.

### 1.3 Decoupling identity

With `m(x) = |Im(M) ∩ [1,x]|` and `D(x) = π(x) − m(x)` (= number of missing primes `≤ x`):
simultaneous avoidance of `q_1<⋯<q_k ≤ x` is *equivalent* to `D(x) ≥ k` plus the individual
conditions, and carries no further content. Avoidance of a set `S` is the single monotone
condition `S ∩ Im(M) = ∅`; there is no interaction term. Contrast Heath-Brown: "2 not a
primitive root mod p" and "3 not a primitive root mod p" are conditions on the *same* `p`,
coupled because non-primitive-roots form a union of *subgroups* — asserting both forces
`⟨2,3⟩` into a proper subgroup, an algebraic closure strictly stronger than the conjunction of
densities. Missing primes generate nothing.

### 1.4 Candidate mechanisms

- **M1 Capture-budget competition.** Each hit of missing `q` costs a fresh capture of a prime
  `< q`. Budgets finite but **non-competing**: one step with `q_1q_2 ∣ E_n` is a hit for both
  and costs one capture. Worse, the budgets are heuristically *empty* — a hit past the point
  where all present primes `< q` are used would itself capture `q`, so conditioned on `q`
  missing the expected hit count is `≈ π(q)/q ≈ 1/log q → 0`. The joint object a competition
  argument counts is, under the hypothesis being refuted, the empty set.
- **M2 Deficiency counting.** Needs a lower bound on `m(x)`. Only `m(x) ≫ log log x` is
  provable (since `M_n` can be `≈ E_n^{1/2}` and `E_n` grows super-exponentially) — consistent
  with `D(x) = π(x) − O(log log x)`. Any usable bound is a smoothness statement about
  individual Euclid numbers, and attacks WM directly rather than producing a disjunction.
- **M3 Tube ratio.** `tube_collapse` (`AvoidanceTube.lean:124`) is a population density; Dead
  End #90. §1.2 sharpens: the confinement being measured is unconditional.
- **M4 Joint subgroup confinement.** For `q ≡ 3 mod 4`, "all multipliers QR mod q" suffices for
  avoidance; jointly it would confine `Im(M)` to density 1/4. Killed twice:
  sufficient-not-necessary (Dead End #20/#130, `ℤ/4ℤ`), and still needs M2's missing input.
- **M5 Reciprocity coupling.** Facts about the pair of primes, not the sequence.
  Sequence-blind.
- **M6 Rogue characters + multiplicative large sieve — the honest Heath-Brown analogue.** Each
  missing `q` supplies `χ_q` with `|∑_{n<N} χ_q(P_n)|² ≥ (N−π(q))²/(q−2)²`. Sum against
  `∑_{q≤Q}∑*_χ |∑_m a_m χ(m)|² ≤ (X+Q²)N` with `a_m = 1_{m ∈ {P_n : n<N}}`, `X = P_{N−1}`.
  This would succeed if `X ≍ N`; but `X ≥ 2^N`. The budget is priced by support *diameter*,
  not cardinality. Off by `2^N/N`. Dead End #108/#96 in sharpest form; no sparse-set large
  sieve applies (`P_m ∣ P_n`, maximally non-equidistributed).

## 2. D2 — The max filter

Booker proved max-EM omits infinitely many primes (Cox–van der Poorten conjecture);
Pollack–Treviño gave an elementary proof; Booker–Simon extend omission to residue-class
analogues **of the second (max) sequence** — so it does *not* license a "generalized min-EM"
filter.

| Mechanism | Min-specific ingredient | Survives max swap? | Fate |
|---|---|---|---|
| M1 capture budget | **Yes** — at a max-hit `maxFac(E_n) > q`, target set infinite, no budget | Yes (fails for max) | Non-competition + empty budget |
| M2 deficiency counting | None (holds for max verbatim) | **No** | Discarded: sequence-agnostic |
| M3 tube ratio | Partly (max-missingness doesn't even imply confinement) | Yes | #90 + avoidance-blindness |
| M4 subgroup confinement | Partly | Yes | #20/#130 + M2's missing input |
| M5 reciprocity | None | **No** | Discarded: sequence-blind |
| M6 large sieve budget | Rogue bound needs confinement (min-specific) | Yes | Sparsity #108/#96 |

**The pattern of what dies is the informative part.** Sequence-agnostic mechanisms (M2, M5)
survive the swap and are therefore vacuous — they never used the sequence. Every min-specific
mechanism (M1, M3, M6) traces its min-specificity to one fact: **min looks downward into a
finite set of smaller primes, max looks upward into an infinite one** — i.e. Finite Hitting.
And Finite Hitting holds with the same strength for present primes (§1.2). So the unique
min-specific ingredient available is avoidance-blind. Min-EM's real structural advantage over
max-EM is the finite downward budget, but that advantage is spent unconditionally and cannot be
conditioned on missingness.

## 3. D3 — Verdict: NO-MECHANISM

1. **No shared object.** Avoidances are conditions on disjoint coordinates of one set `Im(M)`.
   Heath-Brown couples via a generated subgroup; Ball–Rivoal/Zudilin via a rank bound. Neither
   analogue exists. The only coupling is the identity `D(x) = π(x) − m(x)`.
2. **No family.** Both genres are counting theorems over a family with an error term. The EM
   orbit is a single deterministic object with zero degrees of freedom; every embedding family
   yields almost-all statements (Dead End #90).
3. **The one real shared budget is mispriced.** The large sieve *is* the HB engine and *does*
   couple the `q_i`; it fails by `2^N/N` (#108/#96).
4. **Min-specific structure is unconditional** (§1.2). Nothing left to condition on.
5. **The joint object is empty.** `HittingSet q_1 × HittingSet q_2` has size
   `≤ (π(q_1)−2)(π(q_2)−2)` with no lower bound and heuristic size 0.

## 4. Deliverables

**Formalization target (high confidence, ~80–150 lines)** in
`EM/Population/HittingSetStructure.lean`:

```
theorem hittingSet_finite {q : Nat} (hq : q ∈ MissingPrimes) : (HittingSet q).Finite
theorem not_shieldedHitting (q : Nat) : ¬ ShieldedHitting q
theorem missing_implies_epa {q : Nat} (hq : q ∈ MissingPrimes) : EventualPerpetualAvoidance q
```

> **Coordinator update (same session):** the first of these was independently proved by Task A
> as `CvdP.hittingSet_finite` in `EM/Reduction/NoInvariant.lean`, together with an explicit
> cardinality bound `CvdP.hittingSet_ncard_le`. The remaining two, and the downstream
> hypothesis removals below, were dispatched as a follow-up cleanup.

Proof route: `n ↦ seq (n+1)` is injective (`seq_injective`) with image inside
`(Finset.range q).filter Nat.Prime` by `hitting_step_guardian`; conclude via
`Set.Finite.of_finite_image`. Downstream edits: `EM/Equidist/Threshold.lean:201`
(`mcBelow_missing_walk_ne_neg_one` can drop `MCBelow q`);
`EM/Population/AvoidanceTube.lean:466` (`perpetual_avoidance_rogue` can drop
`PerpetualAvoidance`, replacing `walkVisitCount = 0` by `≤ π(q)` in
`confined_visit_energy_lb`). Retire or restate `hitting_set_landscape` clause (1) and
`shielded_hitting_implies_infinitely_many_active` — both become vacuous.

**Candidate new dead end (report only):**

| Cat | Description | File | Witness | Revival |
|---|---|---|---|---|
| CO | Simultaneous avoidance decouples: `k`-fold missingness is the monotone condition `S ∩ Im(minFac) = ∅` with no interaction term; the tail confinement it appears to impose (`E_n` coprime to `q_1⋯q_k`, walk off `−1`) is unconditional, holding for present primes too; the only genuine shared budget (rogue characters + multiplicative large sieve) is mispriced by `2^N/N` from super-exponential sparsity | `EM/Population/HittingSetStructure.lean` | `not_shieldedHitting` (once proved) | 1 |

Category **CO** (joint hypothesis collapses to the conjunction of independent monotone
constraints), secondary **SM** at the large-sieve step, secondary **OS** at the density step.
Revival **1**: no leverage for weak MC via pairwise disjunctions, but Finite Hitting is genuine
unconditional infrastructure, and the reformulation `WM ⟺ D(x) = O(1) ⟺ m(x) ≥ π(x) − O(1)`
identifies the only honest remaining target here — a lower bound on the count of small
least-prime-factors — which is a *single-prime* problem, not a pairwise one.

**Key fact establishing the obstruction:** for every prime `q`, missing **or present**,
`#{n : q ∣ P_n+1} ≤ π(q) − 1`, by injectivity of `n ↦ minFac(P_n+1)` into the primes `≤ q`. The
tail structure that `k`-fold avoidance appears to force is already forced unconditionally, and
carries zero information about missingness.

Sources: [Booker, arXiv:1107.3318](https://arxiv.org/pdf/1107.3318) ·
[Pollack & Treviño, Monthly](https://campus.lakeforest.edu/trevino/mullin-Monthly.pdf) ·
[Booker & Simon, arXiv:2601.21901](https://arxiv.org/html/2601.21901)
