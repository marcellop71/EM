# Can the sure layer say anything about ONE orbit?

**Session 313, frontier scoping. Assessment only — no Lean was written, no proof attempted, no
computation of any kind performed.** Produced independently by `attack-analytic` and
`attack-dynamicalsystem` (neither saw the other's brief output, nor the coordinator's), reconciled
and verified against source by the coordinator (running on `claude:opus`). Every Lean name below was
checked against the source before being cited.

---

## VERDICT

# DEAD — budget vacuous.

All three assessments — the two attack agents, run blind to each other, and the coordinator's own
prior analysis — reached this verdict independently, and by substantially overlapping routes. The
harmonic charge budget `LargeStepRoughness.charge_sum_le_harmonic` carries, for a single prime along
a single orbit, **exactly zero** information: it is an identity plus a pigeonhole. Four further
independent obstructions (§2.2–§2.5), any one of which is on its own sufficient, close the direction.

The one durable positive is a small structural lemma (§1) that is missing from the repo and worth
having regardless.

**Answer to the framing question of the dispatch.** The dispatch asked whether the distinction it
drew — that #90/#117 are about transferring a *population* statement to one orbit, whereas the charge
budget never passes through a population statement — is real. It is **real about the theorems and
inert about their content**. The theorems genuinely are per-path, hypothesis-free, and free of all
four legs of the Four-Way Blocker; Session 309's verification was right about that. But the layer is
the deductive closure of just two facts — the *non-divisibility* content of `minFac` minimality, and
multiplier distinctness — and **neither discriminates between a prime missed forever and a prime
captured at step 10^100**. The population step is not absent; it has been *relocated* to the point of
use, where the weight `1/|box|` is read as a probability over the seed fibre. Recorded as new dead
ends #169–#174.

---

## 0. What was assessed

The "sure layer" is the set of per-path, hypothesis-free results proved in Sessions 309–311:
`charge_sum_le_harmonic` (F1e), `brink_forces_small_multiplier` / `two_le_boxCard_of_exposed` (F3a),
`seed_mem_box` / `boxCard_pos` (F1d), `genSeqAvoid_injOn` / `few_small_multipliers` (F2b/F2c),
`chargeBudget_le` (F1h), and `pathwise_compensator`. None mentions a density, a measure, an average,
or an equidistribution hypothesis. The question: can they bound the counting function of the primes
**missed** by a single orbit — the true one, seed `m = 2` — or `Σ_{q missed ≤ x} 1/q`, or any
nontrivial function of the missed set?

---

## 1. The one durable positive: the Coupling Lemma (missing from the repo)

Both agents derived it independently; the coordinator had derived it before dispatch. It is **not in
the repo** (checked: only `LemmaDBox.genSeqAvoid_eq_iff`, a different statement, matches nearby
greps).

> **Coupling Lemma.** Let `q` be prime, `m ≥ 2`, and suppose `genSeq m j ≠ q` for all `j < n`. Then
> `genProdAvoid q m j = genProd m j` and `genSeqAvoid q m j = genSeq m j` for all `j < n`.
> In particular, **if `q` is missed by the whole orbit, the `q`-free reference dynamics *is* the true
> dynamics.**

*Proof.* Induction on `k < n`. With `P = genProd m k`, `N = P+1 ≥ 3`, `p = minFac N = genSeq m k ≠ q`:
`p` is prime, `p ∣ N`, `p ≠ q`, so `prime_dvd_qfreePart_iff` gives `p ∣ qfreePart q N`, whence
`(qfreePart q N).minFac ≤ p`. Conversely `qfreePart q N ≥ 2` (else `N` is a power of `q` and
`minFac N = q`), so `(qfreePart q N).minFac` is a prime dividing `N`, hence `≥ minFac N = p`.
Equality; accumulators agree at `k+1`. ∎ (~15 lines of Lean.)

**Consequence — the `r ≠ q` hypothesis is *not* an obstruction.** At any finite horizon `n`,
`{genSeq m j : j < n}` is a set of `n` distinct primes (`genSeqAvoid_injOn`), so given the target
prime `r` one may choose **any** prime `q ∉ {p_0,…,p_{n−1}} ∪ {r}` as a throwaway spectator; the box
process for `r` then runs on the true orbit. This is the cleaner of the two available couplings.

*Recorded disagreement between the agents (resolved).* `attack-dynamicalsystem` judged `r ≠ q` "fatal
in the direct form", reasoning with `q` = the missed prime, and routed instead through
`SeedTypes.card_visitedSet_le_sub_two`, which is stated for the **true** dynamics (verified: no
"Avoid" in its statement) and so reaches `r = q` legitimately. `attack-analytic` judged `r ≠ q` a
non-obstruction via the spectator-`q` device above. **Both are correct**; they set up different
bookkeeping and reach the same conclusion. The spectator-`q` device is the more convenient; the
`SeedTypes` route is the one that touches the missed prime *itself*, and is therefore the one that
exhibits the circularity in §2.3.

---

## 2. Why it is dead — six independent obstructions

### 2.1 The budget is an identity, saturated, with zero slack (→ dead end #169)

Read directly off the Lean: `boxCard q m r 0 = r − 1`; **F1a** `boxCard_succ_of_charged` decrements
the box by **exactly one** at a charged step; **F1b** `boxCard_of_not_charged` leaves it
**unchanged**; **F1d** `boxCard_pos` keeps it `≥ 1`. Hence the box size at the `t`-th charged step is
exactly `r − t`, and with `C` charges before `n`

    Σ_{k<n, Charged}  1/boxCard  =  Σ_{t=1}^{C} 1/(r−t)  =  H_{r−1} − H_{r−1−C}.

So `charge_sum_le_harmonic` is **logically equivalent, for a single path, to `C ≤ r−1`** (sharpened
by `boxCard_pos` to `C ≤ r−2`). The Lean proof is transparently this: it injects the charged steps
into `Finset.range (r−1)` via `i ↦ boxCard q m r i − 1`. And `C ≤ r−2` is itself forced by counting
alone: `C` counts *distinct* cofactor residues `c_k mod r` at `r`-exposed steps, these are units mod
`r`, there are `r−1` of them, and one — the death class `−(m mod r)⁻¹` — can never occur at an
exposed step.

The dispatch's reading ("each charge costs `≥ 1/(r−1)`, so `≈ r log r` declines are permitted") is a
lossy relaxation by a factor `log r` in the permissive direction. The number of *declines* (exposed
steps) is unbounded and unconstrained; only the number of *charges* is bounded, and trivially.

**Does it bite at any scale?** For `r ≳ n`, `C ≤ n < r−2` automatically — pure slack. For `r ≲ n`, it
forces the residues mod `r` to repeat — which is exactly what a permanently missed prime does. The
bite is on the capture-free side. Aggregated (`chargeBudget_le` at `N = 2n`: `≤ π(2n) + 2n log 4 ≈
2.8n`), the bound is within an absolute constant of generic behaviour, so it has no asymptotic slack
either.

### 2.2 The model obstruction — the strongest argument of the session (→ dead end #171)

Every theorem of the sure layer is proved *about* `genSeqAvoid q m`. And
`SeedCapture.genSeqAvoid_ne_avoided` (verified, `SeedCapture.lean:159`) proves that this dynamics
**never selects `q`**:

    genSeqAvoid_ne_avoided : 2 ≤ genSeqAvoid q m k → genSeqAvoid q m k ≠ q

So at every finite horizon on which the `q`-free orbit is nondegenerate, the entire sure layer —
budget, brink, distinctness, `chargeBudget_le`, `pathwise_compensator` — is satisfied by a dynamics
that misses `q` **by construction**. No consequence of the sure layer *alone* can therefore force any
prime to be captured.

Stated precisely, so as not to overclaim: capture *is* recoverable per-orbit, via
`captured_iff_mem_visited` at `m' = m`, which reads `q` captured within `n` ⟺
`(m mod q) ∈ −(visitedSetAvoid q m n)⁻¹`. The obstruction is that nothing in the sure layer forces
`visitedSetAvoid` to grow so as to contain a **prescribed** class. This has a formal witness already
in Lean and is the single cleanest reason the direction is closed.

### 2.3 The surviving branch is `¬DynamicalHitting` — circular, the mirror of #166 (→ #170)

The dichotomy the dispatch asked for ("`r` missed ⟹ rarely exposed OR box stays large") **degenerates
to one branch**, and that branch is circular.

*The exposure branch is refuted outright.* By `few_small_multipliers`, `#{k<n : p_k ≤ r} ≤ π(r)`, so
**at least `n − π(r)` of the first `n` steps are `r`-exposed**, whether or not `r` is missed. There is
no "rarely exposed" scenario. Distinctness closes it quantitatively.

*The box branch is the hypothesis restated.* Unwind `seed_mem_box` — its Lean proof is literally
"exposure ⟹ non-divisibility", ending in `not_dvd_succ_of_exposed_avoid`
(`LargeStepRoughness.lean:199`, verified; the analytic agent mis-filed this as `SeedCapture`):

    boxCard q m r k ≥ 1  ⟺  r ∤ genProd m j + 1 at every r-exposed j < k
                         ⟺  the walk mod r avoids the death class at exposed steps.

For `m = 2` and `r` the target, that is literally `¬DynamicalHitting(r)` at horizon `k` — the
hypothesis one is trying to contradict. Nor can this be broken by weakening: the only nonvacuous
quantitative negation, `C ≥ r−1`, **is** MC(`r`) (§2.6).

This is the exact mirror of **#166**. #166: "the bag has caught up" presupposes capture, blocking the
*entrance* to (LS). Here: "the box has not collapsed" presupposes non-capture, blocking the *exit*
from it. Same circle, opposite orientation.

### 2.4 The compensator points the wrong way (→ #172), and cannot be applied at all (→ #173)

Two distinct defects, found by the two agents separately.

*Wrong sign.* `pathwise_compensator` **lower**-bounds `Σ_k S_k`, and `S_k = ∏_r (1 − ρ_r)` is
*maximal* (`≡ 1`) exactly when no position is ever new — i.e. for the orbits that capture nothing.
Per-path, "large `S_k`" means "no progress toward coverage". The opposite (ensemble) reading needs
the seed residue to be uniform in its box, which is #90. So **both** proved sure bounds — charge `≤`,
survival `≥` — constrain the half-line *opposite* to capture-freeness. The set of configurations
satisfying the whole sure layer is downward-closed in charge, and the capture-free configurations sit
at its extreme point (zero charge, `S_k ≡ 1`, boxes frozen). No upper bound on charge can exclude
zero charge.

*Inapplicable.* Verified from source, `pathwise_compensator` requires
`(∀ j < n, genSeqAvoid q m j ≤ Y)` **and** `Real.log Y ≤ n²` (and `exp 600 ≤ n`). For the true orbit
no sure bound of that shape exists: the only sure size information permits `p_k ≈ 2^{2^k}`, i.e.
`log Y ≈ 2^n ≫ n²`. In the seed-average programme `Y` is a **policy** on a seed population, and the
seeds violating it are absorbed into `ls_plus`'s additive degenerate-tail term. **A single orbit
cannot be absorbed into a tail term.** So the strongest sure ingredient in the layer is inapplicable
to the orbit of 2 at every horizon, unconditionally.

### 2.5 The requested outputs are gated on (C∞) anyway (→ #174)

Independently of everything above. Write `hits(x) = #{k : p_k ≤ x}`, `missed(x) = π(x) − hits(x)`.
Every target in the dispatch requires a **lower** bound on `hits(x)`. The sure layer's only
multiplier-size statement is `few_small_multipliers`, an **upper** bound on the number of small
multipliers — the wrong direction, and it is the only one, because distinctness is the only sure
arithmetic fact about the multiplier sequence.

Worse, a lower bound is gated on an open problem. Under `AutonomousBranch.PerpetualPrimality N₁`
(open; its negation is (C∞), the project's top frontier item — verified present and open at
`AutonomousBranch.lean:111`), `prod(n+1) = prod n·(prod n + 1)` and `p_k = prod k + 1`, so
`hits(x) = O(log log x)`. Even granting (C∞), compositeness gives only `p_k ≤ √(prod k + 1)`, still
doubly exponential. Hence:

> **Any nontrivial upper bound on `missed(x)`, or on `Σ_{q missed ≤ x} 1/q`, implies (C∞) — and much
> more besides.** It is strictly harder than the project's own top open arithmetic statement, and
> cannot come from a bookkeeping layer.

### 2.6 The minimal missing ingredient is MC itself (collapse)

Both agents converged on the same statement, from different directions:

> **(NPLB)** For the true orbit, `|visitedSet q m n| ≥ q − 2` for some finite `n` — equivalently, the
> cofactor residues mod `q` at `q`-exposed steps exhaust all units except the death class.

Given (NPLB), capture follows from machinery already in the repo: one more charged step forces the box
to size 1 with a new position, `brink_forces_small_multiplier` yields `q ∣ P(k)+1` with `p_k ≤ q`, and
distinctness gives capture within a further `π(q)` steps.

**Classification: (c), an equivalence collapse.** (NPLB) is not merely sufficient but *equivalent* to
MC-mod-`q`: capture implies the death class was visited, and box positivity means every
not-yet-captured prime has `|V| ≤ q−2`, so the only way to reach `q−1` is *through* capture. The
entire content of (NPLB) sits in its last unit; any `δ`-weakened form is either MC or vacuous. So:
**the sure layer plus one extra per-path hypothesis closes MC-mod-`q` iff that hypothesis is
MC-mod-`q`.**

Three weakenings, all classified: *seed typicality* — (d), refuted by #90 (one point vs. a
positive-density subset of a fibre); *non-periodicity of the residues mod `q`* — (c), equivalent to
(NPLB); *anatomy / (C∞)* — a genuine positive fact of the **wrong type**, since compositeness produces
an additional *large* prime factor, never a *prescribed* one.

---

## 3. The #90 witness is literally a box-process witness

`attack-dynamicalsystem` transported the `(ℤ/5)^×` witness of #90/#117 into box language, which
settles sub-question (D) concretely rather than by analogy. Take `q = 5`, seed `m = 2`, and the
residue pattern in which every multiplier is `≡ 4 (mod 5)`. Then `c(k) mod 5` cycles `1,4,1,4,…`, so
`P(k)+1 = 2c(k)+1 ≡ 3,4 (mod 5)` — never `0`. The box: `V_∞(5) = {1,4}`, `−V⁻¹ = {4,1}`,
`box = {2,3}`, containing the seed residue `2`. Then

* `boxCard_pos` holds forever (box size 2);
* **exactly two charges in the entire history**, so `Σ 1/|box| = 1/4 + 1/3 ≪ H_4` — the budget is
  satisfied with *enormous* slack;
* `two_le_boxCard_of_exposed` holds, the brink is never reached;
* `ρ_5(k) = 0` for all large `k`, so `S_k ≡ 1`: the compensator is **maximally** satisfied;
* and `5` is missed forever.

Every box-process quantity is blind to this. The obvious objection — the multipliers are distinct
primes, so they cannot repeat — is void: distinctness constrains the *primes*, not their *residues*,
and infinitely many distinct primes lie in `4 mod 5`. That is the Marginal/Joint Barrier exactly:
distinctness is an integer-level fact, capture is a residue-level fact.

---

## 4. A principle worth recording (not a dead end)

`attack-dynamicalsystem` isolated the structural reason, which the coordinator endorses and
recommends recording alongside the Session-299 anatomy principle:

> **The sign asymmetry of `minFac`.** The definition `p_k = minFac(N_k)` yields infinitely many
> *negative* facts (`r ∤ N_k` for all `r < p_k`) and exactly **one** positive fact (`p_k ∣ N_k`, about
> a prime that is captured by definition). Every sure ingredient is a deduction from these plus
> distinctness, hence every sure ingredient is a non-divisibility statement about *non-captured*
> primes. The sure layer can only ever produce **upper** bounds on hit counts — indeed
> `#{k : q ∣ P(k)+1} ≤ π(q)` for every `q`, captured or missed — and never the lower bound of 1 that
> capture requires.

**Screening test for any future per-path proposal:** *does it produce a positive divisibility fact
about a prescribed prime?* If not, it is inert.

This also explains, and delimits, the sure layer's much-advertised evasion of leg 4 of the Four-Way
Blocker: the evasion is purchased by making the statements **symmetric in the missed/captured
distinction**, which is exactly why they are inert on one orbit. A per-path statement provable
without any of the four structural inputs has so far invariably been a cardinality statement, and the
missed set is not cardinality-controlled.

---

## 5. What honestly survives for a single orbit

Three per-path facts, all consequences of distinctness, none new, **none a constraint on the missed
set** — each is symmetric between captured and missed primes:

1. **Exposure genericity.** All but `≤ π(r)` of the first `n` steps are `r`-exposed, for every `r`.
   (Already the "past the sieve gap" hypothesis of the Single Hit Theorem.)
2. **Finite hit count.** For every prime `q`, `#{k : q ∣ genProd m k + 1} ≤ π(q)`. Note `q ∣ P(k)+1`
   does *not* imply capture — a smaller prime may also divide `N_k`; capture is `q ∣ N_k` **and**
   `minFac(N_k) = q`.
3. **The Coupling Lemma** (§1) — hygiene, not a bound, but worth landing.

**PARTIAL was considered and deliberately rejected.** These are genuine per-path facts about the
orbit of 2, but every one is symmetric in the missed/captured distinction (§4), so none constrains
the missed set. Calling this PARTIAL would be inflation.

---

## 6. New dead ends proposed

Numbers assigned by the coordinator against `deadEndCount = 168` at time of writing.

| # | Cat | Description | Witness | Rev |
|---|---|---|---|---|
| 169 | CO | Harmonic charge budget is an identity, vacuous per prime at a single seed | `LargeStepRoughness.charge_sum_le_harmonic` | 1 |
| 170 | CI | "The box has not collapsed" is `¬DynamicalHitting(r)` — mirror of #166 | `LargeStepRoughness.seed_mem_box` | 0 |
| 171 | SF | `q`-free model obstruction: the whole sure layer is satisfied by a dynamics missing `q` by construction | `SeedCapture.genSeqAvoid_ne_avoided` | 0 |
| 172 | OS | The sure compensator has the wrong per-path sign: `S_k ≡ 1` is the capture-free extreme | `LargeStepRoughness.pathwise_compensator` | 0 |
| 173 | AG | `pathwise_compensator`'s type bound is a seed-population policy, not an orbit fact | `LargeStepRoughness.pathwise_compensator` | 1 |
| 174 | TM | Missed-prime counting bounds are gated on (C∞); all sure size bounds point the wrong way | `AutonomousBranch.PerpetualPrimality` | 1 |

---

## 7. Agreement and disagreement between the two agents

**Agreement (independent, blind).** Verdict `DEAD — budget vacuous`; the telescoping identity
`Σ = H_{r−1} − H_{r−1−C}`; the exposure branch refuted by distinctness; the box branch circular and
the mirror of #166; the minimal missing ingredient (NPLB) collapsing to MC-mod-`q`; the Coupling
Lemma missing from the repo. The coordinator had independently derived the identity, the Coupling
Lemma, and the circularity before dispatch (`tmp/coordinator_sure_layer_analysis.md`).

**Disagreement (one, minor, resolved in §1).** Whether the `r ≠ q` hypothesis obstructs the natural
setup. Analytic: no — use a spectator `q`. Dynamical: yes in the direct form — route through
`SeedTypes.card_visitedSet_le_sub_two` in the true dynamics instead. Both correct; different
bookkeeping, same conclusion. Recorded rather than averaged.

**Unique to `attack-analytic`:** the (C∞) gate (#174); the compensator-inapplicability argument
(#173).
**Unique to `attack-dynamicalsystem`:** the model obstruction (#171 — the strongest single argument,
and the only one with a ready-made formal witness); the sign analysis (#172); the explicit `(ℤ/5)^×`
box witness (§3); the sign-asymmetry principle (§4).

---

## 8. Recommendation

Close the orbit direction for the box process. The last place it can go is the §G simultaneous-in-`q`
question, which is a *population* question and is unaffected by this note; the `(Ẑ, Haar)` route of
`simultaneous_in_q_scoping.md` §4 remains the natural next mathematical target. The Coupling Lemma
(§1) is worth landing as ~15 lines whenever a formalizer is next dispatched to `EM/Population/`.
