# The simultaneous-in-`q` form of the seed-average law (§G)

**Session 312, frontier scoping. Assessment only — no Lean was written, no proof attempted.**
Produced by the `attack-analytic` agent (which has no write tool) and transcribed by the
coordinator. Every constant below was read off the Lean sources cited; nothing was computed.

## Verdicts

* **Route (i) — `q`-uniform rate + union bound over `q`: NEEDS-NEW-INPUT.** Summability of the
  per-`q` failure fraction *is* achievable, and the differing moduli are *not* fatal. The missing
  input is a **countably additive ambient measure**; no rate, however uniform, substitutes for it.
* **Route (ii) — logarithmic density + Borel–Cantelli: DEAD.** Its premise is false: logarithmic
  density is also only finitely additive. Worse, `1/m` weights destroy the exact CRT selection
  law, and on `M_Y`-periodic events log density *equals* natural density anyway.
* **Third route — the profinite ensemble `(Ẑ, Haar)`: PROMISING, and it needs no new analysis.**

## 1. The quantitative shape of the per-`q` theorem

`AlmostAllGenMC.almost_all_genmc` bounds the uncaptured seeds by three pieces
(`uncaptured_decomposition`):

| piece | bound | source |
|---|---|---|
| good seeds | `exp(−(3/8)·κ_q·(c₁ n/2 − K₀(q)))` | `TheoremC.theorem_C` |
| degenerate / oversized prefixes | `e²⁵ · log(n+1)/(n+1)` | `TailAssembly.tail_small` |
| heavy window divisor mass | `1/Cc` | `TailEstimate.markov_divisor_mass` |

with `c₁ = exp(−250)` absolute (`LargeStepRoughness.c₁`); `κ_q = min(c₂/(16 φ(q)), 1)`,
`c₂ = exp(−128)` (`LemmaDBox.c₂`); `Cc = max(48q, ⌈3/ε⌉)`; `K₀ = max(max 1 k₀) Cc + q`; and
`k₀(q) = max 1 (sup_{b<q} ⌈Y₀(b)⌉)` with `Y₀(b) = max(x₀(q,b,ε_q), exp(8Bφ(q)))`,
`ε_q = 1/(16φ(q))` (`LemmaD.window_ap_recip_lower`). Policy window `n²/2 ≤ log Y ≤ n²`.

Two load-bearing facts about `k₀(q)`, not previously recorded:

* **(K1) `k₀(q) ≥ exp(8Bφ(q))` — exponential in `q`.** Explicit in `window_ap_recip_lower`: the
  threshold absorbs the prime-power constant `B` by demanding `log y ≥ 8Bφ(q)`.
* **(K2) `k₀(q)` is ineffective.** The other half, `x₀(q,b,1/(16φ(q)))`, comes from
  `IK.weightedPNTinAP_asymp_proved`, i.e. from Karamata, which supplies no rate. Classically,
  uniformity of that threshold in `q` *is* Siegel–Walfisz, ineffective by Siegel's theorem.

(K2) limits *explicitness only*: a union bound needs `n(q)` to exist, not to be computable. So
(K2) does not block route (i); it does block any literal "`q`-uniform rate" claim.

## 2. Route (i)

### 2.1 Summability is easy

Target `ε_q = q^{−2}`. Markov piece: `Cc(q) = max(48q, 3q²)` gives `1/Cc ≤ 1/(3q²)`. Tail piece:
`e²⁵ log(n+1)/(n+1) ≤ 1/(3q²)` needs only `n ≳ 3e²⁵ q² log q` — **polynomial in `q`**. (The
dispatch's worry that the `log n/n` tail forces super-polynomial `n(q)` was a miscalculation:
summability over primes needs `Σ ε_q < ∞`, and `q^{−2}` suffices.) Exponential piece: needs
`n ≥ (2/c₁)[K₀(q) + (8/3)(2 log q + log 3)·16e^{128}φ(q)]`, dominated by `k₀(q) ≳ exp(8Bφ(q))`.

So `n(q) ≈ 2e^{250}·exp(8Bφ(q))`, exponential in `q` — and *because* it is exponential the tail
piece is then super-summable. **No single ingredient is the binding constraint.**

### 2.2 The policy window pins `n` to `Y`

`n²/2 ≤ log Y ≤ n²` pins `n ∈ [√(log Y), √(2 log Y)]`, so `log Y(q) ≍ exp(16Bφ(q))` and
`log log M_{Y(q)} ≈ exp(16Bφ(q))` — triple-exponential in `q`.

### 2.3 Different `q` on different sample spaces: NOT fatal

* **(P1)** `modulus q Y = ∏_{r ≤ Y, r prime, r ≠ q} r` divides the primorial `P(Y')` for every
  `Y' ≥ Y`, so all per-`q` sample spaces sit inside one common period.
* **(P2)** `SelectionLaw.genSeqAvoid_prefix_eq_of_modEq` is stated for **any** `M` divisible by
  the band primes, not just `modulus q Y`, and `SelectionLaw.localPred_periodic` +
  `Nat.filter_Ico_card_eq_of_periodic` already do the counting transfer. All three covering sets
  are `M`-measurable. (The *counted* set uses the genuine orbit and is not periodic — but it is
  only ever used inside these periodic supersets. Session 312's `TypeBadSmall.type_bad_small` and
  `FiberTheoremC.FiberGood` make exactly this precise.)

**Corollary available now — the finite-`S` simultaneous law.** For every finite set `S` of primes
and every `ε > 0` there are `n` and `Y` such that, on one period of `P(Y)`, at most `ε·P(Y)` seeds
fail to capture some `q ∈ S` within `n` steps. *Proof.* Apply the per-`q` theorem with `ε/|S|`,
take `Y = max Y_q`, `n = max n_q`, transfer by (P1)+(P2), union bound. ∎ In natural-density form
this is immediate from `AlmostAllDensity.almost_all_genmc_density` and finite subadditivity of
upper density.

### 2.4 The actual binding constraint

At a scale `X`, the per-`q` bound is usable only when `modulus q Y(q) ∣ X`, i.e. only for
`q ≤ Q(X) ≈ (1/16B)·log log log X`. So at any finite scale **only triple-logarithmically many
primes are controlled**, and about `⋃_{q>Q(X)} F_q` there is no information at all. Passing
`Q → ∞` is exactly the countable-union step natural density cannot perform: upper density is
finitely subadditive only, and increasing sets of density `≤ δ` can have union of density `1`
(singletons, each of density `0`, union `ℕ`).

**Summability therefore buys nothing.** `Σ_q ε_q < ∞` is a hypothesis of Borel–Cantelli, and
Borel–Cantelli is a theorem about countably additive measures.

### 2.5 Verdict

**NEEDS-NEW-INPUT**, the input being either **(N1)** a countably additive ambient measure (§4 —
the cheap one, which makes the rate question moot), or **(N2)** a scale-uniform tail-of-primes
bound: for every `δ` a `Q` with `#{m ≤ X : ∃ q > Q, m misses q} ≤ δX` **for all `X`**. (N2) is a
genuinely new statement, uniform in `q` *and* in the scale, at least as strong as everything the
programme proves; no route to it is visible, and it would additionally need the ineffective
`k₀(q)` of (K2) replaced by Siegel–Walfisz-quality input.

## 3. Route (ii): logarithmic density — DEAD

**The premise is false.** Logarithmic density is also only finitely additive (singletons), so it
supports no Borel–Cantelli. The cases where log density genuinely *is* better behaved do not
apply: Davenport–Erdős needs **sets of multiples** (the `F_q` are not — the exclusion of `q` from
`bandUpTo`, dead end #165, is precisely the statement that `F_q` is not a divisibility condition);
log-averaged Furstenberg systems (Tao's entropy decrement) gain from **dilation invariance**, which
the EM greedy map does not have, and which is orthogonal to simultaneity anyway.

**And the architecture does not survive the weight change.** `SelectionLaw.selection_law` is an
*equality*, `#(cell ∩ Survives) = survival · #cell`, proved by CRT surjectivity on a **full
period**; exactness requires a weight constant on residue classes. With `1/m` one gets
`Σ_{m ≤ X, m ≡ a (M)} 1/m = (1/M)log(X/M) + O(1/M)`, exact only as `X/M → ∞`, with an error that
swamps everything at `X ≍ M`. `TreeChernoff.chernoff_quarter_local` consumes `hcond` as an exact
per-cell inequality and would need an error budget at every node of the type tree. Meanwhile
`markov_divisor_mass` and `tail_small` survive but *pointlessly*: for `M`-periodic sets, log
density in the regime `X/M → ∞` **equals** natural density. Pure loss.

## 4. Third route: the profinite ensemble `(Ẑ, Haar)`

Let `Ẑ = lim_M ℤ/Mℤ ≅ ∏_r ℤ_r` with normalized Haar measure `μ` — a **countably additive**
probability measure under which the coordinates `{x mod r}` are independent uniform. This is not
an analogy; it is the exact random model the box process describes. The programme is already
profinite-native: `genSeqAvoid` and `typeData` depend only on `x mod M` for any `M` divisible by
the band primes, and the deliberate omission `r ≠ q` from `modulus` (#165) is precisely the
statement that the `q`-coordinate is a **free independent coordinate**, carried separately by
`SeedCapture.captured_iff_mem_visited`.

Two small facts make the dynamics total:

* **(T1)** At step `k` the event "no prime divides `E_k`" has measure `≤ 2^k ∏_{r ≤ Y}(1 − 1/r)
  → 0` (at most `k` primes are used, by multiplier distinctness), so countably many steps are
  a.e. defined. Needs only Mertens' divergence, not `tail_small`.
* **(T2)** Every event in the chain is a cylinder event, by (P2); and `μ(E) = (count on one
  period)/(period)` for cylinder events.

Hence `almost_all_genmc` transfers verbatim: for every `ε > 0` there is `n` with
`μ(F_q^{(n)}) ≤ ε`, and since `F_q ⊆ F_q^{(n)}` for every `n`,

> **`μ(F_q) = 0` for every prime `q`**, and by **countable additivity** `μ(⋃_q F_q) = 0`:
> Haar-almost every profinite seed captures every prime.

**No `q`-uniform rate is used anywhere.** One takes `n → ∞` at *fixed* `q`, where every error term
already tends to `0`, and lets countable additivity do the union. **Simultaneity is not a rate
problem; it is an additivity problem.**

### Costs and caveats — to be stated as loudly as the existing scope caveat

* `ℕ ⊂ Ẑ` is Haar-null. "Haar-a.e. seed" is **not** "a.a. integer seed"; a Haar-null set can have
  upper density `1` in `ℕ`. This is a statement about the *random model*. **It says nothing about
  the orbit of `2`; #90 and #117 are untouched.**
* **Mathematically new content: none.** The finite-`S` law of §2.3 is the mathematics; the passage
  to all `q` is Carathéodory extension of the cylinder content. That is a feature — no analytic
  risk.
* **Formalization cost**: (a) a countable product measure, or more cheaply the Carathéodory
  extension of the cylinder content on `lim ℤ/Mℤ`; (b) `genSeq`/`genSeqAvoid` as a.e.-defined maps
  on `Ẑ` (needs (T1)); (c) restating the headline as a cylinder-measure bound. `EM/Adelic/
  Profinite.lean` exists. Substantial but routine; a paper-only version captures most of the value.

## 5. Dead-ends check

Neither route maps onto an existing entry (`deadEndCount` was 166 at the time of writing).

* **Route (i)**: nothing in the catalogue concerns unions over `q`. Nearest neighbour is **#163**
  (SM, truncation quantifier order), about the position of `Y` in the quantifier prefix at fixed
  `n` — related in spirit, different statement. No mapping.
* **Route (ii)**: no logarithmic-density entry exists. New — catalogued as **#167**.
* **Third route**: **#101** (profinite bundle walk) used `Ẑ` as a home for the *walk*, to extract
  orbit information; here `Ẑ` is the *sample space of a population statement* and no orbit claim
  is made. **#155** (nonstandard/ultraproduct receptacle) was vacuous because the Loeb measure of
  the hyperfinite orbit is `0` for *every* sequence; here the orbit's measure-zero-ness is a
  declared scope limitation, not a defect. Neither applies — but §4.3's caveat must stay prominent
  so they are never conflated.

## 6. Recommendations, in priority order

1. **Formalize the finite-`S` simultaneous law** (§2.3). Small; the strongest honest
   natural-density statement available. *(Done in Session 312 — see
   `EM/Population/AlmostAllDensity.lean`.)*
2. **Adopt the `Ẑ` framing in the write-up** (§4), with the §4 caveat as prominent as the existing
   population caveat. Key sentence: *simultaneity in `q` is not a question of uniform rates but of
   countable additivity, and the ensemble on which the programme is exact is already the profinite
   one.*
3. **Do not pursue** a `q`-uniform rate for its own sake; record (K1)/(K2) so no future statement
   quietly assumes an explicit `n(q)`.
4. **Do not pursue** logarithmic density.
