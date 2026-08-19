# The profinite transfer: architecture of `μ(F_q) = 0`

**Session 314, coordinator design note.** Written *before* the formalization of WP-4, so that the
architecture is on record whether or not the Lean lands this session. Every Lean name below was
grepped from source; nothing was computed.

Companion documents: `simultaneous_in_q_scoping.md` §4 (why a countably additive ambient measure
is the repair for dead ends #167/#168), `sure_layer_missed_primes.md` (Session 313 — why the
*orbit* direction is closed).

---

## 0. What is being claimed, and what is not

**Claim.** On the profinite ensemble `(Ω, μ)`, `Ω = Π_{r prime} ZMod r` with the product of
uniform measures, the event

    F_q := { x ∈ Ω : the greedy orbit of x never selects q }

is μ-null for every prime `q`, and therefore — *by countable additivity* — `μ(⋃_q F_q) = 0`.

**Not claimed.** Anything about the Euclid–Mullin orbit of the seed `2`. `ℕ ⊂ Ω` (via the
coordinatewise reduction `ι`) is μ-null, so "μ-a.e. seed" does not imply "almost all integer
seeds"; a μ-null set can have upper density `1` in `ℕ`. Dead ends #90 and #117 are untouched.

**Mathematically new content: none.** The mathematics is the already-proved finite counting chain
`theorem_C → theorem_C_fiber → type_bad_small`. The passage from "one prime at a time" to "all
primes" is measure-theoretic packaging. That is a *feature* — there is no analytic risk in it — and
it must be stated, not hidden. Simultaneity in `q` was never a rate problem; it is an additivity
problem (#168).

---

## 1. The five ingredients

| # | Ingredient | Where |
|---|---|---|
| I1 | `(Ω, μ)` with the cylinder-count lemma `μ{x : redMod_M x ∈ T} = #T / M` for squarefree `M` | `EM/Population/ProfiniteEnsemble.lean` (WP-1) |
| I2 | the coordinatewise dynamics `profProd`/`profSeq`, and its agreement with `genProd`/`genSeq` | `EM/Population/ProfiniteDynamics.lean` (WP-2/3) |
| I3 | the covering lemma `AlmostAllDensity.uncaptured_in_few_classes`, with `q ≤ Y` and the band structure of `M` exported | `EM/Population/AlmostAllDensity.lean` |
| I4 | the coupling lemma `SeedCapture.genSeqAvoid_eq_genSeq_of_missed` | `EM/Population/SeedCapture.lean` (WP-6.1, landed) |
| I5 | CRT lifting `ℕ → ZMod (M·q)` surjective onto residue classes | Mathlib |

## 2. The transfer, in the contrapositive-free direction

Fix a prime `q` and `ε > 0`. Let `n, Y, Cc, M = modulus q Y, T` be the data of I3, so that

* `T ⊆ [1, M]` is the *three-bad-type* filter of `TypeBadSmall.type_bad_small`,
* `#T ≤ (ε/2)·M`,
* `M = ∏_{r ∈ bandUpTo q Y} r` — a product of **distinct primes `≤ Y`, all `≠ q`**,
* `q ≤ Y`.

Let `x ∈ Ω` satisfy

* **(H1)** `∀ j < n, profSeq x j ≠ q` — the profinite orbit misses `q`;
* **(H2)** `x_q ≠ 0` — the `q`-coordinate is a unit (the profinite analogue of `¬ q ∣ m`).

Let `c ∈ [1, M]` be the natural representative of `redMod_M x`. **Claim: `c ∈ T`.**

*Proof.* `T` is a filter by a disjunction of three conditions on `c`.

1. If the **degenerate-prefix** clause fails at `c` — i.e. `¬ ∀ j < n+1, 2 ≤ genSeqAvoid q c j ≤ Y`
   — then `c ∈ T` by the first disjunct. Done.
2. Else, if the **heavy window divisor mass** clause holds at `c`, then `c ∈ T` by the second
   disjunct. Done.
3. Else both fail; we must exhibit the fibre witness of `FiberTheoremC.FiberGood q Y Cc n c`,
   namely `∃ m', 1 ≤ m', ¬ q ∣ m', c ≡ m' [MOD M], ¬ ∃ j < n, genSeq m' j = q`.

   Take `m' ≥ 1` with `m' ≡ c [MOD M]` and `m' ≡ (x_q).val [MOD q]` — possible by CRT (I5), since
   `gcd(M, q) = 1` (`M` is a product of primes `≠ q`). Then `¬ q ∣ m'` by (H2), and
   `c ≡ m' [MOD M]` by construction. It remains to show `m'` misses `q` before depth `n`.

   Suppose not, and let `j₀ < n` be **minimal** with `genSeq m' j₀ = q`. For `j < j₀` the coupling
   lemma I4 gives `genSeq m' j = genSeqAvoid q m' j`, and Lemma A2
   (`SelectionLaw.genSeqAvoid_prefix_eq_of_modEq`, `m' ≡ c [MOD M]`) gives
   `genSeqAvoid q m' j = genSeqAvoid q c j ∈ [2, Y]` by clause 1. So *all of `m'`'s multipliers
   before `j₀` lie in `[2, Y]`, and the multiplier at `j₀` is `q ≤ Y`.*

   Now `m'` and `x` agree on **every prime coordinate `≤ Y`**: on `r ≠ q, r ≤ Y` because
   `r ∣ M` and `m' ≡ c ≡ x`; on `r = q` because `m' ≡ x_q [MOD q]` and `q ≤ Y`. So the band-local
   agreement lemma (WP-3b) applies up to and including step `j₀`, giving
   `profSeq x j₀ = genSeq m' j₀ = q`, contradicting (H1). ∎

Hence `{ x : (H1) ∧ (H2) } ⊆ { x : redMod_M x ∈ T }`, and by the cylinder-count lemma I1,

    μ{ x : (H1) ∧ (H2) }  ≤  #T / M  ≤  ε/2 .

The event `{x_q = 0}` has measure exactly `1/q`. Two ways to finish, both fine:
* state the headline **relative to** `{x_q ≠ 0}` (the exact profinite analogue of the integer
  statement, which also carries `¬ q ∣ m`); or
* absorb `1/q` into the bound, giving `μ(F_q^{(n)}) ≤ ε/2 + 1/q`, which is **not** enough on its
  own — so if the unrelativized form is wanted, one must additionally observe that `q ∣ x`
  (i.e. `x_q = 0`) makes the very first Euclid element `x + 1` a unit mod `q` forever, or simply
  keep the relativization. **Keep the relativization.** It costs nothing and is honest.

## 3. Why `q ≤ Y` is load-bearing

Step 3 needs `x` and `m'` to agree at the coordinate `q` *and* at every prime below `q`. The
modulus `M` deliberately omits `q` (dead end #165 — that omission is what makes the `q`-coordinate
free, and it is the whole reason `captured_iff_mem_visited` exists), so the `q`-coordinate is
supplied separately by CRT. But if `q > Y` there would be primes `p ∈ (Y, q)` on which `x` and `m'`
are uncorrelated, and the least prime with vanishing coordinate could differ: `profSeq x j₀` could
be some `p ∈ (Y, q)` rather than `q`, and no contradiction with (H1) follows.

The constants already force `q ≤ Y` (`Cc ≥ 48q` and the exclusion window `(Cc², Y]`, plus the
policy `n²/2 ≤ log Y`), but the finite theorems do not *state* it. Exporting it is the one genuine
prerequisite edit to the existing chain.

## 4. From `μ(F_q^{(n)}) ≤ ε` to `μ(⋃_q F_q) = 0`

* `F_q := { x : ∀ j, profSeq x j ≠ q } ⊆ F_q^{(n)}` for every `n`, so `μ(F_q) ≤ ε` for every `ε`,
  hence `μ(F_q) = 0`. **`F_q` need never be shown measurable**: a Mathlib `Measure` is an outer
  measure, so `measure_mono` applies to arbitrary sets. Only the covering cylinders must be
  measurable, and those are determined by finitely many coordinates.
* `μ(⋃_{q prime} F_q) = 0` by `MeasureTheory.measure_iUnion_null` (countable index; again valid for
  arbitrary sets, by countable subadditivity of the outer measure).
* **No `q`-uniform rate is used anywhere.** One takes `n → ∞` at *fixed* `q`, where every error
  term already tends to `0`, and lets countable additivity do the union. This is precisely the step
  natural density cannot perform (#167, #168).

## 5. Distinctions that must stay visible

* **Not dead end #101.** There `Ẑ` was proposed as a home for the *walk*, to extract orbit
  information. Here `Ω` is the *sample space of a population statement* and no orbit claim is made.
* **Not dead end #155.** The Loeb/ultraproduct receptacle was vacuous because the hyperfinite
  orbit has measure `0` for *every* sequence. Here the orbit's measure-zero-ness is a **declared
  scope limitation**, not a defect that voids the theorem: the theorem is about the ensemble.
* **`Π ZMod r`, not `Π ℤ_p`.** The programme conditions only on `m mod M` with `M` squarefree
  (`modulus q Y` is a product of *distinct* band primes), so `ZMod r` per coordinate suffices.
* The result is a **finite-horizon** statement made infinite by monotone intersection; there is no
  new analytic ingredient, and no equidistribution hypothesis occurs anywhere in the chain.
