# Logic routes to Mullin's conjecture: model theory, ultrafilters, geometric logic (2026-09-01)

Scope: a search for new leverage on MC from model theory, ultrafilter theory and geometric
logic, tested against the repo's walls (#90/#117 orbit specificity, #155 nonstandard
receptacle, #171 model obstruction, the transfer principle of `GrandOrbit.lean`, and the
screening test of `why_its_hard.tex`: *does the idea produce a positive divisibility fact
about a prescribed prime?*).  No computation.  Everything below is either a reformulation
that can be proved, a structural reason a technique cannot pass #90, or a small theorem
target.

Verdict up front.  None of the three theories reaches the orbit of 2.  Each of them, when
pointed at the problem, reconstructs the population picture the repo already has, under a
different name (Feferman–Vaught = CRT band locality, Loeb measure = finite-horizon laws,
invariant measures on the ultrafilter hull = Cesàro statistics), and #90 applies verbatim.
What survives is (a) two clean reformulations worth putting in Lean because they state
existing walls as theorems about compactifications and definability, (b) one framing
result about what kind of proof MC can have, and (c) a sharpening of #155 that also covers
the open population problem §G.

---

## 1. What logic sees immediately

### 1.1 Logical form of MC

* `MC(q)` ("q appears") is Σ₁; its negation is Π₁; MC is Π₂.  In the seed variable
  `m ∈ Ω = ∏_r ℤ/r`, "q captured within n steps" is *open* (a union over multiplier types of
  clopens, since the first n multipliers are unbounded), "q captured eventually" is open, and
  the basin `B = {m : GenMC'(m)}` is a dense G_δ of full Haar measure
  (`ProfiniteHeadline`).  MC says the point 2 lies in a dense G_δ.  Baire category cannot
  place a point any more than measure can: every countable set is meagre.
* MC is a single **geometric sequent in context**: `prime(q) ⊢_q ∃n. seq(n) = q`.  Its truth
  value is the same in every Grothendieck topos with a standard natural-numbers object
  (Π₂ arithmetic with a decidable matrix is absolute).  Nothing about truth follows; what
  follows is about *proofs*: a proof of MC from geometric axioms about ℕ would, by Barr's
  theorem, be constructive, and in Joyal's arithmetic-universe reading truth in the
  initial AU is a primitive-recursive stage bound `n(q)`.  So a "geometric" proof of MC is
  an **effective** MC.  The one non-geometric, ineffective step in the population layer is
  the Karamata/Tauberian input behind the ineffective horizon `Q(m)` in
  `GrowingRange.lean`.  This is the same target the analogy map already named (effective
  Mertens in progressions), now with the logical reason attached.

### 1.2 Nonstandard reading (all by transfer, no content)

In an ultrapower ℕ* with an infinite stage N:

* MC ⟺ every standard prime divides `P_N` ⟺ the least missing prime `q_N` is infinite ⟺
  `E_N − 1` lies in the external ideal `⋂_{r standard} rℕ*`.
* `E_N` is coprime to every standard prime (`AdelicShadow.hits_finite`), so its least
  factor `p_{N+1}` is an infinite prime whether or not MC holds.
* (C∞) ⟺ some infinite stage is composite; its negation puts a hyperprime at every
  infinite stage.

### 1.3 The ultrafilter hull of the orbit

Let `L ⊂ βℕ ∖ ℕ` be the set of limit points of `{P_n}` and `T̄ : βℕ → βℕ` the continuous
extension of `T(m) = m · minFac(m+1)`.  Let `ϕ : βℕ → Ω` extend the diagonal; `ϕ` is a
homomorphism for both `+` and `·`.

* `L` is `T̄`-invariant, `ϕ(L) = W` is the ω-limit set of the orbit in `Ω`, and
  MC ⟺ `W = {0}` (this is `mc_iff_tendsto_zero` restated).
* **Every point of `W` lies in the singular set `U = −1 + Ω^×` of the profinite greedy
  map** (the set where no coordinate of `x+1` vanishes, on which `leastVanishing` is
  undefined and Haar measure is `∏(1−1/r) = 0`).  Proof: `w = lim_U P_n` has
  `w_r + 1 = lim_U (E_n mod r) ≠ 0` for every `r`, because `r ∣ E_n` happens at most
  `π(r)` times (`hits_finite`).  So every integer orbit converges *into* the singular set;
  MC says it converges to the one point of `U` with all coordinates zero.  The
  "no continuous extension to any compactification" remark of `the_story.md` §5 is exactly
  that `T` does not extend to `U` in `Ω`; it does extend to `L` in `βℕ`.
* On the hull the dynamics is **multiplication by a unit**: for `p ∈ L`,
  `ϕ(T̄ p) = ϕ(p) · μ_p` with `μ_p = ϕ(lim_p p_{n+1}) ∈ Ω^×` (the multipliers are distinct
  primes, so `p_{n+1} mod r ≠ 0` for all but one `n`).  At a missed prime `q`, the
  `q`-coordinates of `W` form a set `W_q ⊆ (ℤ/q)^× ∖ {−1}` closed under the *coupled*
  multiplications `w ↦ w·μ_p`.
* `(L, T̄)` is a compact system, so **Krylov–Bogolyubov gives invariant probability
  measures on `L`**, and hence, for every missed `q`, an *exactly stationary* joint law `J`
  on `(position, multiplier) ∈ G×G` supported off the death curve `wμ = −1`.  So ergodic
  stationarity is not absent from the problem (the growth constant only forbids invariant
  measures on ℕ itself, not on the hull).  But these laws are limits of Cesàro statistics
  of the orbit, and #90's witness applies unchanged: `J` may have any position marginal
  and still avoid the curve (e.g. position uniform on `G∖{−1}`, multiplier ≡ 1).  Only a
  *product* law forces positive death mass, and product structure is CME.  This is the
  Marginal/Joint Barrier as a statement about invariant measures on a compactification.
* Idempotents of `(βℕ, ·)` map to `{0,1}`-vectors in `Ω` (divisibility idempotents);
  orbit limit points are not idempotent.  Hindman-type structure of the multiplier
  sequence gives existence of configurations somewhere, never at a prescribed point, and
  the transfer principle already says exactly what an "elsewhere ⇒ at 2" argument needs
  (a `GenMC`-invariant relation with a fat class of 2).

### 1.4 The model theory of the CRT layer is Feferman–Vaught

`ℤ/Y# ≅ ∏_{r ≤ Y} 𝔽_r`; the truncated greedy map `T_Y` is definable in the ring
(idempotents `e_r` are definable, "`x+1 ∈ rR`" is "the `r`-th coordinate vanishes").  The
Feferman–Vaught theorem for products reduces first-order statements about `ℤ/Y#` to
statements about the coordinates plus the Boolean algebra of the index set; that is the
type decomposition (`profProd_agree_of_agree`, `SelectionLaw.bandUpTo`) in logical form.
Like condensed mathematics (analogy map, 2026-08-20): a home, not a tool.

---

## 2. Why each technique cannot pass #90 (structural, not historical)

Applied to the orbit, every one of the following reproduces population data.  Applied to
the population, each reproduces what is already proved.

| Technique | What it produces here | Why it stops |
|---|---|---|
| Łoś / transfer | 1.2 | Conservative: every internal statement about the standard seed 2 is a standard statement. (#155 as stated.) |
| Loeb measure on hyperfinite seeds `[1, X]` | countable additivity over *standard* `q` for free: Loeb-a.e. hyperseed captures every standard prime at a standard step | The union over standard `q` is external. Overspill turns it into "all primes ≤ H for some infinite `H`", which pushes down to `finite_simultaneous_density` and nothing more. **So the Loeb route does not reach §G either**: §G is a uniform tail statement (N2′) about the *translation* of a countable union into natural density, not a countable-additivity problem in disguise. Sharpens #155 and #167/#168 together. |
| Ultrafilter limits / Keisler measures on the walk | 1.3, stationary joint laws | These are Cesàro statistics; #90 witness `(2,2,3,3)` vs `(2,3,2,3)`. |
| Pseudofinite / definable regularity (Chatzidakis–van den Dries–Macintyre, Tao's algebraic regularity, Hrushovski's stabilizer theorem, distal regularity) | equidistribution of *definable* sets in *large* tame finite structures without independence, multiplicativity, algebraic geometry or ergodicity (a genuine "fifth mechanism" in the abstract) | Needs the *walk* definable in a large tame structure. In `𝔽_q` the multiplier is not a function of the position. In `ℤ/Y#` the orbit segment is a definable set of size `K ≪ Y#`; regularity lemmas say nothing about sets of vanishing relative size. The FF model's large-field limit is the Weil regime, #127. |
| Motivic / Denef–Pas uniformity in the prime `q` | for `q` larger than the bounded types, the capture density within `n` steps is *exactly* `n/(q−1)` per type | This is CRT (Lemma C); uniform definability adds nothing. |
| Pointfree topology / locales; Baire category | basin `B` is a dense G_δ; MC(q) is a geometric (open) property of the seed | Countable sets are meagre; a specific point is invisible pointfree. |
| Automorphisms / genericity (stability-theoretic "generic type") | "2 must be generic over its own history" | `(ℕ, ·, S)` is rigid; in nonstandard models automorphisms fix 2. The type of 2 to horizon `n` is a congruence class mod `q·M_{Y(n)}` of density `≈ exp(−Y(n))`, always inside the horizon-`n` failure set of density `≈ exp(−n/q)`. This is #158 quantified. |
| Ramsey / idempotent ultrafilters (Hindman, Bergelson `{x+y, xy}`) | existence of configurations in one colour class | Existence somewhere; the transfer principle is the exact form of what is needed and shows it is a density question. |
| Undecidability (Conway class) | if the *seeded* orbit problem were undecidable, exceptional seeds would exist, refuting GenMC′ | `T` is one fixed low-complexity function, not a family; no universality is in sight. Also says nothing about seed 2. |
| Independence from PA | Π₂ independence via fast-growing witnesses (Paris–Harrington) | The heuristic stage `n(q) ≈ q log q` is polynomial; no fast growth. |
| Proof mining (Kohlenbach) | effective bounds from ineffective proofs of ∀∃ statements | Would give at best metastable rates for the ∀ε∃n∀X form; the explicit analytic route (Mertens in APs with constants) is more direct. |

Screening test: none of the items above produces a positive divisibility fact about a
prescribed prime.  All new facts obtained (1.2, 1.3) are *negative* (coprimality,
`W ⊆ U`), as the sign asymmetry predicts.

---

## 3. What survives, ranked

### A. Definability hierarchy of the No-Invariant Theorem (small theorem, formalizable)

`no_cvdp_obstruction` (`Obstruction/NoInvariant.lean`) rules out propagating invariants that
are unions of residue classes.  Two extensions, in order of difficulty:

1. **Presburger.**  A set definable in `(ℕ, +, <)` is eventually periodic: on `[K, ∞)` it is
   a union of classes mod `M`.  A propagating Presburger set containing the orbit tail
   therefore reduces, on a tail, to the periodic case, and the existing argument
   (`exists_tail_coprime` + `free_transition`) applies.  Statement: *no propagating set
   definable in Presburger arithmetic blocks a prime under `minFac`.*  Expected to be a
   short wrapper around the existing theorem.
2. **Automatic sets.**  A `k`-automatic set closed under the factor-tree relation
   `n ↦ n·p` (`p ∣ n+1`) should be eventually periodic (Cobham-type rigidity: automatic
   sets are multiplicatively fragile).  Literature check needed before claiming it (results
   on automatic sets stable under multiplication by integers coprime to `k` exist; the exact
   form needed here may not).  If true, the No-Invariant Theorem extends to every set
   definable in Büchi arithmetic.

Value: turns the informal thesis "any disproof must be anatomical" into "any propagating
obstruction is not definable in any tame expansion of `(ℕ, +)`", with full arithmetic
`(ℕ, +, ·)` as the trivial upper end (the orbit tail itself is a propagating definable set).
This is map-making, not progress on MC.

### B. The ultrafilter hull in Lean (language, but it states two walls as theorems)

A file `Population/UltrafilterHull.lean` proving, for every seed `m ≥ 1`:

* `omegaLimit_subset_singular`: every limit point of `genProd m` in `Ω` lies in
  `−1 + Ω^×` (from `hits_finite`);
* `genMC_iff_omegaLimit_eq_zero`: GenMC′(m) ⟺ the ω-limit set is `{0}`;
* the hull dynamics is multiplication by a unit, and the stationary joint law exists and
  can avoid the death curve with uniform position marginal (a finite witness in
  `(ℤ/5)^×`, matching #90/#117).

Value: the four-way blocker's fourth leg ("no ergodic stationarity") becomes precise:
stationarity exists on the compactification and is #90-blind.  Mathlib has `Ultrafilter`,
`StoneCech`, and `Filter.Tendsto` in profinite groups; the limit-set statements need only
the product topology on `Ω`, not `βℕ`.

### C. Effective MC is the only kind of proof the geometric reading allows (framing)

Record 1.1 in the paper's "why it's hard" section: MC is a geometric sequent; a proof from
geometric axioms is constructive and yields a computable appearance stage; the population
layer's one ineffective step is the Karamata input, and its effective replacement is
Mertens in progressions with explicit `O(1)`.  No theorem; one paragraph.

### D. Sharpened dead-end entries (candidates, not added)

For `tools/dead_ends.tsv`, next numbers from 178:

* *Loeb measure for the simultaneous-in-`q` law.*  Countable additivity over standard `q`
  is free but external; overspill returns finite simultaneity.  §G is not a
  countable-additivity problem.  Extends #155, #167, #168.  Category SM.
* *Definable-regularity as a fifth equidistribution mechanism.*  Needs the walk definable
  in a large tame finite structure; the only candidate is `ℤ/Y#`, where the orbit is a
  vanishing-density definable set.  Category TM.
* *Invariant measures on the ultrafilter hull.*  Exist, project to stationary joint laws,
  are Cesàro statistics; #90 applies.  Category OS (witness: B above).

### E. One question left open (one scoping pass at most)

The repo's `RotorRouter.lean` proves that a *deterministic* update rule (cycle through a
generating set at each vertex) forces coverage of a finite group.  The logical question
"which deterministic multiplier rules `w ↦ M(w)` force the partial products to cover `G`"
is well posed and has answers (rotor rules, and more generally rules whose per-vertex
multiplier sequences are complete in the sense of visiting a generating set).  The EM rule
is not of this type and nothing known about `minFac` puts it there, so this is expected to
land as another instance of the Marginal/Joint Barrier.  Recorded so it is not rediscovered.

---

## 4. Summary for the story

Model theory, ultrafilters and geometric logic add a compactification (`βℕ`) on which the
greedy map extends and has invariant measures, a definability reading of the obstruction
theorem, and a precise account of what kind of proof MC can have.  They do not add a
mechanism: every equidistribution or genericity statement they deliver is about definable
or measurable *sets*, and the orbit of 2 is a point.  The wall #90 is, in this language, the
statement that hitting `−1` is not a property of the type of the orbit over any of its own
finite-horizon data.

---

## 5. Follow-up question: nonstandard models with new minimal factors or adjoined missed primes

Asked 2026-09-01: could one build a nonstandard model by adding new minimal factors, or by
adjoining the primes missed by the orbit of 2 or by a generic orbit?  Four readings, all closed.

1. **New minimal factor for a Euclid number.**  `minFac E_n = p` for standard `n` is a Σ₁
   fact, provable in any theory containing the true Σ₁ sentences; no model can change it.
   At infinite `N` the least factor is an internal infinite prime whose standard residues
   are the ultrafilter limits of the standard multipliers.  Nothing to adjoin.
2. **Adjoin a prime missed by the orbit.**  (a) Missed at every standard stage: consistent by
   compactness, but the constant is infinite if MC holds, and infinite primes are missed at
   standard stages trivially.  MC ⟺ every infinite prime is captured at some infinite stage
   (transfer).  (b) Missed internally: `Th(ℕ) + ∀n seq n ≠ c` is consistent iff MC is false;
   over PA it is consistent iff PA ⊬ MC, so building the model is an independence proof, not
   a truth proof, and there is no evidence of unprovability (heuristic stage `n(q)` is
   polynomial).
3. **At the level of the axioms the proofs use.**  Already done: `SeedCapture.genSeqAvoid`
   re-chooses the minimal factor at every step to avoid `q`, satisfies the whole sure layer,
   and misses `q` by construction (#171).  Only axioms equivalent to MC kill this model.
4. **A generic seed with the type of 2.**  A hyperseed `m* ≡ 2` mod every standard prime has
   the same multipliers as 2 at every standard stage (band locality), hence the same standard
   captures; but `{m* : m* ≡ 2 mod all standard r} ⊆ 2 + Mℕ*` for every standard `M`, so it is
   Loeb-null and the seed-average law does not see it.  Concrete form of #158.

The only consistent way to "add primes" is to change the ring (norm-minimal rule over a number
ring, cf. the FF variant); ties between Galois-conjugate primes force a symmetry-breaking
tie-break or a collapse to the rational prime.  Comparison-class question, not a logic one.

---

## 6. Follow-up question: F_p[X] → F_p((X)) → Q_p → Q

Asked 2026-09-01: prove full MC over `F_p[X]`, extend a weaker form to `F_p((X))`, transfer to
`Q_p` (Ax–Kochen–Ershov), then to `Q`.  Every arrow fails, and the first is the problem itself.

* **`F_p[X]`.**  The FF model is not easier in the relevant regime: exact telescope, Weil RH,
  Dirichlet density all available, orbit specificity unchanged (#127, #129; "#90 where every
  analytic input is a theorem").  Least-degree factor is constructible, so bounded-degree
  dynamics is definable over `F_p` uniformly in `p`; Ax/CDM then make every bounded-horizon
  statement a Frobenius set of primes up to finite exceptions.  That is the *large `p`, fixed
  degree* regime.  FF-MC at fixed `p` is the *large degree* regime (the analogue of large
  `x`), untouched by pseudofinite methods.  The actual rule's tie-break between irreducibles
  of equal degree is not definable; the definable variant (product of all minimal-degree
  factors) is a Booker-type steered variant.
* **`F_p[X] → F_p((X))`.**  A local field has one prime; MC couples infinitely many primes
  through the ordering `minFac` imposes.  The completion at `X` sees only the residue walk at
  the single prime `X`, one coordinate of the profinite picture already in the repo.  No
  weaker form of MC lives in one local field.
* **`F_p((X)) → Q_p`.**  AKE transfers valued-field sentences, asymptotically in `p`; at fixed
  `p` the fields are not elementarily equivalent.  The EM recursion needs `ℤ`, the primes and
  their order, none definable in a local field.  There is no sentence to transfer.
* **`Q_p → Q`.**  No local-to-global principle for a globally defined orbit; the adelic
  reading (Teichmüller component of the walk in `ℤ_q^×`) was closed as #177.
* **Ring level.**  Ultraproducts of `F_p[X]` are polynomial rings over pseudofinite fields of
  characteristic 0, not `ℤ`.  The function-field analogy guides, it has never transferred a
  proof through completions.

Only FF question still open from the analogy map: is the backward tree of the min-degree
dynamics algebraic over `F_q[t]`?  Comparison-class question; no transfer hope attached.

---

## 7. Pushing the profinite picture (asked 2026-09-01)

Re-derived the dynamics of the greedy map `T` on `Ω = ∏_r 𝔽_r` from scratch.  Notation:
`Z(x) = {r : x_r = 0}`, `S_p = {x_p = −1, x_r ≠ −1 for r < p}` (clopen), `U = −1 + Ω^×` the
singular set, `λ(x)` the least vanishing coordinate of `x+1`.

### 7.1 Structure facts (all elementary, none in Lean yet)

* `T|_{S_p}` is multiplication by `p` with `x_p = −1` pinned, hence **injective on each
  stratum**, measure-preserving onto its image `T(S_p) = {y_p = 0, y_r ≠ −p for r < p}`.
  Images overlap; the number of preimages of `y` is `#{p ∈ Z(y) : y_r ≠ −p ∀ r < p}`, finite
  a.e.  The Ω-backward tree is *free* of the integer square condition `p² ∣ N + p`
  (`GrandOrbit.preimage_cond_iff_sq`): Ω-preimages of `ι(N)` are `ι(N/p)` with the
  `p`-coordinate overwritten to `−1`; they are integers iff the coincidence holds.
* `Z(Tx) = Z(x) ∪ {λ(x)}`: exactly one new zero per step; nonzero coordinates stay nonzero.
* **Coding.**  Let `Λ(x) = (λ(Tⁿx))_n` be the itinerary (an injective prime sequence).  For a
  unit seed, `x_{p_n} = −(p_0⋯p_{n−1})^{-1} mod p_n` is forced, so on `B ∩ Ω^×` the map
  `Ξ : (p_n) ↦ x` inverts `Λ`.  An injective sequence is an itinerary iff for every inversion
  `n < m`, `p_m < p_n`: `p_m ∤ p_n p_{n+1} ⋯ p_{m−1} − 1`.  Hence
  **`B ∩ Ω^× ≅ admissible enumerations of the primes`**, `T` conjugate to the shift.
  Checked against the true orbit: inversions `(43,13)`, `(7,5)`, `(43,5)`, `(13,5)`, `(53,5)`
  all satisfy the condition.
* Provable basin points: the increasing enumeration has no inversions, so the **primorial
  point** `x*_p = −((p−1)#)^{-1} mod p` lies in `B` with itinerary `2,3,5,7,…`; `x* ∉ ι(ℤ)`.
  Any enumeration with finitely many inversions is decidably admissible.
* Factor-tree paths from seed 1 are exactly the sequences with `Ξ(π) = 1` *without* the
  least condition; the greedy path is the leftmost.  MC ⟺ `Ξ(Λ(1)) = 1` ⟺ `Λ(1)` surjective.
* **No invariant probability off `U`**: for `ν` invariant, `E_ν|Z ∩ [1,Y]|` is nondecreasing
  and strictly increases on `{λ ≤ Y}`, so `ν{λ ≤ Y} = 0` for all `Y`.  Dissipative system; the
  profinite form of the growth-constant argument (`the_story.md` §2).
* Haar pushes forward under `Λ` to the box-sieve selection law (`SelectionLaw`).
* The natural `T`-invariant "arithmetic" subspace is `Q = {x : every rational fibre
  {r : x_r = a/b mod r} is finite or cofinite}`; `Q ⊇ ι(ℚ)`, `Q` is `μ`-null (Borel–Cantelli
  per rational), and the countable part of `Q` (finite modifications of rationals) is where
  the CRT-lift arguments of the seed law live.

### 7.2 Min/max dichotomy = profinite continuity (theorem target)

A selection rule `σ` on `Ω ∖ U` is continuous iff locally constant.  For a priority order
`≺` on primes, `σ_≺(x) = ≺-least r with x_r = −1` is continuous iff `≺` has **order type ω**
(every prime has finitely many predecessors).  Then `{σ_≺ = q}` is a clopen cylinder, i.e.
capture is a congruence condition, and every ingredient of `no_cvdp_obstruction`
(`hittingSet_finite` via finitely many `≺`-predecessors each appearing once,
`exists_tail_coprime`, rule-symmetric `free_transition`) goes through.  `maxFac` does not
define a map on `Ω` at all; that is where Cox–van der Poorten lives.

* Lean target: parametrise `Obstruction/NoInvariant.lean` by an order of type ω; the
  statement "no congruence invariant blocks a prime under any ω-greedy rule".
* New averaging axis: **priority orders** (besides seeds and paths).  A.a. ω-orders should
  give a surjective path from 1 by the coverage technology (mild correlations: a prime
  divides ≤ π(q) Euclid numbers).  The archimedean order is one point of that space (#90,
  third guise) — and the *only* order carrying the growth telescope (`minFac ≤ √E`), so the
  (C∞) floor exists only for `<`.

### 7.3 The cofactor's two shadows

In `Ω_Y = ∏_{r ≤ Y} 𝔽_r`, with `s_n = P_n mod`, the walk is
`s_{n+1} = Φ₆(s_n) · ι(c_n)^{-1}`, `Φ₆(w) = w(w+1)`, `c_n = E_n / p_{n+1}` the discarded
cofactor (coordinatewise where `c_n` is a unit; internal selections where a coordinate of
`s_n + 1` vanishes).  `log c_n` is the growth defect (`defect_eq_log_cofactor`); `ι(c_n)` is
the walk's noise.  The two projections meet only at `c_n = 1` (autonomous branch).  `c_n` is
`p_{n+1}`-rough of prescribed size; rough integers occupy every unit class, so the residue is
unconstrained by the size.  Unifying identity, no lever.

### 7.4 Why §G is not reachable from Ω (record as dead-end refinement)

`F = ⋃_q F_q = ι^{-1}(E)` with `μ(E) = 0` (`measure_some_prime_missed_eq_zero`).  The
pullback of a null set need not have density 0; each `F_q` does (seed law), the union is the
question.  Structural reason the tail cannot be controlled from `Ω`: seeds `m ≤ X` occupy
the residues `1..X` mod any prime `q > X`, so they are not equidistributed mod `q`, and
capture of `q` within `n` steps needs `P_m(k) ≥ q − 1`, i.e. at most `n` seeds per type.
The tail `q > Q` of §G is therefore "every seed captures all primes beyond a threshold `Q`
independent of the seed, for a.a. seeds" — cofinite GenMC with uniform threshold on a
density-one set, the Collatz-like upper tail.  Profinite points have no size; the tail is
archimedean.  No measure on any compactification of `ℕ` sees it (countable sets are null).

### 7.5 What not to push

Any further measure on `Ω`, `Ẑ`, the Bohr compactification, or the adelic solenoid: `ℕ` is
countable and null in all of them.  The unfinished part of the profinite layer is 7.1 (the
classification), which would turn it from a receptacle into a classified object; 7.2 is the
one new theorem with conceptual content.

---

## 8. Distant roads and visions (2026-09-01, second pass)

Asked for new roads, including distant analogies and visions.  Each item below is tagged
*theorem-shaped* (could go to Lean), *reading* (literature check), or *language*.

### 8.1 The least-prime-factor recurrence class (reading)

EM is one member of a class of deterministic "lpf-driven" recurrences whose common open
question is *every prime appears*:

* multiplicative, shift `b`: `P ↦ P · lpf(aP + b)` — exactly the greedy orbits of the
  **rational points** `ι(a/b) ∈ Ω` (primes dividing `b` are dead coordinates).  `b = 1` is EM;
  `a = 1, b = 2` from seed 1 starts along the Fermat numbers (`3, 5, 17, 257, 65537, 641, …`)
  until `F_5` breaks the autonomous branch.  The Euler–Lucas congruence on Fermat factors
  shows a *structured* start can only restrict classes, never help.
* additive, linear scale: **Rowland's sequence** `a(n) = a(n−1) + gcd(n, a(n−1))`, `a(1) = 7`,
  whose reset states `s` evolve by `s ↦ s + lpf(s) − 1` and whose produced primes are
  `lpf(s)`; Cloitre-type variants likewise.  Not cited anywhere in the repo.

Why it matters: the additive member lives at *linear* scale, where the orbit is a positive-
density-like set of integers and sieve methods are at full strength.  If "every odd prime
appears" is open even there (Rowland 2008 left it open; check Chamizo–Raboso–Ruiz-Cabello
2011), the difficulty is selection, not size — the strongest possible confirmation of the
story's thesis.  If it is solved, its mechanism is the first proof of an "every prime appears"
statement for an lpf-driven dynamics and must be studied for transfer.  Either outcome is
informative; the task is reading, not computation.

### 8.2 The unique integer unit (language, one small theorem)

`ι(m) ∈ Ω^×` iff `m = 1`.  The Euclid–Mullin orbit is the orbit of the *only* integer unit,
and for a unit seed the accumulator is the bare product of its own itinerary:
`p_n ∣ p_0⋯p_{n−1} + 1` is a purely internal condition on the sequence.  The set of all such
sequences is the factor tree from 1; Pollack–Treviño give a surjective one; MC says the
leftmost (greedy) one is surjective.  Rewriting-theory reading: the factor DAG is
*non-confluent* (firing `p` then `p'` needs `p' ∣ p − 1`), so the abelian-network / Newman
least-action principle ("every complete execution reaches the same state") is unavailable, and
"the leftmost strategy is normalising" is a theorem only for orthogonal systems.  MC is the
non-orthogonal case.  Small theorem: `ι(m)` is a unit iff `m = 1`; unit-seed coding as in §7.1.

### 8.3 Greedy repair of the primorial order; head capture = hit (language)

The ideal itinerary `2, 3, 5, 7, …` is realised in `Ω` by the primorial point (§7.1) and by
*no* integer: the integer 1 would capture `q` at its turn iff `q ∣ (q−1)# + 1`, heuristic
probability `1/q`, so almost every prime is *deferred* at its turn and the greedy rule picks
the least factor instead, scrambling the order.  MC = every deferral is eventually repaired.
For the **head** (least missing prime) exposure is automatic — all smaller primes divide
`P_n`, so `q ∣ E_n` alone captures — hence MC ⟺ every head is eventually *hit*, and MC
failure ⟺ one eventual head `q` with `q ∤ E_n` for all large `n`.  The queue picture: the
head is served with heuristic rate `1/q_n` per step; the deterministic question is whether
the clock ever stops.

### 8.4 Class infinitude mod 4: the weakest statement with a positive fact (theorem-shaped)

The only frozen non-trivial residue along the orbit is 2-adic: `P_n ≡ 2 (mod 4)` for `n ≥ 1`,
so `E_n ≡ 3 (mod 4)` and **every Euclid number has a prime factor `≡ 3 (mod 4)`** — a
*positive* divisibility fact about a class at every step (the sign asymmetry allows class
facts, not prime facts).  With `hits_finite`, infinitely many distinct primes `≡ 3 (mod 4)`
divide Euclid numbers.  Define

  **CI(3 mod 4)**: infinitely many Euclid–Mullin primes are `≡ 3 (mod 4)`.

* MC ⟹ CI; WeakMullin ⟹ CI (the class has divergent reciprocal sum).
* Perpetual primality ⟹ CI (then `p_{n+1} = E_n ≡ 3`).  Hence **¬CI ⟹ (C∞)**, with every
  late cofactor `c_n ≡ 3 (mod 4)`: the guaranteed 3-mod-4 factor is never the least.
* CI is independent of the RD/(C∞) ladder (RD is consistent with all late multipliers
  `≡ 1 (mod 4)`), so it is a new rung: a *marginal* statement about the multiplier sequence
  (the weakest non-degeneracy form of MME), not a hitting statement.
* Generalisation (cheap lemma): if the late multipliers are confined to a proper subgroup
  `H ≤ (ℤ/M)^×` and `E_n mod M ∉ H` eventually, then (C∞).  Reciprocity gives no more
  (`no_reciprocity_induction_proof`; the symbol data is identically consistent).
* Status: apparently open and apparently not in the repo (check `WeakMullin.lean`,
  `Reciprocity/`, `composite_floor.tex` §reciprocity before adding).  Still #90-shaped (one
  specific sequence of least factors), but it is the cleanest target below MC that carries an
  unconditional positive ingredient, and the first candidate for any new marginal technique.

### 8.5 Function-field affine equivariance (theorem-shaped, small)

With the symmetric tie-break (multiply by the product of *all* minimal-degree irreducible
factors), the FF greedy map commutes with `Aut(𝔽_q[t]) ≅` the affine group `t ↦ at + b`, so
"seed `s` misses `Q`" ⟺ "seed `σs` misses `σQ`".  This is the first cross-seed coupling
beyond `T`-invariance the project has (the analogy map asked for one).  It couples only the
`q(q−1)` conjugates of a degree-1 seed, a negligible class for any density statement, and the
large-`q` regime remains Weil/Chebotarev (#127).  Record as an FF fact; no integer analogue
(`(ℤ, ·, S)` is rigid).

### 8.6 Shapes that do not transfer (language)

* *Unlikely intersections reversed.*  Zilber–Pink-type theory bounds how often a curve meets a
  countable union of special subvarieties; here the orbit is *always* in the coincidence set
  (`DivisorFinite`) and the question is convergence to one special point.  No theory of
  "coincidences that must persist".
* *Entropy decrement (Tao).*  Needs the dilation structure `n ↦ pn` of the integers and
  logarithmic averaging; the orbit has neither.
* *Arboreal / Odoni.*  Odoni's density-0 theorem for prime divisors of Sylvester's sequence
  is the autonomous-branch statement; the greedy step destroys the tree at every composite
  stage (already in `why_its_hard.tex`).
* *Egyptian fractions.*  The greedy algorithm for 1 gives Sylvester's sequence; the EM
  telescope `1/P_n − 1/E_n = 1/(c_n P_{n+1})` sees the cofactor's *size* only.

### 8.7 What a proof must look like (constraint, not road)

* The honest conjecture is **universal**: every seed captures every prime coprime to it
  (`GenMC′` for all `m`).  No seed is known to fail, and by the No-Invariant Theorem a failure
  certificate would have to be anatomical.  So a proof must be uniform in the seed; nothing
  about `2` or `1` can be used except that `1` is the unit (8.2).
* It must produce a positive divisibility fact at the head (8.3).  The only unconditional
  positive fact on file is the mod-4 class fact (8.4).
* It must say something about the least prime factor of *one* rough integer in a known class
  mod `M` — the statement that no sieve, character sum, or equidistribution theorem makes for a
  single integer.  Every road in §§1–8 ends here.

### 8.8 Ranked follow-ups

1. Reading: status of "every odd prime appears" for Rowland-type additive lpf recurrences.
2. Lean, small: `iota m` unit iff `m = 1`; unit-seed coding; the mod-4 class-hit lemma;
   confinement ⟹ (C∞); ¬CI(3 mod 4) ⟹ (C∞).
3. Lean, moderate: the classification theorem (§7.1) and `no_cvdp_obstruction` for ω-orders (§7.2).
4. Record 8.5 in the FF section of the paper.

---

## 9. Mullin's conjecture over `𝔽_2[X]` (asked 2026-09-02)

Seed `X`; `FFEMData` in the repo quantifies over all tie-breaks.  Over `𝔽_2` the sequence
starts `X, X+1, X²+X+1, X⁴+X+1`, with `P_n = L^n(X)` for `n ≤ 3` where `L(P) = P² + P`, and
`E_3 = X⁸+X⁴+X²+X+1 = (X⁴+X³+1)(X⁴+X³+X²+X+1)` — a **tie** between two quartics swapped by the
involution `σ : X ↦ X+1` (the accumulator `P_3` is `σ`-invariant, so a non-symmetric
minimal factor must come with its conjugate; ties are forced by symmetry).

### 9.1 A theorem: the composite floor is unconditional over `𝔽_2[X]`, with sharp constant 3

In characteristic 2 the take-all map `P ↦ P(P+1) = P² + P = (F+1)P` is **additive**
(`F` = Frobenius).  If `E_m, E_{m+1}, E_{m+2}` are irreducible then
`P_{m+3} = (F+1)³ P_m = P_m⁸ + P_m⁴ + P_m² + P_m`, and the polynomial identity (char 2)

    y⁸ + y⁴ + y² + y + 1 = (y⁴ + y³ + 1)(y⁴ + y³ + y² + y + 1)

gives `E_{m+3} = (P_m⁴+P_m³+1)(P_m⁴+P_m³+P_m²+P_m+1)`, reducible.  So **no four consecutive
Euclid numbers are irreducible, for any seed**; the seed `X` attains three, so the bound is
sharp.  Consequences via `DegreeTelescope`: reducible stages have density `≥ 1/4`,
`ffDeg_le_pow_mul` gives `deg P_N ≤ (3/4)^{⌊N/4⌋} 2^N deg(seed)`, hence
**`ffGrowthConstant = 0` for every `FFEMData` over `𝔽_2`, and `(C∞)_FF` holds unconditionally**
(`ffInfinitelyManyReducible_iff_ffGrowthConstant_eq_zero`).  Over `ℤ` and over `𝔽_p[X]`,
`p` odd, the same statement is open (Sylvester/Fermat-shaped): there `x² + x` is a genuine
quadratic dynamical system, in char 2 it degenerates to a linear one.  This is the first
ring in the comparison class where the bottom rung of the ladder is a theorem.  Lean cost:
the identity is `ring_nf` in `Polynomial (ZMod 2)` plus the `FFEMData` recursion; no
algebraic closure needed.

Conceptual reason (Artin–Schreier): the roots of `(F+1)^k P + 1` satisfy `P(β) = y` with
`(F+1)^{k+1} y = 0`, so `y ∈ 𝔽_{2^{2^j}}` for `2^j ≥ k+1` and `deg β ≤ 2^j deg P`, while an
irreducible `E_{m+k}` would need `deg β = 2^k deg P`.  For `k = 3`: `4 < 8`.

### 9.2 Other char-2 structure (unconditional, not yet in Lean)

* **Trace exclusion on autonomous runs.**  `L(𝔽_{2^d}) = {Tr = 0}`, so after one autonomous
  step no irreducible of odd degree can be captured on that run; after `2^{v_2(d)}` steps no
  irreducible of degree `d` can (`1` lies in the `(F+1)`-primary part of `𝔽_{2^d}` as an
  `𝔽_2[F]`-module, which `(F+1)^{2^{v_2(d)}}` kills).  Char-2 twin of `AutonomousMap.lean`'s
  `Φ₃` exclusion, exact and for all degrees.  Runs are ≤ 3 long by 9.1, so the exclusion is
  short-lived — the mechanism, not the conclusion, is the point.
* **The death value is the identity**: `Q ∣ P + 1 ⟺ P ≡ 1 (mod Q)`; the walk in the
  odd-order group `𝔽_{2^d}^×` must return to `1`.  Every element is a square; there are no
  quadratic characters and no reciprocity layer at all.
* **Two frozen classes** (vs one over `ℤ`, none over `𝔽_p`, `p` odd): `P_n ≡ X (mod X²)` and
  `P_n ≡ X+1 (mod (X+1)²)`, so every `E_n` has an irreducible factor with `p′(0) = 1` and one
  with `p′(1) = 1`.  Frozen classes come exactly from residue fields with trivial unit group,
  i.e. from `𝔽_2` — the "mod 4" phenomenon of §8.4 is a char-2 phenomenon.  The char-2 twin
  of CI(3 mod 4): infinitely many FF-EM irreducibles with `p′(0) = 1`.
* **Simultaneous walk as a function.**  `𝔽_2[X]/(X^{2^d}+X) ≅` Frobenius-equivariant maps
  `𝔽_{2^d} → 𝔽_{2^d}`; the walk at all `Q` with `deg Q ∣ d` is the function `α ↦ P_n(α)`;
  capture zeroes the minimal Frobenius orbit of the level set `{P_n = 1}`; FF-MC ⟺ the
  function is eventually `0` on every `𝔽_{2^d}`.  This is the profinite picture of §7 with
  `Ω_d` a ring of functions on a finite field.
* **After a run of `k` autonomous steps the Euclid number is a norm**:
  `E_{m+k} = ∏_{y : (F+1)^k y = 1} (P_m − y)`, so its factorisation over `𝔽_2` is the
  factorisation of the *shifted* polynomial `P_m − y` over `𝔽_2(y)`.  The greedy selection
  after a run is "least-degree factor of `P_m − y` over an extension".

### 9.3 What does not change

The top of the ladder is untouched: FF-MC over `𝔽_2` is still "the walk of one specific
sequence returns to `1` in `𝔽_{2^d}^×` at an exposed time", #90 verbatim; the population
statements are exact (character sums cancel exactly, `FFCharacterSums.lean`) and say nothing
about the orbit; and the tie-break quantification makes FF-MC a family statement, with only
the first tie forced symmetric.  RD-FF (`∑ 2^{−deg p_k} = ∞`) stays open: 9.1 gives
`deg p_{n+1} ≤ 2^{(1−c)n}`, still exponential.

### 9.4 Correction to the catalogue

Dead end #129 and `FunctionField/Analog.lean` (line ≈ 900) state
`ffProd(2)+1 = t⁴+t+1 = Φ₅(t)`.  The identity `t(t+1)(t²+t+1)+1 = t⁴+t+1` is right, but
`t⁴+t+1 ≠ Φ₅ = t⁴+t³+t²+t+1`; `t⁴+t+1` is a factor of `Φ₁₅`.  `Φ₅` first appears one step
later, as one of the two tied factors of `ffProd(3)+1`.  The conclusion of #129 (Galois
groups over finite fields are cyclic, so FFLM is structurally false) is unaffected.

### 9.5 Ranked follow-ups

1. Lean: `ff_no_four_consecutive_irreducible` (char 2, the `ring_nf` identity) and
   `ffGrowthConstant_eq_zero_of_two` for every `FFEMData 2`; paper: FF section and the
   variants landscape (first ring with (C∞) proved).
2. Lean, small: trace exclusion on autonomous runs; the two frozen classes; the `σ`-forced
   tie at stage 3.
3. Fix the `Φ₅` identity in `tools/dead_ends.tsv` (#129) and `Analog.lean`, regenerate.
4. Do **not** expect the char-2 linearity to reach MC: it only controls autonomous runs,
   which are ≤ 3 long; the greedy steps between them are as opaque as over `ℤ`.

---

## 10. Hardness of factoring and MC (asked 2026-09-02)

No formal link either way.  MC is a fixed Π₂ sentence; complexity assumptions are about
algorithms.  Decisive contrasts: over `𝔽_q[X]` factoring is polynomial time and FF-MC is
exactly as open (every computational input easy, question unmoved — the computational twin
of the paper's "every analytic input a theorem"); the digits of π are cheap and normality is
open.  The barrier is #90, not cost.

True on the computational side:
* Computing the sequence = factoring numbers `N` with `N − 1` completely factored
  (`E_n − 1 = P_n`).  Primality is polynomial (Pocklington–Lucas `n−1` test); factoring is not
  known to be easier.  Heuristic size `≈ n²` bits, so EM ∈ P^{factoring}; the known terms stop
  at 51 for this reason.
* Perpetual primality = the computationally easy branch (next term `= E_n`, certified prime in
  polynomial time).  MC ⟹ (C∞) ⟹ infinitely many genuine factorisations are required.
* If MC fails, the missed set is co-c.e. and need not be computable.

Heuristic squeeze: hardness of factoring Euclid numbers excludes *predictive* proofs (a rule
giving the next least factor would factor them); #90 excludes *statistical* proofs; what
remains is the Euclid/Dirichlet shape — existence of a capture without location (8.7).  A
proof of MC is not a factoring algorithm; a factoring algorithm is not a proof of MC.

Pseudorandomness: hardness makes "the least-factor sequence is computationally
indistinguishable from the Shanks model" *consistent* (for π it is not), and that hypothesis
implies MC (a trivial martingale detects "q never appears").  But hard ≠ unbiased (all late
multipliers ≡ 1 mod 4 is hard-compatible), so hardness does not imply it; it is CME in
complexity clothing.  Not a road; recorded so it is not reopened.

---

## 11. The growth / least-factor axis (asked 2026-09-02)

### 11.1 Over `ℤ`: closed at the bottom, empty in the middle

* Proved: `log P_n ≥ θ(p_{n+1}) ≈ n log n` (distinct multipliers); `log P_n ≤ C (3/4)^{#comp} 2^n`.
* Heuristic (rough-number law, `P(lpf = p | B_n-rough) ≈ log q_n / (p log p)`):
  `E[log p_{n+1}] ≈ log q_n · log(log E_n / log q_n) = O(log² n)`, so **`log P_n ≍ n log² n`**
  (≈ 340 digits at `n = 51`; record composite 335 digits).  Hence `∑ 1/log E_n < ∞`:
  **finitely many prime Euclid numbers** (Cev), `ρ⁺ := limsup log lpf(E_n)/log P_n = 0`,
  polynomial growth (PG).  Ladder: PG ⟹ (C∞), Cev ⟹ (C∞), Cev ⟺ ρ⁺ < 1; PG, Cev are
  independent of MC (MC bounds nothing; huge multipliers are compatible with MC).
* Any improvement of the `2^n` bound needs a positive density of composite stages = (C∞)
  with a rate = Fermat-shaped.  The 2026-08-17 verdict ("no slack") stands.

### 11.2 Over `𝔽_p[X]`: the floor is provable with explicit constants

On an autonomous run `E_{m+k} = g_k(P_m)`, `g_k = Φ₃ ∘ Φ₆^{k−1}` (the level polynomials of
`ArborealTower`/`BackwardLevels`).  `g_k` reducible over `𝔽_p` ⟹ `k` consecutive irreducible
Euclid numbers force the next to be reducible, for every seed of positive degree.

* `p ≡ 1 (mod 3)`: `Φ₃ = (y−ω)(y−ω²)` splits, `E_{m+1} = (P_m−ω)(P_m−ω²)`: **constant 1**.
* `p = 2`: §9.1, **constant 3** (sharp).
* `p ≡ 2 (mod 3)`: by Capelli + the finite-field norm criterion (`x` square in `𝔽_{p^d}` iff
  `N(x)` square in `𝔽_p`), `g_k` is irreducible iff `g_{k−1}` is and
  `N_k := ∏_{g_{k−1}(α)=0}(1+4α) = 4^{2^{k−1}} g_{k−1}(−1/4)` is a non-square mod `p`, i.e.
  iff the **numerators of `Φ₆^{j}(−1/4) + 1` — `13, 217, 57073, …` — are all non-squares**.
  (Over `ℚ` the repo found level 3 depends on `ω`; over `𝔽_p` the norm makes it rational
  again.)  So: `(13/p) = 1` ⟹ constant 2; `(217/p) = 1` ⟹ constant 3; etc.
* Exceptional primes: the critical orbit of `−1/4` under `y ↦ y² + y` in `𝔽_p` is a finite
  cycle; `p` is exceptional iff every shifted value on it is a non-square.  **`p = 5` is
  exceptional**: orbit `1, 2, 1, 2, …`, shifted values `3, 2`, both non-squares mod 5 — the
  bare tree is stable over `𝔽_5` (Jones/Ayad–McQuillan stability), and the floor there needs
  the seed (`P_m − α` irreducible over `𝔽_5(α)` at every level).  Heuristically
  `∑_p 2^{−(orbit length)} < ∞`: finitely many exceptional primes.

Landscape: composite floor proved over `𝔽_2`, over `p ≡ 1 (3)`, over all `p` outside a thin
exceptional set with explicit constants; open over `ℤ` and over exceptional `p` (e.g. 5).

### 11.3 Formalisation order

1. `ff_floor_one_mod_three` (one line) + `ffGrowthConstant = 0` there.
2. §9.1 (`ring_nf` in `Polynomial (ZMod 2)`).
3. Level-2 norm criterion (13) for `p ≡ 2 (3)`; general level via a root in `𝔽_{p^{2^{k−1}}}`.
4. Over `ℤ`: define PG, `ρ⁺`, Cev; implications to (C∞), non-implications to MC; primorial
   lower bound if absent.  Paper: variants landscape row "composite floor by ring".

---

## 12. Why prove it, and where the beauty lies (2026-09-02; source for the paper's motivation)

**Why prove it.**  Euclid's argument is the oldest proof in number theory, and it is an
existence proof: given any finite list of primes, their product plus one has a prime factor
outside the list.  Mullin's conjecture asks whether that argument, run literally and greedily
from the empty list, is secretly a construction of every prime.  It is the question of whether
existence and enumeration coincide along the most natural path there is.  Nobody needs the
answer for anything else.  The reason to want it is that it tests whether a specific
deterministic orbit can be proved to behave like a typical one, and that is a wall this
project has mapped from every side.  Collatz, the normality of π, the compositeness of
Sylvester and Fermat numbers all sit behind the same wall.  Mullin's conjecture is the
cleanest representative, because the map is one line, `m ↦ m · lpf(m+1)`, and the target is
one line, convergence to `0` in the profinite ring.  A proof would be the first mechanism
anyone has for the genericity of a single arithmetic orbit.  Even the weakest rung, that
infinitely many Euclid–Mullin primes are `3 (mod 4)`, would be a first of its kind.

**Where the beauty lies, concretely.**

* *The sequence itself.*  `2, 3, 7, 43, 13, 53, 5, 6221671, 38709183810571, 139, 2801, 11,
  17, …`  The primes arrive in an order dictated by the arithmetic of their own products.
  Five comes seventh, eleven twelfth.  Almost every prime is deferred at its natural turn,
  and the conjecture says every deferral is eventually repaired.  The disorder is a
  permutation, or it is not.
* *Minimality is continuity.*  Choosing the least factor is the only rule that descends to
  the profinite ring and is continuous there.  The largest-factor rule does not define a map
  on that space at all, and it provably misses primes.  The conjecture says the natural rule
  is the complete rule.
* *One number, two shadows.*  The cofactor the greedy rule throws away at each step has a
  size, which is the growth defect, and a residue, which is the noise driving the walk.  The
  growth axis and the residue axis are the two projections of a single discarded integer.
* *Exact identities where none were expected.*  The telescope for `log P_n` with the growth
  constant as a complete invariant of perpetual primality.  The coding of the profinite
  basin by admissible enumerations.  The additivity of `P ↦ P² + P` in characteristic 2,
  which settles the composite floor over `𝔽_2` with a sharp constant.  The level constants
  `13, 217, 57073` that decide reducibility over `𝔽_p`.
* *The sign asymmetry.*  Each step yields infinitely many negative facts, that smaller
  primes do not divide, and exactly one positive fact, about a prime captured by
  definition.  The conjecture asks for a positive fact about every prime.  That asymmetry is
  why every unconditional theorem the project owns is an upper bound on hits, and it is
  stated in one sentence.
* *The coastline.*  A hundred and seventy-seven recorded dead ends, thirty of them
  theorems, that together say what one orbit provably inherits from the structure of the
  map and what it does not.  That map exists whether or not the conjecture is ever proved,
  and it is the honest product so far.

What a proof would mean is understanding why `1`, the unique integer unit, is generic for
its own dynamics.  Believing it is easy, by Shanks' heuristic.  Knowing it would require an
idea that does not yet exist anywhere in mathematics, and the project has shown fairly
precisely what shape that idea cannot have.

---

## 13. Is there a ring in which MC is provable? (asked 2026-09-02)

**Trivially, in degenerate rings.**
* Finitely many primes (`ℤ` localised at a finite set `S`): the orbit runs until the Euclid
  number is a unit; MC is a finite computation.  `S = {2,3,7,43}`: true (2, 6, 42, 1806,
  then 1807 is a unit).  `S = {2,3,5}`: false (7 is a unit, 5 never reached).
* Infinitely many units: "least prime factor" is defined only up to a unit and the
  representative changes the next Euclid number — the Pollack–Treviño steering freedom.
  Invert every prime dividing no Sylvester number, keep one prime above each `s_n`,
  normalise its generator to be `s_n` itself: the greedy orbit is the Sylvester tower and MC
  holds by construction.

**Hence the honest setting**: finite unit group + canonical prime normalisation — `ℤ`,
imaginary quadratic orders, `𝔽_q[X]` (monic).  **`ℤ` is the unique ring in which MC is
canonical, tie-free and unit-free**: in every other global field infinitely many primes
split and conjugates share a norm.  (Paper: say this.)

**In honest rings nothing is known, and the structural reason**: provability needs rigidity
(control of the factorisation of `P+1` along the orbit); every known rigidity destroys
completeness — perpetual primality ⟹ autonomous quadratic map ⟹ captured primes of density
0 (Odoni); char-2 additivity ⟹ trace exclusion of odd degrees on autonomous runs; a stable
tower (`p = 5`) makes reducibility unprovable, not provable.  Flexibility enough to capture
everything is flexibility enough to defeat every orbit method (#90).  A ring with both would
need an unrelated reason; none visible.  A provable *disproof* is equally out of reach: the
No-Invariant argument uses only Dirichlet/Kornblum and works in every global field.

**Provable pieces in honest rings**: the composite floor over `𝔽_2[X]`, over `𝔽_p[X]` for
`p ≡ 1 (3)`, and with explicit constants for most other `p` (§11); nothing over `ℤ`.
**Untouched and worth defining**: `ℤ[i]` — `1+i` (residue field `𝔽_2`) captured first;
conjugate ties swapped by complex conjugation (twin of `X ↦ X+1` over `𝔽_2`); the powers of
`1+i` should give two frozen unit classes (`(ℤ[i]/(1+i)^k)^×`) instead of one.

### 13.1 Or provably false?  Yes: `𝔽_5[X]` (2026-09-02)

Seed `X`.  On the autonomous branch `E_n = g_n(X)`, `g_n = Φ₃ ∘ Φ₆^{n−1} = Φ₆^n + 1`.  For
the seed `X` the Capelli seed condition (`X − α` irreducible over `𝔽_p(α)`) is automatic, so
**perpetual irreducibility from seed `X` ⟺ all `g_n` irreducible over `𝔽_p` ⟺ `p ≡ 2 (3)`
and `Φ₆^{k}(−1/4) + 1` is a non-square mod `p` for all `k ≥ 1`** (norm criterion, §11.2).

Over `𝔽_5`: `−1/4 = 1`; orbit `1 → 2 → 1 → 2 → …`; shifted values `3, 2`; squares mod 5 are
`{1, 4}`; `5 ≡ 2 (3)`.  Hence every `g_n` is irreducible over `𝔽_5`, the orbit is
`X, X+1, X²+X+1, X⁴+2X³+2X²+X+1, g₃(X), …` — one irreducible of each degree `2^k` and no
other — no ties ever occur, and every irreducible of degree `∉ {2^k}` (and `X−2`, `X−3`) is
missed.  **`FFMullinConjecture 5` is false** (witness: any monic irreducible cubic, e.g.
`X³+X+1`).  Proof = finite check + Capelli; Lean: `Polynomial.irreducible` of the composite via
a root-degree argument, or directly the norm criterion.

Exceptional primes (stable tower over `−1` under `y²+y`) are `≡ 2 (3)` and rare: 11, 17, 23,
29, 41, 47 all fail within a few levels (17, 23, 29 at level 2 via `(13/p) = 1`; 11 at level
4; 41 at level 4; 47 at level ≈ 8).  Heuristically finitely many; 5 is one.

Consequences: (i) over exceptional `p` the composite floor and MC **fail together** for seed
`X` — the perpetually irreducible Sylvester tower that cannot be excluded over `ℤ` is
realised; (ii) the FF conjecture cannot be stated uniformly in `p`: the honest form excludes
exceptional primes (or seeds on the tower); `AutonomousMap.lean` treats perpetual
irreducibility as a hypothesis — for `p = 5` it is a theorem; the registry open point for
FF-MC needs the hypothesis or a refutation note; (iii) over `ℤ` a disproof would be a proof
of perpetual primality of a Sylvester-type tower — unprovable in both directions by any route
in sight.  Landscape: floor proved + MC open (`𝔽_2`, `p ≡ 1 (3)`, most `p`); floor false +
MC false (`𝔽_5`, exceptional `p`); everything open (`ℤ`).

**Implemented 2026-09-02.**  `EM/FunctionField/StableTower.lean` (Frobenius-orbit proof, no
Capelli, standard axioms only): `StableTower.g_irreducible`, `StableTower.tower : FFEMData 5`,
`tower_euclid_irreducible`, `not_ffMullinConjecture_five`.  Published in the registry; paper
(long: function_field, composite_floor §ff-telescope, appendix, Lean-formalization table,
why_its_hard, variants_landscape, introduction, abstract; short: Sylvester-tower subsection and
closing paragraph) corrected; `Analog.lean` §16 identity and dead end #129 rationale fixed;
`AutonomousMap.lean` / `DegreeTelescope.lean` docstrings updated; `docs/the_story.md` §6.

---

## 14. What the `𝔽_5` refutation teaches, and what it extends to (2026-09-02)

1. **Generic seed; specialization vs reduction.**  Over `𝔽_p[X]` the seed `X` is the generic
   point, so on the autonomous branch the Euclid polynomials *are* the level polynomials
   `g_k = Φ₆^k + 1`.  Over `ℤ[x]` with seed `x` the same holds: the **generic Euclid–Mullin
   sequence is the Sylvester tower**, perpetually irreducible iff the tower is stable over `ℚ`.
   Every `𝔽_p` seed-`X` sequence is its reduction mod `p`; the integer sequence is its
   specialization at `x = 2`.  Three regimes: generic (never leaves the tower); reduction mod
   `p` (leaves at the first level where `g_k` factors mod `p` — Galois-theoretic, Chebotarev
   density `2^{−k}` for leaving at level `k` — or never, for exceptional `p`); specialization at
   `2` (leaves at stage 3 because `g₃(2) = 1807 = 13·139` — arithmetic, about a value).  MC over
   `ℤ` lives entirely in the third regime; (C∞) says the specialization leaves every tower it
   enters.
2. **Corollary over `ℚ` (cheap Lean, ~30 lines, `Monic.irreducible_of_irreducible_map`):**
   every level polynomial `Φ₆^k(y) + 1` is irreducible over `ℤ` and `ℚ` (stable mod 5 ⇒ stable
   over `ℚ`); Galois acts transitively on every level of the tree over `−1`.  Not in the repo
   (`ArborealTower` has the Euclid occupancy argument only).  Sharpens (C∞): perpetual
   primality from stage `N` = `P_N` is a simultaneous prime value of infinitely many irreducible
   polynomials; even Bunyakovsky for `y²+y+1` alone is open.
3. **Seed dependence over `𝔽_5`.**  Linear seeds: all five are affine conjugates of `X`, all
   fail.  Quadratic seeds `X² + c`: the same descent gives `χ_k(α_k − c) = χ_0(g_k(c))`, so the
   tower is perpetual iff the `Φ₆`-orbit of `c` stays in `{1, 2}`: `c ∈ {1, 2}` fail, `c ∈ {3, 4,
   0}` break at stage 0.  Degree ≥ 3: value-set conditions, heuristically break quickly.  So the
   failing seeds are the small structured ones; a.a. seeds should still capture everything.
4. **General exceptional-prime criterion** (moderate Lean: norms or parametrized descent):
   seed-`X` tower over `𝔽_p` perpetual ⟺ `p ≡ 2 (3)` and the shifted critical orbit of `−1/4`
   avoids squares.  Decision procedure per `p`; finiteness of exceptional primes out of reach.
5. **Provability lesson.**  Over `𝔽_p` "every Euclid polynomial irreducible" is a *positive*
   fact provable uniformly in `n` (Frobenius orbits); over `ℤ` primality of `E_n` is decidable
   per `n` (Pocklington) but not provable uniformly.  The sign asymmetry is an integer
   phenomenon.

Next, in order: (2); the parametrized descent for quadratic seeds (3); the `𝔽_2` and
`p ≡ 1 (3)` floors (§11.3).
§14 item 2 **implemented 2026-09-02**: `EM/FunctionField/GenericTower.lean` — `iterR R n` (generic
recursion over any commutative ring), `map_iterR`, `gZ_irreducible` (via
`Monic.irreducible_of_irreducible_map` mod 5), `gQ_irreducible` (Gauss), `gZ_three_eval_two`
(`g₃(2) = 13·139`).  Published in the registry.
§11.3 items 1–3 and §14 item 3 **implemented 2026-09-02**: `EM/FunctionField/CompositeFloors.lean`
(`ffProd_succ_of_irreducible`, `exists_root_phi3`, `euclid_succ_reducible_of_one_mod_three`,
`ffGrowthConstant_eq_zero_of_one_mod_three`, `euclid_three_reducible_of_two`,
`not_four_consecutive_irreducible`, `ffGrowthConstant_eq_zero_of_two`, for every `FFEMData`) and
`EM/FunctionField/QuadraticSeeds.lean` (`quad_invariant`, `two_pow_le_natDegree_minpoly_of_pow`,
`g_comp_irreducible` for `c ∈ {1,2}`, `quad_seed_perpetual`, `quad_seed_sel_natDegree` via the
mixed-walk framework of `FactorTree.lean`).  Not formalized: sharpness of the constant 3 over
`𝔽_2` (irreducibility of `X⁴+X+1`), the general exceptional-prime criterion (§14 item 4).

## 15. Small characteristics in full (implemented 2026-09-02)

* `FrobeniusOrbit.lean` (any `p`): `minimalPeriod_le_natDegree_minpoly`,
  `irreducible_of_natDegree_eq_minimalPeriod`, `pow_p_pow_natDegree_eq_self` (roots of an
  irreducible of degree `d` lie in `𝔽_{p^d}`, via `AdjoinRoot`), `minimalPeriod_aeval_dvd_natDegree`,
  `phi3_root_minimalPeriod` (= 2 for `p ≡ 2 (3)`), `even_natDegree_of_dvd_phi3`.
* `CharTwo.lean`: `X²+X+1`, `X⁴+X+1` irreducible (periods 2, 4); `ff_two_first_terms`
  (`X, X+1, X²+X+1, X⁴+X+1` forced), `euclid_three_factor` (the first tie), `ff_two_attains_three`.
* `CharThree.lean`: `euclid_succ_eq_sq` (`Φ₃(P) = (P−1)²`), constant-1 floor, `ffSeq_dvd_sub_one`,
  `ff_three_first_terms` (`X, X+1, X+2, X³+2X+1, X³+2X+2`; `ffProd 2 = X³ − X`).
* `AutonomousDegrees.lean`: even degree after an irreducible stage (`p ≡ 2 (3)`); over `𝔽_2` after
  two, `4 ∣` degree.
* `LinearSeeds.lean`: `𝔽_5`, every `X + a` perpetual (`minimalPeriod_sub_const`).
Not done: the tie resolution over `𝔽_2` (irreducibility of `X⁴+X³+1`, `Φ₅`; needs `y¹⁵ = 1`),
the general exceptional-prime criterion, the value-set condition for cubic seeds over `𝔽_5`.

## 16. Relevance of the function-field results; whether to deepen (2026-09-02)

**Worth:** (i) housekeeping — the FF conjecture as stated was false, now corrected; (ii) landscape
— the floor is *decided* in FF in both directions (true over 𝔽_2, 𝔽_3, p ≡ 1 (3); false with MC over
𝔽_5), undecided over ℤ; (iii) concept — generic seed / specialization vs reduction: MC lives in the
specialization regime; (iv) **litmus test** — 𝔽_5[X] is a *natural* Euclid–Mullin dynamics with all
residue/walk structure and MC false, so any proof of MC must use what 𝔽_5[X] lacks: compositeness
of Euclid numbers (anatomy, (C∞)-type input).  Purely walk/residue arguments are ruled out.  #90's
witness is now natural, not artificial.  Converse of "any disproof must be anatomical".

**Not worth deepening:** remaining FF items are cosmetic (𝔽_2 tie), known theory
(exceptional-prime criterion = Jones/Ayad–McQuillan; classification = computation), or the same
wall (FF-MC for non-exceptional p is #90 once the tower breaks).  ~1,500 Lean lines bought the
above; the next would buy much less.

**Keep:** (a) a paragraph on the litmus test in `why_its_hard.tex`; (b) 𝔽_p[X] as the
falsification bed for any proposed intermediate hypothesis about the walk (if it would hold over
𝔽_5[X], it cannot suffice over ℤ).  Effort goes to CI(3 mod 4) and the growth axis over ℤ.

## 17. Approaching the compositeness of Euclid numbers (2026-09-02)

**Status of the floor.**  `(C∞) ⟺ C = 0 ⟺` no perpetual Sylvester tower from any Euclid number.
Above it (all proved): `MC ⟹ RD ⟹ (S) ⟹ (C∞)`; new (`EM/Population/ClassInfinitude.lean`):
`CI(2 mod 3) ⟹ (C∞)` and `¬CI(3 mod 4) ⟹ (C∞)` — on the perpetual branch every late multiplier
is a prime Euclid number, hence `≡ 7 (mod 12)` and `≡ 1` mod every bag prime; after a prime
Euclid number every prime factor of the next is `≡ 1 (mod 3)` (integer twin of the FF
even-degree exclusion).  Every Euclid number has a prime factor `≡ 3 (mod 4)` (class-hit fact).
So `CI(2 mod 3)` is at least as hard as `(C∞)`; `CI(3 mod 4)` is the class statement *not*
blocked by the floor (it holds on the branch) — still the weakest open target with a positive
ingredient.

**Why every known route fails, structurally.**
1. *Congruences / coverings.*  On a Sylvester tower the terms are pairwise coprime: each prime
   divides at most one term (in general ≤ π(r) Euclid numbers, `hits_finite`).  A Sierpiński-type
   covering needs periodic residues of the sequence mod fixed primes; here a prime witnesses one
   stage and is then absorbed (`Φ₆(−1) = 0`).  Any proof of (C∞) must exhibit infinitely many
   *distinct* proper prime factors, one per composite.  No finite certificate exists.
2. *Sieve / population.*  "A.a. seeds satisfy (C∞)" (MixedDiversity a.e.) reduces to a
   uniform-in-`N` bound on `#{m ≤ X : E_N(m) prime}`; but for `N` large a.a. seeds have captured
   every prime `≤ log X`, so `E_N(m)` is rough beyond the sieve range reachable with `X` seeds,
   and the increasing union `⋃_N A_N` is dominated by that tail.  Same shape as §G.
   (Dead-end candidate.)
3. *Algebraic factorisation.*  The level polynomials are irreducible over `ℚ` (`GenericTower`);
   the char-2/3 door (`(F+1)³P+1` factors; `Φ₃ = (y−1)²`) is closed over `ℤ` for good.
   Compositeness of `g_k(P_N)` is a statement about a *value*.
4. *Reciprocity.*  Quadratic: identically consistent (repo).  Cubic: `P_{N+k}` is a primitive cube
   root of unity mod `E_{N+k+1}` (order exactly 3) and never a cube there (`E ≢ 1 (mod 9)` since
   `P` is squarefree); cubic reciprocity relates this to cubic characters of the bag primes mod
   `E`, which for inert `r ≡ 2 (3)` are *not* determined by `E ≡ 1 (mod r)`.  Consistency
   conditions, no contradiction.
5. *Analytic / size.*  No tool proves compositeness of one specific integer without a factor.
   Pocklington certifies primality of `E_n` cheaply (`E_n − 1 = P_n` is factored) but says
   nothing about compositeness.
6. *Random-model heuristics.*  `𝔽_5[X]`: Euclid polynomials are "reducible by default" for random
   polynomials, yet the seed-`X` tower is all irreducible.  Composite-by-default proves nothing
   about one tower.  And over `ℚ` the tower is irreducible too, so the only difference between
   `ℤ` and `𝔽_5[X]` is *specialization at `P_N`* — the values.

**Sharpened shape.**  Perpetual primality from `N` ⟺ `P_N` is a simultaneous prime value of the
infinitely many irreducible polynomials `g_k`, `deg g_k = 2^k` ⟺ an infinite chain of primes under
`p ↦ p² − p + 1` seeded at `E_N`.  Even single-polynomial Bunyakovsky (`y²+y+1` prime i.o.) is
open, in the *positive* direction; we need the negative one.  Fermat numbers have identical
status.

**What would move it.**  Only a positive divisibility mechanism producing a proper factor of some
`E_n` — none on file — or a genuinely archimedean/specialization argument (the one resource
`ℤ` has and `𝔽_p[X]` lacks).  Heights/S-units closed (#177).  Verdict: (C∞) is the correct
floor and is Fermat-hard; the productive moves were the ladder refinements above.  Effort now
belongs to CI(3 mod 4), the weakest open statement not blocked by the floor.

## 18. "Sufficiently composed" Euclid numbers (asked 2026-09-02)

* **Rigidity, not richness, for fixed primes.**  Each prime `q` divides at most `π(q)` Euclid
  numbers (`AdelicShadow.hits_finite`), and more than `π(q−1)` hits force selection
  (`captured_of_many_hits`).  So "every prime divides many Euclid numbers" is *false*; richness can
  only come from new primes.  The maximal richness statement for fixed primes is MC′ ("every
  prime divides some `E_n`"), and MC′ ⇐ MC; MC′ ⇒ MC fails only through wasted hits (a hit while
  a smaller missing prime is least), of which there are at most `π(q)`.
* **MC is itself an extremal compositeness statement.**  `lpf(E_n) ≥ q_n` (least missing prime)
  always; capture of the head ⟺ `lpf(E_n) = q_n`.  Hence
  **MC ⟺ the least prime factor of `E_n` attains its trivial lower bound `q_n` infinitely often**
  (⟺ `lpf(E_n) < q′_n`, the second missing prime, i.o.).  The ladder `(C∞) ⇐ (S) ⇐ RD ⇐ MC` is a
  hierarchy of "the least factor is small": `lpf < E_n^{1/2}` i.o.; `lpf < 2^{n−c}` i.o.;
  `∑ 1/lpf = ∞`; `lpf = q_n` i.o.  MC is the top: "as composed as it can possibly be, infinitely
  often".  Nothing weaker than equality with the head suffices (lpf equal to the *second* missing
  prime forever is consistent with everything below MC).
* **Universality hypotheses.**  "Factorization patterns of `E_n` are generic" (Shanks model) does
  imply MC a.s., but that is CME in anatomical clothing (#90).  No anatomical hypothesis short of
  it is known to imply MC, because capture is about *which* prime is least, and class-richness
  (a factor in every class i.o.) does not localise to `q_n ∣ E_n`.
* **The FF calibration.**  Over `𝔽_5[X]` Euclid polynomials are maximally *un*composed
  (irreducible) and MC fails; over `𝔽_2`, `𝔽_3` compositeness is forced (constants 3, 1) yet
  FF-MC is open there — "composite" is not "sufficiently composed"; the latter means "least factor
  = head", i.e. MC.
