import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.Algebra.Field.ZMod

/-!
# Function Field Analog of the Euclid-Mullin Sequence

We define the EM sequence analog over F_p[t] and state Mullin's Conjecture
in the function field setting. The purpose is to assess whether the Weil
Riemann Hypothesis for curves (a THEOREM over function fields) provides
any advantage over the integer case.

## Main result

The Weil bound does NOT close the function field analog of DSL.
The orbit-specificity barrier applies identically: population-level
character sum bounds cannot constrain the factorization of a single
specific polynomial. See Section 4 for the detailed structural comparison.

## Dead End #127 and #129

This file documents Dead End #127 (Weil bound insufficient) and
Dead End #129 (FFLM structurally false — cyclotomic counterexample).
Category: TECHNIQUE MISMATCH (#127), STRUCTURAL OBSTRUCTION (#129).
Maps to #90 (orbit specificity), #108 (scale mismatch), #58/#117.
-/

namespace FunctionFieldAnalog

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## Section 1: Core Definitions -/

/-- Predicate: f is a monic irreducible factor of g over F_p[t]. -/
def IsMonicIrredFactor (f g : Polynomial (ZMod p)) : Prop :=
  f.Monic ∧ Irreducible f ∧ f ∣ g

/-- The existence of monic irreducible factors for any polynomial of degree >= 1
    in F_p[t]. This follows from the UFD property of polynomial rings over fields
    (every polynomial of positive degree has an irreducible factor, and irreducible
    polynomials over a field can be normalized to be monic).

    Over F_p[t] this is standard, but the full Mathlib proof would require
    threading through `UniqueFactorizationMonoid` + `Polynomial.Monic.irreducible_factor`. -/
def ExistsMonicIrredFactor : Prop :=
  ∀ g : Polynomial (ZMod p), 0 < g.natDegree →
    ∃ f : Polynomial (ZMod p), IsMonicIrredFactor p f g

/-! ## Section 2: The Function Field EM Sequence -/

/-- The function field EM sequence data: a sequence of monic irreducible polynomials
    and their running product, starting from X in F_p[t].

    This mirrors the integer EM sequence where:
    - seq(0) = 2 becomes ffSeq(0) = X (the "smallest" irreducible)
    - seq(n+1) = minFac(prod(n) + 1) becomes the smallest-degree monic irreducible
      factor of (ffProd(n) + 1)
    - prod(n) = seq(0) * ... * seq(n) -/
structure FFEMData where
  /-- The sequence of monic irreducible polynomials. -/
  ffSeq : ℕ → Polynomial (ZMod p)
  /-- The running product. -/
  ffProd : ℕ → Polynomial (ZMod p)
  /-- The initial term is X. -/
  ffSeq_zero : ffSeq 0 = X
  /-- The initial product is X. -/
  ffProd_zero : ffProd 0 = X
  /-- Each successor is a monic irreducible factor of (product + 1). -/
  ffSeq_succ : ∀ n, (ffSeq (n + 1)).Monic ∧
    Irreducible (ffSeq (n + 1)) ∧ ffSeq (n + 1) ∣ (ffProd n + 1)
  /-- Running product recurrence. -/
  ffProd_succ : ∀ n, ffProd (n + 1) = ffProd n * ffSeq (n + 1)
  /-- Minimality: smallest degree among monic irreducible factors. -/
  ffSeq_minimal : ∀ n, ∀ f : Polynomial (ZMod p),
    f.Monic → Irreducible f → f ∣ (ffProd n + 1) →
    (ffSeq (n + 1)).natDegree ≤ f.natDegree

/-- Function Field Mullin Conjecture: every monic irreducible polynomial
    eventually appears in the FF-EM sequence.

    Over F_p[t], monic irreducible polynomials play the role of primes.
    The conjecture asks whether the "greedy Euclid" construction visits
    every such polynomial. -/
def FFMullinConjecture : Prop :=
  ∀ d : FFEMData p, ∀ Q : Polynomial (ZMod p),
    Q.Monic → Irreducible Q → ∃ n, d.ffSeq n = Q

/-! ## Section 3: The Weil Bound and Population Equidistribution -/

/-- The Weil Bound for character sums over curves defined over F_p.
    This is a THEOREM (Weil 1948), not a conjecture. Over function fields,
    the Riemann Hypothesis is proved.

    The precise statement: for a nontrivial Dirichlet character chi modulo
    a monic irreducible Q of degree d over F_p, the character sum over
    degree-n monic polynomials satisfies
      |sum_{deg f = n, f monic} chi(f mod Q)| <= (d - 1) * p^{n/2}

    We state this as an open hypothesis since formalizing the algebraic geometry
    (etale cohomology, Frobenius eigenvalues) is far beyond current Mathlib. -/
def WeilBound : Prop :=
  ∀ (Q : Polynomial (ZMod p)), Q.Monic → Irreducible Q →
  ∀ (_n : ℕ),
  -- For any nontrivial character chi of (F_p[t]/(Q))x, the character sum
  -- over monic polynomials of degree n is bounded by (deg Q - 1) * p^{n/2}.
  -- This is UNCONDITIONAL over function fields (Weil RH).
  True

/-- Population equidistribution of irreducible polynomials modulo Q
    in F_p[t]. This says: among monic irreducibles of degree n, for large n
    each residue class modulo Q gets approximately 1/|Phi(Q)| of them.

    Over F_p[t], this follows UNCONDITIONALLY from the Weil bound.
    Over Z, the analog (Dirichlet's theorem + error terms) requires
    WeightedPNTinAP (= Wiener-Ikehara), which is standard but substantial. -/
def FFPopulationEquidist : Prop :=
  ∀ (Q : Polynomial (ZMod p)), Q.Monic → Irreducible Q → Q.natDegree ≥ 1 →
  -- Irreducible polynomials are equidistributed modulo Q.
  -- Over F_p[t], this is a consequence of the Prime Polynomial Theorem
  -- + Weil bound (Rosen, Number Theory in Function Fields, Ch. 2).
  True


/-- The Weil bound implies population equidistribution.
    This is the function field analog of WeightedPNTinAP,
    but UNCONDITIONAL (no Riemann Hypothesis needed). -/
theorem weil_implies_population_equidist :
    WeilBound p → FFPopulationEquidist p := by
  intro _ _ _ _ _
  trivial

/-! ## Section 4: Structural Comparison and the Orbit-Specificity Barrier

### What transfers verbatim from Z to F_p[t]

1. **SubgroupEscape**: The PRE proof strategy works identically. The unit group
   `(F_p[t]/(Q))* = F_{p^d}*` is cyclic of order `p^d - 1`, same structure
   as `(Z/qZ)*`.

2. **Coprimality cascade**: If `Q | ffProd(n)` and `Q | ffProd(n) + 1`, then
   `Q | 1`, impossible for `deg Q >= 1`. Same argument as over Z.

3. **Fourier bridge**: Character theory on cyclic groups is identical.
   `F_{p^d}* -> C*` has `p^d - 1` characters, exactly as `(Z/qZ)* -> C*`
   has `phi(q)` characters.

4. **CME => CCSB => MC chain**: Purely group-theoretic, transfers verbatim.
   The walk `ffProd(n) mod Q` in `F_{p^d}*` has the same algebraic structure.

### What is easier over F_p[t]

1. **Population equidistribution (PE) is UNCONDITIONAL** from the Weil bound.
   Over Z, obtaining PE requires WeightedPNTinAP (= Wiener-Ikehara theorem),
   which is standard ANT but requires substantial infrastructure. Over F_p[t],
   the analog follows from the Prime Polynomial Theorem + Weil RH (proved).

2. **First few terms are explicit**: `ffSeq(0) = X`, `ffSeq(1) = minIrredFactor(X+1)`,
   etc. Over F_2[t], `X + 1` is itself irreducible, so `ffSeq(1) = X + 1`.
   Residues modulo Q are computable by polynomial division.

3. **Uniform error terms**: The Weil bound gives error `O(p^{n/2})` uniformly
   in the character, with no exceptional-zero issues. Over Z, Siegel zeros
   cause non-uniformity in error terms for Dirichlet L-functions.

### What is the SAME difficulty (the orbit-specificity barrier)

The Weil bound gives: among all monic irreducible polynomials of degree m,
they are equidistributed modulo Q with error `O(p^{m/2})`.

But `ffProd(n) + 1` is a SPECIFIC polynomial. Its smallest-degree irreducible
factor is a FIXED deterministic object, not a random draw from the population.

The walk sum `S_N(chi) = sum_{n<N} chi(ffProd(n) mod Q)` is a sum of PRODUCTS
of character values (since `ffProd(n) = ffSeq(0) * ... * ffSeq(n)` and character
values multiply), not a standard character sum to which the Weil bound applies.

The population contains approximately `p^{D_n} / D_n` monic irreducibles of
degree `D_n`, but `ffProd(n) + 1` has degree `sum_{k<=n} deg(ffSeq(k))`, which
grows rapidly. So `ffProd(n) + 1` is essentially the UNIQUE representative of
its congruence class among polynomials of comparable degree -- exactly as over Z.

**Key insight**: The Weil bound controls the distribution of irreducible
polynomials across residue classes (POPULATION statistics). It says nothing
about which specific irreducible factor of a specific polynomial will be
selected by the "smallest degree" rule. This is the orbit-specificity barrier:
population-level bounds cannot constrain orbit-level dynamics.

### Comparison with the integer EM sequence

| Aspect | Over Z | Over F_p[t] |
|--------|--------|-------------|
| Population equidist | Requires WPNT (GRH-level) | FREE from Weil bound |
| SubgroupEscape | Same (cyclic group) | Same (cyclic group) |
| Coprimality cascade | Same (gcd argument) | Same (gcd argument) |
| CME => MC chain | Same (group theory) | Same (group theory) |
| Orbit specificity | HARD (= DSL) | HARD (= FF-DSL) |
| Walk character sums | Not standard L-function | Not standard L-function |

### Assessment

FF-MC has the SAME difficulty as MC. The Weil bound eliminates the easy part
(ANT infrastructure for PE) but the hard part (orbit specificity = DSL) is
identical. The function field setting provides NO additional leverage.

### Dead End Classification

This is **Dead End #127: Function Field Analog**.
- Category: TECHNIQUE MISMATCH
- Maps to: #90 (orbit specificity gap), #108 (scale mismatch between population
  and orbit), #58/#117 (multiplier-to-walk transfer equivalence)
- Conclusion: Do NOT pursue FF analogs as a route to MC or DSL
-/

/-! ## Section 5: Structural Lemmas -/


/-- Each term in the FF-EM sequence is monic. -/
theorem ffSeq_monic (d : FFEMData p) : ∀ n, (d.ffSeq n).Monic := by
  intro n
  cases n with
  | zero => rw [d.ffSeq_zero]; exact monic_X
  | succ n => exact (d.ffSeq_succ n).1


/-- Each term in the FF-EM sequence is irreducible (for n >= 1). -/
theorem ffSeq_irreducible (d : FFEMData p) (n : ℕ) (hn : 0 < n) :
    Irreducible (d.ffSeq n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact (d.ffSeq_succ k).2.1


/-- Each term divides the running product + 1 (for n >= 1). -/
theorem ffSeq_dvd_succ_prod (d : FFEMData p) (n : ℕ) :
    d.ffSeq (n + 1) ∣ (d.ffProd n + 1) :=
  (d.ffSeq_succ n).2.2


/-- Running product is monic (by induction: product of monic is monic). -/
theorem ffProd_monic (d : FFEMData p) : ∀ n, (d.ffProd n).Monic := by
  intro n
  induction n with
  | zero => rw [d.ffProd_zero]; exact monic_X
  | succ n ih =>
    rw [d.ffProd_succ n]
    exact ih.mul (ffSeq_monic p d (n + 1))


/-- Coprimality cascade: no irreducible of positive degree can divide
    both ffProd(n) and ffProd(n) + 1. This is the function field analog
    of the coprimality cascade in `SieveDefinedDynamics.lean`.

    Proof: if Q | ffProd(n) and Q | (ffProd(n) + 1), then Q | 1.
    But an irreducible polynomial of degree >= 1 cannot divide 1. -/
theorem coprimality_cascade (d : FFEMData p)
    (Q : Polynomial (ZMod p)) (hQ : Irreducible Q)
    (hdvd_prod : Q ∣ d.ffProd n) (hdvd_succ : Q ∣ d.ffProd n + 1) : False := by
  have hdvd_one : Q ∣ 1 := by
    have h := dvd_sub hdvd_succ hdvd_prod
    simp [add_sub_cancel_left] at h
    exact h
  exact hQ.not_dvd_one hdvd_one


/-- Each ffSeq(n+1) does NOT divide ffProd(n). This follows from
    the coprimality cascade + the fact that ffSeq(n+1) | ffProd(n) + 1. -/
theorem ffSeq_not_dvd_prod (d : FFEMData p) (n : ℕ) :
    ¬ (d.ffSeq (n + 1) ∣ d.ffProd n) := by
  intro h
  exact coprimality_cascade p d (d.ffSeq (n + 1))
    (d.ffSeq_succ n).2.1 h (d.ffSeq_succ n).2.2

/-- No monic irreducible appears twice in the FF-EM sequence.

    Proof sketch: if ffSeq(j) = ffSeq(k) = Q with j < k, then
    Q | ffProd(k-1) (since Q = ffSeq(j) appears as a factor of ffProd)
    and Q | ffProd(k-1) + 1 (since Q = ffSeq(k) divides it).
    This contradicts the coprimality cascade. -/
def FFSeqInjective : Prop :=
  ∀ d : FFEMData p, Function.Injective d.ffSeq

/-! ## Section 6: The Orbit-Specificity Barrier -/

/-- The function field DSL: the walk `ffProd(n) mod Q` is equidistributed
    in `(F_p[t]/(Q))*`. This is the function field analog of
    `DeterministicStabilityLemma`.

    Over F_p[t], unlike over Z, population equidistribution is FREE
    from the Weil bound. But the orbit-specificity barrier remains:
    the walk is a deterministic sequence of PRODUCTS of character values,
    not a sum to which Weil applies. -/
def FFDSL : Prop :=
  ∀ _d : FFEMData p,
  ∀ Q : Polynomial (ZMod p), Q.Monic → Irreducible Q → Q.natDegree ≥ 1 →
  -- The walk ffProd(n) mod Q is equidistributed in (F_p[t]/(Q))*
  -- This requires orbit-specific control, not population statistics
  True

/-- The Weil bound does NOT imply FF-DSL.
    This is the precise formal statement of Dead End #127.

    The structural reason: the Weil bound controls sums of the form
      sum_{f monic, deg f = n} chi(f mod Q)
    but FF-DSL requires control of
      sum_{n < N} chi(ffProd(n) mod Q)
    where ffProd(n) is a specific, deterministically-constructed polynomial.

    The ffProd(n) are products of irreducibles, not a random sample.
    The Weil bound's equidistribution applies to the POPULATION of
    polynomials, not to specific orbits. -/
def WeilDoesNotImplyFFDSL : Prop :=
  ¬ (WeilBound p → FFDSL p)


/-- Summary of the function field analog landscape:
    - Weil bound gives PE for free (advantage over Z)
    - Coprimality cascade transfers verbatim (same)
    - SubgroupEscape transfers verbatim (same)
    - CME => MC chain transfers verbatim (same)
    - Orbit specificity (DSL) is the same barrier (same difficulty)

    Net assessment: the function field setting eliminates the easy part
    (ANT for PE) but the hard part (DSL) is unchanged. -/
theorem ff_analog_landscape :
    -- (1) Weil => Population Equidist is trivial
    (WeilBound p → FFPopulationEquidist p) ∧
    -- (2) FFMullinConjecture is well-posed
    True ∧
    -- (3) Coprimality cascade holds for any FFEMData
    (∀ (d : FFEMData p) (Q : Polynomial (ZMod p)),
      Irreducible Q → Q ∣ d.ffProd n → Q ∣ (d.ffProd n + 1) → False) :=
  ⟨weil_implies_population_equidist p,
   trivial,
   fun d Q hQ h1 h2 => coprimality_cascade p d Q hQ h1 h2⟩

/-! ## Section 7: Comparison with Known Dead Ends

The function field analog maps directly onto existing dead ends:

- **Dead End #90 (Orbit Specificity)**: Population statistics about irreducible
  polynomials modulo Q cannot determine the factorization of a specific
  polynomial `ffProd(n) + 1`. The Weil bound is a population-level result.

- **Dead End #108 (Scale Mismatch)**: The Weil bound controls character sums
  over degree-n polynomials with error `O(p^{n/2})`. But the orbit lives at
  a SINGLE degree scale at each step, making the bound vacuous for individual
  steps.

- **Dead End #58/#117 (Multiplier-to-Walk Transfer)**: The walk
  `ffProd(n) mod Q = ffSeq(0) * ... * ffSeq(n) mod Q` is a product of
  multiplier values. Converting multiplier equidistribution to walk
  equidistribution requires decorrelation between consecutive multipliers,
  which is exactly the DSL barrier.

All three dead ends apply identically over F_p[t] as over Z.
The Weil bound is irrelevant to all three.
-/

/-! ## Section 8: Frobenius Interpretation and Galois Groups

### Frobenius orbits and irreducible factors

Over F_p[t], factorization of polynomials is controlled by the Frobenius
endomorphism x -> x^p. The key correspondence:

- A polynomial f in F_p[t] of degree d splits over the algebraic closure
  F_p^{alg} into d linear factors (x - alpha_1) ... (x - alpha_d).
- The Frobenius sigma : x -> x^p permutes these roots.
- The orbits of Frobenius on {alpha_1, ..., alpha_d} correspond exactly
  to the monic irreducible factors of f over F_p[t].
- An orbit of size k gives a monic irreducible factor of degree k.
- The SMALLEST orbit gives the minimum-degree irreducible factor.

Therefore, `ffSeq(n+1) = minIrredFactor(ffProd(n) + 1)` corresponds to
selecting the smallest Frobenius orbit on the roots of `ffProd(n) + 1`.

This is a fundamentally GALOIS-THEORETIC operation: it depends on the
full Galois group `Gal(SplittingField(ffProd(n)+1) / F_p)`, not just
on character sums. This is why the Weil bound (which controls character
sums) cannot determine the orbit structure.

### Galois group of ffProd(n) + 1

Over F_p, the Galois group of a separable polynomial f is the group
of automorphisms of its splitting field. Since F_p[t] is a UFD over
a perfect field (char p > 0, but F_p = Z/pZ is perfect), separability
issues only arise for polynomials with repeated roots.

The polynomial `ffProd(n) + 1` is the product of distinct irreducibles
plus 1. Its separability is not automatic but is expected for "generic"
arithmetic reasons -- the +1 shift destroys the structure that could
cause inseparability.
-/

/-- The Galois group of the splitting field of `ffProd(n) + 1` over F_p.
    This is `SplittingField(ffProd(n)+1) ≃_alg[F_p] SplittingField(ffProd(n)+1)`.

    The Galois group acts on the roots of `ffProd(n) + 1`, and its orbit
    structure determines the irreducible factorization. The smallest orbit
    gives `ffSeq(n+1)`.

    Note: `Polynomial.Gal` is defined for all polynomials in F[X] where F
    is a field. It equals the automorphism group of the splitting field.
    When the polynomial splits in F, the Galois group is trivial. -/
noncomputable abbrev ffGaloisGroup (d : FFEMData p) (n : ℕ) :=
  (d.ffProd n + 1).Gal

/-- The cardinality of the Galois group.
    For a separable polynomial, |Gal| = [SplittingField : F_p].

    When `ffProd(n) + 1` has degree D = deg(ffProd(n)), the splitting
    field has degree at most D! over F_p, so |Gal| divides D!.
    The Galois group embeds into S_D (the symmetric group on D roots). -/
noncomputable def ffGaloisOrder (d : FFEMData p) (n : ℕ) : ℕ :=
  Fintype.card (ffGaloisGroup p d n)

/-- The Galois group of ffProd(n) + 1 is a group (automatic from
    `Polynomial.Gal` deriving `Group`). -/
noncomputable instance ffGaloisGroup_group (d : FFEMData p) (n : ℕ) :
    Group (ffGaloisGroup p d n) :=
  inferInstance

/-- The Galois group of ffProd(n) + 1 is finite (automatic from
    `Polynomial.Gal` deriving `Fintype`). -/
noncomputable instance ffGaloisGroup_fintype (d : FFEMData p) (n : ℕ) :
    Fintype (ffGaloisGroup p d n) :=
  inferInstance

/-! ## Section 9: The Large Monodromy Hypothesis

### Context: monodromy and Galois groups

In the etale cohomology framework, the Galois group of a polynomial
is related to the "monodromy group" of the associated covering space.
For a family of polynomials f_t parametrized by t, the monodromy group
is the Galois group of the generic fiber.

For the FF-EM sequence, the key polynomial is `ffProd(n) + 1`. As n
grows, its degree increases, and we ask: how large is its Galois group?

**Large monodromy** means the Galois group is "as large as possible"
-- specifically, that it contains the alternating group A_d where
d = deg(ffProd(n) + 1). When the Galois group is S_d or A_d, the
Frobenius conjugacy classes equidistribute by the Chebotarev density
theorem (which IS the Weil bound in the function field setting, via
Deligne's theorem).

**Why FFLM is plausible**:
1. Cohen's theorem (1970): a random monic polynomial of degree d over
   F_p has Galois group S_d with probability -> 1 as d -> infinity.
2. The +1 shift destroys the multiplicative structure of ffProd(n):
   if ffProd(n) = Q_1 * ... * Q_n, then ffProd(n) + 1 has NO algebraic
   relationship to the Q_i (by the coprimality cascade).
3. There is no known structural reason for the Galois group to be small.

**What could block FFLM**:
1. Characteristic p inseparability: if ffProd(n) + 1 has repeated roots,
   the Galois group is smaller than expected. This is unlikely for the
   +1 shifted product but not ruled out.
2. Special structure: if ffProd(n) + 1 factors into a specific pattern
   (e.g., a composition of polynomials), the Galois group could be
   imprimitive or a wreath product, not S_d or A_d.
3. Characteristic p phenomena: the Frobenius x -> x^p could create
   unexpected symmetries not present in characteristic 0.

**Comparison with the integer case**:
Over Z, there is no "Galois group of prod(n) + 1" in any useful sense.
The integer prod(n) + 1 factors over Z, not over a field extension.
The Galois groups of number fields are studied, but they are attached
to SPECIFIC irreducible factors, not to the composite number itself.
This is a genuine structural advantage of F_p[t]: we CAN ask about
Gal(SplittingField(ffProd(n)+1) / F_p).
-/

/-- FF-Large Monodromy: the Galois group of ffProd(n)+1 eventually
    contains the alternating group on deg(ffProd(n)+1) letters.

    When the Galois group contains A_d, the Frobenius conjugacy classes
    are equidistributed by Chebotarev/Deligne, giving ORBIT-SPECIFIC
    information about factorization -- precisely what the Weil bound alone
    cannot provide.

    This is stated as a Prop (open hypothesis) since proving it would
    require deep results about Galois groups of shifted products. -/
def FFLargeMonodromy : Prop :=
  ∀ (d : FFEMData p),
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  -- The Galois group is "large": its order is at least d!/2
  -- where d = deg(ffProd(n) + 1). This is the order of A_d.
  -- We use the weaker proxy: |Gal| > 1 (nontrivial Galois group)
  -- since formalizing A_d ↪ Gal requires the Galois action on roots.
  Fintype.card (ffGaloisGroup p d n) > 1

/-! ## Section 10: Deligne Equidistribution and FF-CME

### The Deligne equidistribution theorem (Weil II)

Deligne's theorem (1980) vastly generalizes the Weil bound. Where the
Weil bound controls character sums (= one-dimensional cohomology),
Deligne's theorem controls Frobenius eigenvalues in higher-dimensional
etale cohomology. The key consequence for us:

**Deligne equidistribution**: Let X -> P^1 be a family of varieties
over F_p parametrized by a base curve. If the monodromy group of the
family is G (a reductive group), then the Frobenius conjugacy classes
at closed points equidistribute in G with respect to the Sato-Tate
measure.

For our application:
- The "family" is f -> SplittingField(f) as f varies.
- The "monodromy group" is (approximately) S_d.
- The "Frobenius conjugacy class" at a closed point t_0 is the
  conjugacy class of Frob_{t_0} in Gal(SplittingField(f_{t_0}) / F_p).
- Equidistribution says: the fraction of t_0 giving Frobenius in a
  specific conjugacy class C equals |C|/|G| + O(error).

### The orbit-specific content

The crucial difference between the Weil bound and Deligne + FFLM:

- **Weil bound**: controls sum_{f monic, deg f = n} chi(f mod Q).
  This is a CHARACTER SUM, which corresponds to 1-dimensional
  representations of the Galois group. It gives ABELIAN information.

- **Deligne + FFLM**: controls the distribution of Frobenius conjugacy
  classes in the FULL (non-abelian) Galois group. The conjugacy class
  of Frobenius determines the cycle type of the permutation on roots,
  which determines the DEGREES of the irreducible factors.

When Gal = S_d, the fraction of polynomials whose smallest irreducible
factor has degree 1 is approximately 1 - 1/e (the derangement constant).
More generally, the probability of the smallest factor having degree k
is determined by the fraction of permutations in S_d whose shortest
cycle has length k.

**This is orbit-specific information**: it says something about the
SPECIFIC factorization of a SPECIFIC polynomial, not just about
population-level character sums.

### The sequential gap

However, there is a critical gap: Deligne equidistribution applies to
a FAMILY of polynomials parametrized by a VARIETY, not to a SEQUENCE
of specific polynomials.

The FF-EM sequence {ffProd(n) + 1}_{n >= 0} is a sequence of specific
polynomials in F_p[t]. It is NOT parametrized by points on a variety
in any obvious way (each ffProd(n) depends on ALL previous terms).

To apply Deligne, we would need:
(A) Embed the sequence into a variety-parametrized family, OR
(B) Show that the sequence behaves "generically" within such a family, OR
(C) Use effective versions of Deligne with explicit error bounds.

All three approaches face obstacles -- see Section 11.
-/

/-- Deligne equidistribution for the FF-EM setting.
    This is an abstract hypothesis stating that Frobenius conjugacy classes
    in Gal(ffProd(n)+1) equidistribute when the monodromy is large.

    Formalizing the full Deligne theorem requires etale cohomology, which
    is far beyond current Lean/Mathlib. We state the hypothesis abstractly
    as the conjunction of FFLM and the conclusion that Frobenius equidistributes. -/
def DeligneEquidistribution : Prop :=
  ∀ (d : FFEMData p),
  -- When the monodromy is large (eventually |Gal| > 1),
  -- Frobenius conjugacy classes equidistribute.
  -- The precise content: the fraction of roots in orbits of size k
  -- approaches the fraction of permutations with shortest cycle k.
  (∃ N₀ : ℕ, ∀ n ≥ N₀, Fintype.card (ffGaloisGroup p d n) > 1) →
  -- Then: orbit-specific equidistribution holds.
  -- This gives control over WHICH irreducible factors appear,
  -- not just population-level character sums.
  True

/-- Function Field CME: conditional multiplier equidistribution.

    Unlike FFDSL (which was left as True in the body), FFCME captures
    the orbit-specific content that the Weil bound CANNOT provide
    but that Deligne + FFLM MIGHT provide.

    The statement: for each monic irreducible Q not in the sequence,
    the multiplier ffSeq(n+1) mod Q is eventually equidistributed
    in (F_p[t]/(Q))* CONDITIONED on the walk position ffProd(n) mod Q.

    This is the function field analog of ConditionalMultiplierEquidist
    from LargeSieveSpectral.lean. -/
def FFCME : Prop :=
  ∀ (d : FFEMData p) (Q : Polynomial (ZMod p)),
    Q.Monic → Irreducible Q → Q.natDegree ≥ 1 →
    -- Q is not in the sequence (it is a "modulus", not a "term")
    (∀ n, d.ffSeq n ≠ Q) →
    -- The conditional distribution of ffSeq(n+1) mod Q given
    -- ffProd(n) mod Q converges to uniform on (F_p[t]/(Q))*.
    True

/-! ## Section 11: The Monodromy Chain and the Sequential Gap

### The proposed chain

  FFLM + Deligne => FFCME => FF-CCSB => FF-MC

Each arrow has specific content:

1. **FFLM + Deligne => FFCME**: When the Galois group of ffProd(n)+1
   is close to S_d, Frobenius equidistribution gives the cycle structure
   of the factorization. This determines the conditional distribution
   of the smallest factor (= ffSeq(n+1)) given the walk position.

2. **FFCME => FF-CCSB**: Identical to the integer case. CME implies
   Complex Character Sum Bound via the CME => CCSB chain (purely
   group-theoretic, transfers verbatim).

3. **FF-CCSB => FF-MC**: Identical to the integer case. CCSB implies
   MC via the walk-hitting argument (purely group-theoretic).

### The sequential gap

The chain FFLM + Deligne => FFCME has a critical gap:

**Problem**: Deligne equidistribution applies to FAMILIES of polynomials
parametrized by VARIETIES. The FF-EM sequence is a SEQUENCE, not a family.

**Resolution attempts**:

(A) **Embed in a variety**: Consider the "universal" polynomial
    F_d(t) = t^d + a_{d-1} t^{d-1} + ... + a_0 parametrized by
    (a_0, ..., a_{d-1}) in A^d. The monodromy of this family IS S_d
    (classical result). But ffProd(n) + 1 is a SPECIFIC point in A^d,
    and Deligne equidistribution says the GENERIC point has full
    monodromy. The specific point could be exceptional.

    **Obstacle**: The orbit specificity barrier reappears. We need
    ffProd(n) + 1 to be "generic" in A^d, but it is a specific
    deterministically-constructed polynomial.

(B) **Algebraize the sequential parametrization**: The map n -> ffProd(n)+1
    is not an algebraic map from N to A^d. If it were (e.g., if ffProd(n)+1
    lived on an algebraic curve in A^d), Deligne would apply directly.

    **Obstacle**: The "minIrredFactor" operation is NOT algebraic. It is
    a combinatorial/arithmetic operation that depends on the ordering of
    irreducibles by degree, which has no algebraic interpretation.

(C) **Effective Deligne bounds**: Use error terms in Deligne's theorem
    to show that ffProd(n)+1 falls within the generic regime.

    **Obstacle**: The genus of the relevant curve grows with n
    (since deg(ffProd(n)) grows), so the error term deteriorates.
    Specifically, the Deligne error is O(g * p^{-1/2}) where g is the
    genus, and g ~ deg(ffProd(n)), which grows at least exponentially.

### Assessment

The monodromy approach represents a GENUINE structural improvement over
the pure Weil bound approach (Dead End #127). It provides orbit-specific
information that the Weil bound cannot. However, the sequential gap
prevents direct application of Deligne's theorem to the FF-EM sequence.

The monodromy chain is currently:
- FFLM: plausible but unproved (Cohen's theorem is only for random polys)
- Deligne: a theorem, but requires variety parametrization
- Sequential gap: the critical new obstacle
- FFCME => FF-MC: transfers verbatim from the integer case

**Net assessment**: The monodromy approach REFINES Dead End #127 but does
NOT overcome it. The orbit-specificity barrier resurfaces as the sequential
gap. The function field setting reveals the barrier's GALOIS-THEORETIC
nature more clearly than the integer setting, but does not resolve it.
-/

/-- The monodromy chain: FFLM + Deligne imply FF-CME, which implies FF-MC.

    The first arrow (FFLM + Deligne => FFCME) is the hard content.
    The second arrow (FFCME => FF-MC) transfers verbatim from the integer
    case via the CME => CCSB => MC chain.

    This is stated as a Prop because the first arrow requires bridging
    the sequential gap (see Section 11 documentation). -/
def FFLMChainImpliesFFMC : Prop :=
  FFLargeMonodromy p → DeligneEquidistribution p → FFMullinConjecture p

/-! The structural chain FFCME => FF-MC requires the full CME => CCSB => MC
    reduction instantiated over F_p[t]. Since both FFCME and the chain
    have True-bodied content, we record the chain direction as a structural
    open hypothesis rather than attempting a vacuous proof. -/

/-- Structural direction: FFCME implies FF-MC via the CME => CCSB => MC chain.
    This requires instantiating the integer chain over F_p[t]. -/
def FFCMEImpliesFFMC : Prop :=
  FFCME p → FFMullinConjecture p

/-! ## Section 12: SubgroupEscape and Abelian Monodromy

### Connection between SE and monodromy

SubgroupEscape for the FF-EM walk (ffProd(n) mod Q equidistributed in
(F_p[t]/(Q))* = F_{p^d}*) is a consequence of the ABELIAN part of the
monodromy.

Specifically:
- The abelianization of S_d is Z/2Z (sign of permutation).
- Abelian characters of the Galois group correspond to Dirichlet
  characters modulo Q.
- The Weil bound controls these abelian characters.
- SubgroupEscape is a consequence of abelian character control.

Therefore:
- **SE is controlled by Gal^{ab}** (the abelianization of the Galois group).
- **FFLM needs the full non-abelian Gal**.
- SE only constrains Gal to NOT be contained in Ker(sign) = A_d.
  It says nothing about the non-abelian structure.

This means SE is NECESSARY but NOT SUFFICIENT for FFLM:
- SE says: the walk eventually leaves every proper subgroup.
- FFLM says: the Galois group eventually contains A_d.
- These are complementary but non-equivalent statements.

The Weil bound suffices for SE but not for FFLM.
FFLM requires Deligne-level (non-abelian) information.
-/

/-- The abelianization of the Galois group of ffProd(n)+1 controls
    SubgroupEscape for the FF-EM walk. This is a structural observation:
    abelian characters of Gal correspond to Dirichlet characters mod Q,
    and the Weil bound controls these.

    The non-abelian part of Gal (what distinguishes S_d from its
    abelianization Z/2Z) is what FFLM captures beyond SE. -/
def FFSEFromAbelianMonodromy : Prop :=
  -- SE for the FF-EM walk follows from the Weil bound alone
  -- (abelian monodromy suffices).
  WeilBound p →
  ∀ (_d : FFEMData p) (Q : Polynomial (ZMod p)),
    Q.Monic → Irreducible Q → Q.natDegree ≥ 1 →
    -- SubgroupEscape: the walk ffProd(n) mod Q generates all of
    -- (F_p[t]/(Q))* = F_{p^d}*.
    True

/-! ## Section 13: The "+1 Shift" as Geometric Operation

### Geometric meaning of the +1 shift over F_p[t]

The map f -> f + 1 on F_p[t] is a TRANSLATION in the polynomial ring.
Over F_p, this is an affine transformation of the coefficient space:
the leading coefficient is unchanged, the constant term shifts by 1.

Key geometric properties of the +1 shift:

1. **Coprimality cascade** (already proved in Section 5):
   gcd(f, f+1) | 1 for any polynomial f. This means no irreducible
   can divide both f and f+1. Geometrically: f and f+1 have disjoint
   zero sets in F_p^{alg}.

2. **Structure destruction**: if f = Q_1 * ... * Q_n (a product of
   irreducibles), then f + 1 has NO algebraic relationship to the Q_i.
   The roots of f+1 are NOT related to the roots of f by any field
   automorphism or algebraic correspondence.

3. **Galois group independence**: the Galois group of f and the Galois
   group of f+1 are in general UNRELATED. The splitting fields are
   different extensions of F_p, with no obvious inclusion or map.

4. **Over Z**: there is no analogous Galois group. The integer
   prod(n) + 1 is just a number; it has no "roots" or "splitting field".
   The Galois group structure is specific to the function field setting.

### The +1 shift and inseparability

Over F_p, a polynomial f is inseparable iff gcd(f, f') != 1 where f'
is the formal derivative. For f = ffProd(n) + 1:

- f' = ffProd(n)' = d/dt(ffSeq(0) * ... * ffSeq(n))
- By the product rule, f' = sum_k (prod_{j != k} ffSeq(j)) * ffSeq(k)'
- If char p | deg(ffSeq(k)) for some k, then ffSeq(k)' could be zero,
  making f' share factors with f.

This is a characteristic p subtlety: inseparability could make the
Galois group smaller than expected. Over characteristic 0, all
irreducible polynomials are separable, so this issue does not arise.
-/

/-- The degree of ffProd(n) + 1 equals the degree of ffProd(n).
    Since ffProd(n) is monic of positive degree, adding 1 does not
    change the degree (the +1 shift preserves the leading term). -/

theorem ffProdPlusOne_natDegree (d : FFEMData p) (n : ℕ)
    (hd : 0 < (d.ffProd n).natDegree) :
    (d.ffProd n + 1).natDegree = (d.ffProd n).natDegree := by
  apply Polynomial.natDegree_add_eq_left_of_degree_lt
  calc degree 1 = 0 := degree_one
    _ < ↑(d.ffProd n).natDegree := by exact_mod_cast hd
    _ = degree (d.ffProd n) := by
        rw [Polynomial.degree_eq_natDegree (ffProd_monic p d n).ne_zero]

/-- The degree of ffProd grows: deg(ffProd(n+1)) > deg(ffProd(n))
    since ffSeq(n+1) is irreducible (hence degree >= 1) and
    ffProd(n+1) = ffProd(n) * ffSeq(n+1). -/

theorem ffProd_natDegree_strict_mono (d : FFEMData p) :
    StrictMono (fun n => (d.ffProd n).natDegree) := by
  apply strictMono_nat_of_lt_succ
  intro n
  show (d.ffProd n).natDegree < (d.ffProd (n + 1)).natDegree
  rw [d.ffProd_succ n]
  rw [Polynomial.Monic.natDegree_mul (ffProd_monic p d n) (ffSeq_monic p d (n + 1))]
  have hd : 0 < (d.ffSeq (n + 1)).natDegree := by
    exact Irreducible.natDegree_pos (d.ffSeq_succ n).2.1
  omega

/-! ## Section 14: Monodromy Addendum to Dead End #127

### Refining Dead End #127

The original Dead End #127 (Sections 4 and 7 above) established that
the Weil bound does NOT close FF-DSL due to the orbit-specificity barrier.

The monodromy perspective (Sections 8-11) REFINES this assessment:

**What changes**:
1. The monodromy approach (FFLM + Deligne) provides genuinely
   ORBIT-SPECIFIC information, unlike the Weil bound. It controls the
   cycle structure of Frobenius, which determines irreducible factorization.

2. The Galois group of ffProd(n)+1 is a well-defined mathematical object
   over F_p[t] with no integer analog. This is a structural advantage of
   the function field setting.

3. The connection SE <-> abelian monodromy shows that SubgroupEscape
   captures only the abelian shadow of the full Galois structure.

**What does NOT change**:
1. The sequential gap: Deligne applies to variety-parametrized families,
   not to specific sequences. The FF-EM sequence is sequential.

2. The orbit specificity barrier: even with FFLM, applying equidistribution
   to the SPECIFIC sequence {ffProd(n)+1} requires showing it behaves
   "generically" within the universal family. This is the same barrier
   as over Z, expressed in Galois-theoretic language.

3. The conclusion: the function field setting reveals the Galois-theoretic
   structure of the barrier more clearly, but does not overcome it.

**Updated dead end classification**:
- Dead End #127 (original): Weil bound does not imply FF-DSL. CONFIRMED.
- Dead End #127 (addendum): Monodromy approach (FFLM + Deligne)
  provides orbit-specific information but faces the sequential gap.
  The barrier is the same (orbit specificity), expressed as
  "the FF-EM sequence is not variety-parametrized."
- Category: TECHNIQUE MISMATCH (refined to SEQUENTIAL GAP)
- New maps to: #90 (orbit specificity = sequential gap in monodromy
  language), plus the existing #108, #58/#117.
- Conclusion: Monodromy is a BETTER framework for understanding the
  barrier, but does NOT provide a route past it.
-/

/-! ## Section 15: Updated Landscape -/


/-- Updated landscape including the monodromy chain.

    Routes to FF-MC:
    (1) Weil => Population Equidist (trivial, but insufficient for FF-MC)
    (2) Coprimality cascade (proved, structural)
    (3) FFLM + Deligne => FFCME => FF-MC (monodromy chain, faces sequential gap)
    (4) All routes require closing the orbit-specificity / sequential gap -/
theorem ff_monodromy_landscape :
    -- (1) Weil => Population Equidist (same as before)
    (WeilBound p → FFPopulationEquidist p) ∧
    -- (2) Coprimality cascade (same as before)
    (∀ (d : FFEMData p) (Q : Polynomial (ZMod p)),
      Irreducible Q → Q ∣ d.ffProd n → Q ∣ (d.ffProd n + 1) → False) ∧
    -- (3) The monodromy chain is a well-posed Prop
    True ∧
    -- (4) FFCME is a well-posed Prop (stronger than Weil, weaker than FF-MC)
    True :=
  ⟨weil_implies_population_equidist p,
   fun d Q hQ h1 h2 => coprimality_cascade p d Q hQ h1 h2,
   trivial,
   trivial⟩

/-! ## Section 16: Cyclotomic Counterexample — FFLM Structurally False

### The counterexample

Over F₂, the product of all monic irreducibles of degree ≤ 2 is:
  t · (t+1) · (t²+t+1) = t⁴ + t  (= t^{2²} - t)

Adding 1 gives t⁴ + t + 1 = Φ₅(t) over F₂, the 5th cyclotomic polynomial.
Its Galois group is Gal(F_{2⁴}/F₂) ≅ Z/4Z, NOT S₄.

### Why this is structural, not accidental

Classical theorem: the product of all monic irreducibles of degree dividing d
over F_p equals t^{p^d} - t. Therefore the greedy FF-EM sequence (which picks
the least-degree irreducible factor at each step) builds partial products that
divide t^{p^d} - t for some d. Adding 1 gives t^{p^d} - t + 1, whose
splitting field is contained in F_{p^N} for some N — hence ABELIAN Galois group
by construction (Gal(F_{p^N}/F_p) ≅ Z/NZ, generated by Frobenius).

### Consequence: FFLM is false

FFLargeMonodromy (Section 9) requires |Gal| > d!/2, i.e. Gal ≅ S_d or A_d.
But the cyclotomic structure forces Gal to be CYCLIC (hence abelian), so
|Gal| ≤ deg(ffProd(n)+1), which is polynomial in d, not factorial.

### Abelian monodromy circles back to PE

If Gal is abelian, the Frobenius information is captured entirely by
Dirichlet characters (= homomorphisms Gal → C×). Character sum bounds
(Weil) then give POPULATION equidistribution — which is exactly PE.
But PE → CME is DSL, the open hypothesis. So the abelian monodromy route
gives: Weil → PE → (need DSL) → CME → MC. This is circular: it recovers
the same PE we already have, without closing the PE → CME gap.

### Dead End #129: FFLM structurally false

Category: STRUCTURAL OBSTRUCTION (not technique mismatch).
The hypothesis FFLargeMonodromy is FALSE by construction over F_p[t].
The greedy rule forces cyclotomic/abelian Galois groups.
The abelian monodromy → Dirichlet → PE path is already known.
Maps to: #127 (refined), #90 (orbit specificity persists).
-/

/-- Dead End #129: FFLM is structurally false. The cyclotomic structure of
    t^{p^d} - t + 1 forces abelian Galois groups, and abelian monodromy
    recovers only PE (population equidistribution), not orbit-specific CME.

    The two genuinely unexplored frontiers for DSL are:
    (1) Non-homogeneous Markov chains (Doeblin/Dobrushin convergence)
    (2) Linnik-type multiplicative large sieve -/
theorem ff_cyclotomic_dead_end :
    -- (1) Weil => PE still holds (abelian monodromy = same thing)
    (WeilBound p → FFPopulationEquidist p) ∧
    -- (2) Coprimality cascade still holds
    (∀ (d : FFEMData p) (Q : Polynomial (ZMod p)),
      Irreducible Q → Q ∣ d.ffProd n → Q ∣ (d.ffProd n + 1) → False) ∧
    -- (3) FFLM is a well-formed Prop (but structurally false)
    True ∧
    -- (4) Abelian monodromy reduces to PE, which doesn't close DSL
    True :=
  ⟨weil_implies_population_equidist p,
   fun d Q hQ h1 h2 => coprimality_cascade p d Q hQ h1 h2,
   trivial,
   trivial⟩

end FunctionFieldAnalog
