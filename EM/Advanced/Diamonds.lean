import EM.Transfer.SieveConstraint
import EM.Adelic.Equidist
import EM.Adelic.Profinite

/-!
# p-adic Geometric Perspective on the Euclid-Mullin Walk

## Purpose

This file assesses whether p-adic geometric methods -- perfectoid spaces,
diamonds (in the sense of Scholze), the Fargues-Fontaine curve, and Hecke
orbit equidistribution -- provide leverage for the Deterministic Stability
Lemma (DSL), the sole remaining gap for Mullin's Conjecture.

## Result: Dead End #128

Every known geometric equidistribution theorem (Hecke orbits, Ratner,
Andre-Oort, small points) requires the dynamics to arise from a FIXED
algebraic correspondence or a FIXED group action. The EM walk
w(n+1) = w(n) * m(n) has a STATE-DEPENDENT, NON-ALGEBRAIC, HISTORY-DEPENDENT
multiplier m(n) = seq(n+1) mod q, selected by a global archimedean operation
(minFac). No known geometric framework accommodates this.

## Category

TECHNIQUE MISMATCH. Maps to:
- Dead End #86 (random/ergodic walk category error)
- Dead End #90 (orbit specificity barrier)
- Dead End #95 (spectral gap for deterministic walks)
- Dead End #101 (profinite structure adds nothing new)
- Dead End #127 (function field analog -- Weil bound insufficient)

## Contents

1. p-adic filtration of the EM walk (emPadicVal, stepOpensDirection)
2. The slope sequence (emSlope)
3. Hecke orbit obstruction analysis (documentation only)
4. Placeholder definitions (ScholzeWeinsteinBridge, padicGeometryDeadEnd)
5. Landscape theorem summarizing the structural observations
6. Expert-readable mathematical summary for p-adic geometers
-/

open Mullin Euclid MullinGroup
open Classical

/-! ## Section 2: p-adic filtration of the EM walk -/

section PadicFiltration

/-- The p-adic valuation of prod(n) at prime p. Since prod(n) is squarefree
    (proved in WeakErgodicity.lean), this is 1 if p appears in emSupport n
    (i.e., p is one of seq(0), ..., seq(n)), and 0 otherwise.

    This gives a binary vector v(n) in {0,1}^Primes that grows monotonically:
    at each step, exactly one new coordinate flips from 0 to 1. The EM process
    is thus a walk on the vertices of a (countably infinite) hypercube, adding
    one new dimension at each step. -/
def emPadicVal (p n : Nat) : Nat :=
  if p ∈ emSupport n then 1 else 0

/-- If p is in emSupport n, the p-adic valuation is 1. -/
theorem emPadicVal_eq_one {p n : Nat} (h : p ∈ emSupport n) : emPadicVal p n = 1 := by
  simp [emPadicVal, h]

/-- If p is not in emSupport n, the p-adic valuation is 0. -/
theorem emPadicVal_eq_zero {p n : Nat} (h : p ∉ emSupport n) : emPadicVal p n = 0 := by
  simp [emPadicVal, h]

/-- The p-adic valuation is monotone: once a prime appears, it stays.
    This follows from emSupport_mono: emSupport n ⊆ emSupport (n + 1). -/
theorem emPadicVal_mono (p n : Nat) : emPadicVal p n ≤ emPadicVal p (n + 1) := by
  unfold emPadicVal
  split_ifs with h1 h2 h2
  · exact le_refl _
  · exact absurd (emSupport_mono (Nat.le_succ n) h1) h2
  · exact Nat.zero_le _
  · exact le_refl _

/-- The "new direction" opened at step n: the prime seq(n+1), which is NOT
    in the current support. In the hypercube picture, this is the new
    coordinate axis along which the walk extends. -/
def stepOpensDirection (n : Nat) : Nat := Mullin.seq (n + 1)

/-- The new direction is genuinely new: seq(n+1) is not among
    seq(0), ..., seq(n). This is the fundamental novelty property of the
    EM construction. -/
theorem step_opens_new (n : Nat) : stepOpensDirection n ∉ emSupport n :=
  seq_succ_not_mem_emSupport n

/-- The new direction is prime. -/
theorem step_opens_prime (n : Nat) : (stepOpensDirection n).Prime :=
  seq_natPrime (n + 1)

end PadicFiltration

/-! ## Section 3: The slope sequence -/

noncomputable section SlopeSequence

/-- The "slope" at step n: log(seq(n+1)). In the Harder-Narasimhan filtration
    analogy, this would be the slope of the new factor added at each step.
    The greedy rule (minFac) selects the smallest available slope, i.e., the
    smallest prime factor of prod(n) + 1.

    The slope sequence is positive because every EM prime is at least 2. -/
noncomputable def emSlope (n : Nat) : Real := Real.log (Mullin.seq (n + 1))

/-- Every EM prime is at least 2 (being Nat.Prime). -/
private theorem seq_succ_ge_two (n : Nat) : 2 ≤ Mullin.seq (n + 1) :=
  (seq_natPrime (n + 1)).two_le

/-- The slope sequence is strictly positive. Since seq(n+1) is prime, it is
    at least 2, so log(seq(n+1)) > log(1) = 0. -/
theorem emSlope_pos (n : Nat) : 0 < emSlope n := by
  unfold emSlope
  apply Real.log_pos
  have h := seq_succ_ge_two n
  exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 1 < 2) h

end SlopeSequence

/-! ## Section 4: Hecke orbit obstruction analysis

This section contains NO Lean proofs -- only a detailed mathematical analysis
of why p-adic geometric equidistribution theorems do not apply to the EM walk.

### 4.1 The Hecke orbit analogy and its failure

The EM walk w(n+1) = w(n) * m(n) in (Z/qZ)* superficially resembles a
Hecke orbit {T_p^k(x) : k >= 0} on a Shimura variety. In both cases:
- The ambient space has a rich arithmetic structure.
- The orbit is generated by iterated multiplication/correspondence.

However, the analogy fails at a fundamental level:
- **Hecke**: The correspondence T_p is FIXED (depends only on the prime p).
  The Cesaro average (1/N) * sum_{k=0}^{N-1} T_p^k is analyzed through the
  spectral decomposition of the single operator T_p. Clozel-Ullmo (2005)
  proved equidistribution of Hecke orbits on Shimura varieties using this
  spectral theory.
- **EM**: The multiplier m(n) = seq(n+1) mod q VARIES with each step.
  The Cesaro average (1/N) * sum_{n=0}^{N-1} f(w(n)) involves the
  product w(N) = w(0) * m(0) * m(1) * ... * m(N-1) of DIFFERENT group
  elements. There is no single operator whose spectral theory controls
  the average.

### 4.2 Why stationarity is essential for spectral methods

The Clozel-Ullmo equidistribution theorem for Hecke orbits proceeds:
1. Decompose L^2 into T_p-eigenspaces.
2. Show the Cesaro average (1/N) sum T_p^k f converges to the
   projection onto the T_p-invariant subspace.
3. The T_p-invariant subspace is one-dimensional (= constants) by
   automorphicity + strong approximation.

If T_p varied with step k, say we had T_{p_k}, then step 2 fails:
the average (1/N) sum T_{p_0} ... T_{p_{k-1}} f is a product of
DIFFERENT operators, and no spectral decomposition controls products
of non-commuting (or even commuting but different) operators without
additional independence or mixing hypotheses. Those hypotheses are
precisely DSL.

### 4.3 Ratner's theorem requirements

Ratner's theorem on orbit closures of unipotent flows requires:
(a) A Lie group G with a lattice Gamma.
(b) A FIXED one-parameter unipotent subgroup U < G.
(c) The orbit U*x is studied in G/Gamma.

The EM walk fails all three requirements:
(a) (Z/qZ)* is finite abelian, not a Lie group.
(b) The multiplier varies at each step.
(c) There is no unipotent structure (finite abelian groups have no
    unipotent elements other than the identity).

### 4.4 The Fargues-Fontaine curve

The Fargues-Fontaine curve X_E is a scheme over Q_p associated to a
perfectoid field E. Its key role is in p-adic Hodge theory: classifying
p-adic Galois representations via vector bundles on X_E. The "slope"
of a vector bundle V on X_E is defined through the Newton polygon of
the associated phi-module.

The tempting analogy is:
- The EM accumulator prod(n), viewed as a "vector bundle" with prime
  factorization giving the "HN filtration".
- The "slopes" are log(seq(i)), ordered by the greedy selection rule.

This analogy is a CATEGORY ERROR:
- FF slopes come from Newton polygons of phi-modules (Frobenius
  semilinear algebra). They are about a SINGLE prime p.
- EM "slopes" come from the global archimedean ordering of primes.
  They involve ALL primes simultaneously.
- The FF curve is a geometric object for p-adic Hodge theory.
  The EM walk lives in the adelic group prod_p (Z/pZ)*, which is
  a profinite group, not a curve.

### 4.5 Complete list of geometric equidistribution theorems

| Theorem | Dynamics | Why it fails for EM |
|---------|----------|---------------------|
| Hecke orbit (Clozel-Ullmo 2005) | FIXED correspondence T_p | EM multiplier varies |
| Ratner (1991) | FIXED unipotent U < G | No Lie group, no unipotent |
| Andre-Oort (Tsimerman 2018) | None (CM point distribution) | No dynamics at all |
| Small points (SUZ 1997) | None (height minimization) | No heights involved |
| Duke (1988) | Modular forms + Heegner pts | No modular structure |
| Eskin-Mozes-Shah (1996) | FIXED semisimple subgroup | No Lie group |

### 4.6 The precise obstruction

Every known geometric equidistribution theorem requires the dynamics to
arise from a FIXED algebraic correspondence or FIXED group action. The
EM walk has a state-dependent, non-algebraic, history-dependent multiplier:

  m(n) = minFac(prod(n) + 1)   [archimedean operation]
  w(n+1) = w(n) * m(n)         [multiplicative update in (Z/qZ)*]

The minFac operation is fundamentally archimedean (it compares sizes of
prime factors), while p-adic geometry is non-archimedean. There is no
known bridge between these two worlds that could make the EM multiplier
sequence amenable to geometric methods.
-/

/-! ## Section 5: Placeholder definitions -/

section Placeholders

/-- Placeholder: the question of whether a Scholze-Weinstein type bridge
    (connecting p-adic geometry to EM dynamics) exists is a RESEARCH QUESTION,
    not a hypothesis. We use `True` since the question itself has not been
    resolved. See Section 4 for why the answer is likely negative:
    the EM multiplier is state-dependent and archimedean, while all known
    geometric equidistribution theorems require fixed algebraic dynamics. -/
def ScholzeWeinsteinBridge : Prop := True

/-- The p-adic geometry direction is Dead End #128.
    See the module documentation for the complete obstruction analysis.
    The core issue: geometric equidistribution requires FIXED algebraic
    correspondences; the EM walk has state-dependent non-algebraic multipliers. -/
def padicGeometryDeadEnd : Prop := True

end Placeholders

/-! ## Section 6: Expert-readable mathematical summary

The following summary is written for a p-adic geometer who may not be
familiar with the Euclid-Mullin sequence or its Lean formalization.

### The Euclid-Mullin sequence

Define:
  - seq(0) = 2
  - prod(n) = seq(0) * seq(1) * ... * seq(n)
  - seq(n+1) = the smallest prime factor of prod(n) + 1

The first few terms are 2, 3, 7, 43, 13, 53, 5, 6221671, ...

**Mullin's Conjecture (MC)**: Every prime eventually appears in seq.

### The DSL reduction

MC has been reduced (in this formalization, with full proof) to the
**Deterministic Stability Lemma (DSL)**: for each prime q, the walk

  w(n) = prod(n) mod q   in (Z/qZ)*

visits the element -1 infinitely often. (Since w(n) = -1 iff q | prod(n)+1.)

### The walk structure

The walk w(n) is multiplicative: w(n+1) = w(n) * m(n) where
m(n) = seq(n+1) mod q. This is a random-looking walk on the finite
abelian group (Z/qZ)*, but the multiplier m(n) is DETERMINISTIC and
depends on the entire history of the walk up to step n.

### The precise question for the p-adic geometer

Does the walk {w(n)} on (Z/qZ)* (or, more precisely, the adelic walk on
the profinite group Z-hat* = prod_p (Z/pZ)*) admit a description in terms
of moduli-theoretic data? Specifically:

(a) Is there a perfectoid space or diamond X such that the EM walk
    corresponds to a sequence of points on X?
(b) Is there a Hecke-type correspondence on X whose orbit is the EM walk?
(c) Does the Fargues-Fontaine curve provide any invariant that
    distinguishes the EM walk from a generic multiplicative walk?

### The obstacles

(a) **minFac is archimedean**: The selection rule minFac(prod(n)+1) compares
    sizes of prime factors using the archimedean absolute value on Z. This
    is fundamentally incompatible with p-adic geometry, which sees the world
    through the p-adic absolute value. There is no known non-archimedean
    analog of "smallest prime factor."

(b) **Multiplier is state-dependent**: In a Hecke orbit {T_p^k(x)}, the
    operator T_p is fixed. In the EM walk, the multiplier m(n) depends on
    prod(n), which depends on the entire orbit up to step n. This makes the
    walk non-Markov in any geometric sense.

(c) **No algebraic avatar**: For Hecke orbits on Shimura varieties, the
    orbit has a moduli interpretation (isogeny classes of abelian varieties).
    The EM walk on (Z/qZ)* has no known moduli interpretation. The group
    (Z/qZ)* is just the automorphism group of the scheme Z/qZ; there is no
    deeper geometric structure.

(d) **Population != orbit**: Even if one could define an "EM Shimura variety"
    whose points parametrize shifted squarefree integers (the population),
    equidistribution of a GENERIC point in this space would not imply
    equidistribution of the SPECIFIC orbit starting from n=2. This is the
    orbit-specificity barrier (Dead End #90), which applies regardless of
    the geometric framework.

### Assessment

The p-adic geometric perspective is likely NEGATIVE for structural reasons:
the EM walk is archimedean in its selection rule, state-dependent in its
dynamics, and lacking in algebraic structure. However, expert consultation
from a p-adic geometer is welcomed, particularly on whether there exist
geometric equidistribution theorems that do NOT require fixed algebraic
correspondences.
-/

/-! ## Section 7: Landscape theorem -/

/-- Summary: the p-adic perspective provides structural observations but no
    new mathematical leverage for DSL. The structural observations are:
    (1) the p-adic filtration is well-defined and monotone,
    (2) each step opens a genuinely new direction,
    (3) the slope sequence is positive,
    and (4) the Scholze-Weinstein bridge question is stated (as True). -/
theorem diamonds_perspective_landscape :
    -- The p-adic valuation is monotone
    (∀ p n, emPadicVal p n ≤ emPadicVal p (n + 1)) ∧
    -- New directions are genuinely new
    (∀ n, stepOpensDirection n ∉ emSupport n) ∧
    -- The slope sequence is positive
    (∀ n, 0 < emSlope n) ∧
    -- The research question is (vacuously) stated
    ScholzeWeinsteinBridge :=
  ⟨emPadicVal_mono, step_opens_new, emSlope_pos, trivial⟩
