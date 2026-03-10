import EM.Group.CRT
import EM.Ensemble.EM

/-!
# Fiber Autonomy: CRT Fiber Determines Multiplier Dynamics

This file formalizes the structural observation that the CRT fiber dynamics
of the Euclid-Mullin sequence is **autonomous**: the multiplier `seq(n+1) mod q`
is determined by the residues of `prod(n)` modulo all primes `r != q`,
not by the walk position `prod(n) mod q` itself.

Consequently, the q-walk position `walkZ q n` is a **readout** of the
fiber trajectory: given the initial walk position and the sequence of
multipliers (each determined by the fiber), the walk is recovered by
the multiplicative telescope.

## Main Results

### Generalized Walk Multi-Step
* `genWalkZ_multi_step` -- genWalkZ(n+K) = genWalkZ(n) * prod of genMultZ

### Single-Step Fiber Determination
* `crt_fiber_determines_genSeq` -- two starting points with same CRT fiber
    at step k produce the same genSeq at step k, provided q does not
    divide either accumulator + 1

### Walk as Fiber Readout
* `walkZ_determined_by_multipliers` -- walkZ at step M is walkZ(0) times
    the product of all multipliers, which is the content of `walkZ_multi_step`
* `genWalkZ_determined_by_multipliers` -- generalized version
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup MullinCRT

/-! ## Generalized Walk Multi-Step

The generalized walk satisfies the same multiplicative telescope as the
standard walk: `genWalkZ n q (M + K) = genWalkZ n q M * prod of genMultZ`.
-/

section GenWalkMultiStep

/-- The generalized walk satisfies a multi-step telescope:
    `genWalkZ n q (M + K) = genWalkZ n q M * ∏_{i<K} genMultZ n q (M+i)`.
    This is the generalized analogue of `MullinCRT.walkZ_multi_step`. -/
theorem genWalkZ_multi_step (n q M K : Nat) :
    genWalkZ n q (M + K) = genWalkZ n q M *
      (Finset.range K).prod (fun i => genMultZ n q (M + i)) := by
  induction K with
  | zero => simp [mul_one]
  | succ K ih =>
    rw [Nat.add_succ, genWalkZ_succ, ih, Finset.prod_range_succ, mul_assoc]

/-- Special case: the walk from step 0 is the initial value times
    the product of all multipliers. -/
theorem genWalkZ_eq_init_mul_prod (n q K : Nat) :
    genWalkZ n q K = genWalkZ n q 0 *
      (Finset.range K).prod (fun i => genMultZ n q i) := by
  have h := genWalkZ_multi_step n q 0 K
  simp only [Nat.zero_add] at h
  exact h

end GenWalkMultiStep

/-! ## Single-Step Fiber Determination

The core CRT invariance theorem (`crt_multiplier_invariance`) says that
if two accumulators P, P' agree modulo every prime r != q, and q divides
neither P+1 nor P'+1, then `minFac(P+1) = minFac(P'+1)`.

We lift this to the generalized EM sequence: two starting points n, n'
with the same CRT fiber at step k produce the same genSeq at step k.
-/

section FiberDetermination

/-- **CRT fiber determines the next prime**: if two generalized accumulators
    `genProd n k` and `genProd n' k` agree modulo every prime `r != q`, and
    `q` is prime and divides neither `genProd n k + 1` nor `genProd n' k + 1`,
    then `genSeq n k = genSeq n' k`.

    This is a direct application of `crt_multiplier_invariance` to the
    generalized accumulators. -/
theorem crt_fiber_determines_genSeq
    {n n' q : Nat}
    (hq_prime : Nat.Prime q)
    (k : Nat)
    (hcrt : ∀ r, Nat.Prime r → r ≠ q →
      genProd n k % r = genProd n' k % r)
    (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (hq_ndvd : ¬ (q ∣ genProd n k + 1))
    (hq_ndvd' : ¬ (q ∣ genProd n' k + 1)) :
    genSeq n k = genSeq n' k := by
  simp only [genSeq_def]
  exact crt_multiplier_invariance
    (by have := genProd_pos hn k; omega)
    (by have := genProd_pos hn' k; omega)
    hq_prime hcrt hq_ndvd hq_ndvd'

/-- **CRT fiber determines the multiplier mod q**: under the same hypotheses
    as `crt_fiber_determines_genSeq`, the multipliers are equal as natural
    numbers, so a fortiori they are equal in ZMod q. -/
theorem crt_fiber_determines_genMultZ
    {n n' q : Nat}
    (hq_prime : Nat.Prime q)
    (k : Nat)
    (hcrt : ∀ r, Nat.Prime r → r ≠ q →
      genProd n k % r = genProd n' k % r)
    (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (hq_ndvd : ¬ (q ∣ genProd n k + 1))
    (hq_ndvd' : ¬ (q ∣ genProd n' k + 1)) :
    genMultZ n q k = genMultZ n' q k := by
  simp only [genMultZ]
  congr 1
  exact crt_fiber_determines_genSeq hq_prime k hcrt hn hn' hq_ndvd hq_ndvd'

end FiberDetermination

/-! ## CRT Fiber Propagation

If two accumulators agree on their CRT fiber (residues mod all primes r != q)
at step k, and the next prime (genSeq) is the same for both (which follows
from CRT invariance), then the CRT fibers at step k+1 are related by the
original fibers: `genProd n (k+1) = genProd n k * genSeq n k`, so
agreement mod r propagates when `genSeq n k = genSeq n' k`.
-/

section FiberPropagation

/-- Helper: if `a % r = b % r` then `(a * c) % r = (b * c) % r`. -/
private theorem mul_mod_of_mod_eq {a b c r : Nat}
    (h : a % r = b % r) : (a * c) % r = (b * c) % r := by
  conv_lhs => rw [Nat.mul_mod]
  conv_rhs => rw [Nat.mul_mod]
  rw [h]

/-- **CRT fiber propagation**: if two accumulators agree mod r at step k,
    and have the same genSeq at step k, then they agree mod r at step k+1.
    This follows from `genProd n (k+1) = genProd n k * genSeq n k`. -/
theorem crt_fiber_propagates
    {n n' : Nat} (k : Nat) (r : Nat)
    (hmod : genProd n k % r = genProd n' k % r)
    (hseq : genSeq n k = genSeq n' k) :
    genProd n (k + 1) % r = genProd n' (k + 1) % r := by
  simp only [genProd_succ, hseq]
  exact mul_mod_of_mod_eq hmod

end FiberPropagation

/-! ## Walk Position as Fiber Readout

The walk position `genWalkZ n q K` is determined by:
1. The initial position `genWalkZ n q 0 = (n : ZMod q)`
2. The multiplier sequence `genMultZ n q 0, ..., genMultZ n q (K-1)`

Each multiplier is fiber-determined (by CRT invariance). Therefore the
walk is a pure readout of the fiber trajectory.

This section records the structural consequence: if two starting points
agree on their CRT fibers at every step (and neither walk hits -1 during
the first K steps), then their walks agree at step K up to the initial
position difference.
-/

section WalkReadout

/-- **Walk readout from multipliers**: if two generalized walks have the same
    multiplier sequence (in ZMod q) for the first K steps, then the walk
    positions at step K differ only by the ratio of initial positions.

    Concretely: `genWalkZ n q K * (genWalkZ n' q 0) = genWalkZ n' q K * (genWalkZ n q 0)`
    provided the multipliers match. -/
theorem walk_readout_from_multipliers
    {n n' q K : Nat}
    (hmult : ∀ i, i < K → genMultZ n q i = genMultZ n' q i) :
    genWalkZ n q K * genWalkZ n' q 0 =
    genWalkZ n' q K * genWalkZ n q 0 := by
  rw [genWalkZ_eq_init_mul_prod n q K, genWalkZ_eq_init_mul_prod n' q K]
  have hprod : (Finset.range K).prod (fun i => genMultZ n q i) =
               (Finset.range K).prod (fun i => genMultZ n' q i) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact hmult i (Finset.mem_range.mp hi)
  ring_nf
  rw [hprod]
  ring

/-- **Walk ratio identity**: when two generalized walks have the same
    multiplier sequence, their walk positions at step K satisfy the same
    ratio to their initial positions:
    `genWalkZ n q K * genWalkZ n' q 0 = genWalkZ n' q K * genWalkZ n q 0`.
    This is `walk_readout_from_multipliers` restated to emphasize the
    "same ratio" interpretation. -/
theorem walk_ratio_invariant
    {n n' q K : Nat}
    (hmult : ∀ i, i < K → genMultZ n q i = genMultZ n' q i) :
    genWalkZ n q K * genWalkZ n' q 0 =
    genWalkZ n' q K * genWalkZ n q 0 :=
  walk_readout_from_multipliers hmult

/-- **Standard walk as multiplier readout**: the standard EM walk satisfies
    `walkZ q K = walkZ q 0 * ∏_{i<K} multZ q i`. This is just
    `walkZ_multi_step` with n = 0, recorded here for cross-reference. -/
theorem walkZ_as_multiplier_readout (q K : Nat) :
    walkZ q K = walkZ q 0 *
      (Finset.range K).prod (fun i => multZ q i) := by
  have h := walkZ_multi_step q 0 K
  simp only [Nat.zero_add] at h
  exact h

end WalkReadout

/-! ## Fiber-Walk Decoupling

The key structural insight: the walk position mod q enters the dynamics
ONLY through the non-divisibility condition `q does not divide P+1`.
When the walk is alive (has not hit -1), the CRT fiber evolves
autonomously and the walk is a passive readout.

This means:
- The fiber trajectory determines the multiplier sequence
- The multiplier sequence determines the walk
- The walk feeds back ONLY through the death condition (hitting -1)
-/

section FiberWalkDecoupling

/-- **Fiber determines walk increment**: when the CRT fiber at step k
    determines the multiplier (via `crt_fiber_determines_genMultZ`),
    the walk increment `genMultZ n q k` at that step is fiber-determined.
    The walk position at step k+1 is then:
    `genWalkZ n q (k+1) = genWalkZ n q k * (fiber-determined multiplier)`.

    This theorem just combines `genWalkZ_succ` with the observation that
    the multiplier on the RHS is fiber-determined (by external CRT argument).
    We record it as the composition of the two facts. -/
theorem fiber_walk_step_decomposition (n q k : Nat) :
    genWalkZ n q (k + 1) = genWalkZ n q k * genMultZ n q k :=
  genWalkZ_succ n q k

/-- **Walk-to-hit bridge for generalized walks**: the walk hits -1 at step k
    iff the CRT fiber is in the "death set" (q divides the accumulator + 1).
    This is `genWalkZ_eq_neg_one_iff` restated for emphasis:
    the death condition is a joint condition on the fiber AND the walk,
    but equivalently just `q | genProd n k + 1`. -/
theorem walk_death_is_fiber_condition (n q k : Nat) :
    genWalkZ n q k = -1 ↔ (q ∣ genProd n k + 1) :=
  genWalkZ_eq_neg_one_iff n q k

end FiberWalkDecoupling

end
