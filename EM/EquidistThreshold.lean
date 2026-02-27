import EM.EquidistBootstrap

/-!
# Threshold Approach and Open Problem Analysis

* `ThresholdHitting B`: DH restricted to q ≥ B
* `concrete_mcBelow_11`: primes < 11 appear in seq
* `threshold_11_implies_mullin`: ThresholdHitting 11 → MC
* Open problem analysis: structure of HH failure
-/

open Mullin Euclid MullinGroup RotorRouter


/-! ## §14. Threshold Approach

We decompose the open hypothesis `DynamicalHitting` into:

1. **ThresholdHitting B**: SE(q) → HH(q) for primes q ≥ B (the analytic component).
2. **FiniteMCBelow B**: MC for primes q < B (the computational component).

Main result: ThresholdHitting B + FiniteMCBelow B + PrimeResidueEscape → MC.
Since PrimeResidueEscape is now proved, this simplifies to
ThresholdHitting B + FiniteMCBelow B → MC.

Concrete verification: MCBelow 11 is proved from seq values 0–6, giving
FiniteMCBelow 11 and the specialization ThresholdHitting 11 → MC. -/

section ThresholdApproach
open Classical

/-- `ThresholdHitting B`: DynamicalHitting restricted to primes q ≥ B.
    For any prime q ≥ B not in the sequence, SubgroupEscape at q implies
    the walk hits -1 mod q cofinally. -/
def ThresholdHitting (B : Nat) : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    B ≤ q →
    (∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H) →
    ∀ N, ∃ n, N ≤ n ∧ q ∣ (prod n + 1)

/-- `FiniteMCBelow B`: all primes below B appear in the Euclid-Mullin sequence.
    This is the computational verification component. -/
def FiniteMCBelow (B : Nat) : Prop :=
  ∀ q, IsPrime q → q < B → ∃ n, seq n = q

/-- DynamicalHitting is equivalent to ThresholdHitting 0. -/
theorem dynamical_hitting_iff_threshold_zero :
    DynamicalHitting ↔ ThresholdHitting 0 := by
  constructor
  · intro hdh q inst hq hne _ hse N; exact hdh q hq hne hse N
  · intro hth q inst hq hne hse N; exact hth q hq hne (Nat.zero_le q) hse N

/-- Weakening: DynamicalHitting implies ThresholdHitting for any B. -/
theorem dynamical_hitting_implies_threshold (hdh : DynamicalHitting) (B : Nat) :
    ThresholdHitting B := by
  intro q inst hq hne _ hse N; exact hdh q hq hne hse N

/-- **Threshold reduction**: ThresholdHitting B + FiniteMCBelow B + PRE → MC.

    Proof by strong induction on q:
    - q < B: FiniteMCBelow gives ∃ n, seq n = q directly.
    - q ≥ B: IH gives MC(< q). Then mcBelow_pre_implies_se derives SE(q)
      from PRE. ThresholdHitting gives HH(q). captures_target finishes. -/
theorem threshold_finite_implies_mullin (B : Nat)
    (hth : ThresholdHitting B) (hfin : FiniteMCBelow B) (hpre : PrimeResidueEscape) :
    MullinConjecture := by
  unfold MullinConjecture
  suffices ∀ k q, q ≤ k → IsPrime q → ∃ n, seq n = q by
    intro q hq; exact this q q (Nat.le_refl q) hq
  intro k
  induction k with
  | zero => intro q hle hq; exact absurd hq.1 (by omega)
  | succ k ih =>
    intro q hle hq
    match Nat.lt_or_ge q (k + 1) with
    | .inl hlt => exact ih q (by omega) hq
    | .inr _ =>
      match Nat.lt_or_ge q B with
      | .inl hlt_B => exact hfin q hq hlt_B
      | .inr hge_B =>
        by_contra hnotexists
        have hne : ∀ m, seq m ≠ q := fun m heq => hnotexists ⟨m, heq⟩
        have hmc : MCBelow q := fun r hr hrq => ih r (by omega) hr.toIsPrime
        haveI : Fact (Nat.Prime q) := ⟨IsPrime.toNatPrime hq⟩
        have hse := mcBelow_pre_implies_se hpre hq hne hmc
        obtain ⟨N, hN⟩ := exists_bound q (fun p hpq hp => ih p (by omega) hp)
        obtain ⟨n, hn_ge, hn_dvd⟩ := hth q hq hne hge_B hse N
        have hall : ∀ p, p < q → IsPrime p → ∃ m, m ≤ n ∧ seq m = p := by
          intro p hpq hp
          obtain ⟨m, hm, hseqm⟩ := hN p hpq hp
          exact ⟨m, by omega, hseqm⟩
        exact hnotexists ⟨n + 1, captures_target hq hn_dvd hall⟩

/-- Concrete: all primes below 11 appear in the EM sequence.
    The primes {2, 3, 5, 7} are seq(0), seq(1), seq(6), seq(2). -/
theorem concrete_mcBelow_11 : MCBelow 11 := by
  intro r hr hrlt
  have h2 := hr.two_le
  interval_cases r
  · exact mullin_for_two         -- r = 2
  · exact mullin_for_three        -- r = 3
  · exact absurd hr (by decide)   -- r = 4
  · exact mullin_for_five         -- r = 5
  · exact absurd hr (by decide)   -- r = 6
  · exact mullin_for_seven        -- r = 7
  · exact absurd hr (by decide)   -- r = 8
  · exact absurd hr (by decide)   -- r = 9
  · exact absurd hr (by decide)   -- r = 10

/-- FiniteMCBelow 11 from the known sequence values. -/
theorem finite_mcBelow_11 : FiniteMCBelow 11 := by
  intro q hq hlt
  exact concrete_mcBelow_11 _ (IsPrime.toNatPrime hq) hlt

/-- **Specialization at B = 11 (with PRE)**: ThresholdHitting 11 + PRE → MC.
    The finite verification uses seq values 0–6. -/
theorem threshold_11_implies_mullin
    (hth : ThresholdHitting 11) (hpre : PrimeResidueEscape) :
    MullinConjecture :=
  threshold_finite_implies_mullin 11 hth finite_mcBelow_11 hpre

/-- **Specialization at B = 11**: ThresholdHitting 11 alone implies MC.
    PrimeResidueEscape is proved elementarily, so the sole remaining
    open hypothesis is the SE-conditioned hitting property for primes ≥ 11. -/
theorem threshold_11_implies_mullin' (hth : ThresholdHitting 11) :
    MullinConjecture :=
  threshold_11_implies_mullin hth prime_residue_escape

end ThresholdApproach

/-! ## Sieve Gap Analysis

The "one prime gap" between sieve level q−1 and level q:
- `mcBelow_implies_seq_ge`: MC(<q) → seq(n+1) ≥ q for large n
- `mcBelow_no_small_factor`: no prime < q divides Prod(n)+1 past roughness bound
- `mcBelow_hit_captures`: q ∣ Prod(n)+1 + all primes < q appeared → seq(n+1) = q
- `mcBelow_cofinal_hit_implies_mc_at`: MC(<q) + cofinal q-hitting → MC(q)
- `mcBelow_dh_implies_mc_at`: MC(<q) + DH(q) → MC(q)

The sole gap between MC(<q) and MC(q) is a cofinal divisibility event
q ∣ Prod(n)+1. DynamicalHitting provides this: SE(q) (free from MC(<q)
via PrimeResidueEscape) implies cofinal hitting. -/

section SieveGap
open Classical

/-- **q-roughness**: MC(<q) implies seq(n+1) ≥ q for all sufficiently large n.
    All primes below q have been consumed into the running product, so none
    can divide Prod(n)+1 past the collection stage. -/
theorem mcBelow_implies_seq_ge {q : Nat} (hmc : MCBelow q) :
    ∃ N, ∀ n, N ≤ n → q ≤ seq (n + 1) := by
  obtain ⟨N, hN⟩ := exists_bound q (fun p hpq hp => hmc p (IsPrime.toNatPrime hp) hpq)
  refine ⟨N, fun n hn => ?_⟩
  rw [seq_succ]
  by_contra hlt
  push_neg at hlt
  have hge2 : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
  have hp := minFac_isPrime (prod n + 1) hge2
  obtain ⟨m, hm, hseqm⟩ := hN (minFac (prod n + 1)) hlt hp
  have hdvd : minFac (prod n + 1) ∣ prod n + 1 := minFac_dvd (prod n + 1) hge2
  rw [← hseqm] at hdvd
  exact seq_not_dvd_prod_succ (by omega : m ≤ n) hdvd

/-- **Roughness at individual primes**: past the collection stage, no prime
    r < q divides Prod(n)+1. This is the sieve remainder vanishing. -/
theorem mcBelow_no_small_factor {q : Nat}
    {N : Nat} (hN : ∀ p, p < q → IsPrime p → ∃ m, m ≤ N ∧ seq m = p)
    {n : Nat} (hn : N ≤ n) {r : Nat} (hr : Nat.Prime r) (hrq : r < q) :
    ¬(r ∣ prod n + 1) := by
  obtain ⟨m, hm, hseqm⟩ := hN r hrq hr.toIsPrime
  intro hdvd
  rw [← hseqm] at hdvd
  exact seq_not_dvd_prod_succ (by omega : m ≤ n) hdvd

/-- **Single-hit capture**: q ∣ Prod(n)+1 with all primes < q already
    in the sequence by stage n gives seq(n+1) = q. -/
theorem mcBelow_hit_captures {q : Nat} (hq : IsPrime q)
    {n : Nat} (hdvd : q ∣ prod n + 1)
    (hlate : ∀ p, Nat.Prime p → p < q → ∃ m, m ≤ n ∧ seq m = p) :
    seq (n + 1) = q :=
  captures_target hq hdvd (fun p hpq hp => hlate p (IsPrime.toNatPrime hp) hpq)

/-- **Lethal hit**: MC(<q) + walkZ(q,n) = -1 past the sieve gap implies seq(n+1) = q.
    Under MC(<q), every hit on -1 past the sieve gap is lethal: q is the smallest
    prime factor of Prod(n)+1, so the minFac selection must pick q. -/
theorem mcBelow_hit_is_lethal {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q)
    {N₀ : Nat} (hN₀ : ∀ p, p < q → IsPrime p → ∃ m, m ≤ N₀ ∧ seq m = p)
    {n : Nat} (hn : N₀ ≤ n) (hwalk : walkZ q n = -1) :
    seq (n + 1) = q := by
  have hdvd := (walkZ_eq_neg_one_iff n).mp hwalk
  exact mcBelow_hit_captures hq hdvd (fun p hp hpq => by
    obtain ⟨m, hm, hseqm⟩ := hN₀ p hpq hp.toIsPrime
    exact ⟨m, by omega, hseqm⟩)

/-- **Walk avoids -1 past sieve gap for a missing prime**: MC(<q) + q missing
    implies walkZ(q,n) ≠ -1 for all n past the sieve gap.
    Immediate from `mcBelow_hit_is_lethal`: any hit would give seq(n+1) = q,
    contradicting q missing. -/
theorem mcBelow_missing_walk_ne_neg_one {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hmc : MCBelow q) (hmiss : ∀ k, seq k ≠ q) :
    ∃ N₀, ∀ n, N₀ ≤ n → walkZ q n ≠ -1 := by
  obtain ⟨N₀, hN₀⟩ := exists_bound q (fun p hpq hp => hmc p (IsPrime.toNatPrime hp) hpq)
  exact ⟨N₀, fun n hn hwalk =>
    hmiss (n + 1) (mcBelow_hit_is_lethal hq hN₀ hn hwalk)⟩

/-- **The one-prime gap theorem**: MC(<q) + cofinal q-hitting → MC(q).
    The sieve at level q−1 is free from MC(<q). Extending by one prime
    requires exactly one cofinal divisibility event q ∣ Prod(n)+1 —
    this is the "sieve gap" that DynamicalHitting bridges. -/
theorem mcBelow_cofinal_hit_implies_mc_at {q : Nat} (hq : IsPrime q)
    (hmc : MCBelow q)
    (hhit : ∀ N, ∃ n, N ≤ n ∧ q ∣ (prod n + 1)) :
    ∃ k, seq k = q := by
  obtain ⟨N, hN⟩ := exists_bound q (fun p hpq hp => hmc p (IsPrime.toNatPrime hp) hpq)
  obtain ⟨n, hn, hdvd⟩ := hhit N
  exact ⟨n + 1, captures_target hq hdvd (fun p hpq hp =>
    let ⟨m, hm, hseqm⟩ := hN p hpq hp; ⟨m, by omega, hseqm⟩)⟩

/-- **Full one-step induction via DH**: MC(<q) + DH at q → MC(q).
    Under MC(<q), SE(q) is free via PrimeResidueEscape. DH converts SE(q)
    to cofinal hitting, and `mcBelow_cofinal_hit_implies_mc_at` finishes. -/
theorem mcBelow_dh_implies_mc_at {q : Nat} (hq : IsPrime q) (hmc : MCBelow q)
    (hdh_q : ∀ [Fact (Nat.Prime q)] (hne : ∀ k, seq k ≠ q),
      (∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
        ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H) →
      ∀ N, ∃ n, N ≤ n ∧ q ∣ (prod n + 1)) :
    ∃ k, seq k = q := by
  by_contra hnotexists
  have hne : ∀ m, seq m ≠ q := fun m heq => hnotexists ⟨m, heq⟩
  haveI : Fact (Nat.Prime q) := ⟨IsPrime.toNatPrime hq⟩
  have hse := mcBelow_pre_implies_se prime_residue_escape hq hne hmc
  exact hnotexists (mcBelow_cofinal_hit_implies_mc_at hq hmc (hdh_q hne hse))

end SieveGap

/-! ## §15. Analysis of the Open Problem

The sole remaining open hypothesis is DynamicalHitting: for primes q not in the
sequence, SE(q) implies HH(q). We reformulate HH failure as **systematic target
avoidance** and characterize the correlation structure required for the EM walk
to avoid hitting -1 forever.

**Key insight.** By `walkZ_hits_iff_target`, the walk hits -1 at step n+1 iff
the walk is at position -(multZ(q,n))⁻¹ at step n. So HH failure means the
walk avoids the "death position" at every step. Since the death position changes
with each multiplier, this requires a systematic correlation between walk
position and multiplier value — a "factoring oracle" effect.

**Quantitative heuristic.** At each step, the death position is one specific
element of (ZMod q)ˣ (which has q-1 elements). A "random" walk would hit
the death position with probability 1/(q-1) at each step, making perpetual
avoidance exponentially unlikely. DH asserts this heuristic is correct for the
EM walk: the greedy factoring process cannot sustain the oracle correlation.

**Character-theoretic view.** Hitting -1 means χ(w(n)) = χ(-1) for ALL
characters χ simultaneously. SE gives that each character walk χ(w(n)) is
non-constant. But synchronizing across all p-1 characters at the same step is
the hard part. In the discrete log formulation, the walk on Z/(q-1)Z with
generating steps must hit the target (q-1)/2 — a single additive congruence. -/

section OpenProblemAnalysis

/-- **Target avoidance ↔ HH failure (threshold version)**: the walk eventually
    never hits -1 iff it eventually avoids the death position -(multZ(q,n))⁻¹
    at every step.

    This reformulates the open problem: DH asserts this avoidance pattern
    cannot persist under SE. The forward direction (→) uses that avoidance at
    step n prevents hitting at step n+1; the reverse (←) uses that failure to
    hit at step n+1 implies the walk was not at the death position at step n. -/
theorem target_avoidance_iff_hh_failure {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) :
    (∃ N, ∀ n, N ≤ n → walkZ q n ≠ -1) ↔
    (∃ N, ∀ n, N ≤ n → walkZ q n ≠ -(multZ q n)⁻¹) := by
  constructor
  · -- → : walk never hits -1 past N, so it avoids the target past N
    rintro ⟨N, hN⟩
    exact ⟨N, fun n hn habs =>
      hN (n + 1) (by omega) ((walkZ_hits_iff_target hq hne n).mpr habs)⟩
  · -- ← : walk avoids target past N, so it never hits -1 past N+1
    rintro ⟨N, hN⟩
    refine ⟨N + 1, fun n hn habs => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact hN m (by omega) ((walkZ_hits_iff_target hq hne m).mp habs)

/-- **Cofinal pair avoids death**: under HH failure, the cofinally-repeating
    (walk, mult) pair from `cofinal_pair_repeat` necessarily avoids the death
    condition. If (w₀, s₀) repeats cofinally, then s₀ ≠ -(w₀)⁻¹.

    This captures the "factoring oracle" obstruction: HH failure requires
    the greedy factoring process to *never* produce the unique death value
    -(w₀)⁻¹ when the walk visits position w₀, even though this pair appears
    cofinally often. For a "random" factoring process, each visit to w₀ would
    independently have probability ~1/(q-1) of producing the death value. -/
theorem cofinal_pair_avoids_death {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {w₀ s₀ : ZMod q}
    (hcof : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = w₀ ∧ multZ q n = s₀)
    (hhf : ∃ N₀, ∀ n, N₀ ≤ n → walkZ q n ≠ -1) :
    s₀ ≠ -(w₀)⁻¹ := by
  obtain ⟨N₀, hN₀⟩ := hhf
  intro heq
  obtain ⟨n, hn, hw, hs⟩ := hcof N₀
  have hdeath : multZ q n = -(walkZ q n)⁻¹ := by rw [hs, hw, heq]
  exact hN₀ (n + 1) (by omega) ((death_value_eq hq hne n).mpr hdeath)

/-- **Successor of cofinal pair is cofinally visited**: if the (walk, mult)
    pair (w₀, s₀) appears cofinally, then the successor position w₀ · s₀
    is also visited cofinally. This gives orbit closure: the set of cofinally
    visited positions is closed under the cofinal transition map x ↦ x · s₀. -/
theorem cofinal_successor_visited {q : Nat}
    {w₀ s₀ : ZMod q}
    (hcof : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = w₀ ∧ multZ q n = s₀) :
    ∀ N, ∃ n, N ≤ n ∧ walkZ q n = w₀ * s₀ := by
  intro N
  obtain ⟨n, hn, hw, hs⟩ := hcof N
  exact ⟨n + 1, by omega, by rw [walkZ_succ, hw, hs]⟩

end OpenProblemAnalysis
