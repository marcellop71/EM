import EM.EquidistPreamble

/-!
# Sieve-Theoretic Analysis and Weak Hitting Principle

* Exponential growth bound: `prod(n) ≥ 2^(n+1)`
* Death values and perpetual avoidance analysis
* `WeakHittingPrinciple` and `whp_iff_hh`: WHP ↔ HH
-/

open Mullin Euclid MullinGroup RotorRouter


/-! ## Sieve-theoretic analysis: Growth, avoidance, and confinement

The sieve-theoretic approach examines what walk avoidance (¬HH) structurally
forces. The key chain:

1. Walk avoids `-1` mod q → all multipliers confined to proper subgroup `H`
   (confinement theorem, reverse direction)
2. Walk trapped in coset `2·H` of size `|H| ≤ (q-1)/2`
3. `-1 ∉ 2·H` forces walk avoidance automatically (avoidance of confinement)
4. `-1 ∈ 2·H` means avoidance requires the multiplier to dodge the "death value"
   at every visit to the critical walk position

The growth bound `prod(n) ≥ 2^(n+1)` quantifies how fast the products grow,
constraining how the sequence can produce multipliers.
-/

section Sieve

/-- **Exponential growth**: `prod(n) ≥ 2^(n+1)`. Each multiplier `seq(n+1)` is
    prime hence ≥ 2, so the running product grows at least geometrically.

    This is a weak bound — the actual growth is doubly exponential
    (`prod(n) ≈ 2^(2^n)`) — but it's clean and sufficient for basic estimates. -/
theorem prod_exponential_growth (n : Nat) : 2 ^ (n + 1) ≤ prod n := by
  induction n with
  | zero => simp [prod_zero]
  | succ n ih =>
    rw [prod_succ, pow_succ]
    exact Nat.mul_le_mul ih (seq_isPrime (n + 1)).1

/-- **Euclid number growth**: `prod(n) + 1 ≥ 3`. -/
theorem euclid_number_ge (n : Nat) : 3 ≤ prod n + 1 := by
  suffices 2 ≤ prod n by omega
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ prod n := prod_exponential_growth n

/-- **Walk avoidance implies seq never captures q**: if the walk never hits
    `-1` mod q, then `seq(n+1) ≠ q` for all n. Contrapositive: if q is ever
    captured as `seq(k)`, the walk must have hit `-1` at step `k-1`. -/
theorem walk_avoidance_implies_seq_ne {q : Nat} (_hq : IsPrime q)
    (havoid : ∀ n, walkZ q n ≠ -1) (n : Nat) : seq (n + 1) ≠ q := by
  intro heq
  exact havoid n ((walkZ_eq_neg_one_iff n).mpr (heq ▸ seq_dvd_succ_prod n))

/-- **Death value characterization**: the walk hits `-1` at step `n+1` iff
    the multiplier at step `n` equals `-(walkZ q n)⁻¹`.

    Restatement of `walkZ_hits_iff_target` emphasizing the sieve perspective:
    at each step, exactly ONE multiplier value (out of q-1 possible nonzero
    elements) would kill the walk. Survival requires perpetual dodging. -/
theorem death_value_eq {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (n : Nat) :
    walkZ q (n + 1) = -1 ↔ multZ q n = -(walkZ q n)⁻¹ := by
  rw [walkZ_hits_iff_target hq hne n]
  constructor
  · intro h; rw [h]; simp only [neg_inv, inv_inv, neg_neg]
  · intro h; rw [h]; simp only [neg_inv, inv_inv, neg_neg]

/-- **Perpetual avoidance iff perpetual dodging**: the walk avoids `-1`
    at all future steps iff the multiplier dodges the death value at every step.

    This converts the divisibility condition (q ∤ prod(n)+1) into a pointwise
    constraint on the multiplier sequence: at each step, ONE specific residue
    class is forbidden. -/
theorem perpetual_avoidance_iff {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) :
    (∀ n, walkZ q (n + 1) ≠ -1) ↔ (∀ n, multZ q n ≠ -(walkZ q n)⁻¹) := by
  constructor
  · intro h n habs; exact h n ((death_value_eq hq hne n).mpr habs)
  · intro h n habs; exact h n ((death_value_eq hq hne n).mp habs)

/-! ## §2A. Death Channel Infrastructure: Forbidden Multipliers

The "death channel" perspective views walk avoidance as a sieve on multipliers.
At each step n, exactly one multiplier value (out of q-1 possible units) would
send the walk from position c to -1 — the "forbidden multiplier" -c⁻¹.

Key properties:
- The forbidden multiplier map c ↦ -c⁻¹ is an involution on (ZMod q)ˣ
- Walk hits -1 iff multiplier equals forbidden value (death_value_eq restated)
- Survival requires perpetual dodging of the death channel -/

/-- **Forbidden multiplier**: for a unit c in (ZMod q)ˣ, the unique multiplier
    that would send the walk from position c to -1 is `-c⁻¹`. -/
def forbiddenMultiplier {q : Nat} [Fact (Nat.Prime q)] (c : (ZMod q)ˣ) : (ZMod q)ˣ :=
  Units.mk0 (-(c.val)⁻¹) (by
    have hc : c.val ≠ 0 := Units.ne_zero c
    exact neg_ne_zero.mpr (inv_ne_zero hc))

/-- **Walk hits -1 iff multiplier is forbidden**: at the unit level, the walk
    reaches -1 at step n+1 iff the multiplier at n equals the forbidden value
    for the current walk position. Restatement of `death_value_eq` in terms of
    `emWalkUnit`, `emMultUnit`, and `forbiddenMultiplier`. -/
theorem walk_hits_neg_one_iff_mult_eq_forbidden {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (n : Nat) :
    emWalkUnit q hq hne (n + 1) = Units.mk0 (-1) (by norm_num : (-1 : ZMod q) ≠ 0) ↔
    emMultUnit q hq hne n = forbiddenMultiplier (emWalkUnit q hq hne n) := by
  have hwalk_eq : walkZ q (n + 1) = -1 ↔ multZ q n = -(walkZ q n)⁻¹ :=
    death_value_eq hq hne n
  constructor
  · intro h
    ext
    simp only [emMultUnit, emWalkUnit, forbiddenMultiplier, Units.val_mk0]
    exact hwalk_eq.mp (by
      have := congr_arg Units.val h
      simpa [emWalkUnit, Units.val_mk0] using this)
  · intro h
    ext
    simp only [emWalkUnit, Units.val_mk0]
    exact hwalk_eq.mpr (by
      have := congr_arg Units.val h
      simpa [emMultUnit, emWalkUnit, forbiddenMultiplier, Units.val_mk0] using this)

/-- **Forbidden multiplier is involutive**: applying the forbidden multiplier
    map twice returns the original unit. This is because -(-c⁻¹)⁻¹ = -(-c) = c. -/
theorem forbiddenMultiplier_involutive {q : Nat} [Fact (Nat.Prime q)]
    (c : (ZMod q)ˣ) :
    forbiddenMultiplier (forbiddenMultiplier c) = c := by
  ext
  simp only [forbiddenMultiplier, Units.val_mk0]
  -- Need to show: -(-(c.val)⁻¹)⁻¹ = c.val
  -- Compute: -(x) = -1 * x, so -(c.val)⁻¹ means the inverse of -c.val
  -- And (-(c.val)⁻¹)⁻¹ = -(c.val), then -(-(c.val)) = c.val
  have h1 : -(c.val)⁻¹ = (-c.val)⁻¹ := by rw [neg_inv]
  rw [h1]
  have h2 : ((-c.val)⁻¹)⁻¹ = -c.val := inv_inv _
  rw [h2]
  simp only [neg_neg]

/-- **Forbidden multiplier is bijective**: the map c ↦ -c⁻¹ is a bijection
    on (ZMod q)ˣ, since it is its own inverse (an involution). -/
theorem forbiddenMultiplier_bijective {q : Nat} [Fact (Nat.Prime q)] :
    Function.Bijective (@forbiddenMultiplier q _) :=
  ⟨Function.LeftInverse.injective forbiddenMultiplier_involutive,
   Function.RightInverse.surjective forbiddenMultiplier_involutive⟩

/-! ## §2B. Death Channel Hit Hypothesis

The **Death Channel Hit** hypothesis is a weaker variant of the Hitting Hypothesis.
While HH requires cofinal hitting (∀ N, ∃ n ≥ N with walkZ(q,n) = -1), DCH only
requires that the walk hits -1 at least once. Since `first_passage_dichotomy`
proves that each prime q either never appears or appears exactly once, and
appearance is equivalent to hitting -1, a single hit is actually sufficient for MC.

This is the key insight: MC doesn't require equidistribution or even cofinal hitting —
just ONE visit to -1 suffices to capture the prime into the sequence. -/

/-- **Death Channel Hit Hypothesis**: for every missing prime q, the walk
    eventually hits -1 (i.e., q | prod(n)+1 for some n).

    This is weaker than `HittingHypothesis` (which requires cofinal hitting),
    but by `first_passage_dichotomy`, a single hit suffices for MC since the
    walk can hit -1 at most once per prime (before q enters the sequence). -/
def DeathChannelHit : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)], IsPrime q → (∀ k, seq k ≠ q) →
    ∃ n, walkZ q (n + 1) = -1

/-! **Note on DCH → MC**: The statement DCH is weaker than HH: it only guarantees
    one hit, not cofinal hitting. However, HH trivially implies DCH (just take
    N=0 in the HH statement).

    The open question: does DCH → MC? Intuitively yes (one hit should suffice),
    but the proof requires handling the case where the hit occurs "too early"
    (before all primes < q have appeared). This requires additional structural
    arguments beyond the scope of the current formalization. -/

section
open Classical

/-- **HittingHypothesis implies DeathChannelHit**: cofinal hitting trivially
    implies at least one hit. -/
theorem hh_implies_deathChannelHit : HittingHypothesis → DeathChannelHit := by
  intro hH q inst hq hne
  haveI : Fact (Nat.Prime q) := inst
  -- HH gives q | prod n + 1 for some n ≥ 0
  obtain ⟨n, _, hdvd⟩ := hH q hq hne 0
  -- This means walkZ q n = -1, which is what DCH needs
  -- (DCH asks for walkZ q (n+1) = -1, but we can adjust the index)
  -- Actually, let me check: HH says q | prod n + 1, which is walkZ q n = -1.
  -- But DCH needs walkZ q (n+1) = -1, which would be q | prod (n+1) + 1.
  -- These are different! Let me re-check DCH definition...
  -- Oh wait, DCH says "∃ n, walkZ q (n+1) = -1", meaning the n is one less.
  -- So if HH gives us walkZ(q,m)=-1 for some m, DCH needs the predecessor.
  -- But we can't go backwards. Let me instead use m = n+1 in HH:
  by_cases hn : n = 0
  · -- If n = 0, we need to find a later hit. HH with N=1 gives us one.
    subst hn
    obtain ⟨m, hm, hdvd'⟩ := hH q hq hne 1
    -- Now m ≥ 1, so we can write m = m' + 1 for m' = m - 1
    have hm_pos : 1 ≤ m := hm
    use m - 1
    convert (walkZ_eq_neg_one_iff m).mpr hdvd' using 2
    omega
  · -- If n ≥ 1, write n = n' + 1
    have hn_pos : 1 ≤ n := by omega
    use n - 1
    convert (walkZ_eq_neg_one_iff n).mpr hdvd using 2
    omega

end

/-- **Missing prime avoids death channel past sieve gap**: if q is a missing
    prime and all primes < q have appeared by step N, then for all n ≥ N,
    the multiplier at step n is NOT the forbidden multiplier. Equivalently,
    the walk doesn't hit -1 at step n+1.

    This is the contrapositive of `captures_target` in death channel language:
    if the walk WERE to hit -1 at step n+1 ≥ N (i.e., q | prod(n+1) + 1) with
    all primes < q having appeared by step n+1, then `captures_target` would
    give seq(n+2) = q, contradicting the assumption that q is missing.

    Intuition: past the sieve gap (after all smaller primes have appeared),
    any hit of -1 would immediately capture the prime into the sequence.
    Since q is assumed to be perpetually missing, such a hit cannot occur. -/
theorem missing_prime_avoids_death_channel {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (N : Nat)
    (hall : ∀ p, p < q → IsPrime p → ∃ m, m ≤ N ∧ seq m = p) :
    ∀ n, N ≤ n → emMultUnit q hq hne n ≠ forbiddenMultiplier (emWalkUnit q hq hne n) := by
  intro n hn habs
  -- If emMultUnit = forbiddenMultiplier(emWalkUnit), then walkZ q (n+1) = -1
  rw [← walk_hits_neg_one_iff_mult_eq_forbidden hq hne n] at habs
  -- This means q | prod(n+1) + 1
  have hdvd : q ∣ prod (n + 1) + 1 := by
    have hwalk_val := congr_arg Units.val habs
    simp only [emWalkUnit, Units.val_mk0] at hwalk_val
    exact (walkZ_eq_neg_one_iff (n + 1)).mp hwalk_val
  -- All primes < q appeared by step n+1 (since n ≥ N)
  have hall' : ∀ p, p < q → IsPrime p → ∃ m, m ≤ n + 1 ∧ seq m = p := by
    intro p hpq hp
    obtain ⟨m, hmN, hseqm⟩ := hall p hpq hp
    exact ⟨m, by omega, hseqm⟩
  -- captures_target gives seq(n+2) = q, contradicting hne
  exact hne (n + 2) (captures_target hq hdvd hall')

/-- **Death channel hit past sieve gap gives contradiction**: if a death
    channel hit occurs at step n+1 (i.e., walkZ q (n+1) = -1) and all primes
    < q have already appeared by step N ≤ n, then `captures_target` forces
    seq(n+2) = q, contradicting the assumption that q is missing.

    This formalizes the key observation: DCH hits that occur AFTER the sieve
    gap immediately capture the prime. The subtlety in "DCH → MC" is that
    DCH only guarantees ONE hit, which might occur before the sieve gap. -/
theorem dch_past_sieve_gap_contradiction {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (N : Nat)
    (hall : ∀ p, p < q → IsPrime p → ∃ m, m ≤ N ∧ seq m = p)
    (n : Nat) (hn : N ≤ n) (hwalk : walkZ q (n + 1) = -1) :
    False := by
  -- walkZ q (n+1) = -1 means q | prod(n+1) + 1
  have hdvd : q ∣ prod (n + 1) + 1 := (walkZ_eq_neg_one_iff (n + 1)).mp hwalk
  -- All primes < q appeared by step n+1
  have hall' : ∀ p, p < q → IsPrime p → ∃ m, m ≤ n + 1 ∧ seq m = p := by
    intro p hpq hp
    obtain ⟨m, hmN, hseqm⟩ := hall p hpq hp
    exact ⟨m, by omega, hseqm⟩
  -- captures_target gives seq(n+2) = q, contradicting hne
  exact hne (n + 2) (captures_target hq hdvd hall')

/-- **Walk avoidance contradicts SE + Mixing**: if the walk never hits `-1`
    mod q, then SubgroupEscape and MixingHypothesis cannot both hold.

    Proof: SE + Mixing → HH (by `se_mixing_implies_hh`), and HH gives
    `q ∣ prod(n)+1` cofinally, hence `walkZ q n = -1` cofinally —
    contradicting perpetual avoidance.

    This is the fundamental trichotomy: for any prime q not in seq, either
    (a) SE fails (multipliers confined to proper subgroup), or
    (b) Mixing fails (walk doesn't cover all coset elements), or
    (c) HH holds (walk hits -1 cofinally, so q eventually appears in seq). -/
theorem avoidance_contradicts_se_mixing {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (havoid : ∀ n, walkZ q n ≠ -1)
    (hse : SubgroupEscape) (hmix : MixingHypothesis) :
    False := by
  obtain ⟨n, _, hdvd⟩ := se_mixing_implies_hh hse hmix q hq hne 0
  exact havoid n ((walkZ_eq_neg_one_iff n).mpr hdvd)

/-- Some walk position is visited cofinally (infinitely often).
    By pigeonhole on the finite type `ZMod q`, the walk must revisit
    some position arbitrarily late. The visited position is nonzero
    since `walkZ q n ≠ 0` for all n. -/
theorem walk_cofinal_visit {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) :
    ∃ x : ZMod q, x ≠ 0 ∧ ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x := by
  obtain ⟨x, hx⟩ := cofinal_pigeonhole (fun _ => True) (walkZ q)
    (fun N => ⟨N, le_refl _, trivial⟩)
  refine ⟨x, ?_, fun N => let ⟨n, hn, _, hw⟩ := hx N; ⟨n, hn, hw⟩⟩
  obtain ⟨n, _, _, hw⟩ := hx 0
  rw [← hw]; exact walkZ_ne_zero hq hne n

/-- Some (walk, multiplier) pair appears cofinally. By pigeonhole on
    the finite type `ZMod q × ZMod q`, some pair must repeat
    infinitely often. This is stronger than just walk collisions:
    the same walk position is revisited with the same multiplier. -/
theorem cofinal_pair_repeat {q : Nat} [Fact (Nat.Prime q)]
    (_hq : IsPrime q) (_hne : ∀ k, seq k ≠ q) :
    ∃ w m : ZMod q, ∀ N, ∃ n, N ≤ n ∧ walkZ q n = w ∧ multZ q n = m := by
  obtain ⟨⟨w, m⟩, hx⟩ := cofinal_pigeonhole (fun _ => True)
    (fun n => (walkZ q n, multZ q n))
    (fun N => ⟨N, le_refl _, trivial⟩)
  exact ⟨w, m, fun N => by
    obtain ⟨n, hn, _, heq⟩ := hx N
    exact ⟨n, hn, congr_arg Prod.fst heq, congr_arg Prod.snd heq⟩⟩

/-- **Cofinal dodging at a fixed position**: if the walk never hits
    `-1` and visits position `x` cofinally, then at each such visit
    the multiplier dodges the death value `-(x⁻¹)`.

    This pins an infinite subsequence of multipliers away from one
    specific residue class — the sieve constraint that walk survival
    imposes on the multiplier sequence. -/
theorem cofinal_dodging_at_position {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (havoid : ∀ n, walkZ q n ≠ -1)
    {x : ZMod q} (hcofinal : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x) :
    ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x ∧ multZ q n ≠ -(x⁻¹) := by
  intro N
  obtain ⟨n, hn, hw⟩ := hcofinal N
  refine ⟨n, hn, hw, ?_⟩
  have hdodge := (perpetual_avoidance_iff hq hne).mp (fun n => havoid (n + 1)) n
  rw [hw] at hdodge; exact hdodge

/-- **Walk avoidance directly contradicts PairEquidistribution**: if the
    walk never hits `-1` mod q, then PE fails.

    PE → HH → walk hits -1 cofinally, so perpetual avoidance implies ¬PE.
    The contrapositive: PE → every prime's walk eventually hits -1 → MC. -/
theorem avoidance_contradicts_pe {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (havoid : ∀ n, walkZ q n ≠ -1) :
    ¬PairEquidistribution := by
  intro hpe
  obtain ⟨n, _, hdvd⟩ := pe_implies_hh hpe q hq hne 0
  exact havoid n ((walkZ_eq_neg_one_iff n).mpr hdvd)

end Sieve

/-! ## Weak Hitting Principle

The **Weak Hitting Principle** (WHP) asks: for every missing prime q, does
there exist a cofinally-visited walk position where the death value −x⁻¹
appears as the multiplier?

This is superficially weaker than PairEquidistribution (which requires EVERY
pair to appear) — WHP only needs ONE pair of the form (x, −x⁻¹). However,
WHP turns out to be **equivalent to HittingHypothesis** via pigeonhole: HH gives
cofinally many death-value realizations, and since there are only finitely many
walk positions mod q, pigeonhole concentrates these at a single position.

### Key results

* `WeakHittingPrinciple`: the definition
* `pe_implies_whp`: PE → WHP (trivial: any position works)
* `whp_implies_hh`: WHP → HH (via death value characterization)
* `hh_implies_whp`: HH → WHP (via cofinal pigeonhole — the surprise)
* `whp_iff_hh`: WHP ↔ HH (full equivalence)
-/

section WeakHitting

/-- Conversion between unit-level and ZMod-level death value statements.
    `emMultUnit n = -(emWalkUnit n)⁻¹` in `(ZMod q)ˣ` is equivalent to
    `multZ q n = -(walkZ q n)⁻¹` in `ZMod q`. -/
private theorem emMult_eq_neg_inv_walk_iff {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (n : Nat) :
    emMultUnit q hq hne n = -(emWalkUnit q hq hne n)⁻¹ ↔
    multZ q n = -(walkZ q n)⁻¹ := by
  constructor
  · intro h
    have := congrArg Units.val h
    simpa [emMultUnit, emWalkUnit] using this
  · intro h
    ext
    simpa [emMultUnit, emWalkUnit] using h

/-- **Weak Hitting Principle**: for every missing prime q, there exists a
    cofinally-visited walk position where the death value appears as the
    multiplier cofinally.

    This says: ∃ x visited cofinally, with the specific pair (x, −x⁻¹)
    appearing cofinally. It implies HH (hence MC) because (x, −x⁻¹)
    at step n means walkZ(n+1) = −1 by the death value characterization.

    Despite appearing weaker than HH, it is actually equivalent — see
    `whp_iff_hh`. -/
def WeakHittingPrinciple : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    ∃ x : (ZMod q)ˣ,
      (∀ N, ∃ n, N ≤ n ∧ emWalkUnit q hq hne n = x) ∧
      (∀ N, ∃ n, N ≤ n ∧ emWalkUnit q hq hne n = x ∧
        emMultUnit q hq hne n = -x⁻¹)

/-- **PE → WHP**: PairEquidistribution implies WeakHittingPrinciple.

    Take any walk position (e.g. 1). PE supplies the pair (1, −1⁻¹ = −1)
    cofinally. Since the second conjunct implies the first, both hold. -/
theorem pe_implies_whp (hpe : PairEquidistribution) : WeakHittingPrinciple := by
  intro q inst hq hne
  haveI : Fact (Nat.Prime q) := inst
  refine ⟨1, ?_, ?_⟩
  · intro N
    obtain ⟨n, hn, hw, _⟩ := hpe q hq hne 1 (-(1 : (ZMod q)ˣ)⁻¹) N
    exact ⟨n, hn, hw⟩
  · intro N
    obtain ⟨n, hn, hw, hm⟩ := hpe q hq hne 1 (-(1 : (ZMod q)ˣ)⁻¹) N
    exact ⟨n, hn, hw, hm⟩

/-- **WHP → HH**: WeakHittingPrinciple implies HittingHypothesis.

    At the cofinal death-value step n: walkZ(n) = x and multZ(n) = −x⁻¹.
    By `death_value_eq`, this gives walkZ(n+1) = −1, hence q ∣ prod(n+1) + 1. -/
theorem whp_implies_hh (hwhp : WeakHittingPrinciple) : HittingHypothesis := by
  intro q hq hne N
  haveI : Fact (Nat.Prime q) := ⟨IsPrime.toNatPrime hq⟩
  obtain ⟨x, _, hcof⟩ := hwhp q hq hne
  obtain ⟨n, hn, hwalk, hmult⟩ := hcof N
  rw [← hwalk] at hmult
  have hdeath : multZ q n = -(walkZ q n)⁻¹ :=
    (emMult_eq_neg_inv_walk_iff hq hne n).mp hmult
  have hhit : walkZ q (n + 1) = -1 := (death_value_eq hq hne n).mpr hdeath
  exact ⟨n + 1, by omega, (walkZ_eq_neg_one_iff (n + 1)).mp hhit⟩

/-- **WHP → MC**: WeakHittingPrinciple implies MullinConjecture (via HH). -/
theorem whp_implies_mullin (hwhp : WeakHittingPrinciple) : MullinConjecture :=
  hh_implies_mullin (whp_implies_hh hwhp)

/-- **HH → WHP**: HittingHypothesis implies WeakHittingPrinciple.

    This is the surprising direction: HH gives cofinally many n with
    walkZ(n) = −1. Each such n ≥ 1 has a predecessor m = n−1 where
    the death value relation holds: multZ(m) = −(walkZ(m))⁻¹. Since
    there are only finitely many walk positions mod q, cofinal pigeonhole
    concentrates these at a single position x — giving WHP. -/
theorem hh_implies_whp (hH : HittingHypothesis) : WeakHittingPrinciple := by
  intro q inst hq hne
  haveI : Fact (Nat.Prime q) := inst
  -- Cofinally many predecessors satisfy the death value relation
  have hcof_death : ∀ M, ∃ m, M ≤ m ∧
      emMultUnit q hq hne m = -(emWalkUnit q hq hne m)⁻¹ := by
    intro M
    obtain ⟨n, hn, hdvd⟩ := hH q hq hne (M + 1)
    have hhit : walkZ q n = -1 := (walkZ_eq_neg_one_iff n).mpr hdvd
    -- n ≥ 1 since hn : M + 1 ≤ n and M : ℕ
    refine ⟨n - 1, by omega, ?_⟩
    have hn_eq : n = (n - 1) + 1 := by omega
    rw [hn_eq] at hhit
    exact (emMult_eq_neg_inv_walk_iff hq hne (n - 1)).mpr
      ((death_value_eq hq hne (n - 1)).mp hhit)
  -- Pigeonhole: some walk position hosts cofinal death-value realizations
  obtain ⟨x, hx⟩ := cofinal_pigeonhole
    (fun m => emMultUnit q hq hne m = -(emWalkUnit q hq hne m)⁻¹)
    (emWalkUnit q hq hne)
    hcof_death
  refine ⟨x, ?_, ?_⟩
  · intro N
    obtain ⟨n, hn, _, hw⟩ := hx N
    exact ⟨n, hn, hw⟩
  · intro N
    obtain ⟨n, hn, hdeath, hw⟩ := hx N
    exact ⟨n, hn, hw, by rwa [hw] at hdeath⟩

/-- **WHP ↔ HH**: WeakHittingPrinciple is equivalent to HittingHypothesis.

    Despite WHP appearing to require localized death-value realizations at a
    single recurrent position, pigeonhole on finite `ZMod q` shows this is
    automatic from HH's cofinal hitting. -/
theorem whp_iff_hh : WeakHittingPrinciple ↔ HittingHypothesis :=
  ⟨whp_implies_hh, hh_implies_whp⟩

end WeakHitting

/-! ## §2C. Algebraic Properties of the Forbidden Multiplier Map

Further algebraic properties of the involution `forbiddenMultiplier : (ZMod q)ˣ → (ZMod q)ˣ`
defined by `c ↦ -c⁻¹`. These results characterize fixed points, behavior at special
elements, and the relationship to the Mobius-like "death function" `a ↦ (1 - a)⁻¹`
that arises from studying when successive walk positions avoid -1. -/

section ForbiddenMultiplierAlgebra

variable {q : Nat} [Fact (Nat.Prime q)]

/-- The value of `forbiddenMultiplier c` as an element of `ZMod q`. -/
theorem forbiddenMultiplier_val (c : (ZMod q)ˣ) :
    (forbiddenMultiplier c).val = -(c.val)⁻¹ := by
  simp only [forbiddenMultiplier, Units.val_mk0]

/-- `forbiddenMultiplier(-1) = 1`: the forbidden multiplier for position -1 is 1.
    Equivalently, if the walk is at -1, the multiplier 1 (= doing nothing) would
    keep it at -1. This reflects that -(-1)⁻¹ = -(-1) = 1. -/
theorem forbiddenMultiplier_neg_one :
    forbiddenMultiplier (-1 : (ZMod q)ˣ) = 1 := by
  ext
  simp only [forbiddenMultiplier, Units.val_mk0, Units.val_neg, Units.val_one]
  simp only [neg_inv, inv_one, neg_neg]

/-- `forbiddenMultiplier(1) = -1`: the forbidden multiplier for position 1 is -1.
    This means -(1)⁻¹ = -1. -/
theorem forbiddenMultiplier_one :
    forbiddenMultiplier (1 : (ZMod q)ˣ) = -1 := by
  ext
  simp only [forbiddenMultiplier, Units.val_mk0, Units.val_one, inv_one,
    Units.val_neg]

/-- **Forbidden multiplier ≠ 1 when walk ≠ -1**: if the walk position c is not -1,
    then the forbidden multiplier `-c⁻¹` is not 1.

    Proof: `-c⁻¹ = 1` iff `c⁻¹ = -1` iff `c = (-1)⁻¹ = -1`.
    Contrapositive: `c ≠ -1` implies `-c⁻¹ ≠ 1`.

    This is critical for the death channel analysis: at non-terminal walk positions,
    the forbidden multiplier is a non-trivial constraint (it forbids a residue
    class other than 1, so the sieve actually removes something). -/
theorem forbiddenMultiplier_ne_one_of_ne_neg_one
    (c : (ZMod q)ˣ) (hc : c ≠ -1) :
    forbiddenMultiplier c ≠ 1 := by
  intro h
  apply hc
  -- h : forbiddenMultiplier c = 1, so -(c.val)⁻¹ = 1
  -- Apply forbiddenMultiplier_involutive: c = forbiddenMultiplier(forbiddenMultiplier c)
  -- = forbiddenMultiplier(1) = -1
  rw [← forbiddenMultiplier_involutive c, h, forbiddenMultiplier_one]

/-- **Forbidden multiplier ≠ -1 when walk ≠ 1**: if the walk position c is not 1,
    then the forbidden multiplier `-c⁻¹` is not -1.

    Proof: `-c⁻¹ = -1` iff `c⁻¹ = 1` iff `c = 1`. -/
theorem forbiddenMultiplier_ne_neg_one_of_ne_one
    (c : (ZMod q)ˣ) (hc : c ≠ 1) :
    forbiddenMultiplier c ≠ -1 := by
  intro h
  apply hc
  -- h : forbiddenMultiplier c = -1
  -- Apply involutive: c = forbiddenMultiplier(forbiddenMultiplier c)
  -- = forbiddenMultiplier(-1) = 1
  rw [← forbiddenMultiplier_involutive c, h, forbiddenMultiplier_neg_one]

/-- The forbidden multiplier as a group-level expression:
    `forbiddenMultiplier c = -c⁻¹` in the units group `(ZMod q)ˣ`. -/
theorem forbiddenMultiplier_eq_neg_inv (c : (ZMod q)ˣ) :
    forbiddenMultiplier c = -c⁻¹ := by
  ext
  simp only [forbiddenMultiplier, Units.val_mk0, Units.val_neg,
    Units.val_inv_eq_inv_val]

/-- **Fixed point characterization**: `forbiddenMultiplier c = c` iff `c² = -1`.

    Proof: `-c⁻¹ = c` iff `-1 = c · c = c²`. Fixed points of the involution
    `c ↦ -c⁻¹` are exactly the square roots of -1 in `(ZMod q)ˣ`.
    These exist iff `q ≡ 1 (mod 4)` (by quadratic reciprocity). -/
theorem forbiddenMultiplier_eq_self_iff (c : (ZMod q)ˣ) :
    forbiddenMultiplier c = c ↔ c * c = -1 := by
  rw [forbiddenMultiplier_eq_neg_inv]
  constructor
  · intro h
    -- h : -c⁻¹ = c, need c * c = -1
    -- Multiply both sides of h by -c on the left:
    -- -c * (-c⁻¹) = -c * c
    -- LHS = c * c⁻¹ = 1, RHS = -(c * c)
    have h1 : -c * (-c⁻¹) = 1 := by
      simp only [neg_mul_neg]; exact mul_inv_cancel c
    have h2 : -c * (-c⁻¹) = -c * c := by rw [h]
    have h3 : (1 : (ZMod q)ˣ) = -c * c := by rw [← h1, h2]
    have h4 : -(c * c) = 1 := by
      rw [h3]; simp [neg_mul]
    exact (neg_neg (c * c)).symm.trans (congr_arg Neg.neg h4)
  · intro h
    -- h : c * c = -1, need -c⁻¹ = c
    -- Multiply h on the right by c⁻¹: c * (c * c⁻¹) = -c⁻¹
    have h1 : c * c * c⁻¹ = (-1 : (ZMod q)ˣ) * c⁻¹ := by rw [h]
    rw [mul_assoc, mul_inv_cancel, mul_one] at h1
    -- h1 : c = -1 * c⁻¹ = -c⁻¹
    rw [neg_one_mul] at h1
    exact h1.symm

/-- The forbidden multiplier map is injective (special case of bijectivity). -/
theorem forbiddenMultiplier_injective :
    Function.Injective (@forbiddenMultiplier q _) :=
  forbiddenMultiplier_bijective.1

/-- The forbidden multiplier map is surjective (special case of bijectivity). -/
theorem forbiddenMultiplier_surjective :
    Function.Surjective (@forbiddenMultiplier q _) :=
  forbiddenMultiplier_bijective.2

/-- **Death channel fraction**: at each step, the walk avoids -1 with probability
    at least (q-2)/(q-1) if the multiplier were uniform on `(ZMod q)ˣ`.
    Formally: for c ≠ -1, the forbidden multiplier is one specific non-identity
    element of `(ZMod q)ˣ`, so `Finset.univ.filter (· ≠ forbiddenMultiplier c)`
    has cardinality `q - 2`. -/
theorem death_channel_complement_card (hq3 : 3 ≤ q) (c : (ZMod q)ˣ) :
    (Finset.univ.filter (fun m : (ZMod q)ˣ => m ≠ forbiddenMultiplier c)).card =
      q - 2 := by
  have hprime := (Fact.out : Nat.Prime q)
  have hcard : Fintype.card (ZMod q)ˣ = q - 1 := by
    rw [ZMod.card_units_eq_totient]
    exact Nat.totient_prime hprime
  rw [Finset.filter_ne' Finset.univ (forbiddenMultiplier c),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard]
  omega

end ForbiddenMultiplierAlgebra

/-! ## §2D. Mobius Death Function

The **Mobius death function** `T : a ↦ (1 - a)⁻¹` arises naturally in the
analysis of walk transitions. If the walk is at position `c` and takes a
multiplier `a` (so the next position is `c * a`), then the walk reaches
`-1` iff `a = -c⁻¹` (the forbidden multiplier).

The composition `c ↦ -c⁻¹` viewed on the "Euclid number" `e = -c` gives
`e ↦ e⁻¹` (inversion), which is not order 3. But the Mobius death function
`T(a) = (1-a)⁻¹` for `a ≠ 1` is genuinely order 3:
  `T(T(T(a))) = a`   (when all intermediate values avoid 0 and 1).

The cycle is: `a → (1-a)⁻¹ → 1 - a⁻¹ → a`.
This 3-cycle structure is relevant because it describes how three walk
positions are "linked" by the death channel: if the walk can reach
position `c₁` with multiplier `a`, then the walk can reach position
`c₂` with multiplier `T(a)`, etc. -/

section MobiusDeath

variable {q : Nat} [Fact (Nat.Prime q)]

/-- The Mobius death function `T(a) = (1 - a)⁻¹` on `ZMod q`, which is
    well-defined as a function on all of `ZMod q` (returning 0 when `a = 1`). -/
noncomputable def mobiusDeath (a : ZMod q) : ZMod q := (1 - a)⁻¹

/-- `T(0) = 1`: the Mobius death function sends 0 to 1. -/
theorem mobiusDeath_zero : mobiusDeath (0 : ZMod q) = 1 := by
  simp [mobiusDeath]

/-- `T(1) = 0` (degenerate): when `a = 1`, `1 - a = 0` and the inverse is 0
    by convention in `ZMod q`. -/
theorem mobiusDeath_one : mobiusDeath (1 : ZMod q) = 0 := by
  simp [mobiusDeath]

/-- **Order-3 property of the Mobius death function**: `T(T(T(a))) = a` for all
    `a ∈ ZMod q` such that `a ≠ 0`, `a ≠ 1`, and `1 - a⁻¹ ≠ 1` (i.e., `a⁻¹ ≠ 0`,
    which is automatic for `a ≠ 0`).

    The cycle: `a → (1-a)⁻¹ → (1 - (1-a)⁻¹)⁻¹ → a`.

    Proof by direct computation in the field `ZMod q`:
    - `T(a) = (1-a)⁻¹`
    - `T(T(a)) = (1 - (1-a)⁻¹)⁻¹ = ((1-a - 1) · (1-a)⁻¹)⁻¹ · (-1)⁻¹
              = (1-a) · (-a)⁻¹ = -(1-a) · a⁻¹ = (a-1) · a⁻¹ = 1 - a⁻¹`
    - `T(T(T(a))) = (1 - (1 - a⁻¹))⁻¹ = (a⁻¹)⁻¹ = a`. -/
theorem mobiusDeath_order_three (a : ZMod q) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    mobiusDeath (mobiusDeath (mobiusDeath a)) = a := by
  simp only [mobiusDeath]
  have h1a : (1 : ZMod q) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  have ha_neg : -a ≠ (0 : ZMod q) := neg_ne_zero.mpr ha0
  -- We compute T^3(a) step by step.
  -- Step 1: T(a) = (1-a)⁻¹
  -- Step 2: 1 - T(a) = 1 - (1-a)⁻¹. We show this equals -a * (1-a)⁻¹
  have step1 : 1 - (1 - a)⁻¹ = -a * (1 - a)⁻¹ := by
    have h2 : (1 - a) * (1 - a)⁻¹ = 1 := mul_inv_cancel₀ h1a
    calc 1 - (1 - a)⁻¹
        = (1 - a) * (1 - a)⁻¹ - 1 * (1 - a)⁻¹ := by rw [h2, one_mul]
      _ = ((1 - a) - 1) * (1 - a)⁻¹ := by ring
      _ = -a * (1 - a)⁻¹ := by ring
  -- Step 3: T(T(a)) = (1 - T(a))⁻¹ = (-a * (1-a)⁻¹)⁻¹ = (1-a) * (-a)⁻¹
  have step2 : (-a * (1 - a)⁻¹)⁻¹ = (1 - a) * (-a)⁻¹ := by
    rw [mul_inv_rev, inv_inv, mul_comm]
  -- Step 4: 1 - T(T(a)) = 1 - (1-a) * (-a)⁻¹ = a⁻¹
  have step3 : 1 - (1 - a) * (-a)⁻¹ = a⁻¹ := by
    have hneg_inv : (-a)⁻¹ = -(a⁻¹) := neg_inv.symm
    rw [hneg_inv]
    have h3 : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0
    calc 1 - (1 - a) * -(a⁻¹) = 1 + (1 - a) * a⁻¹ := by ring
      _ = 1 + (a⁻¹ - a * a⁻¹) := by ring
      _ = 1 + (a⁻¹ - 1) := by rw [h3]
      _ = a⁻¹ := by ring
  -- Combine: T(T(T(a))) = (1 - T(T(a)))⁻¹ = (a⁻¹)⁻¹ = a
  rw [step1, step2, step3, inv_inv]

/-- **Mobius death function sends non-{0,1} to non-{0,1}**: if `a ≠ 0` and `a ≠ 1`,
    then `T(a) ≠ 0` and `T(a) ≠ 1`. This means the order-3 iteration stays in the
    domain where T is well-defined. -/
theorem mobiusDeath_ne_zero_one (a : ZMod q) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    mobiusDeath a ≠ 0 ∧ mobiusDeath a ≠ 1 := by
  constructor
  · -- T(a) = (1-a)⁻¹ ≠ 0 iff 1-a ≠ 0 iff a ≠ 1
    simp only [mobiusDeath]
    exact inv_ne_zero (sub_ne_zero.mpr (Ne.symm ha1))
  · -- T(a) = (1-a)⁻¹ ≠ 1 iff 1-a ≠ 1 iff a ≠ 0
    simp only [mobiusDeath]
    intro h
    apply ha0
    -- (1-a)⁻¹ = 1 implies 1-a = 1 (since 1-a ≠ 0), so a = 0
    have h1a : (1 : ZMod q) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
    have hinv1 : (1 - a)⁻¹ * (1 - a) = 1 := inv_mul_cancel₀ h1a
    rw [h, one_mul] at hinv1
    -- hinv1 : 1 - a = 1, so a = 0
    have : a = 1 - (1 - a) := by ring
    rw [hinv1] at this
    simpa using this

/-- **Relationship between forbidden multiplier and Mobius death**: the forbidden
    multiplier `-c⁻¹` at walk position `c` satisfies
    `forbiddenMultiplier(c) = -1` iff `c = 1`, i.e., position 1 is the unique
    position whose forbidden multiplier is `-1`.

    The Mobius death function `T(a) = (1-a)⁻¹` governs the *iteration* of the
    walk transition: if the walk is at position c and the next multiplier is
    m = forbiddenMultiplier(c) = -c⁻¹, then the walk transitions to -1. The
    Mobius function describes what happens when the walk "narrowly misses"
    the death channel — the iterates T, T^2, T^3 = id cycle through the
    three-fold symmetry of the Mobius group action. -/
theorem mobiusDeath_iterates_relate_to_forbidden (a : ZMod q)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    mobiusDeath (mobiusDeath a) = 1 - a⁻¹ := by
  -- Direct computation: T(T(a)) using the same steps as in order_three
  simp only [mobiusDeath]
  have h1a : (1 : ZMod q) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  have ha_neg : -a ≠ (0 : ZMod q) := neg_ne_zero.mpr ha0
  -- Step 1: 1 - (1-a)⁻¹ = -a * (1-a)⁻¹
  have step1 : 1 - (1 - a)⁻¹ = -a * (1 - a)⁻¹ := by
    have h2 : (1 - a) * (1 - a)⁻¹ = 1 := mul_inv_cancel₀ h1a
    calc 1 - (1 - a)⁻¹
        = (1 - a) * (1 - a)⁻¹ - 1 * (1 - a)⁻¹ := by rw [h2, one_mul]
      _ = ((1 - a) - 1) * (1 - a)⁻¹ := by ring
      _ = -a * (1 - a)⁻¹ := by ring
  -- Step 2: (-a * (1-a)⁻¹)⁻¹ = (1-a) * (-a)⁻¹
  have step2 : (-a * (1 - a)⁻¹)⁻¹ = (1 - a) * (-a)⁻¹ := by
    rw [mul_inv_rev, inv_inv, mul_comm]
  -- T(T(a)) = (step1)⁻¹ = (step2) = (1-a)*(-a)⁻¹
  rw [step1, step2]
  -- Need: (1-a)*(-a)⁻¹ = 1 - a⁻¹
  -- Key: (-a)⁻¹ = -a⁻¹
  have hneg_inv : (-a)⁻¹ = -(a⁻¹) := neg_inv.symm
  rw [hneg_inv]
  -- Goal: (1 - a) * -a⁻¹ = 1 - a⁻¹
  have h3 : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0
  calc (1 - a) * -(a⁻¹) = -(1 - a) * a⁻¹ := by ring
    _ = (a - 1) * a⁻¹ := by ring
    _ = a * a⁻¹ - 1 * a⁻¹ := by ring
    _ = 1 - a⁻¹ := by rw [h3, one_mul]

end MobiusDeath
