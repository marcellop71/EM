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
