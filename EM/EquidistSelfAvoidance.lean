import EM.EquidistSieve

/-!
# Self-Avoidance and Periodicity Constraints

Structural constraints from the ambient injectivity of the EM sequence:
* `prod_strictMono`: products are strictly increasing
* Walk return analysis and distinct primes at returns
* Periodicity vs. generation: periodic walks constrain subgroup structure
-/

open Mullin Euclid MullinGroup RotorRouter


/-! ## Self-avoidance: structural constraints from ambient injectivity

The orbit {prod(n)} in ℤ (hence in Ẑ = profinite completion) is **injective**:
all products are distinct because the sequence is strictly increasing. The walk
mod q is the projection π_q of this orbit to (ℤ/qℤ)×.

Self-avoidance in the ambient space constrains the projected walk:

1. **Return structure**: walkZ(m) = walkZ(n) iff the intervening product
   seq(m+1) * ... * seq(n) ≡ 1 mod q — a specific multiplicative relation
   among distinct primes.

2. **Freshness at returns**: when the walk revisits a position, the multiplier
   at each visit comes from a DISTINCT prime (by seq_injective). So the
   multiplier residues at any cofinally-visited state come from infinitely
   many distinct primes.

3. **Non-periodicity**: walk periodicity would force multiplier periodicity
   (walk_periodic_implies_mult_periodic), constraining the EM primes to
   satisfy infinitely many congruences — an extremely strong constraint
   that "generically" fails.

The self-avoidance is strongest for SE (generation): distinct primes are
multiplicatively independent, making it easy for their residues to generate
the full group. For EMPR (coverage), self-avoidance gives freshness but
not equidistribution — infinitely many distinct primes CAN all avoid a
residue class (by Dirichlet's theorem), so additional input is needed. -/

section SelfAvoidance

/-- **Products are strictly increasing**: `prod(n) < prod(n+1)`.
    Since `seq(n+1) ≥ 2` (it's prime) and `prod(n) ≥ 2`, we have
    `prod(n+1) = prod(n) * seq(n+1) ≥ 2 * prod(n) > prod(n)`. -/
private theorem prod_lt_succ (m : Nat) : prod m < prod (m + 1) := by
  rw [prod_succ]
  calc prod m = prod m * 1 := (Nat.mul_one _).symm
    _ < prod m * seq (m + 1) :=
      Nat.mul_lt_mul_of_pos_left (seq_isPrime (m + 1)).1
        (by have := prod_ge_two m; omega)

theorem prod_strictMono : StrictMono prod := by
  intro m n hmn
  induction hmn with
  | refl => exact prod_lt_succ m
  | step _ ih => exact lt_trans ih (prod_lt_succ _)

/-- **Products are injective**: `prod(m) = prod(n) → m = n`.
    Immediate from strict monotonicity. -/
theorem prod_injective : Function.Injective prod :=
  prod_strictMono.injective

/-- **Walk telescoping product**: `walkZ(n) = walkZ(m) * (product of multipliers m..n-1)`.
    The walk position at step n is the step-m position times all intervening multipliers. -/
theorem walkZ_telescope {q : Nat} (m : Nat) :
    ∀ k, walkZ q (m + k) = walkZ q m * (Finset.range k).prod (fun i => multZ q (m + i)) := by
  intro k
  induction k with
  | zero => simp [Finset.range_zero, Finset.prod_empty, mul_one]
  | succ k ih =>
    have hstep : walkZ q (m + (k + 1)) = walkZ q (m + k) * multZ q (m + k) := by
      rw [show m + (k + 1) = m + k + 1 from by omega]; exact walkZ_succ q (m + k)
    rw [hstep, ih, Finset.prod_range_succ, mul_assoc]

/-- **Walk return means unit product**: if `walkZ(m) = walkZ(m+k)` with `k > 0`,
    then the product of `k` consecutive multipliers starting at index `m` equals
    1 in `ZMod q` (since `walkZ` is nonzero). -/
theorem walk_return_product {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {m k : Nat} (_hk : 0 < k) (hret : walkZ q m = walkZ q (m + k)) :
    (Finset.range k).prod (fun i => multZ q (m + i)) = 1 := by
  have htele := @walkZ_telescope q m k
  -- htele : walkZ q (m + k) = walkZ q m * prod
  -- hret : walkZ q m = walkZ q (m + k)
  rw [hret] at htele
  -- htele : walkZ q (m + k) = walkZ q (m + k) * prod
  have hne_zero := walkZ_ne_zero hq hne (m + k)
  exact (mul_right_eq_self₀.mp htele.symm).resolve_right hne_zero

/-- **Walk returns characterize unit products**: `walkZ(m) = walkZ(m+k)` iff
    the product of the `k` intervening multipliers equals 1 in `ZMod q`.
    This is the multiplicative version of "the walk returns iff the displacement
    is zero." Each multiplier is `seq(j+1) mod q` for a distinct prime, so
    a return encodes a specific multiplicative relation among distinct primes. -/
theorem walk_return_iff_unit_product {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (m k : Nat) :
    walkZ q m = walkZ q (m + k) ↔
      (Finset.range k).prod (fun i => multZ q (m + i)) = 1 := by
  constructor
  · intro hret
    by_cases hk : k = 0
    · subst hk; simp [Finset.range_zero, Finset.prod_empty]
    · exact walk_return_product hq hne (Nat.pos_of_ne_zero hk) hret
  · intro hprod
    have := @walkZ_telescope q m k
    rw [hprod, mul_one] at this
    exact this.symm

/-- **Distinct primes at returns**: if the walk visits position `x` at two
    different steps `n₁ < n₂`, then the multiplier *primes* (not just residues)
    at these steps are distinct: `seq(n₁+1) ≠ seq(n₂+1)`.

    This is immediate from `seq_injective` (the EM sequence never repeats a prime).
    The point is conceptual: self-avoidance in the ambient space (all products distinct)
    forces **fresh** multipliers at every return, preventing the walk from "recycling"
    the same arithmetic information. -/
theorem distinct_primes_at_returns {n₁ n₂ : Nat} (hne : n₁ ≠ n₂) :
    seq (n₁ + 1) ≠ seq (n₂ + 1) :=
  fun h => hne (Nat.succ_injective (seq_injective _ _ h))

/-- **Infinitely many distinct multiplier primes at any cofinal state**:
    if the walk visits position `x` at steps `n₀ < n₁ < n₂ < ...` (cofinally),
    then the multiplier primes `seq(nᵢ+1)` at these visits are ALL DISTINCT.

    Equivalently: the function `i ↦ seq(nᵢ + 1)` is injective on the index set.
    This means the multiplier residues `multZ q nᵢ` come from infinitely many
    different primes — even though their residues mod q may collide.

    This is the strongest structural constraint from self-avoidance: the walk
    cannot "run out" of fresh multiplier primes at any visited state. -/
theorem cofinal_state_has_distinct_mult_primes
    {q : Nat} [Fact (Nat.Prime q)]
    (_hq : IsPrime q) (_hne : ∀ k, seq k ≠ q)
    {x : ZMod q} (_hcof : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x)
    {_i _j : Nat}
    (ni nj : Nat) (_hni : walkZ q ni = x) (_hnj : walkZ q nj = x)
    (hij : ni ≠ nj) :
    seq (ni + 1) ≠ seq (nj + 1) :=
  distinct_primes_at_returns hij

/-- **Non-periodicity from distinct primes**: if the walk were eventually periodic
    with period `d`, then `multZ q n = multZ q (n + d)` for all large `n`
    (by `walk_periodic_implies_mult_periodic`). This means `seq(n+1) ≡ seq(n+d+1) mod q`
    for all large `n`. Since the EM primes are all distinct, this requires infinitely
    many pairs of distinct primes to be congruent mod q — which constrains the
    sequence to use at most `q-1` residue classes, each infinitely often.

    The stronger constraint: periodic multipliers of period `d` mean the walk
    visits at most `d` distinct positions, giving at most `d` "phase classes."
    Combined with the coset structure, this severely limits the walk's behavior. -/
theorem walk_periodic_mult_count {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {i d : Nat} (_hd : 0 < d)
    (hperiod : ∀ k, walkZ q (i + k) = walkZ q (i + d + k)) :
    ∀ k, multZ q (i + k) = multZ q (i + d + k) :=
  walk_periodic_implies_mult_periodic hq hne
    (by intro k; rw [show i + d + k = (i + d) + k from by omega]; exact hperiod k)

/-- **Walk period bounds visit count**: if the walk is periodic with period `d`
    starting from step `i`, then it visits at most `d` distinct positions.
    Specifically: for any `k`, the walk position at step `i + k` equals one
    of the positions at steps `i, i+1, ..., i+d-1`.  -/
theorem periodic_walk_positions_bounded {q : Nat}
    {i d : Nat} (_hd : 0 < d)
    (hperiod : ∀ k, walkZ q (i + k) = walkZ q (i + d + k)) :
    ∀ k, ∃ r, r < d ∧ walkZ q (i + k) = walkZ q (i + r) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases hk : k < d
    · exact ⟨k, hk, rfl⟩
    · have hkd : k - d < k := by omega
      obtain ⟨r, hr, heq⟩ := ih (k - d) hkd
      refine ⟨r, hr, ?_⟩
      calc walkZ q (i + k)
          = walkZ q (i + d + (k - d)) := by congr 1; omega
        _ = walkZ q (i + (k - d)) := (hperiod (k - d)).symm
        _ = walkZ q (i + r) := heq

/-- **Multiplier distinctness limits period**: if the walk has period `d`
    starting from step `i`, then at each of the `d` positions in the cycle,
    the multipliers at successive visits are distinct primes.

    This means: for each position `walkZ q (i + r)` (r = 0, ..., d-1),
    the multipliers at steps `i + r, i + r + d, i + r + 2d, ...` are
    residues of the distinct primes `seq(i+r+1), seq(i+r+d+1), seq(i+r+2d+1), ...`.

    So each position in the cycle sees infinitely many distinct multiplier primes,
    but they all map to the SAME residue mod q (by multiplier periodicity).
    This means: `seq(i+r+1) ≡ seq(i+r+d+1) ≡ seq(i+r+2d+1) ≡ ... (mod q)`.
    Infinitely many distinct primes in the same residue class — possible
    (Dirichlet), but a very strong structural constraint.

    Self-avoidance alone cannot rule this out, but it shows that walk periodicity
    forces the EM primes into `d` specific residue classes mod q, visited
    in a fixed cyclic order. -/
theorem periodic_forces_residue_classes {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {i d : Nat} (hd : 0 < d)
    (hperiod : ∀ k, walkZ q (i + k) = walkZ q (i + d + k))
    (r j : Nat) :
    multZ q (i + r + j * d) = multZ q (i + r) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hmult := walk_periodic_mult_count hq hne hd hperiod
    -- hmult k : multZ q (i + k) = multZ q (i + d + k)
    -- Goal: multZ q (i + r + (j + 1) * d) = multZ q (i + r)
    -- Key step: i + r + (j + 1) * d = (i + d) + (r + j * d)
    --           = i + d + (r + j * d) = target of hmult at k = r + j * d
    have h := hmult (r + j * d)
    -- h : multZ q (i + (r + j * d)) = multZ q (i + d + (r + j * d))
    -- Goal: multZ q (i + r + (j+1)*d) = multZ q (i + r)
    -- Strategy: rewrite goal LHS to match h's RHS, then use h.symm + ih
    calc multZ q (i + r + (j + 1) * d)
        = multZ q (i + d + (r + j * d)) := by
          congr 1; simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ = multZ q (i + (r + j * d)) := h.symm
      _ = multZ q (i + r + j * d) := by congr 1; omega
      _ = multZ q (i + r) := ih

/-- **Cofinal multiplier residue at a visited state**: at any cofinally-visited
    walk state `x`, some multiplier residue `s` appears cofinally.
    This is cofinal_pigeonhole restricted to visits at `x`. -/
theorem cofinal_mult_at_state
    {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {x : ZMod q} (hcof : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x) :
    ∃ s : ZMod q, s ≠ 0 ∧
      ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x ∧ multZ q n = s := by
  obtain ⟨s, hs⟩ := cofinal_pigeonhole (fun n => walkZ q n = x)
    (fun n => multZ q n) hcof
  refine ⟨s, ?_, fun N => by obtain ⟨n, hn, hw, hm⟩ := hs N; exact ⟨n, hn, hw, hm⟩⟩
  obtain ⟨n, _, _, hm⟩ := hs 0
  rw [← hm]; exact multZ_ne_zero hq hne n

/-- **Distinct primes feed each cofinal pair**: at any cofinally-visited
    walk state `x` with cofinal multiplier residue `s`, the visits come from
    infinitely many DISTINCT primes (even though they all have residue `s` mod q).

    Concretely: if steps `n₁ < n₂` both have `walkZ q nᵢ = x` and `multZ q nᵢ = s`,
    then `seq(n₁+1) ≠ seq(n₂+1)` — the primes are fresh.

    This is immediate from `seq_injective`. Its content is conceptual:
    self-avoidance means the walk cannot "recycle" arithmetic information.
    Each return to `(x, s)` requires a genuinely new prime in the residue
    class `s mod q`. Dirichlet guarantees such primes exist, but the EM
    sequence must find them via its greedy algorithm. -/
theorem cofinal_pair_distinct_primes
    {q : Nat} [Fact (Nat.Prime q)]
    {x s : ZMod q} {n₁ n₂ : Nat} (hne12 : n₁ ≠ n₂)
    (_hw1 : walkZ q n₁ = x) (_hm1 : multZ q n₁ = s)
    (_hw2 : walkZ q n₂ = x) (_hm2 : multZ q n₂ = s) :
    seq (n₁ + 1) ≠ seq (n₂ + 1) :=
  distinct_primes_at_returns hne12

/-- **The self-avoidance dichotomy**: for any cofinally-visited walk state `x`,
    either:
    (a) the multiplier residues at visits to `x` take ALL `q-1` nonzero values
        (full EMPR at this state), or
    (b) some nonzero residue `s` is missed — meaning infinitely many distinct
        EM primes map to a STRICT SUBSET of residue classes mod q at visits
        to `x`.

    Option (b) requires the EM construction to "conspire" with the modulus q:
    the subsequence of primes selected when the walk is at position `x` must
    systematically avoid certain residue classes, even though Dirichlet's theorem
    guarantees infinitely many primes in each class.

    This reduces EMPR to a **Dirichlet-type question**: can the EM algorithm's
    greedy selection (minFac of prod(n)+1) correlate with residue classes mod q
    at specific walk positions? -/
theorem self_avoidance_dichotomy
    {q : Nat} [Fact (Nat.Prime q)]
    (_hq : IsPrime q) (_hne : ∀ k, seq k ≠ q)
    {x : ZMod q} (_hx : x ≠ 0) (_hcof : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x) :
    (∀ (s : ZMod q), s ≠ 0 → ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x ∧ multZ q n = s) ∨
    (∃ (s : ZMod q), s ≠ 0 ∧
      ¬∀ N, ∃ n, N ≤ n ∧ walkZ q n = x ∧ multZ q n = s) := by
  by_cases h : ∀ (s : ZMod q), s ≠ 0 → ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x ∧ multZ q n = s
  · exact Or.inl h
  · right; push_neg at h
    obtain ⟨s, hs_ne, N, hN⟩ := h
    exact ⟨s, hs_ne, fun hcof_s => by
      obtain ⟨n, hn, _, _⟩ := hcof_s N; exact hN n hn ‹_› ‹_›⟩

end SelfAvoidance

/-! ## Periodicity vs. Generation: structural constraints

Walk periodicity forces the multiplier sequence into a rigid cyclic pattern.
Combined with SubgroupEscape (generation), this constrains the period:

1. **Cycle product = 1**: The product of one full cycle of multipliers is the
   identity in `(ℤ/qℤ)×` (walk returns to its starting position).

2. **Period 1 forces trivial multiplier**: Walk period 1 means all multipliers
   from the periodic phase onward equal 1.

3. **SE + cycle generates → d ≥ 2**: If the cycle multipliers generate the full
   group (which SE guarantees when all mult values come from the cycle), then
   the period must be ≥ 2 for `q ≥ 3`.

4. **HH ↔ -1 in cycle**: For periodic walks, the Hitting Hypothesis holds iff
   `-1` appears among the `d` cycle positions.

Combined with self-avoidance (`periodic_forces_residue_classes`), each of the
`d` cycle residue classes must contain infinitely many distinct EM primes — an
extreme structural prediction. -/

section PeriodicityVsGeneration

/-- Walk periodicity at multiples: the walk at step `i + r + j*d` equals
    the walk at step `i + r`. This is the "unwound" version of periodicity:
    positions separated by a multiple of the period are equal. -/
theorem walk_periodic_at_multiples {q : Nat}
    {i d : Nat}
    (hperiod : ∀ k, walkZ q (i + k) = walkZ q (i + d + k))
    (r j : Nat) : walkZ q (i + r + j * d) = walkZ q (i + r) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc walkZ q (i + r + (j + 1) * d)
        = walkZ q (i + d + (r + j * d)) := by
          congr 1; simp [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ = walkZ q (i + (r + j * d)) := (hperiod (r + j * d)).symm
      _ = walkZ q (i + r + j * d) := by congr 1; omega
      _ = walkZ q (i + r) := ih

/-- Walk periodic from step `i` with period `d` → product of one cycle of
    multipliers equals 1 in `(ℤ/qℤ)×`. Since `walkZ q i = walkZ q (i + d)`,
    the intervening product must be the identity. -/
theorem walk_periodic_cycle_product_one {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {i d : Nat} (hd : 0 < d)
    (hperiod : ∀ k, walkZ q (i + k) = walkZ q (i + d + k)) :
    (Finset.range d).prod (fun r => multZ q (i + r)) = 1 := by
  have hret : walkZ q i = walkZ q (i + d) := by
    have := hperiod 0; simp at this; exact this
  exact walk_return_product hq hne hd hret

/-- Walk period 1 forces trivial multiplier: if `walkZ q (i + k) = walkZ q (i + 1 + k)`
    for all `k`, then `multZ q (i + k) = 1` for all `k`.

    Proof: the cycle product with `d = 1` gives `multZ q i = 1`, and
    `periodic_forces_residue_classes` gives `multZ q (i + k) = multZ q i`. -/
theorem walk_period_one_mult_eq_one {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {i : Nat} (hperiod : ∀ k, walkZ q (i + k) = walkZ q (i + 1 + k)) :
    ∀ k, multZ q (i + k) = 1 := by
  have h1 := walk_periodic_cycle_product_one hq hne (by omega : 0 < 1) hperiod
  simp [Finset.range_one, Finset.prod_singleton] at h1
  -- h1 : multZ q i = 1
  intro k
  have hresid := periodic_forces_residue_classes hq hne (by omega : 0 < 1) hperiod 0 k
  simp at hresid
  -- hresid : multZ q (i + k) = multZ q i
  rw [hresid, h1]

/-- If walk periodic and `-1` appears among the cycle positions, then
    the walk hits `-1` cofinally (infinitely often). -/
theorem walk_periodic_neg_one_cofinal {q : Nat}
    {i d : Nat} (hd : 0 < d)
    (hperiod : ∀ k, walkZ q (i + k) = walkZ q (i + d + k))
    {r : Nat} (_hr : r < d) (hneg : walkZ q (i + r) = -1) :
    ∀ N, ∃ n, N ≤ n ∧ walkZ q n = -1 := by
  intro N
  refine ⟨i + r + N * d, le_trans (Nat.le_mul_of_pos_right N hd) (Nat.le_add_left _ _), ?_⟩
  rw [walk_periodic_at_multiples hperiod r N, hneg]

/-- If walk periodic from step `i` and `-1` is visited at some step `≥ i`,
    then `-1` appears among the `d` cycle positions. -/
theorem walk_periodic_neg_one_in_cycle {q : Nat}
    {i d : Nat} (hd : 0 < d)
    (hperiod : ∀ k, walkZ q (i + k) = walkZ q (i + d + k))
    {n : Nat} (hn : i ≤ n) (hneg : walkZ q n = -1) :
    ∃ r, r < d ∧ walkZ q (i + r) = -1 := by
  obtain ⟨r, hr, heq⟩ := periodic_walk_positions_bounded hd hperiod (n - i)
  refine ⟨r, hr, ?_⟩
  have hni : i + (n - i) = n := Nat.add_sub_cancel' hn
  rw [← heq, hni, hneg]

/-- **Periodic walk HH criterion**: for a walk periodic from step `i`, the
    Hitting Hypothesis (cofinal divisibility by `q`) holds iff `-1` appears
    among the `d` cycle positions AND all previous steps are accounted for.

    More precisely: `-1` is visited cofinally iff it's in the cycle. -/
theorem walk_periodic_hh_iff_in_cycle {q : Nat}
    {i d : Nat} (hd : 0 < d)
    (hperiod : ∀ k, walkZ q (i + k) = walkZ q (i + d + k)) :
    (∀ N, ∃ n, N ≤ n ∧ walkZ q n = -1) ↔
    (∃ r, r < d ∧ walkZ q (i + r) = -1) := by
  constructor
  · intro hcof
    obtain ⟨n, hn, hneg⟩ := hcof i
    exact walk_periodic_neg_one_in_cycle hd hperiod hn hneg
  · rintro ⟨r, hr, hneg⟩
    exact walk_periodic_neg_one_cofinal hd hperiod hr hneg

open Classical in
/-- **Period ≥ 2 when cycle generates**: if the walk is periodic with period `d`
    and the cycle multiplier values escape every proper subgroup (i.e., SE
    restricted to the cycle), then `d ≥ 2` for `q ≥ 3`.

    Proof: period 1 forces all cycle multipliers = 1, but `{1}` doesn't escape
    the trivial subgroup `⊥` (which is proper for `q ≥ 3`). -/
theorem walk_periodic_d_ge_two {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {i d : Nat} (hd : 0 < d)
    (hperiod : ∀ k, walkZ q (i + k) = walkZ q (i + d + k))
    (hq3 : 3 ≤ q)
    -- The cycle multipliers escape every proper subgroup
    (hcycle_escape : ∀ (H : Subgroup (ZMod q)ˣ), H ≠ ⊤ →
      ∃ r, r < d ∧ Units.mk0 (multZ q (i + r)) (multZ_ne_zero hq hne _) ∉ H) :
    2 ≤ d := by
  by_contra hd2
  have hd1 : d = 1 := by omega
  subst hd1
  -- All cycle mults = 1
  have hmult1 := walk_period_one_mult_eq_one hq hne hperiod
  -- The trivial subgroup ⊥ is proper for q ≥ 3
  have hbot_ne : (⊥ : Subgroup (ZMod q)ˣ) ≠ ⊤ := by
    have hcard : Fintype.card (ZMod q)ˣ = q - 1 := by
      rw [ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out)]
    intro h
    -- ⊥ = ⊤ as subgroups means every element is 1
    have hall : ∀ x : (ZMod q)ˣ, x = 1 := fun x =>
      Subgroup.mem_bot.mp (h ▸ Subgroup.mem_top x)
    have : Fintype.card (ZMod q)ˣ ≤ 1 :=
      Fintype.card_le_one_iff.mpr fun a b => (hall a).trans (hall b).symm
    omega
  -- But cycle escape at ⊥ gives r < 1 with mult ∉ ⊥, i.e., mult ≠ 1
  obtain ⟨r, hr, hesc⟩ := hcycle_escape ⊥ hbot_ne
  -- r < 1 means r = 0
  have hr0 : r = 0 := by omega
  subst hr0
  -- multZ q (i + 0) = 1 by hmult1
  have h1 := hmult1 0
  simp at h1
  -- But Units.mk0 (multZ q (i+0)) _ = 1 ∈ ⊥
  simp only [Nat.add_zero] at hesc
  apply hesc
  have : Units.mk0 (multZ q i) (multZ_ne_zero hq hne i) = 1 := by ext; simpa using h1
  rw [this]
  exact Subgroup.one_mem _

end PeriodicityVsGeneration
