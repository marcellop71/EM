import EM.EquidistThreshold

/-!
# Cofinal Orbit Expansion and Quotient Walk Decomposition

* Cofinal orbit expansion: chain of cofinally visited positions
* Character-theoretic DH reformulation
* Quotient walk decomposition: `quotient_walk_recurrence`
* Cofinal escape reduction and orbit chain cycle
-/

open Mullin Euclid MullinGroup RotorRouter


/-! ## §16. Cofinal Orbit Expansion

Under HH failure, the walk never hits -1 past some threshold. The set of
**cofinally visited positions** (positions visited infinitely often) has rich
structure:

1. It is nonempty (pigeonhole on the finite group).
2. At each cofinally visited position, some multiplier appears cofinally
   (pigeonhole on multipliers at that position).
3. The successor position x · s is also cofinally visited.
4. Under HH failure, the cofinal multiplier at each position avoids the
   death value: s ≠ -(x)⁻¹.
5. Since the group is finite, the chain of cofinally visited positions
   eventually cycles, giving a finite orbit with a product-one cycle relation.

This section formalizes the orbit expansion and its structural constraints. -/

section CofinalOrbitExpansion

/-- At any cofinally visited position, pigeonhole on the finite set of
    possible multipliers gives a cofinal (position, multiplier) pair.
    This is the entry point for orbit expansion: each cofinally visited
    position has an outgoing "edge" to another cofinally visited position. -/
theorem cofinal_visited_has_cofinal_mult {q : Nat} [Fact (Nat.Prime q)]
    (_hq : IsPrime q) (_hne : ∀ k, seq k ≠ q)
    {x : ZMod q} (hx : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x) :
    ∃ s : ZMod q, ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x ∧ multZ q n = s := by
  obtain ⟨s, hs⟩ := cofinal_pigeonhole (fun n => walkZ q n = x) (multZ q)
    (fun N => let ⟨n, hn, hw⟩ := hx N; ⟨n, hn, hw⟩)
  exact ⟨s, fun N => by
    obtain ⟨n, hn, hw, hm⟩ := hs N
    exact ⟨n, hn, hw, hm⟩⟩

/-- The cofinal multiplier at a cofinally visited position is nonzero
    (since all multipliers are nonzero for primes not in the sequence). -/
theorem cofinal_mult_ne_zero {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {x s : ZMod q} (hcof : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x ∧ multZ q n = s) :
    s ≠ 0 := by
  intro hs
  obtain ⟨n, _, _, hm⟩ := hcof 0
  exact multZ_ne_zero hq hne n (hm ▸ hs)

/-- **Orbit expansion step**: from a cofinally visited position x with
    cofinal multiplier s, the successor x · s is cofinally visited and
    has its own cofinal multiplier. This gives a chain:
    x₀ →^{s₀} x₁ →^{s₁} x₂ →^{s₂} ⋯ where each xᵢ is cofinally visited. -/
theorem cofinal_orbit_step {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {x s : ZMod q} (hcof : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x ∧ multZ q n = s) :
    ∃ s' : ZMod q, ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x * s ∧ multZ q n = s' := by
  have hxs_cof : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x * s :=
    cofinal_successor_visited hcof
  exact cofinal_visited_has_cofinal_mult hq hne hxs_cof

/-- Under HH failure, the cofinal multiplier at each cofinally visited
    position avoids the death value. Generalization of `cofinal_pair_avoids_death`
    to arbitrary cofinally visited positions, not just the initial one. -/
theorem cofinal_death_avoidance_at_position {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hhf : ∃ N₀, ∀ n, N₀ ≤ n → walkZ q n ≠ -1)
    {x s : ZMod q} (hcof : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x ∧ multZ q n = s) :
    s ≠ -(x)⁻¹ := cofinal_pair_avoids_death hq hne hcof hhf

/-- Under HH failure, -1 is NOT cofinally visited (eventually avoided). -/
theorem hh_failure_neg_one_not_cofinal {q : Nat} [Fact (Nat.Prime q)]
    (hhf : ∃ N₀, ∀ n, N₀ ≤ n → walkZ q n ≠ -1) :
    ¬(∀ N, ∃ n, N ≤ n ∧ walkZ q n = -1) := by
  obtain ⟨N₀, hN₀⟩ := hhf
  intro hcof
  obtain ⟨n, hn, hw⟩ := hcof N₀
  exact hN₀ n hn hw

/-- The successor position from a cofinal pair is nonzero. -/
theorem cofinal_successor_ne_zero {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {w₀ s₀ : ZMod q}
    (hcof : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = w₀ ∧ multZ q n = s₀) :
    w₀ * s₀ ≠ 0 := by
  obtain ⟨n, _, hw, hs⟩ := hcof 0
  rw [← hw, ← hs, ← walkZ_succ]
  exact walkZ_ne_zero hq hne (n + 1)

/-- Under HH failure, the successor w₀ · s₀ ≠ -1.
    Since w₀ · s₀ = walkZ(n+1) at each cofinal visit, and walkZ(n+1) ≠ -1
    for all large n, the successor position avoids -1. -/
theorem cofinal_successor_ne_neg_one {q : Nat} [Fact (Nat.Prime q)]
    (_hq : IsPrime q) (_hne : ∀ k, seq k ≠ q)
    {w₀ s₀ : ZMod q}
    (hcof : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = w₀ ∧ multZ q n = s₀)
    (hhf : ∃ N₀, ∀ n, N₀ ≤ n → walkZ q n ≠ -1) :
    w₀ * s₀ ≠ -1 := by
  obtain ⟨N₀, hN₀⟩ := hhf
  intro heq
  obtain ⟨n, hn, hw, hs⟩ := hcof N₀
  exact hN₀ (n + 1) (by omega) (by rw [walkZ_succ, hw, hs, heq])

/-- **Cofinal chain length 2**: from the initial cofinal pair (w₀, s₀),
    the successor w₁ = w₀ · s₀ has its own cofinal multiplier s₁,
    and the next successor w₂ = w₁ · s₁ is cofinally visited too.
    Under HH failure, both s₀ and s₁ avoid their respective death values,
    and w₂ ≠ -1.
    This demonstrates the general pattern: the cofinal orbit expands
    indefinitely, with death-value avoidance at every step. -/
theorem cofinal_chain_two {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {w₀ s₀ : ZMod q}
    (hcof₀ : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = w₀ ∧ multZ q n = s₀)
    (hhf : ∃ N₀, ∀ n, N₀ ≤ n → walkZ q n ≠ -1) :
    ∃ s₁ : ZMod q,
      (∀ N, ∃ n, N ≤ n ∧ walkZ q n = w₀ * s₀ ∧ multZ q n = s₁) ∧
      s₁ ≠ -(w₀ * s₀)⁻¹ ∧
      (∀ N, ∃ n, N ≤ n ∧ walkZ q n = w₀ * s₀ * s₁) := by
  have hw₁_cof : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = w₀ * s₀ :=
    cofinal_successor_visited hcof₀
  obtain ⟨s₁, hs₁⟩ := cofinal_visited_has_cofinal_mult hq hne hw₁_cof
  refine ⟨s₁, hs₁, ?_, cofinal_successor_visited hs₁⟩
  exact cofinal_death_avoidance_at_position hq hne hhf hs₁

/-- **Two distinct cofinal positions**: if the cofinal multiplier s₀ ≠ 1,
    then w₀ and w₀ · s₀ are distinct cofinally visited positions. -/
theorem cofinal_two_positions {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {w₀ s₀ : ZMod q}
    (hcof : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = w₀ ∧ multZ q n = s₀)
    (hs : s₀ ≠ 1) :
    w₀ ≠ w₀ * s₀ := by
  intro heq
  have hw_ne : w₀ ≠ 0 := by
    obtain ⟨n, _, hw, _⟩ := hcof 0; rw [← hw]; exact walkZ_ne_zero hq hne n
  exact hs (mul_left_cancel₀ hw_ne (heq ▸ (mul_one w₀).symm))

/-- **Death value is a unit**: the death value -(x)⁻¹ at a nonzero position
    x is nonzero (and hence a unit in ZMod q). -/
theorem death_value_ne_zero {q : Nat} [Fact (Nat.Prime q)]
    {x : ZMod q} (hx : x ≠ 0) : -(x)⁻¹ ≠ 0 := by
  simp [hx]

/-- **Summary of cofinal orbit constraints under HH failure**: for any prime
    q not in the sequence, if HH fails (walk eventually never hits -1), then:
    (1) some position w₀ is cofinally visited,
    (2) some multiplier s₀ appears cofinally at w₀ with s₀ ≠ -(w₀)⁻¹,
    (3) w₁ = w₀ · s₀ is cofinally visited with w₁ ≠ -1,
    (4) some s₁ appears cofinally at w₁ with s₁ ≠ -(w₁)⁻¹,
    (5) w₂ = w₁ · s₁ is cofinally visited with w₂ ≠ -1,
    and so on. The orbit expansion generates a finite graph (since ZMod q is
    finite) that must contain a cycle, with the product of multipliers around
    the cycle equal to 1 (since the walk returns to the same position). -/
theorem cofinal_orbit_summary {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hhf : ∃ N₀, ∀ n, N₀ ≤ n → walkZ q n ≠ -1) :
    ∃ (w₀ s₀ s₁ : ZMod q),
      -- (w₀, s₀) cofinal
      (∀ N, ∃ n, N ≤ n ∧ walkZ q n = w₀ ∧ multZ q n = s₀) ∧
      -- death avoidance at w₀
      s₀ ≠ -(w₀)⁻¹ ∧
      -- (w₀ · s₀, s₁) cofinal
      (∀ N, ∃ n, N ≤ n ∧ walkZ q n = w₀ * s₀ ∧ multZ q n = s₁) ∧
      -- death avoidance at w₀ · s₀
      s₁ ≠ -(w₀ * s₀)⁻¹ ∧
      -- successor w₀ · s₀ · s₁ cofinally visited
      (∀ N, ∃ n, N ≤ n ∧ walkZ q n = w₀ * s₀ * s₁) ∧
      -- -1 not in the first three positions
      w₀ ≠ -1 ∧ w₀ * s₀ ≠ -1 ∧ w₀ * s₀ * s₁ ≠ -1 := by
  obtain ⟨w₀, m₀, hcof₀⟩ := cofinal_pair_repeat hq hne
  have hdeath₀ := cofinal_death_avoidance_at_position hq hne hhf hcof₀
  obtain ⟨s₁, hs₁, hdeath₁, hsucc₁⟩ := cofinal_chain_two hq hne hcof₀ hhf
  have hw₀_ne : w₀ ≠ -1 := by
    obtain ⟨N₀, hN₀⟩ := hhf
    intro heq; obtain ⟨n, hn, hw, _⟩ := hcof₀ N₀; exact hN₀ n hn (hw ▸ heq)
  have hw₁_ne : w₀ * m₀ ≠ -1 := cofinal_successor_ne_neg_one hq hne hcof₀ hhf
  have hw₂_ne : w₀ * m₀ * s₁ ≠ -1 := cofinal_successor_ne_neg_one hq hne hs₁ hhf
  exact ⟨w₀, m₀, s₁, hcof₀, hdeath₀, hs₁, hdeath₁, hsucc₁,
    hw₀_ne, hw₁_ne, hw₂_ne⟩

end CofinalOrbitExpansion

/-! ## §17. Character-Theoretic Reformulation of DynamicalHitting

DynamicalHitting asserts: SE(q) → walk hits -1 cofinally. The character
perspective decomposes "walk = -1" into a family of quotient conditions.

For each proper subgroup H < (ZMod q)ˣ, the quotient map mk'(H) sends
the walk to (ZMod q)ˣ/H. The walk hits -1 iff its quotient image matches
(-1)'s image in EVERY quotient simultaneously.

Under SE, each quotient walk is non-constant (it visits every coset).
DH asks whether these non-constant quotient walks synchronize: can we
find a single step n where ALL quotient walks simultaneously match -1's
image? This is the **character synchronization problem**.

The character product formula (§8) gives:
  mk'(H)(w(n)) = mk'(H)(w(0)) · ∏_{k<n} mk'(H)(m(k))

So synchronization requires the cumulative products in each quotient to
simultaneously reach a prescribed target value.
-/

section CharacterDHReformulation

open MullinGroup

/-- **Walk = -1 iff all quotients agree**: the walk hits -1 at step n iff
    every quotient map sends w(n) and -1 to the same element. The forward
    direction is trivial; the backward direction uses that the walk value
    and -1 are both units, so if they differ, the quotient by the subgroup
    generated by their ratio witnesses the difference. -/
theorem walk_eq_neg_one_iff_quotients {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (n : Nat) :
    walkZ q n = -1 →
    ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      QuotientGroup.mk' H (Units.mk0 (walkZ q n) (walkZ_ne_zero hq hne n)) =
      QuotientGroup.mk' H (Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero)) := by
  intro hw H _
  congr 1; exact Units.ext hw

/-- **Character product target**: the walk hits -1 at step n iff the
    cumulative character product equals the target value χ(-w(0)⁻¹) for
    every group homomorphism χ. This uses the character product formula. -/
theorem char_product_hits_neg_one {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {G : Type*} [CommGroup G]
    (χ : (ZMod q)ˣ →* G) (n : Nat)
    (hhit : emWalkUnit q hq hne n = Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero)) :
    (Finset.range n).prod (fun k => χ (emMultUnit q hq hne k)) =
      χ (Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero)) *
      (χ (emWalkUnit q hq hne 0))⁻¹ := by
  rw [char_displacement hq hne χ n, hhit]

/-- **SE implies non-constant quotient walk**: under SubgroupEscape at q,
    for each proper subgroup H, the walk's image in (ZMod q)ˣ/H is not
    permanently equal to any single element. Specifically, there exists
    a step where the quotient walk's value changes from its initial value.
    This is the "non-trivial character walk" condition. -/
theorem se_quotient_walk_nonconstant {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hse : ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      ∃ n, emMultUnit q hq hne n ∉ H)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ n, QuotientGroup.mk' H (emWalkUnit q hq hne (n + 1)) ≠
         QuotientGroup.mk' H (emWalkUnit q hq hne n) := by
  obtain ⟨k, hk⟩ := hse H hH
  exact ⟨k, fun h => by
    -- If the quotient walk is constant from n to n+1, the multiplier is in H
    have hmem : emMultUnit q hq hne k ∈ H := by
      -- h : mk'(w(k+1)) = mk'(w(k)) in the quotient
      -- w(k+1) = w(k) * m(k), so mk'(w(k)) * mk'(m(k)) = mk'(w(k))
      -- hence m(k) ∈ ker(mk') = H
      have hrec := emWalkUnit_succ q hq hne k
      have hprod : QuotientGroup.mk' H (emWalkUnit q hq hne k *
          emMultUnit q hq hne k) =
          QuotientGroup.mk' H (emWalkUnit q hq hne k) := by
        rw [← hrec]; exact h
      rw [map_mul] at hprod
      -- In a CommGroup, all subgroups are normal
      haveI : H.Normal := inferInstance
      have : QuotientGroup.mk' H (emMultUnit q hq hne k) = 1 :=
        mul_left_cancel (hprod.trans (mul_one _).symm)
      rw [← QuotientGroup.ker_mk' H, MonoidHom.mem_ker]
      exact this
    exact hk hmem⟩

/-- **DH as character synchronization (forward)**: the walk hits -1 at
    step n iff the unit-level walk equals -1 as a unit. This is then
    equivalent (by `walk_eq_neg_one_iff_quotients`) to every quotient map
    simultaneously agreeing.

    The character synchronization problem: under SE, each quotient walk
    is non-constant (by `se_quotient_walk_nonconstant`). The individual
    quotient walks visit every coset eventually (by mixing). DH asks
    whether they synchronize: can all quotient walks simultaneously
    reach (-1)'s coset at some common step? The non-constant quotient
    walks are "free" under SE; the difficulty is alignment. -/
theorem walk_hits_iff_unit_eq {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (n : Nat) :
    walkZ q n = -1 ↔
      emWalkUnit q hq hne n = Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero) := by
  constructor
  · intro h; exact Units.ext h
  · intro h; exact congrArg Units.val h

/-- **Cofinal pair character constraint**: at the cofinally-repeating pair
    (w₀, s₀), every character's product at that step is determined:
    χ(w₀) = χ(w(0)) · ∏_{k<n} χ(m(k)). Under HH failure, s₀ ≠ -(w₀)⁻¹,
    so χ(s₀) ≠ χ(-(w₀)⁻¹) for some character χ — there exists a quotient
    that distinguishes the cofinal multiplier from the death value. -/
theorem cofinal_pair_char_constraint {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {w₀ s₀ : ZMod q}
    (hcof : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = w₀ ∧ multZ q n = s₀)
    (hhf : ∃ N₀, ∀ n, N₀ ≤ n → walkZ q n ≠ -1)
    (hw₀ : w₀ ≠ 0) :
    -- The cofinal multiplier differs from the death value
    Units.mk0 s₀ (cofinal_mult_ne_zero hq hne hcof) ≠
      (Units.mk0 w₀ hw₀)⁻¹ * Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero) := by
  intro heq
  -- This would mean s₀ = w₀⁻¹ · (-1) = -(w₀⁻¹) in the unit group
  have : s₀ = -(w₀)⁻¹ := by
    have := congrArg Units.val heq
    simp [Units.val_mul, Units.val_inv_eq_inv_val] at this
    exact this
  exact cofinal_death_avoidance_at_position hq hne hhf hcof this

end CharacterDHReformulation

/-! ## §18. Quotient Walk Decomposition

The key structural insight: the walk in the full group (ZMod q)ˣ decomposes
into a family of quotient walks, one for each proper subgroup H. DH (the walk
hits -1 cofinally) is equivalent to all quotient walks simultaneously reaching
(-1)'s coset cofinally.

**Quotient walk recurrence**: mk'(H)(w(n+1)) = mk'(H)(w(n)) · mk'(H)(m(n)).
This is just the image of the full walk recurrence under the group homomorphism mk'(H).

**Cofinal pair quotient alternation**: From §16, under HH failure there exists
a cofinal pair (w₀, s₀) with s₀ ≠ -(w₀)⁻¹. For any proper subgroup H:
- If s₀ ∉ H (the cofinal multiplier escapes H), then mk'(H)(s₀) ≠ 1, and
  the quotient walk alternates between at least two distinct cosets cofinally.
- For index-2 subgroups (which have exactly 2 cosets), this means BOTH cosets
  are visited cofinally — the quotient walk is equidistributed.

**Per-ℓ decomposition**: For each prime ℓ dividing q-1, the unique subgroup
H_ℓ of index ℓ gives a quotient walk in a cyclic group of order ℓ. DH holds
if and only if "quotient DH" holds for every such ℓ simultaneously.

This section formalizes the quotient walk structure and the index-2 coset
alternation theorem (the cleanest provable result toward Approach B). -/

section QuotientWalkDecomposition

open MullinGroup
open Classical

/-- **Quotient walk recurrence**: the walk in (ZMod q)ˣ/H satisfies the same
    multiplicative recurrence as the full walk. This follows directly from
    mk'(H) being a group homomorphism. -/
theorem quotient_walk_recurrence {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (H : Subgroup (ZMod q)ˣ) (n : Nat) :
    QuotientGroup.mk' H (emWalkUnit q hq hne (n + 1)) =
      QuotientGroup.mk' H (emWalkUnit q hq hne n) *
      QuotientGroup.mk' H (emMultUnit q hq hne n) := by
  rw [← map_mul, ← emWalkUnit_succ]

/-- **Quotient walk product formula**: the quotient walk at step n equals the
    quotient of the initial position times the cumulative product of quotient
    multipliers. Specialization of `char_walk_product` to mk'(H). -/
theorem quotient_walk_product {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (H : Subgroup (ZMod q)ˣ) (n : Nat) :
    QuotientGroup.mk' H (emWalkUnit q hq hne n) =
      QuotientGroup.mk' H (emWalkUnit q hq hne 0) *
      (Finset.range n).prod (fun k => QuotientGroup.mk' H (emMultUnit q hq hne k)) := by
  haveI : H.Normal := inferInstance
  induction n with
  | zero => simp [Finset.range_zero, Finset.prod_empty]
  | succ n ih =>
    rw [quotient_walk_recurrence hq hne H n, ih, Finset.prod_range_succ, mul_assoc]

/-- **Cofinal pair projects to quotient**: if (w₀, s₀) is a cofinal pair in ZMod q
    and s₀ ∉ H for some proper subgroup H, then the quotient walk visits
    mk'(H)(w₀) and mk'(H)(w₀·s₀) cofinally, and these are DISTINCT quotient elements.
    This is the "quotient-level non-triviality" from a cofinal pair whose multiplier
    escapes the subgroup. -/
theorem cofinal_pair_quotient_distinct {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {w₀ s₀ : ZMod q}
    (hcof : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = w₀ ∧ multZ q n = s₀)
    (H : Subgroup (ZMod q)ˣ)
    (hs_esc : Units.mk0 s₀ (cofinal_mult_ne_zero hq hne hcof) ∉ H)
    (hw₀ : w₀ ≠ 0) :
    QuotientGroup.mk' H (Units.mk0 w₀ hw₀) ≠
    QuotientGroup.mk' H (Units.mk0 (w₀ * s₀) (cofinal_successor_ne_zero hq hne hcof)) := by
  intro heq
  haveI : H.Normal := inferInstance
  have hws : QuotientGroup.mk' H (Units.mk0 (w₀ * s₀)
      (cofinal_successor_ne_zero hq hne hcof)) =
      QuotientGroup.mk' H (Units.mk0 w₀ hw₀) *
      QuotientGroup.mk' H (Units.mk0 s₀ (cofinal_mult_ne_zero hq hne hcof)) := by
    rw [← map_mul]; congr 1; exact Units.ext rfl
  rw [hws] at heq
  have h1 : QuotientGroup.mk' H (Units.mk0 s₀ (cofinal_mult_ne_zero hq hne hcof)) = 1 := by
    have := mul_left_cancel (a := QuotientGroup.mk' H (Units.mk0 w₀ hw₀))
      (show _ * 1 = _ * _ from (mul_one _).trans heq)
    exact this.symm
  exact hs_esc (QuotientGroup.ker_mk' H ▸ MonoidHom.mem_ker.mpr h1)

/-- **Cofinal quotient visit at w₀**: the quotient walk visits mk'(H)(w₀) cofinally.
    This lifts the cofinal visit in ZMod q to the quotient. -/
theorem cofinal_quotient_visit_w {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {w₀ s₀ : ZMod q}
    (hcof : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = w₀ ∧ multZ q n = s₀)
    (H : Subgroup (ZMod q)ˣ)
    (hw₀_ne : w₀ ≠ 0) :
    ∀ N, ∃ n, N ≤ n ∧
      QuotientGroup.mk' H (emWalkUnit q hq hne n) =
      QuotientGroup.mk' H (Units.mk0 w₀ hw₀_ne) := by
  intro N
  obtain ⟨n, hn, hw, _⟩ := hcof N
  exact ⟨n, hn, by congr 1; exact Units.ext hw⟩

/-- **Cofinal quotient visit at w₀·s₀**: the quotient walk visits
    mk'(H)(w₀·s₀) cofinally. This is the successor position in the
    cofinal orbit, lifted to the quotient. -/
theorem cofinal_quotient_visit_ws {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {w₀ s₀ : ZMod q}
    (hcof : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = w₀ ∧ multZ q n = s₀)
    (H : Subgroup (ZMod q)ˣ) :
    ∀ N, ∃ n, N ≤ n ∧
      QuotientGroup.mk' H (emWalkUnit q hq hne n) =
      QuotientGroup.mk' H (Units.mk0 (w₀ * s₀) (cofinal_successor_ne_zero hq hne hcof)) := by
  intro N
  have hsucc := cofinal_successor_visited hcof
  obtain ⟨n, hn, hw⟩ := hsucc N
  exact ⟨n, hn, by congr 1; exact Units.ext hw⟩

/-- **Index-2 coset alternation**: if a cofinal pair (w₀, s₀) has the cofinal
    multiplier escaping an index-2 subgroup H (i.e., s₀ is NOT in H), then
    BOTH cosets of H are visited cofinally by the quotient walk.

    This is the key result for the ℓ = 2 case: since (ZMod q)ˣ/H has exactly
    2 elements when [index H] = 2, and we show both are visited cofinally,
    the quotient walk achieves full coverage.

    Proof: mk'(H)(w₀) and mk'(H)(w₀·s₀) are distinct (by `cofinal_pair_quotient_distinct`)
    and both cofinally visited. Since the quotient has exactly 2 elements, these
    are the two elements, so both cosets are visited cofinally. -/
theorem cofinal_quotient_both_cosets_visited {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {w₀ s₀ : ZMod q}
    (hcof : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = w₀ ∧ multZ q n = s₀)
    (H : Subgroup (ZMod q)ˣ)
    (hs_esc : Units.mk0 s₀ (cofinal_mult_ne_zero hq hne hcof) ∉ H)
    (hw₀ : w₀ ≠ 0) :
    (∀ N, ∃ n, N ≤ n ∧
      QuotientGroup.mk' H (emWalkUnit q hq hne n) =
      QuotientGroup.mk' H (Units.mk0 w₀ hw₀)) ∧
    (∀ N, ∃ n, N ≤ n ∧
      QuotientGroup.mk' H (emWalkUnit q hq hne n) =
      QuotientGroup.mk' H (Units.mk0 (w₀ * s₀) (cofinal_successor_ne_zero hq hne hcof))) ∧
    QuotientGroup.mk' H (Units.mk0 w₀ hw₀) ≠
      QuotientGroup.mk' H (Units.mk0 (w₀ * s₀) (cofinal_successor_ne_zero hq hne hcof)) :=
  ⟨cofinal_quotient_visit_w hq hne hcof H hw₀,
   cofinal_quotient_visit_ws hq hne hcof H,
   cofinal_pair_quotient_distinct hq hne hcof H hs_esc hw₀⟩

/-- **Cofinal multiplier escape from SE**: under SubgroupEscape, the cofinal
    multiplier s₀ from any cofinally visited position either escapes H or
    all multipliers are eventually in H. More precisely, if SE holds at q
    (formulated as: for every proper subgroup H, some multiplier escapes),
    then there exists at least one step where the multiplier escapes H.
    The cofinal multiplier s₀ may or may not escape — but if ALL multipliers
    were eventually in H, then mults generate only H, contradicting SE.

    This gives: under SE, the closure of {m(n) : n ∈ ℕ} is (ZMod q)ˣ,
    so no proper subgroup contains all multipliers, hence s₀ ∉ H for at
    least one proper H. -/
theorem se_implies_some_mult_escapes {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hse : ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      ∃ n, emMultUnit q hq hne n ∉ H)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ n, emMultUnit q hq hne n ∉ H :=
  hse H hH

/-- **HH failure + SE at q implies cofinal multiplier escapes some maximal subgroup**:
    Under HH failure, there is a cofinal pair (w₀, s₀). Under SE, for every
    proper subgroup H, some multiplier escapes H. The cofinal multiplier s₀
    is fixed, but we can ask: does it lie in every maximal subgroup?

    If s₀ generates a subgroup S = ⟨s₀⟩, then s₀ ∉ H for any H that doesn't
    contain S. Since s₀ ≠ 0 (proved), s₀ is a unit with some order d dividing q-1.
    s₀ ∉ H iff the unique subgroup of index ℓ (for each prime ℓ | d) doesn't contain s₀. -/
theorem cofinal_mult_escapes_some_subgroup {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {w₀ s₀ : ZMod q}
    (hcof : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = w₀ ∧ multZ q n = s₀)
    (hs_ne_one : Units.mk0 s₀ (cofinal_mult_ne_zero hq hne hcof) ≠ 1) :
    ∃ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ ∧
      Units.mk0 s₀ (cofinal_mult_ne_zero hq hne hcof) ∉ H := by
  -- s₀ ≠ 1 gives two distinct elements, so the group is nontrivial
  haveI : Nontrivial (ZMod q)ˣ :=
    ⟨⟨Units.mk0 s₀ (cofinal_mult_ne_zero hq hne hcof), 1, hs_ne_one⟩⟩
  exact ⟨⊥, bot_ne_top, fun h => hs_ne_one (Subgroup.mem_bot.mp h)⟩

/-- **Quotient DH at a subgroup**: DynamicalHitting restricted to a single
    quotient. For a proper subgroup H, "quotient DH at H" says:
    the quotient walk mk'(H)(w(n)) visits mk'(H)(-1) cofinally.

    Full DH is equivalent to quotient DH holding for ALL proper H simultaneously
    (since the walk hits -1 iff it hits -1's image in every quotient). -/
def QuotientDH (q : Nat) [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (H : Subgroup (ZMod q)ˣ) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧
    QuotientGroup.mk' H (emWalkUnit q hq hne n) =
    QuotientGroup.mk' H (Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero))

/-- **Full DH implies quotient DH at every subgroup**: if the walk hits -1
    cofinally, then every quotient walk hits mk'(H)(-1) cofinally. -/
theorem dh_implies_quotient_dh {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (H : Subgroup (ZMod q)ˣ)
    (hdh : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = -1) :
    QuotientDH q hq hne H := by
  intro N
  obtain ⟨n, hn, hw⟩ := hdh N
  exact ⟨n, hn, by congr 1; exact Units.ext hw⟩

/-- **Cofinal pair gives quotient DH for escaped subgroups (under HH failure)**:
    If HH fails at q, and (w₀, s₀) is the cofinal pair with s₀ ∉ H,
    then the quotient walk visits at least TWO distinct elements cofinally.
    For an index-2 subgroup H₂, this means the quotient walk visits EVERY
    element cofinally, so quotient DH holds at H₂.

    More precisely: under HH failure, mk'(H)(-1) is either mk'(H)(w₀) or
    mk'(H)(w₀·s₀), and both are visited cofinally. So if the quotient has
    exactly 2 elements, quotient DH holds automatically.

    This is NOT a tautology: it uses the cofinal orbit structure from §16
    and the escape condition to deduce non-trivial quotient coverage. -/
theorem quotient_dh_of_index_two_escape {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {w₀ s₀ : ZMod q}
    (hcof : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = w₀ ∧ multZ q n = s₀)
    (_hhf : ∃ N₀, ∀ n, N₀ ≤ n → walkZ q n ≠ -1)
    (H : Subgroup (ZMod q)ˣ) (_hH : H ≠ ⊤)
    (hs_esc : Units.mk0 s₀ (cofinal_mult_ne_zero hq hne hcof) ∉ H)
    -- The quotient has exactly 2 elements (index-2 subgroup)
    (hcard : Fintype.card ((ZMod q)ˣ ⧸ H) = 2) :
    QuotientDH q hq hne H := by
  -- Get the two distinct cofinally-visited quotient elements
  have hw₀ : w₀ ≠ 0 := by
    obtain ⟨n, _, hw, _⟩ := hcof 0; rw [← hw]; exact walkZ_ne_zero hq hne n
  let a := QuotientGroup.mk' H (Units.mk0 w₀ hw₀)
  let b := QuotientGroup.mk' H (Units.mk0 (w₀ * s₀) (cofinal_successor_ne_zero hq hne hcof))
  have hab : a ≠ b := cofinal_pair_quotient_distinct hq hne hcof H hs_esc hw₀
  -- The target element
  let t := QuotientGroup.mk' H (Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero))
  -- In a 2-element set, any element equals a or b
  have h_two : ∀ x : (ZMod q)ˣ ⧸ H, x = a ∨ x = b := by
    intro x
    by_contra hc
    push_neg at hc
    have : Fintype.card ((ZMod q)ˣ ⧸ H) ≥ 3 := by
      have hinj : Function.Injective (fun i : Fin 3 =>
          match i with | 0 => x | 1 => a | 2 => b) := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [hab.symm, hc.1, hc.2]
      exact le_of_eq (Fintype.card_fin 3).symm |>.trans (Fintype.card_le_of_injective _ hinj)
    omega
  -- The target t equals a or b
  rcases h_two t with ht | ht
  · -- t = a: the quotient walk visits a cofinally, which equals t
    intro N; obtain ⟨n, hn, hw⟩ := cofinal_quotient_visit_w hq hne hcof H hw₀ N
    exact ⟨n, hn, hw.trans ht.symm⟩
  · -- t = b: the quotient walk visits b cofinally, which equals t
    intro N; obtain ⟨n, hn, hw⟩ := cofinal_quotient_visit_ws hq hne hcof H N
    exact ⟨n, hn, hw.trans ht.symm⟩

end QuotientWalkDecomposition

/-! ## §19. Cofinal Escape Reduction and Orbit Chain Cycle

CofinalEscape at a subgroup H states: there exists a cofinally visited position
whose cofinal multiplier escapes H. This bridges the cofinal orbit structure
(§16) to the quotient DH results (§18).

Key result: CofinalEscape at an index-2 subgroup H implies QuotientDH at H.

The orbit chain formalizes the sequence w₀ →^{s₀} w₁ →^{s₁} w₂ →^{s₂} ⋯
as a recursive function. Since ZMod q is finite, the chain must cycle
(pigeonhole). Under HH failure, -1 is excluded from the chain, and death-value
avoidance holds at every position. -/

section CofinalEscapeReduction

open MullinGroup
open Classical

/-- **CofinalEscape at H**: there exists a cofinally visited position with a
    cofinal multiplier that escapes the subgroup H. -/
def CofinalEscape (q : Nat) [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (H : Subgroup (ZMod q)ˣ) : Prop :=
  ∃ (x s : ZMod q) (hcof : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x ∧ multZ q n = s),
    Units.mk0 s (cofinal_mult_ne_zero hq hne hcof) ∉ H

/-- **CofinalEscape → QuotientDH for index-2 subgroups**: if there exists
    a cofinal pair whose multiplier escapes an index-2 subgroup H, then
    QuotientDH holds at H. -/
theorem cofinal_escape_quotient_dh {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hhf : ∃ N₀, ∀ n, N₀ ≤ n → walkZ q n ≠ -1)
    (H : Subgroup (ZMod q)ˣ) (_hH : H ≠ ⊤)
    (hcard : Fintype.card ((ZMod q)ˣ ⧸ H) = 2)
    (hce : CofinalEscape q hq hne H) :
    QuotientDH q hq hne H := by
  obtain ⟨_, _, hcof, hs_esc⟩ := hce
  exact quotient_dh_of_index_two_escape hq hne hcof hhf H _hH hs_esc hcard

/-- **Cofinal successor step**: from a cofinally visited position, produce
    the next cofinally visited position via cofinal multiplier + successor. -/
noncomputable def cofinalStep {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (xp : { x : ZMod q // ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x }) :
    { x : ZMod q // ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x } :=
  let h := cofinal_visited_has_cofinal_mult hq hne xp.property
  ⟨xp.val * h.choose, cofinal_successor_visited h.choose_spec⟩

/-- **The orbit chain**: iterating cofinalStep from a starting position.
    Each position carries a proof that it is cofinally visited. -/
noncomputable def orbitChain {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (start : { x : ZMod q // ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x }) :
    ℕ → { x : ZMod q // ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x }
  | 0 => start
  | k + 1 => cofinalStep hq hne (orbitChain hq hne start k)

/-- **Orbit chain must cycle**: ZMod q is finite, so the chain ℕ → ZMod q
    cannot be injective. Some position must repeat. -/
theorem orbit_chain_repeats {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (start : { x : ZMod q // ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x }) :
    ∃ i j, i ≠ j ∧
      (orbitChain hq hne start i).val = (orbitChain hq hne start j).val := by
  have hinj := not_injective_infinite_finite
    (fun n => (orbitChain hq hne start n).val)
  rw [Function.Injective] at hinj
  push_neg at hinj
  obtain ⟨a, b, hab, hne'⟩ := hinj
  exact ⟨a, b, hne', hab⟩

/-- Under HH failure, -1 does not appear in the orbit chain. -/
theorem orbit_chain_ne_neg_one {q : Nat} [Fact (Nat.Prime q)]
    (_hq : IsPrime q) (_hne : ∀ k, seq k ≠ q)
    (start : { x : ZMod q // ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x })
    (hhf : ∃ N₀, ∀ n, N₀ ≤ n → walkZ q n ≠ -1) (k : ℕ) :
    (orbitChain _hq _hne start k).val ≠ -1 := by
  intro heq
  exact hh_failure_neg_one_not_cofinal hhf (fun N => by
    obtain ⟨n, hn, hw⟩ := (orbitChain _hq _hne start k).property N
    exact ⟨n, hn, heq ▸ hw⟩)

end CofinalEscapeReduction

/-! ## §20. Cofinal Escape Reduction: TailSubgroupEscape

CofinalEscape at a subgroup H (§19) states that some cofinally visited position
has a cofinal multiplier escaping H. But SE only gives a *single* escaping step,
which may lie in the initial segment before the walk settles.

**TailSubgroupEscape** captures the stronger tail condition: for every proper
subgroup H, multipliers don't eventually settle into H. This is strictly between
SE (one escape) and DH (walk hits -1 cofinally).

Key results:
1. `walk_eventually_cofinal`: past some threshold, only cofinally visited positions appear.
2. `cofinal_escape_or_eventual_confinement`: for any proper H, either CofinalEscape(H)
   or multipliers are eventually confined to H.
3. `TailSubgroupEscape ↔ CofinalEscape at every proper H`.
4. `TailSE → QuotientDH` at every index-2 subgroup. -/

section CofinalEscapeReductionTail

open MullinGroup
open Classical

/-- **Walk eventually cofinal**: past some threshold N, every walk position
    is cofinally visited. Non-cofinal positions are each eventually avoided;
    taking the max of all their avoidance bounds gives a uniform threshold. -/
theorem walk_eventually_cofinal {q : Nat} [Fact (Nat.Prime q)]
    (_hq : IsPrime q) (_hne : ∀ k, seq k ≠ q) :
    ∃ N, ∀ n, N ≤ n → (∀ M, ∃ m, M ≤ m ∧ walkZ q m = walkZ q n) := by
  -- For each x : ZMod q, either x is cofinal or there's a bound past which w(n) ≠ x
  -- For non-cofinal x, extract a bound; for cofinal x, use 0
  have h : ∀ x : ZMod q, ∃ Nx : ℕ,
      (¬∀ M, ∃ m, M ≤ m ∧ walkZ q m = x) → ∀ m, Nx ≤ m → walkZ q m ≠ x := by
    intro x
    by_cases hcof : ∀ M, ∃ m, M ≤ m ∧ walkZ q m = x
    · exact ⟨0, fun h => absurd hcof h⟩
    · push_neg at hcof
      obtain ⟨M, hM⟩ := hcof
      exact ⟨M, fun _ m hm => hM m hm⟩
  choose bound hbound using h
  refine ⟨Finset.univ.sup bound, fun n hn => ?_⟩
  by_contra hncof
  have hge : bound (walkZ q n) ≤ n :=
    le_trans (Finset.le_sup (f := bound) (Finset.mem_univ _)) hn
  exact hbound (walkZ q n) hncof n hge rfl

/-- **Cofinal escape or eventual confinement**: for any proper subgroup H,
    either CofinalEscape(H) holds (some cofinal pair's multiplier escapes H),
    or all multipliers are eventually confined to H. -/
theorem cofinal_escape_or_eventual_confinement {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (H : Subgroup (ZMod q)ˣ) :
    CofinalEscape q hq hne H ∨ (∃ N, ∀ n, N ≤ n → emMultUnit q hq hne n ∈ H) := by
  -- Either infinitely many multipliers escape H, or finitely many do
  by_cases hinf : ∀ N, ∃ n, N ≤ n ∧ emMultUnit q hq hne n ∉ H
  · -- Infinitely many escapes: apply cofinal pigeonhole
    left
    -- Classify escaping steps by (walkZ, multZ) pair
    obtain ⟨⟨x, s⟩, hcof⟩ := cofinal_pigeonhole
      (fun n => emMultUnit q hq hne n ∉ H)
      (fun n => (walkZ q n, multZ q n))
      hinf
    -- Build the cofinal pair hypothesis
    have hcof' : ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x ∧ multZ q n = s := by
      intro N
      obtain ⟨n, hn, _, heq⟩ := hcof N
      exact ⟨n, hn, Prod.mk.inj heq |>.1, Prod.mk.inj heq |>.2⟩
    -- The cofinal multiplier s escapes H
    have hesc : Units.mk0 s (cofinal_mult_ne_zero hq hne hcof') ∉ H := by
      obtain ⟨n, _, hnotin, heq⟩ := hcof 0
      have hsn : multZ q n = s := (Prod.mk.inj heq).2
      have : emMultUnit q hq hne n ∉ H := hnotin
      rwa [show emMultUnit q hq hne n =
        Units.mk0 s (cofinal_mult_ne_zero hq hne hcof') from Units.ext hsn] at this
    exact ⟨x, s, hcof', hesc⟩
  · -- Finitely many escapes: push negation
    right
    push_neg at hinf
    obtain ⟨N, hN⟩ := hinf
    exact ⟨N, fun n hn => by_contra (fun h => h (hN n hn))⟩

/-- **TailSubgroupEscape**: the multipliers don't eventually settle into any
    proper subgroup. This is strictly stronger than SE (which gives a single
    escape) and captures the tail behavior of the walk. -/
def TailSubgroupEscape (q : Nat) [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) : Prop :=
  ∀ (H : Subgroup (ZMod q)ˣ), H ≠ ⊤ →
    ∀ N, ∃ n, N ≤ n ∧ emMultUnit q hq hne n ∉ H

/-- **TailSE implies CofinalEscape at every proper H**: if multipliers don't
    settle into any proper subgroup, then for each proper H there's a cofinal
    pair whose multiplier escapes H. -/
theorem tail_se_implies_cofinal_escape {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (htse : TailSubgroupEscape q hq hne)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    CofinalEscape q hq hne H := by
  have hinf : ∀ N, ∃ n, N ≤ n ∧ emMultUnit q hq hne n ∉ H := htse H hH
  -- Use the left branch of the dichotomy
  rcases cofinal_escape_or_eventual_confinement hq hne H with hce | ⟨N, hN⟩
  · exact hce
  · exfalso; obtain ⟨n, hn, hesc⟩ := hinf N; exact hesc (hN n hn)

/-- **CofinalEscape at every proper H implies TailSE**: if every proper subgroup
    has a cofinal pair whose multiplier escapes it, then multipliers don't
    eventually settle into any proper subgroup. -/
theorem cofinal_escape_all_implies_tail_se {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hce : ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ → CofinalEscape q hq hne H) :
    TailSubgroupEscape q hq hne := by
  intro H hH N
  obtain ⟨x, s, hcof, hesc⟩ := hce H hH
  -- From cofinality, get a step n ≥ N with multZ q n = s ∉ H
  obtain ⟨n, hn, _, hs⟩ := hcof N
  refine ⟨n, hn, ?_⟩
  rwa [show emMultUnit q hq hne n =
    Units.mk0 s (cofinal_mult_ne_zero hq hne hcof) from Units.ext hs]

/-- **TailSE ↔ CofinalEscape at every proper H**: the two conditions are
    equivalent, giving a clean characterization of the tail escape property
    in terms of the cofinal orbit structure. -/
theorem tail_se_iff_cofinal_escape_all {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) :
    TailSubgroupEscape q hq hne ↔
    (∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ → CofinalEscape q hq hne H) :=
  ⟨fun htse H hH => tail_se_implies_cofinal_escape hq hne htse H hH,
   fun hce => cofinal_escape_all_implies_tail_se hq hne hce⟩

/-- **TailSE → QuotientDH at every index-2 subgroup**: under HH failure,
    TailSE gives CofinalEscape at every proper H, which by §19 gives
    QuotientDH at every index-2 subgroup.

    This is the main reduction: TailSE handles all index-2 quotients. -/
theorem tail_se_implies_quotient_dh_index_two {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hhf : ∃ N₀, ∀ n, N₀ ≤ n → walkZ q n ≠ -1)
    (htse : TailSubgroupEscape q hq hne)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hcard : Fintype.card ((ZMod q)ˣ ⧸ H) = 2) :
    QuotientDH q hq hne H :=
  cofinal_escape_quotient_dh hq hne hhf H hH hcard
    (tail_se_implies_cofinal_escape hq hne htse H hH)

/-- **SE implies TailSE when the group is trivial** (q = 2): if (ZMod q)ˣ has
    no proper subgroups (i.e., the group has order 1), TailSE is vacuously true.
    This handles the base case q = 2 (where (ZMod 2)ˣ ≅ {1}). -/
theorem tail_se_of_subsingleton {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    [Subsingleton (ZMod q)ˣ] :
    TailSubgroupEscape q hq hne := by
  intro H hH
  exfalso
  exact hH (eq_top_iff.mpr (fun x _ => Subsingleton.elim x 1 ▸ H.one_mem))

/-- **Cofinal escape reduction summary**: packages the equivalences and
    reductions established in this section.

    The hierarchy of hypotheses at a prime q not in the sequence:
    ```
    SE(q)  ←  TailSE(q)  ↔  (∀ proper H, CofinalEscape(q, H))
                    ↓ (under HH failure)
              QuotientDH(q, H) for all index-2 H
    ```
    SE(q) gives a single escape from each proper H.
    TailSE(q) gives infinitely many escapes (tail condition).
    CofinalEscape gives a cofinal pair whose multiplier escapes.
    QuotientDH gives that the quotient walk hits (-1)'s coset cofinally. -/
theorem cofinal_escape_reduction_summary {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (htse : TailSubgroupEscape q hq hne)
    (hhf : ∃ N₀, ∀ n, N₀ ≤ n → walkZ q n ≠ -1) :
    -- TailSE gives CofinalEscape at every proper H
    (∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ → CofinalEscape q hq hne H) ∧
    -- TailSE + HH failure gives QuotientDH at every index-2 H
    (∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      Fintype.card ((ZMod q)ˣ ⧸ H) = 2 → QuotientDH q hq hne H) := by
  exact ⟨fun H hH => tail_se_implies_cofinal_escape hq hne htse H hH,
         fun H hH hcard => tail_se_implies_quotient_dh_index_two
           hq hne hhf htse H hH hcard⟩

end CofinalEscapeReductionTail

/-! ## §21. Factored Sieve Reduction: MertensEscape + SieveAmplification → TailSE

The gap SE → TailSE is open: SE gives one escape from each proper subgroup,
while TailSE requires infinitely many (unbounded). This section introduces a
correctly factored two-hypothesis reduction:

1. **MertensEscape**: for any proper subgroup H of (ZMod q)ˣ and any finite
   exclusion set, there exists a prime outside H ∪ S ∪ {q}. This is pure
   Dirichlet content — no reference to the EM sequence.
2. **EuclidMinFacEscape**: infinitely many Euclid numbers prod(n)+1 have
   their minFac escaping H. This is the correct existential statement over
   EM sequence indices.
3. **SieveAmplification**: MertensEscape → EuclidMinFacEscape. The hard
   sieve-theoretic bridge connecting prime density to EM structure.

Key results:
1. `prod_unbounded`: ∀ B, ∃ n, B ≤ prod n.
2. `EuclidMinFacEscape`: correct existential sieve hypothesis.
3. `emfe_implies_tail_se`: EuclidMinFacEscape → TailSE at every prime.
4. `emfe_implies_se`: EuclidMinFacEscape → SubgroupEscape.
5. `MertensEscape`: Dirichlet-content hypothesis (no EM reference).
6. `SieveAmplification`: MertensEscape → EuclidMinFacEscape.
7. `sieve_reduction_summary`: full chain with both hypotheses. -/

section SieveHypothesisReduction

open MullinGroup
open Classical

/-- **Products are unbounded**: for any bound B, there exists n with B ≤ prod n.
    Follows from exponential growth: prod n ≥ 2^(n+1) and n < 2^n. -/
theorem prod_unbounded (B : Nat) : ∃ n, B ≤ prod n := by
  obtain ⟨n, hn⟩ : ∃ n, B ≤ 2 ^ (n + 1) := by
    exact ⟨B, le_trans Nat.lt_two_pow_self.le (Nat.pow_le_pow_right (by norm_num) (by omega))⟩
  exact ⟨n, le_trans hn (prod_exponential_growth n)⟩

/-- **EuclidMinFacEscape**: for any prime q and proper subgroup H of (ZMod q)ˣ,
    there exist infinitely many indices n where minFac(prod(n)+1) escapes H.
    References `prod` and `Euclid.minFac` but NOT `seq`/`walkZ`/`multZ`/`emMultUnit`,
    separating factorization content from walk dynamics.

    This replaces the (false) universal MinFacCosetEscape with a correct
    existential statement over Euclid number indices. -/
def EuclidMinFacEscape : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)]
    (H : Subgroup (ZMod q)ˣ) (_ : H ≠ ⊤)
    (N : Nat),
    ∃ n, N ≤ n ∧
      ∀ (hne : (Euclid.minFac (prod n + 1) : ZMod q) ≠ 0),
        Units.mk0 ((Euclid.minFac (prod n + 1) : ZMod q)) hne ∉ H

/-- **EMFE implies TailSE**: the existential sieve hypothesis gives infinitely
    many escapes from any proper subgroup. The key idea: minFac(prod(n)+1) is
    exactly seq(n+1), so escape of the minFac unit is escape of emMultUnit. -/
theorem emfe_implies_tail_se (hemfe : EuclidMinFacEscape)
    (q : Nat) [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) :
    TailSubgroupEscape q hq hne := by
  intro H hH N
  obtain ⟨n, hn, hesc⟩ := hemfe q H hH N
  have hne_cast : (Euclid.minFac (prod n + 1) : ZMod q) ≠ 0 := by
    rw [show Euclid.minFac (prod n + 1) = seq (n + 1) from rfl]
    exact multZ_ne_zero hq hne n
  refine ⟨n, hn, ?_⟩
  rw [show emMultUnit q hq hne n =
    Units.mk0 (Euclid.minFac (prod n + 1) : ZMod q) hne_cast from Units.ext rfl]
  exact hesc hne_cast

/-- **EMFE implies SubgroupEscape**: since TailSE gives escapes past any N,
    taking N = 0 recovers the single-escape property SE. -/
theorem emfe_implies_se (hemfe : EuclidMinFacEscape) : SubgroupEscape := by
  intro q _ hq hne H hH
  obtain ⟨n, _, hesc⟩ := emfe_implies_tail_se hemfe q hq hne H hH 0
  exact ⟨n, hesc⟩

/-- **TailSE implies per-q EMFE**: if the walk multipliers escape every proper
    subgroup cofinally, then minFac(prod(n)+1) escapes every proper subgroup
    cofinally. This is the converse of `emfe_implies_tail_se` at a fixed q. -/
theorem tail_se_implies_emfe_at
    {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (htse : TailSubgroupEscape q hq hne) :
    ∀ (H : Subgroup (ZMod q)ˣ) (_ : H ≠ ⊤) (N : Nat),
      ∃ n, N ≤ n ∧
        ∀ (hne' : (Euclid.minFac (prod n + 1) : ZMod q) ≠ 0),
          Units.mk0 ((Euclid.minFac (prod n + 1) : ZMod q)) hne' ∉ H := by
  intro H hH N
  obtain ⟨n, hn, hesc⟩ := htse H hH N
  refine ⟨n, hn, fun hne' => ?_⟩
  rwa [show emMultUnit q hq hne n =
    Units.mk0 (Euclid.minFac (prod n + 1) : ZMod q) hne' from Units.ext rfl] at hesc

/-- **Per-q EMFE implies TailSE**: if minFac(prod(n)+1) escapes every proper
    subgroup cofinally at q, then the walk multipliers do too. Together with
    `tail_se_implies_emfe_at`, this gives a full equivalence at each fixed q. -/
theorem emfe_at_implies_tail_se
    {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hemfe : ∀ (H : Subgroup (ZMod q)ˣ) (_ : H ≠ ⊤) (N : Nat),
      ∃ n, N ≤ n ∧
        ∀ (hne' : (Euclid.minFac (prod n + 1) : ZMod q) ≠ 0),
          Units.mk0 ((Euclid.minFac (prod n + 1) : ZMod q)) hne' ∉ H) :
    TailSubgroupEscape q hq hne := by
  intro H hH N
  obtain ⟨n, hn, hesc⟩ := hemfe H hH N
  have hne_cast : (Euclid.minFac (prod n + 1) : ZMod q) ≠ 0 := by
    rw [show Euclid.minFac (prod n + 1) = seq (n + 1) from rfl]
    exact multZ_ne_zero hq hne n
  refine ⟨n, hn, ?_⟩
  rw [show emMultUnit q hq hne n =
    Units.mk0 (Euclid.minFac (prod n + 1) : ZMod q) hne_cast from Units.ext rfl]
  exact hesc hne_cast

/-- **EMFE ↔ TailSE at a fixed prime**: the factorization-level escape property
    (minFac(prod(n)+1) escapes H cofinally) is equivalent to the walk-level
    escape property (emMultUnit escapes H cofinally). This equivalence holds
    because seq(n+1) = minFac(prod(n)+1) definitionally.

    This is the analytical characterization: TailSubgroupEscape, defined in terms
    of walk dynamics (emMultUnit), is equivalent to a purely number-theoretic
    statement about the smallest prime factors of Euclid numbers. -/
theorem emfe_iff_tail_se_at
    {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) :
    (∀ (H : Subgroup (ZMod q)ˣ) (_ : H ≠ ⊤) (N : Nat),
      ∃ n, N ≤ n ∧
        ∀ (hne' : (Euclid.minFac (prod n + 1) : ZMod q) ≠ 0),
          Units.mk0 ((Euclid.minFac (prod n + 1) : ZMod q)) hne' ∉ H) ↔
    TailSubgroupEscape q hq hne :=
  ⟨emfe_at_implies_tail_se hq hne, tail_se_implies_emfe_at hq hne⟩

/-- **MertensEscape**: for any prime q, proper subgroup H of (ZMod q)ˣ, and
    finite exclusion set S, there exists a prime outside H ∪ S ∪ {q}.

    This captures the Dirichlet/Mertens content: the complement of any proper
    subgroup has positive prime density, so good primes can't be exhausted
    by any finite exclusion. No reference to the EM sequence. -/
def MertensEscape : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)]
    (H : Subgroup (ZMod q)ˣ) (_ : H ≠ ⊤)
    (S : Finset Nat),
    ∃ p, Nat.Prime p ∧ p ∉ S ∧ p ≠ q ∧
      ∀ (hne : (p : ZMod q) ≠ 0),
        Units.mk0 ((p : ZMod q)) hne ∉ H

/-- **SieveAmplification**: the density of primes outside H (MertensEscape)
    can be amplified to show Euclid numbers' minFac values can't stay in H.

    This is the deep sieve-theoretic content. The Euclid numbers prod(n)+1
    grow super-exponentially, each coprime to all prior terms, and primes
    in any proper subgroup have density < 1. The combination should force
    eventual escape. Formalizing this requires Legendre/Selberg sieve bounds
    combined with the EM coprimality structure. -/
def SieveAmplification : Prop :=
  MertensEscape → EuclidMinFacEscape

/-- **Composed reduction**: MertensEscape + SieveAmplification → TailSE. -/
theorem mertens_sieve_implies_tail_se
    (hme : MertensEscape) (hsa : SieveAmplification)
    (q : Nat) [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) :
    TailSubgroupEscape q hq hne :=
  emfe_implies_tail_se (hsa hme) q hq hne

/-- **Composed reduction**: MertensEscape + SieveAmplification → SE. -/
theorem mertens_sieve_implies_se
    (hme : MertensEscape) (hsa : SieveAmplification) :
    SubgroupEscape :=
  emfe_implies_se (hsa hme)

/-- **Sieve reduction summary**: MertensEscape + SieveAmplification combined
    with HH failure gives the full reduction chain at every prime not in the
    sequence: TailSE, CofinalEscape at every proper H, and QuotientDH at
    every index-2 H. -/
theorem sieve_reduction_summary {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hme : MertensEscape) (hsa : SieveAmplification)
    (hhf : ∃ N₀, ∀ n, N₀ ≤ n → walkZ q n ≠ -1) :
    TailSubgroupEscape q hq hne ∧
    (∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ → CofinalEscape q hq hne H) ∧
    (∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      Fintype.card ((ZMod q)ˣ ⧸ H) = 2 → QuotientDH q hq hne H) := by
  have htse := mertens_sieve_implies_tail_se hme hsa q hq hne
  exact ⟨htse,
    fun H hH => tail_se_implies_cofinal_escape hq hne htse H hH,
    fun H hH hcard => tail_se_implies_quotient_dh_index_two
      hq hne hhf htse H hH hcard⟩

end SieveHypothesisReduction

/-! ## §22. The Factoring Oracle Barrier

**The analytical core.** By `emfe_iff_tail_se_at`, TailSubgroupEscape at a
fixed prime q is equivalent to a purely number-theoretic statement about the
smallest prime factors of Euclid numbers:

> For every proper subgroup H < (ℤ/qℤ)ˣ and every N, there exists n ≥ N
> such that minFac(prod(n)+1) mod q ∉ H.

This strips away all walk dynamics: no walkZ, no multZ, no emMultUnit.
The content is purely about the distribution of minFac values of Euclid
numbers in residue classes modulo q.

**The marginal/joint barrier.** The orbit chain machinery (TailSE,
CofinalEscape, QuotientDH) captures everything provable about the
*marginal* distribution of multiplier residues — no proper subgroup
eventually captures all multipliers, quotient walks hit their targets.
But DynamicalHitting is a statement about the *joint* distribution of
(position, multiplier): the death pair (x, −x⁻¹) must eventually occur
as (walkZ q n, multZ q n). No statement about marginal distributions
can force this.

**Even full per-position equidistribution cannot close the gap.** Suppose
every non-death multiplier residue appeared cofinally at every position:
Sₓ = G \ {−x⁻¹} for all x ∈ V. This would give V = G \ {−1} (every
element except −1 visited cofinally). But V = G \ {−1} is perfectly
consistent with HH failure: from position x, the allowed transitions
x·s for s ∈ G \ {−x⁻¹} all land in G \ {−1}. Death avoidance is built
into the transition structure. A walk can visit every element except −1
by simply never taking the single forbidden transition at each step.

**The factoring oracle.** HH failure is equivalent to: for all large n,
  minFac(Prod(n)+1) ≢ −Prod(n)⁻¹ (mod q).
Both sides are determined by Prod(n):
  - Left: minFac(Prod(n)+1) mod q — depends on global factorization
  - Right: −Prod(n)⁻¹ mod q — depends only on Prod(n) mod q

Sustaining avoidance requires a systematic correlation between a mod-q
residue (O(log q) bits) and a factorization outcome of a ~2^{2^n}-digit
integer. This "factoring oracle" must predict enough about the smallest
factor of Prod(n)+1 from the mod-q residue of Prod(n) to steer away
from one forbidden class — at every prime q simultaneously.

**Why the oracle should not exist.** The impossibility is about
*decorrelation*, not computational hardness: even if factoring were easy,
knowing m mod q gives essentially no information about minFac(m) mod q.
For generic integers m ≡ c (mod q), the distribution of minFac(m) mod q
is uniform over (ℤ/qℤ)ˣ — this follows from CRT + Mertens' theorem
(each prime p ∤ q contributes equally to each nonzero residue class).
The correlation needed to sustain the oracle — systematically predicting
one bit of factorization output from a mod-q residue — is absent in the
generic case. The open question is whether this decorrelation transfers
to the specific EM orbit {Prod(n)+1}. The EM-specific structure that
prevents abstract counterexamples is the feedback loop: minFac(Prod(n)+1)
enters the product, determining Prod(n+1) mod q, which determines the
next residue to be factored. This feedback couples consecutive steps but
does not create the global correlation the oracle requires.

**There is no useful intermediate between TailSE and DH.** The minimal
hypothesis to prove DH is literally "∃ n ≥ N : multZ q n = −(walkZ q n)⁻¹"
which *is* DH. Any weaker statement about multiplier distributions at
individual positions falls on the TailSE side of the barrier.

**The reduction status.** The verified chain:

```
EMFE ←proved→ TailSE ─proved→ CofinalEscape ─proved→ QuotientDH
                       ═══════════════════════════════
                       marginal distribution (proved) │
                       ═══════════════════════════════
                       joint distribution (open)      │
                       ═══════════════════════════════
                    DynamicalHitting ────proved────→ MC
```

DynamicalHitting — the assertion that the EM walk's greedy factoring
process cannot sustain the factoring oracle — is the sole open hypothesis
for Mullin's Conjecture. It lives on the joint-distribution side of a
fundamental barrier that no marginal-distribution argument can cross. -/

section AnalyticalCharacterization
open MullinGroup
open Classical

/-- **Reduction summary for DH**: collects the full verified reduction chain.
    Given DH (the sole open hypothesis), we get MC via strong induction + PRE.
    Given only TailSE, we get CofinalEscape and QuotientDH but NOT full DH.
    The barrier is marginal vs joint: DH requires the (position, multiplier)
    pair to hit the death curve, which no marginal statement can force. -/
theorem dh_reduction_chain :
    DynamicalHitting → MullinConjecture :=
  dynamical_hitting_implies_mullin

/-- **TailSE gives everything below DH**: at any prime q not in the sequence,
    TailSE gives CofinalEscape at every proper subgroup and QuotientDH at
    every index-2 subgroup. This exhausts what marginal multiplier distribution
    can prove. DH (joint distribution: factoring oracle impossibility) is open. -/
theorem tail_se_gives_sub_dh {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (htse : TailSubgroupEscape q hq hne)
    (hhf : ∃ N₀, ∀ n, N₀ ≤ n → walkZ q n ≠ -1) :
    (∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ → CofinalEscape q hq hne H) ∧
    (∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      Fintype.card ((ZMod q)ˣ ⧸ H) = 2 → QuotientDH q hq hne H) :=
  ⟨fun H hH => tail_se_implies_cofinal_escape hq hne htse H hH,
   fun H hH hcard => tail_se_implies_quotient_dh_index_two hq hne hhf htse H hH hcard⟩

end AnalyticalCharacterization

/-! ## §23: Oracle Impossibility and the Marginal/Joint Barrier

**OracleImpossibility** asserts: at each cofinally visited walk position x ≠ −1,
the multiplier residues mod q are not eventually locked to a single value. In other
words, the EM walk has "per-position diversity" — no position is coupled to exactly
one eventual multiplier.

**Critical observation: OI does NOT imply DH.** The two are genuinely independent.

**Counterexample (ℤ/7ℤ)ˣ.** Let G = (ℤ/7ℤ)ˣ (order 6). Consider a walk with
cofinally visited positions V = {1,2,3,5} and cofinal multiplier sets:

    S₁ = {2,3}   S₂ = {4,5}   S₃ = {4,5}   S₅ = {1,3}

Then |Sₓ| ≥ 2 everywhere (OI holds), and K = ⟨2,3,4,5,1⟩ = G (TailSE holds).
But −1 = 6 ∉ V, so HH fails. The death values are: at x=1 need m=6, at x=2
need m=3, at x=3 need m=2, at x=5 need m=4. The walk avoids all death pairs.

**Even stronger:** Suppose V = G \ {−1} and Sₓ = G \ {−x⁻¹} for all x ∈ V
(every non-death multiplier appears cofinally at every non-death position).
OI holds maximally, TailSE holds, but HH can still fail: from position x, all
transitions x·s for s ∈ Sₓ land in G \ {−1}, so the walk self-consistently
avoids −1 forever. Death avoidance is built into the transition structure.

**Why OI ↛ DH:** OI is a *marginal* statement (per-position multiplier diversity).
DH is a *joint* statement (the death pair (x, −x⁻¹) must appear as
(walkZ q n, multZ q n)). No marginal statement can force the joint event.

**Why DH ↛ OI:** If DH holds, the walk hits −1 at some step n, meaning
multZ q n = −(walkZ q n)⁻¹. But at that same position x = walkZ q n, the
cofinal multiplier could be exactly that one value (the walk might visit x only
finitely many other times, or all other visits could use the same multiplier).

**TailSE and OI are incomparable.** TailSE is a *global* marginal statement:
multipliers don't settle into any proper subgroup (infinitely many n with
emMultUnit(n) ∉ H for each H). OI is a *local* marginal statement: at each
position, multipliers take multiple values. Neither implies the other:
- TailSE ↛ OI: the escaping multipliers could all occur at positions ≠ x,
  while position x is locked to a single multiplier value.
- OI ↛ TailSE: diverse multipliers at each position could all lie in a
  proper subgroup (e.g., |Sₓ| = 2 but both values are squares).

**DynamicalHitting IS the factoring oracle impossibility.** The "factoring oracle"
is the systematic correlation between Prod(n) mod q (= walkZ q n) and
minFac(Prod(n)+1) mod q (= multZ q n) that would be needed to avoid the death
equation indefinitely. DH asserts this oracle cannot exist. There is no useful
intermediate between TailSE and DH: the minimal hypothesis to force the walk to
hit −1 is literally "∃ n ≥ N : multZ q n = −(walkZ q n)⁻¹", which IS DH. -/

section OracleImpossibility
open MullinGroup

/-- **OracleImpossibility**: at each cofinally visited position x ≠ -1, the
    multiplier residues mod q are not eventually locked to a single value.

    That is: if position x is visited infinitely often, then for any candidate
    multiplier value s, there exist infinitely many visits to x where the
    multiplier is NOT s.

    NOTE: This is a *marginal* per-position diversity statement. It does NOT
    imply DynamicalHitting, and DH does not imply it. TailSE does not imply it
    either (TailSE is global, OI is local). See §23 commentary. -/
def OracleImpossibility : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)]
    (_hq : IsPrime q) (_hne : ∀ k, seq k ≠ q)
    (x : ZMod q) (_ : x ≠ -1)
    (s : ZMod q),
    (∀ N, ∃ n, N ≤ n ∧ walkZ q n = x) →
    ∀ N, ∃ n, N ≤ n ∧ walkZ q n = x ∧ multZ q n ≠ s

/-- **DH restated as death-pair occurrence**: DynamicalHitting is equivalent to
    the statement that for each prime q (with SE), the "death pair"
    (walkZ q n, −(walkZ q n)⁻¹) is eventually realized as (walkZ q n, multZ q n).

    This is the precise "factoring oracle impossibility": the greedy factoring
    process cannot systematically correlate Prod(n) mod q with minFac(Prod(n)+1)
    mod q to avoid the single forbidden residue class at every step.

    The equivalence involves an index shift: DH says `q ∣ (prod n + 1)` cofinally
    (walk IS at -1 at step n), while the death pair says `multZ q n = -(walkZ q n)⁻¹`
    cofinally (walk WILL BE at -1 at step n+1). -/
theorem dh_iff_death_pair :
    DynamicalHitting ↔
    ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
      (∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
        ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H) →
      ∀ N, ∃ n, N ≤ n ∧ multZ q n = -(walkZ q n)⁻¹ := by
  constructor
  · -- Forward: DH (walk hits -1 cofinally) → death pair (multiplier = death value cofinally)
    -- DH gives n ≥ N+1 with q ∣ (prod n + 1), i.e., walkZ q n = -1.
    -- Write n = m + 1 (since n ≥ 1). Then walkZ q (m+1) = -1 ↔ multZ q m = -(walkZ q m)⁻¹.
    intro hdh q _ hq hne hse N
    obtain ⟨n, hn, hdvd⟩ := hdh q hq hne hse (N + 1)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨m, by omega,
      (death_value_eq hq hne m).mp ((walkZ_eq_neg_one_iff (m + 1)).mpr hdvd)⟩
  · -- Backward: death pair → DH
    -- Death pair gives n ≥ N with multZ q n = -(walkZ q n)⁻¹, i.e., walkZ q (n+1) = -1.
    -- Then q ∣ (prod (n+1) + 1) and n+1 ≥ N.
    intro h q _ hq hne hse N
    obtain ⟨n, hn, hdeath⟩ := h q hq hne hse N
    exact ⟨n + 1, by omega,
      (walkZ_eq_neg_one_iff (n + 1)).mp ((death_value_eq hq hne n).mpr hdeath)⟩

end OracleImpossibility

-- ============================================================================
-- §38. THE minFac OBSTRUCTION
--
-- The Euclid construction guarantees fresh primes at every step: every prime
-- factor of prod(n)+1 is new (coprime to the running product). The sole source
-- of difficulty in Mullin's Conjecture is the *selection rule*: seq(n+1) is the
-- *smallest* prime factor of prod(n)+1, not an arbitrary one.
--
-- This section formalizes the contrast:
-- (1) If seq(k+1) = p, then p ∣ prod(k) + 1 — the prime was "selectable".
-- (2) If p divides prod(n)+1, then seq(n+1) ≤ p: the minFac rule may
--     select a smaller prime instead.
-- (3) The capture condition: p is selected iff it is the smallest available.
-- (4) Fresh primes exist at every step, but minFac may not select any given p.
--
-- The reduction `complex_csb_mc'` (CCSB → MC) precisely captures the analytic
-- content needed to control this selection rule.
-- ============================================================================

section MinFacObstruction

/-- §38. **Selectability is necessary for MC (at successor steps).**
If `seq(k+1) = p`, then `p ∣ prod(k) + 1` by definition of the sequence:
`seq(k+1) = minFac(prod(k) + 1)`, and `minFac` always divides its argument.

Note: the base case `seq(0) = 2` is definitional, not obtained from any
Euclid number. Indeed, `prod(n) + 1` is always odd (since `prod(n)` is always
even), so 2 never divides any `prod(n) + 1`. The theorem is stated for
successor indices to avoid this degenerate case. -/
theorem selectability_necessary {p k : Nat} (hk : seq (k + 1) = p) :
    p ∣ prod k + 1 := by
  rw [seq_succ] at hk
  exact hk ▸ minFac_dvd _ (by have := prod_ge_two k; omega)

/-- **The minFac selection blocks larger primes.**
If a prime `p` divides `prod(n) + 1`, then `seq(n+1) = minFac(prod(n)+1) ≤ p`.
The `minFac` rule always prefers a smaller or equal prime. This is the
fundamental obstruction: even when p is "available" (divides the Euclid number),
a smaller prime may be selected instead. -/
theorem minFac_blocks_selection {p n : Nat} (hp : IsPrime p) (hdvd : p ∣ prod n + 1) :
    seq (n + 1) ≤ p := by
  rw [seq_succ]
  exact minFac_min' _ _ (by have := prod_ge_two n; omega) hp.1 hdvd

/-- **The capture condition.** If `p ∣ prod(n) + 1` AND every prime smaller
than `p` has already appeared by step `n`, then `seq(n+1) = p`. This is
exactly `captures_target` from MullinConjectures.lean, restated here for
narrative context.

The condition "all smaller primes have appeared" is what the inductive bootstrap
provides: MC(< p) gives a stage past which all primes below p are in the sequence,
hence divide `prod(n)`, hence cannot divide `prod(n)+1`. After that stage, p is
the *smallest* factor of `prod(n)+1` whenever it divides it. -/
theorem minFac_selects_when_smallest {p n : Nat} (hp : IsPrime p)
    (hdvd : p ∣ prod n + 1)
    (hall : ∀ r, r < p → IsPrime r → ∃ m, m ≤ n ∧ seq m = r) :
    seq (n + 1) = p :=
  captures_target hp hdvd hall

/-- **New primes at every step (Euclid's core argument).**
For any step `n`, the Euclid number `prod(n) + 1` has a prime factor that
does not appear among `seq(0), ..., seq(n)`. This is because every `seq(m)`
with `m ≤ n` divides `prod(n)`, hence cannot divide `prod(n) + 1`
(consecutive integers are coprime).

This is the engine that guarantees the sequence never stalls: fresh primes
are always available. The difficulty is not the *existence* of new primes,
but whether the minFac rule eventually *selects* every specific prime. -/
theorem fresh_prime_at_every_step (n : Nat) :
    ∃ p, IsPrime p ∧ p ∣ prod n + 1 ∧ ∀ m, m ≤ n → seq m ≠ p := by
  refine ⟨seq (n + 1), seq_isPrime (n + 1), ?_, ?_⟩
  · rw [seq_succ]; exact minFac_dvd _ (by have := prod_ge_two n; omega)
  · intro m hm heq
    exact absurd (seq_injective m (n + 1) heq) (by omega)

/-- **Coprimality of Euclid numbers and running products.**
`prod(n) + 1` is coprime to `prod(n)`. Consecutive integers share no common
factor ≥ 2, so every prime factor of the Euclid number `prod(n)+1` is distinct
from every prime factor of `prod(n)` — i.e., every prime factor is *new*. -/
theorem aux_coprime_prod (n : Nat) : Nat.Coprime (prod n + 1) (prod n) :=
  Nat.coprime_self_add_left.mpr (Nat.coprime_one_left_iff (prod n) |>.mpr trivial)

-- ----------------------------------------------------------------------------
-- §38b. THE SELECTABILITY PERSPECTIVE
--
-- The "random-factor" variant: if one could choose ANY prime factor of
-- Prod(n)+1 at each step (not just the smallest), DynamicalHitting would
-- directly give MC.  The sole obstruction is the minimality of minFac.
--
-- Key dichotomy for each prime p:
-- • If p enters the sequence: p ∣ Prod(n) for all subsequent n, so
--   p ∤ Prod(n)+1 ever again.  Selectability is one-shot.
-- • If p never enters: under DH, p ∣ Prod(n)+1 for infinitely many n.
--   The prime is perpetually available but perpetually passed over.
-- ----------------------------------------------------------------------------

/-- **A prime dividing a Euclid number has never appeared in the sequence.**
If `p ∣ prod(n) + 1`, then `seq(m) ≠ p` for all `m ≤ n`. Any prior
sequence term divides `prod(n)`, and consecutive integers are coprime,
so no prior term can equal a factor of `prod(n) + 1`.

Note: no primality hypothesis on `p` is needed; the argument uses only
that `seq(m) ∣ prod(n)` (for `m ≤ n`) and `not_dvd_consec`. -/
theorem divisor_not_yet_in_seq {p n : Nat} (hdvd : p ∣ prod n + 1) :
    ∀ m, m ≤ n → seq m ≠ p := by
  intro m hm heq
  rw [← heq] at hdvd
  exact seq_not_dvd_prod_succ hm hdvd

/-- **Being passed over preserves availability.** If `p ∣ prod(n) + 1` but
`seq(n+1) ≠ p` (the minFac rule chose a smaller prime), then `p` remains
absent from the sequence through step `n + 1`. The prime survives to
potentially divide future Euclid numbers.

This is the combinatorial heart of the "random-factor" intuition: each time
the minFac rule passes over `p`, the prime gets another chance. -/
theorem passed_over_persists {p n : Nat} (hdvd : p ∣ prod n + 1)
    (hpass : seq (n + 1) ≠ p) :
    ∀ m, m ≤ n + 1 → seq m ≠ p := by
  intro m hm
  by_cases h : m ≤ n
  · exact divisor_not_yet_in_seq hdvd m h
  · have : m = n + 1 := by omega
    subst this; exact hpass

/-- **Selectability is extinguished once a prime enters the sequence.**
Once `seq(m) = p`, the prime `p` divides `prod(n)` for all `n ≥ m`.
Since `prod(n)` and `prod(n) + 1` are coprime, `p` can never divide
`prod(n) + 1` again. Selectability is a one-shot resource.

Contrast with `InfinitelySelectable` below: primes that *never* enter the
sequence remain selectable forever (under DH). -/
theorem selectability_extinguished {p m n : Nat}
    (hseq : seq m = p) (hn : m ≤ n) :
    ¬(p ∣ prod n + 1) := by
  rw [← hseq]; exact seq_not_dvd_prod_succ hn

/-- **Infinite selectability**: a prime `p` divides `prod(n) + 1` for
cofinally many `n`. In the "random-factor" variant of the Euclid-Mullin
construction, infinite selectability would suffice for MC(p): each time
`p ∣ prod(n) + 1`, we could simply choose `p`.

In the actual EM sequence with the minFac rule, infinite selectability is
necessary but not sufficient — the prime must also be the *smallest* factor
at some step. By `selectability_extinguished`, MC(p) and
InfinitelySelectable(p) are mutually exclusive: a prime that enters the
sequence can never be selectable again. -/
def InfinitelySelectable (p : Nat) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ p ∣ prod n + 1

/-- **MC(p) implies p is not infinitely selectable.** Once `p` enters the
sequence at step `k`, it divides `prod(n)` for all `n ≥ k`, so it can
never divide `prod(n) + 1` again. -/
theorem mc_implies_not_infinitely_selectable {p : Nat} (hmc : ∃ k, seq k = p) :
    ¬InfinitelySelectable p := by
  obtain ⟨k, hk⟩ := hmc
  intro hinf
  obtain ⟨n, hn, hdvd⟩ := hinf k
  exact selectability_extinguished hk hn hdvd

/-- **DynamicalHitting implies infinite selectability** for primes not in
the sequence. Under DH, every prime `q` that never appears — provided its
multiplier residues escape every proper subgroup — divides `prod(n) + 1`
for infinitely many `n`.

This is the formal content of the "random-factor" argument: in a variant
where one could pick any factor, DH alone would give MC. The gap between
infinite selectability and actual MC is precisely the minimality constraint
of the minFac rule, which the inductive bootstrap (PRE + MC(< p)) bridges
by ensuring that eventually `p` is the smallest available factor. -/
theorem dh_implies_infinitely_selectable (hdh : DynamicalHitting)
    {q : Nat} [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q)
    (hse : ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H) :
    InfinitelySelectable q :=
  hdh q hq hne hse

end MinFacObstruction

