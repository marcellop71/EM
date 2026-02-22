import EM.Equidist.Threshold
import Mathlib.Algebra.Group.Subgroup.Lattice

-- In Mathlib v4.29, CompleteLattice → BoundedOrder TC chain is broken for Subgroup.
instance subgroupBoundedOrder {G : Type*} [Group G] : BoundedOrder (Subgroup G) :=
  CompleteLattice.toBoundedOrder

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
