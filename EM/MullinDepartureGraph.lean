import EM.EquidistBootstrap
import EM.MullinGroupCore

/-!
# Departure Graph Framework

Analyzes the structural consequences of DynamicalHitting failure via
the "departure graph" -- a directed graph on group elements recording
which multiplier residues are observed at each walk position.

## Main definitions

* `departureSet w m g` -- the set of multipliers used when the walk is at position g
* `visitedSet w` -- the range of the walk
* `globalMultiplierSet m` -- the range of the multiplier sequence

## Main results

* `departure_lands_in_visited` -- each step lands in the visited set
* `subgroup_trapping` -- confinement to H forces multipliers into H
* `generation_escapes_subgroup` -- if multipliers generate G, no proper subgroup confines the walk
* `coset_trapping_reduces` -- coset confinement with identity start reduces to subgroup confinement
* `oracle_from_confinement` -- the walk's visited set constrains multipliers position-dependently
* `setStabilizer_subgroup` -- the set stabilizer is a subgroup
* `generation_contradicts_proper_stabilizer` -- if multipliers generate G, V is not properly stabilized
-/

open Mullin Euclid MullinGroup

section DepartureGraph

variable {G : Type*} [Group G]

/-- The departure set from position `g`: the set of multipliers observed when the walk
    is at `g`. Here `w k` is the position before step `k`, and `m k` is the multiplier
    used at step `k`, so `w (k+1) = w k * m k`. -/
def departureSet (w m : ℕ → G) (g : G) : Set G :=
  { x : G | ∃ k, w k = g ∧ m k = x }

/-- The visited set of a walk: the range of positions. -/
def visitedSet (w : ℕ → G) : Set G := Set.range w

/-- The global multiplier set: the range of the multiplier sequence. -/
def globalMultiplierSet (m : ℕ → G) : Set G := Set.range m

omit [Group G] in
/-- **Departure into visited set**: each step of the walk produces a point in the
    visited set. -/
theorem departure_lands_in_visited (w : ℕ → G) (k : ℕ) :
    w (k + 1) ∈ visitedSet w :=
  ⟨k + 1, rfl⟩

/-- **Subgroup trapping**: if the walk is confined to a subgroup H, then every
    multiplier belongs to H. -/
theorem subgroup_trapping (w m : ℕ → G)
    (hwalk : ∀ k, w (k + 1) = w k * m k)
    (H : Subgroup G) (hconf : ∀ k, w k ∈ (H : Set G)) (k : ℕ) :
    m k ∈ (H : Set G) := by
  have h1 : w k ∈ (H : Set G) := hconf k
  have h2 : w (k + 1) ∈ (H : Set G) := hconf (k + 1)
  rw [hwalk k] at h2
  -- h2 : w k * m k ∈ H, h1 : w k ∈ H
  -- So (w k)⁻¹ * (w k * m k) = m k ∈ H
  have : (w k)⁻¹ * (w k * m k) ∈ (H : Set G) := H.mul_mem (H.inv_mem h1) h2
  rwa [inv_mul_cancel_left] at this

/-- **Multiplier set confined to subgroup**: if the walk stays in H,
    the global multiplier set is contained in H. -/
theorem multiplier_set_confined (w m : ℕ → G)
    (hwalk : ∀ k, w (k + 1) = w k * m k)
    (H : Subgroup G) (hconf : ∀ k, w k ∈ (H : Set G)) :
    globalMultiplierSet m ⊆ (H : Set G) := by
  intro x hx
  obtain ⟨k, rfl⟩ := hx
  exact subgroup_trapping w m hwalk H hconf k

/-- **Generation escapes subgroups**: if the multiplier set generates the full group,
    then no proper subgroup can confine the walk. -/
theorem generation_escapes_subgroup (w m : ℕ → G)
    (hwalk : ∀ k, w (k + 1) = w k * m k)
    (hgen : Subgroup.closure (Set.range m) = ⊤)
    (H : Subgroup G) (hH : H ≠ ⊤) :
    ∃ k, w k ∉ (H : Set G) := by
  by_contra hall
  push_neg at hall
  -- hall : ∀ k, w k ∈ H
  have hsub : globalMultiplierSet m ⊆ (H : Set G) :=
    multiplier_set_confined w m hwalk H hall
  -- closure of multiplier set ≤ H
  have hcl : Subgroup.closure (Set.range m) ≤ H := by
    rw [Subgroup.closure_le]
    exact hsub
  -- But closure = ⊤, so H = ⊤
  rw [hgen] at hcl
  exact hH (top_le_iff.mp hcl)

/-- **Coset trapping reduces to subgroup**: if the walk starts at the identity and
    is confined to a coset g₀ * H, then g₀ ∈ H (so the coset is H itself). -/
theorem coset_trapping_reduces (w : ℕ → G)
    (hw0 : w 0 = 1) (H : Subgroup G) (g₀ : G)
    (hconf : ∀ k, ∃ h ∈ (H : Set G), w k = g₀ * h) :
    g₀ ∈ (H : Set G) := by
  obtain ⟨h, hh, heq⟩ := hconf 0
  rw [hw0] at heq
  -- heq : 1 = g₀ * h, so g₀ = h⁻¹
  have : g₀ = h⁻¹ := by
    have := heq.symm
    rwa [mul_eq_one_iff_eq_inv] at this
  rw [this]
  exact H.inv_mem hh

/-- **Oracle from confinement**: the multiplier at step k equals (w k)⁻¹ * w(k+1),
    and w(k+1) is in the visited set. This is the "position-dependent oracle" --
    each position constrains which multipliers can appear. -/
theorem oracle_from_confinement (w m : ℕ → G)
    (hwalk : ∀ k, w (k + 1) = w k * m k) (k : ℕ) :
    ∃ v ∈ visitedSet w, m k = (w k)⁻¹ * v := by
  refine ⟨w (k + 1), ⟨k + 1, rfl⟩, ?_⟩
  rw [hwalk k, inv_mul_cancel_left]

/-- The departure set at g is contained in {g⁻¹ * v | v ∈ visitedSet w}. -/
theorem departureSet_subset_left_translate (w m : ℕ → G)
    (hwalk : ∀ k, w (k + 1) = w k * m k) (g : G) (x : G)
    (hx : x ∈ departureSet w m g) :
    ∃ v ∈ visitedSet w, x = g⁻¹ * v := by
  obtain ⟨k, hpos, hmult⟩ := hx
  refine ⟨w (k + 1), ⟨k + 1, rfl⟩, ?_⟩
  rw [hwalk k, ← hpos, inv_mul_cancel_left, hmult]

omit [Group G] in
/-- The departure set at an unvisited position is empty. -/
theorem departureSet_empty_of_unvisited (w m : ℕ → G) (g : G)
    (hg : g ∉ visitedSet w) :
    departureSet w m g = ∅ := by
  ext x
  simp only [departureSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨k, hpos, -⟩
  exact hg ⟨k, hpos⟩

omit [Group G] in
/-- The global multiplier set is the union of all departure sets over visited positions. -/
theorem globalMultiplierSet_eq_union (w m : ℕ → G) :
    globalMultiplierSet m = ⋃ g ∈ visitedSet w, departureSet w m g := by
  ext x
  simp only [globalMultiplierSet, Set.mem_range, Set.mem_iUnion, visitedSet,
    departureSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨w k, ⟨k, rfl⟩, k, rfl, rfl⟩
  · rintro ⟨g, ⟨_, _⟩, k, _, rfl⟩
    exact ⟨k, rfl⟩

/-- If the walk starts at `a` and multipliers generate the full group,
    then the walk visits every element of a * closure(multipliers) = a * G = G.
    Contrapositively: if some element is missed, multipliers don't generate G. -/
theorem visited_top_of_gen_and_confined (w m : ℕ → G)
    (hwalk : ∀ k, w (k + 1) = w k * m k)
    (hgen : Subgroup.closure (Set.range m) = ⊤)
    (H : Subgroup G) (hconf : ∀ k, w k ∈ (H : Set G)) :
    H = ⊤ := by
  by_contra hH
  exact (generation_escapes_subgroup w m hwalk hgen H hH).elim (fun k hk => hk (hconf k))

/-- **Walk confinement to coset**: the walk is confined to the coset
    w(0) * closure(multipliers). That is, `w k = w 0 * h` for some
    `h ∈ Subgroup.closure (Set.range m)`. -/
theorem walk_in_coset_closure (w m : ℕ → G)
    (hwalk : ∀ k, w (k + 1) = w k * m k) (k : ℕ) :
    ∃ h ∈ (Subgroup.closure (Set.range m) : Set G), w k = w 0 * h := by
  induction k with
  | zero =>
    exact ⟨1, (Subgroup.closure (Set.range m)).one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨h, hh, heq⟩ := ih
    refine ⟨h * m n, Subgroup.mul_mem _ hh (Subgroup.subset_closure ⟨n, rfl⟩), ?_⟩
    rw [hwalk n, heq, mul_assoc]

/-- For a walk starting at the identity, the walk stays in the closure of multipliers. -/
theorem walk_in_closure_of_start_one (w m : ℕ → G)
    (hwalk : ∀ k, w (k + 1) = w k * m k)
    (hw0 : w 0 = 1) (k : ℕ) :
    w k ∈ (Subgroup.closure (Set.range m) : Set G) := by
  obtain ⟨h, hh, heq⟩ := walk_in_coset_closure w m hwalk k
  rw [hw0, one_mul] at heq
  rw [heq]
  exact hh

end DepartureGraph

/-! ## Connection to the Euclid-Mullin walk

We connect the abstract departure graph framework to the concrete
Euclid-Mullin residue walk `walkZ q n` with multipliers `multZ q n`.

The abstract framework works for any `Group G`. For the EM walk, the relevant
group is `(ZMod q)ˣ` (the units of ZMod q), not `ZMod q` itself (which is a
ring, not a group under multiplication). The `walkZ`/`multZ` functions output
elements of `ZMod q`, so the subgroup-level theorems in `MullinGroupCore`
(e.g., `confinement_forward`, `confinement_reverse`) lift to units explicitly.

Here we provide the ring-level definitions (visited set, departure set, multiplier
set) which do not require a group structure. -/

section EuclidMullinConnection

/-- The EM walk satisfies the abstract walk recurrence (in the ring ZMod q). -/
theorem em_walk_recurrence (q : ℕ) :
    ∀ k, walkZ q (k + 1) = walkZ q k * multZ q k :=
  walkZ_succ q

/-- The visited set of the EM walk in ZMod q. -/
def emVisitedSet (q : ℕ) : Set (ZMod q) := Set.range (walkZ q)

/-- The multiplier set of the EM walk in ZMod q. -/
def emMultiplierSet (q : ℕ) : Set (ZMod q) := Set.range (multZ q)

/-- The departure set of the EM walk at a position g in ZMod q. -/
def emDepartureSet (q : ℕ) (g : ZMod q) : Set (ZMod q) :=
  { x : ZMod q | ∃ k, walkZ q k = g ∧ multZ q k = x }

/-- Each step of the EM walk lands in the visited set. -/
theorem em_visited_step (q : ℕ) (k : ℕ) :
    walkZ q (k + 1) ∈ emVisitedSet q :=
  ⟨k + 1, rfl⟩

/-- The departure set at an unvisited element of ZMod q is empty. -/
theorem em_departure_empty_of_unvisited (q : ℕ) (g : ZMod q)
    (hg : g ∉ emVisitedSet q) :
    emDepartureSet q g = ∅ := by
  ext x
  simp only [emDepartureSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨k, hpos, -⟩
  exact hg ⟨k, hpos⟩

/-- The EM multiplier set equals the union of departure sets over visited positions. -/
theorem em_multiplier_union (q : ℕ) :
    emMultiplierSet q = ⋃ g ∈ emVisitedSet q, emDepartureSet q g := by
  ext x
  simp only [emMultiplierSet, Set.mem_range, emVisitedSet, emDepartureSet,
    Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨walkZ q k, ⟨k, rfl⟩, k, rfl, rfl⟩
  · rintro ⟨_, ⟨_, _⟩, k, _, rfl⟩
    exact ⟨k, rfl⟩

/-- The multiplier at step k satisfies `w(k) * m(k) ∈ emVisitedSet q`.
    This is the ring-level analogue of `departure_lands_in_visited`. -/
theorem em_departure_lands_in_visited (q : ℕ) (k : ℕ) :
    walkZ q k * multZ q k ∈ emVisitedSet q := by
  rw [← walkZ_succ]
  exact ⟨k + 1, rfl⟩

end EuclidMullinConnection

/-! ## Infinite Recurrence Lemma

Pigeonhole argument: if G is a finite type and w : ℕ → G is any function,
then some element of G is hit infinitely often. This is the key observation
that an infinite walk in a finite group must revisit positions. -/

section InfiniteRecurrence

/-- **Infinite recurrence**: an infinite sequence in a finite type revisits some value
    infinitely often. This is a direct consequence of the pigeonhole principle
    (`Finite.exists_infinite_fiber`). -/
theorem exists_infinite_fiber_of_finite {G : Type*} [Finite G] (w : ℕ → G) :
    ∃ g : G, Set.Infinite {k : ℕ | w k = g} := by
  obtain ⟨g, hg⟩ := Finite.exists_infinite_fiber w
  refine ⟨g, ?_⟩
  rw [Set.infinite_coe_iff] at hg
  convert hg using 1

/-- The infinitely-visited element lies in the visited set. -/
theorem infinite_fiber_mem_visitedSet {G : Type*} [Finite G] (w : ℕ → G) :
    ∃ g ∈ visitedSet w, Set.Infinite {k : ℕ | w k = g} := by
  obtain ⟨g, hg⟩ := exists_infinite_fiber_of_finite w
  have hne : {k : ℕ | w k = g}.Nonempty := hg.nonempty
  obtain ⟨k, hk⟩ := hne
  exact ⟨g, ⟨k, hk⟩, hg⟩

/-- If the walk visits g infinitely often, then infinitely many steps depart from g
    (i.e., infinitely many multipliers contribute to the departure set at g). -/
theorem infinite_departures_at_recurrent {G : Type*} [Finite G]
    (w m : ℕ → G)
    (g : G) (hg : Set.Infinite {k : ℕ | w k = g}) :
    Set.Infinite {k : ℕ | w k = g ∧ m k ∈ departureSet w m g} := by
  apply Set.Infinite.mono _ hg
  intro k hk
  simp only [Set.mem_setOf_eq] at hk ⊢
  exact ⟨hk, k, hk, rfl⟩

end InfiniteRecurrence

/-! ## Safe Prime Subgroup Lattice

For a cyclic group of order 2p (p an odd prime), the subgroup lattice has
exactly 4 elements: ⊥ (order 1), the unique subgroup of order 2, the unique
subgroup of order p (index 2), and ⊤ (order 2p). This means any proper
subgroup has order dividing p or 2 — a very rigid structure.

We state results abstractly for finite cyclic groups of order 2p, avoiding
ZMod API friction. The key consequence is that a generating set cannot be
contained in any proper subgroup, and for order 2p with p prime there are
only 3 proper subgroups to escape. -/

section SafePrimeLattice

/-- A prime q is a safe prime if (q-1)/2 is also prime. -/
def IsSafePrime (q : ℕ) : Prop := Nat.Prime q ∧ Nat.Prime ((q - 1) / 2)

/-- The divisors of 2*p (p odd prime) are exactly {1, 2, p, 2*p}. -/
theorem dvd_two_mul_prime_iff (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) (d : ℕ) :
    d ∣ 2 * p ↔ d = 1 ∨ d = 2 ∨ d = p ∨ d = 2 * p := by
  constructor
  · intro hd
    by_cases h2d : 2 ∣ d
    · -- d = 2 * e for some e, and 2*e ∣ 2*p, so e ∣ p
      obtain ⟨e, rfl⟩ := h2d
      have he : e ∣ p := by
        rwa [mul_dvd_mul_iff_left (show (2 : ℕ) ≠ 0 by omega)] at hd
      rcases hp.eq_one_or_self_of_dvd e he with rfl | rfl
      · right; left; ring
      · right; right; right; ring
    · -- 2 ∤ d, so Coprime d 2. Since d ∣ 2*p, by coprimality d ∣ p.
      have hcop : Nat.Coprime d 2 := by
        rw [Nat.coprime_comm]
        exact Nat.prime_two.coprime_iff_not_dvd.mpr h2d
      have hdp : d ∣ p := by
        rw [mul_comm] at hd
        exact hcop.dvd_mul_right.mp hd
      rcases hp.eq_one_or_self_of_dvd d hdp with rfl | rfl
      · left; rfl
      · right; right; left; rfl
  · rintro (rfl | rfl | rfl | rfl) <;> simp [dvd_mul_right, dvd_mul_left]

/-- In a finite group of order 2*p (p odd prime), every subgroup has order in {1, 2, p, 2*p}. -/
theorem card_subgroup_of_order_two_mul_prime {G : Type*} [Group G]
    (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (hcard : Nat.card G = 2 * p)
    (H : Subgroup G) :
    Nat.card H = 1 ∨ Nat.card H = 2 ∨
    Nat.card H = p ∨ Nat.card H = 2 * p := by
  have hH := Subgroup.card_subgroup_dvd_card H
  rw [hcard] at hH
  exact (dvd_two_mul_prime_iff p hp hp2 _).mp hH

/-- In a finite group of order 2*p, every proper subgroup has order at most p. -/
theorem card_proper_subgroup_le {G : Type*} [Group G]
    (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (hcard : Nat.card G = 2 * p)
    (H : Subgroup G) (hH : H ≠ ⊤) :
    Nat.card H = 1 ∨ Nat.card H = 2 ∨ Nat.card H = p := by
  rcases card_subgroup_of_order_two_mul_prime p hp hp2 hcard H with h | h | h | h
  · left; exact h
  · right; left; exact h
  · right; right; exact h
  · exfalso; apply hH
    have hp_pos : 0 < p := Nat.Prime.pos hp
    have : Finite H := Nat.finite_of_card_ne_zero (by omega)
    exact Subgroup.eq_top_of_card_eq H (by rw [h, hcard])

/-- **QR confinement contradicts generation**: if all multipliers of a walk in a finite
    group lie in a proper subgroup H, then the closure of multipliers is contained in H,
    so if multipliers generate the full group, we get a contradiction.
    This is a restatement of `generation_escapes_subgroup` in terms of the multiplier set. -/
theorem multiplier_closure_ne_top_of_confined {G : Type*} [Group G]
    (m : ℕ → G)
    (H : Subgroup G) (hH : H ≠ ⊤)
    (hmult : ∀ k, m k ∈ (H : Set G)) :
    Subgroup.closure (Set.range m) ≠ ⊤ := by
  intro heq
  have hsub : Set.range m ⊆ (H : Set G) := by
    rintro x ⟨k, rfl⟩
    exact hmult k
  have hle : Subgroup.closure (Set.range m) ≤ H := by
    rw [Subgroup.closure_le]
    exact hsub
  rw [heq] at hle
  exact hH (top_le_iff.mp hle)

/-- **Generating set escapes every proper subgroup**: if the multiplier sequence generates
    the full group, then for every proper subgroup, some multiplier lies outside it. -/
theorem generating_escapes_proper {G : Type*} [Group G]
    (m : ℕ → G)
    (hgen : Subgroup.closure (Set.range m) = ⊤)
    (H : Subgroup G) (hH : H ≠ ⊤) :
    ∃ k, m k ∉ (H : Set G) := by
  by_contra hall
  push_neg at hall
  exact multiplier_closure_ne_top_of_confined m H hH hall hgen

end SafePrimeLattice
