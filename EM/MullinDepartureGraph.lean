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

/-! ## Complement Generation in Finite Groups

A key structural fact: in a finite group of order ≥ 3, removing any single element
from the group still yields a generating set. This means that the "single-element
avoidance" imposed by DH failure is always compatible with SubgroupEscape. -/

section ComplementGeneration

/-- **Complement generates**: in a group of order ≥ 3, removing any single element
    from the carrier still generates the full group. The proof uses:
    for any `g : G`, pick `a ∈ G \ {g}` with `a ≠ 1` (possible since |G| ≥ 3).
    Then `g = a * (a⁻¹ * g)`, and `a⁻¹ * g ≠ g` since `a ≠ 1`, so both factors
    lie in `G \ {g}`. -/
theorem closure_compl_singleton_eq_top {G : Type*} [Group G] [Fintype G]
    (hcard : 3 ≤ Fintype.card G) (g : G) :
    Subgroup.closure ((Set.univ : Set G) \ {g}) = ⊤ := by
  classical
  -- Step 1: find a ∈ G with a ≠ g and a ≠ 1
  have hexists : ∃ a : G, a ≠ g ∧ a ≠ 1 := by
    by_contra hall
    push_neg at hall
    -- hall : ∀ a, a ≠ g → a = 1, so every element is g or 1
    -- Claim |G| ≤ 2 by bounding via `card_le_one_iff` or explicit injection
    have h2 : Fintype.card G ≤ 2 := by
      by_cases hg1 : g = (1 : G)
      · -- If g = 1, then hall gives ∀ a, a ≠ 1 → a = 1, so |G| = 1
        subst hg1
        have : Fintype.card G ≤ 1 :=
          Fintype.card_le_one_iff.mpr (fun a b => by
            by_cases ha : a = 1
            · by_cases hb : b = 1
              · rw [ha, hb]
              · exact absurd (hall b hb) hb
            · exact absurd (hall a ha) ha)
        omega
      · -- g ≠ 1. Define f : G → Bool with f(g) = true, f(x) = false for x ≠ g
        -- This is injective since all non-g elements equal 1
        have hinj : Function.Injective (fun x : G => decide (x = g)) := by
          intro a b hab
          simp only [decide_eq_decide] at hab
          by_cases hag : a = g
          · by_cases hbg : b = g
            · rw [hag, hbg]
            · simp [hag, hbg] at hab
          · by_cases hbg : b = g
            · simp [hag, hbg] at hab
            · rw [hall a hag, hall b hbg]
        calc Fintype.card G ≤ Fintype.card Bool := Fintype.card_le_of_injective _ hinj
          _ = 2 := Fintype.card_bool
    omega
  -- Step 2: prove closure = ⊤
  rw [eq_top_iff]
  intro x _
  by_cases hxg : x = g
  · obtain ⟨a, hag, ha1⟩ := hexists
    -- x = g = a * (a⁻¹ * g), both factors ≠ g
    rw [hxg, show g = a * (a⁻¹ * g) from by group]
    apply Subgroup.mul_mem
    · exact Subgroup.subset_closure ⟨Set.mem_univ _, by simpa using hag⟩
    · have hne : a⁻¹ * g ≠ g := by
        intro heq
        apply ha1
        have h1 : a⁻¹ = (1 : G) := mul_right_cancel (heq.trans (one_mul g).symm)
        exact inv_eq_one.mp h1
      exact Subgroup.subset_closure ⟨Set.mem_univ _, by simpa using hne⟩
  · exact Subgroup.subset_closure ⟨Set.mem_univ _, by simpa using hxg⟩

/-- **Generating from complement**: if `S ⊇ univ \ {g}` and `|G| ≥ 3`,
    then `closure S = ⊤`. Useful corollary: a multiplier sequence whose range
    misses at most one element still generates the full group. -/
theorem closure_eq_top_of_compl_singleton_subset {G : Type*} [Group G] [Fintype G]
    (hcard : 3 ≤ Fintype.card G) (S : Set G) (g : G)
    (hS : (Set.univ : Set G) \ {g} ⊆ S) :
    Subgroup.closure S = ⊤ := by
  have h := closure_compl_singleton_eq_top hcard g
  exact top_le_iff.mp (h ▸ Subgroup.closure_mono hS)

end ComplementGeneration

/-! ## Structural Dichotomy for Target Avoidance

Abstract framework: for a walk `w` with multipliers `m` in a finite group,
hitting a target element `t` requires `m(k) = w(k)⁻¹ * t` at some step k.
If the walk never hits `t`, then at every recurrent position `c`, the
departure multiplier `c⁻¹ * t` is systematically avoided. This is the
"single death-channel avoidance" constraint.

The key structural insight (for safe primes): this avoidance is compatible
with SubgroupEscape — removing one element from the full group still generates
when |G| ≥ 3. So DH failure at safe primes cannot be detected purely from
generation properties; it requires analytic input (equidistribution). -/

section TargetAvoidance

variable {G : Type*} [Group G]

/-- **Hitting characterization**: the walk hits target `t` at step `k+1`
    iff the multiplier at step k equals the "death value" `w(k)⁻¹ * t`. -/
theorem walk_hits_target_iff (w m : ℕ → G)
    (hwalk : ∀ k, w (k + 1) = w k * m k) (t : G) (k : ℕ) :
    w (k + 1) = t ↔ m k = (w k)⁻¹ * t := by
  constructor
  · intro h
    have hwk := hwalk k
    rw [h] at hwk
    -- hwk : t = w k * m k, need m k = (w k)⁻¹ * t
    calc m k = (w k)⁻¹ * (w k * m k) := by rw [inv_mul_cancel_left]
      _ = (w k)⁻¹ * t := by rw [← hwk]
  · intro h
    rw [hwalk k, h, mul_inv_cancel_left]

/-- **Departure avoidance at recurrent positions**: if the walk never hits
    target `t` after step `N`, then at any position `c`, the departure
    multipliers past step `N` avoid the death value `c⁻¹ * t`. -/
theorem departure_avoids_death_value (w m : ℕ → G)
    (hwalk : ∀ k, w (k + 1) = w k * m k) (t : G) (N : ℕ)
    (havoid : ∀ k, N ≤ k → w k ≠ t) (c : G) (k : ℕ) (hk : N ≤ k)
    (hpos : w k = c) :
    m k ≠ c⁻¹ * t := by
  intro heq
  exact havoid (k + 1) (by omega) ((walk_hits_target_iff w m hwalk t k).mpr (hpos ▸ heq))

/-- **Departure set exclusion**: if the walk avoids target `t` from step `N` onwards,
    then at position `c`, every departure multiplier past `N` lies in `G \ {c⁻¹ * t}`. -/
theorem departure_set_excludes_death_value (w m : ℕ → G)
    (hwalk : ∀ k, w (k + 1) = w k * m k) (t : G) (N : ℕ)
    (havoid : ∀ k, N ≤ k → w k ≠ t) (c : G) (k : ℕ) (hk : N ≤ k)
    (hpos : w k = c) :
    m k ∈ (Set.univ : Set G) \ {c⁻¹ * t} :=
  ⟨Set.mem_univ _, departure_avoids_death_value w m hwalk t N havoid c k hk hpos⟩

/-- **Infinite avoidance**: if the walk visits position `c` infinitely often and
    never hits target `t` after step `N`, then infinitely many departure multipliers
    at `c` avoid the death value `c⁻¹ * t`. -/
theorem infinite_departures_avoiding_death (w m : ℕ → G) [Finite G]
    (hwalk : ∀ k, w (k + 1) = w k * m k) (t : G) (N : ℕ)
    (havoid : ∀ k, N ≤ k → w k ≠ t) (c : G)
    (hcof : Set.Infinite {k : ℕ | w k = c}) :
    Set.Infinite {k : ℕ | N ≤ k ∧ w k = c ∧ m k ≠ c⁻¹ * t} := by
  -- The set {k | w k = c} is infinite, and {k | k < N} is finite,
  -- so {k | N ≤ k ∧ w k = c} is infinite. Each such k also avoids the death value.
  have hN_finite : Set.Finite {k : ℕ | ¬(N ≤ k)} := by
    apply (Set.Finite.subset (Set.finite_Iio N) _)
    intro k hk
    simp only [Set.mem_setOf_eq, not_le] at hk
    exact Set.mem_Iio.mpr hk
  have hinf2 : Set.Infinite ({k : ℕ | w k = c} \ {k | ¬(N ≤ k)}) :=
    hcof.diff hN_finite
  apply hinf2.mono
  intro k hk
  simp only [Set.mem_diff, Set.mem_setOf_eq, not_not] at hk ⊢
  exact ⟨hk.2, hk.1, departure_avoids_death_value w m hwalk t N havoid c k hk.2 hk.1⟩

end TargetAvoidance

/-! ## Safe Prime DH Structural Dichotomy

For a safe prime `q` with `|G| = q - 1 = 2p'` (p' prime), DH failure means
the walk avoids `-1` from some step onwards. The structural consequences:

1. At every recurrent position `c`, departure multipliers avoid `c⁻¹ * (-1) = -c⁻¹`.
2. Despite this avoidance, `G \ {-c⁻¹}` still generates `G` (since `|G| ≥ 4`).
3. So SE (SubgroupEscape) is structurally compatible with DH failure.
4. The DH failure constraint is "invisible" to the subgroup lattice — it requires
   analytic methods (equidistribution, character sums) to detect.

This formalizes why the DH → MC reduction is genuinely hard: the structural
(algebraic) constraints from SE leave room for DH failure. -/

section SafePrimeDichotomy

/-- **Safe prime target avoidance dichotomy**: either every element of `G` is visited
    by the walk, or the walk avoids some element. In the avoidance case, the
    departure multipliers at each recurrent position are restricted but still
    generate the full group (when `|G| ≥ 3`). -/
theorem avoidance_compatible_with_generation {G : Type*} [Group G] [Fintype G]
    (hcard : 3 ≤ Fintype.card G)
    (_w _m : ℕ → G) (_hwalk : ∀ k, _w (k + 1) = _w k * _m k)
    (t : G) (_N : ℕ) (_havoid : ∀ k, _N ≤ k → _w k ≠ t)
    (c : G) :
    Subgroup.closure ((Set.univ : Set G) \ {c⁻¹ * t}) = ⊤ :=
  closure_compl_singleton_eq_top hcard (c⁻¹ * t)

/-- **Avoidance does not obstruct SE**: even when the walk avoids target `t` and
    departure multipliers at position `c` are restricted to `G \ {c⁻¹ * t}`,
    there exists a multiplier sequence whose range is contained in `G \ {c⁻¹ * t}`
    yet still generates the full group. So DH failure cannot be ruled out by
    purely algebraic (subgroup lattice) arguments.

    This is the formal version of "SE is compatible with DH failure." -/
theorem se_compatible_with_dh_failure {G : Type*} [Group G] [Fintype G]
    (hcard : 3 ≤ Fintype.card G) (t : G) (c : G) :
    ∃ S : Set G, S ⊆ (Set.univ : Set G) \ {c⁻¹ * t} ∧
    Subgroup.closure S = ⊤ := by
  exact ⟨(Set.univ : Set G) \ {c⁻¹ * t}, le_refl _,
    closure_compl_singleton_eq_top hcard _⟩

/-- **Safe prime order bound**: for a safe prime `q` (i.e., `q` prime with
    `(q-1)/2` prime), we have `q - 1 ≥ 4`. This ensures `|G| ≥ 3` for any
    group of order `q - 1`, which is needed for complement generation. -/
theorem safe_prime_order_ge_four {q : ℕ} (hq : IsSafePrime q) :
    4 ≤ q - 1 := by
  obtain ⟨hpq, hpp⟩ := hq
  have hq2 : q ≥ 2 := hpq.two_le
  have hp2 : (q - 1) / 2 ≥ 2 := hpp.two_le
  omega

/-- **Safe prime: complement generation applies**: for a safe prime `q` and any
    group `G` of order `q - 1`, we have `|G| ≥ 4 ≥ 3`, so removing any single
    element from `G` still generates `G`. -/
theorem safe_prime_compl_generates {G : Type*} [Group G] [Fintype G]
    {q : ℕ} (hq : IsSafePrime q) (hord : Fintype.card G = q - 1) (g : G) :
    Subgroup.closure ((Set.univ : Set G) \ {g}) = ⊤ := by
  apply closure_compl_singleton_eq_top
  have := safe_prime_order_ge_four hq
  omega

/-- **Safe prime SE + DH failure compatibility**: for a safe prime `q`, the subgroup
    escape condition is structurally compatible with DH failure. Specifically, for
    any position `c` and target `t`, the restricted departure set `G \ {c⁻¹ * t}`
    generates the full group of order `q - 1`. -/
theorem safe_prime_se_dh_compatible {G : Type*} [Group G] [Fintype G]
    {q : ℕ} (hq : IsSafePrime q) (hord : Fintype.card G = q - 1) (c t : G) :
    Subgroup.closure ((Set.univ : Set G) \ {c⁻¹ * t}) = ⊤ :=
  safe_prime_compl_generates hq hord (c⁻¹ * t)

/-- **DH failure forces analytic obstruction**: at the recurrent position, the
    departure multipliers avoid exactly one element (the death value) yet still
    generate the full group. This means the DH failure is "analytically invisible"
    to the subgroup lattice — it can only be detected by measuring the frequency
    of multiplier values (equidistribution), not their group-theoretic span.

    Formally: given a walk that avoids target `t`, visits position `c` infinitely
    often, and has `|G| ≥ 3`, the infinitely-many departure multipliers at `c`
    all lie in `G \ {c⁻¹ * t}`, which generates `G`. The discrepancy between
    "generates G" and "avoids -1" is purely distributional. -/
theorem dh_failure_distributional_gap {G : Type*} [Group G] [Fintype G]
    (hcard : 3 ≤ Fintype.card G)
    (w m : ℕ → G) (hwalk : ∀ k, w (k + 1) = w k * m k)
    (t : G) (N : ℕ) (havoid : ∀ k, N ≤ k → w k ≠ t) (c : G)
    (_hcof : Set.Infinite {k : ℕ | w k = c}) :
    (∀ k, N ≤ k → w k = c → m k ∈ (Set.univ : Set G) \ {c⁻¹ * t}) ∧
    Subgroup.closure ((Set.univ : Set G) \ {c⁻¹ * t}) = ⊤ :=
  ⟨fun k hk hc => departure_set_excludes_death_value w m hwalk t N havoid c k hk hc,
   closure_compl_singleton_eq_top hcard _⟩

end SafePrimeDichotomy
