import EM.MullinGroupCore

/-!
# Gordon's Theorem and Pumping Arguments

* Gordon's theorem: Z/(2m)Z is sequenceable for all m ≥ 1
* Pumping argument: subgroup growth forces walk exploration
* Subgroup growth and walk orbit expansion
-/

namespace MullinGroup

open Mullin Euclid

/-! ## Gordon's Theorem for Cyclic Groups

Gordon (1961) proved that Z/(2m)Z is sequenceable for all m ≥ 1:
there exists an arrangement of its nonzero elements such that the
partial sums (mod 2m) are also a permutation of the nonzero elements.

Elements: gordonElem m (2k) = 2k+1, gordonElem m (2k+1) = 2m-2k-2
Partial sums: gordonPS m (2k) = k+1, gordonPS m (2k+1) = 2m-(k+1)

Application: for odd prime q, the group (ZMod q)× is cyclic of order
q-1 (even), so it is sequenceable. This means there exists an
arrangement of all nonidentity elements whose partial products cover
the entire group — the algebraic capacity needed for mixing. -/

/-- Gordon's element function: the i-th nonzero element of Z/(2m)Z
    in the sequencing arrangement.
    - Even i = 2k: gives 2k+1 (odd values 1, 3, ..., 2m-1)
    - Odd i = 2k+1: gives 2m-2k-2 (even values 2m-2, 2m-4, ..., 2) -/
def gordonElem (m i : Nat) : Nat :=
  if i % 2 = 0 then i + 1 else 2 * m - i - 1

/-- Gordon's partial sum function: the i-th cumulative sum (mod 2m).
    - Even i = 2k: gives k+1
    - Odd i = 2k+1: gives 2m-(k+1) -/
def gordonPS (m i : Nat) : Nat :=
  if i % 2 = 0 then i / 2 + 1 else 2 * m - (i / 2 + 1)

/-- Gordon elements are in range {1, ..., 2m-1}. -/
theorem gordonElem_bounds {m i : Nat} (hm : m ≥ 1) (hi : i < 2 * m - 1) :
    1 ≤ gordonElem m i ∧ gordonElem m i < 2 * m := by
  unfold gordonElem; split <;> constructor <;> omega

/-- Gordon partial sums are in range {1, ..., 2m-1}. -/
theorem gordonPS_bounds {m i : Nat} (hm : m ≥ 1) (hi : i < 2 * m - 1) :
    1 ≤ gordonPS m i ∧ gordonPS m i < 2 * m := by
  unfold gordonPS; split <;> constructor <;> omega

/-- Gordon elements are injective on {0, ..., 2m-2}. -/
theorem gordonElem_inj {m : Nat} (hm : m ≥ 1) {i j : Nat}
    (hi : i < 2 * m - 1) (hj : j < 2 * m - 1)
    (heq : gordonElem m i = gordonElem m j) : i = j := by
  unfold gordonElem at heq; split at heq <;> split at heq <;> omega

/-- Gordon partial sums are injective on {0, ..., 2m-2}. -/
theorem gordonPS_inj {m : Nat} (hm : m ≥ 1) {i j : Nat}
    (hi : i < 2 * m - 1) (hj : j < 2 * m - 1)
    (heq : gordonPS m i = gordonPS m j) : i = j := by
  unfold gordonPS at heq; split at heq <;> split at heq <;> omega

/-- Initial partial sum equals first element. -/
theorem gordonPS_zero (m : Nat) (_hm : m ≥ 1) : gordonPS m 0 = gordonElem m 0 := by
  unfold gordonPS gordonElem
  simp

/-- Even case recurrence: exact Nat equality (no overflow). -/
private theorem gordonPS_step_even {m i : Nat} (hm : m ≥ 1) (hi : i + 1 < 2 * m - 1)
    (heven : i % 2 = 0) :
    gordonPS m i + gordonElem m (i + 1) = gordonPS m (i + 1) := by
  unfold gordonPS gordonElem
  rw [if_pos heven, if_neg (by omega : ¬((i + 1) % 2 = 0)),
      if_neg (by omega : ¬((i + 1) % 2 = 0))]
  omega

/-- Odd case recurrence: sum overflows by exactly 2m. -/
private theorem gordonPS_step_odd {m i : Nat} (hm : m ≥ 1) (hi : i + 1 < 2 * m - 1)
    (hodd : i % 2 ≠ 0) :
    gordonPS m i + gordonElem m (i + 1) = 2 * m + gordonPS m (i + 1) := by
  unfold gordonPS gordonElem
  rw [if_neg hodd, if_pos (by omega : (i + 1) % 2 = 0),
      if_pos (by omega : (i + 1) % 2 = 0)]
  omega

/-- **Gordon recurrence in ZMod**: ps(i+1) = ps(i) + elem(i+1) in Z/(2m)Z. -/
theorem gordonPS_step {m : Nat} (hm : m ≥ 1) {i : Nat} (hi : i + 1 < 2 * m - 1) :
    (gordonPS m (i + 1) : ZMod (2 * m)) =
    (gordonPS m i : ZMod (2 * m)) + (gordonElem m (i + 1) : ZMod (2 * m)) := by
  rw [← Nat.cast_add]
  by_cases hpar : i % 2 = 0
  · -- Even: exact Nat equality, cast preserves it
    exact congrArg _ (gordonPS_step_even hm hi hpar).symm
  · -- Odd: sum = 2m + result, so equal in ZMod (2m)
    have h := gordonPS_step_odd hm hi hpar
    have : ((gordonPS m i + gordonElem m (i + 1) : Nat) : ZMod (2 * m)) =
           ((2 * m + gordonPS m (i + 1) : Nat) : ZMod (2 * m)) := congrArg _ h
    rw [this, Nat.cast_add]
    have h2m : ((2 * m : Nat) : ZMod (2 * m)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_refl _)
    rw [h2m, zero_add]

/-- **Last partial sum is m**: the unique order-2 element of Z/(2m)Z. -/
theorem gordonPS_last {m : Nat} (hm : m ≥ 1) : gordonPS m (2 * m - 2) = m := by
  unfold gordonPS
  rw [if_pos (by omega : (2 * m - 2) % 2 = 0)]
  omega

/-- Gordon elements are surjective onto {1, ..., 2m-1}: every nonzero
    element of Z/(2m)Z appears in the arrangement. -/
theorem gordonElem_surj {m : Nat} (hm : m ≥ 1) {v : Nat}
    (hv1 : 1 ≤ v) (hv2 : v < 2 * m) :
    ∃ i, i < 2 * m - 1 ∧ gordonElem m i = v := by
  by_cases hpar : v % 2 = 0
  · -- v even: use index 2m-v-1 (odd)
    refine ⟨2 * m - v - 1, by omega, ?_⟩
    unfold gordonElem; rw [if_neg (by omega)]; omega
  · -- v odd: use index v-1 (even)
    refine ⟨v - 1, by omega, ?_⟩
    unfold gordonElem; rw [if_pos (by omega)]; omega

/-- Gordon partial sums are surjective onto {1, ..., 2m-1}: every
    nonzero element is a partial sum. -/
theorem gordonPS_surj {m : Nat} (hm : m ≥ 1) {v : Nat}
    (hv1 : 1 ≤ v) (hv2 : v < 2 * m) :
    ∃ i, i < 2 * m - 1 ∧ gordonPS m i = v := by
  by_cases hle : v ≤ m
  · -- v ∈ {1,...,m}: use index 2*(v-1) (even)
    refine ⟨2 * (v - 1), by omega, ?_⟩
    unfold gordonPS; rw [if_pos (by omega)]; omega
  · -- v ∈ {m+1,...,2m-1}: use index 2*(2m-v)-1 (odd)
    refine ⟨2 * (2 * m - v) - 1, by omega, ?_⟩
    unfold gordonPS; rw [if_neg (by omega)]; omega

/-! ## The Pumping Argument: Subgroup Growth Forces Exploration

The key structural insight for mixing: each time a multiplier ESCAPES
the subgroup generated by all previous multipliers, the walk is forced
to visit a state it has never visited before.

Proof idea: if all multipliers m(0),...,m(n-1) are in subgroup H, then
walk positions w(0),...,w(n) are in the coset w(0)·H (by confinement).
If m(n) ∉ H, then w(n+1) = w(n)·m(n) lands in a DIFFERENT coset of H,
so w(n+1) ≠ w(k) for any k ≤ n.

This gives a lower bound on walk exploration: each subgroup growth step
forces a genuinely new state. The gap to full mixing: showing the walk
visits ALL q-1 states, not just one per growth step. -/

/-- **New state from escape**: if all multipliers before step n are in H
    but the n-th multiplier escapes H, the walk at step n+1 visits a
    state never seen at any step k ≤ n. -/
theorem walk_new_state_from_escape {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (H : Subgroup (ZMod q)ˣ)
    {n : Nat}
    (hmult : ∀ k, k < n →
      (Units.mk0 (multZ q k) (multZ_ne_zero hq hne k)) ∈ H)
    (hesc : (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H)
    {k : Nat} (hk : k ≤ n) :
    walkZ q (n + 1) ≠ walkZ q k := by
  obtain ⟨uk, huk, hwk⟩ := prefix_product_in_subgroup hq hne H hmult k hk
  obtain ⟨un, hun, hwn⟩ := prefix_product_in_subgroup hq hne H hmult n (le_refl n)
  intro heq
  have hrec := walkZ_succ q n
  rw [hwn, mul_assoc] at hrec
  rw [heq, hwk] at hrec
  have hval : (uk : ZMod q) = (un : ZMod q) * multZ q n :=
    mul_left_cancel₀ (walkZ_ne_zero hq hne 0) hrec
  have hmult_val : multZ q n = ((un⁻¹ * uk : (ZMod q)ˣ) : ZMod q) := by
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    rw [hval, ← mul_assoc, inv_mul_cancel₀ un.ne_zero, one_mul]
  have hmn : Units.mk0 (multZ q n) (multZ_ne_zero hq hne n) = un⁻¹ * uk := by
    ext; simp only [Units.val_mk0]; exact hmult_val
  exact hesc (hmn ▸ H.mul_mem (H.inv_mem hun) huk)

/-- **First escape gives new state**: SubgroupEscape guarantees that for
    any proper subgroup H, there's a first step where a multiplier
    escapes H. At that step, the walk visits a genuinely new state —
    one it has never visited before. -/
theorem walk_first_escape_new_state {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hse : SubgroupEscape)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ n, ∀ k, k ≤ n → walkZ q (n + 1) ≠ walkZ q k := by
  obtain ⟨n₀, hn₀⟩ := hse q hq hne H hH
  have hexists : ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H := ⟨n₀, hn₀⟩
  classical
  let nf := Nat.find hexists
  have hmult : ∀ k, k < nf → (Units.mk0 (multZ q k) (multZ_ne_zero hq hne k)) ∈ H := by
    intro k hk
    by_contra hc
    exact Nat.find_min hexists hk hc
  exact ⟨nf, fun k hk => walk_new_state_from_escape hq hne H hmult (Nat.find_spec hexists) hk⟩

/-- **Walk escapes every proper coset**: if SubgroupEscape holds, the
    walk cannot be permanently confined to w(0)·H for any proper
    subgroup H < (ZMod q)×. There must exist a step where the walk
    is outside this coset.

    Proof: by contradiction using the confinement theorem. If the walk
    never leaves w(0)·H, then by `confinement_reverse` all multiplier
    residues lie in H, contradicting SubgroupEscape. -/
theorem walk_escapes_coset {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hse : SubgroupEscape)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ n, ∀ u : (ZMod q)ˣ, u ∈ H →
      walkZ q n ≠ walkZ q 0 * (u : ZMod q) := by
  by_contra hall
  push_neg at hall
  exact se_breaks_confinement hq hne hse H hH (confinement_reverse hq hne H hall)

/-! ## Subgroup Growth and Walk Orbit Expansion

The pumping argument shows each escape forces a new state. Here we
make the COSET STRUCTURE explicit: when all multipliers up to step n
are in H, the walk stays in the coset w(0)·H. At step n+1 (escape),
the walk moves to a DIFFERENT coset. This new coset is w(0)·H·m(n),
where m(n) is the escaping multiplier.

Key consequence: if we track a CHAIN of subgroups
  H₀ ⊊ H₁ ⊊ ... ⊊ Hₐ = ⊤
where each Hₖ₊₁ = ⟨Hₖ, m(nₖ)⟩ for some escape step nₖ, then:
1. Each escape forces a genuinely new walk state
2. The walk states at escape points are all pairwise distinct
3. This gives at least d+1 distinct states from d escapes

The chain length d ≥ Ω(q-1) (number of prime factors of q-1 with
multiplicity), so the walk visits at least Ω(q-1)+1 distinct states.

For the gap to full mixing: we'd need to show the walk visits all
q-1 states, not just Ω(q-1)+1. The coset structure suggests an
approach: within each coset, the walk uses sub-multipliers from the
current subgroup, potentially exploring further. -/

/-- **Walk coset membership**: if all multipliers before step n+1 are
    in H, and the walk starts at w(0), then w(n+1) is in the coset
    w(0)·H iff the multiplier at step n is in H.

    More precisely: w(n+1) = w(0) · u · m(n) where u ∈ H. So:
    - If m(n) ∈ H: w(n+1) ∈ w(0)·H
    - If m(n) ∉ H: w(n+1) ∉ w(0)·H (it's in a different coset) -/
theorem walk_in_coset_iff_mult_in_subgroup {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (H : Subgroup (ZMod q)ˣ)
    {n : Nat}
    (hprev : ∀ k, k < n →
      (Units.mk0 (multZ q k) (multZ_ne_zero hq hne k)) ∈ H) :
    (∃ u : (ZMod q)ˣ, u ∈ H ∧ walkZ q (n + 1) = walkZ q 0 * (u : ZMod q)) ↔
    (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∈ H := by
  obtain ⟨un, hun, hwn⟩ := prefix_product_in_subgroup hq hne H hprev n (le_refl n)
  constructor
  · -- (→) w(n+1) ∈ w(0)·H implies m(n) ∈ H
    intro ⟨v, hv, hwn1⟩
    have hrec := walkZ_succ q n
    rw [hwn, mul_assoc] at hrec
    rw [hwn1] at hrec
    have hval : (v : ZMod q) = (un : ZMod q) * multZ q n :=
      mul_left_cancel₀ (walkZ_ne_zero hq hne 0) hrec
    have hmult_eq : Units.mk0 (multZ q n) (multZ_ne_zero hq hne n) = un⁻¹ * v := by
      ext
      simp only [Units.val_mk0, Units.val_mul, Units.val_inv_eq_inv_val]
      rw [hval, ← mul_assoc, inv_mul_cancel₀ un.ne_zero, one_mul]
    rw [hmult_eq]
    exact H.mul_mem (H.inv_mem hun) hv
  · -- (←) m(n) ∈ H implies w(n+1) ∈ w(0)·H
    intro hmn
    exact ⟨un * Units.mk0 (multZ q n) (multZ_ne_zero hq hne n),
           H.mul_mem hun hmn, by
             rw [walkZ_succ, hwn, Units.val_mul, Units.val_mk0, mul_assoc]⟩

/-- **Two escapes give three distinct states**: if the walk has escape
    points at steps n₁ and n₂ (from nested subgroups H₁ ⊆ H₂), then
    the walk states w(0), w(n₁+1), and w(n₂+1) are pairwise distinct.

    This is the first step of the orbit expansion: each escape point
    contributes a genuinely new walk state. -/
theorem walk_two_escapes_three_states {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (H₁ H₂ : Subgroup (ZMod q)ˣ)
    {n₁ n₂ : Nat} (hn : n₁ < n₂)
    -- All mults before n₁ are in H₁
    (hm1 : ∀ k, k < n₁ →
      (Units.mk0 (multZ q k) (multZ_ne_zero hq hne k)) ∈ H₁)
    -- Mult at n₁ escapes H₁
    (hesc1 : (Units.mk0 (multZ q n₁) (multZ_ne_zero hq hne n₁)) ∉ H₁)
    -- All mults before n₂ are in H₂
    (hm2 : ∀ k, k < n₂ →
      (Units.mk0 (multZ q k) (multZ_ne_zero hq hne k)) ∈ H₂)
    -- Mult at n₂ escapes H₂
    (hesc2 : (Units.mk0 (multZ q n₂) (multZ_ne_zero hq hne n₂)) ∉ H₂) :
    -- Three pairwise distinct states
    walkZ q (n₁ + 1) ≠ walkZ q 0 ∧
    walkZ q (n₂ + 1) ≠ walkZ q 0 ∧
    walkZ q (n₁ + 1) ≠ walkZ q (n₂ + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · -- w(n₁+1) ≠ w(0): follows from escape at n₁
    exact walk_new_state_from_escape hq hne H₁ hm1 hesc1 (Nat.zero_le n₁)
  · -- w(n₂+1) ≠ w(0): follows from escape at n₂
    exact walk_new_state_from_escape hq hne H₂ hm2 hesc2 (Nat.zero_le n₂)
  · -- w(n₁+1) ≠ w(n₂+1): n₁+1 ≤ n₂ (since n₁ < n₂), so escape at n₂ gives new state
    exact (walk_new_state_from_escape hq hne H₂ hm2 hesc2 (by omega)).symm

/-- **Gordon's Theorem for Cyclic Groups**: Z/(2m)Z is sequenceable
    for all m ≥ 1. The functions gordonElem and gordonPS give explicit
    bijections {0,...,2m-2} → {1,...,2m-1} satisfying the partial sum
    recurrence in Z/(2m)Z, with last partial sum equal to m (the unique
    element of order 2).

    For odd prime q, (ZMod q)× is cyclic of order q-1 = 2·((q-1)/2),
    so it is sequenceable: there exists an arrangement of all nonidentity
    elements whose partial products cover the entire group. This is the
    algebraic capacity needed for the MixingHypothesis. -/
theorem gordon_sequenceable (m : Nat) (hm : m ≥ 1) :
    -- Elements biject onto {1,...,2m-1}
    (∀ i, i < 2*m - 1 → 1 ≤ gordonElem m i ∧ gordonElem m i < 2*m) ∧
    (∀ i j, i < 2*m - 1 → j < 2*m - 1 → gordonElem m i = gordonElem m j → i = j) ∧
    (∀ v, 1 ≤ v → v < 2*m → ∃ i, i < 2*m - 1 ∧ gordonElem m i = v) ∧
    -- Partial sums biject onto {1,...,2m-1}
    (∀ i, i < 2*m - 1 → 1 ≤ gordonPS m i ∧ gordonPS m i < 2*m) ∧
    (∀ i j, i < 2*m - 1 → j < 2*m - 1 → gordonPS m i = gordonPS m j → i = j) ∧
    (∀ v, 1 ≤ v → v < 2*m → ∃ i, i < 2*m - 1 ∧ gordonPS m i = v) ∧
    -- Recurrence: ps(i+1) = ps(i) + elem(i+1) in Z/(2m)Z
    gordonPS m 0 = gordonElem m 0 ∧
    (∀ i, i + 1 < 2*m - 1 →
      (gordonPS m (i + 1) : ZMod (2*m)) =
      (gordonPS m i : ZMod (2*m)) + (gordonElem m (i + 1) : ZMod (2*m))) ∧
    -- Last partial sum is m (the order-2 element, corresponding to -1)
    gordonPS m (2*m - 2) = m :=
  ⟨fun _i hi => gordonElem_bounds hm hi,
   fun _i _j hi hj heq => gordonElem_inj hm hi hj heq,
   fun _v hv1 hv2 => gordonElem_surj hm hv1 hv2,
   fun _i hi => gordonPS_bounds hm hi,
   fun _i _j hi hj heq => gordonPS_inj hm hi hj heq,
   fun _v hv1 hv2 => gordonPS_surj hm hv1 hv2,
   gordonPS_zero m hm,
   fun _i hi => gordonPS_step hm hi,
   gordonPS_last hm⟩


end MullinGroup
