import EM.EquidistSelfAvoidance
import EM.MullinGroupQR

/-!
# Character Non-Vanishing, Power Residue Escape, and Local PRE

* Greedy sieve constraint (Strategy E)
* Large-ℓ SE reduction
* Character non-vanishing (Strategy C): `se_iff_char_detection`
* Power Residue Decomposition: PRE ↔ SE
* Local PRE decomposition and automatic escape
* Effective Kummer Escape
-/

open Mullin Euclid MullinGroup RotorRouter


/-! ## Section 6: Greedy Sieve Constraint (Strategy E)

If SubgroupEscape fails at a prime q — i.e., all multiplier residues lie in a proper
subgroup H of (ZMod q)ˣ — then the **greedy** nature of the EM sequence (selecting
minFac, the smallest prime factor) imposes a strong constraint: any prime factor of
prod(n)+1 whose residue mod q falls *outside* H must be strictly larger than seq(n+1).

In other words, confinement forces the greedy choice to always select from the "allowed"
residue classes (those in H), because any "disallowed" prime factor is shadowed by a
smaller one that IS in H.

This is the *sieve constraint* from Strategy E: the greedy selection process can't
be permanently biased toward a proper subgroup without every prod(n)+1 having a
specific factorization structure — all small factors in H mod q. -/

section GreedySieveConstraint

/-- Cast of prod(n)+1 into ZMod q equals walkZ q n + 1. -/
theorem walk_add_one_cast (q n : Nat) :
    (↑(prod n + 1) : ZMod q) = walkZ q n + 1 := by
  simp [walkZ, Nat.cast_add]

/-- **Greedy sieve constraint**: if all multipliers are confined to a proper
    subgroup H, and a prime p divides prod(n)+1 with p having a *different*
    ZMod q residue from seq(n+1), then seq(n+1) < p.

    The proof is simple: seq(n+1) = minFac(prod(n)+1) ≤ p (minimality),
    and seq(n+1) ≠ p (different residues mod q), so strict inequality.

    The power of this theorem is in its *application*: under confinement,
    multZ q n ∈ H, so any prime factor p with p mod q ∉ H has a different
    residue from seq(n+1), and hence is strictly larger. The greedy choice
    always picks from H's residue classes. -/
theorem greedy_factor_bound {q : Nat}
    {n : Nat} {p : Nat} (hp : IsPrime p)
    (hdvd : p ∣ prod n + 1)
    (hne_res : (↑p : ZMod q) ≠ (↑(seq (n + 1)) : ZMod q)) :
    seq (n + 1) < p := by
  -- seq(n+1) = minFac(prod n + 1)
  have hseq : seq (n + 1) = minFac (prod n + 1) := seq_succ n
  -- minFac(prod n + 1) ≤ p since p | prod n + 1 and p ≥ 2
  have hle : minFac (prod n + 1) ≤ p :=
    minFac_min' _ _ (by have := prod_ge_two n; omega) hp.1 hdvd
  -- seq(n+1) ≠ p since they have different residues mod q
  have hne : seq (n + 1) ≠ p := by
    intro heq; exact hne_res (by rw [heq])
  omega

/-- **Confinement blocks outside factors**: if all multipliers lie in H
    and a prime p divides prod(n)+1 with p mod q being a unit NOT in H,
    then seq(n+1) < p.

    This is the subgroup-specific version: under confinement, any prime
    factor of prod(n)+1 outside H is shadowed by the greedy choice. -/
theorem confinement_blocks_outside_factor {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {H : Subgroup (ZMod q)ˣ}
    (hconf : ∀ k, (Units.mk0 (multZ q k) (multZ_ne_zero hq hne k)) ∈ H)
    {n : Nat} {p : Nat} (hp : IsPrime p) (hdvd : p ∣ prod n + 1)
    (hp_ne_zero : (↑p : ZMod q) ≠ 0)
    (hout : Units.mk0 (↑p : ZMod q) hp_ne_zero ∉ H) :
    seq (n + 1) < p := by
  apply greedy_factor_bound hp hdvd
  -- Need: (↑p : ZMod q) ≠ (↑(seq (n + 1)) : ZMod q)
  intro heq
  -- Under confinement, multZ q n ∈ H (as unit)
  have hmem := hconf n
  -- multZ q n = (seq(n+1) : ZMod q) by definition
  have hmult_eq : multZ q n = (↑(seq (n + 1)) : ZMod q) := by
    simp [multZ]
  -- So (↑p : ZMod q) = multZ q n
  rw [← hmult_eq] at heq
  -- Therefore Units.mk0 p _ = Units.mk0 (multZ q n) _
  have hunit_eq : Units.mk0 (↑p : ZMod q) hp_ne_zero =
      Units.mk0 (multZ q n) (multZ_ne_zero hq hne n) := by
    ext; simp only [Units.val_mk0]; exact heq
  -- But Units.mk0 (multZ q n) _ ∈ H, so Units.mk0 p _ ∈ H
  rw [hunit_eq] at hout
  exact hout hmem

/-- **Confinement constrains walk targets**: if all mults ∈ H, the walk
    values walkZ q n + 1 (= prod(n)+1 mod q) lie in the set
    {walkZ q 0 * u + 1 : u ∈ H}. This is the "target set" that prod(n)+1
    must reduce to modulo q. -/
theorem confinement_target_set {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {H : Subgroup (ZMod q)ˣ}
    (hconf : ∀ k, (Units.mk0 (multZ q k) (multZ_ne_zero hq hne k)) ∈ H)
    (n : Nat) :
    ∃ u : (ZMod q)ˣ, u ∈ H ∧
      (↑(prod n + 1) : ZMod q) = walkZ q 0 * (u : ZMod q) + 1 := by
  obtain ⟨u, hu, hwalk⟩ := confinement_forward hq hne H hconf n
  exact ⟨u, hu, by rw [walk_add_one_cast, hwalk]⟩

/-- **Hitting requires coset membership**: if all mults ∈ H and the walk
    hits -1 at step n, then -1 is in the confined coset walkZ(0)·H.

    Contrapositively: if -1 ∉ walkZ(0)·H, the walk NEVER hits -1,
    meaning q can never divide prod(n)+1. This means HH fails at q,
    so q never enters the sequence through the walk mechanism. -/
theorem hitting_requires_coset_membership {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {H : Subgroup (ZMod q)ˣ}
    (hconf : ∀ k, (Units.mk0 (multZ q k) (multZ_ne_zero hq hne k)) ∈ H)
    {n : Nat} (hhit : walkZ q n = -1) :
    ∃ u : (ZMod q)ˣ, u ∈ H ∧ walkZ q 0 * (u : ZMod q) = -1 := by
  obtain ⟨u, hu, hwalk⟩ := confinement_forward hq hne H hconf n
  exact ⟨u, hu, hwalk.symm.trans hhit⟩

/-- **SE from a witnessed outside factor**: if for some n, prod(n)+1
    has a prime factor p whose residue mod q is a unit outside H,
    then the multiplier at step n escapes H — proving SE for H. -/
theorem se_of_outside_factor {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {H : Subgroup (ZMod q)ˣ}
    {n : Nat} {p : Nat} (hp : IsPrime p) (hdvd : p ∣ prod n + 1)
    (hp_ne_zero : (↑p : ZMod q) ≠ 0)
    (hout : Units.mk0 (↑p : ZMod q) hp_ne_zero ∉ H)
    (hle : p ≤ seq (n + 1)) :
    ∃ m, (Units.mk0 (multZ q m) (multZ_ne_zero hq hne m)) ∉ H := by
  refine ⟨n, fun hmem => ?_⟩
  -- p ≤ seq(n+1) and seq(n+1) = minFac(prod n + 1) ≤ p, so p = seq(n+1)
  have hseq : seq (n + 1) = minFac (prod n + 1) := seq_succ n
  have hle' : minFac (prod n + 1) ≤ p :=
    minFac_min' _ _ (by have := prod_ge_two n; omega) hp.1 hdvd
  have heq : p = seq (n + 1) := by omega
  -- So (↑p : ZMod q) = multZ q n
  have hcast : (↑p : ZMod q) = multZ q n := by
    simp [multZ, heq]
  -- Transfer membership
  have hunit : Units.mk0 (↑p : ZMod q) hp_ne_zero =
      Units.mk0 (multZ q n) (multZ_ne_zero hq hne n) := by
    ext; exact hcast
  rw [hunit] at hout
  exact hout hmem

/-- **SE from any factor matching the greedy choice**: if seq(n+1) itself
    has residue outside H (mod q), then SE holds at H.

    This is the direct version: the multiplier IS seq(n+1), so if
    seq(n+1) mod q ∉ H, the multiplier at step n escapes H. -/
theorem se_of_seq_outside {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {H : Subgroup (ZMod q)ˣ}
    {n : Nat}
    (hne_zero : (↑(seq (n + 1)) : ZMod q) ≠ 0)
    (hout : Units.mk0 (↑(seq (n + 1)) : ZMod q) hne_zero ∉ H) :
    ∃ m, (Units.mk0 (multZ q m) (multZ_ne_zero hq hne m)) ∉ H := by
  refine ⟨n, fun hmem => ?_⟩
  have : Units.mk0 (↑(seq (n + 1)) : ZMod q) hne_zero =
      Units.mk0 (multZ q n) (multZ_ne_zero hq hne n) := by
    ext; simp [multZ]
  rw [this] at hout
  exact hout hmem

/-- **The contrapositive sieve principle**: if SE fails at q (all mults
    confined to some H ⊊ (ZMod q)ˣ), then for EVERY n and every prime p
    dividing prod(n)+1 with p ≠ q, either:
    (a) p mod q ∈ H (the factor is "allowed"), or
    (b) seq(n+1) < p (the factor is shadowed by a smaller allowed one).

    This is an infinite family of constraints: the factorization of every
    prod(n)+1 must have its smallest factor in the "allowed" residue
    classes mod q. Breaking even ONE such constraint proves SE. -/
theorem se_failure_factor_dichotomy {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {H : Subgroup (ZMod q)ˣ} (_hH : H ≠ ⊤)
    (hfail : ¬∃ m, (Units.mk0 (multZ q m) (multZ_ne_zero hq hne m)) ∉ H)
    {n : Nat} {p : Nat} (hp : IsPrime p) (hdvd : p ∣ prod n + 1)
    (hp_ne_zero : (↑p : ZMod q) ≠ 0) :
    Units.mk0 (↑p : ZMod q) hp_ne_zero ∈ H ∨ seq (n + 1) < p := by
  by_contra h
  push_neg at h
  obtain ⟨hout, hle⟩ := h
  exact hfail (se_of_outside_factor hq hne hp hdvd hp_ne_zero hout (by omega))

/-- **q is always shadowed as a factor**: if q is a prime not in the
    sequence and q | prod(n)+1, then seq(n+1) < q. The greedy choice
    always picks something smaller than q.

    This is fundamental: q mod q = 0, but multZ q n ≠ 0 (since q ∉ seq),
    so seq(n+1) ≠ q. Combined with minFac(prod(n)+1) ≤ q (since q | prod(n)+1),
    we get strict inequality. -/
theorem q_factor_always_shadowed {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {n : Nat} (hdvd : q ∣ prod n + 1) :
    seq (n + 1) < q := by
  have hseq : seq (n + 1) = minFac (prod n + 1) := seq_succ n
  have hle : minFac (prod n + 1) ≤ q :=
    minFac_min' _ _ (by have := prod_ge_two n; omega) hq.1 hdvd
  have hne_q : seq (n + 1) ≠ q := by
    intro heq
    have h0 : (↑(seq (n + 1)) : ZMod q) = 0 := by
      rw [heq]; exact CharP.cast_eq_zero (ZMod q) q
    exact (multZ_ne_zero hq hne n) (by simp [multZ, h0])
  omega

end GreedySieveConstraint

/-! ## Section 7: Large-ℓ SE Reduction

The `eight_elts_escape_order_le_seven` theorem handles subgroups of order ≤ 7.
Combined with `se_of_maximal_escape`, this reduces SubgroupEscape at q (for q ≥ 59)
to escaping only the "large" maximal subgroups — those of order > 7.

In a cyclic group like (ZMod q)ˣ, maximal subgroups have prime index. A maximal
subgroup of index ℓ has order (q-1)/ℓ. For order > 7, we need ℓ < (q-1)/7.
So SE reduces to: for each prime ℓ | q-1 with ℓ < (q-1)/7, escape the index-ℓ
maximal subgroup. This is a finite check, bounded by the number of prime
factors of q-1 (at most log₂(q-1)). -/

section LargeEllReduction

open Classical in
/-- **SE from large subgroup escape**: for q ≥ 59, to prove SE it suffices to
    escape every proper subgroup of order > 7. Subgroups of order ≤ 7 are
    handled automatically by `eight_elts_escape_order_le_seven`. -/
theorem se_of_large_subgroup_escape {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (hq59 : 59 ≤ q)
    (hesc : ∀ (H : Subgroup (ZMod q)ˣ), H ≠ ⊤ → 7 < Fintype.card H →
      ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H) :
    ∀ (H : Subgroup (ZMod q)ˣ), H ≠ ⊤ →
      ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H := by
  intro H hH
  by_cases hcard : Fintype.card H ≤ 7
  · obtain ⟨n, _, hn⟩ := eight_elts_escape_order_le_seven hq hne hq59 H hcard
    exact ⟨n, hn⟩
  · exact hesc H hH (by omega)

open Classical in
/-- **SE from maximal large escape**: for q ≥ 59, SE holds if every maximal
    subgroup (coatom) of order > 7 is escaped.

    This is the sharpest reduction: instead of ALL proper subgroups of order > 7,
    we only need to check MAXIMAL ones (coatoms). Since (ZMod q)ˣ is cyclic,
    its coatoms have prime index ℓ | q-1, and order > 7 means ℓ < (q-1)/7.

    So SE at q reduces to: for each prime ℓ | q-1 with (q-1)/ℓ > 7,
    escape the index-ℓ maximal subgroup. -/
theorem se_of_maximal_large_escape {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (hq59 : 59 ≤ q)
    (hesc : ∀ (M : Subgroup (ZMod q)ˣ), IsCoatom M → 7 < Fintype.card M →
      ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ M) :
    ∀ (H : Subgroup (ZMod q)ˣ), H ≠ ⊤ →
      ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H := by
  apply se_of_maximal_escape hq hne
  intro M hM
  by_cases hcard : Fintype.card M ≤ 7
  · obtain ⟨n, _, hn⟩ := eight_elts_escape_order_le_seven hq hne hq59 M hcard
    exact ⟨n, hn⟩
  · exact hesc M hM (by omega)

open Classical in
/-- **Small primes suffice for SE**: for q ≥ 59, SE holds if every proper
    subgroup of order > 7 has an escaping multiplier among the first 7 mults
    (indices 0..6, corresponding to seq values 3,7,43,13,53,5,6221671).

    This reduces SE verification to: for each "large" proper subgroup H
    (|H| > 7), check that at least one of 7 specific residues is not in H. -/
theorem se_of_seven_mults_escape_large {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (hq59 : 59 ≤ q)
    (hesc : ∀ (H : Subgroup (ZMod q)ˣ), H ≠ ⊤ → 7 < Fintype.card H →
      ∃ n, n < 7 ∧ (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H) :
    ∀ (H : Subgroup (ZMod q)ˣ), H ≠ ⊤ →
      ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H := by
  apply se_of_large_subgroup_escape hq hne hq59
  intro H hH hcard
  obtain ⟨n, _, hn⟩ := hesc H hH hcard
  exact ⟨n, hn⟩

end LargeEllReduction

/-! ## Section 8: Character Non-Vanishing (Strategy C)

The character (dual) perspective reformulates SubgroupEscape in terms of
group homomorphisms. Instead of "does every proper subgroup miss some
multiplier?", we ask "does every non-trivial homomorphism detect some
multiplier?"

### Key results

* `char_walk_product`: χ(w(n)) = χ(w(0)) · ∏_{k<n} χ(m(k))
* `char_annihilation_walk_const`: all χ(m(k)) = 1 → χ(w) constant
* `se_implies_char_nonvanishing`: SE → every non-trivial χ detects some mult
* `char_nonvanishing_implies_se`: character detection → SE (via quotient maps)
* `se_iff_char_detection`: the full SE ↔ character duality

### Perspective

The character product formula converts the multiplicative walk recurrence
into a cumulative product in the character's codomain. Character annihilation
(all χ(m(k)) = 1) corresponds exactly to multiplier confinement in ker(χ).

For `(ZMod q)ˣ` (cyclic of order q-1), the characters are powers of a
primitive character, and SE becomes: no non-trivial character annihilates
the multiplier sequence. This is dual to: the multiplier residues generate
the full group. -/

section CharacterNonVanishing

/-- **Character product formula**: applying a group homomorphism χ to the
    walk recurrence gives a telescoping product:
    χ(w(n)) = χ(w(0)) · ∏_{k<n} χ(m(k)).

    This is the fundamental structural identity for the character perspective:
    the walk's image under any homomorphism factors as the initial value
    times a cumulative product of character values on multipliers. -/
theorem char_walk_product {G : Type*} [CommMonoid G]
    {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* G) (n : Nat) :
    χ (emWalkUnit q hq hne n) =
      χ (emWalkUnit q hq hne 0) *
        (Finset.range n).prod (fun k => χ (emMultUnit q hq hne k)) := by
  induction n with
  | zero => simp [Finset.range_zero, Finset.prod_empty]
  | succ n ih =>
    rw [emWalkUnit_succ, map_mul, ih, Finset.prod_range_succ, mul_assoc]

/-- **Walk constant under character annihilation**: if χ maps all multipliers
    to 1, then χ(w(n)) = χ(w(0)) for all n — the walk is confined to a
    single fiber of χ.

    If χ = mk'(H) for a subgroup H, this means the walk stays in a single
    coset of H — recovering the confinement theorem from the character
    perspective. -/
theorem char_annihilation_walk_const {G : Type*} [CommMonoid G]
    {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* G)
    (hann : ∀ k, χ (emMultUnit q hq hne k) = 1) (n : Nat) :
    χ (emWalkUnit q hq hne n) = χ (emWalkUnit q hq hne 0) := by
  rw [char_walk_product hq hne χ n, Finset.prod_eq_one (fun k _ => hann k), mul_one]

/-- **Character annihilation means kernel confinement**: if χ annihilates
    all multipliers, every multiplier lies in ker(χ). This is the
    character-theoretic statement of "all mults confined to a subgroup." -/
theorem char_annihilation_confinement {G : Type*} [CommGroup G]
    {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* G)
    (hann : ∀ k, χ (emMultUnit q hq hne k) = 1) :
    ∀ k, emMultUnit q hq hne k ∈ MonoidHom.ker χ :=
  fun k => MonoidHom.mem_ker.mpr (hann k)

/-- **Walk variation implies character non-annihilation**: if the walk image
    under χ ever differs from χ(w(0)), then some multiplier has χ(mₖ) ≠ 1.

    Contrapositive of `char_annihilation_walk_const`. This provides a
    detection method: to prove SE, find χ and n with χ(w(n)) ≠ χ(w(0)). -/
theorem walk_variation_char_nontrivial {G : Type*} [CommMonoid G]
    {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* G)
    {n : Nat} (hvar : χ (emWalkUnit q hq hne n) ≠ χ (emWalkUnit q hq hne 0)) :
    ∃ k, χ (emMultUnit q hq hne k) ≠ 1 := by
  by_contra h
  push_neg at h
  exact hvar (char_annihilation_walk_const hq hne χ h n)

/-- **Character displacement formula**: the cumulative product of character
    values on multipliers equals the walk displacement under χ:
    ∏_{k<n} χ(mₖ) = χ(w(n)) · χ(w(0))⁻¹.

    This isolates the cumulative character product from the initial condition,
    expressing it as a "displacement" in the character's target group. -/
theorem char_displacement {G : Type*} [CommGroup G]
    {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* G) (n : Nat) :
    (Finset.range n).prod (fun k => χ (emMultUnit q hq hne k)) =
      χ (emWalkUnit q hq hne n) * (χ (emWalkUnit q hq hne 0))⁻¹ := by
  have h := char_walk_product hq hne χ n
  rw [h, mul_comm (χ (emWalkUnit q hq hne 0)), mul_inv_cancel_right]

/-- **SE → character non-vanishing**: SubgroupEscape implies that every
    group homomorphism with proper kernel detects some multiplier.

    Given a non-trivial χ (ker(χ) ⊊ (ZMod q)ˣ), SE provides a multiplier
    outside ker(χ), hence χ(mₖ) ≠ 1. -/
theorem se_implies_char_nonvanishing
    {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hse : ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      ∃ n, emMultUnit q hq hne n ∉ H)
    {G : Type*} [CommGroup G]
    (χ : (ZMod q)ˣ →* G) (hχ : MonoidHom.ker χ ≠ ⊤) :
    ∃ k, χ (emMultUnit q hq hne k) ≠ 1 := by
  obtain ⟨n, hn⟩ := hse _ hχ
  exact ⟨n, fun h => hn (MonoidHom.mem_ker.mpr h)⟩

/-- **Character non-vanishing → SE**: if every quotient map detects some
    multiplier (mk'(H)(mₖ) ≠ 1 for some k), then SubgroupEscape holds.

    Uses `QuotientGroup.ker_mk'`: the kernel of the canonical quotient map
    `mk' H : G →* G ⧸ H` is exactly H. So mk'(H)(x) ≠ 1 iff x ∉ H. -/
theorem char_nonvanishing_implies_se
    {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hchar : ∀ (H : Subgroup (ZMod q)ˣ), H ≠ ⊤ →
      ∃ k, QuotientGroup.mk' H (emMultUnit q hq hne k) ≠ 1) :
    ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      ∃ n, emMultUnit q hq hne n ∉ H := by
  intro H hH
  obtain ⟨k, hk⟩ := hchar H hH
  exact ⟨k, fun hmem => hk (by
    have : emMultUnit q hq hne k ∈ MonoidHom.ker (QuotientGroup.mk' H) := by
      rw [QuotientGroup.ker_mk']; exact hmem
    exact MonoidHom.mem_ker.mp this)⟩

/-- **SE ↔ character detection**: SubgroupEscape at q is equivalent to
    every quotient map detecting some multiplier. This is the fundamental
    duality between the subgroup perspective and the character perspective.

    The forward direction applies to ANY group homomorphism with proper kernel.
    The backward direction uses the canonical quotient map mk'(H) to witness
    escape from each proper subgroup H. -/
theorem se_iff_char_detection
    {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) :
    (∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      ∃ n, emMultUnit q hq hne n ∉ H) ↔
    (∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      ∃ k, QuotientGroup.mk' H (emMultUnit q hq hne k) ≠ 1) := by
  constructor
  · intro hse H hH
    obtain ⟨n, hn⟩ := hse H hH
    exact ⟨n, fun h => hn (by rw [← QuotientGroup.ker_mk' H]; exact MonoidHom.mem_ker.mpr h)⟩
  · exact fun hchar => char_nonvanishing_implies_se hq hne hchar

/-- **Confinement ↔ quotient annihilation**: all multipliers lie in H iff
    the quotient map mk'(H) annihilates all multipliers. This is the
    bridge between the subgroup-theoretic and character-theoretic viewpoints,
    applied to a single subgroup. -/
theorem confinement_iff_quotient_annihilation
    {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (H : Subgroup (ZMod q)ˣ) :
    (∀ k, emMultUnit q hq hne k ∈ H) ↔
    (∀ k, QuotientGroup.mk' H (emMultUnit q hq hne k) = 1) := by
  simp only [← MonoidHom.mem_ker, QuotientGroup.ker_mk']

end CharacterNonVanishing

/-! ## Section 9: Power Residue Decomposition (Strategy E)

SubgroupEscape decomposes into independent power-residue conditions per prime
factor of the group order. For `(ZMod q)ˣ` (cyclic of order q-1), SE at q is
equivalent to: for each prime ℓ | q-1, some multiplier is not an ℓ-th power
residue mod q.

### Key results

* `PowerResidueEscape`: the power-residue decomposition of SE (global)
* `pre_implies_se`: PowerResidueEscape → SubgroupEscape
* `se_implies_pre`: SubgroupEscape → PowerResidueEscape (uses cyclicity)
* `pre_iff_se`: full equivalence PRE ↔ SE
* `pre_empr_implies_mc`: PRE + EMPR → MullinConjecture

### Perspective

The equivalence PRE ↔ SE replaces the infinitary subgroup quantifier (∀ H proper)
with a finite conjunction over prime factors of q-1 (∀ ℓ | q-1). This makes
SE accessible to sieve methods: showing that the first few multipliers are
not all ℓ-th power residues for each small ℓ.

The QR obstruction theorem (`se_qr_obstruction`) already handles ℓ = 2 for
most primes. The PRE formulation extends this to higher power residues
(cubic, quintic, etc.) and quantifies exactly what remains to prove. -/

section PowerResidueDecomposition

/-- **Power Residue Escape**: for every prime q not in the EM sequence and
    every prime ℓ dividing q-1, some multiplier residue is not an ℓ-th power
    residue mod q.

    This decomposes SubgroupEscape into independent conditions per prime
    factor of the group order. It is the natural "sieve target": sieve methods
    can attack each prime power residue condition independently.

    Equivalently: for each prime ℓ | q-1, the multipliers are not all confined
    to the unique subgroup of index ℓ in the cyclic group (ZMod q)ˣ. -/
def PowerResidueEscape : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)],
  ∀ (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ ℓ ∈ (q - 1).primeFactors,
    ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ^ ((q - 1) / ℓ) ≠ 1

/-- **PRE → SE**: power residue escape implies subgroup escape.
    This direction uses only Lagrange's theorem (no cyclicity needed).

    Each proper subgroup H has |H| < q-1, so its index has some prime factor ℓ.
    All elements of H satisfy x^((q-1)/ℓ) = 1 (since |H| divides (q-1)/ℓ).
    PRE gives a multiplier with m^((q-1)/ℓ) ≠ 1, witnessing m ∉ H. -/
theorem pre_implies_se : PowerResidueEscape → SubgroupEscape := by
  intro hpre q _ hq hne H hH
  exact se_of_prime_index_escape hq hne (fun ℓ hℓ => hpre q hq hne ℓ hℓ) H hH

open Classical in
/-- **SE → PRE**: subgroup escape implies power residue escape.
    This direction uses cyclicity of `(ZMod q)ˣ`.

    For prime ℓ | q-1, the power kernel K = {x | x^((q-1)/ℓ) = 1} is a
    subgroup. In the cyclic group (ZMod q)ˣ, any generator g has
    orderOf g = q-1, so g^((q-1)/ℓ) ≠ 1 (since (q-1)/ℓ < orderOf g).
    Thus K ≠ ⊤, and SE provides a multiplier outside K. -/
theorem se_implies_pre : SubgroupEscape → PowerResidueEscape := by
  intro hse q inst hq hne ℓ hℓ
  -- Extract ℓ data
  have hqm1_ne : q - 1 ≠ 0 := by have := inst.out.one_lt; omega
  have hℓ_data := (Nat.mem_primeFactors_of_ne_zero hqm1_ne).mp hℓ
  have hℓ_prime : ℓ.Prime := hℓ_data.1
  have hℓ_dvd : ℓ ∣ q - 1 := hℓ_data.2
  have hqm1_pos : 0 < q - 1 := by omega
  have hd_pos : 0 < (q - 1) / ℓ :=
    Nat.div_pos (Nat.le_of_dvd hqm1_pos hℓ_dvd) hℓ_prime.pos
  have hd_lt : (q - 1) / ℓ < q - 1 := Nat.div_lt_self hqm1_pos hℓ_prime.one_lt
  -- Construct the ℓ-th power kernel subgroup
  let K : Subgroup (ZMod q)ˣ :=
    { carrier := {x | x ^ ((q - 1) / ℓ) = 1}
      one_mem' := one_pow _
      mul_mem' := fun {a b} (ha : a ^ _ = 1) (hb : b ^ _ = 1) => by
        show (a * b) ^ _ = 1; rw [mul_pow, ha, hb, one_mul]
      inv_mem' := fun {a} (ha : a ^ _ = 1) => by
        show a⁻¹ ^ _ = 1; rw [inv_pow, ha, inv_one] }
  -- K is proper: a cyclic generator escapes it
  have hK_ne_top : K ≠ ⊤ := by
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp
      (inferInstance : IsCyclic (ZMod q)ˣ)
    have hord : orderOf g = q - 1 := by
      rw [hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime inst.out]
    intro heq
    have hg_mem : g ∈ K := heq ▸ Subgroup.mem_top g
    change g ^ ((q - 1) / ℓ) = 1 at hg_mem
    have : orderOf g ∣ (q - 1) / ℓ := orderOf_dvd_of_pow_eq_one hg_mem
    rw [hord] at this
    exact absurd (Nat.le_of_dvd hd_pos this) (by omega)
  -- SE gives escape from K
  obtain ⟨n, hn⟩ := hse q hq hne K hK_ne_top
  exact ⟨n, hn⟩

/-- **PRE ↔ SE**: power residue escape is equivalent to subgroup escape.
    The forward direction uses Lagrange's theorem; the backward direction
    uses cyclicity of (ZMod q)ˣ to show each power kernel is proper. -/
theorem pre_iff_se : PowerResidueEscape ↔ SubgroupEscape :=
  ⟨pre_implies_se, se_implies_pre⟩

/-- **PRE + EMPR → MC**: power residue escape combined with the walk
    recurrence hypothesis implies Mullin's Conjecture.

    This factors through SE: PRE → SE, then SE + EMPR → MC via the
    established reduction in MullinRotorBridge. -/
theorem pre_empr_implies_mc :
    PowerResidueEscape → EMPointwiseRecurrence → MullinConjecture := by
  intro hpre hempr
  exact empr_se_implies_mullin hempr (pre_implies_se hpre)

end PowerResidueDecomposition

/-! ## Section 10: Local PRE Decomposition & Automatic Escape for Large ℓ

When ℓ is a large prime factor of q-1 (meaning (q-1)/ℓ ≤ 7), the ℓ-th power
kernel {x | x^((q-1)/ℓ) = 1} has small order and is automatically escaped by
the 8 known elements {1,3,5,7,13,43,53,21}. This reduces SubgroupEscape from
"escape every proper subgroup" to checking only finitely many small primes ℓ
where the kernel order exceeds 7.

### Key results

* `PRE_at`: local per-prime-factor power residue escape condition
* `pre_at_of_small_kernel`: automatic PRE for ℓ with (q-1)/ℓ ≤ 7
* `se_of_small_pre`: SE reduces to PRE at prime factors with large kernels only
* `not_pre_at_iff_all_pow_eq_one`: PRE failure = all multipliers are ℓ-th
  power residues
* `se_failure_requires_small_obstruction`: SE failure at q ≥ 59 forces some
  small prime ℓ where all multipliers are ℓ-th power residues -/

section LocalPRE

/-- Local per-prime-factor power residue escape at specific q and ℓ.
    PRE_at q ℓ asserts that some multiplier is not an ℓ-th power residue mod q,
    i.e., some multiplier raised to (q-1)/ℓ is not 1. -/
def PRE_at (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (ℓ : Nat) : Prop :=
  ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ^ ((q - 1) / ℓ) ≠ 1

open Classical in
/-- **Automatic PRE for large ℓ**: when the ℓ-th power kernel has order ≤ 7,
    PRE_at holds automatically.

    The kernel K = {x | x^((q-1)/ℓ) = 1} has order (q-1)/ℓ in the cyclic
    group (ZMod q)ˣ (by `IsCyclic.card_powMonoidHom_ker` and the fact that
    (q-1)/ℓ divides q-1). When this is ≤ 7, the 8 known elements escape
    by `eight_elts_escape_order_le_seven`. -/
theorem pre_at_of_small_kernel {q : Nat} [inst : Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (hq59 : q ≥ 59)
    {ℓ : Nat} (hℓ_dvd : ℓ ∣ q - 1) (hsmall : (q - 1) / ℓ ≤ 7) :
    PRE_at q hq hne ℓ := by
  set d := (q - 1) / ℓ with hd_def
  -- The ℓ-th power kernel K = {x | x^d = 1}
  let K : Subgroup (ZMod q)ˣ :=
    { carrier := {x | x ^ d = 1}
      one_mem' := one_pow _
      mul_mem' := fun {a b} (ha : a ^ _ = 1) (hb : b ^ _ = 1) => by
        show (a * b) ^ _ = 1; rw [mul_pow, ha, hb, one_mul]
      inv_mem' := fun {a} (ha : a ^ _ = 1) => by
        show a⁻¹ ^ _ = 1; rw [inv_pow, ha, inv_one] }
  -- K equals ker(powMonoidHom d) as subgroups
  have hK_eq : K = (powMonoidHom d : (ZMod q)ˣ →* (ZMod q)ˣ).ker :=
    Subgroup.ext (fun _ => Iff.rfl)
  -- Nat.card K = gcd(|G|, d) = d (since d | q-1)
  have hcard_G : Nat.card (ZMod q)ˣ = q - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime inst.out]
  have hd_dvd_qm1 : d ∣ q - 1 := Nat.div_dvd_of_dvd hℓ_dvd
  have hgcd : (q - 1).gcd d = d :=
    Nat.dvd_antisymm (Nat.gcd_dvd_right _ _) (Nat.dvd_gcd hd_dvd_qm1 dvd_rfl)
  have hK_natcard : Nat.card K = d := by
    rw [hK_eq]
    have := IsCyclic.card_powMonoidHom_ker (G := (ZMod q)ˣ) d
    rwa [hcard_G, hgcd] at this
  have hK_card : Fintype.card K ≤ 7 := by
    rw [← Nat.card_eq_fintype_card, hK_natcard]; exact hsmall
  -- Eight elements escape any subgroup of order ≤ 7
  obtain ⟨n, _, hn⟩ := eight_elts_escape_order_le_seven hq hne hq59 K hK_card
  -- hn : Units.mk0 (multZ q n) _ ∉ K, i.e., ¬(m^d = 1)
  exact ⟨n, hn⟩

open Classical in
/-- **SE reduces to large-kernel PRE**: SubgroupEscape at q holds provided
    PRE_at holds for every prime factor ℓ of q-1 whose kernel has order > 7.
    Prime factors with small kernels ((q-1)/ℓ ≤ 7) are handled automatically
    by `pre_at_of_small_kernel`. -/
theorem se_of_small_pre {q : Nat} [inst : Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (hq59 : q ≥ 59)
    (hpre : ∀ ℓ ∈ (q - 1).primeFactors, (q - 1) / ℓ > 7 → PRE_at q hq hne ℓ) :
    ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H := by
  apply se_of_prime_index_escape hq hne
  intro ℓ hℓ
  have hqm1_ne : q - 1 ≠ 0 := by have := inst.out.one_lt; omega
  have hℓ_dvd := ((Nat.mem_primeFactors_of_ne_zero hqm1_ne).mp hℓ).2
  by_cases h : (q - 1) / ℓ ≤ 7
  · exact pre_at_of_small_kernel hq hne hq59 hℓ_dvd h
  · exact hpre ℓ hℓ (by omega)

/-- **PRE failure characterization**: PRE_at fails at ℓ iff every multiplier
    is an ℓ-th power residue (its (q-1)/ℓ power equals 1). -/
theorem not_pre_at_iff_all_pow_eq_one {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (ℓ : Nat) :
    ¬ PRE_at q hq hne ℓ ↔
    ∀ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ^ ((q - 1) / ℓ) = 1 := by
  simp only [PRE_at, not_exists, not_not]

open Classical in
/-- **SE failure requires small obstruction**: if SE fails at q ≥ 59, there
    must exist a prime factor ℓ of q-1 with (q-1)/ℓ > 7 (i.e., a "large
    kernel") such that ALL multipliers are ℓ-th power residues mod q.

    Contrapositive of `se_of_small_pre`: if no such obstruction exists,
    SE holds. -/
theorem se_failure_requires_small_obstruction {q : Nat} [inst : Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (hq59 : q ≥ 59)
    (hfail : ∃ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ ∧
      ∀ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∈ H) :
    ∃ ℓ ∈ (q - 1).primeFactors, (q - 1) / ℓ > 7 ∧ ¬ PRE_at q hq hne ℓ := by
  by_contra hall
  push_neg at hall
  obtain ⟨H, hH, hmem⟩ := hfail
  obtain ⟨n, hn⟩ := se_of_small_pre hq hne hq59 hall H hH
  exact hn (hmem n)

end LocalPRE

/-! ## §9b. Effective Kummer Escape

The **EffectiveKummerEscape** hypothesis captures the analytic content needed to
prove SubgroupEscape unconditionally.  For each prime ℓ, it asserts a uniform
bound B(ℓ) such that for every prime q ≥ B(ℓ) with ℓ | q-1, some multiplier
among the first B(ℓ) escapes the ℓ-th power kernel mod q.

This is a Chebotarev-type statement: the Frobenius at q in the Kummer extension
Q(ζ_ℓ, 3^{1/ℓ}, ..., 53^{1/ℓ}) must escape the trivial splitting class for at
least one of the six base primes {3,5,7,13,43,53}.

Combined with `pre_at_of_small_kernel` (automatic escape when kernel order ≤ 7),
EKE reduces SE to a finite computation for small q.
-/

section EffKummer

/-- **Effective Kummer Escape**: for each prime ℓ, there exists a uniform bound
    B such that for any prime q ≥ B with ℓ | q-1, some multiplier among the
    first B escapes the ℓ-th power kernel.  This is the analytic hypothesis
    separating Chebotarev density theory from the EM-specific algebra. -/
def EffectiveKummerEscape : Prop :=
  ∀ (ℓ : Nat), Nat.Prime ℓ →
    ∃ (B : Nat), ∀ (q : Nat) [Fact (Nat.Prime q)],
      ∀ (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
        q ≥ B → ℓ ∣ q - 1 →
          ∃ n, n < B ∧
            (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ^ ((q - 1) / ℓ) ≠ 1

/-- **EKE → PRE_at for large q**: for each prime ℓ, EKE provides a bound B(ℓ)
    above which PRE_at holds automatically. -/
theorem eke_implies_pre_at_large (heke : EffectiveKummerEscape) :
    ∀ (ℓ : Nat), Nat.Prime ℓ →
      ∃ (B : Nat), ∀ (q : Nat) [Fact (Nat.Prime q)],
        ∀ (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
          q ≥ B → ℓ ∣ q - 1 → PRE_at q hq hne ℓ := by
  intro ℓ hℓ
  obtain ⟨B, hB⟩ := heke ℓ hℓ
  exact ⟨B, fun q _ hq hne hqB hdvd => by
    obtain ⟨n, _, hn⟩ := hB q hq hne hqB hdvd; exact ⟨n, hn⟩⟩

open Classical in
/-- **PRE for large-kernel primes → SE**: if PRE_at holds at every prime factor
    ℓ of q-1 with large kernel ((q-1)/ℓ > 7), then SE holds at q ≥ 59.
    Small-kernel primes are handled automatically by `pre_at_of_small_kernel`. -/
theorem pre_at_large_kernel_implies_se
    {q : Nat} [inst : Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hq59 : q ≥ 59)
    (hbounds : ∀ ℓ ∈ (q - 1).primeFactors, (q - 1) / ℓ > 7 →
      ℓ ∣ q - 1 → PRE_at q hq hne ℓ) :
    ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H := by
  apply se_of_small_pre hq hne hq59
  intro ℓ hℓ hbig
  have hqm1_ne : q - 1 ≠ 0 := by have := inst.out.one_lt; omega
  have hℓ_dvd := ((Nat.mem_primeFactors_of_ne_zero hqm1_ne).mp hℓ).2
  exact hbounds ℓ hℓ hbig hℓ_dvd

/-- **EKE reduction**: EffectiveKummerEscape implies SubgroupEscape holds at
    every prime q ≥ 59 that exceeds all relevant EKE bounds.  Since each
    EKE bound B(ℓ) is finite and only finitely many primes ℓ divide q-1,
    this reduces SE to a finite computation for q < max{59, B(2), B(3), ...}. -/
theorem eke_implies_se_above_bounds (heke : EffectiveKummerEscape)
    {q : Nat} [inst : Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hq59 : q ≥ 59)
    (hqB : ∀ ℓ ∈ (q - 1).primeFactors, (q - 1) / ℓ > 7 →
      ∀ B, (∀ (q' : Nat) [Fact (Nat.Prime q')],
        ∀ (hq' : IsPrime q') (hne' : ∀ k, seq k ≠ q'),
          q' ≥ B → ℓ ∣ q' - 1 →
            ∃ n, n < B ∧
              (Units.mk0 (multZ q' n) (multZ_ne_zero hq' hne' n)) ^ ((q' - 1) / ℓ) ≠ 1)
        → q ≥ B) :
    ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H := by
  apply pre_at_large_kernel_implies_se hq hne hq59
  intro ℓ hℓ hbig hℓ_dvd
  have hqm1_ne : q - 1 ≠ 0 := by have := inst.out.one_lt; omega
  have hℓ_prime := ((Nat.mem_primeFactors_of_ne_zero hqm1_ne).mp hℓ).1
  obtain ⟨B, hB⟩ := heke ℓ hℓ_prime
  have hqge := hqB ℓ hℓ hbig B hB
  obtain ⟨n, _, hn⟩ := hB q hq hne hqge hℓ_dvd
  exact ⟨n, hn⟩

/-- **EKE + finite verification → PRE**: EffectiveKummerEscape combined with
    finite verification yields full PowerResidueEscape.  Three mechanisms
    cover all (q, ℓ) pairs:
    1. **Automatic** (q ≥ 59, kernel small): `pre_at_of_small_kernel`
    2. **EKE** (q ≥ B(ℓ)): the Kummer bound handles large q
    3. **Gap computation** (59 ≤ q < B(ℓ), large kernel): finitely many cases
    4. **Small q** (q < 59): finitely many primes to check

    The `hgap` hypothesis takes the EKE bound B and its witness, and must
    provide PRE_at for primes in [59, B) — a finite computation. -/
theorem eke_gap_implies_pre (heke : EffectiveKummerEscape)
    (hsmall_q : ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
      q < 59 → ∀ ℓ ∈ (q - 1).primeFactors, PRE_at q hq hne ℓ)
    (hgap : ∀ (ℓ B : Nat),
      Nat.Prime ℓ →
      (∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
        q ≥ B → ℓ ∣ q - 1 →
          ∃ n, n < B ∧
            (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ^ ((q - 1) / ℓ) ≠ 1) →
      ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
        59 ≤ q → q < B → ℓ ∈ (q - 1).primeFactors → (q - 1) / ℓ > 7 →
          PRE_at q hq hne ℓ) :
    PowerResidueEscape := by
  intro q inst hq hne ℓ hℓ
  have hqm1_ne : q - 1 ≠ 0 := by have := inst.out.one_lt; omega
  have hℓ_prime := ((Nat.mem_primeFactors_of_ne_zero hqm1_ne).mp hℓ).1
  have hℓ_dvd := ((Nat.mem_primeFactors_of_ne_zero hqm1_ne).mp hℓ).2
  by_cases hq59 : q ≥ 59
  · by_cases hsmall : (q - 1) / ℓ ≤ 7
    · exact pre_at_of_small_kernel hq hne hq59 hℓ_dvd hsmall
    · obtain ⟨B, hB⟩ := heke ℓ hℓ_prime
      by_cases hqB : q ≥ B
      · obtain ⟨n, _, hn⟩ := hB q hq hne hqB hℓ_dvd; exact ⟨n, hn⟩
      · exact hgap ℓ B hℓ_prime hB q hq hne hq59 (by omega) hℓ (by omega)
  · exact hsmall_q q hq hne (by omega) ℓ hℓ

end EffKummer
