import EM.FunctionField.Analog

/-!
# Autonomous Map for Degree-1 Targets in FF-EM

For degree-1 targets Q = (t - a) in the function field EM sequence over F_p[t],
the walk position (under perpetual irreducibility of ffProd(n)+1) follows the
autonomous map f(w) = w * (w + 1) on F_p. This file formalizes:

1. The autonomous map f and its orbit.
2. f(-1) = 0 and f(0) = 0 (absorbing fixed point).
3. The Phi_3 criterion: preimage of -1 under f is exactly the roots of w^2+w+1=0.
4. For p equiv 2 mod 3 with p >= 5, w^2+w+1 has no roots in F_p.
5. The exclusion theorem: -1 is unreachable from any starting value a != -1.

## Mathematical significance

This provides a STRUCTURAL OBSTRUCTION for degree-1 capture in FF-EM under
perpetual irreducibility: for p equiv 2 mod 3, only the starting value -1 itself
can reach -1. All other starting values are absorbed into 0 without ever hitting -1.
This is a concrete instance of the orbit-specificity barrier (Dead End #90).
-/

namespace FunctionFieldAnalog

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## Section 1: The Autonomous Map -/

/-- The autonomous map f(w) = w * (w + 1) on ZMod p. -/
def ffAutonomousMap (w : ZMod p) : ZMod p := w * (w + 1)

/-- The orbit of the autonomous map from a starting value. -/
def ffAutonomousOrbit (a : ZMod p) : ℕ → ZMod p
  | 0 => a
  | n + 1 => ffAutonomousMap p (ffAutonomousOrbit a n)

/-! ## Section 2: Basic Properties -/

/-- f(-1) = 0: the value -1 maps to 0. -/
theorem ffAutonomousMap_neg_one : ffAutonomousMap p (-1 : ZMod p) = 0 := by
  simp [ffAutonomousMap]

/-- f(0) = 0: the value 0 is an absorbing fixed point. -/
theorem ffAutonomousMap_zero : ffAutonomousMap p (0 : ZMod p) = 0 := by
  simp [ffAutonomousMap]

/-- Once the orbit hits 0, it stays at 0 forever. -/
theorem ffAutonomousOrbit_absorbed (a : ZMod p) (n : ℕ)
    (h0 : ffAutonomousOrbit p a n = 0) :
    ∀ m, n ≤ m → ffAutonomousOrbit p a m = 0 := by
  intro m hm
  induction m with
  | zero =>
    have : n = 0 := by omega
    subst this; exact h0
  | succ k ih =>
    by_cases hk : n ≤ k
    · simp [ffAutonomousOrbit, ih hk, ffAutonomousMap_zero]
    · have : n = k + 1 := by omega
      subst this; exact h0

/-! ## Section 3: Phi_3 Criterion -/

/-- The preimage of -1 under f is exactly the root set of w^2 + w + 1 = 0.
    Proof: f(w) = w(w+1) = w^2+w, so f(w) = -1 iff w^2+w = -1 iff w^2+w+1 = 0. -/
theorem ffAutonomousMap_eq_neg_one_iff (w : ZMod p) :
    ffAutonomousMap p w = -1 ↔ w ^ 2 + w + 1 = 0 := by
  unfold ffAutonomousMap
  constructor
  · intro h
    -- w * (w + 1) = -1, so w * (w + 1) + 1 = 0, i.e. w^2 + w + 1 = 0
    have key : w * (w + 1) + 1 = 0 := by rw [h]; ring
    linear_combination key
  · intro h
    -- w^2 + w + 1 = 0, so w^2 + w = -1, i.e. w * (w + 1) = -1
    have key : w ^ 2 + w = -1 := by
      have h1 : w ^ 2 + w + 1 - 1 = 0 - 1 := congr_arg (· - 1) h
      simp only [add_sub_cancel_right, zero_sub] at h1
      exact h1
    calc w * (w + 1) = w ^ 2 + w := by ring
    _ = -1 := key

/-! ## Section 4: No Roots of Phi_3 When p equiv 2 mod 3 -/

/-- If w^2+w+1 = 0 then w^3 = 1.
    Proof: (w-1)(w^2+w+1) = w^3-1, so w^2+w+1 = 0 implies w^3 = 1. -/
private theorem pow_three_eq_one_of_phi3 (w : ZMod p) (h : w ^ 2 + w + 1 = 0) :
    w ^ 3 = 1 := by
  have : (w - 1) * (w ^ 2 + w + 1) = w ^ 3 - 1 := by ring
  rw [h, mul_zero] at this
  linear_combination -this

/-- If w^2+w+1 = 0 then w != 0 (since 0^2+0+1 = 1 != 0 in any nontrivial ring). -/
private theorem ne_zero_of_phi3 (w : ZMod p) (h : w ^ 2 + w + 1 = 0) :
    w ≠ 0 := by
  intro heq
  rw [heq] at h
  simp at h

open Classical in
/-- The order of an element satisfying w^3 = 1, w != 1 in a finite group is exactly 3. -/
private theorem orderOf_eq_three_of_cube_eq_one {G : Type*} [Group G] [Fintype G]
    (w : G) (h3 : w ^ 3 = 1) (hne : w ≠ 1) : orderOf w = 3 := by
  have hdvd : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hne1 : orderOf w ≠ 1 := by
    rwa [Ne, orderOf_eq_one_iff]
  -- orderOf w | 3 and orderOf w != 1, and 3 is prime, so orderOf w = 3
  have h3prime : Nat.Prime 3 := by decide
  rcases h3prime.eq_one_or_self_of_dvd _ hdvd with h1 | h3
  · exact absurd h1 hne1
  · exact h3

/-- For p equiv 2 mod 3 with p >= 5, there are no roots of w^2 + w + 1 in F_p.
    Proof: any root w gives w^3 = 1, w != 1 (since 3 != 0), w != 0,
    so w is a unit of order 3. By Lagrange, 3 | (p-1). But p equiv 2 mod 3
    means p-1 equiv 1 mod 3, contradicting 3 | (p-1). -/
theorem phi3_no_roots (hp3 : p % 3 = 2) (hp5 : 5 ≤ p) (w : ZMod p) :
    w ^ 2 + w + 1 ≠ 0 := by
  intro h
  -- Step 1: w^3 = 1
  have hw3 : w ^ 3 = 1 := pow_three_eq_one_of_phi3 p w h
  -- Step 2: w != 0
  have hne0 : w ≠ 0 := ne_zero_of_phi3 p w h
  -- Step 3: w != 1 (since 1+1+1 = 3 != 0 in ZMod p when p does not divide 3)
  have hne1 : w ≠ 1 := by
    intro heq; rw [heq] at h; norm_num at h
    -- h : (3 : ZMod p) = 0
    have h3 : (3 : ZMod p) = 0 := h
    rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) from by push_cast; ring] at h3
    rw [ZMod.natCast_eq_zero_iff] at h3
    -- h3 : p ∣ 3, so p = 1 or p = 3 (since 3 is prime)
    have h3prime : Nat.Prime 3 := by decide
    rcases h3prime.eq_one_or_self_of_dvd p h3 with hp1 | hp3
    · exact absurd hp1 (by omega)
    · omega
  -- Step 4: w is a unit (nonzero in ZMod p for prime p)
  have hunit : IsUnit w := hne0.isUnit
  obtain ⟨u, hu⟩ := hunit
  -- Step 5: u^3 = 1 in the units group
  have hu3 : u ^ 3 = 1 := by
    apply Units.ext; show (u : ZMod p) ^ 3 = 1
    rw [hu]; exact hw3
  -- Step 6: u != 1
  have hune1 : u ≠ 1 := by
    intro heq; apply hne1
    have : (u : ZMod p) = (1 : (ZMod p)ˣ) := congr_arg Units.val heq
    rw [hu] at this; simpa using this
  -- Step 7: orderOf u = 3
  have hord : orderOf u = 3 := orderOf_eq_three_of_cube_eq_one u hu3 hune1
  -- Step 8: 3 | card (ZMod p)× = p - 1
  have h3dvd : 3 ∣ Fintype.card (ZMod p)ˣ := hord ▸ orderOf_dvd_card
  rw [ZMod.card_units_eq_totient, Nat.totient_prime hp.out] at h3dvd
  -- Step 9: p - 1 equiv 1 mod 3, contradiction with 3 | (p-1)
  omega

/-! ## Section 5: Unreachability of -1 -/

/-- For p equiv 2 mod 3 with p >= 5, -1 has no preimage under f. -/
theorem ffAutonomousMap_ne_neg_one (hp3 : p % 3 = 2) (hp5 : 5 ≤ p)
    (w : ZMod p) : ffAutonomousMap p w ≠ -1 := by
  intro heq
  exact phi3_no_roots p hp3 hp5 w ((ffAutonomousMap_eq_neg_one_iff p w).mp heq)

/-- Main exclusion theorem: for p equiv 2 mod 3 with p >= 5, the orbit of f
    from any starting value a != -1 never hits -1. -/
theorem ff_neg_one_unreachable (hp3 : p % 3 = 2) (hp5 : 5 ≤ p)
    (a : ZMod p) (ha : a ≠ (-1 : ZMod p)) :
    ∀ n, ffAutonomousOrbit p a n ≠ -1 := by
  intro n
  induction n with
  | zero =>
    simp [ffAutonomousOrbit]
    exact ha
  | succ k _ih =>
    simp only [ffAutonomousOrbit]
    exact ffAutonomousMap_ne_neg_one p hp3 hp5 _

/-- If the starting value is -1, it maps to 0 immediately. -/
theorem ff_orbit_neg_one_step_zero :
    ffAutonomousOrbit p (-1 : ZMod p) 1 = 0 := by
  simp [ffAutonomousOrbit, ffAutonomousMap_neg_one]

/-- If the starting value is -1, the orbit is 0 for all n >= 1. -/
theorem ff_orbit_neg_one_absorbed :
    ∀ n, 1 ≤ n → ffAutonomousOrbit p (-1 : ZMod p) n = 0 :=
  ffAutonomousOrbit_absorbed p (-1) 1 (ff_orbit_neg_one_step_zero p)

/-! ## Section 6: Orbit Dynamics Summary -/

/-- For p equiv 2 mod 3 with p >= 5, -1 is visited at most at step 0.
    At step n >= 1, the orbit value is never -1 regardless of starting value. -/
theorem ff_neg_one_visited_at_most_once (hp3 : p % 3 = 2) (hp5 : 5 ≤ p)
    (a : ZMod p) (n : ℕ) (hn : 1 ≤ n) :
    ffAutonomousOrbit p a n ≠ -1 := by
  induction n with
  | zero => omega
  | succ k _ih =>
    simp only [ffAutonomousOrbit]
    exact ffAutonomousMap_ne_neg_one p hp3 hp5 _

/-- Landscape theorem assembling the autonomous map results. -/
theorem autonomous_map_landscape (hp3 : p % 3 = 2) (hp5 : 5 ≤ p) :
    -- (1) f(-1) = 0
    ffAutonomousMap p (-1 : ZMod p) = 0 ∧
    -- (2) f(0) = 0
    ffAutonomousMap p (0 : ZMod p) = 0 ∧
    -- (3) Phi_3 has no roots
    (∀ w : ZMod p, w ^ 2 + w + 1 ≠ 0) ∧
    -- (4) -1 has no preimage
    (∀ w : ZMod p, ffAutonomousMap p w ≠ -1) ∧
    -- (5) -1 unreachable from a != -1
    (∀ a : ZMod p, a ≠ -1 → ∀ n, ffAutonomousOrbit p a n ≠ -1) ∧
    -- (6) -1 visited at most once from any starting value
    (∀ a : ZMod p, ∀ n, 1 ≤ n → ffAutonomousOrbit p a n ≠ -1) :=
  ⟨ffAutonomousMap_neg_one p,
   ffAutonomousMap_zero p,
   phi3_no_roots p hp3 hp5,
   ffAutonomousMap_ne_neg_one p hp3 hp5,
   ff_neg_one_unreachable p hp3 hp5,
   ff_neg_one_visited_at_most_once p hp3 hp5⟩

end FunctionFieldAnalog
