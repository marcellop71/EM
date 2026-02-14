import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Rotor-Router Walks on Finite Groups

A **rotor-router walk** on a finite group `G` with generators `gens : Fin k → G` is a
deterministic walk where each vertex maintains a pointer (rotor) into the generator list.
When the walk visits `x`, it moves to `x * gens(rotor_x)` and increments the rotor.

## Main Results

* `rotor_visits_all`: A rotor-router walk with a generating set visits every group element.
* `rotor_visits_all_infinitely`: Every element is visited infinitely often.
-/

open Function

namespace RotorRouter

/-! ## Definitions -/

structure RotorState (G : Type*) (k : ℕ) where
  pos : G
  rotors : G → Fin k

variable {G : Type*} {k : ℕ} [NeZero k]

def rotorStep [DecidableEq G] [Mul G] (gens : Fin k → G)
    (s : RotorState G k) : RotorState G k where
  pos := s.pos * gens (s.rotors s.pos)
  rotors := Function.update s.rotors s.pos (s.rotors s.pos + 1)

def rotorRun [DecidableEq G] [Mul G] (gens : Fin k → G)
    (s₀ : RotorState G k) (n : ℕ) : RotorState G k :=
  (rotorStep gens)^[n] s₀

@[simp] theorem rotorRun_zero [DecidableEq G] [Mul G] (gens : Fin k → G)
    (s₀ : RotorState G k) : rotorRun gens s₀ 0 = s₀ := rfl

theorem rotorRun_succ [DecidableEq G] [Mul G] (gens : Fin k → G)
    (s₀ : RotorState G k) (n : ℕ) :
    rotorRun gens s₀ (n + 1) = rotorStep gens (rotorRun gens s₀ n) :=
  Function.iterate_succ_apply' ..

theorem rotorRun_add [DecidableEq G] [Mul G] (gens : Fin k → G)
    (s₀ : RotorState G k) (m n : ℕ) :
    rotorRun gens s₀ (m + n) = rotorRun gens (rotorRun gens s₀ m) n := by
  show (rotorStep gens)^[m + n] s₀ = (rotorStep gens)^[n] ((rotorStep gens)^[m] s₀)
  rw [← Function.iterate_add_apply, Nat.add_comm]

/-! ## Finiteness -/

def RotorState.equivProd (G : Type*) (k : ℕ) :
    RotorState G k ≃ G × (G → Fin k) where
  toFun s := (s.pos, s.rotors)
  invFun p := ⟨p.1, p.2⟩
  left_inv s := by cases s; rfl
  right_inv _ := rfl

instance [Finite G] : Finite (RotorState G k) :=
  Finite.of_equiv _ (RotorState.equivProd G k).symm

/-! ## Eventually periodic -/

theorem exists_lt_map_eq [Finite α] (f : ℕ → α) :
    ∃ m n, m < n ∧ f m = f n := by
  have h := not_injective_infinite_finite f
  simp only [Injective] at h
  push_neg at h
  obtain ⟨a, b, hab, hne⟩ := h
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨a, b, hlt, hab⟩
  · exact ⟨b, a, hgt, hab.symm⟩

theorem eventually_periodic [Finite α] (f : α → α) (x : α) :
    ∃ μ T, 0 < T ∧ f^[μ + T] x = f^[μ] x := by
  obtain ⟨m, n, hmn, heq⟩ := exists_lt_map_eq (fun i => f^[i] x)
  refine ⟨m, n - m, Nat.sub_pos_of_lt hmn, ?_⟩
  rw [Nat.add_sub_cancel' hmn.le]; exact heq.symm

theorem periodic_of_eq {α : Type*} (f : α → α) (x : α) {μ T : ℕ}
    (h : f^[μ + T] x = f^[μ] x) {n : ℕ} (hn : μ ≤ n) :
    f^[n + T] x = f^[n] x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h1 : f^[μ + d + T] x = f^[d] (f^[μ + T] x) := by
    rw [show μ + d + T = d + (μ + T) from by omega]
    exact iterate_add_apply f d (μ + T) x
  have h2 : f^[μ + d] x = f^[d] (f^[μ] x) := by
    rw [show μ + d = d + μ from by omega]
    exact iterate_add_apply f d μ x
  rw [h1, h2, h]

/-! ## Rotor pointer tracking -/

section RotorTracking

variable [DecidableEq G] [Mul G] (gens : Fin k → G)

theorem rotor_unchanged (s : RotorState G k) {x : G} (hne : s.pos ≠ x) :
    (rotorStep gens s).rotors x = s.rotors x := by
  show (Function.update s.rotors s.pos _ ) x = s.rotors x
  exact Function.update_of_ne hne.symm _ _

theorem rotor_at_pos (s : RotorState G k) :
    (rotorStep gens s).rotors s.pos = s.rotors s.pos + 1 := by
  show (Function.update s.rotors s.pos _) s.pos = s.rotors s.pos + 1
  exact Function.update_self _ _ _

theorem rotor_at_eq (s : RotorState G k) {x : G} (h : s.pos = x) :
    (rotorStep gens s).rotors x = s.rotors x + 1 := by
  subst h; exact rotor_at_pos gens s

def visitCount (s₀ : RotorState G k) (x : G) : ℕ → ℕ
  | 0 => 0
  | n + 1 => visitCount s₀ x n + if (rotorRun gens s₀ n).pos = x then 1 else 0

@[simp] theorem visitCount_zero (s₀ : RotorState G k) (x : G) :
    visitCount gens s₀ x 0 = 0 := rfl

theorem visitCount_succ_of_eq (s₀ : RotorState G k) {x : G} {n : ℕ}
    (h : (rotorRun gens s₀ n).pos = x) :
    visitCount gens s₀ x (n + 1) = visitCount gens s₀ x n + 1 := by
  simp [visitCount, h]

theorem visitCount_succ_of_ne (s₀ : RotorState G k) {x : G} {n : ℕ}
    (h : (rotorRun gens s₀ n).pos ≠ x) :
    visitCount gens s₀ x (n + 1) = visitCount gens s₀ x n := by
  simp [visitCount, h]

theorem visitCount_mono (s₀ : RotorState G k) (x : G) {m n : ℕ} (h : m ≤ n) :
    visitCount gens s₀ x m ≤ visitCount gens s₀ x n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => simp
  | succ d ih =>
    have : visitCount gens s₀ x (m + d) ≤ visitCount gens s₀ x (m + d + 1) := by
      by_cases hv : (rotorRun gens s₀ (m + d)).pos = x
      · rw [visitCount_succ_of_eq gens s₀ hv]; omega
      · rw [visitCount_succ_of_ne gens s₀ hv]
    exact le_trans ih this

private theorem fin_val_add_one (a : Fin k) :
    (a + 1 : Fin k).val = (a.val + 1) % k := by
  simp [Fin.val_add]

theorem rotor_tracks_visits (s₀ : RotorState G k) (x : G) (n : ℕ) :
    ((rotorRun gens s₀ n).rotors x).val =
    ((s₀.rotors x).val + visitCount gens s₀ x n) % k := by
  induction n with
  | zero => simp [Nat.mod_eq_of_lt (s₀.rotors x).isLt]
  | succ n ih =>
    rw [rotorRun_succ]
    by_cases h : (rotorRun gens s₀ n).pos = x
    · rw [visitCount_succ_of_eq gens s₀ h, rotor_at_eq gens (rotorRun gens s₀ n) h,
          fin_val_add_one, ih]
      have mod_add : ∀ a b : ℕ, (a % k + b) % k = (a + b) % k := by
        intro a b
        conv_lhs => rw [Nat.add_mod, Nat.mod_mod_of_dvd _ dvd_rfl, ← Nat.add_mod]
      rw [mod_add]; congr 1
    · rw [visitCount_succ_of_ne gens s₀ h, rotor_unchanged gens (rotorRun gens s₀ n) h, ih]

theorem visit_count_dvd_of_periodic (s₀ : RotorState G k) (x : G)
    {μ T : ℕ} (hperiod : rotorRun gens s₀ (μ + T) = rotorRun gens s₀ μ) :
    k ∣ visitCount gens (rotorRun gens s₀ μ) x T := by
  set s_μ := rotorRun gens s₀ μ
  have hrun : rotorRun gens s_μ T = s_μ := by
    change (rotorStep gens)^[T] ((rotorStep gens)^[μ] s₀) = _
    rw [← iterate_add_apply, Nat.add_comm]; exact hperiod
  have hval : ((rotorRun gens s_μ T).rotors x).val = (s_μ.rotors x).val := by rw [hrun]
  rw [rotor_tracks_visits gens s_μ x T] at hval
  have hmod : (s_μ.rotors x).val ≡ (s_μ.rotors x).val + visitCount gens s_μ x T [MOD k] := by
    show (s_μ.rotors x).val % k = ((s_μ.rotors x).val + visitCount gens s_μ x T) % k
    rw [Nat.mod_eq_of_lt (s_μ.rotors x).isLt, hval]
  rw [Nat.modEq_iff_dvd' (Nat.le_add_right _ _)] at hmod
  simpa using hmod

theorem visit_count_ge_k (s₀ : RotorState G k) (x : G)
    {μ T : ℕ} (hperiod : rotorRun gens s₀ (μ + T) = rotorRun gens s₀ μ)
    (hvisited : 0 < visitCount gens (rotorRun gens s₀ μ) x T) :
    k ≤ visitCount gens (rotorRun gens s₀ μ) x T :=
  Nat.le_of_dvd hvisited (visit_count_dvd_of_periodic gens s₀ x hperiod)

end RotorTracking

/-! ## All generators used at visited vertices -/

section GeneratorCoverage

variable [DecidableEq G] [Mul G] (gens : Fin k → G)

theorem fin_add_surj (r₀ : Fin k) : ∀ j : Fin k, ∃ i : Fin k, r₀ + i = j :=
  fun j => ⟨j - r₀, by abel⟩

end GeneratorCoverage

/-! ## Semigroup = group in finite groups -/

section SemigroupGroup

theorem mem_submonoid_closure_of_subgroup_top [Group G] [Finite G] (S : Set G)
    (h : Subgroup.closure S = ⊤) (g : G) :
    g ∈ Submonoid.closure S := by
  have : g ∈ (Subgroup.closure S).toSubmonoid := by simp [h]
  rwa [Subgroup.closure_toSubmonoid_of_finite] at this

theorem submonoid_closure_subset_of_mul_closed [Monoid G] (V : Set G) (S : Set G)
    (h1 : (1 : G) ∈ V) (hmul : ∀ g ∈ V, ∀ s ∈ S, g * s ∈ V) :
    ↑(Submonoid.closure S) ⊆ V := by
  suffices ∀ (y : G) (_ : y ∈ Submonoid.closure S), ∀ x ∈ V, x * y ∈ V by
    intro y hy; have := this y hy 1 h1; rwa [one_mul] at this
  intro y hy
  induction hy using Submonoid.closure_induction with
  | mem s hs => intro x hx; exact hmul x hx s hs
  | one => intro x hx; rwa [mul_one]
  | mul a b _ _ iha ihb =>
    intro x hx; rw [← mul_assoc]; exact ihb (x * a) (iha x hx)

end SemigroupGroup

/-! ## Main theorem -/

section MainTheorem

variable [Group G] [Fintype G] [DecidableEq G]

theorem walk_eventually_periodic (gens : Fin k → G) (s₀ : RotorState G k) :
    ∃ μ T, 0 < T ∧ rotorRun gens s₀ (μ + T) = rotorRun gens s₀ μ :=
  eventually_periodic (rotorStep gens) s₀

omit [Fintype G] in
/-- The visited set in one period is closed under generator multiplication. -/
theorem visited_closed_under_gens (gens : Fin k → G)
    (s₀ : RotorState G k) {μ T : ℕ} (hT : 0 < T)
    (hperiod : rotorRun gens s₀ (μ + T) = rotorRun gens s₀ μ) :
    ∀ x, (∃ i, i < T ∧ (rotorRun gens (rotorRun gens s₀ μ) i).pos = x) →
    ∀ j : Fin k, ∃ i', i' < T ∧
      (rotorRun gens (rotorRun gens s₀ μ) i').pos = x * gens j := by
  intro x ⟨i₀, hi₀, hpos⟩ j
  set s_μ := rotorRun gens s₀ μ
  have hvc_pos : 0 < visitCount gens s_μ x T := by
    have h1 := visitCount_succ_of_eq gens s_μ hpos
    have h2 := visitCount_mono gens s_μ x (show i₀ + 1 ≤ T by omega)
    omega
  have hge := visit_count_ge_k gens s₀ x hperiod hvc_pos
  obtain ⟨d, hd⟩ := fin_add_surj (s_μ.rotors x) j
  -- It suffices to find a step where rotor at x equals j
  suffices ∃ t, t < T ∧ (rotorRun gens s_μ t).pos = x ∧
      (rotorRun gens s_μ t).rotors x = j by
    obtain ⟨t, ht, hposx, hrotj⟩ := this
    by_cases htT : t + 1 < T
    · exact ⟨t + 1, htT, by
        rw [rotorRun_succ]
        simp only [rotorStep]; rw [hposx, hrotj]⟩
    · have hrun0 : rotorRun gens s_μ T = s_μ := by
        change (rotorStep gens)^[T] ((rotorStep gens)^[μ] s₀) = _
        rw [← iterate_add_apply, Nat.add_comm]; exact hperiod
      have hposT : (rotorRun gens s_μ T).pos = x * gens j := by
        rw [show T = t + 1 from by omega, rotorRun_succ]
        simp only [rotorStep]; rw [hposx, hrotj]
      rw [hrun0] at hposT
      exact ⟨0, hT, by change s_μ.pos = _; exact hposT⟩
  -- Find the d.val-th visit (0-indexed) by scanning
  suffices ∀ m : ℕ, m < visitCount gens s_μ x T →
      ∃ t, t < T ∧ (rotorRun gens s_μ t).pos = x ∧
      (rotorRun gens s_μ t).rotors x =
        s_μ.rotors x + ⟨m % k, Nat.mod_lt m (NeZero.pos k)⟩ by
    have hd_lt : d.val < visitCount gens s_μ x T := Nat.lt_of_lt_of_le d.isLt hge
    obtain ⟨t, ht, hposx, hrotx⟩ := this d.val hd_lt
    exact ⟨t, ht, hposx, by rw [hrotx, ← hd]; congr 1; exact Fin.ext (Nat.mod_eq_of_lt d.isLt)⟩
  -- Prove by induction: the m-th visit has rotor = init + m
  intro m hm
  suffices ∀ n, n ≤ T → m < visitCount gens s_μ x n →
      ∃ t, t < n ∧ (rotorRun gens s_μ t).pos = x ∧
      (rotorRun gens s_μ t).rotors x =
        s_μ.rotors x + ⟨m % k, Nat.mod_lt m (NeZero.pos k)⟩ by
    exact this T le_rfl hm
  intro n
  induction n with
  | zero => intro _ hm0; simp at hm0
  | succ n ihn =>
    intro hn hmn
    by_cases hvisit : (rotorRun gens s_μ n).pos = x
    · rw [visitCount_succ_of_eq gens s_μ hvisit] at hmn
      by_cases hm_eq : m = visitCount gens s_μ x n
      · refine ⟨n, by omega, hvisit, ?_⟩
        have hrt := rotor_tracks_visits gens s_μ x n
        apply Fin.ext; simp only [Fin.val_add]
        rw [hrt, hm_eq]
        conv_rhs => rw [Nat.add_mod, Nat.mod_mod_of_dvd _ dvd_rfl, ← Nat.add_mod]
      · obtain ⟨t, ht, h1, h2⟩ := ihn (by omega) (by omega)
        exact ⟨t, by omega, h1, h2⟩
    · rw [visitCount_succ_of_ne gens s_μ hvisit] at hmn
      obtain ⟨t, ht, h1, h2⟩ := ihn (by omega) hmn
      exact ⟨t, by omega, h1, h2⟩

private theorem period_visits_all (gens : Fin k → G)
    (hgen : Subgroup.closure (Set.range gens) = ⊤)
    (s₀ : RotorState G k) {μ T : ℕ} (hT : 0 < T)
    (hperiod : rotorRun gens s₀ (μ + T) = rotorRun gens s₀ μ) :
    ∀ x : G, ∃ i, i < T ∧ (rotorRun gens (rotorRun gens s₀ μ) i).pos = x := by
  set s_μ := rotorRun gens s₀ μ
  set V : Set G := {x | ∃ i, i < T ∧ (rotorRun gens s_μ i).pos = x}
  have hV_closed : ∀ x ∈ V, ∀ j : Fin k, x * gens j ∈ V :=
    fun x hx j => visited_closed_under_gens gens s₀ hT hperiod x hx j
  have hV_start : s_μ.pos ∈ V := ⟨0, hT, rfl⟩
  -- V' = right-translated visited set
  set V' : Set G := {g | s_μ.pos * g ∈ V}
  have hV'_one : (1 : G) ∈ V' := by show s_μ.pos * 1 ∈ V; rwa [mul_one]
  have hV'_mul : ∀ g ∈ V', ∀ s ∈ Set.range gens, g * s ∈ V' := by
    intro g hg s ⟨j, hj⟩; show s_μ.pos * (g * s) ∈ V
    rw [← mul_assoc, ← hj]; exact hV_closed (s_μ.pos * g) hg j
  have hV'_closure : ↑(Submonoid.closure (Set.range gens)) ⊆ V' :=
    submonoid_closure_subset_of_mul_closed V' (Set.range gens) hV'_one hV'_mul
  -- Every element is in V
  intro x
  have hx : s_μ.pos⁻¹ * x ∈ V' :=
    hV'_closure (mem_submonoid_closure_of_subgroup_top (Set.range gens) hgen _)
  change s_μ.pos * (s_μ.pos⁻¹ * x) ∈ V at hx
  rw [mul_inv_cancel_left] at hx
  exact hx

/-- A rotor-router walk on a finite group with a generating set visits every element. -/
theorem rotor_visits_all (gens : Fin k → G)
    (hgen : Subgroup.closure (Set.range gens) = ⊤)
    (s₀ : RotorState G k) :
    ∀ x : G, ∃ n : ℕ, (rotorRun gens s₀ n).pos = x := by
  obtain ⟨μ, T, hT, hperiod_once⟩ := walk_eventually_periodic gens s₀
  intro x
  obtain ⟨i, _, hpos⟩ := period_visits_all gens hgen s₀ hT hperiod_once x
  exact ⟨μ + i, by rw [rotorRun_add]; exact hpos⟩

/-- Every element is visited infinitely often. -/
theorem rotor_visits_all_infinitely (gens : Fin k → G)
    (hgen : Subgroup.closure (Set.range gens) = ⊤)
    (s₀ : RotorState G k) :
    ∀ x : G, ∀ N, ∃ n, N ≤ n ∧ (rotorRun gens s₀ n).pos = x := by
  intro x N
  obtain ⟨μ, T, hT, hperiod_once⟩ := walk_eventually_periodic gens s₀
  have hperiod_all : ∀ n, μ ≤ n → rotorRun gens s₀ (n + T) = rotorRun gens s₀ n :=
    fun n hn => periodic_of_eq (rotorStep gens) s₀ hperiod_once hn
  obtain ⟨i, hi, hxi⟩ := period_visits_all gens hgen s₀ hT hperiod_once x
  -- x is visited at μ + i + j*T for all j
  suffices ∀ j : ℕ, (rotorRun gens s₀ (μ + i + j * T)).pos = x by
    have hNT : N ≤ N * T := Nat.le_mul_of_pos_right N hT
    obtain ⟨j, hj⟩ : ∃ j, N ≤ μ + i + j * T := ⟨N, by omega⟩
    exact ⟨μ + i + j * T, hj, this j⟩
  intro j; induction j with
  | zero => simpa using (by rw [rotorRun_add]; exact hxi : (rotorRun gens s₀ (μ + i)).pos = x)
  | succ j ihj =>
    rw [show μ + i + (j + 1) * T = (μ + i + j * T) + T from by ring]
    show (rotorRun gens s₀ ((μ + i + j * T) + T)).pos = x
    rw [hperiod_all _ (by omega)]; exact ihj

end MainTheorem

/-! ## Scheduled Walk Coverage

A generalization of rotor-router coverage: any walk `w(n+1) = w(n) * σ(n)` on a
finite group covers all elements, provided the schedule `σ` satisfies **pointwise
recurrence** (at each infinitely-visited state, every generator is used infinitely
often). This abstracts the key property that makes rotor-routers work. -/

section ScheduledWalk

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- An element is visited infinitely often by a sequence. -/
def VisitsInfOften (w : ℕ → G) (x : G) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ w n = x

/-- Pointwise recurrence: at each infinitely-visited state, each generator
    from S is used as the schedule value infinitely often. -/
def PointwiseRecurrence (w : ℕ → G) (σ : ℕ → G) (S : Set G) : Prop :=
  ∀ x, VisitsInfOften w x →
    ∀ s ∈ S, ∀ N, ∃ n, N ≤ n ∧ w n = x ∧ σ n = s

omit [Group G] [DecidableEq G] in
/-- In a finite group, any sequence visits some element infinitely often. -/
theorem exists_visits_inf_often (w : ℕ → G) : ∃ x, VisitsInfOften w x := by
  by_contra hall
  have h : ∀ x : G, ∃ N : ℕ, ∀ n, N ≤ n → w n ≠ x := by
    intro x; by_contra hx; push_neg at hx
    exact hall ⟨x, hx⟩
  choose N hN using h
  exact hN (w _) _ (Finset.le_sup (f := N) (Finset.mem_univ _)) rfl

omit [DecidableEq G] in
/-- **Scheduled Walk Coverage**: any multiplicative walk with pointwise recurrence
    and a generating schedule visits every group element infinitely often. -/
theorem scheduled_walk_covers_all (w : ℕ → G) (σ : ℕ → G) (S : Set G)
    (hwalk : ∀ n, w (n + 1) = w n * σ n)
    (hgen : Subgroup.closure S = ⊤)
    (hrecur : PointwiseRecurrence w σ S) :
    ∀ x : G, VisitsInfOften w x := by
  obtain ⟨w₀, hw₀⟩ := exists_visits_inf_often w
  -- V' = {g | w₀ * g is visited infinitely often}
  let V' : Set G := {g | VisitsInfOften w (w₀ * g)}
  have hV'_one : (1 : G) ∈ V' := by show VisitsInfOften w (w₀ * 1); rwa [mul_one]
  have hV'_mul : ∀ g ∈ V', ∀ s ∈ S, g * s ∈ V' := by
    intro g (hg : VisitsInfOften w (w₀ * g)) s hs
    show VisitsInfOften w (w₀ * (g * s))
    intro N
    obtain ⟨n, hn, hwn, hσn⟩ := hrecur (w₀ * g) hg s hs N
    exact ⟨n + 1, by omega, by rw [hwalk, hwn, hσn, mul_assoc]⟩
  have hV'_closure : ↑(Submonoid.closure S) ⊆ V' :=
    submonoid_closure_subset_of_mul_closed V' S hV'_one hV'_mul
  intro x
  have hx : w₀⁻¹ * x ∈ V' :=
    hV'_closure (mem_submonoid_closure_of_subgroup_top S hgen _)
  show VisitsInfOften w x
  have : VisitsInfOften w (w₀ * (w₀⁻¹ * x)) := hx
  rwa [mul_inv_cancel_left] at this

end ScheduledWalk

end RotorRouter
