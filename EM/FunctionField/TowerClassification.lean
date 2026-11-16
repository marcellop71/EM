import EM.FunctionField.Dichotomy

/-!
# The classification by the tower: `FF-MC(p) ↔ ¬ Stable p ∧ Dichotomy p`

Let `g = Y² + Y` and `T k = g^k(Y) + 1 ∈ 𝔽_p[Y]`, the level polynomials of the tower. Say
that `p` is **stable** if every `T k` is irreducible.

A run of prime stages composes: if stages `n, …, n+k-1` are prime then
`P_{n+k} = g^k ∘ P_n`, so the Euclid polynomial at stage `n+k` is `T k ∘ P_n`. A composition
`T ∘ B` is irreducible only if `T` is. Hence the level polynomials bound the runs of *every*
sequence, from *every* stage:

* `level_irreducible_of_run` — if stages `n, …, n+k` are all prime, `T k` is irreducible.
* `exists_reducible_of_not_level` — if `T k` is reducible, any `k+1` consecutive stages
  contain a composite one.
* `infinitelyManyReducible_of_not_stable` — if `p` is not stable, every sequence has
  infinitely many composite stages (with bounded gaps).

In the other direction the tower is the sequence itself:

* `perpetual_of_stable` — if `p` is stable, every sequence is a tower from stage `0`.

Together with `Dichotomy.lean`:

* `not_ffMullinConjecture_of_stable` — stable `p`: the conjecture is false.
* `ffDichotomy_of_stable` — stable `p`: the dichotomy holds.
* `ffMullinConjecture_iff_of_not_stable` — unstable `p`: the conjecture is the dichotomy.
* **`ffMullinConjecture_iff_not_stable_and_dichotomy`** — for every prime `p`,
  `FFMullinConjecture p ↔ ¬ Stable p ∧ FFDichotomy p`.

## Reading

This contains the earlier case results as instances: `𝔽_2` (`T 3` reducible), `𝔽_3` and
`p ≡ 1 (mod 3)` (`T 1` reducible), `𝔽_5` (stable). Stability is a property of the single
polynomial map `g` over `𝔽_p`; for odd `p` it is decided by the orbit of the critical point
`−1/2` (Capelli's lemma and the norm criterion; stated in `StableTower.lean`, not proved here
for general `p`). The dichotomy is the part that does not depend on `p`.
-/

namespace FunctionFieldAnalog

namespace TowerClassification

open Polynomial CompositeFloors CompositeEntry FFDegreeTelescope Dichotomy

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The iterates `g^k(Y)` of `g = Y² + Y`. -/
noncomputable def iter (p : ℕ) [Fact (Nat.Prime p)] : ℕ → (ZMod p)[X]
  | 0 => X
  | k + 1 => iter p k * (iter p k + 1)

/-- The level polynomials `T k = g^k(Y) + 1`. -/
noncomputable def level (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ) : (ZMod p)[X] := iter p k + 1

/-- `p` is stable: every level polynomial of the tower is irreducible over `𝔽_p`. -/
def Stable (p : ℕ) [Fact (Nat.Prime p)] : Prop := ∀ k, Irreducible (level p k)

/-- **A run of prime stages composes.** -/
theorem ffProd_add_of_run (d : FFEMData p) (n k : ℕ)
    (h : ∀ j, j < k → Irreducible (d.ffProd (n + j) + 1)) :
    d.ffProd (n + k) = (iter p k).comp (d.ffProd n) := by
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    rw [← add_assoc, ffProd_succ_of_irreducible d (n + k) (h k (Nat.lt_succ_self k)),
      ih (fun j hj => h j (by omega))]
    simp [iter]

/-- A composition `T ∘ B` with `B` non-constant is irreducible only if `T` is. -/
theorem irreducible_of_comp {T B : (ZMod p)[X]} (hB : 0 < B.natDegree)
    (h : Irreducible (T.comp B)) : Irreducible T := by
  have hunit : ∀ a : (ZMod p)[X], IsUnit (a.comp B) → IsUnit a := by
    intro a ha
    have hdeg : (a.comp B).natDegree = 0 := natDegree_eq_zero_of_isUnit ha
    rw [natDegree_comp] at hdeg
    have ha0 : a.natDegree = 0 := by
      rcases Nat.mul_eq_zero.mp hdeg with h0 | h0
      · exact h0
      · omega
    rw [eq_C_of_natDegree_eq_zero ha0] at ha ⊢
    rwa [C_comp] at ha
  refine ⟨fun hT => h.not_isUnit ?_, fun a b hab => ?_⟩
  · have h0 : T.natDegree = 0 := natDegree_eq_zero_of_isUnit hT
    rw [eq_C_of_natDegree_eq_zero h0] at hT ⊢
    rwa [C_comp]
  · have : T.comp B = a.comp B * b.comp B := by rw [hab, mul_comp]
    rcases h.isUnit_or_isUnit this with h1 | h1
    · exact Or.inl (hunit a h1)
    · exact Or.inr (hunit b h1)

/-- **The tower bounds every run.** If stages `n, …, n+k` are all prime, the level polynomial
    `T k` is irreducible. -/
theorem level_irreducible_of_run (d : FFEMData p) (n k : ℕ)
    (h : ∀ j, j ≤ k → Irreducible (d.ffProd (n + j) + 1)) : Irreducible (level p k) := by
  have hk := h k le_rfl
  rw [ffProd_add_of_run d n k (fun j hj => h j hj.le)] at hk
  have : (level p k).comp (d.ffProd n) = (iter p k).comp (d.ffProd n) + 1 := by
    simp [level]
  exact irreducible_of_comp (ffProd_natDegree_pos d n) (this ▸ hk)

/-- If `T k` is reducible, any `k + 1` consecutive stages contain a composite one. -/
theorem exists_reducible_of_not_level (d : FFEMData p) {k : ℕ}
    (hk : ¬ Irreducible (level p k)) (n : ℕ) :
    ∃ j, j ≤ k ∧ ¬ Irreducible (d.ffProd (n + j) + 1) := by
  by_contra hcon
  push Not at hcon
  exact hk (level_irreducible_of_run d n k hcon)

/-- **Unstable `p`: composite stages are forced, for every sequence.** -/
theorem infinitelyManyReducible_of_not_stable (hp : ¬ Stable p) (d : FFEMData p) :
    FFInfinitelyManyReducible d := by
  rw [Stable] at hp
  push Not at hp
  obtain ⟨k, hk⟩ := hp
  intro N
  obtain ⟨j, -, hj⟩ := exists_reducible_of_not_level d hk N
  exact ⟨N + j, by omega, hj⟩

/-- **Stable `p`: every sequence is the tower.** -/
theorem perpetual_of_stable (hp : Stable p) (d : FFEMData p) : FFPerpetualIrreducibility d 0 := by
  intro n _
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hrun := ffProd_add_of_run d 0 n (fun j hj => by simpa using ih j hj (Nat.zero_le j))
    rw [Nat.zero_add, d.ffProd_zero, comp_X] at hrun
    rw [hrun]
    exact hp n

/-- Stable `p`: the conjecture fails. -/
theorem not_ffMullinConjecture_of_stable (hp : Stable p) : ¬ FFMullinConjecture p := by
  intro h
  obtain ⟨d⟩ : Nonempty (FFEMData p) := inferInstance
  exact (ffMullinConjecture_iff_not_misses p).mp h d
    (misses_of_eventuallyPrime d ⟨0, perpetual_of_stable hp d⟩)

/-- Stable `p`: the dichotomy holds. -/
theorem ffDichotomy_of_stable (hp : Stable p) : FFDichotomy p :=
  fun d _ => ⟨0, perpetual_of_stable hp d⟩

/-- Unstable `p`: the conjecture is the dichotomy. -/
theorem ffMullinConjecture_iff_of_not_stable (hp : ¬ Stable p) :
    FFMullinConjecture p ↔ FFDichotomy p :=
  (ffDichotomy_iff_of_forced (infinitelyManyReducible_of_not_stable hp)).symm

/-- **The classification.** Over every `𝔽_p`, the function-field Mullin conjecture holds
    exactly when the tower is unstable and the dichotomy holds. -/
theorem ffMullinConjecture_iff_not_stable_and_dichotomy (p : ℕ) [Fact (Nat.Prime p)] :
    FFMullinConjecture p ↔ ¬ Stable p ∧ FFDichotomy p := by
  constructor
  · intro h
    exact ⟨fun hs => not_ffMullinConjecture_of_stable hs h, ffDichotomy_of_ffMullinConjecture h⟩
  · rintro ⟨hs, hd⟩
    exact (ffMullinConjecture_iff_of_not_stable hs).mpr hd

end TowerClassification

end FunctionFieldAnalog
