import EM.WeakErgodicity
import EM.IKCh2

/-!
# Population Equidistribution: Proof from Dirichlet + Sieve Axioms

This file proves `PopulationEquidist` (PE) from a standard hypothesis
of analytic number theory:

**`MinFacResidueEquidist`**: among q-rough shifted squarefree numbers,
the minFac residue class mod q is equidistributed, in the sense that
each class a ∈ {1,...,q−1} has density (1/(q−1)) of the total.

This follows from the Selberg sieve and Dirichlet's theorem on primes in
arithmetic progressions (`PrimesEquidistributedInAP` in IKCh2.lean).

## Mathematical Proof Sketch

For prime r, the density of r | m among m ∈ S is g(r) = r/(r²−1).
This follows from CRT: the event r | m forces m−1 ≡ −1 (mod r), so
squarefreeness at r is automatic, giving density (1/r) · (6/π²)/(1−1/r²).

The minFac density is d_S(p) = g(p) · ∏_{r<p}(1−g(r)). Writing this as
d_S(p) = h(p)/p where h(p) = (p²/(p²−1)) · ∏_{r<p}((1−g(r))/(1−1/r)) · ∏_{r<p}(1−1/r),
the weight h(p) depends on p only through its size, not through p mod q.

By Dirichlet's theorem (weighted form): for any weight w(p) depending
only on |p|, primes in arithmetic progressions are equidistributed:
  ∑_{p≡a(q)} w(p)/p ∼ (1/(q−1)) · ∑_{gcd(p,q)=1} w(p)/p.

Applying this to w = h gives PE.

## Main Results

* `MinFacResidueEquidist`           — equidist of minFac mod q in S_q (HYPOTHESIS)
* `pe_of_mfre`                      — PE from the hypothesis (PROVED)
* `pe_of_equidist`                  — PE from the hypothesis for all q (PROVED)
* `equidist_transfer_cme_implies_mc` — full chain to MC (PROVED)
-/

open Mullin Euclid MullinGroup RotorRouter

/-! ## Counting Functions -/

section CountingFunctions

/-- The q-rough shifted squarefree counting function:
    |{m ∈ [2,X] : μ²(m−1) = 1, minFac(m) > q}|. -/
noncomputable def qRoughSSCount (q X : Nat) : Nat :=
  ((Finset.Icc 2 X).filter (fun m => Squarefree (m - 1) ∧ q < Nat.minFac m)).card

/-- The residue-restricted q-rough shifted squarefree counting function:
    |{m ∈ [2,X] : μ²(m−1) = 1, minFac(m) > q, minFac(m) ≡ a (mod q)}|. -/
noncomputable def qRoughSSResCount (q a X : Nat) : Nat :=
  ((Finset.Icc 2 X).filter
    (fun m => Squarefree (m - 1) ∧ q < Nat.minFac m ∧ Nat.minFac m % q = a)).card

/-- The residue-restricted count is at most the total q-rough count. -/
theorem qRoughSSResCount_le (q a X : Nat) :
    qRoughSSResCount q a X ≤ qRoughSSCount q X := by
  apply Finset.card_le_card
  intro m
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact fun ⟨hm, hsq, hmin, _⟩ => ⟨hm, hsq, hmin⟩

end CountingFunctions

/-! ## Analytic Hypothesis -/

section Hypothesis

/-- **Equidistribution of minFac residues in the q-rough shifted squarefree
    population.**

    For each residue class a ∈ {1,...,q−1}, the natural density of
    {m ∈ S_q : minFac(m) ≡ a (mod q)} is exactly 1/(q−1) of the natural
    density of S_q itself.

    The hypothesis packages two facts:
    (1) S_q has positive natural density c > 0 (from the sieve),
    (2) each residue class has density c/(q−1) (from Dirichlet + sieve).

    **Proof from standard ANT:**
    The sieve axiom gives g(r) = r/(r²−1) for the density of divisibility
    by r in S. The minFac distribution d_S(p) = g(p) · ∏_{r<p}(1−g(r))
    can be written as h(p)/p where h(p) depends on p only through its
    magnitude, not through p mod q. By Dirichlet's theorem on primes in
    arithmetic progressions (`PrimesEquidistributedInAP` from IKCh2.lean),
    primes weighted by h are equidistributed in residue classes mod q.
    Error control uses Barban-Davenport-Halberstam for the sieve
    remainders. -/
def MinFacResidueEquidist (q : Nat) : Prop :=
  ∀ (a : Nat), 0 < a → a < q →
    ∃ (c : ℝ), 0 < c ∧
      Filter.Tendsto (fun X : Nat => (qRoughSSCount q X : ℝ) / (X : ℝ))
        Filter.atTop (nhds c) ∧
      Filter.Tendsto (fun X : Nat => (qRoughSSResCount q a X : ℝ) / (X : ℝ))
        Filter.atTop (nhds (c / (q - 1 : ℝ)))

end Hypothesis

/-! ## PE from the Hypothesis -/

section PEProof

/-- Auxiliary: if `f(n)/n → L₁` and `g(n)/n → L₂ > 0` and `f ≤ g`, then
    `f(n)/g(n) → L₁/L₂`. Used to derive the PE ratio from densities. -/
private theorem tendsto_ratio_of_tendsto_densities
    {f g : Nat → ℝ}
    {L₁ L₂ : ℝ} (hL₂ : L₂ ≠ 0)
    (hf : Filter.Tendsto (fun n : Nat => f n / (n : ℝ)) Filter.atTop (nhds L₁))
    (hg : Filter.Tendsto (fun n : Nat => g n / (n : ℝ)) Filter.atTop (nhds L₂)) :
    Filter.Tendsto (fun n : Nat => f n / g n) Filter.atTop (nhds (L₁ / L₂)) := by
  have key : Filter.Tendsto
      (fun n : Nat => (f n / (n : ℝ)) / (g n / (n : ℝ)))
      Filter.atTop (nhds (L₁ / L₂)) :=
    Filter.Tendsto.div hf hg hL₂
  apply key.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  by_cases hgn : g n = 0
  · simp [hgn]
  · have hn_pos : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp

/-- **PE follows from MinFacResidueEquidist.**

    The PE ratio is resCount(X) / totalCount(X). Since both
    resCount(X)/X → c/(q−1) and totalCount(X)/X → c with c > 0,
    the ratio converges to (c/(q−1))/c = 1/(q−1). -/
theorem pe_of_mfre {q : Nat} (hq : Nat.Prime q)
    (hmfre : MinFacResidueEquidist q) :
    ∀ (a : Nat), 0 < a → a < q →
      Filter.Tendsto
        (fun X : Nat =>
          (((Finset.Icc 2 X).filter
            (fun m => Squarefree (m - 1) ∧ q < Nat.minFac m ∧ Nat.minFac m % q = a)).card : ℝ) /
          ((Finset.Icc 2 X).filter (fun m => Squarefree (m - 1) ∧ q < Nat.minFac m)).card)
        Filter.atTop
        (nhds (1 / (q - 1 : ℝ))) := by
  intro a ha haq
  obtain ⟨c, hc_pos, h_total, h_res⟩ := hmfre a ha haq
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  -- Rewrite the target as c/(q-1) / c
  have hq_cast : (q : ℝ) - 1 ≠ 0 := by
    have h2 := hq.two_le
    have : (1 : ℝ) < (q : ℝ) := by exact_mod_cast h2
    linarith
  rw [show (1 : ℝ) / (q - 1) = c / (q - 1) / c by field_simp]
  -- The PE ratio = (resCount/X) / (totalCount/X), apply limit quotient
  exact tendsto_ratio_of_tendsto_densities hc_ne h_res h_total

/-- **Population Equidistribution from analytic hypotheses.**

    PE follows from MinFacResidueEquidist for every prime q. This
    separates the combinatorial content (this proof) from the analytic
    content (Dirichlet + sieve → MinFacResidueEquidist). -/
theorem pe_of_equidist
    (h : ∀ (q : Nat), Nat.Prime q → MinFacResidueEquidist q) :
    PopulationEquidist :=
  fun q hq a ha haq => pe_of_mfre hq (h q hq) a ha haq

end PEProof

/-! ## Connection to the Reduction Chain -/

section ReductionChain

/-- **Standard ANT → PE → (+ PT + EMDImpliesCME) → MC.**

    This theorem makes explicit the full reduction from standard analytic
    number theory to Mullin's Conjecture, with the two remaining open
    gaps (PopulationTransfer and EMDImpliesCME) clearly identified.

    The chain is:
    1. Dirichlet + Sieve → MinFacResidueEquidist (standard ANT)
    2. MinFacResidueEquidist → PE (this file, `pe_of_equidist`)
    3. PE + PT → EMDirichlet (WeakErgodicity, `pe_transfer_implies_emd`)
    4. EMDirichlet + EMDImpliesCME → CME (CMEDecomposition)
    5. CME → MC (LargeSieveSpectral, `cme_implies_mc`) -/
theorem equidist_transfer_cme_implies_mc
    (h_equidist : ∀ (q : Nat), Nat.Prime q → MinFacResidueEquidist q)
    (hpt : PopulationTransfer)
    (hcme : EMDImpliesCME) :
    MullinConjecture :=
  pe_transfer_cme_implies_mc (pe_of_equidist h_equidist) hpt hcme

end ReductionChain
