# Inventing a height argument for capture — the attempt (Session 318, 2026-08-20)

Goal: a functional `Φ` on the greedy orbit, built from absolute values `|·|_v` (archimedean
and `p`-adic) and the product formula, such that the failure of MC at a fixed prime `q`
(`E_n ∈ ℤ_q^×` eventually, `AdelicShadow.misses_iff_eventually_unit_both`) forces `Φ` to
violate a size bound.  Four constructions were tried.  Each fails for a precise reason; the
reasons compose into a single obstruction, which is already a theorem in the repository.

## A. Approximation exponent (Ridout / p-adic Roth)

View `P_n` as approximating `−1` at the finite places.  By the product formula
`∏_{v<∞} |P_n + 1|_v = 1/E_n = H(P_n)^{−1−o(1)}`: the total non-archimedean approximation
exponent is **identically 1**, below Ridout's threshold `2`, at every step — no
contradiction is available and no information is carried (the identity says `E_n` is an
integer).  At the chosen place alone the exponent is `log p_{n+1}/log E_n`, i.e. the relative
size `ρ` of `RelativeSize.lean` — the floor axis again.  At the fixed place `q` it is `0`
eventually, symmetrically for capture and failure.  **Fails: exponent is a constant.**

## B. The S-unit equation `E_n − P_n = 1` (Baker, subspace)

`P_n` is an `S_n`-unit, `E_n` an `S'_n`-unit, and the linear form
`Λ_n = Σ_k log p_k − Σ_j a_j log r_j` satisfies `|Λ_n| ≈ 1/E_n`.  Baker's lower bound is
`exp(−C^{ω} ∏ h(α_i) log B)` with `ω ≈ n` terms of height up to `E_n`; it is astronomically
below `1/E_n`.  The subspace theorem needs a *fixed* finite set of places; here the support
grows with `n`, so every fixed-`S` statement is exhausted after finitely many steps (the
technique mismatch of #134).  **Fails: growing support.**

## C. The `q`-adic decomposition — the real obstruction

`ℤ_q^× = μ_{q−1} × (1 + qℤ_q)`.  The `q`-adic logarithm kills the torsion `μ_{q−1}`; the
walk mod `q` is exactly the **torsion component** `ω(P_n) = ∏_k ω(p_k)` (Teichmüller).
Every absolute value and every `q`-adic logarithm factors through the torsion-free data
(sizes of multipliers, 1-unit parts).  Capture at `q` is a statement about the torsion
component.  So a functional built from heights and logarithms cannot distinguish two orbits
with the same multiplier sizes and 1-unit parts but different torsion.

This is not a heuristic; it is the **capture identity**
(`SeedCapture.captured_iff_mem_visited`, Lemma C of the seed-average programme): for a fixed
multiplier prefix — hence fixed heights, defects, and all `|·|_v` for `v ≠ q` — capture of
`q` within `n` steps is a condition on the single residue `m mod q`, and both outcomes are
realised by seeds with that prefix.  Therefore **no inequality among height-type functionals
of the multiplier sequence decides capture**.  For the orbit of `2` the residue is fixed, so
the identity does not apply literally; but it shows that any argument must use the specific
arithmetic of `2 mod q` and the factorisations along the orbit — which is #90.

## D. The product of Euclid numbers in `Ω`

`∏_{n<N} E_n → 0` in `Ω = ∏_r ℤ/r` iff every prime divides some Euclid number (weak
hitting); tautological, like `P_n → 0 ⟺ MC` (`ProfiniteAttractor.mc_iff_tendsto_zero`).
Its archimedean size is `Σ δ_n` up to `O(1)`, the defect telescope — discard, not location
(`AdelicShadow.defect_eq_log_cofactor`).  **Fails: reformulation only.**

## E. What a height argument would have to be

Heights and torsion are coupled in exactly three known ways: Northcott (torsion has height
`0`; bounded height ⇒ finitely many points), Bilu-type equidistribution of small points, and
Chebotarev/Frobenius for fixed fields.  The last two are population statements.  The first
suggests the only design left: a *bounded-height family* in which capture is the torsion
datum — and that family is the seeds `m ≤ X`, with the counting among them being natural
density.  The height angle therefore **reproduces the seed-average programme** and nothing
beyond it.  Recorded as dead end #177 with witness `captured_iff_mem_visited`.

## Verdict

The adelic/height language is the right way to state the dichotomy (`AdelicShadow.lean`); as a
source of an argument it is closed by C.  A proof of MC must use the torsion component
directly, i.e. the arithmetic of the specific integers `P_n + 1`.
