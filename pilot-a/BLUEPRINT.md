# Pilot A blueprint: widening the modularity step of the Lean FLT proof

Source: [anthropics/fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem), `PROOF-PATH.md` step 4
and "Exact strength of the named steps". Lean 4.33.1, Mathlib `db584cd6`.

## 1. What is proved today, and where it is narrow

| # | Lean theorem (repo) | Narrow hypothesis | Literature result that removes it | Size of the job |
|---|---|---|---|---|
| H1 | `WeierstrassCurve.modularity_of_semistableModel` | Semistability is a property of the **chosen integral equation** `W : WeierstrassCurve ℤ` (`IsSemistableModel`: no prime divides both Δ and c₄). A curve over ℚ that is semistable but given by a non-minimal or non-integral equation is not covered. | Existence of global minimal models over ℚ (class number 1; Silverman AEC VII.1, VIII.8.2) together with Tate's criterion for semistable reduction (AEC VII.5.1). | Small to medium. Only Mathlib's Weierstrass-curve algebra and p-adic valuations are needed. **Chosen as target.** |
| H2 | same | Only semistable curves (no additive reduction). | (a) Quadratic twisting of newforms (Shimura; Atkin–Li 1978) covers twists of semistable curves. (b) Diamond 1996 (semistable at 3 and 5); Conrad–Diamond–Taylor 1999; Breuil–Conrad–Diamond–Taylor 2001 (all of ℚ). | (a) Large: twisting of cusp forms is absent from Mathlib (Gauss sums, slash by translation matrices, cusp conditions on Γ₀(Nd²)). (b) Very large: needs ramified local deformation rings (Breuil modules / flat deformations beyond the semistable case). |
| H3 | `modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd`, `..._inertia_moves_torsion_of_eq_three_...` | Lifting only at p ∈ {3, 5}, only for semistable `W`, with level conditions (p² ∤ M₀, no q³ ∣ M₀, inertia condition at 3). | Taylor–Wiles–Diamond for general p ≥ 3 with ρ̄ irreducible on Gal(Q̄/Q(√p*)) (Diamond 1997, Fujiwara); Kisin 2009 for general local conditions. | Large. The patching core (`Algebra.PatchingDatum`) is generic, but the local deformation conditions and the 3/5-specific auxiliary steps would have to be redone for each p. |
| H4 | `WeierstrassCurve.isResiduallyModular_three_..._of_isSemistableModel`, `LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_eq_trace_lift` | Langlands–Tunnell only in the octahedral case with surjective ρ̄₃, cyclotomic determinant, and an explicit lift Ψ to GL₂(ℤ[√−2]). | Full Langlands–Tunnell for soluble image (Langlands 1980 cyclic base change; Tunnell 1981) covering the tetrahedral and dihedral cases; or Khare–Wintenberger (Serre's conjecture, 2009) for all odd irreducible ρ̄. | Tetrahedral/dihedral cases: large but closest to existing code. Serre's conjecture: out of reach. |
| H5 | `WeierstrassCurve.modThreeOrFiveIrreducible`, `fifteenIsogenyClassification` | Irreducibility only for semistable models. | Mazur's isogeny theorem (1978) in general. | Very large (the repo proves Mazur only for Frey curves). |
| H6 | `IsModular` | "Modular" means a_ℓ-matching at good primes away from N on *some* integral model. | Model independence of a_ℓ at good primes (AEC VII.1.3(d), reduction of p-integral changes of variables). | Small; a side lemma of H1. |

## 2. Target picked: H1, intrinsic semistability

**Statement (Lean, `pilot-a/PilotA/IntrinsicSemistable.lean`).** For `E : WeierstrassCurve ℚ` with `E.Δ ≠ 0`, say `E`
is *semistable at p* if some change of variables over ℚ takes `E` to an equation with p-integral coefficients
on which p does not divide both Δ and c₄ (Tate's criterion; this is a property of the curve, not of an equation).
Then:

1. `exists_semistableModel_of_isSemistable`: if `E` is semistable at every prime, it has a global integral model
   `W : WeierstrassCurve ℤ` with `W.IsSemistableModel` (existence of a global semistable minimal model over ℚ).
2. `isModular_of_isSemistable`: assuming the repo's `modularity_of_semistableModel`, every such `E` is modular.

This removes the "chosen integral equation" restriction flagged in PROOF-PATH ("The hypothesis is on a chosen
integral equation"): any equation of a semistable curve, with rational coefficients and any scaling, is now covered.

**Proof plan.**
- (a) Every `E` has an integral model (scale by a common denominator).
- (b) Strong induction on |Δ| over integral models. If an integral model `W` is not semistable, some prime p divides
  Δ and c₄; compare with the local semistable model `W_p = C • W`. Tate's criterion forces `v_p(u⁻¹) = k ≥ 1`.
- (c) Integrality of the change of variables (AEC VII.1.3(d)): if `W`, `C • W` are p-integral and `u⁻¹` is p-integral,
  then r, s, t are p-integral. Valuation argument with the b-invariant transformation rules.
- (d) Approximate r, s, t by integers modulo p^{6k} and use `u = p^{-k}` (in the repo's convention); the result is a
  global integral model with |Δ| divided by p^{12k}, contradicting minimality.
- (e) Transport `IsModular` along changes of variables (the group action composes).

**Dependency note.** The repo's full build needs about 153 GB of memory and 67 GB of disk. The theorem here is
therefore proved against the repo's *definitions* (`Definitions/Def_FLTPrelim_Modularity.lean`, vendored verbatim)
with Wiles's theorem as an explicit hypothesis; `PilotA/WithRepo.lean.txt` is the two-line instantiation with the
repo's theorem, to be compiled on a machine that can build the repo.

## Status (2026-11-01)
H1 **proved formally**: `PilotA.exists_semistable_model` and `PilotA.isModular_of_isSemistable` compile with only
the standard axioms. The composition with the repo's proved theorem (`WithRepo.lean.txt`) is a one-line
application that has not been compiled, because the repo's build exceeds this machine.

## 3. Next targets after H1
- H6 (model independence of a_ℓ), which makes `IsModular` usable for any equation.
- H2(a) twists: start by formalising quadratic twists of q-expansions and the point-count identity
  a_p(E^d) = χ_d(p) a_p(E); the cusp-form side is the bottleneck.
