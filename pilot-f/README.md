# Pilot F: the Petersson inner product on cusp forms

Lean 4 (v4.33.1) with Mathlib `db584cd6`, building on Pilot D (`../pilot-d`, required as a path
dependency). Standard axioms only, no `sorry`.

## What is proved

| Result | Lean name | Status |
| --- | --- | --- |
| `𝒟` (fundamental domain of `SL(2, ℤ)`) has finite invariant measure | `PilotF.volume_fd_lt_top` | proved formally |
| Convergence: the Petersson integrand of two cusp forms is integrable on `𝒟` | `PilotF.integrableOn_peterssonSum` | proved formally |
| Definition of `⟪f, g⟫` on `S_k(𝒢)`, `𝒢` arithmetic with determinant one (e.g. `Γ₀(N)`) | `PilotF.peterssonInner` | definition |
| Hermitian, sesquilinear | `peterssonInner_conj_symm`, `_add_left/right`, `_smul_left/right` | proved formally |
| Positive definite | `peterssonInner_self_nonneg`, `peterssonInner_self_eq_zero` | proved formally |
| Bundled inner product structure | `PilotF.peterssonCore : InnerProductSpace.Core ℂ (CuspForm 𝒢 k)` | proved formally |
| Boundary of `𝒟` is null; translates of `𝒟` cover `ℍ` exactly twice a.e. | `volume_fd_diff_fdo`, `tsum_indicator_fd_smul` | proved formally |
| Unfolding: invariance under any det-one `W` normalizing `𝒢 ≤ SL(2, ℤ)` | `lintegral_fd_sum_comp_smul`, `peterssonInner_self_slash`, `peterssonInner_map_eq` | proved formally |
| Trace is adjoint to inclusion: `⟪g, f⟫_𝒢 = ⟪g, Tr f⟫_{SL(2,ℤ)}` | `peterssonInner_eq_peterssonInner_trace` | proved formally |
| Fricke `W_N` is unitary and self-adjoint on `S_k(Γ₀(N))` | `peterssonInner_fricke`, `peterssonInner_fricke_left` | proved formally |
| Statement: D's trace-kernel new space = Petersson complement of old space | `PilotF.NewSubspaceEqOrthogonal N k` | compiles (all `N`) |
| The statement for `N = p` prime | `newSubspaceEqOrthogonal_prime`, `newSubspace_eq_peterssonOrthogonal_oldSubspace` | proved formally |
| The statement for composite `N` | | open |

## Definition

```
⟪f, g⟫ = ∫_{τ ∈ 𝒟} ∑_{h ∈ 𝒮ℒ ⧸ 𝒢} conj (f (h⁻¹ τ)) · g (h⁻¹ τ) · (im (h⁻¹ τ)) ^ k  dx dy / y²
```

When `-1 ∈ 𝒢` (as for `Γ₀(N)`) this is the integral over `𝒢 \ ℍ`, unfolded along `SL(2, ℤ)`, so
no fundamental domain for `𝒢` is constructed. It is not divided by the index (divide by
`[SL(2, ℤ) : 𝒢]` for the level-independent normalization). It is conjugate linear in the first argument, matching Mathlib's
`UpperHalfPlane.petersson` and `InnerProductSpace`.

## Files

* `PilotF/Petersson.lean`: finite volume, integrability, the inner product, positivity, the
  identity theorem step (a holomorphic function vanishing on `𝒟ᵒ` is zero).
* `PilotF/Unfolding.lean`: the change-of-variables argument with Lebesgue integrals, polarization.
* `PilotF/Newforms.lean`: trace adjointness, Fricke, the newform statement and the prime case.
* `AxiomCheck.lean`: 16 `#guard_msgs` checks that the main results depend only on
  `propext`, `Classical.choice`, `Quot.sound`.

## Build

```
lake build PilotF AxiomCheck
```

The Mathlib cache host is blocked in the cloud container, so Mathlib is compiled from source
(about 3,400 modules, roughly 1.5 h on 4 cores and 15 GB RAM).

## Assumptions and design choices

* Proof for prime level only. For composite `N` the old space has more summands (`B_d` from all
  `M · d ∣ N`), and the proof needs the adjoints of `B_d` and of the traces `Tr_{N/M}` for every
  `M`, plus the general Atkin–Lehner operators; the same unfolding lemma handles each change of
  variables, but it has not been done.
* The equivalence is stated with D's `CuspForm.newSubspace` and `CuspForm.oldSubspace` unchanged.
