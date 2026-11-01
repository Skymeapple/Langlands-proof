# Pilot D: Mathlib-quality modular forms infrastructure

Lean 4.33.1, Mathlib `db584cd6` (same pin as Pilot A). Depends on Mathlib only.

## Status

| Item | File | Status |
|---|---|---|
| Gauss sum of a primitive Dirichlet character is nonzero (any modulus, any domain, any primitive additive character) | `PilotD/GaussSum.lean` | proved formally |
| Twisting sum `∑ χ(a) f(τ + a/D)` of a weight-`k` cusp form on Γ₀(N) by a quadratic χ is a cusp form on Γ₀(N D²) | `PilotD/Twist.lean` | proved formally |
| Normalized twist `f ⊗ χ` has coefficients `χ(n) aₙ(f)` (χ primitive quadratic) | `PilotD/TwistQExpansion.lean` | proved formally |
| Slash by `g ∈ GL₂(ℝ)⁺` as a linear map `M_k(Γ) → M_k(Γ')` for `Γ' ≤ g⁻¹Γg`, and restriction | `PilotD/AtkinLehner.lean` | proved formally |
| Fricke matrix `W_N` normalizes Γ₀(N); the Fricke operator is an involution on `M_k(Γ₀(N))` and `S_k(Γ₀(N))` | `PilotD/AtkinLehner.lean` | proved formally |
| Level raising `B_d` (`(B_d f)(τ) = f(dτ)`), injective; trace maps as linear maps | `PilotD/Newforms.lean` | proved formally |
| Old and new subspaces; the Atkin–Lehner decomposition `S_k(Γ₀(N)) = ⨁_{Md ∣ N} B_d S_k^new(Γ₀(M))` as a statement | `PilotD/Newforms.lean` | statement compiles |
| The decomposition at level 1 | `PilotD/Newforms.lean` | proved formally |
| The decomposition for general N | | open (see below) |

Milestone 1 (Mathlib lint and style): the build runs with `linter.mathlibStandardSet` on and emits no
warnings, and `#lint in PilotD` (`Lint.lean`) reports 0 errors. Files use Mathlib's `module` syntax,
copyright headers and module docstrings.

## Design note: the new subspace

Mathlib has no Petersson inner product on `S_k(Γ)` (only the pointwise integrand), so the usual
definition "orthogonal complement of the old subspace" is not available. `newSubspace` is defined as
the common kernel of `Tr_{N/p}` and `Tr_{N/p} ∘ W_N` for primes `p ∣ N` (Serre's characterization).
Its equivalence with the Petersson definition is a known theorem that is **not** formalized here.

## Open

* `NewformDecomposition N k` for general `N`. This needs the Petersson inner product (with
  finite-dimensionality of `S_k(Γ₀(N))`), or the Atkin–Lehner main lemma on forms whose
  q-expansion is supported on `n` sharing a factor with `N`.
* General Atkin–Lehner operators `W_Q` for `Q ∥ N`.
* Bibliography keys cited in docstrings (`shimura1971`, `atkinlehner1970`) would need entries in
  Mathlib's `docs/references.bib` for an upstream PR. No PR to Mathlib has been opened.

## Build and check

```
cd pilot-d
lake build                # library, style linters on
lake build AxiomCheck     # 13 #guard_msgs checks of #print axioms
lake env lean Lint.lean   # environment linters
```

The Mathlib cache host is blocked in our container, so Mathlib builds from source (about 1.5 h on 4 cores).
