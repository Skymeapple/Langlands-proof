# Pilot C: numerical checks of BZSV relative Langlands predictions

Ben-Zvi–Sakellaridis–Venkatesh (arXiv:2409.04677) predict that for a hyperspherical
G-variety X with dual M, the square of the automorphic period P_X(φ) equals, up to an
explicit constant made of local factors, a special value of the L-function attached to M.
Milestone 1 tests this in the smallest cases, G = PGL2 and PGL2³, on weight-2 newforms of
prime level p, using exact Brandt-module (definite quaternion) periods and L-values
computed from scratch in PARI/GP 2.17. LMFDB was not reachable from the compute
environment, so every L-value here is computed directly and its functional equation is
checked with `lfuncheckfeq`.

## Scope, stated honestly

All four predictions below are cases where a theorem already exists (Hecke; Waldspurger and
Gross 1987; Gross–Kudla 1992 / Ichino 2008; Rankin–Shimura). "Matched" therefore means the
BZSV shape (period² ∝ L-value, with vanishing forced by local or global signs) and the
classical constants are confirmed numerically on these examples. It is not new evidence for
an open case. The value is a calibrated pipeline: the same code can now be pointed at cases
with no known formula.

## Predictions and outcomes

| # | X (dual M) | Prediction | Data | Outcome |
|---|---|---|---|---|
| P1 | PGL2/Gm, Hecke (M = T*(std)) | ∫₀^∞ f(iy) dy = L(f,1)/2π, so P = 0 when ε(f) = −1 | 12 elliptic curves, conductors 11–101 | **Matched** (agree to double precision; zero exactly when ε = −1) |
| P2 | PGL2/T, nonsplit torus T = Res K/Q Gm (Waldspurger) | L(f,1)·L(f⊗χ_D,1) = 8π²‖f‖² · P_D(f)² / (√\|D\| · ⟨f,f⟩_B) for p inert in Q(√D), D < −4; P_D = 0 iff the L-value vanishes | 12 rational newforms at p ∈ {11,37,43,53,61,67,79,83,89,101}, 237 pairs (f, D), \|D\| < 120 | **Matched**: 63 nonzero periods give the constant 8π² to 25 digits at 38-digit precision; 174 zero periods all have L(f,1)L(f⊗χ_D,1) = 0 to 10⁻⁴⁰ (159 from ε(f) = −1, 15 sporadic zeros of L(f⊗χ_D,1) with ε = +1) |
| P3 | PGL2³/ΔPGL2, triple product (M = std⊗std⊗std) | L(f₁⊗f₂⊗f₃, 2) = (2⁷π⁵/p) · ‖f₁‖²‖f₂‖²‖f₃‖² · I² / ∏⟨fᵢ,fᵢ⟩_B, with I = Σᵢ f₁f₂f₃(eᵢ)/wᵢ; I = 0 whenever a_p(f₁)a_p(f₂)a_p(f₃) = −1 (local dichotomy at p) | all 14 triples at p = 37, 43 (including Galois-conjugate pairs); p = 53 see below | **Matched**: 8 nonzero triples give 2⁷π⁵/p to 13–16 digits (rational forms) and 5–6 digits (triples of the quadratic-field forms at 43, where the functional-equation check is only 10⁻¹⁶); 6 zero periods all have global sign −1 |
| P4 | Whittaker period, degenerate case (M = G^ adjoint) | ‖f‖² ∝ 1/L(1,Ad): L(Sym²f,2) = 8π³‖f‖²/p, and 4π²‖f‖² = deg(φ_E)·vol(E) | same 12 curves | **Matched** to double precision for all 12 |

Here ‖f‖² = ∫_{Γ0(p)\H} |f|² dx dy, ⟨f,f⟩_B = Σᵢ f(eᵢ)²/wᵢ on the supersingular points eᵢ
with wᵢ = #Aut(Eᵢ)/2, and P_D(f) = Σ f over the reductions mod p of the CM j-invariants of
discriminant D (the roots of the Hilbert class polynomial in F_{p²}).

Nothing was marked mismatched. Nothing was marked not computable in milestone 1, but larger
p and higher-rank X are limited by cost: the triple-product L-function has conductor p⁵, so
p = 53 already needs about 7·10⁵ Dirichlet coefficients.

## How it works

- `brandt.gp`: supersingular j-invariants over F_{p²} by walking the 2-isogeny graph from
  `ellsupersingularj`, and Brandt matrices B(ℓ) from the classical modular polynomial
  Φ_ℓ. The matrices satisfy wⱼBᵢⱼ = wᵢBⱼᵢ, so B is self-adjoint for the mass 1/wᵢ.
- `gross.py`: P2. Matches each rational newform to a Brandt eigenvector by a₂, a₃; builds
  L(f⊗χ_D, s) from twisted coefficients, picks the sign by `lfuncheckfeq`.
- `triple.gp`, `triple_run.py`: P3. Numerically embedded eigenvectors for every newform
  (rational or not); the triple L-function is built from its Euler product with
  L_p = (1 − εp^{−s})⁻¹(1 − εp^{1−s})⁻², conductor p⁵, gamma factor Γ_C(s)Γ_C(s−1)³.
  Both signs are tried and the one passing the functional equation is kept.
- `whittaker.py`: P1 and P4, using `lfunsympow` and `ellmoddegree`.
- `results/`: raw JSON output of every run.

Run with `pip install cypari2` and, from this folder, `python3 gross.py 11 37`,
`python3 triple_run.py 37 300000`, `python3 whittaker.py`.

## Next steps

1. Translate the classical constants 8π² and 2⁷π⁵/p into BZSV's normalization (Tamagawa
   measures and the local unramified factors) and check the ramified local factor at p
   against their local conjecture.
2. Point the pipeline at a case with no published formula, for example a BZSV example
   with G of rank 2 whose period is not one of the classical Rankin–Selberg, Gan–Gross–Prasad
   or Waldspurger families.
