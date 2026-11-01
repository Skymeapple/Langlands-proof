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

## Milestone 2: SO(5)×SO(4) periods of Saito–Kurokawa forms (folder `so5/`)

**Why this case.** A literature check showed that the tempered rank-2 period formulas we can
reach are already theorems: Bessel periods (Furusawa–Morimoto), Yoshida lifts for SO(5)×SO(4)
(Liu; Corbett), and the classical rank-1 cases. The open tempered cases, such as general-type Siegel
forms against SO(4), need degree-16 L-functions that are out of reach here. So we took the
*non-tempered* Saito–Kurokawa (SK) packet on the **definite** inner form. BZSV and the
non-tempered Gan–Gross–Prasad conjecture predict which periods vanish and what L-value
governs the rest. The L-values factor into GL2 pieces we can compute. The split-group
analogue is a theorem: Ichino 2005, and arXiv:1804.02352 at squarefree level. In a quick search I
found no published version on the definite form.

**Setup.** O is a maximal order in the quaternion algebra ramified at {p, ∞}. The quinary lattice
is L = ⟨1⟩ ⊕ (O, nrd), with SO(4) = SO(O, nrd) the stabiliser of the unit vector. We enumerate
the genus classes of L and of (O, nrd) by Kneser 3-neighbours, and take Hecke eigenforms
from the 3-, 5- and 7-neighbour operators. The quinary 3-neighbour eigenvalue is
a₃(f) + 12 on SK(f) and 3a₃(g) + a₃(f) on Yoshida(g, f), and every quinary eigenform was sorted
this way. The period is P(F, G) = Σ_{[L']} F(L')/|O(L')| · Σ_{v ∈ L', Q(v)=1, B(v,L') ⊆ 2Z} G([v^⊥]).
The norms are ⟨F,F⟩ = Σ F²/|O(L')| and ⟨G,G⟩ = Σ G²/|O(M)|.

**Empirical formula.** Take f a weight-4 newform of level p with root number ε_f, F the SK
eigenform attached to f, and G the SO(4) eigenform attached to g⊗g with g a weight-2 newform
of level p. Then

  |P(F,G)|² / (⟨F,F⟩⟨G,G⟩) = 3/(8π³) · L(f × Sym²g, 3) / ( ‖f‖² · L(f, 3) · (p − ε_f) ),

where ‖f‖² = ∫_{Γ0(p)\H} |f|² y⁴ dx dy/y² (the weight-4 Petersson norm, PARI's `mfpetersson` times p+1) and L-values are in arithmetic normalisation
(centre 3 for f × Sym²g).

| Prediction | Data | Outcome |
|---|---|---|
| S1: P = 0 when σ = g₁⊗g₂ with g₁ ≠ g₂ (σ not *relevant* to the SK parameter f ⊞ S₂ in non-tempered GGP), although L(f×g₁×g₂) ≠ 0 | 29 pairs at p = 23, 29, 31, 43 | **Matched**: all \|P\|² < 10⁻⁷³ |
| S2: P = 0 for σ = Eis ⊗ g | 69 pairs | **Matched**: all zero |
| S3: for σ = g⊗g, \|P\|² ∝ L(1/2, f × Sym²g)/(L(1, Ad f) L(3/2, f)), with the constant above | 88 (f, g) pairs over p = 11, 23, 29, 31, 37, 43; 58 with ε_f = +1, 30 with ε_f = −1 | **Matched**: every ratio equals 1 to within 2·10⁻¹¹ |

Points worth noting:
- The factor L(1/2, f) in L(1/2, ψ×σ) cancels against the same factor in L(1, Ad ψ) for
  ψ = f ⊞ S₂. So the formula holds even when ε_f = −1 and L(f×g×g) vanishes identically, where
  the naive "period² ∝ L(1/2, ψ×σ)" reading would wrongly predict P = 0.
- The only dependence on p and on the packet is the factor 1/(p − ε_f). It is presumably the
  local factor at p, since our lattice is not maximal at p, and both SK packet members appear.
- The g-dependence cancels completely: no ‖g‖² or L(1, Ad g) term survives.
- Not tested: σ = Eis ⊗ Eis (27 nonzero periods), and the Yoshida and "other" quinary forms.

**Caveats.** This is a numerically discovered formula, not a proof. "Matched" means the BZSV and
non-tempered GGP shape holds and a single constant fits all 88 cases. The constant 3/(8π³) and
the factor (p − ε_f) depend on our measure and lattice normalisations. At p = 43, building
L(f × Sym²g) directly from its Euler product failed the functional-equation check for the
quadratic-field form g, for a reason I have not found. Those 30 values were instead obtained as
L(f×g×g, 3)/L(f, 2), or as the ratio of first derivatives when ε_f = −1, from the triple-product
L-function, which passes its check (to 10⁻³³ or better). For rational g at 43 the two routes agree.

Reproduce from `so5/`: `python3 so5run.py <p>` (genera, Hecke matrices, perp counts), `python3 analyse.py <p>`
(eigenforms, periods), `python3 fvals.py 11 23 29 31 37 43`, `python3 sym2.py <p> 150000`, and
`python3 fix43.py` for p = 43. Results: `so5/results/so5_summary.json`.

## Next steps

1. Translate the classical constants 8π² and 2⁷π⁵/p into BZSV's normalization (Tamagawa
   measures and the local unramified factors) and check the ramified local factor at p
   against their local conjecture.
2. Have an expert check whether the SO(5)×SO(4) formula above is already in the literature, and
   derive the local factor (p − ε_f) at p from the non-maximal lattice.
3. Extend to the maximal quinary lattice (paramodular level), the Eis ⊗ Eis periods, and the
   general-type forms that appear from p = 61 on.
