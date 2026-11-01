# Pilot E: GL2 Langlands data over F_3(t) and F_5(t), computed from scratch

This folder builds a dataset that matches Hecke eigenvalues of automorphic forms over F_q(t) with
Frobenius traces of elliptic curves over F_q(t). It also checks one relative Langlands (BZSV)
period over a function field. Nothing here uses LMFDB. Everything is plain Python 3 with
`pip install python-flint numpy`.

## Results

| Claim | Status | Evidence |
|---|---|---|
| Every elliptic curve E/F_3(t) with χ = 1, multiplicative reduction at ∞ and finite conductor n of degree ≤ 4 (744 curves) has a_P(E) equal to the T_P eigenvalue of exactly one rational newform of level Γ0(n), for every place P ∤ n of degree ≤ 4 | checked by computation | `data/match_q3.json`, `data/curves_q3.csv` |
| The same over F_5(t), deg n ≤ 3, places of degree ≤ 3 (880 curves) | checked by computation | `data/match_q5.json`, `data/curves_q5.csv` |
| Converse: every rational newform of level n is matched, by at least one curve split at ∞ and one non-split at ∞. That is 186 newforms over F_3(t) (deg n ≤ 4) and 140 over F_5(t) (deg n = 3). Old eigensystems (90 for q = 3, each with multiplicity 2) match no curve | checked by computation | `analyze.py` output below |
| Twisted Hecke period identity Λ_D(f; z) = κ_f · z · L(E^D, z/q) as polynomials, with κ_f = ±q(q−1) independent of D. Tested for all newforms of degree-3 level and all monic squarefree D of degree 2 prime to n: 96 checks for q = 3 and 1,820 for q = 5, all exact | checked by computation (the identity itself is the function-field Hecke/Birch formula; we did not prove it here) | `data/period_q*.json`, `check_period.py` |

"Rational newform" means a simultaneous eigenvector with integer eigenvalues for all T_P with
deg P ≤ 2 (P ∤ n), whose eigensystem does not occur at a proper divisor level. Its eigenvalues
at the remaining places are then read off one Hecke row at a time.

Why the converse matters: by Drinfeld's theorem, isogeny classes of non-isotrivial E with
conductor n·∞ and split multiplicative reduction at ∞ correspond to rational newforms of level n.
Since every rational newform is hit, the curve list is complete up to isogeny, including curves
with χ > 1, which the enumeration does not search directly.

### Sign rule found

The newform attached to E has λ_P = a_P(E) when E is split multiplicative at ∞, and
λ_P = (−1)^deg P · a_P(E) when it is non-split. The non-split curve is the unramified quadratic
twist of a split one, so this is the expected twist by the sign character of the degree.

### Period check (the BZSV part)

This is the simplest BZSV pair, X = PGL2/G_m (Hecke's period) with dual T*(std). For the newform
f and a quadratic character χ = (·/D),

    Λ_D(f; z) = Σ_{a mod D, (a,D)=1} χ(a) Σ_{k∈Z} f(v(k, a/D) → v(k+1, a/D)) z^k,

where v(k, u) is the vertex [[π^k, u],[0,1]] of the Bruhat–Tits tree (π = 1/t). This is the sum
along the geodesic from ∞ to the cusp a/D, which is the split-torus integral of a unipotent
translate of f against χ|·|^s. On the curve side, L(E^D, T) is computed by its Euler product from
point counts on E, with no functional equation used. The two sides agree coefficient by coefficient.
At z = 1 this says the Hecke period equals the central value L(E^D, 1/q) up to κ_f. 1,121 of the
1,916 twists have central value 0, and the period vanishes exactly in those cases.

## Method

* `harmonic.py`: cuspidal harmonic cochains for Γ0(n) ⊂ GL2(F_q[t]). It works on the quotient of
  the Bruhat–Tits tree by GL2(A), the half line v_0 − v_1 − …. A Γ0(n)-invariant cochain is a family
  c_k on P^1(A/n). Harmonicity at v_k (k ≥ 1) determines c_k from c_{k−1}, so the unknowns are the
  B(F_q)-invariant functions c_0. The conditions are harmonicity at v_0 and c_K = 0 (cuspidality).
  Hecke operators act through the q^deg P + 1 matrices of determinant P. To evaluate f on an arbitrary
  edge, `reduce_vertex` column-reduces adj(M) over F_q[t] (Popov form) to get M·O² = γ·v_k.
  Checks: dim S(n) equals the genus of X_0(n) for prime n (q for deg 3, q² for deg 4 when q = 3),
  is independent of the cuspidality cutoff K, and the T_P commute.
* `curves.py`: Tate's algorithm for y² = x³ + a2x² + a4x + a6 at any place, including ∞ and the wild
  case p = 3. Conductor exponents come from Ogg's formula. a_P comes from point counts. Validated on 50
  random curves: deg L(E,T) from the Euler product equals deg N − 4 in every case.
* `enumerate_curves.py`: one model per isomorphism class (normal forms in the docstring). A
  discriminant prefilter is followed by Tate's algorithm at every bad place.
* `match.py`, `analyze.py`: rational eigenspaces, matching, new/old classification.
* `period.py`, `check_period.py`: the twisted Hecke period and the comparison with L(E^D, T).
* `export.py`: CSV tables.

## Reproduce

    python3 enumerate_curves.py 3 4 4 data/curves_q3.jsonl     # ~5 s
    python3 enumerate_curves.py 5 3 3 data/curves_q5.jsonl     # ~30 s
    python3 match.py 3 4 2 data/match_q3.json data/curves_q3.jsonl   # ~40 s
    python3 match.py 5 3 2 data/match_q5.json data/curves_q5.jsonl   # ~70 s
    python3 analyze.py data/match_q3.json; python3 analyze.py data/match_q5.json
    python3 period.py data/match_q3.json x data/period_q3.json 2; python3 check_period.py data/period_q3.json 3
    python3 period.py data/match_q5.json x data/period_q5.json 2; python3 check_period.py data/period_q5.json 5
    python3 export.py

## Scope and limits

* The curve search covers χ = 1 (rational elliptic surfaces) with ∞ multiplicative. Every curve of
  conductor degree 4 or 5 with a degree-1 multiplicative place can be moved to this form by an
  automorphism of P^1. Completeness up to isogeny for all χ comes from the converse check above.
* Curves with no degree-1 multiplicative place need automorphic forms with other level structure at
  ∞. They are not covered.
* Matching is on finitely many places (deg ≤ 4 for q = 3, deg ≤ 3 for q = 5). That two Hecke
  eigensystems agreeing at these places agree everywhere is a theorem (strong multiplicity one with
  explicit bounds), not something checked here.
