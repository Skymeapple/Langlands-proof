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
| Twisted Hecke period identity Λ_D(f; z) = ε_f (q−1) q^{deg D/2} · z · L(E^D, z/q) as polynomials, where ε_f = ±1 depends only on f (the sign of the primitive normalization). Tested for all newforms of degree-3 level and all monic squarefree D of degree 2 prime to n (96 checks for q = 3, 1,820 for q = 5), and for D of degree 4 over F_3(t) on 12 newforms (365 checks). All 2,281 are exact | checked by computation (the identity is the function-field Hecke/Birch formula; we did not prove it here) | `data/period_q*.json`, `check_period.py` |
| Jacquet–Langlands: for the definite quaternion algebra ramified at {P, ∞} (deg P = 1) and an Eichler order of level M (n = PM), the Brandt matrices have a 1-dimensional common eigenspace for every rational newform of level n, with the same T_ℓ eigenvalues | checked by computation | `quaternion.py`, `gross.py` |
| Gross/Waldspurger toric period (BZSV X = PGL2/T, T a non-split torus, on the definite inner form). L(E^{D0}, 1/q) · ⟨f_D, f_D⟩ · \|d_K\|^{1/2} = c · P_{D0}(f)² · ‖f‖², with P_{D0} the sum of f_D over Gross points in Pic(O_K) and ‖f‖² the Petersson norm of the primitive harmonic cochain. c = 2 when ∞ ramifies in K and c = 1 when ∞ is inert. Holds with this one constant in all 603 non-vanishing cases (74 over F_3(t) with deg D0 ≤ 3, 529 over F_5(t) with deg D0 ≤ 2). The period vanishes exactly when the L-value does, in all 52 vanishing cases | checked by computation (empirical constant; it should follow from the function-field Gross formula, but we did not derive the constant) | `data/gross_q*.json`, `check_gross.py` |

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

### Gross / Waldspurger period (non-split torus)

D = (ν, P) with ν a non-square constant and deg P = 1 is ramified exactly at P and ∞.
O = A⟨1, i, j, ij⟩ is maximal with class number 1 and O^× = F_{q²}^×. So the Brandt module of the
Eichler order of level M is the set of functions on P^1(A/M)/(O^×/F_q^×), with O acting through an
explicit isomorphism O/MO ≅ M_2(A/M). For K = F(√D0) with P inert, the primes of M split and ∞
not split, the Gross points are y ∈ O with y² = D0 (with fixed orientations at P and M). Each
CM point of Pic(O_K) appears q + 1 times among the y, and `check_gross.py` divides the raw sum by
(q + 1) to get P_{D0}. The L-value comes from point counts on E alone. Note L(E, 1/q) = 1 here
(deg N = 4), so L(E_K, 1) = L(E^{D0}, 1/q).

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
    python3 period.py data/match_q3.json x data/period_q3_D4_s0.json 4 0/10   # shards 0..3 of degree-4 twists
    python3 gross.py 3 data/match_q3.json data/gross_q3.json 3; python3 check_gross.py data/gross_q3.json 3
    python3 gross.py 5 data/match_q5.json data/gross_q5.json 2; python3 check_gross.py data/gross_q5.json 5
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

## Round 3: triple product period, and the SO(5) question

### SO(5) × SO(4) (Saito–Kurokawa) over F_q(t): stalled, with a structural reason

Over Q, Pilot C uses the definite SO(5) of the lattice ⟨1⟩ ⊕ (O, nrd). Over F_q(t) there is no
such group. Every quadratic form of dimension ≥ 5 over the local field F_q((1/t)) is isotropic, so
SO(5) is never compact at ∞, and the finite class-set method has no analogue. A real analogue needs
automorphic forms on SO(5) acting on its Bruhat–Tits tree at ∞ (the ∞-rank is 1), including cusps,
plus the non-tempered Saito–Kurokawa packet at ∞. That is a separate build and is not attempted here.

### Triple product (GGP for SO(3) ⊂ SO(4), Ichino): checked by computation

`triple.py`, `check_triple.py`. Take three rational newforms f1, f2, f3 of one level n = P·M,
deg n = 3, with Brandt eigenvectors on the definite algebra ramified at {P, ∞} (Eichler level M).
Set I = Σ_x f1(x) f2(x) f3(x) / #Stab_x. The L-function L(f1 × f2 × f3, T) is the Euler product
of the triple tensor of the three curves' Frobenius modules. At the bad places, with all three
Steinberg and ε_v = a1 a2 a3, the factor is (1 − ε_v T^d)^{-1} (1 − ε_v q^d T^d)^{-2}. It
terminates at degree ≤ 4, which was checked through degree 5 over F_3(t). The centre is T = q^{-2}.

For squarefree n:

* If ε_P = +1 and ε_ℓ = −1 for every ℓ | M (the local signs that allow a period on this B), then
  L(f1×f2×f3, q^{-2}) · Π ⟨f_i, f_i⟩_D = I² · Π ‖f_i‖²_Pet / (2^{ω(M)} q^4).
  This holds in 33 of 33 cases (9 over F_3(t), 24 over F_5(t)), 4 of them with L = 0 and I = 0.
* For every other sign pattern, I = 0. That is 116 of 116 cases, and in 104 of them L ≠ 0.
  This is Prasad's dichotomy: the period then lives on a different quaternion algebra.

The constant 2^{ω(M)} q^4 is empirical.

**Levels M = ℓ² (424 cases, `check_triple_l2.py`).** Here each curve is additive at ℓ with conductor
exponent 2 (tame). Its local representation is labelled from the Kodaira type:
* I_n* gives St⊗χ;
* III/III* has e = 4, IV/IV* has e = 3, II/II* has e = 6;
* the representation is principal series (ps) if q ≡ 1 mod e and supercuspidal (sc) otherwise.

Result (checked by computation): the 424 cases fall into 24 classes, keyed by the three local labels
at ℓ and ε_P. In **every class the ratio X = L·Π⟨f_i,f_i⟩_D / (I²·Π‖f_i‖²) takes exactly one value**,
and whether I vanishes is decided by the class alone. So the identity holds with a local constant
c_ℓ(τ1, τ2, τ3) that depends only on the local types. The constants are in
`data/check_triple_l2_q*.txt`; for example, 1/900 for (St⊗χ)³ and 1/2250 for (sc6)³ when q = 5.
I = 0 in every class with ε_P = −1. It also vanishes for the class (St⊗χ, sc6, sc6) with ε_P = +1,
where L ≠ 0, which points to a local sign −1 at ℓ.

What is not resolved: (i) the constants c_ℓ are tabulated, not derived. That needs Ichino's local
integral for depth-zero supercuspidal and St⊗χ new vectors. (ii) The local L-factor at ℓ of the triple
tensor was not computed from first principles. In 320 cases the Euler product without an ℓ-factor is a
polynomial that satisfies the expected functional equation, consistent with L_ℓ = 1. In 104 cases
(4 classes) it is one fixed polynomial per class that does not, so L_ℓ is non-trivial there (the triple
tensor has inertia invariants). The constant for those classes absorbs it. All local data is in
`data/triple_local_data_q*.csv`.

    python3 triple.py 3 data/match_q3.json data/triple_q3.json 5; python3 check_triple.py data/triple_q3.json 3
    python3 triple.py 5 data/match_q5.json data/triple_q5.json 4; python3 check_triple.py data/triple_q5.json 5
    python3 check_triple_l2.py 3; python3 check_triple_l2.py 5; python3 export_triple.py
