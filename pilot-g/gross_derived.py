"""Test the Gross constant derived from Waldspurger's formula (see DERIVATION.md, section 1)
against Pilot E's stored toric periods, with no fitted constant.

Derived prediction, for every non-vanishing case:
    P_Pic^2 / <f_D, f_D>  =  |d_K|^{1/2} * L(E^{D0}, 1/q) / ( kappa * q^2 * L^{add}(1, pi, Ad) )
kappa = 2 if oo is ramified in K, 1 if oo is inert, and L^{add}(1, Ad) the adjoint L-value with the
Euler factors at additive places of E removed (at multiplicative places they are kept). L(1, Ad) = L(Sym^2 E, q^-2) is
computed here from Frobenius traces (independent of the automorphic side).
Second statement checked: ||f||^2_Pet = q^2 * L^{add}(1, pi, Ad); together they give E's c = kappa.
Usage: python3 gross_derived.py q gross_q*.json match_q*.json"""
import sys, json, ast
from fractions import Fraction as Fr
from collections import Counter
from flint import nmod_poly
from adjoint import partial_sym2
q = int(sys.argv[1])
G = json.load(open(sys.argv[2])); Mj = json.load(open(sys.argv[3]))


B = max(len(ast.literal_eval(k)) - 1 for k in Mj['curves'][0]['ap'])
Lad = {}
notes = Counter()
for r in G:
    key = (tuple(r['n']), r['sys'])
    if key in Lad:
        continue
    c = [c for c in Mj['curves'] if c['n'] == r['n'] and c.get('match') == [r['sys']] and c['oo_split']][0]
    ser, add = partial_sym2(c, B, q)
    if not add:
        # all multiplicative: complete L(Sym^2) has degree -6 + 2*4 = 2
        assert all(x == 0 for x in ser[3:]), 'degree > 2'
        Lad[key] = sum(x / Fr(q) ** (2 * i) for i, x in enumerate(ser[:3]))
        notes['squarefree level, L(Sym^2) polynomial of degree <= 2'] += 1
    else:
        # one additive place l of degree 1, conductor exponent 2 (tame). Sym^2 then has conductor 2 at l
        # (inertia invariants of dimension 1), so the complete L(Sym^2) has degree -6 + 2+2+2 = 0, i.e. is 1,
        # and the partial product (no l-factor) must equal 1/L_l = 1 - beta T with beta in {1, q, -q}.
        # What enters the derived formula is the PARTIAL value L^{(l)}(1, Ad) = 1 - beta q^-2.
        assert len(add) == 1 and len(add[0]) == 2
        assert all(x == 0 for x in ser[2:]), ('partial L(Sym^2) not of the form 1 - beta T', ser)
        beta = -ser[1]
        assert beta in (1, q, -q), beta
        Lad[key] = 1 - beta / Fr(q) ** 2
        notes['additive at l: L_l(Sym^2) = 1/(1 - %s T)' % beta] += 1

ok = bad = zero = 0
pet_ratio = Counter()
for r in G:
    L, P = Fr(r['L']), r['period']
    if P == 0 or L == 0:
        zero += 1
        continue
    d = len(r['D0']) - 1
    kappa, dK = (2, q ** (d + 1)) if d % 2 else (1, q ** d)
    Ppic = Fr(P, q + 1)
    lhs = (Ppic ** 2 / Fr(r['ff'])) ** 2
    rhs = (L / (kappa * q * q * Lad[(tuple(r['n']), r['sys'])])) ** 2 * dK     # squares: |d_K|^{1/2} may be irrational
    if lhs == rhs:
        ok += 1
    else:
        bad += 1
        print('MISMATCH', r['n'], r['sys'], r['D0'], lhs / rhs)
for key, v in Lad.items():
    r = next(r for r in G if (tuple(r['n']), r['sys']) == key)
    pet_ratio[str(Fr(r['petersson']) / v)] += 1
print(dict(q=q, nonvanishing_match=ok, mismatch=bad, vanishing_skipped=zero, newforms=len(Lad)))
print('L(1,Ad) bookkeeping:', dict(notes))
print('||f||^2 / L^add(1,Ad) over newforms:', dict(pet_ratio))
