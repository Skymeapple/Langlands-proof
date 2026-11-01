"""Triple product period (GGP for SO(3) in SO(4), i.e. B^x diagonal in B^x^3; Ichino's formula)
over F_q(t), on the definite quaternion algebra B ramified at {P, oo} with an Eichler order of level M.

For rational newforms f1, f2, f3 of the same level n = P M (deg n = 3):
  period    I(f1,f2,f3) = sum over classes x of f1_D(x) f2_D(x) f3_D(x) / #Stab_x,
  L-value   L(f1 x f2 x f3, T) at the centre T = q^-2, from the Euler product of the three curves:
     good v:  det(1 - Frob T^d) on the tensor product of the three 2-dim Frobenius modules,
     v | n oo (all three Steinberg, eps = a1 a2 a3):  (1 - eps T^d)^-1 (1 - eps q^d T^d)^-2.
We record X = L * prod <f_i, f_i>_D / (I^2 * prod ||f_i||^2_Pet) and test whether it is constant.
Usage: python3 triple.py p match.json out.json
"""
import sys, json, itertools
from fractions import Fraction as Fr
from flint import nmod_poly, fmpz_mat
from harmonic import Field, Level
from quaternion import Eichler
from period import eigenvector, count_points_generic
from gross import petersson


def kron(A, B):
    n, m = len(A), len(B)
    return [[A[i // m][j // m] * B[i % m][j % m] for j in range(n * m)] for i in range(n * m)]


def local_poly_good(aps, qd, d, B):
    """1 - ... polynomial in T (truncated to deg B) for det(1 - Frob T^d) on the triple tensor."""
    C = [[0, -qd], [1, aps[0]]]
    M = C
    for a in aps[1:]:
        M = kron(M, [[0, -qd], [1, a]])
    cp = fmpz_mat(M).charpoly()  # det(x - M) = sum c_k x^k ; det(1 - M T) = sum c_k T^(8-k)
    cs = [int(c) for c in cp.coeffs()]
    deg = len(cs) - 1
    poly = [0] * (B + 1)
    for k, c in enumerate(cs):
        e = (deg - k) * d
        if e <= B:
            poly[e] += c
    return poly


def series_divide(ser, poly, B):
    out = [0] * (B + 1)
    for i in range(B + 1):
        out[i] = ser[i] - sum(poly[j] * out[i - j] for j in range(1, i + 1) if j < len(poly))
    return out


def ap_table(c, p, B, F):
    ap = {tuple(eval(k)): v for k, v in c['ap'].items()}
    have = max(len(k) - 1 for k in ap)
    if B > have:
        a2, a4, a6 = (nmod_poly(c[x], p) for x in ('a2', 'a4', 'a6'))
        for d in range(have + 1, B + 1):
            for P in F.irreducibles(d):
                ap[tuple(int(x) for x in P.coeffs())] = p ** d + 1 - count_points_generic(a2, a4, a6, P)
    return ap


def triple_L(cs, p, n, B, F, tabs):
    ser = [1] + [0] * B
    for key in tabs[0]:
        P = nmod_poly(list(key), p)
        d = P.degree()
        if d > B:
            continue
        aps = [t[key] for t in tabs]
        if (n % P).is_zero():
            eps = aps[0] * aps[1] * aps[2]
            for poly in ([1] + [0] * (d - 1) + [-eps], [1] + [0] * (d - 1) + [-eps * p ** d],
                         [1] + [0] * (d - 1) + [-eps * p ** d]):
                ser = series_divide(ser, poly, B)
        else:
            ser = series_divide(ser, local_poly_good(aps, p ** d, d, B), B)
    eps = 1  # newforms on harmonic cochains are Steinberg (untwisted) at oo
    for poly in ([1, -eps], [1, -eps * p], [1, -eps * p]):
        ser = series_divide(ser, poly, B)
    return ser


def main():
    p, mfile, outfn = int(sys.argv[1]), sys.argv[2], sys.argv[3]
    B = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    F = Field(p)
    Mj = json.load(open(mfile))
    curves = Mj['curves']
    nu = next(c for c in range(2, p) if pow(c, (p - 1) // 2, p) == p - 1)
    res = []
    for r in Mj['levels']:
        n = nmod_poly(r['n'], p)
        if n.degree() != 3 or not r['systems']:
            continue
        Ps = [P for P, e in n.factor()[1] if P.degree() == 1 and e == 1]
        if not Ps:
            continue
        P = Ps[0]
        M = n // P
        E = Eichler(p, P, M, nu)
        E.classes()
        h = len(E.orbs)
        ells = [l for d in (1, 2) for l in F.irreducibles(d) if not (n % l).is_zero()]
        Bs = {str(l): E.brandt(l) for l in ells}
        Lh = Level(F, n)
        Lh.build()
        forms = []
        for si, s in enumerate(r['systems']):
            if s['old']:
                continue
            lam = {str(nmod_poly(list(eval(k)), p)): v for k, v in s['lam'].items()}
            rows = []
            for l in ells:
                Bm = Bs[str(l)]
                for i in range(h):
                    rows.append([Bm[i][j] - (lam[str(l)] if i == j else 0) for j in range(h)])
            X, nul = fmpz_mat(rows).nullspace()
            assert nul == 1
            fD = [int(X[i, 0]) for i in range(h)]
            ff = sum(Fr(fD[i] ** 2, E.stab[i]) for i in range(h))
            pet = petersson(Lh, eigenvector(Lh, F, s['lam']), p)
            c = [c for c in curves if c['n'] == r['n'] and c.get('match') == [si] and c['oo_split']][0]
            forms.append(dict(si=si, fD=fD, ff=ff, pet=pet, tab=ap_table(c, p, B, F)))
        for trip in itertools.combinations_with_replacement(range(len(forms)), 3):
            fs = [forms[i] for i in trip]
            I = sum(Fr(fs[0]['fD'][x] * fs[1]['fD'][x] * fs[2]['fD'][x], E.stab[x]) for x in range(h))
            Ls = triple_L(None, p, n, B, F, [f['tab'] for f in fs])
            Lc = sum(Fr(Ls[i], p ** (2 * i)) for i in range(B + 1))
            bad = []
            for Q_, e_ in n.factor()[1]:
                key = tuple(int(x) for x in Q_.coeffs())
                bad.append((Q_.degree(), e_, fs[0]['tab'][key] * fs[1]['tab'][key] * fs[2]['tab'][key], (Q_ - P).is_zero()))
            rec = dict(bad=bad, n=r['n'], P=[int(x) for x in P.coeffs()], forms=[f['si'] for f in fs],
                       period=str(I), L=str(Lc), Lpoly=Ls,
                       ff=[str(f['ff']) for f in fs], pet=[str(f['pet']) for f in fs])
            if I:
                X = Lc * fs[0]['ff'] * fs[1]['ff'] * fs[2]['ff'] / (I * I * fs[0]['pet'] * fs[1]['pet'] * fs[2]['pet'])
                rec['X'] = str(X)
            res.append(rec)
            print(r['n'], [f['si'] for f in fs], 'I', I, 'Lpoly', Ls, 'L', Lc, rec.get('X'), flush=True)
    json.dump(res, open(outfn, 'w'))


if __name__ == '__main__':
    main()
