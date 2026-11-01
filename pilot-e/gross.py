"""Gross / Waldspurger toric period over F_q(t) on the definite quaternion algebra ramified at {P, oo}.

For each rational newform f of level n = P M (deg n = 3, P of degree 1 exactly dividing n):
  * f_D = Brandt eigenvector on P^1(A/M)/(O^*/F_q^*) with the same T_l eigenvalues (Jacquet-Langlands),
  * for D0 squarefree with oo not split in K = F(sqrt D0), P inert in K, primes of M split in K:
      period  P_D0 = sum over Gross points y (y^2 = D0, fixed orientations) of f_D(x_y),
      L-value L(E^{D0}, 1/q) from the Euler product of the curve E (independent of the quaternion side),
  * ratio R = L(E^{D0}, 1/q) * <f,f> * q^{deg D0 / 2} / P_D0^2, with <f,f> = sum_i f_i^2 / #Stab_i.
Usage: python3 gross.py p match.json out.json maxdegD0
"""
import sys, json, itertools
from fractions import Fraction
from flint import nmod_poly, fmpz_mat
from harmonic import Field
from quaternion import Eichler
from period import legendre, count_points_generic, eigenvector
from harmonic import Level


def L_twist_general(c, D0, nuflag, p, B):
    """L(E^{D0}, T) mod T^(B+1); D0 = (nu if nuflag) * monic; oo ramified if deg odd, inert if nuflag."""
    F = Field(p)
    ap = {tuple(eval(k)): v for k, v in c['ap'].items()}
    have = max(len(k) - 1 for k in ap)
    a2, a4, a6 = (nmod_poly(c[x], p) for x in ('a2', 'a4', 'a6'))
    for d in range(have + 1, B + 1):
        for P in F.irreducibles(d):
            k = tuple(int(x) for x in P.coeffs())
            if k not in c.setdefault('_extra', {}):
                c['_extra'][k] = p ** d + 1 - count_points_generic(a2, a4, a6, P)
        ap.update(c['_extra'])
    for k, v in c.get('_extra', {}).items():
        ap[k] = v
    n = nmod_poly(c['n'], p)
    ser = [0] * (B + 1)
    ser[0] = 1

    def divide(ser, poly):
        poly = poly[:B + 1] + [0] * max(0, B + 1 - len(poly))
        out = [0] * (B + 1)
        for i in range(B + 1):
            out[i] = ser[i] - sum(poly[j] * out[i - j] for j in range(1, i + 1))
        return out
    for key, a in ap.items():
        P = nmod_poly(list(key), p)
        d = P.degree()
        if d > B or (D0 % P).is_zero():
            continue
        chi = legendre(D0, P)
        if (n % P).is_zero():
            poly = [1] + [0] * (d - 1) + [-chi * a]
        else:
            poly = [1] + [0] * (d - 1) + [-chi * a] + [0] * (d - 1) + [p ** d]
        ser = divide(ser, poly)
    aoo = 1 if c['oo_split'] else -1
    if nuflag:
        ser = divide(ser, [1, aoo])   # oo inert in K: twist is the other multiplicative type
    elif D0.degree() % 2 == 0:
        ser = divide(ser, [1, -aoo])  # oo split (not used)
    # oo ramified: additive, factor 1
    return ser


def petersson(L, c0, p):
    """sum over edges of Gamma_0(n)\\T of f(e)^2 / #Stab(e) (stabilisers modulo the centre F_q^*),
    = sum_k sum_{x in P^1(A/n)} c_k(x)^2 / #(Stab(e_k)/Z)."""
    tot = Fraction(0)
    k = 0
    zero_run = 0
    while zero_run < 3:
        rows = L.ck_value(k, 0, None) and L.C[k]
        s = 0
        for x in range(L.N):
            v = sum(a * b for a, b in zip(L.C[k][x], c0))
            s += v * v
        order = p * (p - 1) if k == 0 else (p - 1) * p ** (k + 1)
        tot += Fraction(s, order)
        zero_run = zero_run + 1 if s == 0 else 0
        k += 1
    return tot


def main():
    p, mfile, outfn, maxd = int(sys.argv[1]), sys.argv[2], sys.argv[3], int(sys.argv[4])
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
        for si, s in enumerate(r['systems']):
            if s['old']:
                continue
            c0 = eigenvector(Lh, F, s['lam'])
            pet = petersson(Lh, c0, p)
            lam = {str(nmod_poly(list(eval(k)), p)): v for k, v in s['lam'].items()}
            rows = []
            for l in ells:
                B = Bs[str(l)]
                for i in range(h):
                    rows.append([B[i][j] - (lam[str(l)] if i == j else 0) for j in range(h)])
            X, nul = fmpz_mat(rows).nullspace()
            assert nul == 1
            fD = [int(X[i, 0]) for i in range(h)]
            ff = sum(Fraction(fD[i] ** 2, E.stab[i]) for i in range(h))
            c = [c for c in curves if c['n'] == r['n'] and c.get('match') == [si] and c['oo_split']][0]
            for dD in range(1, maxd + 1):
                for D1 in F.monic(dD):
                    if any(e > 1 for _, e in D1.factor()[1]) or D1.gcd(n).degree() > 0:
                        continue
                    for nuflag in ((False,) if dD % 2 else (True,)):
                        D0 = D1 * nu if nuflag else D1
                        if legendre(D0, P) != -1:
                            continue
                        if any(legendre(D0, l) != 1 for l, e in M.factor()[1]):
                            continue
                        pts = E.gross_points(D0)
                        per = sum(fD[E.cls[x]] for x in pts)
                        degL = 2 * dD + (0 if nuflag else 1)
                        Ls = L_twist_general(c, D0, nuflag, p, degL)
                        Lval = sum(Fraction(Ls[i], p ** i) for i in range(degL + 1))
                        rec = dict(petersson=str(pet), n=r['n'], P=[int(x) for x in P.coeffs()], sys=si,
                                   D0=[int(x) for x in D0.coeffs()], npoints=len(pts), period=per,
                                   ff=str(ff), Lpoly=Ls, L=str(Lval))
                        if per:
                            R = Lval * ff * Fraction(p ** dD) / per ** 2  # R^2-normalised: compare R vs q^{deg D0}
                            rec['ratio_times_qdeg_over_P2'] = str(R)
                        res.append(rec)
                        print(r['n'], si, D0, 'pts', len(pts), 'P', per, 'ff', ff, 'L', Lval,
                              rec.get('ratio_times_qdeg_over_P2'), flush=True)
    json.dump(res, open(outfn, 'w'))


if __name__ == '__main__':
    main()
