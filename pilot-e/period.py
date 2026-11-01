"""Function-field Hecke period (BZSV: X = PGL_2/G_m, dual T^*(std)) twisted by quadratic characters.

For a rational newform f in S(Gamma_0(n)) and a monic squarefree D of even degree, coprime to n,
with chi = (./D) on (A/D)^*, define the twisted Hecke (Birch) period as a Laurent polynomial in z:

  Lambda_D(f; z) = sum_{a mod D, (a,D)=1} chi(a) sum_{k in Z} f( v(k, a/D) -> v(k+1, a/D) ) z^k,

with v(k, u) the vertex [[pi^k, u],[0,1]] O^2 (pi = 1/t), i.e. the geodesic from the cusp oo to the
cusp a/D, weighted by |pi^k|-powers.  (Along the split torus diag(y,1), y in F_oo^*, this is the
adelic Hecke integral of the translate of f by [[1, a/D],[0,1]] against chi |.|^s.)

The curve side is independent: L(E^D, T) from point counts on E (a_P(E^D) = (D/P) a_P(E)).
We test  Lambda_D(f; z) = kappa(f) * eps_D * z^{m} * L(E^D, z/q^?)  numerically, see results.

Usage: python3 period.py match.json curves.jsonl out.json [maxD [shard/nshards]]
  (with shards, only twists of degree maxD are computed, for newforms with index = shard mod nshards)
"""
import sys, json, itertools
from flint import nmod_poly, fmpq_mat, fmpq
from harmonic import Field, Level
from match import rational_eigenspaces, colmat


def legendre(a, P):
    """(a/P) for P monic irreducible over F_p."""
    p = P.modulus()
    a = a % P
    if a.is_zero():
        return 0
    Q = p ** P.degree()
    return 1 if a.pow_mod((Q - 1) // 2, P).is_one() else -1


def jacobi(a, D):
    s = 1
    for P, e in D.factor()[1]:
        s *= legendre(a, P) ** e
    return s


def eigenvector(L, F, lam):
    """Recover the eigenvector (in c_0-variable coordinates) whose T_P eigenvalues are lam."""
    p = F.p
    labs = [k for k in lam if len(eval(k)) - 1 <= 2][:6]
    mats = [(k, L.hecke_on_cusp(nmod_poly(list(eval(k)), p))) for k in labs]
    bounds = [int(2 * p ** ((len(eval(k)) - 1) / 2)) for k in labs]
    sp = rational_eigenspaces(mats, L.dim, bounds)
    cand = [cols for ev, cols in sp if all(ev[k] == lam[k] for k in labs)]
    assert len(cand) == 1 and len(cand[0]) == 1
    B = fmpq_mat(L.nv, L.dim, [fmpq(L.basis[j][i]) for i in range(L.nv) for j in range(L.dim)])
    v = B * colmat(cand[0], L.dim)
    vals = [v[i, 0] for i in range(L.nv)]
    # scale to primitive integer vector
    import math
    den = 1
    for x in vals:
        den = den * x.q // math.gcd(den, x.q)
    ints = [int(x * den) for x in vals]
    g = 0
    for x in ints:
        g = math.gcd(g, x)
    return [x // g for x in ints]


def value(L, c0, M1, M2):
    s, k, x = L.edge_functional(M1, M2)
    row = L.ck_value(k, x, None)
    return s * sum(r * c for r, c in zip(row, c0))


def hecke_period(L, F, c0, D, KMIN=-12, KMAX=12):
    """returns dict k -> coefficient of z^k of Lambda_D."""
    p = F.p
    t = F.t
    out = {}
    for a in F.polys(D.degree() - 1):
        if a.is_zero() or a.gcd(D).degree() > 0:
            continue
        chi = jacobi(a, D)
        for k in range(KMIN, KMAX + 1):
            def M(k):
                if k <= 0:
                    return (D * t ** (-k), a, F.zero, D)
                return (D, a * t ** k, F.zero, D * t ** k)
            v = value(L, c0, M(k), M(k + 1))
            if v:
                out[k] = out.get(k, 0) + chi * v
    # sanity: boundary terms must vanish
    return {k: v for k, v in out.items() if v}


def count_points_generic(a2, a4, a6, P):
    p = P.modulus()
    Q = p ** P.degree()
    e = (Q - 1) // 2
    tot = 1
    for cs in itertools.product(range(p), repeat=P.degree()):
        x = nmod_poly(list(cs), p)
        y = (x * x * x + a2 * x * x + a4 * x + a6) % P
        if y.is_zero():
            tot += 1
        elif y.pow_mod(e, P).is_one():
            tot += 2
    return tot


_EXTRA = {}


def L_twist(c, D, F, B):
    """L(E^D, T) truncated to degree B from the a_P of E; a_P for places of degree beyond the
    curve file are counted here."""
    p = F.p
    ap = {eval(k): v for k, v in c['ap'].items()}
    have = max(len(k) - 1 for k in ap)
    key = (tuple(c['a2']), tuple(c['a4']), tuple(c['a6']))
    if B > have:
        if key not in _EXTRA:
            ex = {}
            a2, a4, a6 = (nmod_poly(c[x], p) for x in ('a2', 'a4', 'a6'))
            for d in range(have + 1, B + 1):
                for P in F.irreducibles(d):
                    ex[tuple(int(x) for x in P.coeffs())] = p ** d + 1 - count_points_generic(a2, a4, a6, P)
            _EXTRA[key] = ex
        ap.update(_EXTRA[key])
    n = nmod_poly(c['n'], p)
    ser = [0] * (B + 1)
    ser[0] = 1

    def divide(ser, poly):
        out = [0] * (B + 1)
        for i in range(B + 1):
            s = ser[i] - sum(poly[j] * out[i - j] for j in range(1, min(i, len(poly) - 1) + 1))
            out[i] = s
        return out
    for key, a in ap.items():
        P = nmod_poly(list(key), p)
        d = P.degree()
        if d > B:
            continue
        if (D % P).is_zero():
            continue  # additive for E^D
        chi = legendre(D, P)
        if (n % P).is_zero():
            poly = [0] * (d + 1)
            poly[0] = 1
            poly[d] = -chi * a
        else:
            poly = [0] * (2 * d + 1)
            poly[0] = 1
            poly[d] = -chi * a
            poly[2 * d] = p ** d
        ser = divide(ser, poly[:B + 1] + [0] * max(0, B + 1 - len(poly)))
    # place at oo: D monic of even degree, E^D has the same (multiplicative) reduction as E at oo
    aoo = 1 if c['oo_split'] else -1
    ser = divide(ser, [1, -aoo])
    return ser


def main():
    mfile, cfile, outfn = sys.argv[1], sys.argv[2], sys.argv[3]
    maxD = int(sys.argv[4]) if len(sys.argv) > 4 else 2
    shard, nshard = (int(x) for x in sys.argv[5].split('/')) if len(sys.argv) > 5 else (0, 1)
    fcount = -1
    M = json.load(open(mfile))
    p = M['curves'][0]['p']
    F = Field(p)
    curves = M['curves']
    B = max(len(eval(k)) - 1 for k in curves[0]['ap'])
    res = []
    for r in M['levels']:
        if not r['systems']:
            continue
        n = nmod_poly(r['n'], p)
        if n.degree() != 3:
            continue
        L = None
        for i, s in enumerate(r['systems']):
            if s['old']:
                continue
            fcount += 1
            if fcount % nshard != shard:
                continue
            cs = [c for c in curves if c['n'] == r['n'] and c.get('match') == [i] and c['oo_split']]
            c = cs[0]
            if L is None:
                L = Level(F, n)
                L.build()
            c0 = eigenvector(L, F, s['lam'])
            for dD in range(2 if nshard == 1 else maxD, maxD + 1, 2):
                for D in F.monic(dD):
                    fac = D.factor()[1]
                    if any(e > 1 for _, e in fac) or D.gcd(n).degree() > 0:
                        continue
                    lam = hecke_period(L, F, c0, D)
                    degL = n.degree() - 3 + 2 * dD
                    Lser = L_twist(c, D, F, max(B, degL))
                    res.append(dict(n=r['n'], sys=i, curve=[c['a2'], c['a4'], c['a6']], D=[int(x) for x in D.coeffs()],
                                    period={str(k): v for k, v in sorted(lam.items())}, L=Lser, degL=degL))
                    print(r['n'], i, D, sorted(lam.items()), Lser, flush=True)
    json.dump(res, open(outfn, 'w'))


if __name__ == '__main__':
    main()
