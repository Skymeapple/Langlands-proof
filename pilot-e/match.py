"""Match rational Hecke eigensystems on cuspidal harmonic cochains for Gamma_0(n) with
Frobenius traces of elliptic curves of conductor n * oo.

Usage: python3 match.py p DMAX SPLITDEG out.json curves.jsonl
  For each monic n with 1 <= deg n <= DMAX: build S(n) (cuspidal harmonic cochains),
  split it into rational eigenspaces using T_P for deg P <= SPLITDEG,
  then compute the eigenvalue of every T_P (P not dividing n, deg P <= the curves' BMAX) on each
  eigenvector from a single row, and compare with a_P of each curve of conductor n*oo:
  lambda_P = a_P            if E is split multiplicative at oo,
  lambda_P = (-1)^deg P a_P  if non-split (the unramified quadratic twist is split).
"""
import sys, json, time, itertools
from flint import fmpz_mat, fmpq_mat, fmpq, nmod_poly
from harmonic import Field, Level


def nullspace_q(A):
    """basis (list of column lists) of the kernel of an fmpq_mat A."""
    r, c = A.nrows(), A.ncols()
    den = 1
    for i in range(r):
        for j in range(c):
            den = den * A[i, j].q // __import__('math').gcd(den, A[i, j].q)
    Z = fmpz_mat(r, c, [int(A[i, j] * den) for i in range(r) for j in range(c)])
    X, nul = Z.nullspace()
    return [[fmpq(int(X[i, j])) for i in range(c)] for j in range(nul)]


def colmat(cols, nrows):
    return fmpq_mat(nrows, len(cols), [cols[j][i] for i in range(nrows) for j in range(len(cols))])


def rational_eigenspaces(mats, dim, bounds):
    """mats: list of (label, fmpq_mat dim x dim) commuting. Returns list of (eigenvalues dict, basis cols)."""
    spaces = [({}, [[fmpq(1 if i == j else 0) for i in range(dim)] for j in range(dim)])]
    for (lab, T), bd in zip(mats, bounds):
        new = []
        for ev, cols in spaces:
            S = colmat(cols, dim)
            r = len(cols)
            St = S.transpose()
            A = (St * S).solve(St * (T * S))  # T restricted to span(S) in S-coordinates
            for lam in range(-bd, bd + 1):
                K = nullspace_q(A - fmpq_mat(r, r, [fmpq(lam if i == j else 0) for i in range(r) for j in range(r)]))
                if K:
                    Kc = S * colmat(K, r)
                    newcols = [[Kc[i, j] for i in range(dim)] for j in range(Kc.ncols())]
                    e = dict(ev)
                    e[lab] = lam
                    new.append((e, newcols))
        spaces = new
    return spaces


def main():
    p, DMAX, SPLITDEG, outfn = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    curvefile = sys.argv[5]
    F = Field(p)
    curves = [json.loads(l) for l in open(curvefile)]
    bylevel = {}
    for c in curves:
        bylevel.setdefault(tuple(c['n']), []).append(c)
    places = [eval(k) for k in curves[0]['ap'].keys()]
    results = []
    levels_sys = {}
    t0 = time.time()
    for dn in range(1, DMAX + 1):
        for n in F.monic(dn):
            nkey = tuple(int(x) for x in n.coeffs())
            L = Level(F, n)
            dim = L.build()
            rec = dict(n=list(nkey), dim=dim, systems=[], curves=len(bylevel.get(nkey, [])))
            if dim == 0:
                results.append(rec)
                if rec['curves']:
                    print('!! curves at level with no cusp forms', nkey)
                continue
            good = [P for P in places if len(P) - 1 <= SPLITDEG and (n % nmod_poly(list(P), p)).degree() >= 0
                    and not (n % nmod_poly(list(P), p)).is_zero()]
            mats = [(P, L.hecke_on_cusp(nmod_poly(list(P), p))) for P in good]
            bounds = [int(2 * p ** ((len(P) - 1) / 2)) for P in good]
            spaces = rational_eigenspaces(mats, dim, bounds)
            B = fmpq_mat(L.nv, dim, [fmpq(L.basis[j][i]) for i in range(L.nv) for j in range(dim)])
            for ev, cols in spaces:
                vec = B * colmat(cols[:1], dim)  # one eigenvector in variable coordinates
                ve = [vec[i, 0] for i in range(L.nv)]
                v0 = next(i for i in range(L.nv) if ve[i] != 0)
                lam = {}
                for P in places:
                    Pp = nmod_poly(list(P), p)
                    if (n % Pp).is_zero():
                        continue
                    row = L.hecke_matrix_vars(Pp, [v0])[0]
                    val = sum(fmpq(row[i]) * ve[i] for i in range(L.nv)) / ve[v0]
                    assert val.q == 1
                    lam[str(P)] = int(val.p)
                # check it is really an eigenvector for deg-1 operators (full matrices)
                rec['systems'].append(dict(mult=len(cols), lam=lam))
            # match curves
            for c in bylevel.get(nkey, []):
                sgn = lambda P: 1 if c['oo_split'] else (-1) ** (len(eval(P)) - 1)
                hits = [i for i, s in enumerate(rec['systems'])
                        if all(s['lam'][P] == sgn(P) * c['ap'][P] for P in s['lam'])]
                c['match'] = hits
            levels_sys[nkey] = rec
            results.append(rec)
            print(nkey, 'dim', dim, 'rational systems', [(s['mult']) for s in rec['systems']],
                  'curves', rec['curves'], 'matched', [c.get('match') for c in bylevel.get(nkey, [])][:6],
                  round(time.time() - t0, 1), flush=True)
    json.dump(dict(levels=results, curves=curves), open(outfn, 'w'))


if __name__ == '__main__':
    main()
