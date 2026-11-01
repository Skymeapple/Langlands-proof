"""Enumerate elliptic curves E/F_p(t) (p = 3, 5) with chi = 1 (minimal model deg a_i <= i),
multiplicative reduction at oo, and finite conductor n of degree <= DMAX.

Usage: python3 enumerate_curves.py p DMAX BMAX out.jsonl
  BMAX: compute a_P for all finite places of degree <= BMAX.

Normal forms (one model per F_p(t)-isomorphism class):
  p = 3: y^2 = x^3 + a2 x^2 + a4 x + a6, deg a2 = 2 (forced by multiplicative reduction at oo,
         since c4 = a2^2), a4 reduced mod a2 (deg a4 <= 1) via x -> x + r, deg a6 <= 6.
         Remaining isomorphisms (u = -1) act trivially, so models = classes.
  p = 5: y^2 = x^3 + a4 x + a6 (a2 killed by x -> x - a2/3), deg a4 = 4 (c4 ~ a4 must be a unit
         at oo), deg a6 <= 6; (a4, a6) ~ (a4, -a6) (u = 2), we keep the lexicographically
         smaller of a6, -a6.
A prefilter keeps only models whose discriminant has degree <= 11 (so oo is bad) and whose finite
radical has degree <= DMAX (necessary, since every finite bad place contributes >= deg P).
Then Tate's algorithm decides the reduction types and the conductor exactly.
"""
import sys, json, itertools, time
import numpy as np
from flint import nmod_poly
from harmonic import Field
from curves import disc_data, local_data, residue_field


def rad_deg(D):
    return sum(P.degree() for P, e in D.factor()[1])


def coeffs(f, n=None):
    c = [int(x) for x in f.coeffs()]
    return c


def allowed_disc_codes(F, DMAX, maxdeg=11):
    """Integer codes (base p, coefficients of t^0..t^maxdeg) of all c * prod P_i^e_i with
    sum deg P_i <= DMAX and total degree <= maxdeg."""
    p = F.p
    irr = []
    for d in range(1, DMAX + 1):
        irr += list(F.irreducibles(d))
    codes = set()
    rads = [[]]
    # all sets of distinct irreducibles with total degree <= DMAX
    def rec(start, cur, dsum):
        for i in range(start, len(irr)):
            d = irr[i].degree()
            if dsum + d <= DMAX:
                rads.append(cur + [irr[i]])
                rec(i + 1, cur + [irr[i]], dsum + d)
    rec(0, [], 0)
    for R in rads:
        degs = [P.degree() for P in R]
        def recE(i, f, dsum):
            if i == len(R):
                for c in range(1, p):
                    g = f * c
                    cs = [int(g[j]) for j in range(maxdeg + 1)]
                    codes.add(sum(cs[j] * p ** j for j in range(maxdeg + 1)))
                return
            e = 1
            while dsum + e * degs[i] <= maxdeg:
                recE(i + 1, f * R[i] ** e, dsum + e * degs[i])
                e += 1
        recE(0, F.one, 0)
    return codes


def candidates_p3(F, DMAX):
    out = []
    for a2 in F.polys(2):
        if a2.degree() != 2:
            continue
        for a4 in F.polys(1):
            for a6 in F.polys(6):
                D = disc_data(a2, a4, a6)[4]
                if D.is_zero() or D.degree() > 11:
                    continue
                if rad_deg(D) > DMAX:
                    continue
                out.append((a2, a4, a6))
    return out


def candidates_p5(F, DMAX):
    p = 5
    codes = np.array(sorted(allowed_disc_codes(F, DMAX)), dtype=np.int64)
    print('allowed discriminant codes', len(codes), file=sys.stderr)
    # all a6 (deg <= 6) and their squares
    A6 = np.array(list(itertools.product(range(p), repeat=7)), dtype=np.int64)  # big-endian? index j = coeff t^j
    # product(range(p), repeat=7) gives tuples (c0..c6) in order; treat tuple[j] as coeff of t^j
    sq = np.zeros((len(A6), 13), dtype=np.int64)
    for i in range(7):
        for j in range(7):
            sq[:, i + j] += A6[:, i] * A6[:, j]
    sq %= p
    pw = np.array([p ** j for j in range(12)], dtype=np.int64)
    out = []
    for a4t in itertools.product(range(p), repeat=5):
        if a4t[4] == 0:
            continue
        a4 = nmod_poly(list(a4t), p)
        c3 = a4 * a4 * a4
        c3v = np.array([int(c3[j]) for j in range(13)], dtype=np.int64)
        G = (4 * c3v[None, :] + 27 * sq) % p   # 4 a4^3 + 27 a6^2
        mask = G[:, 12] == 0
        idx = np.nonzero(mask)[0]
        code = G[idx, :12] @ pw
        hit = idx[np.isin(code, codes)]
        for i in hit:
            a6t = [int(x) for x in A6[i]]
            neg = [(-x) % p for x in a6t]
            # keep lexicographically smaller of a6, -a6 (compare from top coefficient)
            if neg[::-1] < a6t[::-1]:
                continue
            out.append((F.zero, a4, nmod_poly(a6t, p)))
    return out


def main():
    p, DMAX, BMAX, outfn = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    F = Field(p)
    t0 = time.time()
    cands = candidates_p3(F, DMAX) if p == 3 else candidates_p5(F, DMAX)
    print('candidates after prefilter', len(cands), round(time.time() - t0, 1), file=sys.stderr)
    places = []
    for d in range(1, BMAX + 1):
        places += list(F.irreducibles(d))
    kept = 0
    with open(outfn, 'w') as fo:
        for a2, a4, a6 in cands:
            D = disc_data(a2, a4, a6)[4]
            ld = local_data(a2, a4, a6, D)
            inf = [d for P, d in ld if P == 'oo'][0]
            if inf['f'] != 1:
                continue
            fin = [(P, d) for P, d in ld if P != 'oo' and d['f'] > 0]
            degn = sum(P.degree() * d['f'] for P, d in fin)
            if degn > DMAX:
                continue
            if not all(d['minimal'] for P, d in ld):
                continue
            n = F.one
            for P, d in fin:
                n = n * P ** d['f']
            bad = {tuple(coeffs(P)): d for P, d in fin}
            ap = {}
            for P in places:
                key = tuple(coeffs(P))
                if key in bad:
                    d = bad[key]
                    ap[str(key)] = (1 if d['split'] else -1) if d['f'] == 1 else 0
                else:
                    K = residue_field(P)
                    ap[str(key)] = p ** P.degree() + 1 - K.count_points(a2, a4, a6)
            rec = dict(p=p, a2=coeffs(a2), a4=coeffs(a4), a6=coeffs(a6),
                       n=coeffs(n), degn=degn,
                       local=[(coeffs(P), d['kod'], d['f']) for P, d in fin],
                       oo=inf['kod'], oo_split=inf['split'], ap=ap)
            fo.write(json.dumps(rec) + '\n')
            kept += 1
    print('kept', kept, round(time.time() - t0, 1), file=sys.stderr)


if __name__ == '__main__':
    main()
