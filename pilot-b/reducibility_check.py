"""Necessary conditions on Frobenius char polys mod 3 (primes < 1000) for the image to lie in a parabolic.
Klingen (fixes a line): every char poly has a root in F3.  Siegel (fixes a Lagrangian plane): every char
poly factors over F3 into two quadratics (or finer). A class failing both can't lie in either parabolic."""
import json, sys, collections
from g2lib import pari, conductor_data, ap_list
P = [int(p) for p in pari.primes([5, 1000])]
def root(c): return any(sum(ci * pow(x, i, 3) for i, ci in enumerate(c)) % 3 == 0 for x in (1, 2))
def has_quad_split(c):
    f = pari(f"Mod(1,3)*Pol({list(reversed(c))})")
    degs = [int(pari.poldegree(f_)) for f_ in pari.factor(f)[0]] if True else []
    fa = pari.factor(f); ds = []
    for i in range(int(pari.matsize(fa)[0])): ds += [int(pari.poldegree(fa[i, 0]))] * int(fa[i, 1])
    return max(ds) <= 2
def one(l):
    r = json.loads(l)
    N, mm, bad = conductor_data((r["f"], r["h"]))
    cps = ap_list(mm, bad, P)
    cl = all(root([c % 3 for c in cp]) for cp in cps.values())
    sg = all(has_quad_split([c % 3 for c in cp]) for cp in cps.values())
    k = ("line-compatible" if cl else "") + ("+" if cl and sg else "") + ("plane-compatible" if sg else "")
    k = k or "neither parabolic"
    return {"N": N, "curve": r["curve"], "parabolic_test": k}

if __name__ == "__main__":
    from multiprocessing import Pool
    with Pool(4) as pool:
        out = pool.map(one, open(sys.argv[1]).readlines())
    json.dump(out, open(sys.argv[2], "w"), indent=0)
    print(dict(collections.Counter(o["parabolic_test"] for o in out)))
