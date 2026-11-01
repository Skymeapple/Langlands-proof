"""Galois-side data for a Faltings-Serre proof of paramodularity of the conductor 349 surface.

Prints: the model, mod 2 image (Galois group of the Weierstrass sextic), the mod 3 status,
why BCGP Theorem A fails, and the Euler factors L_p(A, T) for p < 200, which the spin
L-factors of the weight 2 paramodular newform of level K(349) must match.
"""
import json
from g2lib import pari, conductor_data, ap_list, charpoly, BAD_FROB2

f, h = "-x^5 - x^3 - x^2 - x", "x^3 + x^2 + x + 1"
N, mm, bad = conductor_data((f, h))
F = pari(f"4*({f})+({h})^2")
fa = pari.factor(F)
quint = fa[1, 0]
out = {"N": N, "curve": f"y^2 + ({h})y = {f}", "sextic": str(F),
       "sextic_factorization": [str(fa[i, 0]) for i in range(int(pari.matsize(fa)[0]))],
       "mod2_image": str(pari.polgalois(quint)),
       "quintic_field_disc": str(pari.factor(pari.nfdisc(quint))),
       "frob2_charpoly": charpoly(mm, 2),
       "frob2_mod3": [c % 3 for c in charpoly(mm, 2)],
       "frob2_excluded_by_thmA": tuple(c % 3 for c in charpoly(mm, 2)) in BAD_FROB2}
cps = ap_list(mm, bad, [int(p) for p in pari.primes(46)])
out["euler_factors"] = {p: {"charpoly_low_to_high": cp, "a_p": -cp[3], "b_p": cp[2]} for p, cp in cps.items()}
json.dump(out, open("target349.json", "w"), indent=1)
print({k: v for k, v in out.items() if k != "euler_factors"})
print("a_p for p<=43:", {p: -cp[3] for p, cp in cps.items() if p <= 43})
