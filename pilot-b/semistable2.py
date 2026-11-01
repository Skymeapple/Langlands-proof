"""Theorem A hypothesis (2) for curves with bad reduction at 2.

If Jac(C) is semistable at 2 with toric rank t (conductor exponent 1 or 2, Namikawa-Ueno type
I_{n-m-r}) then, by Grothendieck's description of inertia, rho_bar_3 is unramified at 2 iff the
monodromy pairing is 0 mod 3, iff the component group Phi_2 = coker(pairing) has 3-rank t.
In that case the char poly of rho_bar_3(Frob_2) is (x^2 - a x + 2)(x^2 + 2) (t = 1) or
(x^2 + 2)^2 (t = 2) mod 3, never (x^2 +- x + 2)^2, so hypothesis (2) holds.
Usage: python3 semistable2.py tagged.jsonl... > upgraded.jsonl
"""
import json, re, sys
from g2lib import pari, model


def unramified_mod3_at_2(f, h):
    R = pari.genus2red(model((f, h)))
    fa = R[1]
    e = [int(fa[i, 1]) for i in range(int(pari.matsize(fa)[0])) if int(fa[i, 0]) == 2]
    if not e or e[0] not in (1, 2):
        return False, None
    loc = [x for x in R[3] if int(x[0]) == 2][0]
    typ, phi = str(loc[2][0]), [int(c) for c in loc[2][1]]
    if not re.match(r"\[I\{\d+-\d+-\d+\}\]", typ):
        return False, None
    t = e[0]
    r3 = sum(1 for c in phi if c % 3 == 0)
    return r3 >= t, {"type": typ, "Phi": phi, "toric_rank": t}


if __name__ == "__main__":
    n = 0
    for fn in sys.argv[1:]:
        for l in open(fn):
            r = json.loads(l)
            if r["tag"] != "OPEN" or r["N"] <= 0 or "bad-at-2" not in r["thmA_fails"]:
                continue
            ok, info = unramified_mod3_at_2(r["f"], r["h"])
            if ok:
                rest = [x for x in r["thmA_fails"] if x != "bad-at-2"]
                r["at2"] = info
                if not rest:
                    r["tag"] = "A"
                    r["note"] = "Theorem A with bad semistable reduction at 2 (rho_bar_3 unramified at 2)"
                    n += 1
                else:
                    r["thmA_fails"] = rest
                print(json.dumps(r))
    print(f"# upgraded to A: {n}", file=sys.stderr)
