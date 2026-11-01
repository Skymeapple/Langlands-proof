"""From Theorem-A curves C, produce quadratic twists D = C^d (d = -1, +-2, +-3, +-6), which Theorem A
cannot be applied to directly but whose modularity follows. Writes certificates for verify_certificate.py."""
import json, sys
from g2lib import pari, conductor_data, quad_twist, curve_str
COND = {-1: 4, 2: 8, -2: 8, 3: 3, -3: 3, 6: 24, -6: 24}   # conductor of chi_d (d -> Q(sqrt d))
COND[3] = 12; COND[6] = 24; COND[-6] = 24  # Q(sqrt 3): disc 12 ; Q(sqrt +-6): disc 24 ; Q(sqrt -3): disc 3
src = [json.loads(l) for f in sys.argv[1:-1] for l in open(f)]
A = [r for r in src if r["tag"] == "A"]
out = []
for r in A:
    for d in (-3, 3, -1, 2, -2, 6, -6):
        tw = quad_twist(pari(f"[{r['f']},{r['h']}]"), d)
        ND, mmD, badD = conductor_data((str(tw[0]), str(tw[1])))
        NDtrue = r["N"] * COND[d] ** 4    # good reduction of C at 2,3: exponent multiplies (dim 4)
        if ND > 0:
            assert ND == NDtrue, (r, d, ND, NDtrue)
        wp = sorted(int(p) for p in r["mod3_witnesses"])
        # witness primes for C may include primes where only charpolys were used; verifier recomputes
        out.append({"D": {"f": str(mmD[0]), "h": str(mmD[1])}, "d": d, "N_D": NDtrue, "N_C": r["N"],
                    "C": r["curve"], "witness_primes": wp})
out.sort(key=lambda c: c["N_D"])
json.dump(out, open(sys.argv[-1], "w"), indent=1)
small = [c for c in out if c["N_D"] <= 10**6]
print(len(out), "twists;", len(small), "with conductor <= 10^6")
for c in out[:12]: print(c["N_D"], c["d"], c["N_C"])
