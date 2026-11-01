"""Enumerate y^2 + h y = f with h in {0,1}-coeffs deg<=3, f coeffs in [-B,B] deg 5/6; keep N <= NMAX.
Dedupe by isogeny-class fingerprint (N, Frobenius polys for p<60). Output JSON lines."""
import itertools, json, sys
from g2lib import *
B = int(sys.argv[1]) if len(sys.argv)>1 else 1
NMAX = int(sys.argv[2]) if len(sys.argv)>2 else 10**6
fp_primes = [p for p in PRIMES if p < 60]
seen = {}
xs = ["", "*x", "*x^2", "*x^3", "*x^4", "*x^5", "*x^6"]
def poly(cs): 
    s = "+".join(f"({c}){xs[i]}" for i,c in enumerate(cs) if c)
    return s or "0"
cnt=0
for hc in itertools.product([0,1], repeat=4):
    h = poly(hc)
    for fc in itertools.product(range(-B,B+1), repeat=7):
        if fc[6]==0 and fc[5]==0: continue
        f = poly(fc)
        disc = pari(f"poldisc(4*({f})+({h})^2)")
        if disc == 0: continue
        if hc[3]==0 and fc[6]==0 and fc[5]==0: continue
        cnt+=1
        try:
            N, mm, bad = conductor_data((f,h))
        except Exception as e:
            continue
        if abs(N) > NMAX: continue
        cps = ap_list(mm, bad, fp_primes)
        key = (N, tuple(tuple(cps[p]) for p in sorted(cps)))
        if key in seen: continue
        seen[key] = 1
        print(json.dumps({"N":N, "bad":bad, "f":str(mm[0]), "h":str(mm[1])}), flush=True)
print(f"# scanned {cnt} models, {len(seen)} classes", file=sys.stderr)
