"""Round 3: re-run exact mod 3 certification, with primes up to 3000, on open classes whose image was not certified."""
import json, sys, collections
import classify
from g2lib import pari, conductor_data, ap_list, theorem_A, PRIMES
classify.CERT_PRIMES = [int(p) for p in pari.primes([5, int(__import__('os').environ.get('PMAX','3000'))])]
from multiprocessing import Pool

def run(r):
    N, mm, bad = conductor_data((r["f"], r["h"]))
    cps = ap_list(mm, bad, [p for p in PRIMES if p < 400])
    surj = classify.certify_mod3(mm, bad, cps)
    okA, fails = theorem_A(bad, mm, cps, surj)
    return {"N": N, "curve": r["curve"], "f": r["f"], "h": r["h"], "mod3_surjective": surj[0],
            "mod3_not_excluded": [d for s, d in surj[1]], "thmA_ok": okA, "thmA_fails": fails,
            "endo": r.get("endo")}

if __name__ == "__main__":
    recs = [json.loads(l) for l in open(sys.argv[1])]
    res = []
    with Pool(4) as pool, open(sys.argv[2], "w") as o:
        for r in pool.imap_unordered(run, recs):
            res.append(r); o.write(json.dumps(r) + "\n"); o.flush()
    print("classes:", len(res))
    print("now certified surjective:", sum(r["mod3_surjective"] for r in res))
    print("now Theorem A:", sum(r["thmA_ok"] for r in res))
    print("remaining maximal classes:", collections.Counter(tuple(r["mod3_not_excluded"]) for r in res if not r["mod3_surjective"]).most_common())
