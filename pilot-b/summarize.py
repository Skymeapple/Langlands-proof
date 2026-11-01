"""Merge tagged files, dedupe by isogeny-class fingerprint, write inventory.csv and summary.json."""
import csv, json, sys, collections
from g2lib import pari, conductor_data, ap_list
THM = {"A": "BCGP 2025 Theorem A (arXiv:2502.20645)",
       "FS": "Faltings-Serre (BPPTVY 2019 / Berger-Klosin 2020)",
       "NT-split": "isogenous over Q to E1 x E2 (heuristic): Wiles, BCDT",
       "NT-RM": "GL2-type over Q (heuristic): Khare-Wintenberger + Ribet",
       "NT-other": "non-typical (heuristic): BCGP Thm 10.2.1 unless 'challenging'",
       "OPEN": "none found", "A-twist": "BCGP Theorem A applied to a quadratic twist", "ERROR": "computation failed", "TIMEOUT": "computation timed out"}
FP = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59]
RANK = {"A": 0, "A-twist": 0, "FS": 1, "NT-split": 2, "NT-RM": 2, "NT-other": 2, "OPEN": 5, "ERROR": 6, "TIMEOUT": 6}
best = {}
for f in sys.argv[1:]:
    for l in open(f):
        r = json.loads(l)
        if r["N"] <= 0: continue
        _, mm, bad = conductor_data((r["f"], r["h"]))
        cps = ap_list(mm, bad, [p for p in FP])
        k = (r["N"], tuple(tuple(cps[p]) for p in sorted(cps)))
        if k not in best or RANK[r["tag"]] < RANK[best[k]["tag"]]:
            best[k] = r
known = list(best.values())
with open("inventory.csv", "w", newline="") as o:
    w = csv.writer(o)
    w.writerow(["conductor", "curve", "tag", "covering_theorem", "mod3_surjective_certified",
                "endomorphism_heuristic", "theorem_A_failures"])
    for r in sorted(known, key=lambda r: r["N"]):
        w.writerow([r["N"], r.get("curve", ""), r["tag"], THM[r["tag"]], r.get("mod3_surjective", ""),
                    r.get("endo", ""), ";".join(x.split(":")[0] for x in r.get("thmA_fails", []))])
tags = collections.Counter(r["tag"] for r in known)
op = [r for r in known if r["tag"] == "OPEN"]
fails = collections.Counter(x.split(":")[0] for r in op for x in r["thmA_fails"])
only = collections.Counter(r["thmA_fails"][0].split(":")[0] for r in op if len(r["thmA_fails"]) == 1)
s = {"isogeny_classes_known_conductor": len(known), "tags": dict(tags),
     "open_failure_counts": dict(fails), "open_single_failure": dict(only),
     "open_mod3_not_certified": sum(1 for r in op if not r["mod3_surjective"]),
     "smallest_open": [(r["N"], r["curve"], r["thmA_fails"]) for r in sorted(op, key=lambda r: r["N"])[:25]]}
json.dump(s, open("summary.json", "w"), indent=1)
print(json.dumps({k: v for k, v in s.items() if k != "smallest_open"}, indent=1))
print([x[0] for x in s["smallest_open"]])
