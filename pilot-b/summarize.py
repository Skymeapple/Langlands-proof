"""Merge tagged files, dedupe, write inventory.csv and summary.json."""
import csv, json, sys, collections
THM = {"A": "BCGP 2025 Theorem A (arXiv:2502.20645)",
       "FS": "Faltings-Serre (BPPTVY 2019 / Berger-Klosin 2020)",
       "NT-split": "isogenous over Q to E1 x E2 (heuristic): Wiles, BCDT",
       "NT-RM": "GL2-type over Q (heuristic): Khare-Wintenberger + Ribet",
       "NT-other": "non-typical (heuristic): BCGP Thm 10.2.1 unless 'challenging'",
       "OPEN": "none found", "ERROR": "computation failed", "TIMEOUT": "computation timed out"}
recs, seen = [], set()
for f in sys.argv[1:]:
    for l in open(f):
        r = json.loads(l)
        k = (r["N"], r.get("curve", r["f"]))
        if k in seen: continue
        seen.add(k); recs.append(r)
known = [r for r in recs if r["N"] > 0]
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
s = {"classes_total": len(recs), "classes_known_conductor": len(known),
     "classes_2part_unknown_bad_at_2": len(recs) - len(known),
     "tags_known_conductor": dict(tags), "open_failure_counts": dict(fails),
     "open_single_failure": dict(only),
     "open_reducible_or_small_mod3": sum(1 for r in op if not r["mod3_surjective"]),
     "smallest_open": [(r["N"], r["curve"], r["thmA_fails"]) for r in sorted(op, key=lambda r: r["N"])[:15]]}
json.dump(s, open("summary.json", "w"), indent=1)
print(json.dumps(s, indent=1))
