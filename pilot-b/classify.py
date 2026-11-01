"""Tag each genus 2 isogeny-class representative by the modularity theorem that covers it.

Usage: python3 classify.py classes.jsonl out.jsonl
Tags (first that applies):
  A        BCGP 2025 Theorem A applies directly (all hypotheses certified exactly)
  A-twist  Theorem A applies to a quadratic twist C^d, d in {-1,+-2,+-3,+-6}; modularity of
           Jac(C) = Jac(C^d) (x) chi_d follows
  FS       in the published Faltings-Serre / explicit lists (BPPTVY 277,353,587; Berger-Klosin 731)
  NT-split / NT-RM / NT-other   heuristically non-typical: split over Q (Wiles+BCDT), RM over Q
           (Khare-Wintenberger + Ribet), other non-typical (BCGP Thm 10.2.1 unless 'challenging')
  OPEN     looks typical but no theorem we can certify applies
"""
import json
import sys
from multiprocessing import Pool

from g2lib import (pari, conductor_data, ap_list, charpoly, PRIMES, endo_heuristic,
                   theorem_A, quad_twist, curve_str)
from inv_check import ALL2, MAX2
from jac3rank import sylow3_rank

FS_CONDUCTORS = {277: "BPPTVY 2019", 353: "BPPTVY 2019", 587: "BPPTVY 2019", 731: "Berger-Klosin 2020"}
CERT_PRIMES = [p for p in PRIMES if p < 800]


def certify_mod3(mm, bad, cps):
    """Exact certification that rho_bar_{A,3} is onto GSp4(F3). Returns (bool, remaining maxes, witnesses)."""
    remaining = list(MAX2)
    witnesses = {}
    F = pari(f"4*({mm[0]})+({mm[1]})^2")
    for p in CERT_PRIMES:
        if p <= 3 or p in bad:
            continue
        cp = cps.get(p) or charpoly(mm, p)
        cpm = tuple(c % 3 for c in cp)
        # cheap pre-filter: does this charpoly alone already exclude something new?
        need = [M for M in remaining if not any(inv[0] == cpm and inv[1] == p % 3 for inv in M[2])]
        if need:
            remaining = [M for M in remaining if M not in need]
            witnesses[p] = cpm
            if not remaining:
                break
            continue
        r1 = sylow3_rank(F, p, sum(cp))
        nr = next(a for a in range(2, p) if pari.kronecker(a, p) == -1)
        r2 = sylow3_rank(F * nr, p, sum(c * (-1) ** i for i, c in enumerate(cp)))
        if r1 is None or r2 is None:
            continue
        inv = (cpm, p % 3, r1, r2)
        assert inv in ALL2, (p, inv)
        newrem = [M for M in remaining if inv in M[2]]
        if len(newrem) < len(remaining):
            witnesses[p] = inv
            remaining = newrem
            if not remaining:
                break
    return (not remaining), [(s, d) for s, d, _ in remaining], witnesses


def analyse(mm, bad):
    cps = ap_list(mm, bad, [p for p in PRIMES if p < 400])
    surj = certify_mod3(mm, bad, cps)
    okA, fails = theorem_A(bad, mm, cps, surj)
    return cps, surj, okA, fails


def classify(rec):
    fh = (rec["f"], rec["h"])
    N, mm, bad = conductor_data(fh)
    cps, surj, okA, fails = analyse(mm, bad)
    out = {"N": N, "bad": bad, "curve": curve_str(mm), "f": str(mm[0]), "h": str(mm[1]),
           "mod3_surjective": surj[0], "mod3_not_excluded": [d for s, d in surj[1]],
           "mod3_witnesses": {str(k): v for k, v in surj[2].items()},
           "endo": endo_heuristic(cps), "thmA_fails": fails}
    if okA:
        out["tag"] = "A"
        return out
    if N in FS_CONDUCTORS:
        out["tag"] = "FS"
        out["ref"] = FS_CONDUCTORS[N]
        return out
    e = out["endo"]
    if e.startswith("split"):
        out["tag"] = "NT-split"
        return out
    if e.startswith("RM"):
        out["tag"] = "NT-RM"
        return out
    if e.startswith("geometrically"):
        out["tag"] = "NT-other"
        return out
    # typical-looking: try quadratic twists when only local conditions at 2/3 fail
    if any(x in ("bad-at-2", "bad-at-3") for x in fails) and surj[0]:
        for d in (-1, 2, -2, 3, -3, 6, -6):
            tw = quad_twist(mm, d)
            try:
                Nt, mmt, badt = conductor_data((str(tw[0]), str(tw[1])))
            except Exception:
                continue
            if 2 in badt or 3 in badt:
                continue
            _, surjt, okt, failst = analyse(mmt, badt)
            if okt:
                out["tag"] = "A-twist"
                out["twist"] = {"d": d, "N": Nt, "curve": curve_str(mmt), "f": str(mmt[0]),
                                "h": str(mmt[1]),
                                "mod3_witnesses": {str(k): v for k, v in surjt[2].items()}}
                return out
    out["tag"] = "OPEN"
    return out


class _Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise _Timeout()


def safe(rec, limit=180):
    import signal
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(limit)
    try:
        return classify(rec)
    except _Timeout:
        return {"N": rec["N"], "f": rec["f"], "h": rec["h"], "tag": "TIMEOUT"}
    except Exception as ex:  # keep going; record the failure honestly
        return {"N": rec["N"], "f": rec["f"], "h": rec["h"], "tag": "ERROR", "error": repr(ex)}
    finally:
        signal.alarm(0)


if __name__ == "__main__":
    recs = [json.loads(l) for l in open(sys.argv[1]) if l.strip()]
    with Pool(4) as pool, open(sys.argv[2], "w") as out:
        for r in pool.imap_unordered(safe, recs, chunksize=4):
            out.write(json.dumps(r) + "\n")
            out.flush()
