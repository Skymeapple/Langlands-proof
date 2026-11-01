"""Standalone checker: modularity of a genus 2 curve D via BCGP Theorem A on a quadratic twist.

Usage: python3 verify_certificate.py certificates.json

Each certificate: {"D": {"f":..., "h":...}, "d": int, "witness_primes": [...]}.
For each one this script recomputes everything from scratch:
  1. C := quadratic twist of D by d.  Jac(D) = Jac(C) (x) chi_d, so D is modular iff C is.
  2. D itself is outside Theorem A: it has bad reduction at 2 or 3 coming from the ramified
     character chi_d, so hypothesis (2) or (3) of Theorem A fails for D.
  3. C satisfies Theorem A:
     (0) Jac(C) is principally polarized (degree 1, prime to 3);
     (1) rho_bar_{C,3} is onto GSp4(F3): at the witness primes the exact invariants
         (char poly mod 3, multiplier, dim ker(g-1), dim ker(g+1)) rule out each of the six
         classes of maximal subgroups (table maxsub2.txt, computed by maxsub2.g in GAP);
     (2) C has good reduction at 2 (so rho_bar is unramified at 2) and the char poly of
         Frob_2 mod 3 is not (x^2 +- x + 2)^2;
     (3) C has good ordinary reduction at 3 and the Frob_3 polynomial is squarefree.
"""
import json
import sys

from g2lib import pari, conductor_data, charpoly, quad_twist, curve_str, BAD_FROB2
from inv_check import ALL2, MAX2
from jac3rank import sylow3_rank


def invariant(mm, p):
    cp = charpoly(mm, p)
    F = pari(f"4*({mm[0]})+({mm[1]})^2")
    nr = next(a for a in range(2, p) if pari.kronecker(a, p) == -1)
    r1 = sylow3_rank(F, p, sum(cp))
    r2 = sylow3_rank(F * nr, p, sum(c * (-1) ** i for i, c in enumerate(cp)))
    return (tuple(c % 3 for c in cp), p % 3, r1, r2)


def check(cert):
    log = []
    ND, mmD, badD = conductor_data((cert["D"]["f"], cert["D"]["h"]))
    d = cert["d"]
    tw = quad_twist(mmD, d)
    NC, mmC, badC = conductor_data((str(tw[0]), str(tw[1])))
    log.append(f"D: {curve_str(mmD)}   conductor {ND if ND > 0 else 'odd part ' + str(-ND)}  bad {badD}")
    log.append(f"C = D twisted by {d}: {curve_str(mmC)}   conductor {NC}  bad {badC}")
    assert 2 in badD or 3 in badD, "D has good reduction at 2 and 3; twist not needed"
    assert 2 not in badC and 3 not in badC, "C is bad at 2 or 3"
    # (1) mod 3 surjectivity
    remaining = list(MAX2)
    for p in cert["witness_primes"]:
        assert p not in badC and p > 3
        inv = invariant(mmC, p)
        before = len(remaining)
        if None in inv:   # 3-rank not computed: use char poly + multiplier only (weaker, still exact)
            remaining = [M for M in remaining if any(i[0] == inv[0] and i[1] == inv[1] for i in M[2])]
        else:
            assert inv in ALL2
            remaining = [M for M in remaining if inv in M[2]]
        log.append(f"  p={p}: invariant {inv}  rules out {before - len(remaining)} more maximal class(es)")
    assert not remaining, f"maximal subgroups not excluded: {[m[1] for m in remaining]}"
    log.append("  (1) mod 3 image is all of GSp4(F3)")
    # (2) at 2
    c2 = charpoly(mmC, 2)
    assert tuple(c % 3 for c in c2) not in BAD_FROB2
    log.append(f"  (2) good at 2, Frob_2 char poly {c2} (mod 3 {[c % 3 for c in c2]}) allowed")
    # (3) at 3
    c3 = charpoly(mmC, 3)
    assert c3[2] % 3 != 0, "not ordinary at 3"
    assert pari.issquarefree(pari(f"Pol({list(reversed(c3))})"))
    log.append(f"  (3) good ordinary at 3, Frob_3 char poly {c3} squarefree")
    log.append(f"=> Jac(C) is modular (BCGP Thm A), hence Jac(D) = Jac(C) (x) chi_{d} is modular.")
    return log


if __name__ == "__main__":
    certs = json.load(open(sys.argv[1]))
    ok = 0
    for cert in certs:
        try:
            print("\n".join(check(cert)))
            ok += 1
        except AssertionError as e:
            print("FAILED:", cert, e)
        print()
    print(f"{ok}/{len(certs)} certificates verified")
