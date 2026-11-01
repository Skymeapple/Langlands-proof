"""Check  Lambda_D(f; z) = kappa_f * z * L(E^D, z/q)  coefficientwise (exact rationals), with kappa_f
independent of D.  Usage: python3 check_period.py period.json"""
import sys, json
from fractions import Fraction
R = json.load(open(sys.argv[1]))
byf = {}
ok = bad = 0
for r in R:
    q = 3 if len(r['curve'][0]) and False else None
for r in R:
    p = r['p'] if 'p' in r else None
p = int(sys.argv[2])
nonzero_central = zero_central = 0
for r in R:
    per = {int(k): v for k, v in r['period'].items()}
    Ls = r['L'][:r['degL'] + 1]
    pred = {i + 1: Fraction(Ls[i], p ** i) for i in range(len(Ls)) if Ls[i]}
    keys = set(per) | set(pred)
    kap = None
    good = set(per) == set(pred)
    if good:
        for k in keys:
            ratio = Fraction(per[k]) / pred[k]
            kap = ratio if kap is None else kap
            good &= (ratio == kap)
    fkey = (tuple(r['n']), r['sys'])
    if good:
        byf.setdefault(fkey, set()).add(kap)
        ok += 1
    else:
        bad += 1
        print('MISMATCH', r)
    central = sum(Fraction(Ls[i], p ** i) for i in range(len(Ls)))
    if central == 0:
        zero_central += 1
        assert sum(per.values()) == 0
    else:
        nonzero_central += 1
const = sum(1 for v in byf.values() if len(v) == 1)
print(dict(checks=len(R), polynomial_identity_holds=ok, fails=bad, newforms=len(byf),
           kappa_constant_in_D=const, central_value_zero=zero_central, central_value_nonzero=nonzero_central,
           kappas=sorted(set(str(next(iter(v))) for v in byf.values() if len(v) == 1))))
