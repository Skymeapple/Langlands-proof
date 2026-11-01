"""Check the Gross/Waldspurger toric period identity found in gross.py output:

    L(E^{D0}, 1/q) * <f_D, f_D> * |d_K|^{1/2}  =  C * P_{D0}(f_D)^2 * ||f||^2

with |d_K| = q^{deg D0 + 1} if oo is ramified in K (deg D0 odd), q^{deg D0} if oo is inert,
<f_D,f_D> = sum_i f_D(i)^2 / #Stab_i on the quaternion side, ||f||^2 the Petersson norm of the
primitive harmonic cochain (sum over edges of Gamma_0(n)\\T of f(e)^2 / #Stab(e)), and C a constant
depending only on q and on whether oo is ramified or inert in K.
Also checks that P_{D0} = 0 exactly when L(E^{D0}, 1/q) = 0.
Squares are compared exactly: (L <f_D,f_D> / (P^2 ||f||^2))^2 * |d_K| = C^2.
Usage: python3 check_gross.py gross_q*.json q"""
import sys, json
from fractions import Fraction as Fr
R = json.load(open(sys.argv[1]))
q = int(sys.argv[2])
consts = {}
zero_ok = zero_bad = 0
for r in R:
    L, P = Fr(r['L']), r['period']
    d = len(r['D0']) - 1
    typ = 'ramified' if d % 2 else 'inert'
    if P == 0 or L == 0:
        if P == 0 and L == 0:
            zero_ok += 1
        else:
            zero_bad += 1
            print('VANISHING MISMATCH', r)
        continue
    dK = q ** (d + 1) if d % 2 else q ** d
    Ppic = Fr(P, q + 1)  # each CM point of Pic(O_K) occurs q+1 times among the y
    X = L * Fr(r['ff']) / (Ppic * Ppic * Fr(r['petersson']))
    consts.setdefault(typ, set()).add(X * X * dK)
print(dict(cases=len(R), vanishing_agree=zero_ok, vanishing_disagree=zero_bad,
           C_squared={k: sorted(str(v) for v in s) for k, s in consts.items()},
           nonzero_cases=len(R) - zero_ok - zero_bad))
