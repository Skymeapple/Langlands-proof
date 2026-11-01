"""Check the triple product (Ichino / GGP SO(3) in SO(4)) identity found in triple.py output, for squarefree
levels n = P M (deg n = 3) on the definite algebra ramified at {P, oo}:
  * local signs eps_v = a_v(E1) a_v(E2) a_v(E3) at v | n.  "Allowed" (Prasad's dichotomy for this B):
    eps_P = +1 and eps_l = -1 for every l | M.
  * allowed:      L(f1 x f2 x f3, q^-2) * prod <f_i,f_i>_D = I^2 * prod ||f_i||^2 / (2^omega(M) q^4)
  * not allowed:  I = 0.
Non-squarefree levels (M = l^2) are reported separately.  Usage: python3 check_triple.py triple_q*.json q"""
import sys, json
from fractions import Fraction as Fr
R = json.load(open(sys.argv[1]))
q = int(sys.argv[2])
st = dict(cases=0, allowed=0, allowed_identity_holds=0, allowed_L_zero_and_I_zero=0, allowed_fail=0,
          forbidden=0, forbidden_I_zero=0, forbidden_I_nonzero=0, forbidden_L_nonzero=0, nonsquarefree_cases=0)
for r in R:
    if any(b[1] > 1 for b in r['bad']):
        st['nonsquarefree_cases'] += 1
        continue
    st['cases'] += 1
    I, L = Fr(r['period']), Fr(r['L'])
    allowed = all((b[2] == 1) if b[3] else (b[2] == -1) for b in r['bad'])
    omega = sum(1 for b in r['bad'] if not b[3])
    if allowed:
        st['allowed'] += 1
        ff = Fr(1)
        pet = Fr(1)
        for a, b in zip(r['ff'], r['pet']):
            ff *= Fr(a)
            pet *= Fr(b)
        if L * ff * 2 ** omega * q ** 4 == I * I * pet:
            st['allowed_identity_holds'] += 1
            if L == 0:
                st['allowed_L_zero_and_I_zero'] += 1
        else:
            st['allowed_fail'] += 1
            print('FAIL', r)
    else:
        st['forbidden'] += 1
        st['forbidden_I_zero' if I == 0 else 'forbidden_I_nonzero'] += 1
        st['forbidden_L_nonzero'] += (L != 0)
print(st)
