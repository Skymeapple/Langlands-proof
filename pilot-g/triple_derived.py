"""Test the triple product constant derived from Ichino's formula (DERIVATION.md section 2) on Pilot E's
squarefree-level cases, with L(1, pi_i, Ad) computed from Frobenius traces (no Petersson norms used).
Derived: allowed signs  ->  I^2 / prod <f_i,f_i>_D = 2^omega(M) * L(1/2, f1 x f2 x f3) / (q^2 * prod L(1, pi_i, Ad));
         other signs    ->  I = 0 (a local trilinear form vanishes at P or at some l | M).
Usage: python3 triple_derived.py q triple_q*.json match_q*.json"""
import sys, json, ast
from fractions import Fraction as Fr
from adjoint import L_adjoint
q = int(sys.argv[1]); R = json.load(open(sys.argv[2])); Mj = json.load(open(sys.argv[3]))
B = max(len(ast.literal_eval(k)) - 1 for k in Mj['curves'][0]['ap'])
cur = {(tuple(c['n']), c['match'][0]): c for c in Mj['curves'] if c['oo_split'] and c.get('match')}
st = dict(allowed_match=0, allowed_mismatch=0, forbidden_I_zero=0, forbidden_I_nonzero=0, skipped_nonsquarefree=0)
for r in R:
    if any(b[1] > 1 for b in r['bad']):
        st['skipped_nonsquarefree'] += 1
        continue
    I, L = Fr(r['period']), Fr(r['L'])
    allowed = all((b[2] == 1) if b[3] else (b[2] == -1) for b in r['bad'])
    if not allowed:
        st['forbidden_I_zero' if I == 0 else 'forbidden_I_nonzero'] += 1
        continue
    omega = sum(1 for b in r['bad'] if not b[3])
    ff = Fr(1); Lad = Fr(1)
    for si, a in zip(r['forms'], r['ff']):
        ff *= Fr(a); Lad *= L_adjoint(cur[(tuple(r['n']), si)], q, B)
    ok = I * I / ff == 2 ** omega * L / (q * q * Lad)
    st['allowed_match' if ok else 'allowed_mismatch'] += 1
print(dict(q=q, **st))
