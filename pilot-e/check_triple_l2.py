"""Triple products at levels n = P * l^2 (M = l^2, deg l = 1): local-type analysis.

For each curve the local representation at l (conductor exponent 2, tame since p >= 3 and f = 2) is
labelled from its Kodaira type:
  I_n* (n >= 1): St x chi (chi ramified quadratic)        I0*: ps, e = 2
  III, III*: e = 4      IV, IV*: e = 3      II, II*: e = 6
  (e = semistability defect; principal series 'ps' if q_l = 1 mod e, otherwise supercuspidal 'sc').
Checks:
  (1) the Euler product without an l-factor is a polynomial S(T) of degree <= 2 satisfying the functional
      equation c_{D-i} = eps q^{2(D-2i)} c_i  -> consistent with L_l(f1 x f2 x f3) = 1 and a(l) = 8;
  (2) X = L * prod <f_i,f_i>_D / (I^2 * prod ||f_i||^2) takes ONE value per class
      (multiset of local labels at l, eps_P);
  (3) the vanishing pattern of I per class.
Usage: python3 check_triple_l2.py q"""
import sys, json
from fractions import Fraction as Fr
from collections import defaultdict

q = int(sys.argv[1])
M = json.load(open(f'data/match_q{q}.json'))
R = json.load(open(f'data/triple_q{q}.json'))
cur = {(tuple(c['n']), c['match'][0]): c for c in M['curves'] if c['oo_split']}


def label(kod):
    if kod[0] == 'I' and kod[1:-1].isdigit() and kod.endswith('*') and kod != 'I0*':
        return 'Stxchi'
    e = {'I0*': 2, 'III': 4, 'III*': 4, 'IV': 3, 'IV*': 3, 'II': 6, 'II*': 6}[kod]
    return ('ps' if (q - 1) % e == 0 else 'sc') + str(e)


cls = defaultdict(lambda: dict(n=0, X=set(), I0_L0=0, I0_Lnz=0, Inz=0, kod=set()))
fe_ok = fe_bad = total = 0
bad_examples = []
for r in R:
    if not any(b[1] > 1 for b in r['bad']):
        continue
    total += 1
    n = tuple(r['n'])
    kods = [[k for P, k, f in cur[(n, si)]['local'] if f == 2][0] for si in r['forms']]
    labs = tuple(sorted(label(k) for k in kods))
    epsP = [b[2] for b in r['bad'] if b[3]][0]
    S = r['Lpoly']
    while S and S[-1] == 0:
        S = S[:-1]
    D = len(S) - 1
    eps = None
    good = D <= 2
    for i in range(D + 1):
        if S[i] == 0 and S[D - i] == 0:
            continue
        if S[i] == 0:
            good = False
            break
        e = Fr(S[D - i]) / (S[i] * Fr(q) ** (2 * (D - 2 * i)))
        if e not in (1, -1) or (eps is not None and e != eps):
            good = False
            break
        eps = e
    fe_ok += good
    fe_bad += (not good)
    if not good:
        bad_examples.append((labs, epsP, tuple(S)))
    c = cls[(labs, epsP)]
    c['n'] += 1
    c['kod'].add(tuple(sorted(kods)))
    I, L = Fr(r['period']), Fr(r['L'])
    if I == 0:
        c['I0_L0' if L == 0 else 'I0_Lnz'] += 1
    else:
        c['Inz'] += 1
        c['X'].add(r['X'])
print(dict(q=q, cases=total, functional_equation_ok=fe_ok, fe_fail=fe_bad, classes=len(cls),
           classes_with_one_X=sum(1 for c in cls.values() if len(c['X']) <= 1)))
import collections
print('FE failures by class:', dict(collections.Counter(bad_examples)))
for k, c in sorted(cls.items()):
    print(k, 'cases', c['n'], 'I!=0', c['Inz'], 'I=0&L=0', c['I0_L0'], 'I=0&L!=0', c['I0_Lnz'],
          'X', sorted(c['X']))
