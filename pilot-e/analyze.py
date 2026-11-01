"""Both-direction check: every curve matches exactly one rational eigensystem of its level, and every
rational *new* eigensystem is matched by at least one curve split at oo and one non-split at oo.
An eigensystem at level n is old if it agrees (on common good places) with a system at a proper divisor
level.  Usage: python3 analyze.py match.json"""
import sys, json
from flint import nmod_poly
D = json.load(open(sys.argv[1]))
p = D['curves'][0]['p']
lev = {tuple(r['n']): r for r in D['levels']}
def P(c): return nmod_poly(list(c), p)
summary = dict(levels=0, levels_with_cusp_forms=0, rational_systems=0, new=0, old=0,
               new_matched=0, new_unmatched=[], curves=len(D['curves']), curves_unique_match=0,
               curves_matching_old=0)
for c in D['curves']:
    if len(c.get('match', [])) == 1:
        summary['curves_unique_match'] += 1
for nk, r in lev.items():
    summary['levels'] += 1
    if r['dim']:
        summary['levels_with_cusp_forms'] += 1
    n = P(nk)
    for i, s in enumerate(r['systems']):
        summary['rational_systems'] += 1
        old = False
        for mk, rm in lev.items():
            m = P(mk)
            if m.degree() >= n.degree() or not (n % m).is_zero():
                continue
            for sm in rm['systems']:
                common = set(s['lam']) & set(sm['lam'])
                if common and all(s['lam'][k] == sm['lam'][k] for k in common):
                    old = True
        s['old'] = old
        cs = [c for c in D['curves'] if tuple(c['n']) == nk and c.get('match') == [i]]
        s['curves_split'] = sum(1 for c in cs if c['oo_split'])
        s['curves_nonsplit'] = sum(1 for c in cs if not c['oo_split'])
        if old:
            summary['old'] += 1
            summary['curves_matching_old'] += len(cs)
        else:
            summary['new'] += 1
            if s['curves_split'] and s['curves_nonsplit']:
                summary['new_matched'] += 1
            else:
                summary['new_unmatched'].append((nk, i, s['mult'], s['curves_split'], s['curves_nonsplit']))
json.dump(D, open(sys.argv[1], 'w'))
print(json.dumps(summary, indent=1))
