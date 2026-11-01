"""Write compact CSV tables from match_*.json:  curves_q{p}.csv and newforms_q{p}.csv"""
import sys, json, csv
for p in (3, 5):
    D = json.load(open(f'data/match_q{p}.json'))
    places = sorted(D['curves'][0]['ap'].keys(), key=lambda k: (len(eval(k)), eval(k)[::-1]))
    def pstr(c):
        def term(i, a):
            m = '' if i == 0 else ('t' if i == 1 else f't^{i}')
            if i == 0:
                return str(a)
            return m if a == 1 else f'{a}{m}'
        return '+'.join(term(i, a) for i, a in reversed(list(enumerate(c))) if a) or '0'
    with open(f'data/newforms_q{p}.csv', 'w', newline='') as fo:
        w = csv.writer(fo)
        w.writerow(['level_n', 'index', 'old', 'multiplicity', 'curves_split_at_oo', 'curves_nonsplit_at_oo'] +
                   ['lambda_' + pstr(eval(k)) for k in places])
        for r in D['levels']:
            for i, s in enumerate(r['systems']):
                w.writerow([pstr(r['n']), i, int(s['old']), s['mult'], s['curves_split'], s['curves_nonsplit']] +
                           [s['lam'].get(k, '') for k in places])
    with open(f'data/curves_q{p}.csv', 'w', newline='') as fo:
        w = csv.writer(fo)
        w.writerow(['a2', 'a4', 'a6', 'conductor_n', 'deg_n', 'bad_fibres', 'oo_fibre', 'oo_split', 'newform_index'] +
                   ['a_' + pstr(eval(k)) for k in places])
        for c in D['curves']:
            w.writerow([pstr(c['a2']), pstr(c['a4']), pstr(c['a6']), pstr(c['n']), c['degn'],
                        ' '.join(f'{k}@({pstr(P)})' for P, k, f in c['local']), c['oo'], int(c['oo_split']),
                        c['match'][0]] + [c['ap'][k] for k in places])
print('ok')
