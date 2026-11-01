"""Export all triple-product cases with their local data (for deriving the constants).
Writes data/triple_local_data_q{q}.csv with: level n, P, form indices, per bad place (deg, exponent,
eps = a1 a2 a3, is_P), Kodaira types of the three curves at each bad place, period I, L (centre value of the
Euler product without the l-factor when exponent 2), <f_i,f_i>_D, Petersson norms, X."""
import json, csv
for q in (3, 5):
    M = json.load(open(f'data/match_q{q}.json'))
    cur = {(tuple(c['n']), c['match'][0]): c for c in M['curves'] if c['oo_split']}
    R = json.load(open(f'data/triple_q{q}.json'))
    with open(f'data/triple_local_data_q{q}.csv', 'w', newline='') as fo:
        w = csv.writer(fo)
        w.writerow(['n', 'P', 'forms', 'bad_places(deg,exp,eps,isP)', 'kodaira_at_bad_places', 'I', 'L_centre',
                    'Lpoly', 'ff_D', 'petersson', 'X'])
        for r in R:
            n = tuple(r['n'])
            kods = [' '.join(f'{k}' for P, k, f in cur[(n, si)]['local']) for si in r['forms']]
            w.writerow([r['n'], r['P'], r['forms'], r['bad'], ' | '.join(kods), r['period'], r['L'], r['Lpoly'],
                        r['ff'], r['pet'], r.get('X', '')])
print('ok')
