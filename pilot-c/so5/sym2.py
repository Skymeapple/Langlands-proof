import cypari2,sys,json; pari=cypari2.Pari(); pari.allocatemem(10**10); pari.set_real_precision(19)
from embed import make_embedded
pari('read("lvals.gp")')
p=int(sys.argv[1]); NC=int(sys.argv[2])
D=json.load(open(f'periods_{p}.json')); fv=json.load(open('fvals_11_23_29_31_37_43.json'))
embedded=make_embedded(pari,p,NC); F4=embedded(4); F2=embedded(2)
rows=[]
for per in D['periods']:
    if not per['F'].startswith('SK:'): continue
    G=per['G']; flab=per['F'][3:]
    if 'Eis' in G: continue
    g1,g2=G.split('x')
    if g1!=g2:
        rows.append(dict(f=flab,sigma=G,P2n=per['P2n'],kind='offdiag')); continue
    pari(f'B=bestL(s->fsym2L({p},{F4[flab][0]},{F2[g1][0]},{NC},s)); LS=lfun(B[1],3)')
    r=dict(f=flab,sigma=G,P2n=per['P2n'],eps_f=fv[flab]['eps'],feq=int(pari('B[2]')),sgn=int(pari('B[3]')),Lsym=float(pari('LS')),petg=float(pari(F2[g1][1])))
    r['Yp']=r['P2n']*fv[flab]['pet']*fv[flab]['L3']/r['Lsym'] if abs(r['Lsym'])>1e-12 else None
    print(r,flush=True); rows.append(r)
json.dump(rows,open(f'sym2_{p}.json','w'),indent=1)
