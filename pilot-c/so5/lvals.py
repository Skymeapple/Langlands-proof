import cypari2,sys,json,itertools,math; pari=cypari2.Pari(); pari.allocatemem(10**10); pari.set_real_precision(19)
pari('read("lvals.gp")')
p=int(sys.argv[1]); NC=int(sys.argv[2])
D=json.load(open(f'periods_{p}.json'))
def embedded(k):
    pari(f'mf{k}=mfinit([{p},{k}],0); EB{k}=mfeigenbasis(mf{k})')
    out={}
    for i in range(1,int(pari(f'#EB{k}'))+1):
        deg=int(pari(f'poldegree(mfparams(EB{k}[{i}])[4])'))
        pari(f'co=mfcoefs(EB{k}[{i}],{NC}); P=mfparams(EB{k}[{i}])[4]; rts=if(poldegree(P)==1,[0],polroots(P)); pet=(({p}+1))*mfpetersson(mfsymbol(mf{k},EB{k}[{i}]))')
        for e in range(deg):
            lab=f'{p}.{k}.{i}.{e}'
            pari(f'an_{k}_{i}_{e} = real(apply(x->if(type(x)=="t_POLMOD", subst(lift(x),variable(P),rts[{e+1}]), x), co)); pt_{k}_{i}_{e}=real(if(type(pet)=="t_MAT", pet[{e+1},{e+1}], pet))')
            out[lab]=(f'an_{k}_{i}_{e}', f'pt_{k}_{i}_{e}')
    return out
F4=embedded(4); F2=embedded(2)
print('coeffs ready',flush=True)
rows=[]
cacheRS={}
for per in D['periods']:
    if not per['F'].startswith('SK:'): continue
    flab=per['F'][3:]; G=per['G']
    if 'Eis' in G: 
        rows.append(dict(f=flab,sigma=G,P2n=per['P2n'],note='Eisenstein on SO(4) side')); continue
    g1,g2=G.split('x'); af=F4[flab][0]; a1,pt1=F2[g1]; a2,pt2=F2[g2]
    pari(f'B=bestL(s->tripleL422({p},{af},{a1},{a2},{NC},s)); LT=lfun(B[1],3)')
    row=dict(f=flab,sigma=G,P2n=per['P2n'],trip_sign=int(pari('B[3]')),trip_feq=int(pari('B[2]')),Ltrip=float(pari('LT')),pet1=float(pari(pt1)),pet2=float(pari(pt2)),ap_f=float(pari(f'{af}[{p}+1]')),ap1=float(pari(f'{a1}[{p}+1]')),ap2=float(pari(f'{a2}[{p}+1]')))
    if g1!=g2:
        pari(f'B2=bestL(s->rsL({p},{a1},{a2},{NC},s)); LR=lfun(B2[1],2)')
        row.update(rs_feq=int(pari('B2[2]')),Lrs=float(pari('LR')))
    print(row,flush=True); rows.append(row)
json.dump(rows,open(f'lvals_{p}.json','w'),indent=1)
