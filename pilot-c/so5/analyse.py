import cypari2,sys,json,itertools; pari=cypari2.Pari(); pari.allocatemem(8*10**9); pari.set_real_precision(30)
pari('read("lattice.gp")'); pari('read("analyse.gp")')
p=int(sys.argv[1]); NC=int(sys.argv[2]) if len(sys.argv)>2 else 0
pari(f'[R5,I5,T5_3,T5_5,R4,I4,T4_3,T4_5,CC,A5,A4]=read("so5_{p}.gpd")')
pari('T4_7=heckemat(R4,I4,7)')
pari('E5=eigforms(T5_3,T5_5,A5); E4=eigforms(T4_3,T4_5,A4,T4_7)')
# newform data (embedded), weight 2 and 4
def forms(k):
    pari(f'mf=mfinit([{p},{k}],0); EB=mfeigenbasis(mf)')
    out=[]
    for i in range(1,int(pari('#EB'))+1):
        P=pari(f'mfparams(EB[{i}])[4]'); deg=int(pari(f'poldegree(mfparams(EB[{i}])[4])'))
        roots=[0] if deg==1 else list(pari(f'polroots(mfparams(EB[{i}])[4])'))
        for e,r in enumerate(roots):
            ev=lambda x: float(pari(f'real(subst(lift({x}),variable(mfparams(EB[{i}])[4]),{r}))')) if deg>1 else float(x)
            co=pari(f'mfcoefs(EB[{i}],{p}+1)')
            out.append(dict(label=f'{p}.{k}.{i}.{e}',a3=ev(co[3]),a5=ev(co[5]),a7=ev(co[7]),ap=ev(co[p]) if p< len(co) else None, i=i, root=str(r), deg=deg))
    return out
W2=forms(2); W4=forms(4)
eis=dict(label='Eis',a3=4.0,a5=6.0,a7=8.0)
def close(a,b): return abs(a-b)<1e-6
# classify quinary eigenforms
q5=[]
for k,(l3,l5,F,_) in enumerate(pari('E5')):
    l3=float(l3); l5=float(l5); tag='other'
    if close(l3,40) and close(l5,156): tag='const'
    for f in W4:
        if close(l3,f['a3']+12) and close(l5,f['a5']+30): tag='SK:'+f['label']
        for g in W2:
            if close(l3,3*g['a3']+f['a3']) and close(l5,5*g['a5']+f['a5']): tag=f"Yoshida:{g['label']},{f['label']}"
    q5.append((k,l3,l5,tag))
q4=[]
for k,(l3,l5,F,l7) in enumerate(pari('E4')):
    l3=float(l3); l5=float(l5); l7=float(l7); tags=[]
    for g1,g2 in itertools.combinations_with_replacement([eis]+W2,2):
        if close(l3,g1['a3']*g2['a3']) and close(l5,g1['a5']*g2['a5']) and close(l7,g1['a7']*g2['a7']): tags.append(f"{g1['label']}x{g2['label']}")
    q4.append((k,l3,l5,'|'.join(tags) or 'unmatched'))
for x in q5: print('Q5',x)
for x in q4: print('Q4',x)
# periods
res=[]
for (k5,_,_,t5) in q5:
    for (k4,_,_,t4) in q4:
        pari(f'F=E5[{k5+1}][3]; G=E4[{k4+1}][3]; P=sum(i=1,#F, F[i]/A5[i]*sum(k=1,#G, CC[i][k]*G[k])); nF=sum(i=1,#F,F[i]^2/A5[i]); nG=sum(k=1,#G,G[k]^2/A4[k])')
        r=float(pari('P^2/(nF*nG)'))
        res.append(dict(F=t5,G=t4,P2n=r))
        if abs(r)>1e-12 or not t5.startswith('SK') : pass
for x in res:
    if x['F'].startswith('SK') or x['P2n']>1e-12: print('PER', x)
json.dump(dict(p=p,q5=q5,q4=q4,W2=W2,W4=W4,periods=res),open(f'periods_{p}.json','w'),indent=1)
