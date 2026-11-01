# p=43: L(f x Sym^2 g) via L(f x g x g, s) = L(f x Sym^2 g, s) * L(f, s-1); use derivatives when L(f,2)=0
import cypari2,json,math; pari=cypari2.Pari(); pari.allocatemem(10**10); pari.set_real_precision(19)
from embed import make_embedded
pari('read("lvals.gp")')
import sys
p=int(sys.argv[1]); NC=int(sys.argv[2])
emb=make_embedded(pari,p,NC); F4=emb(4); F2=emb(2)
import glob
fv={k:v for g in glob.glob('fvals_*.json') for k,v in json.load(open(g)).items()}
pari(f'mf4=mfinit([{p},4],0); EB4=mfeigenbasis(mf4)')
rows=json.load(open(f'sym2_{p}.json')); out=[]
for r in rows:
    if 'Yp' not in r: out.append(r); continue
    f=r['f']; g=r['sigma'].split('x')[0]; i,e=int(f.split('.')[2]),int(f.split('.')[3])
    pari(f'Lf=lfunmf(mf4,EB4[{i}]); Lf=if(type(Lf)=="t_VEC" && #Lf>0 && type(Lf[1])=="t_VEC" && #Lf[1]>1 && poldegree(mfparams(EB4[{i}])[4])>1, Lf[{e+1}], Lf)')
    pari(f'B=bestL(s->tripleL422({p},{F4[f][0]},{F2[g][0]},{F2[g][0]},{NC},s))')
    if r['eps_f']==1:
        ls=float(pari('lfun(B[1],3)/lfun(Lf,2)'))
    else:
        ls=float(pari('lfun(B[1],3,1)/lfun(Lf,2,1)'))
    r2=dict(r); r2['Lsym_old']=r['Lsym']; r2['Lsym']=ls; r2['trip_feq']=int(pari('B[2]')); r2['method']='triple/L(f,2)' if r['eps_f']==1 else "triple'/L'(f,2)"
    r2['Yp']=r['P2n']*fv[f]['pet']*fv[f]['L3']/ls
    print(f,g,r['eps_f'],r2['trip_feq'],'%.12f'%(r2['Yp']*(p-r['eps_f'])/(3/(8*math.pi**3))),flush=True)
    out.append(r2)
json.dump(out,open(f'sym2_{p}_fixed.json','w'),indent=1)
