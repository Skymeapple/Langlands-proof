import cypari2,json,sys; pari=cypari2.Pari(); pari.allocatemem(4*10**9); pari.set_real_precision(30)
out={}
for p in map(int,sys.argv[1:]):
  pari(f'mf=mfinit([{p},4],0); E=mfeigenbasis(mf)')
  for i in range(1,int(pari('#E'))+1):
    pari(f'L=lfunmf(mf,E[{i}]); pet=({p}+1)*mfpetersson(mfsymbol(mf,E[{i}])); deg=poldegree(mfparams(E[{i}])[4])')
    deg=int(pari('deg'))
    for e in range(deg):
        pari(f'LL=if(deg==1,L,L[{e+1}]); pe=real(if(type(pet)=="t_MAT",pet[{e+1},{e+1}],pet))')
        out[f'{p}.4.{i}.{e}']=dict(L2=float(pari('lfun(LL,2)')),L3=float(pari('lfun(LL,3)')),pet=float(pari('pe')),eps=int(pari('lfunrootres(LL)[3]')))
json.dump(out,open('fvals_'+'_'.join(sys.argv[1:])+'.json','w'),indent=1)
print(out)
