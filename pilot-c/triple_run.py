import cypari2,time,sys,json,itertools; pari=cypari2.Pari(); pari.allocatemem(8*10**9); pari.set_real_precision(19)
pari('read("brandt.gp")'); pari('read("triple.gp")')
p=int(sys.argv[1]); NC=int(sys.argv[2])
t=time.time(); pari(f'R=forms({p},{NC})'); n=int(pari('#R')); print('forms',n,time.time()-t,flush=True)
out=[]
for (i,j,k) in itertools.combinations_with_replacement(range(1,n+1),3):
  t=time.time()
  pari(f'f1=R[{i}];f2=R[{j}];f3=R[{k}]; W=f1[5]; Ip=sum(m=1,#W,f1[3][m]*f2[3][m]*f3[3][m]/W[m]); nv=prod(r=1,3,my(g=[f1,f2,f3][r]); sum(m=1,#W,g[3][m]^2/W[m])); eps=f1[2][{p}+1]*f2[2][{p}+1]*f3[2][{p}+1]')
  row=dict(forms=[str(pari(f'R[{x}][1]')) for x in (i,j,k)], ap=[int(pari(f'R[{x}][2][{p}+1]')) for x in (i,j,k)], I=float(pari('Ip')))
  best=None
  for s in (1,-1):
    pari(f'LT=tripleL({p},f1[2],f2[2],f3[2],{NC},{s}); fe=lfuncheckfeq(LT)')
    fe=int(pari('fe'))
    if best is None or fe<best[0]: best=(fe,s,float(pari('lfun(LT,2)')))
  row.update(feq=best[0],sign=best[1],L=best[2])
  row['C']=float(pari(f'{best[2]}*nv/Ip^2/(f1[4]*f2[4]*f3[4])')) if abs(row['I'])>1e-8 else None
  print(row, round(time.time()-t,1), flush=True); out.append(row)
json.dump(out,open(f'triple_{p}.json','w'),indent=1)
