# Calibration checks: Hecke period (X=PGL2/Gm) and Whittaker period (Petersson norm vs L(1,Ad))
import cypari2, json; pari=cypari2.Pari(); pari.allocatemem(4*10**9); pari.set_real_precision(38)
curves={'11a1':[0,-1,1,-10,-20],'37a1':[0,0,1,-1,0],'37b1':[0,1,1,-23,-50],'43a1':[0,1,1,0,0],'53a1':[1,-1,1,0,0],
 '61a1':[1,0,0,-2,1],'67a1':[0,1,1,-12,-21],'79a1':[1,1,1,-2,0],'83a1':[1,1,1,1,0],'89a1':[1,1,1,-1,0],'89b1':[1,1,0,4,5],'101a1':[0,1,1,-1,-1]}
out=[]
for lab,a in curves.items():
    pari(f'E=ellinit({a}); N=ellglobalred(E)[1]; mf=mfinit([N,2],0); EB=mfeigenbasis(mf); an=ellan(E,30)')
    N=int(pari('N'))
    k=[i for i in range(1,int(pari('#EB'))+1) if pari(f'mfcoefs(EB[{i}],30)[2..31]==an')]
    if len(k)!=1: print(lab,'no match',N); continue
    pari(f'F=EB[{k[0]}]; pet=(N+1)*mfpetersson(mfsymbol(mf,F))')
    # Hecke period: int_0^infty f(iy) dy computed from q-expansion, compared with L(f,1)/(2pi)
    pari('a=ellan(E,4000); hp=(1+ellrootno(E))*sum(n=1,4000,a[n]*exp(-2*Pi*n/sqrt(N))/(2*Pi*n))')  # (1+eps) * int_{1/sqrt N}^oo f(iy)dy, using f|W_N
    pari('L1=lfun(E,1); S2=lfun(lfunsympow(E,2),2); deg=ellmoddegree(E)')
    # Whittaker/adjoint: ratio L(Sym^2 E,2) / pet
    rat=pari('S2/pet'); 
    row=dict(curve=lab,N=N,rootno=int(pari('ellrootno(E)')),hecke_period=float(pari('hp')),L1_over_2pi=float(pari('L1/(2*Pi)')),
      pet=float(pari('pet')),LSym2_at_2=float(pari('S2')),ratio_over_8pi3_div_N=float(pari('S2/pet/(8*Pi^3)*N')),
      moddeg=int(pari('deg')),area=float(pari('E.area')),deg_check=float(pari('4*Pi^2*pet/E.area')))
    print(row,flush=True); out.append(row)
json.dump(out,open('whittaker_results.json','w'),indent=1)
