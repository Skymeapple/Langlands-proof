# Test of BZSV prediction for X = PGL2/T (nonsplit torus): Waldspurger/Gross formula
import cypari2, sys, json
pari=cypari2.Pari(); pari.allocatemem(4*10**9); pari.set_real_precision(38)
pari('read("brandt.gp")')
def run(p, Dmax=200, out=None):
    pari(f'p={p}; J=sslist(p); W=wts(J); B2=brandt(p,J,2); B3=brandt(p,J,3); mf=mfinit([p,2],0); EB=mfeigenbasis(mf)')
    res=[]
    for k in range(int(pari('#EB'))):
        co=pari(f'co=mfcoefs(EB[{k+1}],5); [type(co[3]),type(co[4])]')
        if str(co)!='["t_INT", "t_INT"]': continue   # rational newforms only
        a2=int(pari('co[3]')); a3=int(pari('co[4]'))
        # common eigenvector of B2,B3 with eigenvalues a2,a3 (rational)
        K=pari(f'K=matintersect(matker(B2-({a2})),matker(B3-({a3}))); #K')
        if int(K)!=1: print(p,k,'eigenspace dim',K); continue
        pari('v=K[,1]; v=v/content(v)')
        nv=pari('nv=sum(i=1,#J,v[i]^2/W[i])')
        # Petersson norm (unnormalized, d x d y over Gamma0(p)\H)
        pari(f'FS=mfsymbol(mf,EB[{k+1}]); pet=(p+1)*mfpetersson(FS)')
        # determine sign via functional equation check
        pari(f'an=mfcoefs(EB[{k+1}],60000)')
        pari('Lf=lfuncreate([vector(60000,n,an[n+1]),0,[0,1],2,p,1]); c1=lfuncheckfeq(Lf); Lf2=lfuncreate([vector(60000,n,an[n+1]),0,[0,1],2,p,-1]); c2=lfuncheckfeq(Lf2); if(c2<c1, Lf=Lf2; eps=-1, eps=1)')
        eps=int(pari('eps')); Lf1=pari('L1=lfun(Lf,1)')
        rows=[]
        for D in range(-7,-Dmax,-1):
            if not int(pari(f'isfundamental({D})')) or int(pari(f'kronecker({D},p)'))!=-1: continue
            h=int(pari(f'qfbclassno({D})'))
            pari(f'H=polclass({D}); R=ffroots(H*J[1]^0, J[1]); if(#R!={h}, error("roots"))')
            P=pari('P=sum(i=1,#R, v[vecsearch2(J,R[i])])')
            N2=p*D*D
            pari(f'LD=lfuncreate([vector(60000,n,an[n+1]*kronecker({D},n)),0,[0,1],2,{N2},eps*kronecker({D},-p)]); feq=lfuncheckfeq(LD); LDv=lfun(LD,1)')
            Lprod=pari('L1*LDv')
            C=pari(f'if(P==0, "P=0", L1*LDv*sqrt({-D})*nv/P^2/pet)')
            rows.append(dict(D=D,h=h,P=int(P),L1=float(Lf1),LD=float(pari('LDv')),feq=int(pari('feq')),C=str(C)))
            print(p,'a2=',a2,'eps',eps,'D',D,'h',h,'P',P,'L(f,1)=',pari('L1'),'L(fxD,1)=',pari('LDv'),'feq',pari('feq'),'C=',C, flush=True)
        res.append(dict(p=p,a2=a2,a3=a3,eps=eps,v=str(pari('v')),w=str(pari('W')),norm=str(nv),pet=float(pari('pet')),rows=rows))
    return res
if __name__=='__main__':
    allr=[]
    for p in map(int,sys.argv[1:]):
        allr+=run(p, Dmax=120)
    json.dump(allr,open('gross_results_'+'_'.join(sys.argv[1:])+'.json','w'),indent=1)
