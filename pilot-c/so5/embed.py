def make_embedded(pari,p,NC):
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
    return embedded
