isin(L,x) = for(k=1,#L, if(L[k]==x, return(1))); 0;
\\ Supersingular j-invariants over F_{p^2}, Brandt matrices B(l) via Phi_l
ffroots(P, t) = my(F=factor(P*t^0)[,1], E=factor(P*t^0)[,2], R=List()); \
  for(k=1,#F, if(poldegree(F[k])==1, my(r=-polcoef(F[k],0)/polcoef(F[k],1)); for(m=1,E[k], listput(R,r)))); Vec(R);
\\ list of ss j's (as ffelts) by BFS on the 2-isogeny graph (p>3 ok)
sslist(p) = { my(j0=ellsupersingularj(p), L=List([j0]), i=1, P2=polmodular(2));
  while(i<=#L, my(R=ffroots(subst(subst(P2,'x,L[i]),'y,'x), j0));
    for(k=1,#R, if(!isin(L,R[k]), listput(L,R[k]))); i++);
  Vec(L) };
brandt(p, J, l) = { my(n=#J, B=matrix(n,n), Pl=polmodular(l));
  for(i=1,n, my(R=ffroots(subst(subst(Pl,'x,J[i]),'y,'x), J[1]));
    if(#R != l+1, error("root count ",#R," at i=",i));
    for(k=1,#R, my(c=vecsearch2(J,R[k])); B[i,c]++)); B };
vecsearch2(J,x) = for(k=1,#J, if(J[k]==x, return(k))); error("not found");
\\ w_i = #Aut/2 : 3 for j=0, 2 for j=1728, else 1 (p>3)
wts(J) = vector(#J,i, if(J[i]==0,3, if(J[i]==1728,2,1)));
