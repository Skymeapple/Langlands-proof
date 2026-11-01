\\ numerically embedded newforms & Brandt eigenvectors at prime level p
\\ returns list of [label, a_n vector (real), brandt vector (real), petersson unnormalized]
kron3(A,B,C) = matkronecker(matkronecker(A,B),C);
matkronecker(A,B) = { my(m=#A~, n=#A, r=#B~, s=#B, M=matrix(m*r,n*s));
  for(i=1,m, for(j=1,n, for(k=1,r, for(l=1,s, M[(i-1)*r+k,(j-1)*s+l]=A[i,j]*B[k,l])))); M };
forms(p, NC) = { my(J=sslist(p), W=wts(J), B2=brandt(p,J,2), B3=brandt(p,J,3), B5=brandt(p,J,5), mf=mfinit([p,2],0), EB=mfeigenbasis(mf), out=List());
  for(k=1,#EB, my(F=EB[k], P=mfparams(F)[4], co=mfcoefs(F,NC), K, emb, FS=mfsymbol(mf,F), pets);
    \\ eigenvector over K = Q[y]/P
    K = matker(B2 - co[3]*matid(#J)); 
    if(#K!=1, K = matintersect(K, matker(B3-co[4]*matid(#J))));
    if(#K!=1, K = matintersect(K, matker(B5-co[6]*matid(#J))));
    if(#K!=1, error("eigenspace dim ",#K," p=",p," k=",k));
    pets = mfpetersson(FS);  \\ vector over embeddings when deg>1? 
    emb = if(poldegree(P)==1, [0], polroots(P));
    for(e=1,#emb, my(ev = x->if(type(x)=="t_POLMOD", subst(lift(x),variable(P),real(emb[e])), x));
      my(an=apply(ev,co), v=apply(ev,K[,1]), pt=if(type(pets)=="t_MAT", pets[e,e], pets));
      listput(out,[Str(p,"-",k,"-",e), real(an), real(v), real((p+1)*pt), W])));
  Vec(out) };
\\ triple product L-function L(f1 x f2 x f3, s), arithmetic normalization, center s=2
\\ an_i real coefficient vectors (index n+1), ap at p = +-1
tripleL(p, a1, a2, a3, NC, sgn) = { my(eps=a1[p+1]*a2[p+1]*a3[p+1], v=vector(NC), E);
  E = vector(NC);  \\ build via Euler product
  forprime(q=2, NC, my(Fq);
    if(q==p, Fq = (1-eps*'T)*(1-eps*p*'T)^2,
      my(A=kron3([a1[q+1],-q;1,0],[a2[q+1],-q;1,0],[a3[q+1],-q;1,0]));
      Fq = polrecip(charpoly(A,'T)));  \\ det(1 - A T)
    my(S = 1/(Fq + O('T^(logint(NC,q)+1))));
    E[q] = S);
  v[1]=1;
  for(n=2,NC, my(f=factor(n), r=1); for(i=1,#f~, r *= polcoef(E[f[i,1]], f[i,2], 'T)); v[n]=r);
  lfuncreate([v, 0, [-1,0,-1,0,-1,0,0,1], 4, p^5, sgn]) };
