\\ Maximal order of B_{p,infty} (Pizer) and its norm-form Gram matrix (B(x,y)=nrd(x+y)-nrd(x)-nrd(y))
quatgram(p) = { my(al, be, bas, q, c);
  if(p%4==3, al=-1; be=-p; bas=[[1,0,0,0],[0,1,0,0],[1/2,0,1/2,0],[0,1/2,0,1/2]],
  if(p%8==5, al=-2; be=-p; bas=[[1/2,0,1/2,1/2],[0,1/4,1/2,1/4],[0,0,1,0],[0,0,0,1]],
    q=3; while(!(q%4==3 && isprime(q) && kronecker(p,q)==-1), q++);
    al=-p; be=-q; c=0; while((c^2*p+1)%q, c++);
    bas=[[1/2,0,1/2,0],[0,1/2,0,1/2],[0,0,1/q,c/q],[0,0,0,1]];
    \\ Pizer's order for p = 1 mod 8 uses B=(-p,-q) with i^2=-p, j^2=-q
  ));
  my(nrd = v -> v[1]^2 - al*v[2]^2 - be*v[3]^2 + al*be*v[4]^2);
  my(G = matrix(4,4,a,b, nrd(bas[a]+bas[b]) - nrd(bas[a]) - nrd(bas[b])));
  G };
\\ odd prime ell-neighbours of even lattice with Gram G (diag = 2Q)
neighbours(G, ell) = { my(n=#G, res=List(), seen=List());
  forvec(v=vector(n,i,[0,ell-1]), 
    my(x=v~, f=0); \\ normalise: first nonzero coordinate = 1
    for(i=1,n, if(x[i], f=(x[i]==1); break));
    if(!f, next);
    if((x~*G*x/2) % ell, next);
    \\ lift so that Q(x) = 0 mod ell^2
    my(Q=x~*G*x/2, Bx=G*x, k=0);
    for(i=1,n, if(Bx[i]%ell, k=i; break));
    if(!k, next); \\ x in ell*L^# : skip (radical), not for odd ell coprime to disc
    my(t = Mod(-Q/ell,ell)/Mod(Bx[k],ell)); x[k] += ell*lift(t);
    if((x~*G*x/2) % ell^2, error("lift"));
    \\ L_x = {y : B(x,y) = 0 mod ell}
    my(K = matkermod(Mat(Bx~), ell), M);
    M = mathnf(concat(concat(ell*K, ell^2*matid(n)), x)) / ell;
    listput(res, M~*G*M));
  Vec(res) };
inv(G) = { my(a=qfauto(G)[1]); [a, qfminim(G,2,,2)[1], qfminim(G,4,,2)[1]] };
\\ classify: list of reps; returns index of class of G, appending if new
classidx(G, ~R, ~I) = { my(iv=inv(G), Gl=qflllgram(G), H=Gl~*G*Gl);
  for(k=1,#R, if(I[k]==iv && qfisom(R[k],H), return(k)));
  listput(R,H); listput(I,iv); #R };
\\ genus by neighbour closure; returns [reps, invariants, T_ell matrix]
genus(G0, ell) = { my(R=List(), I=List(), T=List(), i=1);
  classidx(G0, ~R, ~I);
  while(i<=#R, my(N=neighbours(R[i],ell), row=List());
    for(k=1,#N, listput(row, classidx(N[k], ~R, ~I))); listput(T, Vec(row)); i++);
  my(h=#R, M=matrix(h,h)); for(a=1,h, for(k=1,#T[a], M[a,T[a][k]]++));
  [Vec(R), Vec(I), M] };
\\ Hecke matrix of ell-neighbours on an existing genus list R (with invariants I)
heckemat(R, I, ell) = { my(h=#R, M=matrix(h,h), RR=List(R), II=List(I));
  for(a=1,h, my(N=neighbours(R[a],ell)); for(k=1,#N, my(c=classidx(N[k], ~RR, ~II)); if(c>h, error("left genus at ell=",ell)); M[a,c]++)); M };
\\ index of G in fixed list (error if absent)
findclass(G, R, I) = { my(iv=inv(G)); for(k=1,#R, if(I[k]==iv && qfisom(R[k],G), return(k))); 0 };
\\ for each quinary class: vector of counts c[k] = #{v : Q(v)=1, B(v,L) in 2Z, v^perp ~ quaternary class k}
perpcounts(R5, R4, I4) = { my(out=vector(#R5));
  for(i=1,#R5, my(G=R5[i], V=qfminim(G,2,,2)[3], c=vector(#R4));
    for(t=1,#V, my(v=V[,t]); if(v~*G*v!=2, next); my(b=G*v); if(#select(z->z%2,Vec(b)), next);
      my(K=matkerint(Mat(b~)), H=K~*G*K, k=findclass(H,R4,I4)); if(!k, error("perp not in genus, class ",i)); c[k]+=2);
    out[i]=c); out };
