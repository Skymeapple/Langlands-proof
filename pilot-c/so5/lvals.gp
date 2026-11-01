kron(A,B) = matconcat(matrix(#A~,#A,i,j,A[i,j]*B));
\\ triple L(f x g1 x g2) with f weight 4, g weight 2, level p (all Steinberg at p); arithmetic normalisation, centre s=3
tripleL422(p, af, a1, a2, NC, sgn) = { my(eps=af[p+1]/p*a1[p+1]*a2[p+1], E=vector(NC), v=vector(NC));
  forprime(q=2, NC, my(Fq);
    if(q==p, Fq=(1-eps*p*'T)*(1-eps*p^2*'T)^2,
      Fq=polrecip(charpoly(kron(kron([af[q+1],-q^3;1,0],[a1[q+1],-q;1,0]),[a2[q+1],-q;1,0]),'T)));
    E[q]=1/(Fq+O('T^(logint(NC,q)+1))));
  v[1]=1; for(n=2,NC, my(f=factor(n), r=1); for(i=1,#f~, r*=polcoef(E[f[i,1]],f[i,2],'T)); v[n]=r);
  lfuncreate([v,0,[0,1,-1,0,-1,0,-2,-1],6,p^5,sgn]) };
\\ Rankin-Selberg L(g1 x g2, s), weight 2 forms of level p, centre 3/2
rsL(p, a1, a2, NC, sgn) = { my(eps=a1[p+1]*a2[p+1], E=vector(NC), v=vector(NC));
  forprime(q=2, NC, my(Fq);
    if(q==p, Fq=(1-eps*'T)*(1-eps*p*'T),
      Fq=polrecip(charpoly(kron([a1[q+1],-q;1,0],[a2[q+1],-q;1,0]),'T)));
    E[q]=1/(Fq+O('T^(logint(NC,q)+1))));
  v[1]=1; for(n=2,NC, my(f=factor(n), r=1); for(i=1,#f~, r*=polcoef(E[f[i,1]],f[i,2],'T)); v[n]=r);
  lfuncreate([v,0,[0,1,-1,0],3,p^2,sgn]) };
bestL(mk) = { my(L1=mk(1), L2=mk(-1), c1=lfuncheckfeq(L1), c2=lfuncheckfeq(L2)); if(c1<=c2, [L1,c1,1], [L2,c2,-1]) };
\\ L(f x Sym^2 g, s): f weight 4, g weight 2, level p (Steinberg at p); centre s=3
fsym2L(p, af, ag, NC, sgn) = { my(ef=af[p+1]/p, E=vector(NC), v=vector(NC));
  forprime(q=2, NC, my(Fq);
    if(q==p, Fq=(1-ef*p*'T)*(1-ef*p^2*'T),
      my(S=matcompanion('x^3 - (ag[q+1]^2-q)*'x^2 + q*(ag[q+1]^2-q)*'x - q^3));
      Fq=polrecip(charpoly(kron([af[q+1],-q^3;1,0],S),'T)));
    E[q]=1/(Fq+O('T^(logint(NC,q)+1))));
  v[1]=1; for(n=2,NC, my(f=factor(n), r=1); for(i=1,#f~, r*=polcoef(E[f[i,1]],f[i,2],'T)); v[n]=r);
  lfuncreate([v,0,[0,1,-1,0,-2,-1],6,p^4,sgn]) };
