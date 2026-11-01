\\ numeric eigenforms for commuting Hecke matrices T3,T5 self-adjoint for masses 1/A
eigforms(T3, T5, A, T7=0) = { my(h=#A, D=matdiagonal(vector(h,i,1/sqrt(A[i]))), Di=matdiagonal(vector(h,i,sqrt(A[i]))), T=T3+Pi*T5/7+if(T7,exp(1)*T7/13,0), S, J, out=List());
  \\ T_ij / A_i... symmetrise: S = Di^-1 ... check numerically
  S = D^-1 * T * D; \\ try
  if(normlp(S-S~) > 1e-10, S = D*T*D^-1);
  if(normlp(S-S~) > 1e-10, error("not self-adjoint"));
  J = qfjacobi(S);
  for(k=1,h, my(u=J[2][,k], F=if(normlp(D^-1*T*D-(D^-1*T*D)~)<1e-10, D*u, D^-1*u));
    my(i0=1); for(i=1,h, if(abs(F[i])>abs(F[i0]), i0=i));
    listput(out, [ (T3*F)[i0]/F[i0], (T5*F)[i0]/F[i0], F, if(T7,(T7*F)[i0]/F[i0],0)]));
  Vec(out) };
