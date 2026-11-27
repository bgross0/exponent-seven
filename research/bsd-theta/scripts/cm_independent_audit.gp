\\ Independent PARI/GP audit of the CM theta certificate.
\\ Run from repository root: gp -fq -s 256M scripts/cm_independent_audit.gp
\\ Integer-only JSON arrays are GP vector expressions; all other witness arrays
\\ below are embedded and bound to their originating JSON by the audit receipt.
\\ No routine from tools/supersingular_probe.py or tools/cm_jet_probe.py is used.
require(c,msg)=if(!c,error(msg));
readnumjson(file)=eval(concat(readstr(file)));
main()={
  q=389; p=5; precision_exponent=4;
  ss_pairs=[[0,0],[0,96],[0,293],[7,0],[16,0],[17,0],[36,0],[48,20],[48,369],[78,112],[78,277],[112,136],[112,253],[121,0],[148,124],[148,265],[149,168],[149,221],[154,0],[173,124],[173,265],[181,68],[181,321],[220,0],[284,51],[284,338],[318,0],[327,0],[347,53],[347,336],[358,0],[386,6],[386,383]];
  stored_rows=[[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0],[0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0],[0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0],[0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0],[0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0],[0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,1,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0],[0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0],[0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],[0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0],[0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0],[1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,2,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,1,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,1,0,0,0,0],[0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0]];
  v=[0,0,0,2,-2,-2,-2,1,1,-1,-1,1,1,0,-1,-1,0,0,0,1,1,1,1,0,-1,-1,0,2,0,0,2,-1,-1];
  cm7=[10,11,14,22,23,29,30];
  n=#ss_pairs;
  require(n==33 && #Set(ss_pairs)==33,"supersingular witness count");
  a=ffgen(Mod(1,q)*(z^2-2),'a);
  J=vector(n,i,ss_pairs[i][1]+ss_pairs[i][2]*a);
  require(prod(i=1,n,ellissupersingular(ellinit(ellfromj(J[i])))),"supersingularity");
  w=vector(n,i,if(J[i]==0,3,if(J[i]==1728,2,1)));
  require(sum(i=1,n,1/w[i])==(q-1)/12,"Eichler mass completeness");
  Phi=polmodular(2);
  A=matrix(n,n,i,j,stored_rows[i][j]);
  require(prod(i=1,n,subst(Phi,x,J[i])==prod(j=1,n,(y-J[j])^A[i,j])),"Phi2 exact factorization / multiplicities");
  require(prod(i=1,n,sum(j=1,n,A[i,j])==3),"Brandt row sums");
  require(prod(i=1,n,prod(j=1,n,w[j]*A[i,j]==w[i]*A[j,i])),"weighted self-adjointness");
  require(A*v~ == -2*v~,"right eigenfunction");
  require(matsize(matker(A+2*matid(n)))[2]==1,"unique rational T2 eigenspace");
  require(gcd(v)==1 && sum(i=1,n,v[i]/w[i])==0,"primitive cuspidal normalization");
  require(prod(i=1,n,sum(j=1,n,(J[j]==J[i]^q)*v[j])==v[i]),"Frobenius plus sign");
  E=ellinit([0,1,1,-2,0]);
  require(ellglobalred(E)[1]==389 && ellap(E,2)==-2 && ellap(E,389)==1 && ellrootno(E)==1,"curve identification");
  require(qfbclassno(-71)==7 && kronecker(-71,q)==-1,"CM field checks");
  require(subst(polclass(-71),x,y)==prod(i=1,#cm7,y-J[cm7[i]]),"H_minus71 exact factorization");
  cmvalues=vector(#cm7,i,v[cm7[i]]);
  require(#Set(cmvalues)>1 && prod(i=1,#cm7,w[cm7[i]]==1),"nonconstant rational toric weights");
  print("PASS supersingular Brandt module: 33 vertices; dim T2=-2 is 1; CM values ",cmvalues);

  H=Polrev(readnumjson("data/H-minus44375-coeffs.json"));
  roots=readnumjson("data/CM-minus44375-lifts32.json");
  require(H==polclass(-44375),"independent PARI class polynomial");
  require(poldegree(H)==140 && pollead(H)==1 && #roots==140,"CM polynomial / root count");
  require(qfbclassno(-44375)==140 && kronecker(-71,2)==1 && kronecker(-71,5)==1,"CM splitting and class number");
  classgroup=quadclassunit(-44375);
  require(classgroup[1]==140 && classgroup[2]==[140] && classgroup[3]==[Qfb(2,1,5547)],"cyclic Pic and norm-two generator");
  exactroots=vector(#roots,i,roots[i][1]+roots[i][2]*Mod(u,u^2-2));
  D=deriv(H);
  hv=vector(#roots,i,valuation(lift(subst(H,x,exactroots[i])),q));
  dv=vector(#roots,i,valuation(lift(subst(D,x,exactroots[i])),q));
  require(prod(i=1,#roots,hv[i]>2*dv[i] && hv[i]-dv[i]>=precision_exponent),"strong Hensel certification");
  Q=q^precision_exponent;
  Jp=vector(#roots,i,Mod(lift(exactroots[i])*Mod(1,Q),u^2-2));
  require(#Set(Jp)==140,"distinct actual root balls");
  B=matrix(#roots,#roots,i,j,subst(subst(Phi,x,Jp[i]),y,Jp[j])==0);
  require(B==B~ && prod(i=1,#roots,sum(j=1,#roots,B[i,j])==2),"exactly two horizontal candidates");
  neighbors=vector(#roots,i,select(j->B[i,j],vector(#roots,j,j)));
  C=List([1,neighbors[1][1]]);
  while(#C<#roots,
    candidates=select(j->j!=C[#C-1],neighbors[C[#C]]);
    require(#candidates==1,"unique next cycle edge");
    require(!setsearch(Set(Vec(C)),candidates[1]),"no premature cycle closure");
    listput(C,candidates[1]);
  );
  require(B[C[#C],C[1]] && #Set(Vec(C))==140,"connected 140-cycle");
  Jbar=vector(#roots,i,roots[i][1]+roots[i][2]*a);
  indices=vector(#roots,i,select(j->J[j]==Jbar[i],vector(n,j,j)));
  require(prod(i=1,#roots,#indices[i]==1),"unique supersingular reduction for every lift");
  cv=vector(#roots,i,v[indices[C[i]][1]]);
  grouped=vector(p,j,sum(k=0,27,cv[j+p*k]));
  jet=vector(3,k,sum(j=0,p-1,grouped[j+1]*binomial(j,k-1))%p);
  require(grouped==[5,-1,-1,5,-8],"reconstructed Gamma1 coefficients");
  require(jet==[0,0,1],"quadratic jet");
  require(ellap(E,5)==-3,"ordinary trace");
  print("PASS CM polynomial / lifts: 140 roots; min v(H)=",vecmin(hv),"; max v(H')=",vecmax(dv));
  print("PASS CM graph: connected 140-cycle; raw Gamma1 coefficients ",grouped,"; jet mod5 ",jet);
  print("CM_INDEPENDENT_AUDIT_PASS PARI=",version());
};
main();
