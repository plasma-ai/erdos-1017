# Exact checker: the Bernstein coefficients of the hard empty-SAT corner sector are positive.
# Exact rational replay of the certificate; not an independent implementation.

from fractions import Fraction as F
from hashlib import sha256
from math import comb
from itertools import product
n=5;zz=(0,)*n
def C(x):return {zz:F(x)} if x else {}
def V(i):a=[0]*n;a[i]=1;return {tuple(a):F(1)}
def ad(*ps):
 c={}
 for p in ps:
  for a,x in p.items():c[a]=c.get(a,F(0))+x
 return {a:x for a,x in c.items() if x}
def sc(p,x):return {a:v*x for a,v in p.items() if v*x}
def mu(p,q):
 c={}
 for a,x in p.items():
  for b,y in q.items():
   t=tuple(i+j for i,j in zip(a,b));c[t]=c.get(t,F(0))+x*y
 return {a:x for a,x in c.items() if x}
def sq(p):return mu(p,p)
def bd(p,lo,hi,deg):
 q={}
 for a,v in p.items():
  assert a[0]>=0
  for j in range(a[0]+1):
   t=(j,*a[1:]);q[t]=q.get(t,F(0))+v*comb(a[0],j)*lo**(a[0]-j)*(hi-lo)**j
 for i in range(n):
  new={}
  for a,v in q.items():
   for k in range(a[i],deg[i]+1):
    t=list(a);t[i]=k;t=tuple(t);new[t]=new.get(t,F(0))+v*F(comb(k,a[i]),comb(deg[i],a[i]))
  q={a:v for a,v in new.items() if v}
 return {a:q.get(a,F(0)) for a in product(*(range(d+1) for d in deg))}


delta,x,y,z,w=[V(i) for i in range(n)]
one=C(1);ell=ad(one,sc(delta,-1));m=ad(C(2),sc(delta,-1))
invdelta={(-1,0,0,0,0):F(1)};kk=F(37,2500)
def common(A,E,L):
 D=ad(A,E);v=ad(sc(A,3),E,C(-1));b=ad(one,sc(A,-1),sc(D,-1),sc(L,-1))
 gamma=sc(mu(delta,ad(one,sc(D,-1))),F(1,2));nu=ad(ell,gamma)
 en=ad(sc(gamma,3),sc(mu(delta,A),-1))
 N=sc(ad(nu,sc(mu(m,A),-1)),F(1,2));Bc=ad(one,sc(A,-3),b)
 K0=ad(mu(m,v),sc(D,-F(1,12)));pp=sc(ad(sc(mu(m,v),4),sc(D,8)),F(1,25))
 P0=ad(C(2*kk),sc(mu(ell,sq(v)),-2),sc(sq(D),-F(1,12)),sc(sq(K0),F(12,25)),sc(mu(pp,L),-1),sc(sq(L),-F(8,25)),sc(mu(mu(mu(delta,b),L),C(4)),-1))
 return D,v,b,gamma,en,N,Bc,P0
def q0(A,E,L,j,b,gamma):
 K=ad(mu(A,j),sc(sq(j),-F(1,2)))
 beta=ad(one,sc(delta,-2));aa=ad(mu(ell,A),sc(mu(delta,L),-1))
 dc=ad(gamma,mu(ell,ad(b,sc(A,-1))),sc(mu(delta,L),2))
 C0=ad(sc(mu(beta,sq(j)),-F(1,2)),mu(aa,j),mu(mu(A,delta),L))
 RJ=ad(mu(beta,sq(j)),mu(dc,j),sc(mu(mu(A,delta),L),-1))
 return K,beta,aa,dc,C0,RJ
def affine(P,i,lo,hi):
 ans={}
 for pw,co in P.items():
  assert pw[i]>=0
  for k in range(pw[i]+1):
   tw=list(pw);tw[i]=k;tw=tuple(tw)
   ans[tw]=ans.get(tw,F(0))+co*comb(pw[i],k)*lo**(pw[i]-k)*(hi-lo)**k
 return {pw:co for pw,co in ans.items() if co}
def report(name,P,expected_degree,expected_min):
 assert all(min(pw)>=0 for pw in P)
 deg=tuple(max(pw[i] for pw in P) for i in range(n))
 assert deg==expected_degree
 bb=bd(P,F(1,4),F(2,5),deg);values=[bb[pw] for pw in product(*(range(v+1) for v in deg))]
 assert all(v>0 for v in values) and min(values)==expected_min
 encoded=(" ".join(str(v) for v in values)+"\n").encode()
 print(name,"degree",deg,"count",len(values),"minimum",min(values))
 print(name,"coefficient_sha256",sha256(encoded).hexdigest())
 return len(values)

A=ad(C(F(7,20)),sc(x,F(1,40)));E=ad(C(F(1,20)),sc(y,F(33,500)))
D,v,b,gamma,en,N,Bc,P0=common(A,E,E)
guard=ad(sc(mu(en,ad(sc(mu(A,E),2),sc(sq(A),-1),C(F(123,1000)))),2),sc(mu(mu(A,Bc),N),-1))
total=report("DJ_GUARD",guard,(1,3,2,0,0),F(20829,5120000))

L=ad(E,sc(mu(ad(sc(A,3),C(-1)),z),F(1,2)))
D,v,b,gamma,en,N,Bc,P0=common(A,E,L)
j=ad(sc(L,2),mu(ad(v,sc(L,-1)),w));K,beta,aa,dc,C0,RJ=q0(A,E,L,j,b,gamma)
Cp=ad(aa,sc(mu(beta,j),-1));Kp=ad(A,sc(j,-1));Rp=ad(dc,sc(mu(beta,j),2));Z0=ad(gamma,mu(ell,b))
core=ad(mu(Cp,ad(C(F(123,1000)),sc(K,-1))),mu(ad(sq(A),sc(K,-1)),Rp),sc(mu(Kp,ad(C0,RJ,mu(b,Z0),sc(mu(mu(ell,invdelta),P0),-F(1,4)))),-1))
P=ad(sc(mu(en,core),2),sc(mu(mu(mu(Cp,A),Bc),N),-1))
total+=report("DUST_J_DERIVATIVE",P,(3,4,4,3,3),F(169187,192000000))

E=V(2);invE={(0,0,-1,0,0):F(1)}
L=ad(E,sc(mu(ad(sc(A,3),C(-1)),z),F(1,2)))
D,v,b,gamma,en,N,Bc,P0=common(A,E,L)
j=mu(mu(L,ad(L,E)),invE);K,beta,aa,dc,C0,RJ=q0(A,E,L,j,b,gamma)
Z0=ad(gamma,mu(ell,b))
T=ad(mu(C0,ad(C(F(123,1000)),sc(K,-1))),sc(mu(mu(K,b),Z0),-1),mu(ad(sq(A),sc(K,-1)),RJ),sc(mu(mu(mu(K,ell),invdelta),P0),F(1,4)))
P=ad(sc(mu(en,T),2),sc(mu(mu(mu(A,C0),Bc),N),-1))
P={tuple([pw[0],pw[1],pw[2]+4,pw[3],pw[4]]):co for pw,co in P.items()}
P=affine(P,2,F(1,20),F(29,250))
total+=report("DUST_J_LO",P,(3,9,9,8,0),F(262717,409600000000000))

E=ad(C(F(1,20)),sc(y,F(33,500)))
L=ad(E,sc(mu(ad(sc(A,3),C(-1)),z),F(1,2)))
D,v,b,gamma,en,N,Bc,P0=common(A,E,L);j=ad(sc(L,2),mu(ad(v,sc(L,-1)),w));CC=ad(L,E)
K=ad(mu(A,j),sc(sq(j),-F(1,2)),sc(mu(j,E),F(1,2)));ee=ad(sc(sq(j),F(1,2)),sc(mu(j,E),-F(1,2)))
Fd=ad(mu(mu(mu(delta,j),ad(j,sc(L,-2))),CC),sc(mu(mu(mu(delta,j),ad(L,sc(E,-1))),E),-1))
C0d=ad(sc(Fd,F(1,2)),sc(mu(mu(ell,ee),CC),-1),mu(mu(A,j),CC),sc(mu(mu(mu(A,delta),ad(j,sc(L,-1))),CC),-1))
ZJ=ad(gamma,mu(ell,ad(b,j)));Z0=ad(gamma,mu(ell,b))
RJd=ad(mu(ad(mu(j,ad(ZJ,sc(A,-1))),mu(mu(A,delta),ad(j,sc(L,-1)))),CC),sc(Fd,-1))
Td=ad(mu(C0d,ad(C(F(123,1000)),sc(K,-1))),sc(mu(mu(mu(K,b),Z0),CC),-1),mu(ad(sq(A),sc(K,-1)),RJd),sc(mu(mu(mu(mu(K,ell),invdelta),P0),CC),F(1,4)))
P=ad(sc(mu(en,Td),2),sc(mu(mu(mu(A,C0d),Bc),N),-1))
total+=report("Q_EQUALS_E",P,(3,6,6,5,4),F(109919,12800000000))
assert total==11104
print("ALL",total,"EXACT BERNSTEIN COEFFICIENTS POSITIVE")

