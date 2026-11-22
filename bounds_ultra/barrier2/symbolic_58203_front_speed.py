"""Bound growth of the largest genuine inverse discrepancy on the fixed
155-cell pure-five ether, for any past q boundary. With finite marked
west at EVERY earlier cut this yields a uniform multiplicative ceiling
on the lengths/spacing of pure-five blocks. A superunit cycle gives
the exact loss preventing this bound from itself settling all schedules."""
from symbolic_58203_integer_cocycle import E,p
import numpy as np
from fractions import Fraction
from math import gcd,ceil
def edges():
 # Translate k+2 back to k by spatial shift 31, reducing to 310 vertices.
 A=[];B=[];w=[]
 for k in range(2):
  for m in range(p):
   for state in range(4):
    u=state>>1;v=state&1;M=None
    for j,z in ((m-1,u),(m,v)):
     if z!=E[k-1][j%p]:M=j
    j=m
    while True:
     b=E[k][j%p]^(j==m)^(u|v);u,v=v,b;j+=1
     if b!=E[k-1][j%p]:M=j
     if (u,v)==(E[k-1][(j-1)%p],E[k-1][j%p]):break
     assert j<m+40
    assert M is not None
    oldk=(k-1)%2
    # k=0 rewind goes to reference phase 9 = phase1 advanced by 124 = -31.
    A.append(k*p+m);B.append(oldk*p+(M+(-31 if k==0 else 0))%p);w.append(M-m)
 return np.array(A),np.array(B),np.array(w)
def go():
 A,B,V=edges();n=2*p;D=np.zeros((n+1,n),np.int64)
 for j in range(1,n+1):
  D[j].fill(-10**9);np.maximum.at(D[j],B,D[j-1,A]+V)
 c=max(min(Fraction(int(D[n,i]-D[j,i]),n-j)for j in range(n))for i in range(n))
 # Integral max-plus potential supplies a separately checkable certificate
 # V <= c + (pot[dst]−pot[src])/den on every explicitly generated edge.
 d=c.denominator;v=c.numerator
 P=np.zeros(n,np.int64)
 for _ in range(n):np.maximum.at(P,B,P[A]+d*V-v)
 assert np.all(d*V<=v+P[B]-P[A])
 print('max one-step growth',max(V),'certified worst mean speed',c,'potential spread',int(max(P)-min(P)),'denominator',d)
 H=ceil(Fraction(int(max(P)-min(P)),d))+30
 print('last discrepancy after s ticks <= C*s + K',c,H,'pure-five future length/age asymptotic upper',(c-1)/(c+1),'successive short-age ratio upper',2*c/(c+1),flush=True)
 return c,H
if __name__=='__main__':go()
