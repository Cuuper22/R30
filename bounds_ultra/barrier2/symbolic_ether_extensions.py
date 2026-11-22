"""Extend an *actual surviving host* q word after L strobes by the
period-four ether, then rewind its rational west tape. A uniform spatial
period and tail cutoff below 2L would forbid an eventually blank west
directly, not via a larger onset search. If the cutoff outruns 2L, record
the actual tail range and test the separate first discrepancy front."""
from symbolic_host_wall import sample
from symbolic_q221_lift import *
from symbolic_fork_reflector import ref
def unstep(y,s):
 a,p=y;b=0;c=s;w=[c];D={};j=0
 while True:
  if j>=len(a):
   key=((j-len(a))%len(p),b,c)
   if key in D:break
   D[key]=j
  d=(a[j] if j<len(a)else p[(j-len(a))%len(p)])^(b|c)
  w.append(d);b,c=c,d;j+=1
 start=D[key];w=w[:j];A=tuple(w[:start]);P=tuple(w[start:])
 # minimize period and move the boundary as far east (toward bit 0) as allowed
 for k in range(1,len(P)+1):
  if len(P)%k==0 and P==P[:k]*(len(P)//k):P=P[:k];break
 while A and A[-1]==P[-1]:A=A[:-1];P=P[-1:]+P[:-1]
 return A,P
def root(w):
 _,off,p,b,_=ref('','10');v=(b[:off],b[off:]);out=[]
 for j,s in enumerate(w[::-1],1):
  v=unstep(v,1-int(s));v=unstep(v,1)
  if j in(1,2,4,8,16,32,64,128,256,512):
   A,P=v;N=2*j;ww=[A[k]if k<len(A)else P[(k-len(A))%len(P)]for k in range(N)]
   out.append((N,len(A),len(P), N-max((i+1 for i,b in enumerate(ww)if b),default=0)))
  if len(v[1])>20000:break
 return out
if __name__=='__main__':
 for n,d in((25,58203),(31,315078),(39,264368)):
  W=sample(gethost(n,d),n,515,sd=200)
  print(n,d,'(physical word length, tail start, spatial period, trailing zeros to west)',root(W),flush=True)
