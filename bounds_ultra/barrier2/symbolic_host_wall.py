"""Test whether the actual eventual channel grammar, rather than arbitrary 3/5 gaps, forces another periodic wall or a wall that admits excision with finite-state correction. A forced translated P2 wall would descend finite marked west; absence selects genuinely two-sided source transport."""
from symbolic_q221_lift import *
from random import Random
def sample(S,n,N,sd=9):
 a,b,h=edges(S,n); G,C,sz=cc(a,b,len(S));rng=Random(sd);v=rng.randrange(len(S));Q=[]
 for i in range(N):
  Q.append(int(S[v])&1);s=G.indices[G.indptr[v]:G.indptr[v+1]];v=int(s[rng.randrange(len(s))])
 return Q
def cols(q,K=2000,T=400):
 n=2*len(q); C=sum((1-i%2)<<i for i in range(n));E=sum(x<<(2*i+1)for i,x in enumerate(q));M=(1<<T)-1;even=sum(1<<(2*i)for i in range(T//2));odd=M^even
 D=[];W=C;R=E
 for k in range(1,K+1):
  L=(W>>1)^(W|R);S=L&M;F=[]
  for j,P in enumerate((even,odd)):
   if not(S&P): F.append('%s=0'%j)
   if(S&P)==P:F.append('%s=1'%j)
  if F:D.append((k,F))
  W,R=L,W
 return D
if __name__=='__main__':
 for n,s in [(25,58203),(25,24899),(34,82754),(25,221)]:
  S=gethost(n,s);Q=sample(S,n,1700);D=cols(Q);print(n,s,'white q head',''.join(map(str,Q[:100])),'wall phase pins',D[:45],'count',len(D),flush=True)
