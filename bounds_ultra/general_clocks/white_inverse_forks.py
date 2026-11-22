"""Ignore decoded past centers already known black; a white q is ambiguous
iff both old final pairs 00 and 10 fit the ENTIRE current prefix. Can the
physical channel avoid every unambiguous white forever? A surviving cycle
is an explicit obstruction; nilpotence gives deterministic bounded gaps."""
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components
from spatial_certificate import trans
def run(p,n=12,r=30):
 N=1<<n;mask=N-1;P=len(p);X=np.arange(N);S=np.full(N,15)
 F=np.array([[trans(s,b,r)for b in(0,1)]for s in range(16)])
 for j in reversed(range(n)):S=F[S,(X>>j)&1]
 bad=(S&5)==5;src=[];dst=[]
 for i,c in enumerate(map(int,p)):
  for b in(0,1):
   sh=(X>>1)|(b<<(n-1));y=((2*X+c)^((X|sh)if r==30 else sh))&mask
   ok=np.ones(N,bool)if c else bad[y];src.append(i*N+X[ok]);dst.append((i+1)%P*N+y[ok])
 u,v=np.concatenate(src),np.concatenate(dst);G=coo_matrix((np.ones(len(u),np.int8),(u,v)),shape=(P*N,P*N)).tocsr();_,cc=connected_components(G,directed=True,connection='strong');core=np.unique(cc[u[cc[u]==cc[v]]])
 if len(core):
  print('ambiguous-forever possible',p,'rule',r,'Nsites',n,'temporal SCC sizes',sorted(np.bincount(cc)[core],reverse=True)[:8],flush=True)
 else:
  live=np.ones(P*N,np.int32);s=0
  while live.any():live=((G@live)>0).astype(np.int32);s+=1
  print('each',s,'physical edges includes a certified white q; clock',p,'rule',r,'Nsites',n,flush=True)
if __name__=='__main__':
 for p in('01','011','0011','00101','01011','0110000000110000001'):
  run(p);run(p,8,90)
def free(n=12,r=30):
 N=1<<n;mask=N-1;X=np.arange(N);S=np.full(N,15)
 F=np.array([[trans(s,b,r)for b in(0,1)]for s in range(16)])
 for j in reversed(range(n)):S=F[S,(X>>j)&1]
 bad=(S&5)==5;src=[];dst=[];ct=[]
 for c in(0,1):
  for b in(0,1):
   sh=(X>>1)|(b<<(n-1));y=((2*X+c)^((X|sh)if r==30 else sh))&mask;ok=np.ones(N,bool)if c else bad[y]
   src.append(X[ok]);dst.append(y[ok]);ct.append(np.full(ok.sum(),c))
 u,v,c=map(np.concatenate,(src,dst,ct));G=coo_matrix((np.ones(len(u),np.int8),(u,v)),shape=(N,N)).tocsr();_,cc=connected_components(G,directed=True,connection='strong')
 cyc=cc[u]==cc[v];D={}
 for i,j,b in zip(u[cyc],v[cyc],c[cyc]):D.setdefault(int(cc[i]),{}).setdefault(int(i),set()).add((int(j),int(b)))
 O=[]
 for Q in D.values():
  dom={b for e in Q.values()for j,b in e}
  if len(dom)==1:O.append((len(Q),'constant',str(dom)))
  elif all(len(y)==1 for y in Q.values()):
   i=next(iter(Q));w=''
   for _ in Q:
    i,b=next(iter(Q[i]));w+=str(b)
   w=min(w[j:]+w[:j]for j in range(len(w)));O.append((len(Q),'cycle',w))
  else:O.append((len(Q),'mixed branching',sum(map(len,Q.values()))))
 from collections import Counter
 print('free previous-white ambiguous r',r,'width',n,'SCC distributions',dict(Counter(O)),flush=True)
if __name__=='__main__':free();free(8,90)
