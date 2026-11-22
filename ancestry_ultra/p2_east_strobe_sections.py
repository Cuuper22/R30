"""Replace the strong every-tick section equality of the stripe
normal form by exact net group action between physical H strobes.
Distinct per-tick cap actions could cancel in pairs or longer macros;
a strict extra identification would permit deleting irreducible tips."""
from collections import deque
import numpy as np
# A=00, B=*1, C=10. Output bit toggles exactly in B,C.
def act(q,b):return b^(q!=0),(1 if b else 2 if q==1 else 0)
def transit(word,b):
 w=[]
 for q in word:
  b,s=act(q,b);w.append(s)
 return b,tuple(w)
def eq(u,v):
 todo=[(tuple(u),tuple(v))];seen=set(todo)
 for x,y in todo:
  if x==y:continue
  for b in(0,1):
   a,p=transit(x,b);c,q=transit(y,b)
   if a!=c:return False
   if (p,q)not in seen:seen.add((p,q));todo.append((p,q))
 return True
def scan(n,h):
 S=np.arange(1<<n);G=(S^(2*S|4*S))%2**n
 u=S>>(n-1);v=S>>(n-2)&1;state=np.where(u,1,2*v)
 p=S.copy();codes=np.zeros(len(S),int)
 for i in range(h):codes=codes*3+state[p];p=G[p]
 U=np.unique(codes)
 def word(v):return tuple((v//3**j)%3 for j in range(h-1,-1,-1))
 # Most pairs are separated by images of one small fixed all-zero body;
 # group equalities within remaining buckets are proved by finite bisimulation.
 H={};ids={};nx=0
 for k in U:
  w=word(int(k));bits=[]
  for seed in(0,1,3,13):
   z=seed
   for q in w:
    z=(z^((2*z+(q==1))|(4*z+2*(q==1)+(q!=0)) )) &65535
   bits.append(z)
  b=tuple(bits);V=H.setdefault(b,[])
  for w0,cl in V:
   if eq(w,w0):ids[int(k)]=cl;break
  else:ids[int(k)]=nx;V.append((w,nx));nx+=1
 ix=np.array([ids[int(k)]for k in codes]);c=ix
 for _ in range(n+1):
  K=len(np.unique(c));nw=np.unique(c*(int(c.max())+1)+c[p],return_inverse=True)[1];p=p[p]
  if int(nw.max())+1==K:c=nw;break
  c=nw
 even=np.zeros(int(c.max())+1,bool);even[c[::2]]=1
 non=np.flatnonzero(even[c[1::2]])*2+1
 ir=non[(non%8==1)|(non%8==7)]
 print(n,h,'different period-h contents/actual group actions',len(U),nx,'irreducible erasures',len(ir),'examples',list(map(hex,ir[:8])),flush=True)
if __name__=='__main__':
 for t in(2,4,6,7,8,10,14):scan(12,t)
