"""Refine 64-tick two-tail prefix groups. Keep only genuinely distinct
west marks already reached LONG before the stated horizon; test later
divergence by forward replay, never assume equality forever."""
import sys,itertools
from collections import defaultdict
def tr(s,d,K,rule):
 off=K+d+2;z=(s<<(off-d))|sum(1<<(off+i)for i in range(d+1,K+3)if not i%2)
 t=0
 for i in range(K):
  t|=(z>>off&1)<<i;z=2*z^((z|z>>1)if rule==30 else z>>1)
 return t
def edge(s,d):
 k=(s&-s).bit_length()-1-d if s else d+1+(d%2==0);return k
def go(path,d,rule):
 D=defaultdict(list)
 for l in open(path):
  a,b=l.split();D[a].append(int(b,16))
 S=list(D.values())
 for H in (128,256,501,1025):
  new=[];prev=S
  for V in S:
   T=defaultdict(list)
   for v in V:T[tr(v,d,H,rule)].append(v)
   new.extend(w for w in T.values()if len({edge(s,d)for s in w})>1)
  S=new;print(d,rule,H,len(S),sum(map(len,S)),flush=True)
  if S:
   ex=next((V for V in S if all(edge(v,d)<=0 for v in V)),S[0])
   i=ex[0];j=next(v for v in ex if edge(v,d)!=edge(i,d))
   print('example',hex(i),hex(j),edge(i,d),edge(j,d),flush=True)
  else:break
if __name__=='__main__':go(sys.argv[1],int(sys.argv[2]),int(sys.argv[3]))
