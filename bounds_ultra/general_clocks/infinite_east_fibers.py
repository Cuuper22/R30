"""Exact genuine infinite-east competitors at a finite landing with a fixed
past center. Compare actual merged full eastern rays, not a refreshed finite
strip. If a different white history survives, report the earliest full lift;
if none does, distinguish center-forced uniqueness from an enumeration cap.
Spatial right tails are periodic products of the four-state inverse maps.
"""
from functools import lru_cache
def f(h,z,r):return ((h&1)<<1)|(z^(((h>>1)|(h&1)) if r==30 else h>>1))
def canon(B,S):
 n=len(S)
 for d in range(1,n+1):
  if n%d==0 and S==S[:d]*(n//d):break
 S=S[:d]
 while B and B[-1]==S[-1]:B=B[:-1];S=S[-1:]+S[:-1]
 return tuple(B),tuple(S)
def finite(x):return tuple((x>>j)&1 for j in range(x.bit_length())),(0,)
def pairs(Y,r,c):
 B,S=Y;g=[]
 for h in range(4):
  z=h
  for b in S[::-1]:z=f(z,b,r)
  g.append(z)
 for h in range(4):
  z=g[h];m=1
  while m<5 and z!=h:z=g[z];m+=1
  if z!=h:continue
  sx=S*m;bits=[];z=h
  for b in sx[::-1]:
   bits.append(z&1);z=f(z,b,r)
  assert z==h
  S1=tuple(reversed(bits));bs=[]
  for b in B[::-1]:bs.append(z&1);z=f(z,b,r)
  if z&1!=c:continue
  B1=tuple(reversed(bs))
  yield canon(B1,S1)
def bit(Y,n=0):
 B,S=Y;return B[n]if n<len(B) else S[(n-len(B))%len(S)]
def F(Y,r,c):
 B,S=Y;x=[c]+[bit(Y,j) for j in range(len(B)+len(S)+2)]
 v=[x[i]^((x[i+1]|x[i+2])if r==30 else x[i+2]) for i in range(len(x)-2)]
 return canon(tuple(v[:len(B)+1]),tuple(v[len(B)+1:]))
def history(r,p,N):
 z=1;e=1;C=[];R=[]
 for t in range(N+1):
  c=z>>t&1 if p is None else int(p[t%len(p)]);a=z>>(t+1)if p is None else e;C.append(c);R.append(a)
  z=4*z^((2*z|z)if r==30 else z)
  e=(2*e+c)^((e|(e>>1))if r==30 else e>>1)
 return C,R
def find(r,p,ages,K,cap=3000,stcap=12000):
 C,R=history(r,p,max(ages));outs=[]
 for t in ages:
  states={(finite(R[t]),0)};first=None;last=[];miss=False
  for k in range(1,min(t,K)+1):
   c=C[t-k]
   if sum(len(S) for (_,S),_ in states)>stcap or len(states)>cap:break
   ns=set()
   for Y,w in states:
    for V in pairs(Y,r,c):
     # White reads stored chronologically low first into the increasingly old past.
     flag=(not c) and bit(V)!=bool(R[t-k]&1)
     code=(w<<1)|int(flag)
     ns.add((V,code))
   states=ns
   assert any(y==finite(R[t-k]) and not w for y,w in states)
   if first is None and any(w for _,w in states):first=k
   if states:last.append((k,len(states),sum(bool(w) for _,w in states),max(len(y[1])for y,w in states)))
  outs.append((t,first,last[-1] if last else None))
 print('true infinite east fibers, rule/clock, (landing age,first backward depth permitting earlier q fork, deepest reconstructed depth/#rays with histories/#forked/righthand maximal periodic tail)',r,p or 'singleton',outs,flush=True)
if __name__=='__main__':
 for p in(None,'01','011','0011','00101'):
  for r in(30,90):find(r,p,[20,60,120,250,500],20)
