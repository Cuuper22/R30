"""At a fixed east site, prove a compulsory genuine ambiguity event
under *any* periodic center unless the actual band becomes periodic.
Measure the exact forced-corridor bound at d=1 on 01,011,00101 and R90;
if finite use it for the next transverse propagation, not an onset scan."""
from general_mixed_return_certificate import step,D,S as cert
from general_characteristic_d4 import field

def observer(r):
 U=(1<<64)-1; O=sum(1<<k for k in range(1,64,2))
 A=[[(1<<step(x,c,0,r))|(1<<step(x,c,1,r)) for x in range(64)]for c in range(2)]
 cache=[]
 for c in range(2):
  T=[]
  for j in range(8):
   z=[0]
   for k in range(1,256):
    p=k&-k;z.append(z[k-p]|A[c][8*j+p.bit_length()-1])
   T.append(z)
  cache.append(T)
 def nxt(y,c): 
  o=0
  for x,tab in zip(y.to_bytes(8,'little'),cache[c]):o|=tab[x]
  return o
 Q=[U];ID={U:0};success=[];out=[]
 for s in Q:
  ee=[]
  for c in (0,1):
   u=nxt(s,c)
   if not u in ID:ID[u]=len(Q);Q.append(u)
   ee.append(ID[u])
  success.append(ee);out.append(2 if s&O and s&(U^O) else int(bool(s&O)))
 return Q,success,out

def sheet(p,W):
 Q,A,Z=W;P=len(p);D={};E={}
 for j in range(P):
  for k in range(len(Q)):
   for v in range(2):
    x=j,k,v;q=Z[k]
    if v==0 and q==2:E[x]=None
    else:E[x]=((j+1)%P,A[k][v],int(p[j])^(v|q if not v else 1))
 for x in E:
  s=x;seen={};path=[]
  while s is not None and s not in D and s not in seen:
   seen[s]=len(path);path.append(s);s=E[s]
  if s in seen:
   for j in range(seen[s],len(path)):D[path[j]]=-1
   path=path[:seen[s]];a=-1
  else:a=-1 if s is not None and D[s]<0 else D[s] if s is not None else -1
  for y in reversed(path):
   if s is None or a>=0:a+=1
   D[y]=a
 return D
def main():
 for r in (30,90):
  W=observer(r);print('rule, unrestricted six-state-subset orbit',r,len(W[0]))
  for p in ('01','011','00101',D[0]+D[1]):
   dist=sheet(p,W);print('rule,w,max finite guaranteed ticks until ambiguity, states reaching infinite deterministic band',r,p,max(dist.values()),sum(v==-1 for v in dist.values()))
   if r==30:
    at=field(30,None,500);subset=0;same=0;partial=0
    for t in range(500):
     c=at(t,1)
     if c==0 and W[2][subset]<2:assert W[2][subset]==at(t,2);same+=1
     subset=W[1][subset][c]
    print('true R30 controlled-site singleton 500-tick determinate whites',same)
   else:
    at=field(90,p,500);assert all(at(t,0)==int(p[(t-1)%len(p)])for t in range(1,501))
    # R90 with free seventh site always preserves full ambiguity.
    assert W[2]==[2]
if __name__=='__main__':main()
