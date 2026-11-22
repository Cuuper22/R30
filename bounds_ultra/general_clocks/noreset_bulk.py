"""If the marked inverse run has few resets, its long spatial pieces avoid all
four-pair synchronizers. Is there actual spacetime with no synchronizer on
several neighboring rows and arbitrary spatial data? Build the exact stack of
sofic observers, scan each true finite cone, and classify spatial recurrent components.
A zero-entropy stack forces periodic islands or interfaces. Positive entropy
requires identifying which extra actual marked boundary property removes it."""
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components
import numpy as np
from spatial_certificate import trans
def stack(H,rule,cap=400000):
 # Right-to-left ages 0..H-1. v is the next westmost symbol on this age;
 # buffer old lowbit is the nearest of its two earlier symbols.
 F=[[trans(s,b,rule) for b in(0,1)] for s in range(16)]
 st=[((15,)*H,(-1,)*(H-1))];ids={st[0]:0};E=[];full=[]
 for i,(s,z)in enumerate(st):
  full.append(all(d>=0 and d<4 for d in z));es=[]
  for x in(0,1):
   ss=[];zz=[];v=x;ok=True
   for k in range(H):
    if v>=0:
     sk=F[s[k]][v]
     if sk.bit_count()==1:ok=False;break
    else:sk=s[k]
    ss.append(sk)
    if k==H-1:break
    d=z[k]
    if v<0:zz.append(d);continue
    if d==-1:zz.append(4+v);v=-1
    elif d>=4:zz.append(v+2*(d-4));v=-1
    else:zz.append(v+2*(d&1));v^=(int(d!=0)if rule==30 else (d>>1))
   if not ok:es.append(-1);continue
   u=tuple(ss),tuple(zz);j=ids.get(u)
   if j is None:
    j=len(st);ids[u]=j;st.append(u)
    if j>cap:return print('stack H',H,'r',rule,'exceeded',cap,flush=True)
   es.append(j)
  E.append(es)
 u,v=zip(*[(i,j) for i,a in enumerate(E) for j in a if j>=0]);G=coo_matrix((np.ones(len(u)),(u,v)),shape=(len(st),len(st))).tocsr()
 _,cc=connected_components(G,directed=True,connection='strong');D={}
 for i,a in enumerate(E):
  same=sum(j>=0 and cc[j]==cc[i] for j in a)
  if same:D.setdefault(cc[i],[0,0,[]]);D[cc[i]][0]+=1;D[cc[i]][1]+=same;D[cc[i]][2].append(i)
 def cyc(k):
  V=D[k][2];i=V[0];w=[]
  for _ in V:
   b,j=next((b,j)for b,j in enumerate(E[i])if j>=0 and cc[j]==k);i=j;w.append(b)
  bits=''.join(map(str,w));return min(bits[j:]+bits[:j]for j in range(len(w)))if len(w)<200 else str(len(w))
 cycles=sorted(set(cyc(k) for k,(n,m,V)in D.items()if n==m));branches=sorted([(n,m)for n,m,V in D.values()if m>n],reverse=True)
 print('stack H',H,'r',rule,'states',len(E),'recurrent SCCs',len(D),'branching',branches[:4],'pure cycles',cycles[:20],flush=True)
 return st,E,D,cc
if __name__=='__main__':
 for h in range(1,10):stack(h,30)
 for h in range(1,5):stack(h,90)
