"""Turn whole-ray candidates into genuine paired full-space unforced initial
rows. Require a long common true marked western rim and identical entire
finite landing, but unequal earlier q under the same mixed clock. This tests
whether a terminal reset plus the outer mark can by themselves preclude the
fork. A surviving pair requires the exact interior singleton ancestor instead.
"""
from infinite_east_fibers import pairs,bit,F,finite,history
def lowwest(C,H,r):
 B=list(C);A=list(H);v=0
 for i in range(len(H)):
  v|=A[0]<<i
  B,A=A,[A[t+1]^((B[t]|A[t])if r==30 else B[t])for t in range(len(A)-1)]
 return v
def actualW(A,r):
 z=1
 for _ in range(A):z=4*z^((2*z|z)if r==30 else z)
 return int(format(z&((1<<A)-1),f'0{A}b')[::-1],2)
def pastwest(W,y,c,e,r):
 h=y^((c|e)if r==30 else e);x=h
 a=c;b=h
 for j in range(W.bit_length()+4):
  v=(W>>j&1)^((a|b)if r==30 else a);x|=v<<(j+1);a,b=b,v
 return x if not(a|b) else None
def sim(W,c,E,r,n):
 out=[];R=[]
 for _ in range(n):
  e=bit(E);out.append((c,e if not c else 0));R.append(E)
  W,c,E=(W>>1)^((W|(2*W+c))if r==30 else 2*W+c),(W&1)^((c|e)if r==30 else e),F(E,r,c)
 return W,c,E,out,R
def bits(B):return ''.join(map(str,B))
def go(p,r=30,k=20,t=20,A=400):
 C,R=history(r,p,t);s=t-k
 H=[C[i+1]^((C[i]|(R[i]&1))if r==30 else (R[i]&1)) for i in range(s,t)]
 w=lowwest(C[s:t+1],H,r)|(actualW(A,r)>>k<<k);e=finite(R[s])
 w1,c1,e1,q,h=sim(w,C[s],e,r,k)
 assert c1==C[t] and e1==finite(R[t]) and [z[0]for z in q]==C[s:t]
 V=[(w1,e1,0)]
 for j in range(t-1,s-1,-1):
  U=[]
  for oldW,oldE,d in V:
   for X in pairs(oldE,r,C[j]):
    W=pastwest(oldW,C[j+1],C[j],bit(X),r)
    if W is None or W.bit_length()!=A+j-s:continue
    nd=2*d+int(not C[j] and bit(X)!=R[j]&1)
    U.append((W,X,nd))
  V=U
  if r==90 and len(V)>600: # trim to at least one partial fork plus actual whenever present
   V=sorted(V,key=lambda a:(a[2]==0,a[1][0],a[1][1]))[:600]+[x for x in V if x[1]==finite(R[j])]
 V=[x for x in V if x[2]]
 if not V:
  print('no fork',p,r,'K',k,flush=True);return
 a,b,fork=max(V,key=lambda v:(A-(v[0]^w).bit_length(),-len(v[1][1])))
 z,c,Z,out,other=sim(a,C[s],b,r,k)
 assert z==w1 and c==c1 and Z==e1 and q!=out and [x for x,y in out]==C[s:t]
 first=next((i for i,(x,y)in enumerate(zip(h,other)) if x==y),k)
 assert a.bit_length()==A==w.bit_length()
 print('clock',p,'r',r,'K',k,'same entire true outer left bits at start',A-(a^w).bit_length(),
       'differing white times',[i for i,(X,Y)in enumerate(zip(q,out)) if X!=Y],
       'strict east merges by relative time',first,'full common terminal C/W/E',c1,hex(w1),hex(R[t]),
       'seed1 C/W/finite E',C[s],hex(w),hex(R[s]),'seed2 C/W/east prefix+period',C[s],hex(a),bits(b[0])or '-',bits(b[1]),flush=True)
if __name__=='__main__':
 for p in('01','011','0011','00101'):
  go(p)
  # Same genuine normalization, shorter depth suffices for a Rule90 control.
  go(p,90,k=5,t=5)
