"""Can arbitrarily long defect-free 5-gap stretches in the initialized
absorbing right basin have even a full physical infinite extension? Lift
ONLY pure5 recurrent temporal cycles. Emptiness would force positive
short-gap density on true runs; surviving a spatially periodic reference
would explicitly disprove that mechanism."""
from p2_b_recur_host import edges,cc,np
def run(S,n,cap):
 # same q5 cycle up to phase; restricting white q at all steps.
 N=len(S);a,b,h=edges(S,n);A=[];B=[]
 for p in range(5):
  m=(S[a]&1)==(p==0);A.append(a[m]+p*N);B.append(b[m]+((p+1)%5)*N)
 A,B=np.concatenate(A),np.concatenate(B);_,C,sz=cc(A,B,5*N);U=[]
 for g in np.flatnonzero(sz>1):
  V=np.flatnonzero(C==g);U.append(set((int(i)//N,int(S[int(i)%N]))for i in V))
 print('width',n,'pure5 physical cyclic hosts',list(map(len,U)),flush=True);return U
def lift(U,n):
 V=sorted((p,w+(b<<(n-1)))for p,w in U for b in (0,1));I={a:i for i,a in enumerate(V)};A=[];D=[];m=(1<<n)-1
 for i,(p,w)in enumerate(V):
  if w&1!=(p==0):continue
  for b in (0,1):
   x=(2*w^(w|w>>1|b<<(n-1)))&m
   for k in (0,1):
    u=((2*x+1)^(x|x>>1|k<<(n-1)))&m;j=I.get(((p+1)%5,u))
    if j is not None:A.append(i);D.append(j)
 G,C,sz=cc(np.array(A),np.array(D),len(V));out=[]
 for g in np.flatnonzero(sz>1):
  q=np.flatnonzero(C==g);out.append({V[int(i)]for i in q})
 return out
if __name__=='__main__':
 U=run(np.load('/tmp/r30a_bhost_25_58203.npy'),25,None)
 for n in range(26,61):
  U=[q for s in U for q in lift(s,n)]
  for w in U:
   if len(w)<200:
    m=(1<<n)-1;ex=0
    for p,a in w:
     for b in (0,1):
      x=(2*a^(a|a>>1|b<<(n-1)))&m
      for k in (0,1):
       y=((2*x+1)^(x|x>>1|k<<(n-1)))&m
       if ((p+1)%5,y)not in w:ex+=1
    print('small',n,len(w),'actual exits',ex,'word',min(w),flush=True)
  print('width',n,'surviving isolated pure5 host sizes',list(map(len,U)),flush=True)
  if not U or sum(map(len,U))>75000:break
