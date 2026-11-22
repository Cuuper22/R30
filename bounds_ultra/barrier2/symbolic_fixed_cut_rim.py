"""Use the fixed-old Baire cut without assuming its deep left lanes are
mature: compare the newer RIGHT rim to the whole finite old marked row.
Power-of-two returns locate the exact first break between the old center
and its translated spatial copy. If this alone also holds for R90, it is
a genuine origin coupling but requires the host-OR gate for discrimination."""
def G(z,r):return z^(2*(z|2*z)if r==30 else 4*z)
def vf(x):return (x&-x).bit_length()-1
def run(rule,N=500):
 A=[1]
 for _ in range(N):A.append(G(A[-1],rule))
 pos=[]
 for n in range(9):
  p=1<<n;d=vf(A[p]^1);ct=0;copies=0
  for Q in range(p,N+1,2*p):
   for u in range(0,min(45,N-Q)+1):
    assert vf(A[u]^A[Q+u])==d
    if d>2*u:
     assert A[Q+u]%(1<<d)==A[u];copies+=1
    ct+=1
   if d+Q<=N:
    for t in range(d+1):
     a=A[t]>>t&1;b=A[Q+t]>>t&1
     assert(a==b)==(t<d)
  pos.append((p,d,ct,copies))
 print('rule',rule,'lag power, first different right depth, checked paired ages, copies incl older full row',pos,flush=True)
if __name__=='__main__':run(30);run(90)
