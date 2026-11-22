"""Use the marked southwest boundary itself as an exact finite-state
D4 reader of the two-spacetime-diagonal word at a P2 strobe.
Antipodal entering states cannot both pass a black strobe on a common
old suffix; test the whole-marked-word reader on the real fields."""
def physical(rule=30,N=500):
 O=N+8
 z=1<<O if rule==30 else ((1<<O)|sum(1<<(O+j)for j in range(1,2*N+3)if j%6 in(2,4)))
 rr=[]
 for n in range(N+1):
  rr.append(z);z=(2*z)^((z|z>>1)if rule==30 else z>>1)
 return lambda n,x:(rr[n]>>(O+x))&1
def scan(w,state=0,bprev=0):
 out=[];z=state
 for d in w:
  a=d&1;b=d>>1;k=bprev|a
  s=1 if k^b else -1
  c=3 if k else 2*b
  z=(s*z+c)&3;bprev=b;out.append(z)
 return out
def run():
 for rule in (30,90):
  at=physical(rule);ok=bad=good=0;sample=[]
  # First old row index i≥0; include all normalized j≥0.
  for i in range(1,249):
   a=[at(i+j,j-i)+2*at(i+j+1,j-i)for j in range(i+1)]
   b=[at(i+1+j,j-i-1)+2*at(i+j+2,j-i-1)for j in range(i+1)]
   z=scan(a);ok+=z==b;bad+=z!=b
   if z!=b and len(sample)<4:sample.append((i,z[-1],b[-1]))
   if rule==30:
    assert scan(a,2)==[x^2 for x in z]
    if a[-1]==1 and at(2*i+2,0) and not at(2*i+3,0):
     # true black-to-black strobe with two successive P2 pairs
     q=at(2*i+1,1)
     assert z[-1]==3-q;good+=1
  if rule==30:assert not bad
  else:assert all(at(t,0)==1-(t&1)for t in range(501))and bad
  print(rule,'exact full marked characteristic word transfers,failures,terminal P2 q reads',ok,bad,good,'first mismatch endpoint examples',sample)
if __name__=='__main__':run()
