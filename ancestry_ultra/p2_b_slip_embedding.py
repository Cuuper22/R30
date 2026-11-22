"""Is a short B-gap phase slip carried through the actual western field as
FOUR moving time deletions, even though its two outer fronts separate?
If yes a monotone winding bounds the vacuum; if not locate the first
nonembeddable temporal pair and compare one-column projections."""
def test(D=400):
 O=3*D+100;O+=(-O)%10;M=3*O;mask=(1<<M)-1;cen=sum(1<<i for i in range(0,M,2))
 def west(offset):return sum(1<<i for i in range(M)if i%2==0 or ((i-1)//2-offset)%5!=0)
 wl,wr=west(0),west(3);cut=(1<<(O+3))-1;rows=[[cen,wl],[cen,(wl&cut)|(wr&~cut)]]
 fails={};bonus=[]
 for j in range(1,D+1):
  # Use the actual right-of-splice reference for our fixed loss of four ticks.
  l,h=rows;lo=O-j-12;hi=O+18
  vals={}
  for k in (1,2,3):
   obs=lambda z,t:((z[0]>>t&1)if k&1 else 0)+((z[1]>>t&1)*2 if k&2 else 0)
   n=lo
   wrong=None
   for t in range(lo,hi):
    v=obs(h,t);z=n
    while n<z+10 and obs(l,n)!=v:n+=1
    if n==z+10:wrong=(t-O,'symbol absent',v);break
    n+=1
    if n-t-1>4 and wrong is None:wrong=(t-O,'extra skip',n-t-1)
   vals[k]=n-hi
   if wrong is not None and k not in fails:fails[k]=(j,wrong)
  if j in (4,10,25,50,100,200,D):bonus.append((j,vals.copy()))
  for z in rows:z[:]=[z[1],((z[1]>>1)^(z[0]|z[1]))&mask]
 print('first failure of four conserved deletions for first/second/joint traces',fails,'greedy overshoots (if target stays in alphabet)',bonus,flush=True)
if __name__=='__main__':test()
