"""Test near-squares on the true finite-eastern forcing, not a path
assembled from finite automaton loops. If one prefix reproduces to its
lag repeatedly, target its physical origin; if returns stay short,
derive a quantitative decoder deficit from the actual clamped tape."""
from p2_b_dyadic_replica import run
def qword(w,N):
 a=[]
 for i in range(N):
  w=(2*w+1)^(w|w>>1);a.append(w&1)
  w=2*w^(w|w>>1)
 return bytes(a)
def Z(a):
 n=len(a);z=[0]*n;l=r=0
 for i in range(1,n):
  if i<r:z[i]=min(r-i,z[i-l])
  while i+z[i]<n and a[z[i]]==a[i+z[i]]:z[i]+=1
  if i+z[i]>r:l,r=i,i+z[i]
 return z
def go(N=65536):
 for w in(1,3):
  s=qword(w,N)
  for t in(9,37,1024,3367,8192):
   z=Z(s[t:]);p=[]
   for r in(6,8,10,12,14):
    i=max(range(1<<r,1<<(r+1)),key=z.__getitem__)
    p.append((i,z[i]))
   print('finite east,old absolute strobe; dyadic bands best (strobe lag,LCP)',w,t,p)
 run()
if __name__=='__main__':go()
