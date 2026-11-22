"""Test actual marked horizontal phase observability across the moving
center, not just a local transfer matrix. If matching the same center
block also allows different white q labels under period translations,
use them against right language. If never, prove the cyclic fiber is one.
"""
import numpy as np
from general_marked_fiber import child

def go():
 W=[np.array([3,1],np.uint8)]
 for k in range(17):W.append(child(W[-1])[0])
 for i,k in [(1,5),(3,8),(6,8),(9,7),(11,6)]:
    d=len(W[i]);P=len(W[i+k]);distinct={};patcnt={p:[0,0] for p in('01','011','00101')}
    for q in range(0,P,d):
        codes=[int(W[i+h][(i+h+q)%len(W[i+h])])for h in range(1,k+1)]
        s=''.join(str(b)for w in codes for b in(w&1,w>>1));assert s not in distinct;distinct[s]=q
        for pat,n in patcnt.items():
            L=min(len(s),len(pat)*2)
            if s[:L]==(pat*(L+1))[:L]:n[0]+=1
            if s==(pat*(len(s)+1))[:len(s)]:n[1]+=1
    print('marked base,subsequent layers,distinct full center blocks,phase index,counts for 2-period/full word tests',i,k,len(distinct),P//d,patcnt)
if __name__=='__main__':go()
