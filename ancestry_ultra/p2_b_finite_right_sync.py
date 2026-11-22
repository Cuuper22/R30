"""If all finite east perturbations leave a shared eventual q clock, the
fixed old singleton cut can use that clock directly. Compare genuine finite
tapes in the absorbing basin and test literal synchrony, not SCC reach."""
def go(N=120000):
 R=[0,1,3,11];C=1;E=[];start=0;K=[[0,None,0]for _ in R];h=[0]*len(R);m=list(K)
 for t in range(N):
  if not C:
   sig=[r&1 for r in R]
   for i,v in enumerate(sig):
    if v!=sig[0]:K[i][0]+=1;K[i][1]=t;h[i]=0
    else:h[i]+=1;K[i][2]=max(K[i][2],h[i])
  R=[(2*r+C)^(r|r>>1)for r in R];C^=1
 print('finite east against R0 through',N, 'number of white read differences, latest, longest agreement',K)
if __name__=='__main__':go()
