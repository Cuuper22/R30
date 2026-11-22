// Is absolute tip arrival from a finite tape uniformly O(width)? If
// numerics support this seek a monotone binary potential; if not, use
// the extremal initial word to explain the superlinear obstruction.
#include<cstdio>
#include<cstdlib>
#include<cstdint>
#include<vector>
int main(int ac,char**av){int N=ac>1?atoi(av[1]):23,rule=ac>2?atoi(av[2]):30;std::vector<uint16_t> d(1u<<N);
for(int n=1;n<=N;n++){unsigned lo=1u<<(n-1),hi=lo*2,best=0,br=0;
for(int g=0;g<n;g++){unsigned j=1u<<g,k=2*j,r=lo+((j-lo)%k);
for(;r<hi;r+=k){unsigned v=r>>2;d[r]=g==0?d[r>>1]:g==1?d[v]:1+d[4*v^(rule==30?(v|2*v):v)];
if(d[r]>best){best=d[r];br=r;}
}}printf("rule%d width%d maxwait %u word %x\n",rule,n,best,br);}
}
