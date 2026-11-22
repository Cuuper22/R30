// Which individual black P2 arrivals can transmit an increasing jump
// in exact finite-tape right-tip labels? Distinguish the genuinely reachable
// east rows by complete initialized central two-step evolution, not an
// independent choice of evolved R'. A uniformly bounded type can be
// deleted from the obligatory unbounded-jump support; otherwise examine
// the first growing suffix.
#include<cstdio>
#include<cstdlib>
#include<cstdint>
#include<vector>
#include<array>
unsigned st(unsigned r,int c){return (2*r+c)^(r|(r>>1));}
int main(int ac,char**av){int N=ac>1?atoi(av[1]):24,rule=30;std::vector<uint16_t>d(1u<<(N+2));
for(int n=1;n<=N+2;n++){unsigned lo=1u<<(n-1),hi=lo*2;
for(int g=0;g<n;g++){unsigned j=1u<<g,k=2*j;for(unsigned r=lo+((j-lo)%k);r<hi;r+=k){unsigned v=r>>2;d[r]=g==0?d[r>>1]:g==1?d[v]:1+d[4*v^(v|2*v)];}}}
for(int n=6;n<=N;n+=2){std::array<unsigned,32> A{},E{};for(unsigned r=0;r<(1u<<n);r++){unsigned q=st(r,1),y=st(q,0);int z=2+d[y]-d[r];if(z<0)abort();auto j=r&31;if(unsigned(z)>A[j]){A[j]=z;E[j]=r;}}
printf("initial width %d: exact max jump by black east low5",n);
for(unsigned i=0;i<32;i++)printf(" %u",A[i]);printf("\n");if(n==N){printf("witnesses:");for(auto e:E)printf(" %x",e);puts("");}}
}
