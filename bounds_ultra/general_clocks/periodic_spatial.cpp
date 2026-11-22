// Does a shortest nonconstant readout cycle in a coupled width-18 host
// have a computable synchronizing west ether after the constant clock failed?
// Exact Brent cycle detection, no sampled claim when the cap is reached.
#include <cstdio>
#include <vector>
#include <cstdint>
#include <cstdlib>
#include <string>
using I=uint64_t;
struct pair {I a,b;bool operator==(const pair&)const=default;};
int main(int ac,char**av){
 std::string p=av[1],q=av[2];const int P=p.size(),L=P*q.size();if(L>60)return 2;
 I C=0,R=0;int w=0;for(char b:p)w+=b=='0';
 for(int i=0;i<q.size();i++){int k=w;for(int j=0;j<P;j++){int t=i*P+j;C|=I(p[j]-'0')<<t;if(p[j]=='0')R|=I((q[i]-'0')>>--k&1)<<t;}}
 auto s=[&](I x){return (x>>1)|((x&1)<<(L-1));};
 auto f=[&](pair a){return pair{a.b,s(a.b)^(a.a|a.b)};};
 pair start{C,s(C)^(C|R)},x=start,y=f(x);
 int u=0,d=1,k=1,i=1,cap=ac>=4?atoi(av[3]):50000000;
 while(!(x==y)&&i<cap){if(k==d){k*=2;x=y;d=0;}y=f(y);d++;i++;}
 if(!(x==y)){printf("%s:%s no spatial period certificate before %d\n",p.c_str(),q.c_str(),i);return 0;}
 x=start;y=start;for(int j=0;j<d;j++)y=f(y);while(!(x==y)){x=f(x);y=f(y);u++;}
 printf("%s:%s temporal %d spatial transient %d period %d",p.c_str(),q.c_str(),L,u,d);
 if(d>15000000){puts(" exceeds synchronizer budget");return 0;}
 std::vector<I>E(d);for(int j=0;j<d;j++){E[j]=x.b;x=f(x);}int commonK=0,maxgap=0,exactK=0;
 for(int a=0;a<L;a++){
   // A 010 target fragment followed by ANY symbol sends all four pair states into one.
   // Exact max distance to any such fragment supplies a uniform synchronization upper bound.
   int first=-1,last=-1,maxdist=0,gap=0,mg=0;
   for(int j=0;j<2*d+2;j++){int z=E[j%d]>>a&1;gap=z?0:gap+1;if(gap>mg)mg=gap;
    if(j>=2 && z==0 &&(E[(j-1)%d]>>a&1) && !(E[(j-2)%d]>>a&1)){
      if(first<0)first=j;if(last>=0&&j-last>maxdist)maxdist=j-last;last=j;
    }
   }
   if(first<0){printf(" no 010 reset at phase %d\n",a);return 0;}
   if(maxdist+4>commonK)commonK=maxdist+4;if(mg>maxgap)maxgap=mg;
   int n[4]={},v[4]={};int old=(a+L-1)%L;
   for(int j=2*d-1;j>=0;j--){int b=E[j%d]>>a&1,ref=((E[(j+d-1)%d]>>old&1)<<1)|(E[j%d]>>old&1);
    for(int st=0;st<4;st++){int f=((st&1)<<1)|(b^(st!=0));v[st]=st==ref?0:1+n[f];if(j<d&&v[st]>exactK)exactK=v[st];}
    for(int st=0;st<4;st++)n[st]=v[st];
   }
 }
 printf(" all phases reset K=%d (universal word bound %d) gap<=%d\n",exactK,commonK,maxgap);
}
