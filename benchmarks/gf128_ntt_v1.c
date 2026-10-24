#include <stdint.h>
#include <stdio.h>
#include <time.h>
#include <stdlib.h>

typedef struct { uint64_t lo, hi; } u128;
static u128 gf128_mul(u128 a, u128 b) { u128 x=a, y=b, out={0,0}; for (unsigned i=0;i<128;++i) { uint64_t mask=0-(y.lo&1), carry=x.hi>>63; out.lo^=x.lo&mask; out.hi^=x.hi&mask; x=(u128){(x.lo<<1)^(0x87& (0-carry)),(x.hi<<1)|(x.lo>>63)}; y=(u128){(y.lo>>1)|(y.hi<<63),y.hi>>1}; } return out; }
static u128 mix128(u128 v, unsigned rounds) { for (unsigned i=0; i<rounds; ++i) { u128 k = {(uint64_t)i * 0x9e3779b97f4a7c15ULL ^ 0x0123456789abcdefULL, (uint64_t)i * 0xd1b54a32d192ed03ULL ^ 0xfedcba9876543210ULL}; v = gf128_mul((u128){v.lo ^ k.lo, v.hi ^ k.hi}, (u128){0x1f1e1d1c1b1a1918ULL, 0x1716151413121110ULL}); } return v; }
static uint64_t mod_mul(uint64_t a, uint64_t b) { return (a*b) % 998244353ULL; }
static uint64_t mod_pow(uint64_t a, uint64_t e) { uint64_t r=1; while(e) { if(e&1) r=mod_mul(r,a); a=mod_mul(a,a); e>>=1; } return r; }
__attribute__((noinline)) static uint64_t run_gf128(uint64_t rounds) { u128 v=mix128((u128){0x0123456789abcdefULL,0xfedcba9876543210ULL},(unsigned)rounds); return v.lo ^ v.hi * 0x9e3779b97f4a7c15ULL; }
__attribute__((noinline)) static uint64_t run_ntt(uint64_t rounds) { uint64_t total=0, a[256]; for(unsigned r=0;r<rounds;++r) { for(unsigned i=0;i<256;++i) a[i]=(i*17+r*13+7)%998244353ULL; for(unsigned i=0;i<256;++i) { unsigned rev=0; for(unsigned b=0;b<8;++b) if((i>>b)&1) rev|=1u<<(7-b); if(i<rev){uint64_t t=a[i];a[i]=a[rev];a[rev]=t;} } for(unsigned len=2;len<=256;len<<=1) { uint64_t wlen=mod_pow(3,(998244353ULL-1)/len); for(unsigned base=0;base<256;base+=len) { uint64_t w=1; for(unsigned i=0;i<len/2;++i){uint64_t u=a[base+i],v=mod_mul(a[base+i+len/2],w),s=u+v; a[base+i]=s>=998244353ULL?s-998244353ULL:s; a[base+i+len/2]=u>=v?u-v:u+998244353ULL-v; w=mod_mul(w,wlen);} } } total += a[0]+a[127]; } return total; }
static uint64_t nanos(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return (uint64_t)t.tv_sec*1000000000ULL+t.tv_nsec; }
int main(void) { volatile uint64_t z=0, sink=0; sink^=run_gf128(4096+z)^run_ntt(64+z); uint64_t t=nanos(), g=run_gf128(4096+z); uint64_t tg=nanos()-t; sink^=g; t=nanos(); uint64_t n=run_ntt(64+z); uint64_t tn=nanos()-t; sink^=n; printf("BENCH:gf128_scalar:checksum=%llu:time_ns=%llu\n",(unsigned long long)g,(unsigned long long)tg); printf("BENCH:ntt_modular:checksum=%llu:time_ns=%llu\n",(unsigned long long)n,(unsigned long long)tn); return (int)(sink==1); }
