#include "memory-contracts.h"

void *memcpy(void *dst, const void *src, size_t n) {
    unsigned char *d = dst;
    const unsigned char *s = src;
    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer k; 0 <= k < i ==> d[k] == \at(((const unsigned char*)src)[k],Pre);
      loop assigns i, d[0 .. n-1];
      loop variant n-i;
    */
    for (size_t i = 0; i < n; ++i) d[i] = s[i];
    return dst;
}

void *memmove(void *dst, const void *src, size_t n) {
    unsigned char *d = dst;
    const unsigned char *s = src;
    /* wasm32 addresses: compare integers, not unrelated C pointers. */
    if ((size_t)d < (size_t)s) {
        /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer k; 0 <= k < i ==> d[k] == \at(((const unsigned char*)src)[k],Pre);
      loop assigns i, d[0 .. n-1];
      loop variant n-i;
    */
    for (size_t i = 0; i < n; ++i) d[i] = s[i];
    } else {
        /*@
          loop invariant 0 <= n <= \at(n,Pre);
          loop invariant \forall integer k; 0 <= k < \at(n,Pre) ==>
            s[k] == \at(((const unsigned char*)src)[k],Pre);
          loop invariant \forall integer k; n <= k < \at(n,Pre) ==>
            d[k] == \at(((const unsigned char*)src)[k],Pre);
          loop assigns n, d[0 .. \at(n,Pre)-1];
          loop variant n;
        */
        while (n != 0) { --n; d[n] = s[n]; }
    }
    return dst;
}

void *memset(void *dst, int byte, size_t n) {
    unsigned char *d = dst;
    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer k; 0 <= k < i ==> d[k] == (unsigned char)byte;
      loop assigns i, d[0 .. n-1];
      loop variant n-i;
    */
    for (size_t i = 0; i < n; ++i) d[i] = (unsigned char)byte;
    return dst;
}
