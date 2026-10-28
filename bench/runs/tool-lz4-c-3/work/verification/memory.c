#define memcpy proof_memcpy
#define memmove proof_memmove
#define memset proof_memset
#include "../src/c-memory.h"

/*@ requires n <= 2097152;
    requires \valid((unsigned char*)dst + (0..n-1));
    requires \valid_read((const unsigned char*)src + (0..n-1));
    requires \separated((unsigned char*)dst + (0..n-1),
                         (const unsigned char*)src + (0..n-1));
    terminates \true;
    assigns ((unsigned char*)dst)[0..n-1];
    ensures \result == dst;
    ensures \forall integer k; 0 <= k < \old(n) ==>
        ((unsigned char*)dst)[k] == \old(((const unsigned char*)src)[k]);
    exits \false;
*/
void *memcpy(void *dst, const void *src, size_t n) {
    unsigned char *d = dst;
    const unsigned char *s = src;
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < n ==>
            s[k] == \at(((const unsigned char*)src)[k],Pre);
        loop invariant \forall integer k; 0 <= k < i ==> d[k] == \at(((const unsigned char*)src)[k],Pre);
        loop assigns i, d[0..n-1];
        loop variant n-i;
    */
    for (size_t i = 0; i < n; ++i)
        /*@ assert s[i] == \at(((const unsigned char*)src)[\at(i,Here)],Pre); */
        d[i] = s[i];
    return dst;
}

/*@ requires n <= 2097152;
    requires \valid((unsigned char*)dst + (0..n-1));
    requires \valid_read((const unsigned char*)src + (0..n-1));
    requires \separated((unsigned char*)dst + (0..n-1),
                         (const unsigned char*)src + (0..n-1));
    terminates \true;
    assigns ((unsigned char*)dst)[0..n-1];
    ensures \result == dst;
    ensures \forall integer k; 0 <= k < \old(n) ==>
        ((unsigned char*)dst)[k] == \old(((const unsigned char*)src)[k]);
    exits \false;
*/
void *memmove(void *dst, const void *src, size_t n) {
    unsigned char *d = dst;
    const unsigned char *s = src;
    /* wasm32 addresses: compare integers, not unrelated C pointers. */
    if ((size_t)d < (size_t)s) {
        /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < n ==>
            s[k] == \at(((const unsigned char*)src)[k],Pre);
        loop invariant \forall integer k; 0 <= k < i ==> d[k] == \at(((const unsigned char*)src)[k],Pre);
        loop assigns i, d[0..n-1];
        loop variant n-i;
    */
    for (size_t i = 0; i < n; ++i)
        /*@ assert s[i] == \at(((const unsigned char*)src)[\at(i,Here)],Pre); */
        d[i] = s[i];
    } else {
        /*@ loop invariant 0 <= n <= \at(n,Pre);
            loop invariant \forall integer k; 0 <= k < \at(n,Pre) ==>
                s[k] == \at(((const unsigned char*)src)[k],Pre);
            loop invariant \forall integer k; n <= k < \at(n,Pre) ==>
                d[k] == \at(((const unsigned char*)src)[k],Pre);
            loop assigns n, d[0..\at(n,Pre)-1];
            loop variant n;
        */
        while (n != 0) {
            --n;
            /*@ assert n + 1 == \at(n,LoopCurrent); */
            /*@ assert s[n] == \at(((const unsigned char*)src)[\at(n,Here)],Pre); */
            d[n] = s[n];
            /*@ assert d[n] == \at(((const unsigned char*)src)[\at(n,Here)],Pre); */
        }
    }
    return dst;
}

/*@ requires n <= 2097152;
    requires \valid((unsigned char*)dst + (0..n-1));
    terminates \true;
    assigns ((unsigned char*)dst)[0..n-1];
    ensures \result == dst;
    ensures \forall integer k; 0 <= k < \old(n) ==>
        ((unsigned char*)dst)[k] == (unsigned char)byte;
    exits \false;
*/
void *memset(void *dst, int byte, size_t n) {
    unsigned char *d = dst;
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> d[k] == (unsigned char)byte;
        loop assigns i, d[0..n-1];
        loop variant n-i;
    */
    for (size_t i = 0; i < n; ++i) d[i] = (unsigned char)byte;
    return dst;
}
