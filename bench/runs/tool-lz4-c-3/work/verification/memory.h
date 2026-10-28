#include <stddef.h>
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
void *proof_memcpy(void *dst, const void *src, size_t n);
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
void *proof_memmove(void *dst, const void *src, size_t n);
/*@ requires n <= 2097152;
    requires \valid((unsigned char*)dst + (0..n-1));
    terminates \true;
    assigns ((unsigned char*)dst)[0..n-1];
    ensures \result == dst;
    ensures \forall integer k; 0 <= k < \old(n) ==>
        ((unsigned char*)dst)[k] == (unsigned char)byte;
    exits \false;
*/
void *proof_memset(void *dst, int byte, size_t n);
