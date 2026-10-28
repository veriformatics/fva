#define LZ4_FREESTANDING 1
#define LZ4_memcpy memcpy
#define LZ4_memmove memmove
#define LZ4_memset memset
#define LZ4_FAST_DEC_LOOP 0
#include <stddef.h>
/*@ requires \false; assigns \nothing; */
void *memcpy(void *dst, const void *src, size_t n);
#include "c-memory.h"
#include "lz4.annotated.c"
#include "memory.annotated.c"

/*@ requires \separated(m + (..), inc32table + (..), dec64table + (..));
    requires \valid(m + (0 .. 2097151));
    requires 131072 <= s <= 2097151;
    requires 131072 <= d <= 2097151;
    requires 0 <= n <= 14;
    requires s+n+1 <= 2097152;
    requires 1 <= cap <= 2097152-d;
    requires n <= cap;
    requires s+n+1 <= d || d+cap <= s;
    requires (m[s] >> 4) == n;
    assigns m[d .. d+cap-1];
    ensures \result == n;
    ensures \forall integer k; 0 <= k < n ==> m[d+k] == \old(m[s+1+k]);
*/
int literal_block(unsigned char *m, int s, int d, int n, int cap) {
    return LZ4_decompress_safe((char *)(m+s), (char *)(m+d), n+1, cap);
}

/*@ requires \separated(m + (..), inc32table + (..), dec64table + (..));
    requires \valid(m + (0 .. 2097151));
    requires 131072 <= s <= 2097151;
    requires 131072 <= d <= 2097151;
    requires 1 <= size <= 15;
    requires s+size <= 2097152;
    requires 1 <= cap <= 11;
    requires d+cap <= 2097152;
    requires s+size <= d || d+cap <= s;
    requires m[s] < 240;
    assigns m[d .. d+cap-1];
    ensures \result == (((m[s] >> 4) == size-1 && size-1 <= cap) ? size-1 : -2);
    ensures \result >= 0 ==> \result <= cap;
    ensures \result >= 0 ==> (\forall integer k; 0 <= k < \result ==>
                                 m[d+k] == \old(m[s+1+k]));
*/
int small_output(unsigned char *m, int s, int d, int size, int cap) {
    return LZ4_decompress_safe((char *)(m+s), (char *)(m+d), size, cap);
}
