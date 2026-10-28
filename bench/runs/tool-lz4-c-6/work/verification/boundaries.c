#define LZ4_FREESTANDING 1
#define LZ4_memcpy memcpy
#define LZ4_memmove memmove
#define LZ4_memset memset
#define LZ4_FAST_DEC_LOOP 0
#include <stddef.h>
/*@ requires \false; assigns \nothing; */
void *memcpy(void *dst, const void *src, size_t n);
/*@ requires \false; assigns \nothing; */
void *memmove(void *dst, const void *src, size_t n);
#include "c-memory.h"
#include "lz4.annotated.c"

/*@ requires \separated(m + (..), inc32table + (..), dec64table + (..));
    requires \valid(m + (0 .. 2097151));
    requires 131072 <= s <= 2097151;
    requires 131072 <= d <= 2097151;
    requires 0 <= cap <= 2097152-d;
    terminates \true;
    assigns \nothing;
    ensures \result == -1;
*/
int empty_source(unsigned char *m, int s, int d, int cap) {
    return LZ4_decompress_safe((char *)(m+s), (char *)(m+d), 0, cap);
}

/*@ requires \separated(m + (..), inc32table + (..), dec64table + (..));
    requires \valid(m + (0 .. 2097151));
    requires 131072 <= s <= 2097151;
    requires 131072 <= d <= 2097151;
    requires 0 <= size <= 2097152-s;
    terminates \true;
    assigns \nothing;
    ensures \result == ((size == 1 && m[s] == 0) ? 0 : -1);
*/
int zero_capacity(unsigned char *m, int s, int d, int size) {
    return LZ4_decompress_safe((char *)(m+s), (char *)(m+d), size, 0);
}
