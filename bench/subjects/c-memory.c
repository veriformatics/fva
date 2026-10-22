#include "c-memory.h"

void *memcpy(void *dst, const void *src, size_t n) {
    unsigned char *d = dst;
    const unsigned char *s = src;
    for (size_t i = 0; i < n; ++i) d[i] = s[i];
    return dst;
}

void *memmove(void *dst, const void *src, size_t n) {
    unsigned char *d = dst;
    const unsigned char *s = src;
    /* wasm32 addresses: compare integers, not unrelated C pointers. */
    if ((size_t)d < (size_t)s) {
        for (size_t i = 0; i < n; ++i) d[i] = s[i];
    } else {
        while (n != 0) { --n; d[n] = s[n]; }
    }
    return dst;
}

void *memset(void *dst, int byte, size_t n) {
    unsigned char *d = dst;
    for (size_t i = 0; i < n; ++i) d[i] = (unsigned char)byte;
    return dst;
}
