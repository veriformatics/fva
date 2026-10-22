#ifndef FVA_BENCH_MEMORY_H
#define FVA_BENCH_MEMORY_H
#include <stddef.h>
void *memcpy(void *dst, const void *src, size_t n);
void *memmove(void *dst, const void *src, size_t n);
void *memset(void *dst, int byte, size_t n);
#endif
