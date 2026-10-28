#define LZ4_FREESTANDING 1
#define LZ4_memcpy memcpy
#define LZ4_memmove memmove
#define LZ4_memset memset
#define LZ4_FAST_DEC_LOOP 0
#define LZ4_FORCE_MEMORY_ACCESS 1
#include "memory-contracts.h"
#include "lz4-sliced.c"
