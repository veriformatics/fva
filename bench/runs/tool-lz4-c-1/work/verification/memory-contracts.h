#include "../src/c-memory.h"
/*@
  requires n <= 1966080;
  requires \valid(((unsigned char*)dst) + (0 .. n-1));
  requires \valid_read(((const unsigned char*)src) + (0 .. n-1));
  requires \separated(((unsigned char*)dst) + (0 .. n-1),
                      ((const unsigned char*)src) + (0 .. n-1));
  assigns ((unsigned char*)dst)[0 .. n-1];
  ensures \result == dst;
  ensures \forall integer k; 0 <= k < n ==>
    ((unsigned char*)dst)[k] == \old(((const unsigned char*)src)[k]);
*/
void *memcpy(void *dst, const void *src, size_t n);
/*@
  requires n <= 1966080;
  requires \valid(((unsigned char*)dst) + (0 .. n-1));
  requires \valid_read(((const unsigned char*)src) + (0 .. n-1));
  requires \separated(((unsigned char*)dst) + (0 .. n-1),
                      ((const unsigned char*)src) + (0 .. n-1));
  assigns ((unsigned char*)dst)[0 .. n-1];
  ensures \result == dst;
  ensures \forall integer k; 0 <= k < n ==>
    ((unsigned char*)dst)[k] == \old(((const unsigned char*)src)[k]);
*/
void *memmove(void *dst, const void *src, size_t n);
/*@
  requires n <= 1966080;
  requires \valid(((unsigned char*)dst) + (0 .. n-1));
  assigns ((unsigned char*)dst)[0 .. n-1];
  ensures \result == dst;
  ensures \forall integer k; 0 <= k < n ==>
    ((unsigned char*)dst)[k] == (unsigned char)byte;
*/
void *memset(void *dst, int byte, size_t n);
