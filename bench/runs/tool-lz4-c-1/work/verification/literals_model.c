/* A manually written projection of the final-literal path, NOT the full decoder.
   Flat byte offsets model Wasm addresses. Calls to memmove are expanded as a
   forward byte copy, equivalent only because the buffers are disjoint here. */
unsigned char memory[2097152];

/*@
  requires 131072 <= src < 2097152;
  requires 131072 <= dst < 2097152;
  requires 1 <= size <= 15;
  requires src + size <= 2097152;
  requires 0 <= capacity <= 2097152 - dst;
  requires src + size <= dst || dst + capacity <= src;
  requires memory[src] / 16 == size - 1;
  requires size - 1 <= capacity;
  requires capacity == 0 ==> memory[src] == 0;
  terminates \true;
  assigns memory[dst .. dst + size - 2];
  ensures \result == size - 1;
  ensures 0 <= \result <= capacity;
  ensures \forall integer k; 0 <= k < \result ==>
    memory[dst+k] == \old(memory[src+1+k]);
*/
int literal_path(int src, int dst, int size, int capacity)
{
    /*@ assert src <= src < src + size; */
    if (capacity == 0)
        return ((size == 1) && memory[src] == 0) ? 0 : -1;
    unsigned token = memory[src];
    int length = (int)(token / 16U); /* high nibble, expressed arithmetically */
    int ip = src + 1;
    int cpy = dst + length;
    /* Path conditions selecting the final-literal copy in the original C. */
    /*@ assert length < 15; */
    /*@ assert !(ip < src + size - 16); */
    /*@ assert ip + length > src + size - 8; */
    if (ip + length != src + size || cpy > dst + capacity)
        return -1;
    /*@
      loop invariant 0 <= i <= length;
      loop invariant length == size - 1;
      loop invariant \forall integer k; 0 <= k < i ==>
        memory[dst+k] == \at(memory[src+1+k],Pre);
      loop invariant \forall integer k; src <= k < src + size ==>
        memory[k] == \at(memory[k],Pre);
      loop assigns i, memory[dst .. dst + size - 2];
      loop variant length - i;
    */
    for (int i = 0; i < length; ++i) {
        /* These assertions specify each caller-memory access, beyond \valid. */
        /*@ assert src <= ip+i < src+size; */
        /*@ assert dst <= dst+i < dst+capacity; */
        memory[dst+i] = memory[ip+i];
    }
    return cpy - dst;
}
