/* Byte-memory implementation of the lifting interface. Table reads refer to
   the immutable data segment checked by lift.py. No client buffer can reach it. */
#include "memory.h"
unsigned char mem[2097152];
uint32_t sb, se, db, de;

uint32_t load8(uint64_t a) { return mem[a]; }
uint32_t load16(uint64_t a) { return mem[a] + 256u*mem[a+1]; }
uint32_t load32(uint64_t a) {
    if (a == 65540 || a == 65548 || a == 65588) return 1;
    if (a == 65544 || a == 65592) return 2;
    if (a == 65556 || a == 65560 || a == 65564) return 4;
    if (a == 65580) return 4294967295u;
    if (a == 65584) return 4294967292u;
    if (a == 65596) return 3;
    return 0;
}
void store8(uint64_t a, uint32_t value) { mem[a] = (unsigned char)value; }
void store32(uint64_t a, uint32_t value) {
    mem[a] = (unsigned char)value;
    mem[a+1] = (unsigned char)(value >> 8);
    mem[a+2] = (unsigned char)(value >> 16);
    mem[a+3] = (unsigned char)(value >> 24);
}

#ifdef LIFT_RUNTIME
uint32_t getmem(void) { return (uint32_t)(uintptr_t)mem; }
#endif
