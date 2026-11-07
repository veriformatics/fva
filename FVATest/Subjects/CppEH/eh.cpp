#include <stdint.h>

// All arithmetic is unsigned. The caught object carries the original input.
extern "C" uint32_t eh(uint32_t x) {
  try {
    if ((x & 1u) != 0u) throw x;
    return x + 1u;
  } catch (uint32_t value) {
    return value ^ UINT32_C(0xa5a5a5a5);
  }
}
