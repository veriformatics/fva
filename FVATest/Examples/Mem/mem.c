/* Untrusted source: FVA verifies the compiled mem.wasm, never this file. */

/* The sum of the n 32-bit words at p, wrapping. */
unsigned array_sum(const unsigned *p, unsigned n) {
  unsigned s = 0;
#pragma clang loop unroll(disable) vectorize(disable)
  for (unsigned i = 0; i < n; i++) s += p[i];
  return s;
}

__attribute__((noinline)) static unsigned scale(unsigned x) { return 3 * x + 1; }

/* Two calls of a helper: scale(x) + scale(x + 1). */
unsigned call_scale(unsigned x) { return scale(x) + scale(x + 1); }

/* A dense switch (a br_table): each case a different function of y. */
unsigned classify(unsigned x, unsigned y) {
  switch (x) {
  case 0: return y + 7;
  case 1: return y << 3;
  case 2: return y ^ 0x55;
  case 3: return y * 100;
  case 4: return y - 9;
  default: return 0;
  }
}
