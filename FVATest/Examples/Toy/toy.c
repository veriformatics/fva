/* Untrusted source: FVA verifies the compiled toy.wasm, never this file. */
int clamp(int x, int lo, int hi) {
  if (x < lo) return lo;
  if (x > hi) return hi;
  return x;
}

unsigned gcd(unsigned a, unsigned b) {
  while (b != 0) {
    unsigned t = a % b;
    a = b;
    b = t;
  }
  return a;
}

unsigned sum_to(unsigned n) {
  unsigned s = 0;
  for (unsigned i = 0; i < n; i++) s += i;
  return s;
}
