/* Integer square root. */
unsigned isqrt(unsigned n) {
  unsigned lo = 0, hi = 65536;
  while (hi - lo > 1) {
    unsigned mid = lo + (hi - lo) / 2;
    if ((unsigned long long)mid * mid <= n) lo = mid; else hi = mid;
  }
  return lo;
}
