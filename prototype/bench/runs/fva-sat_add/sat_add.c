/* Saturating addition of 32-bit signed integers. */
int sat_add(int a, int b) {
  long long s = (long long)a + b;
  if (s > 2147483647) return 2147483647;
  if (s < -2147483647 - 1) return -2147483647 - 1;
  return (int)s;
}
