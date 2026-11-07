#ifndef FVA_ACCEPT_WASI_COMMON_H
#define FVA_ACCEPT_WASI_COMMON_H
#include <stdint.h>
#include <wasi/api.h>

static void bytes(__wasi_fd_t fd, const void *data, __wasi_size_t n) {
  const uint8_t *p = data;
  while (n != 0) {
    __wasi_ciovec_t v = {p, n};
    __wasi_size_t wrote = 0;
    if (__wasi_fd_write(fd, &v, 1, &wrote) != 0 || wrote == 0 || wrote > n)
      __wasi_proc_exit(99);
    p += wrote;
    n -= wrote;
  }
}
static __wasi_size_t length(const char *s) {
  __wasi_size_t n = 0;
  while (s[n] != 0) ++n;
  return n;
}
static void text(__wasi_fd_t fd, const char *s) { bytes(fd, s, length(s)); }
static void number(__wasi_fd_t fd, uint64_t n) {
  char b[20];
  unsigned i = sizeof b;
  do { b[--i] = '0' + n % 10; n /= 10; } while (n != 0);
  bytes(fd, b + i, sizeof b - i);
}
static void check(int good, unsigned line) {
  if (good) return;
  text(2, "check failed at line ");
  number(2, line);
  text(2, "\n");
  __wasi_proc_exit(90);
}
#define CHECK(p) check((p), __LINE__)
static void hex(const uint8_t *p, __wasi_size_t n) {
  const char digits[] = "0123456789abcdef";
  for (__wasi_size_t i = 0; i < n; ++i) {
    char b[] = {digits[p[i] >> 4], digits[p[i] & 15]};
    bytes(1, b, 2);
  }
  text(1, "\n");
}
#endif
