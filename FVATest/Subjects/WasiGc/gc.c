/* GC count of a DNA sequence: reads seq.txt from the first preopened directory (fd 3), counts
   the bases G and C and every base A, C, G, T, and writes "<gc> <bases>\n" to stdout. Direct WASI
   preview1 calls and an explicit _start: no C library is linked. Exit status 0, or 1 when the
   file cannot be opened or read. */
#include <stdint.h>

#define WASI(name) __attribute__((import_module("wasi_snapshot_preview1"), import_name(#name)))

typedef struct { uint8_t *buf; uint32_t len; } iovec;

WASI(path_open) int32_t path_open(int32_t dirfd, int32_t dirflags, const char *path, int32_t path_len,
                                  int32_t oflags, int64_t rights_base, int64_t rights_inheriting,
                                  int32_t fdflags, int32_t *fd);
WASI(fd_read) int32_t fd_read(int32_t fd, const iovec *iovs, int32_t iovs_len, uint32_t *nread);
WASI(fd_write) int32_t fd_write(int32_t fd, const iovec *iovs, int32_t iovs_len, uint32_t *nwritten);
WASI(proc_exit) _Noreturn void proc_exit(int32_t code);

#define RIGHT_FD_READ 2 /* __WASI_RIGHTS_FD_READ */

static uint8_t buf[256];
static uint8_t out[24];

/* Writes v in decimal at p, returns the digit count. */
static uint32_t put_dec(uint8_t *p, uint32_t v) {
  uint8_t tmp[10];
  uint32_t n = 0;
  do { tmp[n++] = (uint8_t)('0' + v % 10); v /= 10; } while (v != 0);
  for (uint32_t i = 0; i < n; i++) p[i] = tmp[n - 1 - i];
  return n;
}

void _start(void) {
  int32_t fd;
  if (path_open(3, 0, "seq.txt", 7, 0, RIGHT_FD_READ, 0, 0, &fd) != 0) proc_exit(1);
  uint32_t gc = 0, bases = 0, n;
  iovec in = {buf, sizeof buf};
  for (;;) {
    if (fd_read(fd, &in, 1, &n) != 0) proc_exit(1);
    if (n == 0) break;
    for (uint32_t i = 0; i < n; i++) {
      uint8_t c = buf[i];
      if (c == 'G' || c == 'C') gc++;
      if (c == 'A' || c == 'C' || c == 'G' || c == 'T') bases++;
    }
  }
  uint32_t k = put_dec(out, gc);
  out[k++] = ' ';
  k += put_dec(out + k, bases);
  out[k++] = '\n';
  iovec o = {out, k};
  fd_write(1, &o, 1, &n);
  proc_exit(0);
}
