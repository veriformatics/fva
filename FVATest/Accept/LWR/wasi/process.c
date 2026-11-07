// D28/U29b: args/env sizes + bytes, streamed stdin, both output streams, opaque clock/random.
#include "common.h"

static __wasi_size_t strings_size(uint8_t **items, __wasi_size_t count) {
  __wasi_size_t size = 0;
  for (__wasi_size_t i = 0; i < count; ++i) size += length((const char *)items[i]) + 1;
  return size;
}

void _start(void) {
  __wasi_size_t count, size;
  uint8_t *items[32];
  uint8_t data[4096];
  CHECK(__wasi_args_sizes_get(&count, &size) == 0);
  CHECK(count != 0 && count <= 32 && size <= sizeof data);
  CHECK(__wasi_args_get(items, data) == 0);
  CHECK(strings_size(items, count) == size);
  text(1, "argc="); number(1, count - 1); text(1, "\n");
  for (__wasi_size_t i = 1; i < count; ++i) {
    text(1, "arg="); text(1, (const char *)items[i]); text(1, "\n");
  }
  CHECK(__wasi_environ_sizes_get(&count, &size) == 0);
  CHECK(count <= 32 && size <= sizeof data);
  CHECK(__wasi_environ_get(items, data) == 0);
  CHECK(strings_size(items, count) == size);
  text(1, "envc="); number(1, count); text(1, "\n");
  for (__wasi_size_t i = 0; i < count; ++i) {
    text(1, "env="); text(1, (const char *)items[i]); text(1, "\n");
  }
  __wasi_timestamp_t now;
  uint8_t noise[17];
  CHECK(__wasi_clock_time_get(__WASI_CLOCKID_REALTIME, 1000, &now) == 0);
  CHECK(__wasi_clock_time_get(__WASI_CLOCKID_MONOTONIC, 1, &now) == 0);
  CHECK(__wasi_random_get(noise, 0) == 0);
  CHECK(__wasi_random_get(noise, sizeof noise) == 0);
  text(1, "stdin=");
  for (;;) {
    uint8_t chunk[3];
    __wasi_iovec_t v = {chunk, sizeof chunk};
    __wasi_size_t n;
    CHECK(__wasi_fd_read(0, &v, 1, &n) == 0 && n <= sizeof chunk);
    if (n == 0) break;
    bytes(1, chunk, n);
  }
  text(1, "\n");
  text(2, "stderr=process\n");
}
