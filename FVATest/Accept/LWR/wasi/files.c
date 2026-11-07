// D28/U29b: namespace/file/fd identity, independent offsets, flags, short reads, sparse extension.
#include "common.h"

static const __wasi_rights_t rights = __WASI_RIGHTS_FD_READ | __WASI_RIGHTS_FD_WRITE |
  __WASI_RIGHTS_FD_SEEK | __WASI_RIGHTS_FD_FDSTAT_SET_FLAGS;
static __wasi_fd_t open_at(__wasi_fd_t dir, const char *name, __wasi_oflags_t flags) {
  __wasi_fd_t fd;
  CHECK(__wasi_path_open(dir, 0, name, flags, rights, 0, 0, &fd) == 0);
  return fd;
}
static uint64_t seek(__wasi_fd_t fd, int64_t delta, __wasi_whence_t whence) {
  __wasi_filesize_t at;
  CHECK(__wasi_fd_seek(fd, delta, whence, &at) == 0);
  return at;
}
static __wasi_size_t read_chunk(__wasi_fd_t fd, uint8_t *data, __wasi_size_t cap) {
  __wasi_iovec_t v = {data, cap};
  __wasi_size_t n;
  CHECK(__wasi_fd_read(fd, &v, 1, &n) == 0 && n <= cap);
  return n;
}
void _start(void) {
  __wasi_fd_t dir = -1;
  for (__wasi_fd_t fd = 3; fd < 64; ++fd) {
    __wasi_prestat_t p;
    if (__wasi_fd_prestat_get(fd, &p) != 0) continue;
    CHECK(p.tag == __WASI_PREOPENTYPE_DIR && p.u.dir.pr_name_len <= 128);
    uint8_t name[128];
    CHECK(__wasi_fd_prestat_dir_name(fd, name, p.u.dir.pr_name_len) == 0);
    if (p.u.dir.pr_name_len == 8) {
      const char expected[] = "/sandbox";
      unsigned i = 0;
      while (i < 8 && name[i] == (uint8_t)expected[i]) ++i;
      if (i == 8) dir = fd;
    }
  }
  CHECK(dir >= 0);
  text(1, "preopen=/sandbox\n");
  __wasi_fd_t fd = open_at(dir, "created.bin", __WASI_OFLAGS_CREAT | __WASI_OFLAGS_EXCL);
  bytes(fd, "abcdefghij", 10);
  __wasi_fd_t ignored;
  CHECK(__wasi_path_open(dir, 0, "created.bin", __WASI_OFLAGS_CREAT | __WASI_OFLAGS_EXCL,
    rights, 0, 0, &ignored) == __WASI_ERRNO_EXIST);
  CHECK(__wasi_path_open(dir, 0, "missing", 0, rights, 0, 0, &ignored) == __WASI_ERRNO_NOENT);
  __wasi_filestat_t st;
  CHECK(__wasi_path_filestat_get(dir, 0, "created.bin", &st) == 0);
  CHECK(st.filetype == __WASI_FILETYPE_REGULAR_FILE && st.size == 10);
  text(1, "created-size="); number(1, st.size); text(1, "\n");
  CHECK(__wasi_fd_fdstat_set_flags(fd, __WASI_FDFLAGS_APPEND) == 0);
  __wasi_fdstat_t fs;
  CHECK(__wasi_fd_fdstat_get(fd, &fs) == 0);
  CHECK(fs.fs_filetype == __WASI_FILETYPE_REGULAR_FILE);
  CHECK((fs.fs_flags & __WASI_FDFLAGS_APPEND) != 0);
  CHECK(seek(fd, 0, __WASI_WHENCE_SET) == 0);
  bytes(fd, "+", 1);
  CHECK(__wasi_fd_fdstat_set_flags(fd, 0) == 0);
  CHECK(seek(fd, 15, __WASI_WHENCE_SET) == 15);
  bytes(fd, "Z", 1);
  CHECK(seek(fd, 0, __WASI_WHENCE_CUR) == 16);
  __wasi_fd_t second = open_at(dir, "created.bin", 0);
  uint8_t buf[32];
  __wasi_size_t n = read_chunk(second, buf, 3);
  CHECK(n > 0);
  text(1, "second-prefix="); bytes(1, buf, n); text(1, "\n");
  CHECK(seek(fd, 0, __WASI_WHENCE_CUR) == 16);
  CHECK(seek(fd, -1, __WASI_WHENCE_END) == 15);
  CHECK(read_chunk(fd, buf, 2) == 1 && buf[0] == 'Z');
  CHECK(read_chunk(fd, buf, sizeof buf) == 0);
  CHECK(seek(fd, -6, __WASI_WHENCE_CUR) == 10);
  n = read_chunk(fd, buf, 5);
  text(1, "after-eof="); hex(buf, n);
  CHECK(seek(fd, 0, __WASI_WHENCE_SET) == 0);
  text(1, "chunked=");
  for (;;) {
    n = read_chunk(fd, buf, 2);
    if (n == 0) break;
    for (__wasi_size_t i = 0; i < n; ++i) {
      const char d[] = "0123456789abcdef";
      char h[] = {d[buf[i] >> 4], d[buf[i] & 15]};
      bytes(1, h, 2);
    }
  }
  text(1, "\n");
  CHECK(__wasi_fd_close(fd) == 0 && __wasi_fd_close(second) == 0);
  CHECK(__wasi_fd_close(second) == __WASI_ERRNO_BADF);
  fd = open_at(dir, "seed.txt", __WASI_OFLAGS_TRUNC);
  bytes(fd, "T", 1);
  CHECK(__wasi_fd_close(fd) == 0);
  fd = open_at(dir, "unlinked.bin", __WASI_OFLAGS_CREAT | __WASI_OFLAGS_EXCL);
  bytes(fd, "identity", 8);
  CHECK(__wasi_path_unlink_file(dir, "unlinked.bin") == 0);
  CHECK(seek(fd, 0, __WASI_WHENCE_SET) == 0);
  CHECK(read_chunk(fd, buf, sizeof buf) == 8);
  text(1, "unlinked-open="); bytes(1, buf, 8); text(1, "\n");
  CHECK(__wasi_fd_close(fd) == 0);
  CHECK(__wasi_path_filestat_get(dir, 0, "unlinked.bin", &st) == __WASI_ERRNO_NOENT);
  CHECK(__wasi_path_create_directory(dir, "temporary") == 0);
  CHECK(__wasi_path_filestat_get(dir, 0, "temporary", &st) == 0);
  CHECK(st.filetype == __WASI_FILETYPE_DIRECTORY);
  fd = open_at(dir, "temporary/child", __WASI_OFLAGS_CREAT | __WASI_OFLAGS_EXCL);
  CHECK(__wasi_fd_close(fd) == 0);
  CHECK(__wasi_path_remove_directory(dir, "temporary") == __WASI_ERRNO_NOTEMPTY);
  CHECK(__wasi_path_unlink_file(dir, "temporary/child") == 0);
  CHECK(__wasi_path_remove_directory(dir, "temporary") == 0);
  CHECK(__wasi_path_filestat_get(dir, 0, "temporary", &st) == __WASI_ERRNO_NOENT);
  text(1, "namespace=clean\n");
  text(2, "stderr=files\n");
}
