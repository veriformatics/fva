// D28/U29b: proc_exit is absorbing; it preserves prior stdout + stderr and exits nonzero.
#include "common.h"
void _start(void) {
  text(1, "before-exit\n");
  text(2, "exit-seven\n");
  __wasi_proc_exit(7);
  text(1, "unreachable-after-exit\n");
}
