// libFuzzer driver for FVA's untrusted-byte readers (D70): Lean starts once, then each input
// goes to the Lean entry FVA_FUZZ_TARGET names (FVATest/Fuzz.lean, exported functions).
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern lean_object *initialize_fva_FVATest_Fuzz(uint8_t builtin);
void lean_initialize(void);
extern uint32_t fva_fuzz_lift(lean_obj_arg bytes);
extern uint32_t fva_fuzz_blob(lean_obj_arg bytes);
extern uint32_t fva_fuzz_codex(lean_obj_arg bytes);

static uint32_t (*target)(lean_obj_arg);

int LLVMFuzzerInitialize(int *argc, char ***argv) {
  (void)argc; (void)argv;
  const char *t = getenv("FVA_FUZZ_TARGET");
  if (t == NULL) t = "";
  if (strcmp(t, "lift") == 0) target = fva_fuzz_lift;
  else if (strcmp(t, "blob") == 0) target = fva_fuzz_blob;
  else if (strcmp(t, "codex") == 0) target = fva_fuzz_codex;
  else { fprintf(stderr, "fvafuzz: FVA_FUZZ_TARGET = lift | blob | codex\n"); exit(2); }
  lean_initialize();
  lean_object *r = initialize_fva_FVATest_Fuzz(1);
  if (lean_io_result_is_error(r)) { lean_io_result_show_error(r); exit(2); }
  lean_dec_ref(r);
  lean_io_mark_end_initialization();
  lean_init_task_manager();
  return 0;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  lean_object *bs = lean_alloc_sarray(1, size, size);
  memcpy(lean_sarray_cptr(bs), data, size);
  target(bs); // consumes bs
  return 0;
}
