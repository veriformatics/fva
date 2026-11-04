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

extern lean_obj_res fva_fuzz_decode(lean_obj_arg bytes);
extern uint32_t fva_fuzz_leaves(lean_obj_arg module);
extern lean_obj_res fva_fuzz_leaf(lean_obj_arg module, uint32_t i);
extern lean_obj_res fva_fuzz_splice(lean_obj_arg module, uint32_t i, lean_obj_arg leaf);
extern lean_obj_res fva_fuzz_regen(lean_obj_arg module, uint64_t seed);
size_t LLVMFuzzerMutate(uint8_t *data, size_t size, size_t max_size);

static uint32_t (*target)(lean_obj_arg);
static int structured; // lift: structure-aware mutation (D76)

int LLVMFuzzerInitialize(int *argc, char ***argv) {
  (void)argc; (void)argv;
  const char *t = getenv("FVA_FUZZ_TARGET");
  if (t == NULL) t = "";
  if (strcmp(t, "lift") == 0) target = fva_fuzz_lift, structured = 1;
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

static lean_object *bytes_of(const uint8_t *data, size_t size) {
  lean_object *bs = lean_alloc_sarray(1, size, size);
  memcpy(lean_sarray_cptr(bs), data, size);
  return bs;
}

// Copy a Lean byte array into data when it is a non-empty module within max_size; else 0.
static size_t take(lean_object *out, uint8_t *data, size_t max_size) {
  size_t n = lean_sarray_size(out);
  if (n == 0 || n > max_size) { lean_dec(out); return 0; }
  memcpy(data, lean_sarray_cptr(out), n);
  lean_dec(out);
  return n;
}

// lift: a third byte mutation, a third one leaf (data bytes or a name) mutated by libFuzzer and
// spliced back into a re-encoded module, a third a regenerated function body; an input that
// does not decode, or a splice that fails, falls back to byte mutation (D76).
size_t LLVMFuzzerCustomMutator(uint8_t *data, size_t size, size_t max_size, unsigned int seed) {
  if (!structured || seed % 3 == 0) return LLVMFuzzerMutate(data, size, max_size);
  lean_object *m = fva_fuzz_decode(bytes_of(data, size)); // one decode; each call consumes a ref
  size_t n = 0;
  if (seed % 3 == 1) {
    lean_inc(m);
    uint32_t leaves = fva_fuzz_leaves(m);
    if (leaves > 0) {
      uint32_t i = (seed / 3) % leaves;
      lean_inc(m);
      lean_object *leaf = fva_fuzz_leaf(m, i);
      size_t len = lean_sarray_size(leaf), cap = len * 2 + 16;
      uint8_t *buf = malloc(cap);
      if (buf != NULL) {
        memcpy(buf, lean_sarray_cptr(leaf), len);
        size_t k = LLVMFuzzerMutate(buf, len, cap);
        lean_inc(m);
        n = take(fva_fuzz_splice(m, i, bytes_of(buf, k)), data, max_size);
        free(buf);
      }
      lean_dec(leaf);
    }
  } else {
    lean_inc(m);
    n = take(fva_fuzz_regen(m, seed), data, max_size);
  }
  lean_dec(m);
  return n > 0 ? n : LLVMFuzzerMutate(data, size, max_size);
}
