/* M2 (b) fidelity: a run's hand-written C model on each case (same output as artifact.mjs).
   Build: gcc -O1 -DMODEL_PREFIX|-DMODEL_LITERAL -DSRC='"path"' model.c */
#include <stdio.h>
#include <string.h>
#define LO 131072u
#define HI 2097152u
#include SRC
#ifdef MODEL_PREFIX
static unsigned char memory[HI];
#endif
static unsigned char before[HI];
int main(void) {
  char m[16], hex[512];
  unsigned s, d, size, cap;
  while (scanf("%15s %u %u %u %u %511s", m, &s, &d, &size, &cap, hex) == 6) {
    memset(memory + LO, 0xa5, HI - LO);
    if (strcmp(hex, "-"))
      for (unsigned i = 0; i < size; i++) sscanf(hex + 2 * i, "%2hhx", &memory[s + i]);
    memcpy(before, memory, HI);
#ifdef MODEL_PREFIX
    int ret = wasm_entry_prefix(memory, s, d, size, cap);
#else
    int ret = literal_path((int)s, (int)d, (int)size, (int)cap);
#endif
    long lo = -1, hi = -1;
    for (unsigned i = LO; i < HI; i++)
      if (before[i] != memory[i]) { if (lo < 0) lo = i; hi = i; }
    if (lo < 0) printf("%d none\n", ret);
    else {
      printf("%d %ld %ld ", ret, lo, hi);
      for (long i = lo; i <= hi; i++) printf("%02x", memory[i]);
      printf("\n");
    }
  }
  return 0;
}
