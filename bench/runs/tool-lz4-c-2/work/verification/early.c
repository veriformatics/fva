#include "memory.h"
/*@ requires arena;
 requires v0 == sb && v1 == db;
 requires v2 == se-sb && v3 == de-db;
 requires v2 == 0 || v3 == 0;
 assigns \nothing;
 ensures \result == ((v3 == 0 && v2 == 1 && mem[v0] == 0) ? 0 : 4294967295);
*/
uint32_t f2_early(uint32_t v0, uint32_t v1, uint32_t v2, uint32_t v3) {
  uint32_t v4 = 0, v5 = 0, v6 = 0, v7 = 0, v8 = 0, v9 = 0, v10 = 0, v11 = 0, v12 = 0, v13 = 0, v14 = 0, v15 = 0, v16 = 0, v17 = 0, v18 = 0;
  uint32_t t0 = 4294967295u;
  v4 = t0;
  {
  uint32_t t1 = v0;
  uint32_t t2 = !t1;
  if (t2) goto end1;
  uint32_t t3 = v3;
  uint32_t t4 = 0u;
  uint32_t t5 = t3 >= 2147483648u;
  if (t5) goto end1;
  {
  uint32_t t6 = v3;
  if (t6) goto end2;
  uint32_t t7 = v2;
  uint32_t t8 = 1u;
  uint32_t t9 = t7 != t8;
  if (t9) goto end1;
  uint32_t t10 = 4294967295u;
  uint32_t t11 = 0u;
  uint32_t t12 = v0;
  uint32_t t13 = load8((uint64_t)t12 + 0u);
  uint32_t t14 = t13 ? t10 : t11;
  return t14;
  }
  end2: ;
  uint32_t t15 = v2;
  uint32_t t16 = !t15;
  if (t16) goto end1;
  /*@ assert unreachable_suffix: \false; */
  }
end1: ;
  return v4;
}
