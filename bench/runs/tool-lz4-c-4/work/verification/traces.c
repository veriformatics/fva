/* Generated from SHA256 8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6 by verification/lift.py. */
_Static_assert(sizeof(unsigned int) == 4 && sizeof(int) == 4, "i32 machine model");
/*@
  requires specialization: n == 0 && d >= s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;

*/
unsigned int move4_0_0(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 0; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 == 0; */
  /* Wasm instruction 4: local.get */
  /* Wasm instruction 5: i32.eqz */
  unsigned int t1 = !0U;
  /* Wasm instruction 6: br_if */
  /*@ assert branch_1: t1 != 0; */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  return d;
}
/*@
  requires specialization: n == 0 && d < s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;

*/
unsigned int move4_0_1(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 0; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 != 0; */
  /* Wasm instruction 94: local.get */
  /* Wasm instruction 95: i32.eqz */
  unsigned int t1 = !0U;
  /* Wasm instruction 96: br_if */
  /*@ assert branch_6: t1 != 0; */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  return d;
}
/*@
  requires specialization: n == 1 && d >= s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
*/
unsigned int move4_1_0(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 1; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 == 0; */
  /* Wasm instruction 4: local.get */
  /* Wasm instruction 5: i32.eqz */
  unsigned int t1 = !1U;
  /* Wasm instruction 6: br_if */
  /*@ assert branch_1: t1 == 0; */
  /* Wasm instruction 7: local.get */
  /* Wasm instruction 8: local.set */
  /* Wasm instruction 9: local.get */
  /* Wasm instruction 10: i32.const */
  /* Wasm instruction 11: i32.and */
  unsigned int t2 = 1U & 3U;
  /* Wasm instruction 12: local.tee */
  /* Wasm instruction 13: i32.eqz */
  unsigned int t3 = !t2;
  /* Wasm instruction 14: br_if */
  /*@ assert branch_2: t3 == 0; */
  /* Wasm instruction 15: local.get */
  /* Wasm instruction 16: i32.const */
  /* Wasm instruction 17: i32.add */
  unsigned int t4 = s + 4294967295U;
  /*@ assert address_normalization: t4 == s + (-1); */
  /* Wasm instruction 18: local.set */
  /* Wasm instruction 19: local.get */
  /* Wasm instruction 20: i32.const */
  /* Wasm instruction 21: i32.add */
  unsigned int t5 = d + 4294967295U;
  /*@ assert address_normalization: t5 == d + (-1); */
  /* Wasm instruction 22: local.set */
  /* Wasm instruction 23: local.get */
  /* Wasm instruction 24: local.set */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: local.get */
  /* Wasm instruction 27: i32.add */
  unsigned int t6 = t5 + 1U;
  /*@ assert address_normalization: t6 == d + (0); */
  /* Wasm instruction 28: local.get */
  /* Wasm instruction 29: local.get */
  /* Wasm instruction 30: i32.add */
  unsigned int t7 = t4 + 1U;
  /*@ assert address_normalization: t7 == s + (0); */
  /* Wasm instruction 31: i32.load8_u */
  /*@ assert physical_bounds: t7 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t7 && t7 + 1 <= s + n; */
  unsigned int t8 = ((unsigned int)m[t7 + 0U] << 0);
  /* Wasm instruction 32: i32.store8 */
  /*@ assert physical_bounds: t6 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t6 && t6 + 1 <= d + n; */
  m[t6 + 0U] = (unsigned char)(t8 >> 0);
  /* Wasm instruction 33: local.get */
  /* Wasm instruction 34: i32.const */
  /* Wasm instruction 35: i32.add */
  unsigned int t9 = 1U + 4294967295U;
  /* Wasm instruction 36: local.set */
  /* Wasm instruction 37: local.get */
  /* Wasm instruction 38: i32.const */
  /* Wasm instruction 39: i32.add */
  unsigned int t10 = t2 + 4294967295U;
  /* Wasm instruction 40: local.tee */
  /* Wasm instruction 41: br_if */
  /*@ assert branch_3: t10 == 0; */
  /* Wasm instruction 42: local.get */
  /* Wasm instruction 43: i32.const */
  /* Wasm instruction 44: i32.lt_u */
  unsigned int t11 = 1U < 4U;
  /* Wasm instruction 45: br_if */
  /*@ assert branch_4: t11 != 0; */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  return d;
}
/*@
  requires specialization: n == 1 && d < s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
*/
unsigned int move4_1_1(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 1; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 != 0; */
  /* Wasm instruction 94: local.get */
  /* Wasm instruction 95: i32.eqz */
  unsigned int t1 = !1U;
  /* Wasm instruction 96: br_if */
  /*@ assert branch_6: t1 == 0; */
  /* Wasm instruction 97: local.get */
  /* Wasm instruction 98: i32.const */
  /* Wasm instruction 99: i32.and */
  unsigned int t2 = 1U & 3U;
  /* Wasm instruction 100: local.set */
  /* Wasm instruction 101: i32.const */
  /* Wasm instruction 102: local.set */
  /* Wasm instruction 103: local.get */
  /* Wasm instruction 104: i32.const */
  /* Wasm instruction 105: i32.lt_u */
  unsigned int t3 = 1U < 4U;
  /* Wasm instruction 106: br_if */
  /*@ assert branch_7: t3 != 0; */
  /* Wasm instruction 157: local.get */
  /* Wasm instruction 158: local.get */
  /* Wasm instruction 159: i32.add */
  unsigned int t4 = s + 0U;
  /*@ assert address_normalization: t4 == s + (0); */
  /* Wasm instruction 160: local.set */
  /* Wasm instruction 161: local.get */
  /* Wasm instruction 162: local.get */
  /* Wasm instruction 163: i32.add */
  unsigned int t5 = d + 0U;
  /*@ assert address_normalization: t5 == d + (0); */
  /* Wasm instruction 164: local.set */
  /* Wasm instruction 165: local.get */
  /* Wasm instruction 166: local.get */
  /* Wasm instruction 167: i32.load8_u */
  /*@ assert physical_bounds: t4 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t4 && t4 + 1 <= s + n; */
  unsigned int t6 = ((unsigned int)m[t4 + 0U] << 0);
  /* Wasm instruction 168: i32.store8 */
  /*@ assert physical_bounds: t5 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t5 && t5 + 1 <= d + n; */
  m[t5 + 0U] = (unsigned char)(t6 >> 0);
  /* Wasm instruction 169: local.get */
  /* Wasm instruction 170: i32.const */
  /* Wasm instruction 171: i32.add */
  unsigned int t7 = t4 + 1U;
  /*@ assert address_normalization: t7 == s + (1); */
  /* Wasm instruction 172: local.set */
  /* Wasm instruction 173: local.get */
  /* Wasm instruction 174: i32.const */
  /* Wasm instruction 175: i32.add */
  unsigned int t8 = t5 + 1U;
  /*@ assert address_normalization: t8 == d + (1); */
  /* Wasm instruction 176: local.set */
  /* Wasm instruction 177: local.get */
  /* Wasm instruction 178: i32.const */
  /* Wasm instruction 179: i32.add */
  unsigned int t9 = t2 + 4294967295U;
  /* Wasm instruction 180: local.tee */
  /* Wasm instruction 181: br_if */
  /*@ assert branch_10: t9 == 0; */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  return d;
}
/*@
  requires specialization: n == 2 && d >= s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
*/
unsigned int move4_2_0(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 2; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 == 0; */
  /* Wasm instruction 4: local.get */
  /* Wasm instruction 5: i32.eqz */
  unsigned int t1 = !2U;
  /* Wasm instruction 6: br_if */
  /*@ assert branch_1: t1 == 0; */
  /* Wasm instruction 7: local.get */
  /* Wasm instruction 8: local.set */
  /* Wasm instruction 9: local.get */
  /* Wasm instruction 10: i32.const */
  /* Wasm instruction 11: i32.and */
  unsigned int t2 = 2U & 3U;
  /* Wasm instruction 12: local.tee */
  /* Wasm instruction 13: i32.eqz */
  unsigned int t3 = !t2;
  /* Wasm instruction 14: br_if */
  /*@ assert branch_2: t3 == 0; */
  /* Wasm instruction 15: local.get */
  /* Wasm instruction 16: i32.const */
  /* Wasm instruction 17: i32.add */
  unsigned int t4 = s + 4294967295U;
  /*@ assert address_normalization: t4 == s + (-1); */
  /* Wasm instruction 18: local.set */
  /* Wasm instruction 19: local.get */
  /* Wasm instruction 20: i32.const */
  /* Wasm instruction 21: i32.add */
  unsigned int t5 = d + 4294967295U;
  /*@ assert address_normalization: t5 == d + (-1); */
  /* Wasm instruction 22: local.set */
  /* Wasm instruction 23: local.get */
  /* Wasm instruction 24: local.set */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: local.get */
  /* Wasm instruction 27: i32.add */
  unsigned int t6 = t5 + 2U;
  /*@ assert address_normalization: t6 == d + (1); */
  /* Wasm instruction 28: local.get */
  /* Wasm instruction 29: local.get */
  /* Wasm instruction 30: i32.add */
  unsigned int t7 = t4 + 2U;
  /*@ assert address_normalization: t7 == s + (1); */
  /* Wasm instruction 31: i32.load8_u */
  /*@ assert physical_bounds: t7 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t7 && t7 + 1 <= s + n; */
  unsigned int t8 = ((unsigned int)m[t7 + 0U] << 0);
  /* Wasm instruction 32: i32.store8 */
  /*@ assert physical_bounds: t6 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t6 && t6 + 1 <= d + n; */
  m[t6 + 0U] = (unsigned char)(t8 >> 0);
  /* Wasm instruction 33: local.get */
  /* Wasm instruction 34: i32.const */
  /* Wasm instruction 35: i32.add */
  unsigned int t9 = 2U + 4294967295U;
  /* Wasm instruction 36: local.set */
  /* Wasm instruction 37: local.get */
  /* Wasm instruction 38: i32.const */
  /* Wasm instruction 39: i32.add */
  unsigned int t10 = t2 + 4294967295U;
  /* Wasm instruction 40: local.tee */
  /* Wasm instruction 41: br_if */
  /*@ assert branch_3: t10 != 0; */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: local.get */
  /* Wasm instruction 27: i32.add */
  unsigned int t11 = t5 + t9;
  /*@ assert address_normalization: t11 == d + (0); */
  /* Wasm instruction 28: local.get */
  /* Wasm instruction 29: local.get */
  /* Wasm instruction 30: i32.add */
  unsigned int t12 = t4 + t9;
  /*@ assert address_normalization: t12 == s + (0); */
  /* Wasm instruction 31: i32.load8_u */
  /*@ assert physical_bounds: t12 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t12 && t12 + 1 <= s + n; */
  unsigned int t13 = ((unsigned int)m[t12 + 0U] << 0);
  /* Wasm instruction 32: i32.store8 */
  /*@ assert physical_bounds: t11 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t11 && t11 + 1 <= d + n; */
  m[t11 + 0U] = (unsigned char)(t13 >> 0);
  /* Wasm instruction 33: local.get */
  /* Wasm instruction 34: i32.const */
  /* Wasm instruction 35: i32.add */
  unsigned int t14 = t9 + 4294967295U;
  /* Wasm instruction 36: local.set */
  /* Wasm instruction 37: local.get */
  /* Wasm instruction 38: i32.const */
  /* Wasm instruction 39: i32.add */
  unsigned int t15 = t10 + 4294967295U;
  /* Wasm instruction 40: local.tee */
  /* Wasm instruction 41: br_if */
  /*@ assert branch_3: t15 == 0; */
  /* Wasm instruction 42: local.get */
  /* Wasm instruction 43: i32.const */
  /* Wasm instruction 44: i32.lt_u */
  unsigned int t16 = 2U < 4U;
  /* Wasm instruction 45: br_if */
  /*@ assert branch_4: t16 != 0; */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  return d;
}
/*@
  requires specialization: n == 2 && d < s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
*/
unsigned int move4_2_1(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 2; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 != 0; */
  /* Wasm instruction 94: local.get */
  /* Wasm instruction 95: i32.eqz */
  unsigned int t1 = !2U;
  /* Wasm instruction 96: br_if */
  /*@ assert branch_6: t1 == 0; */
  /* Wasm instruction 97: local.get */
  /* Wasm instruction 98: i32.const */
  /* Wasm instruction 99: i32.and */
  unsigned int t2 = 2U & 3U;
  /* Wasm instruction 100: local.set */
  /* Wasm instruction 101: i32.const */
  /* Wasm instruction 102: local.set */
  /* Wasm instruction 103: local.get */
  /* Wasm instruction 104: i32.const */
  /* Wasm instruction 105: i32.lt_u */
  unsigned int t3 = 2U < 4U;
  /* Wasm instruction 106: br_if */
  /*@ assert branch_7: t3 != 0; */
  /* Wasm instruction 157: local.get */
  /* Wasm instruction 158: local.get */
  /* Wasm instruction 159: i32.add */
  unsigned int t4 = s + 0U;
  /*@ assert address_normalization: t4 == s + (0); */
  /* Wasm instruction 160: local.set */
  /* Wasm instruction 161: local.get */
  /* Wasm instruction 162: local.get */
  /* Wasm instruction 163: i32.add */
  unsigned int t5 = d + 0U;
  /*@ assert address_normalization: t5 == d + (0); */
  /* Wasm instruction 164: local.set */
  /* Wasm instruction 165: local.get */
  /* Wasm instruction 166: local.get */
  /* Wasm instruction 167: i32.load8_u */
  /*@ assert physical_bounds: t4 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t4 && t4 + 1 <= s + n; */
  unsigned int t6 = ((unsigned int)m[t4 + 0U] << 0);
  /* Wasm instruction 168: i32.store8 */
  /*@ assert physical_bounds: t5 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t5 && t5 + 1 <= d + n; */
  m[t5 + 0U] = (unsigned char)(t6 >> 0);
  /* Wasm instruction 169: local.get */
  /* Wasm instruction 170: i32.const */
  /* Wasm instruction 171: i32.add */
  unsigned int t7 = t4 + 1U;
  /*@ assert address_normalization: t7 == s + (1); */
  /* Wasm instruction 172: local.set */
  /* Wasm instruction 173: local.get */
  /* Wasm instruction 174: i32.const */
  /* Wasm instruction 175: i32.add */
  unsigned int t8 = t5 + 1U;
  /*@ assert address_normalization: t8 == d + (1); */
  /* Wasm instruction 176: local.set */
  /* Wasm instruction 177: local.get */
  /* Wasm instruction 178: i32.const */
  /* Wasm instruction 179: i32.add */
  unsigned int t9 = t2 + 4294967295U;
  /* Wasm instruction 180: local.tee */
  /* Wasm instruction 181: br_if */
  /*@ assert branch_10: t9 != 0; */
  /* Wasm instruction 165: local.get */
  /* Wasm instruction 166: local.get */
  /* Wasm instruction 167: i32.load8_u */
  /*@ assert physical_bounds: t7 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t7 && t7 + 1 <= s + n; */
  unsigned int t10 = ((unsigned int)m[t7 + 0U] << 0);
  /* Wasm instruction 168: i32.store8 */
  /*@ assert physical_bounds: t8 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t8 && t8 + 1 <= d + n; */
  m[t8 + 0U] = (unsigned char)(t10 >> 0);
  /* Wasm instruction 169: local.get */
  /* Wasm instruction 170: i32.const */
  /* Wasm instruction 171: i32.add */
  unsigned int t11 = t7 + 1U;
  /*@ assert address_normalization: t11 == s + (2); */
  /* Wasm instruction 172: local.set */
  /* Wasm instruction 173: local.get */
  /* Wasm instruction 174: i32.const */
  /* Wasm instruction 175: i32.add */
  unsigned int t12 = t8 + 1U;
  /*@ assert address_normalization: t12 == d + (2); */
  /* Wasm instruction 176: local.set */
  /* Wasm instruction 177: local.get */
  /* Wasm instruction 178: i32.const */
  /* Wasm instruction 179: i32.add */
  unsigned int t13 = t9 + 4294967295U;
  /* Wasm instruction 180: local.tee */
  /* Wasm instruction 181: br_if */
  /*@ assert branch_10: t13 == 0; */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  return d;
}
/*@
  requires specialization: n == 3 && d >= s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
*/
unsigned int move4_3_0(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 3; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 == 0; */
  /* Wasm instruction 4: local.get */
  /* Wasm instruction 5: i32.eqz */
  unsigned int t1 = !3U;
  /* Wasm instruction 6: br_if */
  /*@ assert branch_1: t1 == 0; */
  /* Wasm instruction 7: local.get */
  /* Wasm instruction 8: local.set */
  /* Wasm instruction 9: local.get */
  /* Wasm instruction 10: i32.const */
  /* Wasm instruction 11: i32.and */
  unsigned int t2 = 3U & 3U;
  /* Wasm instruction 12: local.tee */
  /* Wasm instruction 13: i32.eqz */
  unsigned int t3 = !t2;
  /* Wasm instruction 14: br_if */
  /*@ assert branch_2: t3 == 0; */
  /* Wasm instruction 15: local.get */
  /* Wasm instruction 16: i32.const */
  /* Wasm instruction 17: i32.add */
  unsigned int t4 = s + 4294967295U;
  /*@ assert address_normalization: t4 == s + (-1); */
  /* Wasm instruction 18: local.set */
  /* Wasm instruction 19: local.get */
  /* Wasm instruction 20: i32.const */
  /* Wasm instruction 21: i32.add */
  unsigned int t5 = d + 4294967295U;
  /*@ assert address_normalization: t5 == d + (-1); */
  /* Wasm instruction 22: local.set */
  /* Wasm instruction 23: local.get */
  /* Wasm instruction 24: local.set */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: local.get */
  /* Wasm instruction 27: i32.add */
  unsigned int t6 = t5 + 3U;
  /*@ assert address_normalization: t6 == d + (2); */
  /* Wasm instruction 28: local.get */
  /* Wasm instruction 29: local.get */
  /* Wasm instruction 30: i32.add */
  unsigned int t7 = t4 + 3U;
  /*@ assert address_normalization: t7 == s + (2); */
  /* Wasm instruction 31: i32.load8_u */
  /*@ assert physical_bounds: t7 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t7 && t7 + 1 <= s + n; */
  unsigned int t8 = ((unsigned int)m[t7 + 0U] << 0);
  /* Wasm instruction 32: i32.store8 */
  /*@ assert physical_bounds: t6 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t6 && t6 + 1 <= d + n; */
  m[t6 + 0U] = (unsigned char)(t8 >> 0);
  /* Wasm instruction 33: local.get */
  /* Wasm instruction 34: i32.const */
  /* Wasm instruction 35: i32.add */
  unsigned int t9 = 3U + 4294967295U;
  /* Wasm instruction 36: local.set */
  /* Wasm instruction 37: local.get */
  /* Wasm instruction 38: i32.const */
  /* Wasm instruction 39: i32.add */
  unsigned int t10 = t2 + 4294967295U;
  /* Wasm instruction 40: local.tee */
  /* Wasm instruction 41: br_if */
  /*@ assert branch_3: t10 != 0; */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: local.get */
  /* Wasm instruction 27: i32.add */
  unsigned int t11 = t5 + t9;
  /*@ assert address_normalization: t11 == d + (1); */
  /* Wasm instruction 28: local.get */
  /* Wasm instruction 29: local.get */
  /* Wasm instruction 30: i32.add */
  unsigned int t12 = t4 + t9;
  /*@ assert address_normalization: t12 == s + (1); */
  /* Wasm instruction 31: i32.load8_u */
  /*@ assert physical_bounds: t12 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t12 && t12 + 1 <= s + n; */
  unsigned int t13 = ((unsigned int)m[t12 + 0U] << 0);
  /* Wasm instruction 32: i32.store8 */
  /*@ assert physical_bounds: t11 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t11 && t11 + 1 <= d + n; */
  m[t11 + 0U] = (unsigned char)(t13 >> 0);
  /* Wasm instruction 33: local.get */
  /* Wasm instruction 34: i32.const */
  /* Wasm instruction 35: i32.add */
  unsigned int t14 = t9 + 4294967295U;
  /* Wasm instruction 36: local.set */
  /* Wasm instruction 37: local.get */
  /* Wasm instruction 38: i32.const */
  /* Wasm instruction 39: i32.add */
  unsigned int t15 = t10 + 4294967295U;
  /* Wasm instruction 40: local.tee */
  /* Wasm instruction 41: br_if */
  /*@ assert branch_3: t15 != 0; */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: local.get */
  /* Wasm instruction 27: i32.add */
  unsigned int t16 = t5 + t14;
  /*@ assert address_normalization: t16 == d + (0); */
  /* Wasm instruction 28: local.get */
  /* Wasm instruction 29: local.get */
  /* Wasm instruction 30: i32.add */
  unsigned int t17 = t4 + t14;
  /*@ assert address_normalization: t17 == s + (0); */
  /* Wasm instruction 31: i32.load8_u */
  /*@ assert physical_bounds: t17 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t17 && t17 + 1 <= s + n; */
  unsigned int t18 = ((unsigned int)m[t17 + 0U] << 0);
  /* Wasm instruction 32: i32.store8 */
  /*@ assert physical_bounds: t16 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t16 && t16 + 1 <= d + n; */
  m[t16 + 0U] = (unsigned char)(t18 >> 0);
  /* Wasm instruction 33: local.get */
  /* Wasm instruction 34: i32.const */
  /* Wasm instruction 35: i32.add */
  unsigned int t19 = t14 + 4294967295U;
  /* Wasm instruction 36: local.set */
  /* Wasm instruction 37: local.get */
  /* Wasm instruction 38: i32.const */
  /* Wasm instruction 39: i32.add */
  unsigned int t20 = t15 + 4294967295U;
  /* Wasm instruction 40: local.tee */
  /* Wasm instruction 41: br_if */
  /*@ assert branch_3: t20 == 0; */
  /* Wasm instruction 42: local.get */
  /* Wasm instruction 43: i32.const */
  /* Wasm instruction 44: i32.lt_u */
  unsigned int t21 = 3U < 4U;
  /* Wasm instruction 45: br_if */
  /*@ assert branch_4: t21 != 0; */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  return d;
}
/*@
  requires specialization: n == 3 && d < s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
*/
unsigned int move4_3_1(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 3; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 != 0; */
  /* Wasm instruction 94: local.get */
  /* Wasm instruction 95: i32.eqz */
  unsigned int t1 = !3U;
  /* Wasm instruction 96: br_if */
  /*@ assert branch_6: t1 == 0; */
  /* Wasm instruction 97: local.get */
  /* Wasm instruction 98: i32.const */
  /* Wasm instruction 99: i32.and */
  unsigned int t2 = 3U & 3U;
  /* Wasm instruction 100: local.set */
  /* Wasm instruction 101: i32.const */
  /* Wasm instruction 102: local.set */
  /* Wasm instruction 103: local.get */
  /* Wasm instruction 104: i32.const */
  /* Wasm instruction 105: i32.lt_u */
  unsigned int t3 = 3U < 4U;
  /* Wasm instruction 106: br_if */
  /*@ assert branch_7: t3 != 0; */
  /* Wasm instruction 157: local.get */
  /* Wasm instruction 158: local.get */
  /* Wasm instruction 159: i32.add */
  unsigned int t4 = s + 0U;
  /*@ assert address_normalization: t4 == s + (0); */
  /* Wasm instruction 160: local.set */
  /* Wasm instruction 161: local.get */
  /* Wasm instruction 162: local.get */
  /* Wasm instruction 163: i32.add */
  unsigned int t5 = d + 0U;
  /*@ assert address_normalization: t5 == d + (0); */
  /* Wasm instruction 164: local.set */
  /* Wasm instruction 165: local.get */
  /* Wasm instruction 166: local.get */
  /* Wasm instruction 167: i32.load8_u */
  /*@ assert physical_bounds: t4 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t4 && t4 + 1 <= s + n; */
  unsigned int t6 = ((unsigned int)m[t4 + 0U] << 0);
  /* Wasm instruction 168: i32.store8 */
  /*@ assert physical_bounds: t5 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t5 && t5 + 1 <= d + n; */
  m[t5 + 0U] = (unsigned char)(t6 >> 0);
  /* Wasm instruction 169: local.get */
  /* Wasm instruction 170: i32.const */
  /* Wasm instruction 171: i32.add */
  unsigned int t7 = t4 + 1U;
  /*@ assert address_normalization: t7 == s + (1); */
  /* Wasm instruction 172: local.set */
  /* Wasm instruction 173: local.get */
  /* Wasm instruction 174: i32.const */
  /* Wasm instruction 175: i32.add */
  unsigned int t8 = t5 + 1U;
  /*@ assert address_normalization: t8 == d + (1); */
  /* Wasm instruction 176: local.set */
  /* Wasm instruction 177: local.get */
  /* Wasm instruction 178: i32.const */
  /* Wasm instruction 179: i32.add */
  unsigned int t9 = t2 + 4294967295U;
  /* Wasm instruction 180: local.tee */
  /* Wasm instruction 181: br_if */
  /*@ assert branch_10: t9 != 0; */
  /* Wasm instruction 165: local.get */
  /* Wasm instruction 166: local.get */
  /* Wasm instruction 167: i32.load8_u */
  /*@ assert physical_bounds: t7 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t7 && t7 + 1 <= s + n; */
  unsigned int t10 = ((unsigned int)m[t7 + 0U] << 0);
  /* Wasm instruction 168: i32.store8 */
  /*@ assert physical_bounds: t8 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t8 && t8 + 1 <= d + n; */
  m[t8 + 0U] = (unsigned char)(t10 >> 0);
  /* Wasm instruction 169: local.get */
  /* Wasm instruction 170: i32.const */
  /* Wasm instruction 171: i32.add */
  unsigned int t11 = t7 + 1U;
  /*@ assert address_normalization: t11 == s + (2); */
  /* Wasm instruction 172: local.set */
  /* Wasm instruction 173: local.get */
  /* Wasm instruction 174: i32.const */
  /* Wasm instruction 175: i32.add */
  unsigned int t12 = t8 + 1U;
  /*@ assert address_normalization: t12 == d + (2); */
  /* Wasm instruction 176: local.set */
  /* Wasm instruction 177: local.get */
  /* Wasm instruction 178: i32.const */
  /* Wasm instruction 179: i32.add */
  unsigned int t13 = t9 + 4294967295U;
  /* Wasm instruction 180: local.tee */
  /* Wasm instruction 181: br_if */
  /*@ assert branch_10: t13 != 0; */
  /* Wasm instruction 165: local.get */
  /* Wasm instruction 166: local.get */
  /* Wasm instruction 167: i32.load8_u */
  /*@ assert physical_bounds: t11 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t11 && t11 + 1 <= s + n; */
  unsigned int t14 = ((unsigned int)m[t11 + 0U] << 0);
  /* Wasm instruction 168: i32.store8 */
  /*@ assert physical_bounds: t12 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t12 && t12 + 1 <= d + n; */
  m[t12 + 0U] = (unsigned char)(t14 >> 0);
  /* Wasm instruction 169: local.get */
  /* Wasm instruction 170: i32.const */
  /* Wasm instruction 171: i32.add */
  unsigned int t15 = t11 + 1U;
  /*@ assert address_normalization: t15 == s + (3); */
  /* Wasm instruction 172: local.set */
  /* Wasm instruction 173: local.get */
  /* Wasm instruction 174: i32.const */
  /* Wasm instruction 175: i32.add */
  unsigned int t16 = t12 + 1U;
  /*@ assert address_normalization: t16 == d + (3); */
  /* Wasm instruction 176: local.set */
  /* Wasm instruction 177: local.get */
  /* Wasm instruction 178: i32.const */
  /* Wasm instruction 179: i32.add */
  unsigned int t17 = t13 + 4294967295U;
  /* Wasm instruction 180: local.tee */
  /* Wasm instruction 181: br_if */
  /*@ assert branch_10: t17 == 0; */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  return d;
}
/*@
  requires specialization: n == 4 && d >= s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
  ensures byte_3: m[d+3] == \old(m[s+3]);
*/
unsigned int move4_4_0(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 4; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 == 0; */
  /* Wasm instruction 4: local.get */
  /* Wasm instruction 5: i32.eqz */
  unsigned int t1 = !4U;
  /* Wasm instruction 6: br_if */
  /*@ assert branch_1: t1 == 0; */
  /* Wasm instruction 7: local.get */
  /* Wasm instruction 8: local.set */
  /* Wasm instruction 9: local.get */
  /* Wasm instruction 10: i32.const */
  /* Wasm instruction 11: i32.and */
  unsigned int t2 = 4U & 3U;
  /* Wasm instruction 12: local.tee */
  /* Wasm instruction 13: i32.eqz */
  unsigned int t3 = !t2;
  /* Wasm instruction 14: br_if */
  /*@ assert branch_2: t3 != 0; */
  /* Wasm instruction 42: local.get */
  /* Wasm instruction 43: i32.const */
  /* Wasm instruction 44: i32.lt_u */
  unsigned int t4 = 4U < 4U;
  /* Wasm instruction 45: br_if */
  /*@ assert branch_4: t4 == 0; */
  /* Wasm instruction 46: local.get */
  /* Wasm instruction 47: i32.const */
  /* Wasm instruction 48: i32.add */
  unsigned int t5 = s + 4294967292U;
  /*@ assert address_normalization: t5 == s + (-4); */
  /* Wasm instruction 49: local.set */
  /* Wasm instruction 50: local.get */
  /* Wasm instruction 51: i32.const */
  /* Wasm instruction 52: i32.add */
  unsigned int t6 = d + 4294967292U;
  /*@ assert address_normalization: t6 == d + (-4); */
  /* Wasm instruction 53: local.set */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: local.get */
  /* Wasm instruction 56: i32.add */
  unsigned int t7 = t6 + 4U;
  /*@ assert address_normalization: t7 == d + (0); */
  /* Wasm instruction 57: local.tee */
  /* Wasm instruction 58: i32.const */
  /* Wasm instruction 59: i32.add */
  unsigned int t8 = t7 + 3U;
  /*@ assert address_normalization: t8 == d + (3); */
  /* Wasm instruction 60: local.get */
  /* Wasm instruction 61: local.get */
  /* Wasm instruction 62: i32.add */
  unsigned int t9 = t5 + 4U;
  /*@ assert address_normalization: t9 == s + (0); */
  /* Wasm instruction 63: local.tee */
  /* Wasm instruction 64: i32.const */
  /* Wasm instruction 65: i32.add */
  unsigned int t10 = t9 + 3U;
  /*@ assert address_normalization: t10 == s + (3); */
  /* Wasm instruction 66: i32.load8_u */
  /*@ assert physical_bounds: t10 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t10 && t10 + 1 <= s + n; */
  unsigned int t11 = ((unsigned int)m[t10 + 0U] << 0);
  /* Wasm instruction 67: i32.store8 */
  /*@ assert physical_bounds: t8 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t8 && t8 + 1 <= d + n; */
  m[t8 + 0U] = (unsigned char)(t11 >> 0);
  /* Wasm instruction 68: local.get */
  /* Wasm instruction 69: i32.const */
  /* Wasm instruction 70: i32.add */
  unsigned int t12 = t7 + 2U;
  /*@ assert address_normalization: t12 == d + (2); */
  /* Wasm instruction 71: local.get */
  /* Wasm instruction 72: i32.const */
  /* Wasm instruction 73: i32.add */
  unsigned int t13 = t9 + 2U;
  /*@ assert address_normalization: t13 == s + (2); */
  /* Wasm instruction 74: i32.load8_u */
  /*@ assert physical_bounds: t13 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t13 && t13 + 1 <= s + n; */
  unsigned int t14 = ((unsigned int)m[t13 + 0U] << 0);
  /* Wasm instruction 75: i32.store8 */
  /*@ assert physical_bounds: t12 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t12 && t12 + 1 <= d + n; */
  m[t12 + 0U] = (unsigned char)(t14 >> 0);
  /* Wasm instruction 76: local.get */
  /* Wasm instruction 77: i32.const */
  /* Wasm instruction 78: i32.add */
  unsigned int t15 = t7 + 1U;
  /*@ assert address_normalization: t15 == d + (1); */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: i32.const */
  /* Wasm instruction 81: i32.add */
  unsigned int t16 = t9 + 1U;
  /*@ assert address_normalization: t16 == s + (1); */
  /* Wasm instruction 82: i32.load8_u */
  /*@ assert physical_bounds: t16 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t16 && t16 + 1 <= s + n; */
  unsigned int t17 = ((unsigned int)m[t16 + 0U] << 0);
  /* Wasm instruction 83: i32.store8 */
  /*@ assert physical_bounds: t15 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t15 && t15 + 1 <= d + n; */
  m[t15 + 0U] = (unsigned char)(t17 >> 0);
  /* Wasm instruction 84: local.get */
  /* Wasm instruction 85: local.get */
  /* Wasm instruction 86: i32.load8_u */
  /*@ assert physical_bounds: t9 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t9 && t9 + 1 <= s + n; */
  unsigned int t18 = ((unsigned int)m[t9 + 0U] << 0);
  /* Wasm instruction 87: i32.store8 */
  /*@ assert physical_bounds: t7 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t7 && t7 + 1 <= d + n; */
  m[t7 + 0U] = (unsigned char)(t18 >> 0);
  /* Wasm instruction 88: local.get */
  /* Wasm instruction 89: i32.const */
  /* Wasm instruction 90: i32.add */
  unsigned int t19 = 4U + 4294967292U;
  /* Wasm instruction 91: local.tee */
  /* Wasm instruction 92: br_if */
  /*@ assert branch_5: t19 == 0; */
  /* Wasm instruction 93: br */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  /*@ assert copied_byte_3: m[d+3] == \at(m[s+3],Pre); */
  return d;
}
/*@
  requires specialization: n == 4 && d < s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
  ensures byte_3: m[d+3] == \old(m[s+3]);
*/
unsigned int move4_4_1(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 4; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 != 0; */
  /* Wasm instruction 94: local.get */
  /* Wasm instruction 95: i32.eqz */
  unsigned int t1 = !4U;
  /* Wasm instruction 96: br_if */
  /*@ assert branch_6: t1 == 0; */
  /* Wasm instruction 97: local.get */
  /* Wasm instruction 98: i32.const */
  /* Wasm instruction 99: i32.and */
  unsigned int t2 = 4U & 3U;
  /* Wasm instruction 100: local.set */
  /* Wasm instruction 101: i32.const */
  /* Wasm instruction 102: local.set */
  /* Wasm instruction 103: local.get */
  /* Wasm instruction 104: i32.const */
  /* Wasm instruction 105: i32.lt_u */
  unsigned int t3 = 4U < 4U;
  /* Wasm instruction 106: br_if */
  /*@ assert branch_7: t3 == 0; */
  /* Wasm instruction 107: local.get */
  /* Wasm instruction 108: i32.const */
  /* Wasm instruction 109: i32.and */
  unsigned int t4 = 4U & 4294967292U;
  /* Wasm instruction 110: local.set */
  /* Wasm instruction 111: i32.const */
  /* Wasm instruction 112: local.set */
  /* Wasm instruction 113: local.get */
  /* Wasm instruction 114: local.get */
  /* Wasm instruction 115: i32.add */
  unsigned int t5 = d + 0U;
  /*@ assert address_normalization: t5 == d + (0); */
  /* Wasm instruction 116: local.tee */
  /* Wasm instruction 117: local.get */
  /* Wasm instruction 118: local.get */
  /* Wasm instruction 119: i32.add */
  unsigned int t6 = s + 0U;
  /*@ assert address_normalization: t6 == s + (0); */
  /* Wasm instruction 120: local.tee */
  /* Wasm instruction 121: i32.load8_u */
  /*@ assert physical_bounds: t6 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t6 && t6 + 1 <= s + n; */
  unsigned int t7 = ((unsigned int)m[t6 + 0U] << 0);
  /* Wasm instruction 122: i32.store8 */
  /*@ assert physical_bounds: t5 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t5 && t5 + 1 <= d + n; */
  m[t5 + 0U] = (unsigned char)(t7 >> 0);
  /* Wasm instruction 123: local.get */
  /* Wasm instruction 124: i32.const */
  /* Wasm instruction 125: i32.add */
  unsigned int t8 = t5 + 1U;
  /*@ assert address_normalization: t8 == d + (1); */
  /* Wasm instruction 126: local.get */
  /* Wasm instruction 127: i32.const */
  /* Wasm instruction 128: i32.add */
  unsigned int t9 = t6 + 1U;
  /*@ assert address_normalization: t9 == s + (1); */
  /* Wasm instruction 129: i32.load8_u */
  /*@ assert physical_bounds: t9 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t9 && t9 + 1 <= s + n; */
  unsigned int t10 = ((unsigned int)m[t9 + 0U] << 0);
  /* Wasm instruction 130: i32.store8 */
  /*@ assert physical_bounds: t8 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t8 && t8 + 1 <= d + n; */
  m[t8 + 0U] = (unsigned char)(t10 >> 0);
  /* Wasm instruction 131: local.get */
  /* Wasm instruction 132: i32.const */
  /* Wasm instruction 133: i32.add */
  unsigned int t11 = t5 + 2U;
  /*@ assert address_normalization: t11 == d + (2); */
  /* Wasm instruction 134: local.get */
  /* Wasm instruction 135: i32.const */
  /* Wasm instruction 136: i32.add */
  unsigned int t12 = t6 + 2U;
  /*@ assert address_normalization: t12 == s + (2); */
  /* Wasm instruction 137: i32.load8_u */
  /*@ assert physical_bounds: t12 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t12 && t12 + 1 <= s + n; */
  unsigned int t13 = ((unsigned int)m[t12 + 0U] << 0);
  /* Wasm instruction 138: i32.store8 */
  /*@ assert physical_bounds: t11 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t11 && t11 + 1 <= d + n; */
  m[t11 + 0U] = (unsigned char)(t13 >> 0);
  /* Wasm instruction 139: local.get */
  /* Wasm instruction 140: i32.const */
  /* Wasm instruction 141: i32.add */
  unsigned int t14 = t5 + 3U;
  /*@ assert address_normalization: t14 == d + (3); */
  /* Wasm instruction 142: local.get */
  /* Wasm instruction 143: i32.const */
  /* Wasm instruction 144: i32.add */
  unsigned int t15 = t6 + 3U;
  /*@ assert address_normalization: t15 == s + (3); */
  /* Wasm instruction 145: i32.load8_u */
  /*@ assert physical_bounds: t15 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t15 && t15 + 1 <= s + n; */
  unsigned int t16 = ((unsigned int)m[t15 + 0U] << 0);
  /* Wasm instruction 146: i32.store8 */
  /*@ assert physical_bounds: t14 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t14 && t14 + 1 <= d + n; */
  m[t14 + 0U] = (unsigned char)(t16 >> 0);
  /* Wasm instruction 147: local.get */
  /* Wasm instruction 148: local.get */
  /* Wasm instruction 149: i32.const */
  /* Wasm instruction 150: i32.add */
  unsigned int t17 = 0U + 4U;
  /* Wasm instruction 151: local.tee */
  /* Wasm instruction 152: i32.ne */
  unsigned int t18 = t4 != t17;
  /* Wasm instruction 153: br_if */
  /*@ assert branch_8: t18 == 0; */
  /* Wasm instruction 154: local.get */
  /* Wasm instruction 155: i32.eqz */
  unsigned int t19 = !t2;
  /* Wasm instruction 156: br_if */
  /*@ assert branch_9: t19 != 0; */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  /*@ assert copied_byte_3: m[d+3] == \at(m[s+3],Pre); */
  return d;
}
/*@
  requires specialization: n == 5 && d >= s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
  ensures byte_3: m[d+3] == \old(m[s+3]);
  ensures byte_4: m[d+4] == \old(m[s+4]);
*/
unsigned int move4_5_0(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 5; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 == 0; */
  /* Wasm instruction 4: local.get */
  /* Wasm instruction 5: i32.eqz */
  unsigned int t1 = !5U;
  /* Wasm instruction 6: br_if */
  /*@ assert branch_1: t1 == 0; */
  /* Wasm instruction 7: local.get */
  /* Wasm instruction 8: local.set */
  /* Wasm instruction 9: local.get */
  /* Wasm instruction 10: i32.const */
  /* Wasm instruction 11: i32.and */
  unsigned int t2 = 5U & 3U;
  /* Wasm instruction 12: local.tee */
  /* Wasm instruction 13: i32.eqz */
  unsigned int t3 = !t2;
  /* Wasm instruction 14: br_if */
  /*@ assert branch_2: t3 == 0; */
  /* Wasm instruction 15: local.get */
  /* Wasm instruction 16: i32.const */
  /* Wasm instruction 17: i32.add */
  unsigned int t4 = s + 4294967295U;
  /*@ assert address_normalization: t4 == s + (-1); */
  /* Wasm instruction 18: local.set */
  /* Wasm instruction 19: local.get */
  /* Wasm instruction 20: i32.const */
  /* Wasm instruction 21: i32.add */
  unsigned int t5 = d + 4294967295U;
  /*@ assert address_normalization: t5 == d + (-1); */
  /* Wasm instruction 22: local.set */
  /* Wasm instruction 23: local.get */
  /* Wasm instruction 24: local.set */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: local.get */
  /* Wasm instruction 27: i32.add */
  unsigned int t6 = t5 + 5U;
  /*@ assert address_normalization: t6 == d + (4); */
  /* Wasm instruction 28: local.get */
  /* Wasm instruction 29: local.get */
  /* Wasm instruction 30: i32.add */
  unsigned int t7 = t4 + 5U;
  /*@ assert address_normalization: t7 == s + (4); */
  /* Wasm instruction 31: i32.load8_u */
  /*@ assert physical_bounds: t7 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t7 && t7 + 1 <= s + n; */
  unsigned int t8 = ((unsigned int)m[t7 + 0U] << 0);
  /* Wasm instruction 32: i32.store8 */
  /*@ assert physical_bounds: t6 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t6 && t6 + 1 <= d + n; */
  m[t6 + 0U] = (unsigned char)(t8 >> 0);
  /* Wasm instruction 33: local.get */
  /* Wasm instruction 34: i32.const */
  /* Wasm instruction 35: i32.add */
  unsigned int t9 = 5U + 4294967295U;
  /* Wasm instruction 36: local.set */
  /* Wasm instruction 37: local.get */
  /* Wasm instruction 38: i32.const */
  /* Wasm instruction 39: i32.add */
  unsigned int t10 = t2 + 4294967295U;
  /* Wasm instruction 40: local.tee */
  /* Wasm instruction 41: br_if */
  /*@ assert branch_3: t10 == 0; */
  /* Wasm instruction 42: local.get */
  /* Wasm instruction 43: i32.const */
  /* Wasm instruction 44: i32.lt_u */
  unsigned int t11 = 5U < 4U;
  /* Wasm instruction 45: br_if */
  /*@ assert branch_4: t11 == 0; */
  /* Wasm instruction 46: local.get */
  /* Wasm instruction 47: i32.const */
  /* Wasm instruction 48: i32.add */
  unsigned int t12 = s + 4294967292U;
  /*@ assert address_normalization: t12 == s + (-4); */
  /* Wasm instruction 49: local.set */
  /* Wasm instruction 50: local.get */
  /* Wasm instruction 51: i32.const */
  /* Wasm instruction 52: i32.add */
  unsigned int t13 = d + 4294967292U;
  /*@ assert address_normalization: t13 == d + (-4); */
  /* Wasm instruction 53: local.set */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: local.get */
  /* Wasm instruction 56: i32.add */
  unsigned int t14 = t13 + t9;
  /*@ assert address_normalization: t14 == d + (0); */
  /* Wasm instruction 57: local.tee */
  /* Wasm instruction 58: i32.const */
  /* Wasm instruction 59: i32.add */
  unsigned int t15 = t14 + 3U;
  /*@ assert address_normalization: t15 == d + (3); */
  /* Wasm instruction 60: local.get */
  /* Wasm instruction 61: local.get */
  /* Wasm instruction 62: i32.add */
  unsigned int t16 = t12 + t9;
  /*@ assert address_normalization: t16 == s + (0); */
  /* Wasm instruction 63: local.tee */
  /* Wasm instruction 64: i32.const */
  /* Wasm instruction 65: i32.add */
  unsigned int t17 = t16 + 3U;
  /*@ assert address_normalization: t17 == s + (3); */
  /* Wasm instruction 66: i32.load8_u */
  /*@ assert physical_bounds: t17 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t17 && t17 + 1 <= s + n; */
  unsigned int t18 = ((unsigned int)m[t17 + 0U] << 0);
  /* Wasm instruction 67: i32.store8 */
  /*@ assert physical_bounds: t15 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t15 && t15 + 1 <= d + n; */
  m[t15 + 0U] = (unsigned char)(t18 >> 0);
  /* Wasm instruction 68: local.get */
  /* Wasm instruction 69: i32.const */
  /* Wasm instruction 70: i32.add */
  unsigned int t19 = t14 + 2U;
  /*@ assert address_normalization: t19 == d + (2); */
  /* Wasm instruction 71: local.get */
  /* Wasm instruction 72: i32.const */
  /* Wasm instruction 73: i32.add */
  unsigned int t20 = t16 + 2U;
  /*@ assert address_normalization: t20 == s + (2); */
  /* Wasm instruction 74: i32.load8_u */
  /*@ assert physical_bounds: t20 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t20 && t20 + 1 <= s + n; */
  unsigned int t21 = ((unsigned int)m[t20 + 0U] << 0);
  /* Wasm instruction 75: i32.store8 */
  /*@ assert physical_bounds: t19 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t19 && t19 + 1 <= d + n; */
  m[t19 + 0U] = (unsigned char)(t21 >> 0);
  /* Wasm instruction 76: local.get */
  /* Wasm instruction 77: i32.const */
  /* Wasm instruction 78: i32.add */
  unsigned int t22 = t14 + 1U;
  /*@ assert address_normalization: t22 == d + (1); */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: i32.const */
  /* Wasm instruction 81: i32.add */
  unsigned int t23 = t16 + 1U;
  /*@ assert address_normalization: t23 == s + (1); */
  /* Wasm instruction 82: i32.load8_u */
  /*@ assert physical_bounds: t23 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t23 && t23 + 1 <= s + n; */
  unsigned int t24 = ((unsigned int)m[t23 + 0U] << 0);
  /* Wasm instruction 83: i32.store8 */
  /*@ assert physical_bounds: t22 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t22 && t22 + 1 <= d + n; */
  m[t22 + 0U] = (unsigned char)(t24 >> 0);
  /* Wasm instruction 84: local.get */
  /* Wasm instruction 85: local.get */
  /* Wasm instruction 86: i32.load8_u */
  /*@ assert physical_bounds: t16 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t16 && t16 + 1 <= s + n; */
  unsigned int t25 = ((unsigned int)m[t16 + 0U] << 0);
  /* Wasm instruction 87: i32.store8 */
  /*@ assert physical_bounds: t14 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t14 && t14 + 1 <= d + n; */
  m[t14 + 0U] = (unsigned char)(t25 >> 0);
  /* Wasm instruction 88: local.get */
  /* Wasm instruction 89: i32.const */
  /* Wasm instruction 90: i32.add */
  unsigned int t26 = t9 + 4294967292U;
  /* Wasm instruction 91: local.tee */
  /* Wasm instruction 92: br_if */
  /*@ assert branch_5: t26 == 0; */
  /* Wasm instruction 93: br */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  /*@ assert copied_byte_3: m[d+3] == \at(m[s+3],Pre); */
  /*@ assert copied_byte_4: m[d+4] == \at(m[s+4],Pre); */
  return d;
}
/*@
  requires specialization: n == 5 && d < s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
  ensures byte_3: m[d+3] == \old(m[s+3]);
  ensures byte_4: m[d+4] == \old(m[s+4]);
*/
unsigned int move4_5_1(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 5; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 != 0; */
  /* Wasm instruction 94: local.get */
  /* Wasm instruction 95: i32.eqz */
  unsigned int t1 = !5U;
  /* Wasm instruction 96: br_if */
  /*@ assert branch_6: t1 == 0; */
  /* Wasm instruction 97: local.get */
  /* Wasm instruction 98: i32.const */
  /* Wasm instruction 99: i32.and */
  unsigned int t2 = 5U & 3U;
  /* Wasm instruction 100: local.set */
  /* Wasm instruction 101: i32.const */
  /* Wasm instruction 102: local.set */
  /* Wasm instruction 103: local.get */
  /* Wasm instruction 104: i32.const */
  /* Wasm instruction 105: i32.lt_u */
  unsigned int t3 = 5U < 4U;
  /* Wasm instruction 106: br_if */
  /*@ assert branch_7: t3 == 0; */
  /* Wasm instruction 107: local.get */
  /* Wasm instruction 108: i32.const */
  /* Wasm instruction 109: i32.and */
  unsigned int t4 = 5U & 4294967292U;
  /* Wasm instruction 110: local.set */
  /* Wasm instruction 111: i32.const */
  /* Wasm instruction 112: local.set */
  /* Wasm instruction 113: local.get */
  /* Wasm instruction 114: local.get */
  /* Wasm instruction 115: i32.add */
  unsigned int t5 = d + 0U;
  /*@ assert address_normalization: t5 == d + (0); */
  /* Wasm instruction 116: local.tee */
  /* Wasm instruction 117: local.get */
  /* Wasm instruction 118: local.get */
  /* Wasm instruction 119: i32.add */
  unsigned int t6 = s + 0U;
  /*@ assert address_normalization: t6 == s + (0); */
  /* Wasm instruction 120: local.tee */
  /* Wasm instruction 121: i32.load8_u */
  /*@ assert physical_bounds: t6 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t6 && t6 + 1 <= s + n; */
  unsigned int t7 = ((unsigned int)m[t6 + 0U] << 0);
  /* Wasm instruction 122: i32.store8 */
  /*@ assert physical_bounds: t5 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t5 && t5 + 1 <= d + n; */
  m[t5 + 0U] = (unsigned char)(t7 >> 0);
  /* Wasm instruction 123: local.get */
  /* Wasm instruction 124: i32.const */
  /* Wasm instruction 125: i32.add */
  unsigned int t8 = t5 + 1U;
  /*@ assert address_normalization: t8 == d + (1); */
  /* Wasm instruction 126: local.get */
  /* Wasm instruction 127: i32.const */
  /* Wasm instruction 128: i32.add */
  unsigned int t9 = t6 + 1U;
  /*@ assert address_normalization: t9 == s + (1); */
  /* Wasm instruction 129: i32.load8_u */
  /*@ assert physical_bounds: t9 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t9 && t9 + 1 <= s + n; */
  unsigned int t10 = ((unsigned int)m[t9 + 0U] << 0);
  /* Wasm instruction 130: i32.store8 */
  /*@ assert physical_bounds: t8 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t8 && t8 + 1 <= d + n; */
  m[t8 + 0U] = (unsigned char)(t10 >> 0);
  /* Wasm instruction 131: local.get */
  /* Wasm instruction 132: i32.const */
  /* Wasm instruction 133: i32.add */
  unsigned int t11 = t5 + 2U;
  /*@ assert address_normalization: t11 == d + (2); */
  /* Wasm instruction 134: local.get */
  /* Wasm instruction 135: i32.const */
  /* Wasm instruction 136: i32.add */
  unsigned int t12 = t6 + 2U;
  /*@ assert address_normalization: t12 == s + (2); */
  /* Wasm instruction 137: i32.load8_u */
  /*@ assert physical_bounds: t12 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t12 && t12 + 1 <= s + n; */
  unsigned int t13 = ((unsigned int)m[t12 + 0U] << 0);
  /* Wasm instruction 138: i32.store8 */
  /*@ assert physical_bounds: t11 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t11 && t11 + 1 <= d + n; */
  m[t11 + 0U] = (unsigned char)(t13 >> 0);
  /* Wasm instruction 139: local.get */
  /* Wasm instruction 140: i32.const */
  /* Wasm instruction 141: i32.add */
  unsigned int t14 = t5 + 3U;
  /*@ assert address_normalization: t14 == d + (3); */
  /* Wasm instruction 142: local.get */
  /* Wasm instruction 143: i32.const */
  /* Wasm instruction 144: i32.add */
  unsigned int t15 = t6 + 3U;
  /*@ assert address_normalization: t15 == s + (3); */
  /* Wasm instruction 145: i32.load8_u */
  /*@ assert physical_bounds: t15 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t15 && t15 + 1 <= s + n; */
  unsigned int t16 = ((unsigned int)m[t15 + 0U] << 0);
  /* Wasm instruction 146: i32.store8 */
  /*@ assert physical_bounds: t14 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t14 && t14 + 1 <= d + n; */
  m[t14 + 0U] = (unsigned char)(t16 >> 0);
  /* Wasm instruction 147: local.get */
  /* Wasm instruction 148: local.get */
  /* Wasm instruction 149: i32.const */
  /* Wasm instruction 150: i32.add */
  unsigned int t17 = 0U + 4U;
  /* Wasm instruction 151: local.tee */
  /* Wasm instruction 152: i32.ne */
  unsigned int t18 = t4 != t17;
  /* Wasm instruction 153: br_if */
  /*@ assert branch_8: t18 == 0; */
  /* Wasm instruction 154: local.get */
  /* Wasm instruction 155: i32.eqz */
  unsigned int t19 = !t2;
  /* Wasm instruction 156: br_if */
  /*@ assert branch_9: t19 == 0; */
  /* Wasm instruction 157: local.get */
  /* Wasm instruction 158: local.get */
  /* Wasm instruction 159: i32.add */
  unsigned int t20 = s + t17;
  /*@ assert address_normalization: t20 == s + (4); */
  /* Wasm instruction 160: local.set */
  /* Wasm instruction 161: local.get */
  /* Wasm instruction 162: local.get */
  /* Wasm instruction 163: i32.add */
  unsigned int t21 = d + t17;
  /*@ assert address_normalization: t21 == d + (4); */
  /* Wasm instruction 164: local.set */
  /* Wasm instruction 165: local.get */
  /* Wasm instruction 166: local.get */
  /* Wasm instruction 167: i32.load8_u */
  /*@ assert physical_bounds: t20 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t20 && t20 + 1 <= s + n; */
  unsigned int t22 = ((unsigned int)m[t20 + 0U] << 0);
  /* Wasm instruction 168: i32.store8 */
  /*@ assert physical_bounds: t21 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t21 && t21 + 1 <= d + n; */
  m[t21 + 0U] = (unsigned char)(t22 >> 0);
  /* Wasm instruction 169: local.get */
  /* Wasm instruction 170: i32.const */
  /* Wasm instruction 171: i32.add */
  unsigned int t23 = t20 + 1U;
  /*@ assert address_normalization: t23 == s + (5); */
  /* Wasm instruction 172: local.set */
  /* Wasm instruction 173: local.get */
  /* Wasm instruction 174: i32.const */
  /* Wasm instruction 175: i32.add */
  unsigned int t24 = t21 + 1U;
  /*@ assert address_normalization: t24 == d + (5); */
  /* Wasm instruction 176: local.set */
  /* Wasm instruction 177: local.get */
  /* Wasm instruction 178: i32.const */
  /* Wasm instruction 179: i32.add */
  unsigned int t25 = t2 + 4294967295U;
  /* Wasm instruction 180: local.tee */
  /* Wasm instruction 181: br_if */
  /*@ assert branch_10: t25 == 0; */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  /*@ assert copied_byte_3: m[d+3] == \at(m[s+3],Pre); */
  /*@ assert copied_byte_4: m[d+4] == \at(m[s+4],Pre); */
  return d;
}
/*@
  requires specialization: n == 6 && d >= s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
  ensures byte_3: m[d+3] == \old(m[s+3]);
  ensures byte_4: m[d+4] == \old(m[s+4]);
  ensures byte_5: m[d+5] == \old(m[s+5]);
*/
unsigned int move4_6_0(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 6; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 == 0; */
  /* Wasm instruction 4: local.get */
  /* Wasm instruction 5: i32.eqz */
  unsigned int t1 = !6U;
  /* Wasm instruction 6: br_if */
  /*@ assert branch_1: t1 == 0; */
  /* Wasm instruction 7: local.get */
  /* Wasm instruction 8: local.set */
  /* Wasm instruction 9: local.get */
  /* Wasm instruction 10: i32.const */
  /* Wasm instruction 11: i32.and */
  unsigned int t2 = 6U & 3U;
  /* Wasm instruction 12: local.tee */
  /* Wasm instruction 13: i32.eqz */
  unsigned int t3 = !t2;
  /* Wasm instruction 14: br_if */
  /*@ assert branch_2: t3 == 0; */
  /* Wasm instruction 15: local.get */
  /* Wasm instruction 16: i32.const */
  /* Wasm instruction 17: i32.add */
  unsigned int t4 = s + 4294967295U;
  /*@ assert address_normalization: t4 == s + (-1); */
  /* Wasm instruction 18: local.set */
  /* Wasm instruction 19: local.get */
  /* Wasm instruction 20: i32.const */
  /* Wasm instruction 21: i32.add */
  unsigned int t5 = d + 4294967295U;
  /*@ assert address_normalization: t5 == d + (-1); */
  /* Wasm instruction 22: local.set */
  /* Wasm instruction 23: local.get */
  /* Wasm instruction 24: local.set */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: local.get */
  /* Wasm instruction 27: i32.add */
  unsigned int t6 = t5 + 6U;
  /*@ assert address_normalization: t6 == d + (5); */
  /* Wasm instruction 28: local.get */
  /* Wasm instruction 29: local.get */
  /* Wasm instruction 30: i32.add */
  unsigned int t7 = t4 + 6U;
  /*@ assert address_normalization: t7 == s + (5); */
  /* Wasm instruction 31: i32.load8_u */
  /*@ assert physical_bounds: t7 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t7 && t7 + 1 <= s + n; */
  unsigned int t8 = ((unsigned int)m[t7 + 0U] << 0);
  /* Wasm instruction 32: i32.store8 */
  /*@ assert physical_bounds: t6 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t6 && t6 + 1 <= d + n; */
  m[t6 + 0U] = (unsigned char)(t8 >> 0);
  /* Wasm instruction 33: local.get */
  /* Wasm instruction 34: i32.const */
  /* Wasm instruction 35: i32.add */
  unsigned int t9 = 6U + 4294967295U;
  /* Wasm instruction 36: local.set */
  /* Wasm instruction 37: local.get */
  /* Wasm instruction 38: i32.const */
  /* Wasm instruction 39: i32.add */
  unsigned int t10 = t2 + 4294967295U;
  /* Wasm instruction 40: local.tee */
  /* Wasm instruction 41: br_if */
  /*@ assert branch_3: t10 != 0; */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: local.get */
  /* Wasm instruction 27: i32.add */
  unsigned int t11 = t5 + t9;
  /*@ assert address_normalization: t11 == d + (4); */
  /* Wasm instruction 28: local.get */
  /* Wasm instruction 29: local.get */
  /* Wasm instruction 30: i32.add */
  unsigned int t12 = t4 + t9;
  /*@ assert address_normalization: t12 == s + (4); */
  /* Wasm instruction 31: i32.load8_u */
  /*@ assert physical_bounds: t12 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t12 && t12 + 1 <= s + n; */
  unsigned int t13 = ((unsigned int)m[t12 + 0U] << 0);
  /* Wasm instruction 32: i32.store8 */
  /*@ assert physical_bounds: t11 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t11 && t11 + 1 <= d + n; */
  m[t11 + 0U] = (unsigned char)(t13 >> 0);
  /* Wasm instruction 33: local.get */
  /* Wasm instruction 34: i32.const */
  /* Wasm instruction 35: i32.add */
  unsigned int t14 = t9 + 4294967295U;
  /* Wasm instruction 36: local.set */
  /* Wasm instruction 37: local.get */
  /* Wasm instruction 38: i32.const */
  /* Wasm instruction 39: i32.add */
  unsigned int t15 = t10 + 4294967295U;
  /* Wasm instruction 40: local.tee */
  /* Wasm instruction 41: br_if */
  /*@ assert branch_3: t15 == 0; */
  /* Wasm instruction 42: local.get */
  /* Wasm instruction 43: i32.const */
  /* Wasm instruction 44: i32.lt_u */
  unsigned int t16 = 6U < 4U;
  /* Wasm instruction 45: br_if */
  /*@ assert branch_4: t16 == 0; */
  /* Wasm instruction 46: local.get */
  /* Wasm instruction 47: i32.const */
  /* Wasm instruction 48: i32.add */
  unsigned int t17 = s + 4294967292U;
  /*@ assert address_normalization: t17 == s + (-4); */
  /* Wasm instruction 49: local.set */
  /* Wasm instruction 50: local.get */
  /* Wasm instruction 51: i32.const */
  /* Wasm instruction 52: i32.add */
  unsigned int t18 = d + 4294967292U;
  /*@ assert address_normalization: t18 == d + (-4); */
  /* Wasm instruction 53: local.set */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: local.get */
  /* Wasm instruction 56: i32.add */
  unsigned int t19 = t18 + t14;
  /*@ assert address_normalization: t19 == d + (0); */
  /* Wasm instruction 57: local.tee */
  /* Wasm instruction 58: i32.const */
  /* Wasm instruction 59: i32.add */
  unsigned int t20 = t19 + 3U;
  /*@ assert address_normalization: t20 == d + (3); */
  /* Wasm instruction 60: local.get */
  /* Wasm instruction 61: local.get */
  /* Wasm instruction 62: i32.add */
  unsigned int t21 = t17 + t14;
  /*@ assert address_normalization: t21 == s + (0); */
  /* Wasm instruction 63: local.tee */
  /* Wasm instruction 64: i32.const */
  /* Wasm instruction 65: i32.add */
  unsigned int t22 = t21 + 3U;
  /*@ assert address_normalization: t22 == s + (3); */
  /* Wasm instruction 66: i32.load8_u */
  /*@ assert physical_bounds: t22 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t22 && t22 + 1 <= s + n; */
  unsigned int t23 = ((unsigned int)m[t22 + 0U] << 0);
  /* Wasm instruction 67: i32.store8 */
  /*@ assert physical_bounds: t20 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t20 && t20 + 1 <= d + n; */
  m[t20 + 0U] = (unsigned char)(t23 >> 0);
  /* Wasm instruction 68: local.get */
  /* Wasm instruction 69: i32.const */
  /* Wasm instruction 70: i32.add */
  unsigned int t24 = t19 + 2U;
  /*@ assert address_normalization: t24 == d + (2); */
  /* Wasm instruction 71: local.get */
  /* Wasm instruction 72: i32.const */
  /* Wasm instruction 73: i32.add */
  unsigned int t25 = t21 + 2U;
  /*@ assert address_normalization: t25 == s + (2); */
  /* Wasm instruction 74: i32.load8_u */
  /*@ assert physical_bounds: t25 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t25 && t25 + 1 <= s + n; */
  unsigned int t26 = ((unsigned int)m[t25 + 0U] << 0);
  /* Wasm instruction 75: i32.store8 */
  /*@ assert physical_bounds: t24 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t24 && t24 + 1 <= d + n; */
  m[t24 + 0U] = (unsigned char)(t26 >> 0);
  /* Wasm instruction 76: local.get */
  /* Wasm instruction 77: i32.const */
  /* Wasm instruction 78: i32.add */
  unsigned int t27 = t19 + 1U;
  /*@ assert address_normalization: t27 == d + (1); */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: i32.const */
  /* Wasm instruction 81: i32.add */
  unsigned int t28 = t21 + 1U;
  /*@ assert address_normalization: t28 == s + (1); */
  /* Wasm instruction 82: i32.load8_u */
  /*@ assert physical_bounds: t28 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t28 && t28 + 1 <= s + n; */
  unsigned int t29 = ((unsigned int)m[t28 + 0U] << 0);
  /* Wasm instruction 83: i32.store8 */
  /*@ assert physical_bounds: t27 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t27 && t27 + 1 <= d + n; */
  m[t27 + 0U] = (unsigned char)(t29 >> 0);
  /* Wasm instruction 84: local.get */
  /* Wasm instruction 85: local.get */
  /* Wasm instruction 86: i32.load8_u */
  /*@ assert physical_bounds: t21 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t21 && t21 + 1 <= s + n; */
  unsigned int t30 = ((unsigned int)m[t21 + 0U] << 0);
  /* Wasm instruction 87: i32.store8 */
  /*@ assert physical_bounds: t19 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t19 && t19 + 1 <= d + n; */
  m[t19 + 0U] = (unsigned char)(t30 >> 0);
  /* Wasm instruction 88: local.get */
  /* Wasm instruction 89: i32.const */
  /* Wasm instruction 90: i32.add */
  unsigned int t31 = t14 + 4294967292U;
  /* Wasm instruction 91: local.tee */
  /* Wasm instruction 92: br_if */
  /*@ assert branch_5: t31 == 0; */
  /* Wasm instruction 93: br */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  /*@ assert copied_byte_3: m[d+3] == \at(m[s+3],Pre); */
  /*@ assert copied_byte_4: m[d+4] == \at(m[s+4],Pre); */
  /*@ assert copied_byte_5: m[d+5] == \at(m[s+5],Pre); */
  return d;
}
/*@
  requires specialization: n == 6 && d < s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
  ensures byte_3: m[d+3] == \old(m[s+3]);
  ensures byte_4: m[d+4] == \old(m[s+4]);
  ensures byte_5: m[d+5] == \old(m[s+5]);
*/
unsigned int move4_6_1(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 6; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 != 0; */
  /* Wasm instruction 94: local.get */
  /* Wasm instruction 95: i32.eqz */
  unsigned int t1 = !6U;
  /* Wasm instruction 96: br_if */
  /*@ assert branch_6: t1 == 0; */
  /* Wasm instruction 97: local.get */
  /* Wasm instruction 98: i32.const */
  /* Wasm instruction 99: i32.and */
  unsigned int t2 = 6U & 3U;
  /* Wasm instruction 100: local.set */
  /* Wasm instruction 101: i32.const */
  /* Wasm instruction 102: local.set */
  /* Wasm instruction 103: local.get */
  /* Wasm instruction 104: i32.const */
  /* Wasm instruction 105: i32.lt_u */
  unsigned int t3 = 6U < 4U;
  /* Wasm instruction 106: br_if */
  /*@ assert branch_7: t3 == 0; */
  /* Wasm instruction 107: local.get */
  /* Wasm instruction 108: i32.const */
  /* Wasm instruction 109: i32.and */
  unsigned int t4 = 6U & 4294967292U;
  /* Wasm instruction 110: local.set */
  /* Wasm instruction 111: i32.const */
  /* Wasm instruction 112: local.set */
  /* Wasm instruction 113: local.get */
  /* Wasm instruction 114: local.get */
  /* Wasm instruction 115: i32.add */
  unsigned int t5 = d + 0U;
  /*@ assert address_normalization: t5 == d + (0); */
  /* Wasm instruction 116: local.tee */
  /* Wasm instruction 117: local.get */
  /* Wasm instruction 118: local.get */
  /* Wasm instruction 119: i32.add */
  unsigned int t6 = s + 0U;
  /*@ assert address_normalization: t6 == s + (0); */
  /* Wasm instruction 120: local.tee */
  /* Wasm instruction 121: i32.load8_u */
  /*@ assert physical_bounds: t6 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t6 && t6 + 1 <= s + n; */
  unsigned int t7 = ((unsigned int)m[t6 + 0U] << 0);
  /* Wasm instruction 122: i32.store8 */
  /*@ assert physical_bounds: t5 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t5 && t5 + 1 <= d + n; */
  m[t5 + 0U] = (unsigned char)(t7 >> 0);
  /* Wasm instruction 123: local.get */
  /* Wasm instruction 124: i32.const */
  /* Wasm instruction 125: i32.add */
  unsigned int t8 = t5 + 1U;
  /*@ assert address_normalization: t8 == d + (1); */
  /* Wasm instruction 126: local.get */
  /* Wasm instruction 127: i32.const */
  /* Wasm instruction 128: i32.add */
  unsigned int t9 = t6 + 1U;
  /*@ assert address_normalization: t9 == s + (1); */
  /* Wasm instruction 129: i32.load8_u */
  /*@ assert physical_bounds: t9 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t9 && t9 + 1 <= s + n; */
  unsigned int t10 = ((unsigned int)m[t9 + 0U] << 0);
  /* Wasm instruction 130: i32.store8 */
  /*@ assert physical_bounds: t8 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t8 && t8 + 1 <= d + n; */
  m[t8 + 0U] = (unsigned char)(t10 >> 0);
  /* Wasm instruction 131: local.get */
  /* Wasm instruction 132: i32.const */
  /* Wasm instruction 133: i32.add */
  unsigned int t11 = t5 + 2U;
  /*@ assert address_normalization: t11 == d + (2); */
  /* Wasm instruction 134: local.get */
  /* Wasm instruction 135: i32.const */
  /* Wasm instruction 136: i32.add */
  unsigned int t12 = t6 + 2U;
  /*@ assert address_normalization: t12 == s + (2); */
  /* Wasm instruction 137: i32.load8_u */
  /*@ assert physical_bounds: t12 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t12 && t12 + 1 <= s + n; */
  unsigned int t13 = ((unsigned int)m[t12 + 0U] << 0);
  /* Wasm instruction 138: i32.store8 */
  /*@ assert physical_bounds: t11 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t11 && t11 + 1 <= d + n; */
  m[t11 + 0U] = (unsigned char)(t13 >> 0);
  /* Wasm instruction 139: local.get */
  /* Wasm instruction 140: i32.const */
  /* Wasm instruction 141: i32.add */
  unsigned int t14 = t5 + 3U;
  /*@ assert address_normalization: t14 == d + (3); */
  /* Wasm instruction 142: local.get */
  /* Wasm instruction 143: i32.const */
  /* Wasm instruction 144: i32.add */
  unsigned int t15 = t6 + 3U;
  /*@ assert address_normalization: t15 == s + (3); */
  /* Wasm instruction 145: i32.load8_u */
  /*@ assert physical_bounds: t15 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t15 && t15 + 1 <= s + n; */
  unsigned int t16 = ((unsigned int)m[t15 + 0U] << 0);
  /* Wasm instruction 146: i32.store8 */
  /*@ assert physical_bounds: t14 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t14 && t14 + 1 <= d + n; */
  m[t14 + 0U] = (unsigned char)(t16 >> 0);
  /* Wasm instruction 147: local.get */
  /* Wasm instruction 148: local.get */
  /* Wasm instruction 149: i32.const */
  /* Wasm instruction 150: i32.add */
  unsigned int t17 = 0U + 4U;
  /* Wasm instruction 151: local.tee */
  /* Wasm instruction 152: i32.ne */
  unsigned int t18 = t4 != t17;
  /* Wasm instruction 153: br_if */
  /*@ assert branch_8: t18 == 0; */
  /* Wasm instruction 154: local.get */
  /* Wasm instruction 155: i32.eqz */
  unsigned int t19 = !t2;
  /* Wasm instruction 156: br_if */
  /*@ assert branch_9: t19 == 0; */
  /* Wasm instruction 157: local.get */
  /* Wasm instruction 158: local.get */
  /* Wasm instruction 159: i32.add */
  unsigned int t20 = s + t17;
  /*@ assert address_normalization: t20 == s + (4); */
  /* Wasm instruction 160: local.set */
  /* Wasm instruction 161: local.get */
  /* Wasm instruction 162: local.get */
  /* Wasm instruction 163: i32.add */
  unsigned int t21 = d + t17;
  /*@ assert address_normalization: t21 == d + (4); */
  /* Wasm instruction 164: local.set */
  /* Wasm instruction 165: local.get */
  /* Wasm instruction 166: local.get */
  /* Wasm instruction 167: i32.load8_u */
  /*@ assert physical_bounds: t20 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t20 && t20 + 1 <= s + n; */
  unsigned int t22 = ((unsigned int)m[t20 + 0U] << 0);
  /* Wasm instruction 168: i32.store8 */
  /*@ assert physical_bounds: t21 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t21 && t21 + 1 <= d + n; */
  m[t21 + 0U] = (unsigned char)(t22 >> 0);
  /* Wasm instruction 169: local.get */
  /* Wasm instruction 170: i32.const */
  /* Wasm instruction 171: i32.add */
  unsigned int t23 = t20 + 1U;
  /*@ assert address_normalization: t23 == s + (5); */
  /* Wasm instruction 172: local.set */
  /* Wasm instruction 173: local.get */
  /* Wasm instruction 174: i32.const */
  /* Wasm instruction 175: i32.add */
  unsigned int t24 = t21 + 1U;
  /*@ assert address_normalization: t24 == d + (5); */
  /* Wasm instruction 176: local.set */
  /* Wasm instruction 177: local.get */
  /* Wasm instruction 178: i32.const */
  /* Wasm instruction 179: i32.add */
  unsigned int t25 = t2 + 4294967295U;
  /* Wasm instruction 180: local.tee */
  /* Wasm instruction 181: br_if */
  /*@ assert branch_10: t25 != 0; */
  /* Wasm instruction 165: local.get */
  /* Wasm instruction 166: local.get */
  /* Wasm instruction 167: i32.load8_u */
  /*@ assert physical_bounds: t23 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t23 && t23 + 1 <= s + n; */
  unsigned int t26 = ((unsigned int)m[t23 + 0U] << 0);
  /* Wasm instruction 168: i32.store8 */
  /*@ assert physical_bounds: t24 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t24 && t24 + 1 <= d + n; */
  m[t24 + 0U] = (unsigned char)(t26 >> 0);
  /* Wasm instruction 169: local.get */
  /* Wasm instruction 170: i32.const */
  /* Wasm instruction 171: i32.add */
  unsigned int t27 = t23 + 1U;
  /*@ assert address_normalization: t27 == s + (6); */
  /* Wasm instruction 172: local.set */
  /* Wasm instruction 173: local.get */
  /* Wasm instruction 174: i32.const */
  /* Wasm instruction 175: i32.add */
  unsigned int t28 = t24 + 1U;
  /*@ assert address_normalization: t28 == d + (6); */
  /* Wasm instruction 176: local.set */
  /* Wasm instruction 177: local.get */
  /* Wasm instruction 178: i32.const */
  /* Wasm instruction 179: i32.add */
  unsigned int t29 = t25 + 4294967295U;
  /* Wasm instruction 180: local.tee */
  /* Wasm instruction 181: br_if */
  /*@ assert branch_10: t29 == 0; */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  /*@ assert copied_byte_3: m[d+3] == \at(m[s+3],Pre); */
  /*@ assert copied_byte_4: m[d+4] == \at(m[s+4],Pre); */
  /*@ assert copied_byte_5: m[d+5] == \at(m[s+5],Pre); */
  return d;
}
/*@
  requires specialization: n == 7 && d >= s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
  ensures byte_3: m[d+3] == \old(m[s+3]);
  ensures byte_4: m[d+4] == \old(m[s+4]);
  ensures byte_5: m[d+5] == \old(m[s+5]);
  ensures byte_6: m[d+6] == \old(m[s+6]);
*/
unsigned int move4_7_0(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 7; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 == 0; */
  /* Wasm instruction 4: local.get */
  /* Wasm instruction 5: i32.eqz */
  unsigned int t1 = !7U;
  /* Wasm instruction 6: br_if */
  /*@ assert branch_1: t1 == 0; */
  /* Wasm instruction 7: local.get */
  /* Wasm instruction 8: local.set */
  /* Wasm instruction 9: local.get */
  /* Wasm instruction 10: i32.const */
  /* Wasm instruction 11: i32.and */
  unsigned int t2 = 7U & 3U;
  /* Wasm instruction 12: local.tee */
  /* Wasm instruction 13: i32.eqz */
  unsigned int t3 = !t2;
  /* Wasm instruction 14: br_if */
  /*@ assert branch_2: t3 == 0; */
  /* Wasm instruction 15: local.get */
  /* Wasm instruction 16: i32.const */
  /* Wasm instruction 17: i32.add */
  unsigned int t4 = s + 4294967295U;
  /*@ assert address_normalization: t4 == s + (-1); */
  /* Wasm instruction 18: local.set */
  /* Wasm instruction 19: local.get */
  /* Wasm instruction 20: i32.const */
  /* Wasm instruction 21: i32.add */
  unsigned int t5 = d + 4294967295U;
  /*@ assert address_normalization: t5 == d + (-1); */
  /* Wasm instruction 22: local.set */
  /* Wasm instruction 23: local.get */
  /* Wasm instruction 24: local.set */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: local.get */
  /* Wasm instruction 27: i32.add */
  unsigned int t6 = t5 + 7U;
  /*@ assert address_normalization: t6 == d + (6); */
  /* Wasm instruction 28: local.get */
  /* Wasm instruction 29: local.get */
  /* Wasm instruction 30: i32.add */
  unsigned int t7 = t4 + 7U;
  /*@ assert address_normalization: t7 == s + (6); */
  /* Wasm instruction 31: i32.load8_u */
  /*@ assert physical_bounds: t7 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t7 && t7 + 1 <= s + n; */
  unsigned int t8 = ((unsigned int)m[t7 + 0U] << 0);
  /* Wasm instruction 32: i32.store8 */
  /*@ assert physical_bounds: t6 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t6 && t6 + 1 <= d + n; */
  m[t6 + 0U] = (unsigned char)(t8 >> 0);
  /* Wasm instruction 33: local.get */
  /* Wasm instruction 34: i32.const */
  /* Wasm instruction 35: i32.add */
  unsigned int t9 = 7U + 4294967295U;
  /* Wasm instruction 36: local.set */
  /* Wasm instruction 37: local.get */
  /* Wasm instruction 38: i32.const */
  /* Wasm instruction 39: i32.add */
  unsigned int t10 = t2 + 4294967295U;
  /* Wasm instruction 40: local.tee */
  /* Wasm instruction 41: br_if */
  /*@ assert branch_3: t10 != 0; */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: local.get */
  /* Wasm instruction 27: i32.add */
  unsigned int t11 = t5 + t9;
  /*@ assert address_normalization: t11 == d + (5); */
  /* Wasm instruction 28: local.get */
  /* Wasm instruction 29: local.get */
  /* Wasm instruction 30: i32.add */
  unsigned int t12 = t4 + t9;
  /*@ assert address_normalization: t12 == s + (5); */
  /* Wasm instruction 31: i32.load8_u */
  /*@ assert physical_bounds: t12 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t12 && t12 + 1 <= s + n; */
  unsigned int t13 = ((unsigned int)m[t12 + 0U] << 0);
  /* Wasm instruction 32: i32.store8 */
  /*@ assert physical_bounds: t11 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t11 && t11 + 1 <= d + n; */
  m[t11 + 0U] = (unsigned char)(t13 >> 0);
  /* Wasm instruction 33: local.get */
  /* Wasm instruction 34: i32.const */
  /* Wasm instruction 35: i32.add */
  unsigned int t14 = t9 + 4294967295U;
  /* Wasm instruction 36: local.set */
  /* Wasm instruction 37: local.get */
  /* Wasm instruction 38: i32.const */
  /* Wasm instruction 39: i32.add */
  unsigned int t15 = t10 + 4294967295U;
  /* Wasm instruction 40: local.tee */
  /* Wasm instruction 41: br_if */
  /*@ assert branch_3: t15 != 0; */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: local.get */
  /* Wasm instruction 27: i32.add */
  unsigned int t16 = t5 + t14;
  /*@ assert address_normalization: t16 == d + (4); */
  /* Wasm instruction 28: local.get */
  /* Wasm instruction 29: local.get */
  /* Wasm instruction 30: i32.add */
  unsigned int t17 = t4 + t14;
  /*@ assert address_normalization: t17 == s + (4); */
  /* Wasm instruction 31: i32.load8_u */
  /*@ assert physical_bounds: t17 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t17 && t17 + 1 <= s + n; */
  unsigned int t18 = ((unsigned int)m[t17 + 0U] << 0);
  /* Wasm instruction 32: i32.store8 */
  /*@ assert physical_bounds: t16 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t16 && t16 + 1 <= d + n; */
  m[t16 + 0U] = (unsigned char)(t18 >> 0);
  /* Wasm instruction 33: local.get */
  /* Wasm instruction 34: i32.const */
  /* Wasm instruction 35: i32.add */
  unsigned int t19 = t14 + 4294967295U;
  /* Wasm instruction 36: local.set */
  /* Wasm instruction 37: local.get */
  /* Wasm instruction 38: i32.const */
  /* Wasm instruction 39: i32.add */
  unsigned int t20 = t15 + 4294967295U;
  /* Wasm instruction 40: local.tee */
  /* Wasm instruction 41: br_if */
  /*@ assert branch_3: t20 == 0; */
  /* Wasm instruction 42: local.get */
  /* Wasm instruction 43: i32.const */
  /* Wasm instruction 44: i32.lt_u */
  unsigned int t21 = 7U < 4U;
  /* Wasm instruction 45: br_if */
  /*@ assert branch_4: t21 == 0; */
  /* Wasm instruction 46: local.get */
  /* Wasm instruction 47: i32.const */
  /* Wasm instruction 48: i32.add */
  unsigned int t22 = s + 4294967292U;
  /*@ assert address_normalization: t22 == s + (-4); */
  /* Wasm instruction 49: local.set */
  /* Wasm instruction 50: local.get */
  /* Wasm instruction 51: i32.const */
  /* Wasm instruction 52: i32.add */
  unsigned int t23 = d + 4294967292U;
  /*@ assert address_normalization: t23 == d + (-4); */
  /* Wasm instruction 53: local.set */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: local.get */
  /* Wasm instruction 56: i32.add */
  unsigned int t24 = t23 + t19;
  /*@ assert address_normalization: t24 == d + (0); */
  /* Wasm instruction 57: local.tee */
  /* Wasm instruction 58: i32.const */
  /* Wasm instruction 59: i32.add */
  unsigned int t25 = t24 + 3U;
  /*@ assert address_normalization: t25 == d + (3); */
  /* Wasm instruction 60: local.get */
  /* Wasm instruction 61: local.get */
  /* Wasm instruction 62: i32.add */
  unsigned int t26 = t22 + t19;
  /*@ assert address_normalization: t26 == s + (0); */
  /* Wasm instruction 63: local.tee */
  /* Wasm instruction 64: i32.const */
  /* Wasm instruction 65: i32.add */
  unsigned int t27 = t26 + 3U;
  /*@ assert address_normalization: t27 == s + (3); */
  /* Wasm instruction 66: i32.load8_u */
  /*@ assert physical_bounds: t27 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t27 && t27 + 1 <= s + n; */
  unsigned int t28 = ((unsigned int)m[t27 + 0U] << 0);
  /* Wasm instruction 67: i32.store8 */
  /*@ assert physical_bounds: t25 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t25 && t25 + 1 <= d + n; */
  m[t25 + 0U] = (unsigned char)(t28 >> 0);
  /* Wasm instruction 68: local.get */
  /* Wasm instruction 69: i32.const */
  /* Wasm instruction 70: i32.add */
  unsigned int t29 = t24 + 2U;
  /*@ assert address_normalization: t29 == d + (2); */
  /* Wasm instruction 71: local.get */
  /* Wasm instruction 72: i32.const */
  /* Wasm instruction 73: i32.add */
  unsigned int t30 = t26 + 2U;
  /*@ assert address_normalization: t30 == s + (2); */
  /* Wasm instruction 74: i32.load8_u */
  /*@ assert physical_bounds: t30 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t30 && t30 + 1 <= s + n; */
  unsigned int t31 = ((unsigned int)m[t30 + 0U] << 0);
  /* Wasm instruction 75: i32.store8 */
  /*@ assert physical_bounds: t29 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t29 && t29 + 1 <= d + n; */
  m[t29 + 0U] = (unsigned char)(t31 >> 0);
  /* Wasm instruction 76: local.get */
  /* Wasm instruction 77: i32.const */
  /* Wasm instruction 78: i32.add */
  unsigned int t32 = t24 + 1U;
  /*@ assert address_normalization: t32 == d + (1); */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: i32.const */
  /* Wasm instruction 81: i32.add */
  unsigned int t33 = t26 + 1U;
  /*@ assert address_normalization: t33 == s + (1); */
  /* Wasm instruction 82: i32.load8_u */
  /*@ assert physical_bounds: t33 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t33 && t33 + 1 <= s + n; */
  unsigned int t34 = ((unsigned int)m[t33 + 0U] << 0);
  /* Wasm instruction 83: i32.store8 */
  /*@ assert physical_bounds: t32 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t32 && t32 + 1 <= d + n; */
  m[t32 + 0U] = (unsigned char)(t34 >> 0);
  /* Wasm instruction 84: local.get */
  /* Wasm instruction 85: local.get */
  /* Wasm instruction 86: i32.load8_u */
  /*@ assert physical_bounds: t26 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t26 && t26 + 1 <= s + n; */
  unsigned int t35 = ((unsigned int)m[t26 + 0U] << 0);
  /* Wasm instruction 87: i32.store8 */
  /*@ assert physical_bounds: t24 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t24 && t24 + 1 <= d + n; */
  m[t24 + 0U] = (unsigned char)(t35 >> 0);
  /* Wasm instruction 88: local.get */
  /* Wasm instruction 89: i32.const */
  /* Wasm instruction 90: i32.add */
  unsigned int t36 = t19 + 4294967292U;
  /* Wasm instruction 91: local.tee */
  /* Wasm instruction 92: br_if */
  /*@ assert branch_5: t36 == 0; */
  /* Wasm instruction 93: br */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  /*@ assert copied_byte_3: m[d+3] == \at(m[s+3],Pre); */
  /*@ assert copied_byte_4: m[d+4] == \at(m[s+4],Pre); */
  /*@ assert copied_byte_5: m[d+5] == \at(m[s+5],Pre); */
  /*@ assert copied_byte_6: m[d+6] == \at(m[s+6],Pre); */
  return d;
}
/*@
  requires specialization: n == 7 && d < s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
  ensures byte_3: m[d+3] == \old(m[s+3]);
  ensures byte_4: m[d+4] == \old(m[s+4]);
  ensures byte_5: m[d+5] == \old(m[s+5]);
  ensures byte_6: m[d+6] == \old(m[s+6]);
*/
unsigned int move4_7_1(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 7; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 != 0; */
  /* Wasm instruction 94: local.get */
  /* Wasm instruction 95: i32.eqz */
  unsigned int t1 = !7U;
  /* Wasm instruction 96: br_if */
  /*@ assert branch_6: t1 == 0; */
  /* Wasm instruction 97: local.get */
  /* Wasm instruction 98: i32.const */
  /* Wasm instruction 99: i32.and */
  unsigned int t2 = 7U & 3U;
  /* Wasm instruction 100: local.set */
  /* Wasm instruction 101: i32.const */
  /* Wasm instruction 102: local.set */
  /* Wasm instruction 103: local.get */
  /* Wasm instruction 104: i32.const */
  /* Wasm instruction 105: i32.lt_u */
  unsigned int t3 = 7U < 4U;
  /* Wasm instruction 106: br_if */
  /*@ assert branch_7: t3 == 0; */
  /* Wasm instruction 107: local.get */
  /* Wasm instruction 108: i32.const */
  /* Wasm instruction 109: i32.and */
  unsigned int t4 = 7U & 4294967292U;
  /* Wasm instruction 110: local.set */
  /* Wasm instruction 111: i32.const */
  /* Wasm instruction 112: local.set */
  /* Wasm instruction 113: local.get */
  /* Wasm instruction 114: local.get */
  /* Wasm instruction 115: i32.add */
  unsigned int t5 = d + 0U;
  /*@ assert address_normalization: t5 == d + (0); */
  /* Wasm instruction 116: local.tee */
  /* Wasm instruction 117: local.get */
  /* Wasm instruction 118: local.get */
  /* Wasm instruction 119: i32.add */
  unsigned int t6 = s + 0U;
  /*@ assert address_normalization: t6 == s + (0); */
  /* Wasm instruction 120: local.tee */
  /* Wasm instruction 121: i32.load8_u */
  /*@ assert physical_bounds: t6 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t6 && t6 + 1 <= s + n; */
  unsigned int t7 = ((unsigned int)m[t6 + 0U] << 0);
  /* Wasm instruction 122: i32.store8 */
  /*@ assert physical_bounds: t5 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t5 && t5 + 1 <= d + n; */
  m[t5 + 0U] = (unsigned char)(t7 >> 0);
  /* Wasm instruction 123: local.get */
  /* Wasm instruction 124: i32.const */
  /* Wasm instruction 125: i32.add */
  unsigned int t8 = t5 + 1U;
  /*@ assert address_normalization: t8 == d + (1); */
  /* Wasm instruction 126: local.get */
  /* Wasm instruction 127: i32.const */
  /* Wasm instruction 128: i32.add */
  unsigned int t9 = t6 + 1U;
  /*@ assert address_normalization: t9 == s + (1); */
  /* Wasm instruction 129: i32.load8_u */
  /*@ assert physical_bounds: t9 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t9 && t9 + 1 <= s + n; */
  unsigned int t10 = ((unsigned int)m[t9 + 0U] << 0);
  /* Wasm instruction 130: i32.store8 */
  /*@ assert physical_bounds: t8 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t8 && t8 + 1 <= d + n; */
  m[t8 + 0U] = (unsigned char)(t10 >> 0);
  /* Wasm instruction 131: local.get */
  /* Wasm instruction 132: i32.const */
  /* Wasm instruction 133: i32.add */
  unsigned int t11 = t5 + 2U;
  /*@ assert address_normalization: t11 == d + (2); */
  /* Wasm instruction 134: local.get */
  /* Wasm instruction 135: i32.const */
  /* Wasm instruction 136: i32.add */
  unsigned int t12 = t6 + 2U;
  /*@ assert address_normalization: t12 == s + (2); */
  /* Wasm instruction 137: i32.load8_u */
  /*@ assert physical_bounds: t12 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t12 && t12 + 1 <= s + n; */
  unsigned int t13 = ((unsigned int)m[t12 + 0U] << 0);
  /* Wasm instruction 138: i32.store8 */
  /*@ assert physical_bounds: t11 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t11 && t11 + 1 <= d + n; */
  m[t11 + 0U] = (unsigned char)(t13 >> 0);
  /* Wasm instruction 139: local.get */
  /* Wasm instruction 140: i32.const */
  /* Wasm instruction 141: i32.add */
  unsigned int t14 = t5 + 3U;
  /*@ assert address_normalization: t14 == d + (3); */
  /* Wasm instruction 142: local.get */
  /* Wasm instruction 143: i32.const */
  /* Wasm instruction 144: i32.add */
  unsigned int t15 = t6 + 3U;
  /*@ assert address_normalization: t15 == s + (3); */
  /* Wasm instruction 145: i32.load8_u */
  /*@ assert physical_bounds: t15 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t15 && t15 + 1 <= s + n; */
  unsigned int t16 = ((unsigned int)m[t15 + 0U] << 0);
  /* Wasm instruction 146: i32.store8 */
  /*@ assert physical_bounds: t14 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t14 && t14 + 1 <= d + n; */
  m[t14 + 0U] = (unsigned char)(t16 >> 0);
  /* Wasm instruction 147: local.get */
  /* Wasm instruction 148: local.get */
  /* Wasm instruction 149: i32.const */
  /* Wasm instruction 150: i32.add */
  unsigned int t17 = 0U + 4U;
  /* Wasm instruction 151: local.tee */
  /* Wasm instruction 152: i32.ne */
  unsigned int t18 = t4 != t17;
  /* Wasm instruction 153: br_if */
  /*@ assert branch_8: t18 == 0; */
  /* Wasm instruction 154: local.get */
  /* Wasm instruction 155: i32.eqz */
  unsigned int t19 = !t2;
  /* Wasm instruction 156: br_if */
  /*@ assert branch_9: t19 == 0; */
  /* Wasm instruction 157: local.get */
  /* Wasm instruction 158: local.get */
  /* Wasm instruction 159: i32.add */
  unsigned int t20 = s + t17;
  /*@ assert address_normalization: t20 == s + (4); */
  /* Wasm instruction 160: local.set */
  /* Wasm instruction 161: local.get */
  /* Wasm instruction 162: local.get */
  /* Wasm instruction 163: i32.add */
  unsigned int t21 = d + t17;
  /*@ assert address_normalization: t21 == d + (4); */
  /* Wasm instruction 164: local.set */
  /* Wasm instruction 165: local.get */
  /* Wasm instruction 166: local.get */
  /* Wasm instruction 167: i32.load8_u */
  /*@ assert physical_bounds: t20 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t20 && t20 + 1 <= s + n; */
  unsigned int t22 = ((unsigned int)m[t20 + 0U] << 0);
  /* Wasm instruction 168: i32.store8 */
  /*@ assert physical_bounds: t21 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t21 && t21 + 1 <= d + n; */
  m[t21 + 0U] = (unsigned char)(t22 >> 0);
  /* Wasm instruction 169: local.get */
  /* Wasm instruction 170: i32.const */
  /* Wasm instruction 171: i32.add */
  unsigned int t23 = t20 + 1U;
  /*@ assert address_normalization: t23 == s + (5); */
  /* Wasm instruction 172: local.set */
  /* Wasm instruction 173: local.get */
  /* Wasm instruction 174: i32.const */
  /* Wasm instruction 175: i32.add */
  unsigned int t24 = t21 + 1U;
  /*@ assert address_normalization: t24 == d + (5); */
  /* Wasm instruction 176: local.set */
  /* Wasm instruction 177: local.get */
  /* Wasm instruction 178: i32.const */
  /* Wasm instruction 179: i32.add */
  unsigned int t25 = t2 + 4294967295U;
  /* Wasm instruction 180: local.tee */
  /* Wasm instruction 181: br_if */
  /*@ assert branch_10: t25 != 0; */
  /* Wasm instruction 165: local.get */
  /* Wasm instruction 166: local.get */
  /* Wasm instruction 167: i32.load8_u */
  /*@ assert physical_bounds: t23 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t23 && t23 + 1 <= s + n; */
  unsigned int t26 = ((unsigned int)m[t23 + 0U] << 0);
  /* Wasm instruction 168: i32.store8 */
  /*@ assert physical_bounds: t24 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t24 && t24 + 1 <= d + n; */
  m[t24 + 0U] = (unsigned char)(t26 >> 0);
  /* Wasm instruction 169: local.get */
  /* Wasm instruction 170: i32.const */
  /* Wasm instruction 171: i32.add */
  unsigned int t27 = t23 + 1U;
  /*@ assert address_normalization: t27 == s + (6); */
  /* Wasm instruction 172: local.set */
  /* Wasm instruction 173: local.get */
  /* Wasm instruction 174: i32.const */
  /* Wasm instruction 175: i32.add */
  unsigned int t28 = t24 + 1U;
  /*@ assert address_normalization: t28 == d + (6); */
  /* Wasm instruction 176: local.set */
  /* Wasm instruction 177: local.get */
  /* Wasm instruction 178: i32.const */
  /* Wasm instruction 179: i32.add */
  unsigned int t29 = t25 + 4294967295U;
  /* Wasm instruction 180: local.tee */
  /* Wasm instruction 181: br_if */
  /*@ assert branch_10: t29 != 0; */
  /* Wasm instruction 165: local.get */
  /* Wasm instruction 166: local.get */
  /* Wasm instruction 167: i32.load8_u */
  /*@ assert physical_bounds: t27 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t27 && t27 + 1 <= s + n; */
  unsigned int t30 = ((unsigned int)m[t27 + 0U] << 0);
  /* Wasm instruction 168: i32.store8 */
  /*@ assert physical_bounds: t28 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t28 && t28 + 1 <= d + n; */
  m[t28 + 0U] = (unsigned char)(t30 >> 0);
  /* Wasm instruction 169: local.get */
  /* Wasm instruction 170: i32.const */
  /* Wasm instruction 171: i32.add */
  unsigned int t31 = t27 + 1U;
  /*@ assert address_normalization: t31 == s + (7); */
  /* Wasm instruction 172: local.set */
  /* Wasm instruction 173: local.get */
  /* Wasm instruction 174: i32.const */
  /* Wasm instruction 175: i32.add */
  unsigned int t32 = t28 + 1U;
  /*@ assert address_normalization: t32 == d + (7); */
  /* Wasm instruction 176: local.set */
  /* Wasm instruction 177: local.get */
  /* Wasm instruction 178: i32.const */
  /* Wasm instruction 179: i32.add */
  unsigned int t33 = t29 + 4294967295U;
  /* Wasm instruction 180: local.tee */
  /* Wasm instruction 181: br_if */
  /*@ assert branch_10: t33 == 0; */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  /*@ assert copied_byte_3: m[d+3] == \at(m[s+3],Pre); */
  /*@ assert copied_byte_4: m[d+4] == \at(m[s+4],Pre); */
  /*@ assert copied_byte_5: m[d+5] == \at(m[s+5],Pre); */
  /*@ assert copied_byte_6: m[d+6] == \at(m[s+6],Pre); */
  return d;
}
/*@
  requires specialization: n == 8 && d >= s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
  ensures byte_3: m[d+3] == \old(m[s+3]);
  ensures byte_4: m[d+4] == \old(m[s+4]);
  ensures byte_5: m[d+5] == \old(m[s+5]);
  ensures byte_6: m[d+6] == \old(m[s+6]);
  ensures byte_7: m[d+7] == \old(m[s+7]);
*/
unsigned int move4_8_0(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 8; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 == 0; */
  /* Wasm instruction 4: local.get */
  /* Wasm instruction 5: i32.eqz */
  unsigned int t1 = !8U;
  /* Wasm instruction 6: br_if */
  /*@ assert branch_1: t1 == 0; */
  /* Wasm instruction 7: local.get */
  /* Wasm instruction 8: local.set */
  /* Wasm instruction 9: local.get */
  /* Wasm instruction 10: i32.const */
  /* Wasm instruction 11: i32.and */
  unsigned int t2 = 8U & 3U;
  /* Wasm instruction 12: local.tee */
  /* Wasm instruction 13: i32.eqz */
  unsigned int t3 = !t2;
  /* Wasm instruction 14: br_if */
  /*@ assert branch_2: t3 != 0; */
  /* Wasm instruction 42: local.get */
  /* Wasm instruction 43: i32.const */
  /* Wasm instruction 44: i32.lt_u */
  unsigned int t4 = 8U < 4U;
  /* Wasm instruction 45: br_if */
  /*@ assert branch_4: t4 == 0; */
  /* Wasm instruction 46: local.get */
  /* Wasm instruction 47: i32.const */
  /* Wasm instruction 48: i32.add */
  unsigned int t5 = s + 4294967292U;
  /*@ assert address_normalization: t5 == s + (-4); */
  /* Wasm instruction 49: local.set */
  /* Wasm instruction 50: local.get */
  /* Wasm instruction 51: i32.const */
  /* Wasm instruction 52: i32.add */
  unsigned int t6 = d + 4294967292U;
  /*@ assert address_normalization: t6 == d + (-4); */
  /* Wasm instruction 53: local.set */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: local.get */
  /* Wasm instruction 56: i32.add */
  unsigned int t7 = t6 + 8U;
  /*@ assert address_normalization: t7 == d + (4); */
  /* Wasm instruction 57: local.tee */
  /* Wasm instruction 58: i32.const */
  /* Wasm instruction 59: i32.add */
  unsigned int t8 = t7 + 3U;
  /*@ assert address_normalization: t8 == d + (7); */
  /* Wasm instruction 60: local.get */
  /* Wasm instruction 61: local.get */
  /* Wasm instruction 62: i32.add */
  unsigned int t9 = t5 + 8U;
  /*@ assert address_normalization: t9 == s + (4); */
  /* Wasm instruction 63: local.tee */
  /* Wasm instruction 64: i32.const */
  /* Wasm instruction 65: i32.add */
  unsigned int t10 = t9 + 3U;
  /*@ assert address_normalization: t10 == s + (7); */
  /* Wasm instruction 66: i32.load8_u */
  /*@ assert physical_bounds: t10 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t10 && t10 + 1 <= s + n; */
  unsigned int t11 = ((unsigned int)m[t10 + 0U] << 0);
  /* Wasm instruction 67: i32.store8 */
  /*@ assert physical_bounds: t8 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t8 && t8 + 1 <= d + n; */
  m[t8 + 0U] = (unsigned char)(t11 >> 0);
  /* Wasm instruction 68: local.get */
  /* Wasm instruction 69: i32.const */
  /* Wasm instruction 70: i32.add */
  unsigned int t12 = t7 + 2U;
  /*@ assert address_normalization: t12 == d + (6); */
  /* Wasm instruction 71: local.get */
  /* Wasm instruction 72: i32.const */
  /* Wasm instruction 73: i32.add */
  unsigned int t13 = t9 + 2U;
  /*@ assert address_normalization: t13 == s + (6); */
  /* Wasm instruction 74: i32.load8_u */
  /*@ assert physical_bounds: t13 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t13 && t13 + 1 <= s + n; */
  unsigned int t14 = ((unsigned int)m[t13 + 0U] << 0);
  /* Wasm instruction 75: i32.store8 */
  /*@ assert physical_bounds: t12 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t12 && t12 + 1 <= d + n; */
  m[t12 + 0U] = (unsigned char)(t14 >> 0);
  /* Wasm instruction 76: local.get */
  /* Wasm instruction 77: i32.const */
  /* Wasm instruction 78: i32.add */
  unsigned int t15 = t7 + 1U;
  /*@ assert address_normalization: t15 == d + (5); */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: i32.const */
  /* Wasm instruction 81: i32.add */
  unsigned int t16 = t9 + 1U;
  /*@ assert address_normalization: t16 == s + (5); */
  /* Wasm instruction 82: i32.load8_u */
  /*@ assert physical_bounds: t16 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t16 && t16 + 1 <= s + n; */
  unsigned int t17 = ((unsigned int)m[t16 + 0U] << 0);
  /* Wasm instruction 83: i32.store8 */
  /*@ assert physical_bounds: t15 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t15 && t15 + 1 <= d + n; */
  m[t15 + 0U] = (unsigned char)(t17 >> 0);
  /* Wasm instruction 84: local.get */
  /* Wasm instruction 85: local.get */
  /* Wasm instruction 86: i32.load8_u */
  /*@ assert physical_bounds: t9 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t9 && t9 + 1 <= s + n; */
  unsigned int t18 = ((unsigned int)m[t9 + 0U] << 0);
  /* Wasm instruction 87: i32.store8 */
  /*@ assert physical_bounds: t7 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t7 && t7 + 1 <= d + n; */
  m[t7 + 0U] = (unsigned char)(t18 >> 0);
  /* Wasm instruction 88: local.get */
  /* Wasm instruction 89: i32.const */
  /* Wasm instruction 90: i32.add */
  unsigned int t19 = 8U + 4294967292U;
  /* Wasm instruction 91: local.tee */
  /* Wasm instruction 92: br_if */
  /*@ assert branch_5: t19 != 0; */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: local.get */
  /* Wasm instruction 56: i32.add */
  unsigned int t20 = t6 + t19;
  /*@ assert address_normalization: t20 == d + (0); */
  /* Wasm instruction 57: local.tee */
  /* Wasm instruction 58: i32.const */
  /* Wasm instruction 59: i32.add */
  unsigned int t21 = t20 + 3U;
  /*@ assert address_normalization: t21 == d + (3); */
  /* Wasm instruction 60: local.get */
  /* Wasm instruction 61: local.get */
  /* Wasm instruction 62: i32.add */
  unsigned int t22 = t5 + t19;
  /*@ assert address_normalization: t22 == s + (0); */
  /* Wasm instruction 63: local.tee */
  /* Wasm instruction 64: i32.const */
  /* Wasm instruction 65: i32.add */
  unsigned int t23 = t22 + 3U;
  /*@ assert address_normalization: t23 == s + (3); */
  /* Wasm instruction 66: i32.load8_u */
  /*@ assert physical_bounds: t23 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t23 && t23 + 1 <= s + n; */
  unsigned int t24 = ((unsigned int)m[t23 + 0U] << 0);
  /* Wasm instruction 67: i32.store8 */
  /*@ assert physical_bounds: t21 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t21 && t21 + 1 <= d + n; */
  m[t21 + 0U] = (unsigned char)(t24 >> 0);
  /* Wasm instruction 68: local.get */
  /* Wasm instruction 69: i32.const */
  /* Wasm instruction 70: i32.add */
  unsigned int t25 = t20 + 2U;
  /*@ assert address_normalization: t25 == d + (2); */
  /* Wasm instruction 71: local.get */
  /* Wasm instruction 72: i32.const */
  /* Wasm instruction 73: i32.add */
  unsigned int t26 = t22 + 2U;
  /*@ assert address_normalization: t26 == s + (2); */
  /* Wasm instruction 74: i32.load8_u */
  /*@ assert physical_bounds: t26 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t26 && t26 + 1 <= s + n; */
  unsigned int t27 = ((unsigned int)m[t26 + 0U] << 0);
  /* Wasm instruction 75: i32.store8 */
  /*@ assert physical_bounds: t25 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t25 && t25 + 1 <= d + n; */
  m[t25 + 0U] = (unsigned char)(t27 >> 0);
  /* Wasm instruction 76: local.get */
  /* Wasm instruction 77: i32.const */
  /* Wasm instruction 78: i32.add */
  unsigned int t28 = t20 + 1U;
  /*@ assert address_normalization: t28 == d + (1); */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: i32.const */
  /* Wasm instruction 81: i32.add */
  unsigned int t29 = t22 + 1U;
  /*@ assert address_normalization: t29 == s + (1); */
  /* Wasm instruction 82: i32.load8_u */
  /*@ assert physical_bounds: t29 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t29 && t29 + 1 <= s + n; */
  unsigned int t30 = ((unsigned int)m[t29 + 0U] << 0);
  /* Wasm instruction 83: i32.store8 */
  /*@ assert physical_bounds: t28 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t28 && t28 + 1 <= d + n; */
  m[t28 + 0U] = (unsigned char)(t30 >> 0);
  /* Wasm instruction 84: local.get */
  /* Wasm instruction 85: local.get */
  /* Wasm instruction 86: i32.load8_u */
  /*@ assert physical_bounds: t22 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t22 && t22 + 1 <= s + n; */
  unsigned int t31 = ((unsigned int)m[t22 + 0U] << 0);
  /* Wasm instruction 87: i32.store8 */
  /*@ assert physical_bounds: t20 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t20 && t20 + 1 <= d + n; */
  m[t20 + 0U] = (unsigned char)(t31 >> 0);
  /* Wasm instruction 88: local.get */
  /* Wasm instruction 89: i32.const */
  /* Wasm instruction 90: i32.add */
  unsigned int t32 = t19 + 4294967292U;
  /* Wasm instruction 91: local.tee */
  /* Wasm instruction 92: br_if */
  /*@ assert branch_5: t32 == 0; */
  /* Wasm instruction 93: br */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  /*@ assert copied_byte_3: m[d+3] == \at(m[s+3],Pre); */
  /*@ assert copied_byte_4: m[d+4] == \at(m[s+4],Pre); */
  /*@ assert copied_byte_5: m[d+5] == \at(m[s+5],Pre); */
  /*@ assert copied_byte_6: m[d+6] == \at(m[s+6],Pre); */
  /*@ assert copied_byte_7: m[d+7] == \at(m[s+7],Pre); */
  return d;
}
/*@
  requires specialization: n == 8 && d < s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
  ensures byte_3: m[d+3] == \old(m[s+3]);
  ensures byte_4: m[d+4] == \old(m[s+4]);
  ensures byte_5: m[d+5] == \old(m[s+5]);
  ensures byte_6: m[d+6] == \old(m[s+6]);
  ensures byte_7: m[d+7] == \old(m[s+7]);
*/
unsigned int move4_8_1(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 8; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 != 0; */
  /* Wasm instruction 94: local.get */
  /* Wasm instruction 95: i32.eqz */
  unsigned int t1 = !8U;
  /* Wasm instruction 96: br_if */
  /*@ assert branch_6: t1 == 0; */
  /* Wasm instruction 97: local.get */
  /* Wasm instruction 98: i32.const */
  /* Wasm instruction 99: i32.and */
  unsigned int t2 = 8U & 3U;
  /* Wasm instruction 100: local.set */
  /* Wasm instruction 101: i32.const */
  /* Wasm instruction 102: local.set */
  /* Wasm instruction 103: local.get */
  /* Wasm instruction 104: i32.const */
  /* Wasm instruction 105: i32.lt_u */
  unsigned int t3 = 8U < 4U;
  /* Wasm instruction 106: br_if */
  /*@ assert branch_7: t3 == 0; */
  /* Wasm instruction 107: local.get */
  /* Wasm instruction 108: i32.const */
  /* Wasm instruction 109: i32.and */
  unsigned int t4 = 8U & 4294967292U;
  /* Wasm instruction 110: local.set */
  /* Wasm instruction 111: i32.const */
  /* Wasm instruction 112: local.set */
  /* Wasm instruction 113: local.get */
  /* Wasm instruction 114: local.get */
  /* Wasm instruction 115: i32.add */
  unsigned int t5 = d + 0U;
  /*@ assert address_normalization: t5 == d + (0); */
  /* Wasm instruction 116: local.tee */
  /* Wasm instruction 117: local.get */
  /* Wasm instruction 118: local.get */
  /* Wasm instruction 119: i32.add */
  unsigned int t6 = s + 0U;
  /*@ assert address_normalization: t6 == s + (0); */
  /* Wasm instruction 120: local.tee */
  /* Wasm instruction 121: i32.load8_u */
  /*@ assert physical_bounds: t6 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t6 && t6 + 1 <= s + n; */
  unsigned int t7 = ((unsigned int)m[t6 + 0U] << 0);
  /* Wasm instruction 122: i32.store8 */
  /*@ assert physical_bounds: t5 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t5 && t5 + 1 <= d + n; */
  m[t5 + 0U] = (unsigned char)(t7 >> 0);
  /* Wasm instruction 123: local.get */
  /* Wasm instruction 124: i32.const */
  /* Wasm instruction 125: i32.add */
  unsigned int t8 = t5 + 1U;
  /*@ assert address_normalization: t8 == d + (1); */
  /* Wasm instruction 126: local.get */
  /* Wasm instruction 127: i32.const */
  /* Wasm instruction 128: i32.add */
  unsigned int t9 = t6 + 1U;
  /*@ assert address_normalization: t9 == s + (1); */
  /* Wasm instruction 129: i32.load8_u */
  /*@ assert physical_bounds: t9 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t9 && t9 + 1 <= s + n; */
  unsigned int t10 = ((unsigned int)m[t9 + 0U] << 0);
  /* Wasm instruction 130: i32.store8 */
  /*@ assert physical_bounds: t8 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t8 && t8 + 1 <= d + n; */
  m[t8 + 0U] = (unsigned char)(t10 >> 0);
  /* Wasm instruction 131: local.get */
  /* Wasm instruction 132: i32.const */
  /* Wasm instruction 133: i32.add */
  unsigned int t11 = t5 + 2U;
  /*@ assert address_normalization: t11 == d + (2); */
  /* Wasm instruction 134: local.get */
  /* Wasm instruction 135: i32.const */
  /* Wasm instruction 136: i32.add */
  unsigned int t12 = t6 + 2U;
  /*@ assert address_normalization: t12 == s + (2); */
  /* Wasm instruction 137: i32.load8_u */
  /*@ assert physical_bounds: t12 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t12 && t12 + 1 <= s + n; */
  unsigned int t13 = ((unsigned int)m[t12 + 0U] << 0);
  /* Wasm instruction 138: i32.store8 */
  /*@ assert physical_bounds: t11 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t11 && t11 + 1 <= d + n; */
  m[t11 + 0U] = (unsigned char)(t13 >> 0);
  /* Wasm instruction 139: local.get */
  /* Wasm instruction 140: i32.const */
  /* Wasm instruction 141: i32.add */
  unsigned int t14 = t5 + 3U;
  /*@ assert address_normalization: t14 == d + (3); */
  /* Wasm instruction 142: local.get */
  /* Wasm instruction 143: i32.const */
  /* Wasm instruction 144: i32.add */
  unsigned int t15 = t6 + 3U;
  /*@ assert address_normalization: t15 == s + (3); */
  /* Wasm instruction 145: i32.load8_u */
  /*@ assert physical_bounds: t15 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t15 && t15 + 1 <= s + n; */
  unsigned int t16 = ((unsigned int)m[t15 + 0U] << 0);
  /* Wasm instruction 146: i32.store8 */
  /*@ assert physical_bounds: t14 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t14 && t14 + 1 <= d + n; */
  m[t14 + 0U] = (unsigned char)(t16 >> 0);
  /* Wasm instruction 147: local.get */
  /* Wasm instruction 148: local.get */
  /* Wasm instruction 149: i32.const */
  /* Wasm instruction 150: i32.add */
  unsigned int t17 = 0U + 4U;
  /* Wasm instruction 151: local.tee */
  /* Wasm instruction 152: i32.ne */
  unsigned int t18 = t4 != t17;
  /* Wasm instruction 153: br_if */
  /*@ assert branch_8: t18 != 0; */
  /* Wasm instruction 113: local.get */
  /* Wasm instruction 114: local.get */
  /* Wasm instruction 115: i32.add */
  unsigned int t19 = d + t17;
  /*@ assert address_normalization: t19 == d + (4); */
  /* Wasm instruction 116: local.tee */
  /* Wasm instruction 117: local.get */
  /* Wasm instruction 118: local.get */
  /* Wasm instruction 119: i32.add */
  unsigned int t20 = s + t17;
  /*@ assert address_normalization: t20 == s + (4); */
  /* Wasm instruction 120: local.tee */
  /* Wasm instruction 121: i32.load8_u */
  /*@ assert physical_bounds: t20 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t20 && t20 + 1 <= s + n; */
  unsigned int t21 = ((unsigned int)m[t20 + 0U] << 0);
  /* Wasm instruction 122: i32.store8 */
  /*@ assert physical_bounds: t19 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t19 && t19 + 1 <= d + n; */
  m[t19 + 0U] = (unsigned char)(t21 >> 0);
  /* Wasm instruction 123: local.get */
  /* Wasm instruction 124: i32.const */
  /* Wasm instruction 125: i32.add */
  unsigned int t22 = t19 + 1U;
  /*@ assert address_normalization: t22 == d + (5); */
  /* Wasm instruction 126: local.get */
  /* Wasm instruction 127: i32.const */
  /* Wasm instruction 128: i32.add */
  unsigned int t23 = t20 + 1U;
  /*@ assert address_normalization: t23 == s + (5); */
  /* Wasm instruction 129: i32.load8_u */
  /*@ assert physical_bounds: t23 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t23 && t23 + 1 <= s + n; */
  unsigned int t24 = ((unsigned int)m[t23 + 0U] << 0);
  /* Wasm instruction 130: i32.store8 */
  /*@ assert physical_bounds: t22 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t22 && t22 + 1 <= d + n; */
  m[t22 + 0U] = (unsigned char)(t24 >> 0);
  /* Wasm instruction 131: local.get */
  /* Wasm instruction 132: i32.const */
  /* Wasm instruction 133: i32.add */
  unsigned int t25 = t19 + 2U;
  /*@ assert address_normalization: t25 == d + (6); */
  /* Wasm instruction 134: local.get */
  /* Wasm instruction 135: i32.const */
  /* Wasm instruction 136: i32.add */
  unsigned int t26 = t20 + 2U;
  /*@ assert address_normalization: t26 == s + (6); */
  /* Wasm instruction 137: i32.load8_u */
  /*@ assert physical_bounds: t26 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t26 && t26 + 1 <= s + n; */
  unsigned int t27 = ((unsigned int)m[t26 + 0U] << 0);
  /* Wasm instruction 138: i32.store8 */
  /*@ assert physical_bounds: t25 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t25 && t25 + 1 <= d + n; */
  m[t25 + 0U] = (unsigned char)(t27 >> 0);
  /* Wasm instruction 139: local.get */
  /* Wasm instruction 140: i32.const */
  /* Wasm instruction 141: i32.add */
  unsigned int t28 = t19 + 3U;
  /*@ assert address_normalization: t28 == d + (7); */
  /* Wasm instruction 142: local.get */
  /* Wasm instruction 143: i32.const */
  /* Wasm instruction 144: i32.add */
  unsigned int t29 = t20 + 3U;
  /*@ assert address_normalization: t29 == s + (7); */
  /* Wasm instruction 145: i32.load8_u */
  /*@ assert physical_bounds: t29 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t29 && t29 + 1 <= s + n; */
  unsigned int t30 = ((unsigned int)m[t29 + 0U] << 0);
  /* Wasm instruction 146: i32.store8 */
  /*@ assert physical_bounds: t28 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t28 && t28 + 1 <= d + n; */
  m[t28 + 0U] = (unsigned char)(t30 >> 0);
  /* Wasm instruction 147: local.get */
  /* Wasm instruction 148: local.get */
  /* Wasm instruction 149: i32.const */
  /* Wasm instruction 150: i32.add */
  unsigned int t31 = t17 + 4U;
  /* Wasm instruction 151: local.tee */
  /* Wasm instruction 152: i32.ne */
  unsigned int t32 = t4 != t31;
  /* Wasm instruction 153: br_if */
  /*@ assert branch_8: t32 == 0; */
  /* Wasm instruction 154: local.get */
  /* Wasm instruction 155: i32.eqz */
  unsigned int t33 = !t2;
  /* Wasm instruction 156: br_if */
  /*@ assert branch_9: t33 != 0; */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  /*@ assert copied_byte_3: m[d+3] == \at(m[s+3],Pre); */
  /*@ assert copied_byte_4: m[d+4] == \at(m[s+4],Pre); */
  /*@ assert copied_byte_5: m[d+5] == \at(m[s+5],Pre); */
  /*@ assert copied_byte_6: m[d+6] == \at(m[s+6],Pre); */
  /*@ assert copied_byte_7: m[d+7] == \at(m[s+7],Pre); */
  return d;
}
/*@
  requires specialization: n == 9 && d >= s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
  ensures byte_3: m[d+3] == \old(m[s+3]);
  ensures byte_4: m[d+4] == \old(m[s+4]);
  ensures byte_5: m[d+5] == \old(m[s+5]);
  ensures byte_6: m[d+6] == \old(m[s+6]);
  ensures byte_7: m[d+7] == \old(m[s+7]);
  ensures byte_8: m[d+8] == \old(m[s+8]);
*/
unsigned int move4_9_0(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 9; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 == 0; */
  /* Wasm instruction 4: local.get */
  /* Wasm instruction 5: i32.eqz */
  unsigned int t1 = !9U;
  /* Wasm instruction 6: br_if */
  /*@ assert branch_1: t1 == 0; */
  /* Wasm instruction 7: local.get */
  /* Wasm instruction 8: local.set */
  /* Wasm instruction 9: local.get */
  /* Wasm instruction 10: i32.const */
  /* Wasm instruction 11: i32.and */
  unsigned int t2 = 9U & 3U;
  /* Wasm instruction 12: local.tee */
  /* Wasm instruction 13: i32.eqz */
  unsigned int t3 = !t2;
  /* Wasm instruction 14: br_if */
  /*@ assert branch_2: t3 == 0; */
  /* Wasm instruction 15: local.get */
  /* Wasm instruction 16: i32.const */
  /* Wasm instruction 17: i32.add */
  unsigned int t4 = s + 4294967295U;
  /*@ assert address_normalization: t4 == s + (-1); */
  /* Wasm instruction 18: local.set */
  /* Wasm instruction 19: local.get */
  /* Wasm instruction 20: i32.const */
  /* Wasm instruction 21: i32.add */
  unsigned int t5 = d + 4294967295U;
  /*@ assert address_normalization: t5 == d + (-1); */
  /* Wasm instruction 22: local.set */
  /* Wasm instruction 23: local.get */
  /* Wasm instruction 24: local.set */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: local.get */
  /* Wasm instruction 27: i32.add */
  unsigned int t6 = t5 + 9U;
  /*@ assert address_normalization: t6 == d + (8); */
  /* Wasm instruction 28: local.get */
  /* Wasm instruction 29: local.get */
  /* Wasm instruction 30: i32.add */
  unsigned int t7 = t4 + 9U;
  /*@ assert address_normalization: t7 == s + (8); */
  /* Wasm instruction 31: i32.load8_u */
  /*@ assert physical_bounds: t7 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t7 && t7 + 1 <= s + n; */
  unsigned int t8 = ((unsigned int)m[t7 + 0U] << 0);
  /* Wasm instruction 32: i32.store8 */
  /*@ assert physical_bounds: t6 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t6 && t6 + 1 <= d + n; */
  m[t6 + 0U] = (unsigned char)(t8 >> 0);
  /* Wasm instruction 33: local.get */
  /* Wasm instruction 34: i32.const */
  /* Wasm instruction 35: i32.add */
  unsigned int t9 = 9U + 4294967295U;
  /* Wasm instruction 36: local.set */
  /* Wasm instruction 37: local.get */
  /* Wasm instruction 38: i32.const */
  /* Wasm instruction 39: i32.add */
  unsigned int t10 = t2 + 4294967295U;
  /* Wasm instruction 40: local.tee */
  /* Wasm instruction 41: br_if */
  /*@ assert branch_3: t10 == 0; */
  /* Wasm instruction 42: local.get */
  /* Wasm instruction 43: i32.const */
  /* Wasm instruction 44: i32.lt_u */
  unsigned int t11 = 9U < 4U;
  /* Wasm instruction 45: br_if */
  /*@ assert branch_4: t11 == 0; */
  /* Wasm instruction 46: local.get */
  /* Wasm instruction 47: i32.const */
  /* Wasm instruction 48: i32.add */
  unsigned int t12 = s + 4294967292U;
  /*@ assert address_normalization: t12 == s + (-4); */
  /* Wasm instruction 49: local.set */
  /* Wasm instruction 50: local.get */
  /* Wasm instruction 51: i32.const */
  /* Wasm instruction 52: i32.add */
  unsigned int t13 = d + 4294967292U;
  /*@ assert address_normalization: t13 == d + (-4); */
  /* Wasm instruction 53: local.set */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: local.get */
  /* Wasm instruction 56: i32.add */
  unsigned int t14 = t13 + t9;
  /*@ assert address_normalization: t14 == d + (4); */
  /* Wasm instruction 57: local.tee */
  /* Wasm instruction 58: i32.const */
  /* Wasm instruction 59: i32.add */
  unsigned int t15 = t14 + 3U;
  /*@ assert address_normalization: t15 == d + (7); */
  /* Wasm instruction 60: local.get */
  /* Wasm instruction 61: local.get */
  /* Wasm instruction 62: i32.add */
  unsigned int t16 = t12 + t9;
  /*@ assert address_normalization: t16 == s + (4); */
  /* Wasm instruction 63: local.tee */
  /* Wasm instruction 64: i32.const */
  /* Wasm instruction 65: i32.add */
  unsigned int t17 = t16 + 3U;
  /*@ assert address_normalization: t17 == s + (7); */
  /* Wasm instruction 66: i32.load8_u */
  /*@ assert physical_bounds: t17 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t17 && t17 + 1 <= s + n; */
  unsigned int t18 = ((unsigned int)m[t17 + 0U] << 0);
  /* Wasm instruction 67: i32.store8 */
  /*@ assert physical_bounds: t15 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t15 && t15 + 1 <= d + n; */
  m[t15 + 0U] = (unsigned char)(t18 >> 0);
  /* Wasm instruction 68: local.get */
  /* Wasm instruction 69: i32.const */
  /* Wasm instruction 70: i32.add */
  unsigned int t19 = t14 + 2U;
  /*@ assert address_normalization: t19 == d + (6); */
  /* Wasm instruction 71: local.get */
  /* Wasm instruction 72: i32.const */
  /* Wasm instruction 73: i32.add */
  unsigned int t20 = t16 + 2U;
  /*@ assert address_normalization: t20 == s + (6); */
  /* Wasm instruction 74: i32.load8_u */
  /*@ assert physical_bounds: t20 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t20 && t20 + 1 <= s + n; */
  unsigned int t21 = ((unsigned int)m[t20 + 0U] << 0);
  /* Wasm instruction 75: i32.store8 */
  /*@ assert physical_bounds: t19 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t19 && t19 + 1 <= d + n; */
  m[t19 + 0U] = (unsigned char)(t21 >> 0);
  /* Wasm instruction 76: local.get */
  /* Wasm instruction 77: i32.const */
  /* Wasm instruction 78: i32.add */
  unsigned int t22 = t14 + 1U;
  /*@ assert address_normalization: t22 == d + (5); */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: i32.const */
  /* Wasm instruction 81: i32.add */
  unsigned int t23 = t16 + 1U;
  /*@ assert address_normalization: t23 == s + (5); */
  /* Wasm instruction 82: i32.load8_u */
  /*@ assert physical_bounds: t23 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t23 && t23 + 1 <= s + n; */
  unsigned int t24 = ((unsigned int)m[t23 + 0U] << 0);
  /* Wasm instruction 83: i32.store8 */
  /*@ assert physical_bounds: t22 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t22 && t22 + 1 <= d + n; */
  m[t22 + 0U] = (unsigned char)(t24 >> 0);
  /* Wasm instruction 84: local.get */
  /* Wasm instruction 85: local.get */
  /* Wasm instruction 86: i32.load8_u */
  /*@ assert physical_bounds: t16 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t16 && t16 + 1 <= s + n; */
  unsigned int t25 = ((unsigned int)m[t16 + 0U] << 0);
  /* Wasm instruction 87: i32.store8 */
  /*@ assert physical_bounds: t14 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t14 && t14 + 1 <= d + n; */
  m[t14 + 0U] = (unsigned char)(t25 >> 0);
  /* Wasm instruction 88: local.get */
  /* Wasm instruction 89: i32.const */
  /* Wasm instruction 90: i32.add */
  unsigned int t26 = t9 + 4294967292U;
  /* Wasm instruction 91: local.tee */
  /* Wasm instruction 92: br_if */
  /*@ assert branch_5: t26 != 0; */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: local.get */
  /* Wasm instruction 56: i32.add */
  unsigned int t27 = t13 + t26;
  /*@ assert address_normalization: t27 == d + (0); */
  /* Wasm instruction 57: local.tee */
  /* Wasm instruction 58: i32.const */
  /* Wasm instruction 59: i32.add */
  unsigned int t28 = t27 + 3U;
  /*@ assert address_normalization: t28 == d + (3); */
  /* Wasm instruction 60: local.get */
  /* Wasm instruction 61: local.get */
  /* Wasm instruction 62: i32.add */
  unsigned int t29 = t12 + t26;
  /*@ assert address_normalization: t29 == s + (0); */
  /* Wasm instruction 63: local.tee */
  /* Wasm instruction 64: i32.const */
  /* Wasm instruction 65: i32.add */
  unsigned int t30 = t29 + 3U;
  /*@ assert address_normalization: t30 == s + (3); */
  /* Wasm instruction 66: i32.load8_u */
  /*@ assert physical_bounds: t30 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t30 && t30 + 1 <= s + n; */
  unsigned int t31 = ((unsigned int)m[t30 + 0U] << 0);
  /* Wasm instruction 67: i32.store8 */
  /*@ assert physical_bounds: t28 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t28 && t28 + 1 <= d + n; */
  m[t28 + 0U] = (unsigned char)(t31 >> 0);
  /* Wasm instruction 68: local.get */
  /* Wasm instruction 69: i32.const */
  /* Wasm instruction 70: i32.add */
  unsigned int t32 = t27 + 2U;
  /*@ assert address_normalization: t32 == d + (2); */
  /* Wasm instruction 71: local.get */
  /* Wasm instruction 72: i32.const */
  /* Wasm instruction 73: i32.add */
  unsigned int t33 = t29 + 2U;
  /*@ assert address_normalization: t33 == s + (2); */
  /* Wasm instruction 74: i32.load8_u */
  /*@ assert physical_bounds: t33 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t33 && t33 + 1 <= s + n; */
  unsigned int t34 = ((unsigned int)m[t33 + 0U] << 0);
  /* Wasm instruction 75: i32.store8 */
  /*@ assert physical_bounds: t32 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t32 && t32 + 1 <= d + n; */
  m[t32 + 0U] = (unsigned char)(t34 >> 0);
  /* Wasm instruction 76: local.get */
  /* Wasm instruction 77: i32.const */
  /* Wasm instruction 78: i32.add */
  unsigned int t35 = t27 + 1U;
  /*@ assert address_normalization: t35 == d + (1); */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: i32.const */
  /* Wasm instruction 81: i32.add */
  unsigned int t36 = t29 + 1U;
  /*@ assert address_normalization: t36 == s + (1); */
  /* Wasm instruction 82: i32.load8_u */
  /*@ assert physical_bounds: t36 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t36 && t36 + 1 <= s + n; */
  unsigned int t37 = ((unsigned int)m[t36 + 0U] << 0);
  /* Wasm instruction 83: i32.store8 */
  /*@ assert physical_bounds: t35 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t35 && t35 + 1 <= d + n; */
  m[t35 + 0U] = (unsigned char)(t37 >> 0);
  /* Wasm instruction 84: local.get */
  /* Wasm instruction 85: local.get */
  /* Wasm instruction 86: i32.load8_u */
  /*@ assert physical_bounds: t29 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t29 && t29 + 1 <= s + n; */
  unsigned int t38 = ((unsigned int)m[t29 + 0U] << 0);
  /* Wasm instruction 87: i32.store8 */
  /*@ assert physical_bounds: t27 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t27 && t27 + 1 <= d + n; */
  m[t27 + 0U] = (unsigned char)(t38 >> 0);
  /* Wasm instruction 88: local.get */
  /* Wasm instruction 89: i32.const */
  /* Wasm instruction 90: i32.add */
  unsigned int t39 = t26 + 4294967292U;
  /* Wasm instruction 91: local.tee */
  /* Wasm instruction 92: br_if */
  /*@ assert branch_5: t39 == 0; */
  /* Wasm instruction 93: br */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  /*@ assert copied_byte_3: m[d+3] == \at(m[s+3],Pre); */
  /*@ assert copied_byte_4: m[d+4] == \at(m[s+4],Pre); */
  /*@ assert copied_byte_5: m[d+5] == \at(m[s+5],Pre); */
  /*@ assert copied_byte_6: m[d+6] == \at(m[s+6],Pre); */
  /*@ assert copied_byte_7: m[d+7] == \at(m[s+7],Pre); */
  /*@ assert copied_byte_8: m[d+8] == \at(m[s+8],Pre); */
  return d;
}
/*@
  requires specialization: n == 9 && d < s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
  ensures byte_3: m[d+3] == \old(m[s+3]);
  ensures byte_4: m[d+4] == \old(m[s+4]);
  ensures byte_5: m[d+5] == \old(m[s+5]);
  ensures byte_6: m[d+6] == \old(m[s+6]);
  ensures byte_7: m[d+7] == \old(m[s+7]);
  ensures byte_8: m[d+8] == \old(m[s+8]);
*/
unsigned int move4_9_1(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 9; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 != 0; */
  /* Wasm instruction 94: local.get */
  /* Wasm instruction 95: i32.eqz */
  unsigned int t1 = !9U;
  /* Wasm instruction 96: br_if */
  /*@ assert branch_6: t1 == 0; */
  /* Wasm instruction 97: local.get */
  /* Wasm instruction 98: i32.const */
  /* Wasm instruction 99: i32.and */
  unsigned int t2 = 9U & 3U;
  /* Wasm instruction 100: local.set */
  /* Wasm instruction 101: i32.const */
  /* Wasm instruction 102: local.set */
  /* Wasm instruction 103: local.get */
  /* Wasm instruction 104: i32.const */
  /* Wasm instruction 105: i32.lt_u */
  unsigned int t3 = 9U < 4U;
  /* Wasm instruction 106: br_if */
  /*@ assert branch_7: t3 == 0; */
  /* Wasm instruction 107: local.get */
  /* Wasm instruction 108: i32.const */
  /* Wasm instruction 109: i32.and */
  unsigned int t4 = 9U & 4294967292U;
  /* Wasm instruction 110: local.set */
  /* Wasm instruction 111: i32.const */
  /* Wasm instruction 112: local.set */
  /* Wasm instruction 113: local.get */
  /* Wasm instruction 114: local.get */
  /* Wasm instruction 115: i32.add */
  unsigned int t5 = d + 0U;
  /*@ assert address_normalization: t5 == d + (0); */
  /* Wasm instruction 116: local.tee */
  /* Wasm instruction 117: local.get */
  /* Wasm instruction 118: local.get */
  /* Wasm instruction 119: i32.add */
  unsigned int t6 = s + 0U;
  /*@ assert address_normalization: t6 == s + (0); */
  /* Wasm instruction 120: local.tee */
  /* Wasm instruction 121: i32.load8_u */
  /*@ assert physical_bounds: t6 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t6 && t6 + 1 <= s + n; */
  unsigned int t7 = ((unsigned int)m[t6 + 0U] << 0);
  /* Wasm instruction 122: i32.store8 */
  /*@ assert physical_bounds: t5 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t5 && t5 + 1 <= d + n; */
  m[t5 + 0U] = (unsigned char)(t7 >> 0);
  /* Wasm instruction 123: local.get */
  /* Wasm instruction 124: i32.const */
  /* Wasm instruction 125: i32.add */
  unsigned int t8 = t5 + 1U;
  /*@ assert address_normalization: t8 == d + (1); */
  /* Wasm instruction 126: local.get */
  /* Wasm instruction 127: i32.const */
  /* Wasm instruction 128: i32.add */
  unsigned int t9 = t6 + 1U;
  /*@ assert address_normalization: t9 == s + (1); */
  /* Wasm instruction 129: i32.load8_u */
  /*@ assert physical_bounds: t9 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t9 && t9 + 1 <= s + n; */
  unsigned int t10 = ((unsigned int)m[t9 + 0U] << 0);
  /* Wasm instruction 130: i32.store8 */
  /*@ assert physical_bounds: t8 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t8 && t8 + 1 <= d + n; */
  m[t8 + 0U] = (unsigned char)(t10 >> 0);
  /* Wasm instruction 131: local.get */
  /* Wasm instruction 132: i32.const */
  /* Wasm instruction 133: i32.add */
  unsigned int t11 = t5 + 2U;
  /*@ assert address_normalization: t11 == d + (2); */
  /* Wasm instruction 134: local.get */
  /* Wasm instruction 135: i32.const */
  /* Wasm instruction 136: i32.add */
  unsigned int t12 = t6 + 2U;
  /*@ assert address_normalization: t12 == s + (2); */
  /* Wasm instruction 137: i32.load8_u */
  /*@ assert physical_bounds: t12 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t12 && t12 + 1 <= s + n; */
  unsigned int t13 = ((unsigned int)m[t12 + 0U] << 0);
  /* Wasm instruction 138: i32.store8 */
  /*@ assert physical_bounds: t11 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t11 && t11 + 1 <= d + n; */
  m[t11 + 0U] = (unsigned char)(t13 >> 0);
  /* Wasm instruction 139: local.get */
  /* Wasm instruction 140: i32.const */
  /* Wasm instruction 141: i32.add */
  unsigned int t14 = t5 + 3U;
  /*@ assert address_normalization: t14 == d + (3); */
  /* Wasm instruction 142: local.get */
  /* Wasm instruction 143: i32.const */
  /* Wasm instruction 144: i32.add */
  unsigned int t15 = t6 + 3U;
  /*@ assert address_normalization: t15 == s + (3); */
  /* Wasm instruction 145: i32.load8_u */
  /*@ assert physical_bounds: t15 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t15 && t15 + 1 <= s + n; */
  unsigned int t16 = ((unsigned int)m[t15 + 0U] << 0);
  /* Wasm instruction 146: i32.store8 */
  /*@ assert physical_bounds: t14 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t14 && t14 + 1 <= d + n; */
  m[t14 + 0U] = (unsigned char)(t16 >> 0);
  /* Wasm instruction 147: local.get */
  /* Wasm instruction 148: local.get */
  /* Wasm instruction 149: i32.const */
  /* Wasm instruction 150: i32.add */
  unsigned int t17 = 0U + 4U;
  /* Wasm instruction 151: local.tee */
  /* Wasm instruction 152: i32.ne */
  unsigned int t18 = t4 != t17;
  /* Wasm instruction 153: br_if */
  /*@ assert branch_8: t18 != 0; */
  /* Wasm instruction 113: local.get */
  /* Wasm instruction 114: local.get */
  /* Wasm instruction 115: i32.add */
  unsigned int t19 = d + t17;
  /*@ assert address_normalization: t19 == d + (4); */
  /* Wasm instruction 116: local.tee */
  /* Wasm instruction 117: local.get */
  /* Wasm instruction 118: local.get */
  /* Wasm instruction 119: i32.add */
  unsigned int t20 = s + t17;
  /*@ assert address_normalization: t20 == s + (4); */
  /* Wasm instruction 120: local.tee */
  /* Wasm instruction 121: i32.load8_u */
  /*@ assert physical_bounds: t20 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t20 && t20 + 1 <= s + n; */
  unsigned int t21 = ((unsigned int)m[t20 + 0U] << 0);
  /* Wasm instruction 122: i32.store8 */
  /*@ assert physical_bounds: t19 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t19 && t19 + 1 <= d + n; */
  m[t19 + 0U] = (unsigned char)(t21 >> 0);
  /* Wasm instruction 123: local.get */
  /* Wasm instruction 124: i32.const */
  /* Wasm instruction 125: i32.add */
  unsigned int t22 = t19 + 1U;
  /*@ assert address_normalization: t22 == d + (5); */
  /* Wasm instruction 126: local.get */
  /* Wasm instruction 127: i32.const */
  /* Wasm instruction 128: i32.add */
  unsigned int t23 = t20 + 1U;
  /*@ assert address_normalization: t23 == s + (5); */
  /* Wasm instruction 129: i32.load8_u */
  /*@ assert physical_bounds: t23 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t23 && t23 + 1 <= s + n; */
  unsigned int t24 = ((unsigned int)m[t23 + 0U] << 0);
  /* Wasm instruction 130: i32.store8 */
  /*@ assert physical_bounds: t22 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t22 && t22 + 1 <= d + n; */
  m[t22 + 0U] = (unsigned char)(t24 >> 0);
  /* Wasm instruction 131: local.get */
  /* Wasm instruction 132: i32.const */
  /* Wasm instruction 133: i32.add */
  unsigned int t25 = t19 + 2U;
  /*@ assert address_normalization: t25 == d + (6); */
  /* Wasm instruction 134: local.get */
  /* Wasm instruction 135: i32.const */
  /* Wasm instruction 136: i32.add */
  unsigned int t26 = t20 + 2U;
  /*@ assert address_normalization: t26 == s + (6); */
  /* Wasm instruction 137: i32.load8_u */
  /*@ assert physical_bounds: t26 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t26 && t26 + 1 <= s + n; */
  unsigned int t27 = ((unsigned int)m[t26 + 0U] << 0);
  /* Wasm instruction 138: i32.store8 */
  /*@ assert physical_bounds: t25 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t25 && t25 + 1 <= d + n; */
  m[t25 + 0U] = (unsigned char)(t27 >> 0);
  /* Wasm instruction 139: local.get */
  /* Wasm instruction 140: i32.const */
  /* Wasm instruction 141: i32.add */
  unsigned int t28 = t19 + 3U;
  /*@ assert address_normalization: t28 == d + (7); */
  /* Wasm instruction 142: local.get */
  /* Wasm instruction 143: i32.const */
  /* Wasm instruction 144: i32.add */
  unsigned int t29 = t20 + 3U;
  /*@ assert address_normalization: t29 == s + (7); */
  /* Wasm instruction 145: i32.load8_u */
  /*@ assert physical_bounds: t29 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t29 && t29 + 1 <= s + n; */
  unsigned int t30 = ((unsigned int)m[t29 + 0U] << 0);
  /* Wasm instruction 146: i32.store8 */
  /*@ assert physical_bounds: t28 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t28 && t28 + 1 <= d + n; */
  m[t28 + 0U] = (unsigned char)(t30 >> 0);
  /* Wasm instruction 147: local.get */
  /* Wasm instruction 148: local.get */
  /* Wasm instruction 149: i32.const */
  /* Wasm instruction 150: i32.add */
  unsigned int t31 = t17 + 4U;
  /* Wasm instruction 151: local.tee */
  /* Wasm instruction 152: i32.ne */
  unsigned int t32 = t4 != t31;
  /* Wasm instruction 153: br_if */
  /*@ assert branch_8: t32 == 0; */
  /* Wasm instruction 154: local.get */
  /* Wasm instruction 155: i32.eqz */
  unsigned int t33 = !t2;
  /* Wasm instruction 156: br_if */
  /*@ assert branch_9: t33 == 0; */
  /* Wasm instruction 157: local.get */
  /* Wasm instruction 158: local.get */
  /* Wasm instruction 159: i32.add */
  unsigned int t34 = s + t31;
  /*@ assert address_normalization: t34 == s + (8); */
  /* Wasm instruction 160: local.set */
  /* Wasm instruction 161: local.get */
  /* Wasm instruction 162: local.get */
  /* Wasm instruction 163: i32.add */
  unsigned int t35 = d + t31;
  /*@ assert address_normalization: t35 == d + (8); */
  /* Wasm instruction 164: local.set */
  /* Wasm instruction 165: local.get */
  /* Wasm instruction 166: local.get */
  /* Wasm instruction 167: i32.load8_u */
  /*@ assert physical_bounds: t34 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t34 && t34 + 1 <= s + n; */
  unsigned int t36 = ((unsigned int)m[t34 + 0U] << 0);
  /* Wasm instruction 168: i32.store8 */
  /*@ assert physical_bounds: t35 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t35 && t35 + 1 <= d + n; */
  m[t35 + 0U] = (unsigned char)(t36 >> 0);
  /* Wasm instruction 169: local.get */
  /* Wasm instruction 170: i32.const */
  /* Wasm instruction 171: i32.add */
  unsigned int t37 = t34 + 1U;
  /*@ assert address_normalization: t37 == s + (9); */
  /* Wasm instruction 172: local.set */
  /* Wasm instruction 173: local.get */
  /* Wasm instruction 174: i32.const */
  /* Wasm instruction 175: i32.add */
  unsigned int t38 = t35 + 1U;
  /*@ assert address_normalization: t38 == d + (9); */
  /* Wasm instruction 176: local.set */
  /* Wasm instruction 177: local.get */
  /* Wasm instruction 178: i32.const */
  /* Wasm instruction 179: i32.add */
  unsigned int t39 = t2 + 4294967295U;
  /* Wasm instruction 180: local.tee */
  /* Wasm instruction 181: br_if */
  /*@ assert branch_10: t39 == 0; */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  /*@ assert copied_byte_3: m[d+3] == \at(m[s+3],Pre); */
  /*@ assert copied_byte_4: m[d+4] == \at(m[s+4],Pre); */
  /*@ assert copied_byte_5: m[d+5] == \at(m[s+5],Pre); */
  /*@ assert copied_byte_6: m[d+6] == \at(m[s+6],Pre); */
  /*@ assert copied_byte_7: m[d+7] == \at(m[s+7],Pre); */
  /*@ assert copied_byte_8: m[d+8] == \at(m[s+8],Pre); */
  return d;
}
/*@
  requires specialization: n == 10 && d >= s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
  ensures byte_3: m[d+3] == \old(m[s+3]);
  ensures byte_4: m[d+4] == \old(m[s+4]);
  ensures byte_5: m[d+5] == \old(m[s+5]);
  ensures byte_6: m[d+6] == \old(m[s+6]);
  ensures byte_7: m[d+7] == \old(m[s+7]);
  ensures byte_8: m[d+8] == \old(m[s+8]);
  ensures byte_9: m[d+9] == \old(m[s+9]);
*/
unsigned int move4_10_0(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 10; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 == 0; */
  /* Wasm instruction 4: local.get */
  /* Wasm instruction 5: i32.eqz */
  unsigned int t1 = !10U;
  /* Wasm instruction 6: br_if */
  /*@ assert branch_1: t1 == 0; */
  /* Wasm instruction 7: local.get */
  /* Wasm instruction 8: local.set */
  /* Wasm instruction 9: local.get */
  /* Wasm instruction 10: i32.const */
  /* Wasm instruction 11: i32.and */
  unsigned int t2 = 10U & 3U;
  /* Wasm instruction 12: local.tee */
  /* Wasm instruction 13: i32.eqz */
  unsigned int t3 = !t2;
  /* Wasm instruction 14: br_if */
  /*@ assert branch_2: t3 == 0; */
  /* Wasm instruction 15: local.get */
  /* Wasm instruction 16: i32.const */
  /* Wasm instruction 17: i32.add */
  unsigned int t4 = s + 4294967295U;
  /*@ assert address_normalization: t4 == s + (-1); */
  /* Wasm instruction 18: local.set */
  /* Wasm instruction 19: local.get */
  /* Wasm instruction 20: i32.const */
  /* Wasm instruction 21: i32.add */
  unsigned int t5 = d + 4294967295U;
  /*@ assert address_normalization: t5 == d + (-1); */
  /* Wasm instruction 22: local.set */
  /* Wasm instruction 23: local.get */
  /* Wasm instruction 24: local.set */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: local.get */
  /* Wasm instruction 27: i32.add */
  unsigned int t6 = t5 + 10U;
  /*@ assert address_normalization: t6 == d + (9); */
  /* Wasm instruction 28: local.get */
  /* Wasm instruction 29: local.get */
  /* Wasm instruction 30: i32.add */
  unsigned int t7 = t4 + 10U;
  /*@ assert address_normalization: t7 == s + (9); */
  /* Wasm instruction 31: i32.load8_u */
  /*@ assert physical_bounds: t7 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t7 && t7 + 1 <= s + n; */
  unsigned int t8 = ((unsigned int)m[t7 + 0U] << 0);
  /* Wasm instruction 32: i32.store8 */
  /*@ assert physical_bounds: t6 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t6 && t6 + 1 <= d + n; */
  m[t6 + 0U] = (unsigned char)(t8 >> 0);
  /* Wasm instruction 33: local.get */
  /* Wasm instruction 34: i32.const */
  /* Wasm instruction 35: i32.add */
  unsigned int t9 = 10U + 4294967295U;
  /* Wasm instruction 36: local.set */
  /* Wasm instruction 37: local.get */
  /* Wasm instruction 38: i32.const */
  /* Wasm instruction 39: i32.add */
  unsigned int t10 = t2 + 4294967295U;
  /* Wasm instruction 40: local.tee */
  /* Wasm instruction 41: br_if */
  /*@ assert branch_3: t10 != 0; */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: local.get */
  /* Wasm instruction 27: i32.add */
  unsigned int t11 = t5 + t9;
  /*@ assert address_normalization: t11 == d + (8); */
  /* Wasm instruction 28: local.get */
  /* Wasm instruction 29: local.get */
  /* Wasm instruction 30: i32.add */
  unsigned int t12 = t4 + t9;
  /*@ assert address_normalization: t12 == s + (8); */
  /* Wasm instruction 31: i32.load8_u */
  /*@ assert physical_bounds: t12 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t12 && t12 + 1 <= s + n; */
  unsigned int t13 = ((unsigned int)m[t12 + 0U] << 0);
  /* Wasm instruction 32: i32.store8 */
  /*@ assert physical_bounds: t11 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t11 && t11 + 1 <= d + n; */
  m[t11 + 0U] = (unsigned char)(t13 >> 0);
  /* Wasm instruction 33: local.get */
  /* Wasm instruction 34: i32.const */
  /* Wasm instruction 35: i32.add */
  unsigned int t14 = t9 + 4294967295U;
  /* Wasm instruction 36: local.set */
  /* Wasm instruction 37: local.get */
  /* Wasm instruction 38: i32.const */
  /* Wasm instruction 39: i32.add */
  unsigned int t15 = t10 + 4294967295U;
  /* Wasm instruction 40: local.tee */
  /* Wasm instruction 41: br_if */
  /*@ assert branch_3: t15 == 0; */
  /* Wasm instruction 42: local.get */
  /* Wasm instruction 43: i32.const */
  /* Wasm instruction 44: i32.lt_u */
  unsigned int t16 = 10U < 4U;
  /* Wasm instruction 45: br_if */
  /*@ assert branch_4: t16 == 0; */
  /* Wasm instruction 46: local.get */
  /* Wasm instruction 47: i32.const */
  /* Wasm instruction 48: i32.add */
  unsigned int t17 = s + 4294967292U;
  /*@ assert address_normalization: t17 == s + (-4); */
  /* Wasm instruction 49: local.set */
  /* Wasm instruction 50: local.get */
  /* Wasm instruction 51: i32.const */
  /* Wasm instruction 52: i32.add */
  unsigned int t18 = d + 4294967292U;
  /*@ assert address_normalization: t18 == d + (-4); */
  /* Wasm instruction 53: local.set */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: local.get */
  /* Wasm instruction 56: i32.add */
  unsigned int t19 = t18 + t14;
  /*@ assert address_normalization: t19 == d + (4); */
  /* Wasm instruction 57: local.tee */
  /* Wasm instruction 58: i32.const */
  /* Wasm instruction 59: i32.add */
  unsigned int t20 = t19 + 3U;
  /*@ assert address_normalization: t20 == d + (7); */
  /* Wasm instruction 60: local.get */
  /* Wasm instruction 61: local.get */
  /* Wasm instruction 62: i32.add */
  unsigned int t21 = t17 + t14;
  /*@ assert address_normalization: t21 == s + (4); */
  /* Wasm instruction 63: local.tee */
  /* Wasm instruction 64: i32.const */
  /* Wasm instruction 65: i32.add */
  unsigned int t22 = t21 + 3U;
  /*@ assert address_normalization: t22 == s + (7); */
  /* Wasm instruction 66: i32.load8_u */
  /*@ assert physical_bounds: t22 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t22 && t22 + 1 <= s + n; */
  unsigned int t23 = ((unsigned int)m[t22 + 0U] << 0);
  /* Wasm instruction 67: i32.store8 */
  /*@ assert physical_bounds: t20 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t20 && t20 + 1 <= d + n; */
  m[t20 + 0U] = (unsigned char)(t23 >> 0);
  /* Wasm instruction 68: local.get */
  /* Wasm instruction 69: i32.const */
  /* Wasm instruction 70: i32.add */
  unsigned int t24 = t19 + 2U;
  /*@ assert address_normalization: t24 == d + (6); */
  /* Wasm instruction 71: local.get */
  /* Wasm instruction 72: i32.const */
  /* Wasm instruction 73: i32.add */
  unsigned int t25 = t21 + 2U;
  /*@ assert address_normalization: t25 == s + (6); */
  /* Wasm instruction 74: i32.load8_u */
  /*@ assert physical_bounds: t25 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t25 && t25 + 1 <= s + n; */
  unsigned int t26 = ((unsigned int)m[t25 + 0U] << 0);
  /* Wasm instruction 75: i32.store8 */
  /*@ assert physical_bounds: t24 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t24 && t24 + 1 <= d + n; */
  m[t24 + 0U] = (unsigned char)(t26 >> 0);
  /* Wasm instruction 76: local.get */
  /* Wasm instruction 77: i32.const */
  /* Wasm instruction 78: i32.add */
  unsigned int t27 = t19 + 1U;
  /*@ assert address_normalization: t27 == d + (5); */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: i32.const */
  /* Wasm instruction 81: i32.add */
  unsigned int t28 = t21 + 1U;
  /*@ assert address_normalization: t28 == s + (5); */
  /* Wasm instruction 82: i32.load8_u */
  /*@ assert physical_bounds: t28 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t28 && t28 + 1 <= s + n; */
  unsigned int t29 = ((unsigned int)m[t28 + 0U] << 0);
  /* Wasm instruction 83: i32.store8 */
  /*@ assert physical_bounds: t27 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t27 && t27 + 1 <= d + n; */
  m[t27 + 0U] = (unsigned char)(t29 >> 0);
  /* Wasm instruction 84: local.get */
  /* Wasm instruction 85: local.get */
  /* Wasm instruction 86: i32.load8_u */
  /*@ assert physical_bounds: t21 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t21 && t21 + 1 <= s + n; */
  unsigned int t30 = ((unsigned int)m[t21 + 0U] << 0);
  /* Wasm instruction 87: i32.store8 */
  /*@ assert physical_bounds: t19 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t19 && t19 + 1 <= d + n; */
  m[t19 + 0U] = (unsigned char)(t30 >> 0);
  /* Wasm instruction 88: local.get */
  /* Wasm instruction 89: i32.const */
  /* Wasm instruction 90: i32.add */
  unsigned int t31 = t14 + 4294967292U;
  /* Wasm instruction 91: local.tee */
  /* Wasm instruction 92: br_if */
  /*@ assert branch_5: t31 != 0; */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: local.get */
  /* Wasm instruction 56: i32.add */
  unsigned int t32 = t18 + t31;
  /*@ assert address_normalization: t32 == d + (0); */
  /* Wasm instruction 57: local.tee */
  /* Wasm instruction 58: i32.const */
  /* Wasm instruction 59: i32.add */
  unsigned int t33 = t32 + 3U;
  /*@ assert address_normalization: t33 == d + (3); */
  /* Wasm instruction 60: local.get */
  /* Wasm instruction 61: local.get */
  /* Wasm instruction 62: i32.add */
  unsigned int t34 = t17 + t31;
  /*@ assert address_normalization: t34 == s + (0); */
  /* Wasm instruction 63: local.tee */
  /* Wasm instruction 64: i32.const */
  /* Wasm instruction 65: i32.add */
  unsigned int t35 = t34 + 3U;
  /*@ assert address_normalization: t35 == s + (3); */
  /* Wasm instruction 66: i32.load8_u */
  /*@ assert physical_bounds: t35 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t35 && t35 + 1 <= s + n; */
  unsigned int t36 = ((unsigned int)m[t35 + 0U] << 0);
  /* Wasm instruction 67: i32.store8 */
  /*@ assert physical_bounds: t33 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t33 && t33 + 1 <= d + n; */
  m[t33 + 0U] = (unsigned char)(t36 >> 0);
  /* Wasm instruction 68: local.get */
  /* Wasm instruction 69: i32.const */
  /* Wasm instruction 70: i32.add */
  unsigned int t37 = t32 + 2U;
  /*@ assert address_normalization: t37 == d + (2); */
  /* Wasm instruction 71: local.get */
  /* Wasm instruction 72: i32.const */
  /* Wasm instruction 73: i32.add */
  unsigned int t38 = t34 + 2U;
  /*@ assert address_normalization: t38 == s + (2); */
  /* Wasm instruction 74: i32.load8_u */
  /*@ assert physical_bounds: t38 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t38 && t38 + 1 <= s + n; */
  unsigned int t39 = ((unsigned int)m[t38 + 0U] << 0);
  /* Wasm instruction 75: i32.store8 */
  /*@ assert physical_bounds: t37 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t37 && t37 + 1 <= d + n; */
  m[t37 + 0U] = (unsigned char)(t39 >> 0);
  /* Wasm instruction 76: local.get */
  /* Wasm instruction 77: i32.const */
  /* Wasm instruction 78: i32.add */
  unsigned int t40 = t32 + 1U;
  /*@ assert address_normalization: t40 == d + (1); */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: i32.const */
  /* Wasm instruction 81: i32.add */
  unsigned int t41 = t34 + 1U;
  /*@ assert address_normalization: t41 == s + (1); */
  /* Wasm instruction 82: i32.load8_u */
  /*@ assert physical_bounds: t41 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t41 && t41 + 1 <= s + n; */
  unsigned int t42 = ((unsigned int)m[t41 + 0U] << 0);
  /* Wasm instruction 83: i32.store8 */
  /*@ assert physical_bounds: t40 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t40 && t40 + 1 <= d + n; */
  m[t40 + 0U] = (unsigned char)(t42 >> 0);
  /* Wasm instruction 84: local.get */
  /* Wasm instruction 85: local.get */
  /* Wasm instruction 86: i32.load8_u */
  /*@ assert physical_bounds: t34 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t34 && t34 + 1 <= s + n; */
  unsigned int t43 = ((unsigned int)m[t34 + 0U] << 0);
  /* Wasm instruction 87: i32.store8 */
  /*@ assert physical_bounds: t32 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t32 && t32 + 1 <= d + n; */
  m[t32 + 0U] = (unsigned char)(t43 >> 0);
  /* Wasm instruction 88: local.get */
  /* Wasm instruction 89: i32.const */
  /* Wasm instruction 90: i32.add */
  unsigned int t44 = t31 + 4294967292U;
  /* Wasm instruction 91: local.tee */
  /* Wasm instruction 92: br_if */
  /*@ assert branch_5: t44 == 0; */
  /* Wasm instruction 93: br */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  /*@ assert copied_byte_3: m[d+3] == \at(m[s+3],Pre); */
  /*@ assert copied_byte_4: m[d+4] == \at(m[s+4],Pre); */
  /*@ assert copied_byte_5: m[d+5] == \at(m[s+5],Pre); */
  /*@ assert copied_byte_6: m[d+6] == \at(m[s+6],Pre); */
  /*@ assert copied_byte_7: m[d+7] == \at(m[s+7],Pre); */
  /*@ assert copied_byte_8: m[d+8] == \at(m[s+8],Pre); */
  /*@ assert copied_byte_9: m[d+9] == \at(m[s+9],Pre); */
  return d;
}
/*@
  requires specialization: n == 10 && d < s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
  ensures byte_3: m[d+3] == \old(m[s+3]);
  ensures byte_4: m[d+4] == \old(m[s+4]);
  ensures byte_5: m[d+5] == \old(m[s+5]);
  ensures byte_6: m[d+6] == \old(m[s+6]);
  ensures byte_7: m[d+7] == \old(m[s+7]);
  ensures byte_8: m[d+8] == \old(m[s+8]);
  ensures byte_9: m[d+9] == \old(m[s+9]);
*/
unsigned int move4_10_1(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 10; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 != 0; */
  /* Wasm instruction 94: local.get */
  /* Wasm instruction 95: i32.eqz */
  unsigned int t1 = !10U;
  /* Wasm instruction 96: br_if */
  /*@ assert branch_6: t1 == 0; */
  /* Wasm instruction 97: local.get */
  /* Wasm instruction 98: i32.const */
  /* Wasm instruction 99: i32.and */
  unsigned int t2 = 10U & 3U;
  /* Wasm instruction 100: local.set */
  /* Wasm instruction 101: i32.const */
  /* Wasm instruction 102: local.set */
  /* Wasm instruction 103: local.get */
  /* Wasm instruction 104: i32.const */
  /* Wasm instruction 105: i32.lt_u */
  unsigned int t3 = 10U < 4U;
  /* Wasm instruction 106: br_if */
  /*@ assert branch_7: t3 == 0; */
  /* Wasm instruction 107: local.get */
  /* Wasm instruction 108: i32.const */
  /* Wasm instruction 109: i32.and */
  unsigned int t4 = 10U & 4294967292U;
  /* Wasm instruction 110: local.set */
  /* Wasm instruction 111: i32.const */
  /* Wasm instruction 112: local.set */
  /* Wasm instruction 113: local.get */
  /* Wasm instruction 114: local.get */
  /* Wasm instruction 115: i32.add */
  unsigned int t5 = d + 0U;
  /*@ assert address_normalization: t5 == d + (0); */
  /* Wasm instruction 116: local.tee */
  /* Wasm instruction 117: local.get */
  /* Wasm instruction 118: local.get */
  /* Wasm instruction 119: i32.add */
  unsigned int t6 = s + 0U;
  /*@ assert address_normalization: t6 == s + (0); */
  /* Wasm instruction 120: local.tee */
  /* Wasm instruction 121: i32.load8_u */
  /*@ assert physical_bounds: t6 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t6 && t6 + 1 <= s + n; */
  unsigned int t7 = ((unsigned int)m[t6 + 0U] << 0);
  /* Wasm instruction 122: i32.store8 */
  /*@ assert physical_bounds: t5 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t5 && t5 + 1 <= d + n; */
  m[t5 + 0U] = (unsigned char)(t7 >> 0);
  /* Wasm instruction 123: local.get */
  /* Wasm instruction 124: i32.const */
  /* Wasm instruction 125: i32.add */
  unsigned int t8 = t5 + 1U;
  /*@ assert address_normalization: t8 == d + (1); */
  /* Wasm instruction 126: local.get */
  /* Wasm instruction 127: i32.const */
  /* Wasm instruction 128: i32.add */
  unsigned int t9 = t6 + 1U;
  /*@ assert address_normalization: t9 == s + (1); */
  /* Wasm instruction 129: i32.load8_u */
  /*@ assert physical_bounds: t9 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t9 && t9 + 1 <= s + n; */
  unsigned int t10 = ((unsigned int)m[t9 + 0U] << 0);
  /* Wasm instruction 130: i32.store8 */
  /*@ assert physical_bounds: t8 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t8 && t8 + 1 <= d + n; */
  m[t8 + 0U] = (unsigned char)(t10 >> 0);
  /* Wasm instruction 131: local.get */
  /* Wasm instruction 132: i32.const */
  /* Wasm instruction 133: i32.add */
  unsigned int t11 = t5 + 2U;
  /*@ assert address_normalization: t11 == d + (2); */
  /* Wasm instruction 134: local.get */
  /* Wasm instruction 135: i32.const */
  /* Wasm instruction 136: i32.add */
  unsigned int t12 = t6 + 2U;
  /*@ assert address_normalization: t12 == s + (2); */
  /* Wasm instruction 137: i32.load8_u */
  /*@ assert physical_bounds: t12 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t12 && t12 + 1 <= s + n; */
  unsigned int t13 = ((unsigned int)m[t12 + 0U] << 0);
  /* Wasm instruction 138: i32.store8 */
  /*@ assert physical_bounds: t11 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t11 && t11 + 1 <= d + n; */
  m[t11 + 0U] = (unsigned char)(t13 >> 0);
  /* Wasm instruction 139: local.get */
  /* Wasm instruction 140: i32.const */
  /* Wasm instruction 141: i32.add */
  unsigned int t14 = t5 + 3U;
  /*@ assert address_normalization: t14 == d + (3); */
  /* Wasm instruction 142: local.get */
  /* Wasm instruction 143: i32.const */
  /* Wasm instruction 144: i32.add */
  unsigned int t15 = t6 + 3U;
  /*@ assert address_normalization: t15 == s + (3); */
  /* Wasm instruction 145: i32.load8_u */
  /*@ assert physical_bounds: t15 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t15 && t15 + 1 <= s + n; */
  unsigned int t16 = ((unsigned int)m[t15 + 0U] << 0);
  /* Wasm instruction 146: i32.store8 */
  /*@ assert physical_bounds: t14 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t14 && t14 + 1 <= d + n; */
  m[t14 + 0U] = (unsigned char)(t16 >> 0);
  /* Wasm instruction 147: local.get */
  /* Wasm instruction 148: local.get */
  /* Wasm instruction 149: i32.const */
  /* Wasm instruction 150: i32.add */
  unsigned int t17 = 0U + 4U;
  /* Wasm instruction 151: local.tee */
  /* Wasm instruction 152: i32.ne */
  unsigned int t18 = t4 != t17;
  /* Wasm instruction 153: br_if */
  /*@ assert branch_8: t18 != 0; */
  /* Wasm instruction 113: local.get */
  /* Wasm instruction 114: local.get */
  /* Wasm instruction 115: i32.add */
  unsigned int t19 = d + t17;
  /*@ assert address_normalization: t19 == d + (4); */
  /* Wasm instruction 116: local.tee */
  /* Wasm instruction 117: local.get */
  /* Wasm instruction 118: local.get */
  /* Wasm instruction 119: i32.add */
  unsigned int t20 = s + t17;
  /*@ assert address_normalization: t20 == s + (4); */
  /* Wasm instruction 120: local.tee */
  /* Wasm instruction 121: i32.load8_u */
  /*@ assert physical_bounds: t20 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t20 && t20 + 1 <= s + n; */
  unsigned int t21 = ((unsigned int)m[t20 + 0U] << 0);
  /* Wasm instruction 122: i32.store8 */
  /*@ assert physical_bounds: t19 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t19 && t19 + 1 <= d + n; */
  m[t19 + 0U] = (unsigned char)(t21 >> 0);
  /* Wasm instruction 123: local.get */
  /* Wasm instruction 124: i32.const */
  /* Wasm instruction 125: i32.add */
  unsigned int t22 = t19 + 1U;
  /*@ assert address_normalization: t22 == d + (5); */
  /* Wasm instruction 126: local.get */
  /* Wasm instruction 127: i32.const */
  /* Wasm instruction 128: i32.add */
  unsigned int t23 = t20 + 1U;
  /*@ assert address_normalization: t23 == s + (5); */
  /* Wasm instruction 129: i32.load8_u */
  /*@ assert physical_bounds: t23 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t23 && t23 + 1 <= s + n; */
  unsigned int t24 = ((unsigned int)m[t23 + 0U] << 0);
  /* Wasm instruction 130: i32.store8 */
  /*@ assert physical_bounds: t22 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t22 && t22 + 1 <= d + n; */
  m[t22 + 0U] = (unsigned char)(t24 >> 0);
  /* Wasm instruction 131: local.get */
  /* Wasm instruction 132: i32.const */
  /* Wasm instruction 133: i32.add */
  unsigned int t25 = t19 + 2U;
  /*@ assert address_normalization: t25 == d + (6); */
  /* Wasm instruction 134: local.get */
  /* Wasm instruction 135: i32.const */
  /* Wasm instruction 136: i32.add */
  unsigned int t26 = t20 + 2U;
  /*@ assert address_normalization: t26 == s + (6); */
  /* Wasm instruction 137: i32.load8_u */
  /*@ assert physical_bounds: t26 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t26 && t26 + 1 <= s + n; */
  unsigned int t27 = ((unsigned int)m[t26 + 0U] << 0);
  /* Wasm instruction 138: i32.store8 */
  /*@ assert physical_bounds: t25 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t25 && t25 + 1 <= d + n; */
  m[t25 + 0U] = (unsigned char)(t27 >> 0);
  /* Wasm instruction 139: local.get */
  /* Wasm instruction 140: i32.const */
  /* Wasm instruction 141: i32.add */
  unsigned int t28 = t19 + 3U;
  /*@ assert address_normalization: t28 == d + (7); */
  /* Wasm instruction 142: local.get */
  /* Wasm instruction 143: i32.const */
  /* Wasm instruction 144: i32.add */
  unsigned int t29 = t20 + 3U;
  /*@ assert address_normalization: t29 == s + (7); */
  /* Wasm instruction 145: i32.load8_u */
  /*@ assert physical_bounds: t29 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t29 && t29 + 1 <= s + n; */
  unsigned int t30 = ((unsigned int)m[t29 + 0U] << 0);
  /* Wasm instruction 146: i32.store8 */
  /*@ assert physical_bounds: t28 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t28 && t28 + 1 <= d + n; */
  m[t28 + 0U] = (unsigned char)(t30 >> 0);
  /* Wasm instruction 147: local.get */
  /* Wasm instruction 148: local.get */
  /* Wasm instruction 149: i32.const */
  /* Wasm instruction 150: i32.add */
  unsigned int t31 = t17 + 4U;
  /* Wasm instruction 151: local.tee */
  /* Wasm instruction 152: i32.ne */
  unsigned int t32 = t4 != t31;
  /* Wasm instruction 153: br_if */
  /*@ assert branch_8: t32 == 0; */
  /* Wasm instruction 154: local.get */
  /* Wasm instruction 155: i32.eqz */
  unsigned int t33 = !t2;
  /* Wasm instruction 156: br_if */
  /*@ assert branch_9: t33 == 0; */
  /* Wasm instruction 157: local.get */
  /* Wasm instruction 158: local.get */
  /* Wasm instruction 159: i32.add */
  unsigned int t34 = s + t31;
  /*@ assert address_normalization: t34 == s + (8); */
  /* Wasm instruction 160: local.set */
  /* Wasm instruction 161: local.get */
  /* Wasm instruction 162: local.get */
  /* Wasm instruction 163: i32.add */
  unsigned int t35 = d + t31;
  /*@ assert address_normalization: t35 == d + (8); */
  /* Wasm instruction 164: local.set */
  /* Wasm instruction 165: local.get */
  /* Wasm instruction 166: local.get */
  /* Wasm instruction 167: i32.load8_u */
  /*@ assert physical_bounds: t34 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t34 && t34 + 1 <= s + n; */
  unsigned int t36 = ((unsigned int)m[t34 + 0U] << 0);
  /* Wasm instruction 168: i32.store8 */
  /*@ assert physical_bounds: t35 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t35 && t35 + 1 <= d + n; */
  m[t35 + 0U] = (unsigned char)(t36 >> 0);
  /* Wasm instruction 169: local.get */
  /* Wasm instruction 170: i32.const */
  /* Wasm instruction 171: i32.add */
  unsigned int t37 = t34 + 1U;
  /*@ assert address_normalization: t37 == s + (9); */
  /* Wasm instruction 172: local.set */
  /* Wasm instruction 173: local.get */
  /* Wasm instruction 174: i32.const */
  /* Wasm instruction 175: i32.add */
  unsigned int t38 = t35 + 1U;
  /*@ assert address_normalization: t38 == d + (9); */
  /* Wasm instruction 176: local.set */
  /* Wasm instruction 177: local.get */
  /* Wasm instruction 178: i32.const */
  /* Wasm instruction 179: i32.add */
  unsigned int t39 = t2 + 4294967295U;
  /* Wasm instruction 180: local.tee */
  /* Wasm instruction 181: br_if */
  /*@ assert branch_10: t39 != 0; */
  /* Wasm instruction 165: local.get */
  /* Wasm instruction 166: local.get */
  /* Wasm instruction 167: i32.load8_u */
  /*@ assert physical_bounds: t37 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t37 && t37 + 1 <= s + n; */
  unsigned int t40 = ((unsigned int)m[t37 + 0U] << 0);
  /* Wasm instruction 168: i32.store8 */
  /*@ assert physical_bounds: t38 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t38 && t38 + 1 <= d + n; */
  m[t38 + 0U] = (unsigned char)(t40 >> 0);
  /* Wasm instruction 169: local.get */
  /* Wasm instruction 170: i32.const */
  /* Wasm instruction 171: i32.add */
  unsigned int t41 = t37 + 1U;
  /*@ assert address_normalization: t41 == s + (10); */
  /* Wasm instruction 172: local.set */
  /* Wasm instruction 173: local.get */
  /* Wasm instruction 174: i32.const */
  /* Wasm instruction 175: i32.add */
  unsigned int t42 = t38 + 1U;
  /*@ assert address_normalization: t42 == d + (10); */
  /* Wasm instruction 176: local.set */
  /* Wasm instruction 177: local.get */
  /* Wasm instruction 178: i32.const */
  /* Wasm instruction 179: i32.add */
  unsigned int t43 = t39 + 4294967295U;
  /* Wasm instruction 180: local.tee */
  /* Wasm instruction 181: br_if */
  /*@ assert branch_10: t43 == 0; */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  /*@ assert copied_byte_3: m[d+3] == \at(m[s+3],Pre); */
  /*@ assert copied_byte_4: m[d+4] == \at(m[s+4],Pre); */
  /*@ assert copied_byte_5: m[d+5] == \at(m[s+5],Pre); */
  /*@ assert copied_byte_6: m[d+6] == \at(m[s+6],Pre); */
  /*@ assert copied_byte_7: m[d+7] == \at(m[s+7],Pre); */
  /*@ assert copied_byte_8: m[d+8] == \at(m[s+8],Pre); */
  /*@ assert copied_byte_9: m[d+9] == \at(m[s+9],Pre); */
  return d;
}
/*@
  requires specialization: n == 11 && d >= s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
  ensures byte_3: m[d+3] == \old(m[s+3]);
  ensures byte_4: m[d+4] == \old(m[s+4]);
  ensures byte_5: m[d+5] == \old(m[s+5]);
  ensures byte_6: m[d+6] == \old(m[s+6]);
  ensures byte_7: m[d+7] == \old(m[s+7]);
  ensures byte_8: m[d+8] == \old(m[s+8]);
  ensures byte_9: m[d+9] == \old(m[s+9]);
  ensures byte_10: m[d+10] == \old(m[s+10]);
*/
unsigned int move4_11_0(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 11; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 == 0; */
  /* Wasm instruction 4: local.get */
  /* Wasm instruction 5: i32.eqz */
  unsigned int t1 = !11U;
  /* Wasm instruction 6: br_if */
  /*@ assert branch_1: t1 == 0; */
  /* Wasm instruction 7: local.get */
  /* Wasm instruction 8: local.set */
  /* Wasm instruction 9: local.get */
  /* Wasm instruction 10: i32.const */
  /* Wasm instruction 11: i32.and */
  unsigned int t2 = 11U & 3U;
  /* Wasm instruction 12: local.tee */
  /* Wasm instruction 13: i32.eqz */
  unsigned int t3 = !t2;
  /* Wasm instruction 14: br_if */
  /*@ assert branch_2: t3 == 0; */
  /* Wasm instruction 15: local.get */
  /* Wasm instruction 16: i32.const */
  /* Wasm instruction 17: i32.add */
  unsigned int t4 = s + 4294967295U;
  /*@ assert address_normalization: t4 == s + (-1); */
  /* Wasm instruction 18: local.set */
  /* Wasm instruction 19: local.get */
  /* Wasm instruction 20: i32.const */
  /* Wasm instruction 21: i32.add */
  unsigned int t5 = d + 4294967295U;
  /*@ assert address_normalization: t5 == d + (-1); */
  /* Wasm instruction 22: local.set */
  /* Wasm instruction 23: local.get */
  /* Wasm instruction 24: local.set */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: local.get */
  /* Wasm instruction 27: i32.add */
  unsigned int t6 = t5 + 11U;
  /*@ assert address_normalization: t6 == d + (10); */
  /* Wasm instruction 28: local.get */
  /* Wasm instruction 29: local.get */
  /* Wasm instruction 30: i32.add */
  unsigned int t7 = t4 + 11U;
  /*@ assert address_normalization: t7 == s + (10); */
  /* Wasm instruction 31: i32.load8_u */
  /*@ assert physical_bounds: t7 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t7 && t7 + 1 <= s + n; */
  unsigned int t8 = ((unsigned int)m[t7 + 0U] << 0);
  /* Wasm instruction 32: i32.store8 */
  /*@ assert physical_bounds: t6 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t6 && t6 + 1 <= d + n; */
  m[t6 + 0U] = (unsigned char)(t8 >> 0);
  /* Wasm instruction 33: local.get */
  /* Wasm instruction 34: i32.const */
  /* Wasm instruction 35: i32.add */
  unsigned int t9 = 11U + 4294967295U;
  /* Wasm instruction 36: local.set */
  /* Wasm instruction 37: local.get */
  /* Wasm instruction 38: i32.const */
  /* Wasm instruction 39: i32.add */
  unsigned int t10 = t2 + 4294967295U;
  /* Wasm instruction 40: local.tee */
  /* Wasm instruction 41: br_if */
  /*@ assert branch_3: t10 != 0; */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: local.get */
  /* Wasm instruction 27: i32.add */
  unsigned int t11 = t5 + t9;
  /*@ assert address_normalization: t11 == d + (9); */
  /* Wasm instruction 28: local.get */
  /* Wasm instruction 29: local.get */
  /* Wasm instruction 30: i32.add */
  unsigned int t12 = t4 + t9;
  /*@ assert address_normalization: t12 == s + (9); */
  /* Wasm instruction 31: i32.load8_u */
  /*@ assert physical_bounds: t12 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t12 && t12 + 1 <= s + n; */
  unsigned int t13 = ((unsigned int)m[t12 + 0U] << 0);
  /* Wasm instruction 32: i32.store8 */
  /*@ assert physical_bounds: t11 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t11 && t11 + 1 <= d + n; */
  m[t11 + 0U] = (unsigned char)(t13 >> 0);
  /* Wasm instruction 33: local.get */
  /* Wasm instruction 34: i32.const */
  /* Wasm instruction 35: i32.add */
  unsigned int t14 = t9 + 4294967295U;
  /* Wasm instruction 36: local.set */
  /* Wasm instruction 37: local.get */
  /* Wasm instruction 38: i32.const */
  /* Wasm instruction 39: i32.add */
  unsigned int t15 = t10 + 4294967295U;
  /* Wasm instruction 40: local.tee */
  /* Wasm instruction 41: br_if */
  /*@ assert branch_3: t15 != 0; */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: local.get */
  /* Wasm instruction 27: i32.add */
  unsigned int t16 = t5 + t14;
  /*@ assert address_normalization: t16 == d + (8); */
  /* Wasm instruction 28: local.get */
  /* Wasm instruction 29: local.get */
  /* Wasm instruction 30: i32.add */
  unsigned int t17 = t4 + t14;
  /*@ assert address_normalization: t17 == s + (8); */
  /* Wasm instruction 31: i32.load8_u */
  /*@ assert physical_bounds: t17 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t17 && t17 + 1 <= s + n; */
  unsigned int t18 = ((unsigned int)m[t17 + 0U] << 0);
  /* Wasm instruction 32: i32.store8 */
  /*@ assert physical_bounds: t16 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t16 && t16 + 1 <= d + n; */
  m[t16 + 0U] = (unsigned char)(t18 >> 0);
  /* Wasm instruction 33: local.get */
  /* Wasm instruction 34: i32.const */
  /* Wasm instruction 35: i32.add */
  unsigned int t19 = t14 + 4294967295U;
  /* Wasm instruction 36: local.set */
  /* Wasm instruction 37: local.get */
  /* Wasm instruction 38: i32.const */
  /* Wasm instruction 39: i32.add */
  unsigned int t20 = t15 + 4294967295U;
  /* Wasm instruction 40: local.tee */
  /* Wasm instruction 41: br_if */
  /*@ assert branch_3: t20 == 0; */
  /* Wasm instruction 42: local.get */
  /* Wasm instruction 43: i32.const */
  /* Wasm instruction 44: i32.lt_u */
  unsigned int t21 = 11U < 4U;
  /* Wasm instruction 45: br_if */
  /*@ assert branch_4: t21 == 0; */
  /* Wasm instruction 46: local.get */
  /* Wasm instruction 47: i32.const */
  /* Wasm instruction 48: i32.add */
  unsigned int t22 = s + 4294967292U;
  /*@ assert address_normalization: t22 == s + (-4); */
  /* Wasm instruction 49: local.set */
  /* Wasm instruction 50: local.get */
  /* Wasm instruction 51: i32.const */
  /* Wasm instruction 52: i32.add */
  unsigned int t23 = d + 4294967292U;
  /*@ assert address_normalization: t23 == d + (-4); */
  /* Wasm instruction 53: local.set */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: local.get */
  /* Wasm instruction 56: i32.add */
  unsigned int t24 = t23 + t19;
  /*@ assert address_normalization: t24 == d + (4); */
  /* Wasm instruction 57: local.tee */
  /* Wasm instruction 58: i32.const */
  /* Wasm instruction 59: i32.add */
  unsigned int t25 = t24 + 3U;
  /*@ assert address_normalization: t25 == d + (7); */
  /* Wasm instruction 60: local.get */
  /* Wasm instruction 61: local.get */
  /* Wasm instruction 62: i32.add */
  unsigned int t26 = t22 + t19;
  /*@ assert address_normalization: t26 == s + (4); */
  /* Wasm instruction 63: local.tee */
  /* Wasm instruction 64: i32.const */
  /* Wasm instruction 65: i32.add */
  unsigned int t27 = t26 + 3U;
  /*@ assert address_normalization: t27 == s + (7); */
  /* Wasm instruction 66: i32.load8_u */
  /*@ assert physical_bounds: t27 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t27 && t27 + 1 <= s + n; */
  unsigned int t28 = ((unsigned int)m[t27 + 0U] << 0);
  /* Wasm instruction 67: i32.store8 */
  /*@ assert physical_bounds: t25 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t25 && t25 + 1 <= d + n; */
  m[t25 + 0U] = (unsigned char)(t28 >> 0);
  /* Wasm instruction 68: local.get */
  /* Wasm instruction 69: i32.const */
  /* Wasm instruction 70: i32.add */
  unsigned int t29 = t24 + 2U;
  /*@ assert address_normalization: t29 == d + (6); */
  /* Wasm instruction 71: local.get */
  /* Wasm instruction 72: i32.const */
  /* Wasm instruction 73: i32.add */
  unsigned int t30 = t26 + 2U;
  /*@ assert address_normalization: t30 == s + (6); */
  /* Wasm instruction 74: i32.load8_u */
  /*@ assert physical_bounds: t30 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t30 && t30 + 1 <= s + n; */
  unsigned int t31 = ((unsigned int)m[t30 + 0U] << 0);
  /* Wasm instruction 75: i32.store8 */
  /*@ assert physical_bounds: t29 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t29 && t29 + 1 <= d + n; */
  m[t29 + 0U] = (unsigned char)(t31 >> 0);
  /* Wasm instruction 76: local.get */
  /* Wasm instruction 77: i32.const */
  /* Wasm instruction 78: i32.add */
  unsigned int t32 = t24 + 1U;
  /*@ assert address_normalization: t32 == d + (5); */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: i32.const */
  /* Wasm instruction 81: i32.add */
  unsigned int t33 = t26 + 1U;
  /*@ assert address_normalization: t33 == s + (5); */
  /* Wasm instruction 82: i32.load8_u */
  /*@ assert physical_bounds: t33 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t33 && t33 + 1 <= s + n; */
  unsigned int t34 = ((unsigned int)m[t33 + 0U] << 0);
  /* Wasm instruction 83: i32.store8 */
  /*@ assert physical_bounds: t32 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t32 && t32 + 1 <= d + n; */
  m[t32 + 0U] = (unsigned char)(t34 >> 0);
  /* Wasm instruction 84: local.get */
  /* Wasm instruction 85: local.get */
  /* Wasm instruction 86: i32.load8_u */
  /*@ assert physical_bounds: t26 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t26 && t26 + 1 <= s + n; */
  unsigned int t35 = ((unsigned int)m[t26 + 0U] << 0);
  /* Wasm instruction 87: i32.store8 */
  /*@ assert physical_bounds: t24 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t24 && t24 + 1 <= d + n; */
  m[t24 + 0U] = (unsigned char)(t35 >> 0);
  /* Wasm instruction 88: local.get */
  /* Wasm instruction 89: i32.const */
  /* Wasm instruction 90: i32.add */
  unsigned int t36 = t19 + 4294967292U;
  /* Wasm instruction 91: local.tee */
  /* Wasm instruction 92: br_if */
  /*@ assert branch_5: t36 != 0; */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: local.get */
  /* Wasm instruction 56: i32.add */
  unsigned int t37 = t23 + t36;
  /*@ assert address_normalization: t37 == d + (0); */
  /* Wasm instruction 57: local.tee */
  /* Wasm instruction 58: i32.const */
  /* Wasm instruction 59: i32.add */
  unsigned int t38 = t37 + 3U;
  /*@ assert address_normalization: t38 == d + (3); */
  /* Wasm instruction 60: local.get */
  /* Wasm instruction 61: local.get */
  /* Wasm instruction 62: i32.add */
  unsigned int t39 = t22 + t36;
  /*@ assert address_normalization: t39 == s + (0); */
  /* Wasm instruction 63: local.tee */
  /* Wasm instruction 64: i32.const */
  /* Wasm instruction 65: i32.add */
  unsigned int t40 = t39 + 3U;
  /*@ assert address_normalization: t40 == s + (3); */
  /* Wasm instruction 66: i32.load8_u */
  /*@ assert physical_bounds: t40 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t40 && t40 + 1 <= s + n; */
  unsigned int t41 = ((unsigned int)m[t40 + 0U] << 0);
  /* Wasm instruction 67: i32.store8 */
  /*@ assert physical_bounds: t38 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t38 && t38 + 1 <= d + n; */
  m[t38 + 0U] = (unsigned char)(t41 >> 0);
  /* Wasm instruction 68: local.get */
  /* Wasm instruction 69: i32.const */
  /* Wasm instruction 70: i32.add */
  unsigned int t42 = t37 + 2U;
  /*@ assert address_normalization: t42 == d + (2); */
  /* Wasm instruction 71: local.get */
  /* Wasm instruction 72: i32.const */
  /* Wasm instruction 73: i32.add */
  unsigned int t43 = t39 + 2U;
  /*@ assert address_normalization: t43 == s + (2); */
  /* Wasm instruction 74: i32.load8_u */
  /*@ assert physical_bounds: t43 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t43 && t43 + 1 <= s + n; */
  unsigned int t44 = ((unsigned int)m[t43 + 0U] << 0);
  /* Wasm instruction 75: i32.store8 */
  /*@ assert physical_bounds: t42 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t42 && t42 + 1 <= d + n; */
  m[t42 + 0U] = (unsigned char)(t44 >> 0);
  /* Wasm instruction 76: local.get */
  /* Wasm instruction 77: i32.const */
  /* Wasm instruction 78: i32.add */
  unsigned int t45 = t37 + 1U;
  /*@ assert address_normalization: t45 == d + (1); */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: i32.const */
  /* Wasm instruction 81: i32.add */
  unsigned int t46 = t39 + 1U;
  /*@ assert address_normalization: t46 == s + (1); */
  /* Wasm instruction 82: i32.load8_u */
  /*@ assert physical_bounds: t46 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t46 && t46 + 1 <= s + n; */
  unsigned int t47 = ((unsigned int)m[t46 + 0U] << 0);
  /* Wasm instruction 83: i32.store8 */
  /*@ assert physical_bounds: t45 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t45 && t45 + 1 <= d + n; */
  m[t45 + 0U] = (unsigned char)(t47 >> 0);
  /* Wasm instruction 84: local.get */
  /* Wasm instruction 85: local.get */
  /* Wasm instruction 86: i32.load8_u */
  /*@ assert physical_bounds: t39 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t39 && t39 + 1 <= s + n; */
  unsigned int t48 = ((unsigned int)m[t39 + 0U] << 0);
  /* Wasm instruction 87: i32.store8 */
  /*@ assert physical_bounds: t37 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t37 && t37 + 1 <= d + n; */
  m[t37 + 0U] = (unsigned char)(t48 >> 0);
  /* Wasm instruction 88: local.get */
  /* Wasm instruction 89: i32.const */
  /* Wasm instruction 90: i32.add */
  unsigned int t49 = t36 + 4294967292U;
  /* Wasm instruction 91: local.tee */
  /* Wasm instruction 92: br_if */
  /*@ assert branch_5: t49 == 0; */
  /* Wasm instruction 93: br */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  /*@ assert copied_byte_3: m[d+3] == \at(m[s+3],Pre); */
  /*@ assert copied_byte_4: m[d+4] == \at(m[s+4],Pre); */
  /*@ assert copied_byte_5: m[d+5] == \at(m[s+5],Pre); */
  /*@ assert copied_byte_6: m[d+6] == \at(m[s+6],Pre); */
  /*@ assert copied_byte_7: m[d+7] == \at(m[s+7],Pre); */
  /*@ assert copied_byte_8: m[d+8] == \at(m[s+8],Pre); */
  /*@ assert copied_byte_9: m[d+9] == \at(m[s+9],Pre); */
  /*@ assert copied_byte_10: m[d+10] == \at(m[s+10],Pre); */
  return d;
}
/*@
  requires specialization: n == 11 && d < s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
  ensures byte_3: m[d+3] == \old(m[s+3]);
  ensures byte_4: m[d+4] == \old(m[s+4]);
  ensures byte_5: m[d+5] == \old(m[s+5]);
  ensures byte_6: m[d+6] == \old(m[s+6]);
  ensures byte_7: m[d+7] == \old(m[s+7]);
  ensures byte_8: m[d+8] == \old(m[s+8]);
  ensures byte_9: m[d+9] == \old(m[s+9]);
  ensures byte_10: m[d+10] == \old(m[s+10]);
*/
unsigned int move4_11_1(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 11; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 != 0; */
  /* Wasm instruction 94: local.get */
  /* Wasm instruction 95: i32.eqz */
  unsigned int t1 = !11U;
  /* Wasm instruction 96: br_if */
  /*@ assert branch_6: t1 == 0; */
  /* Wasm instruction 97: local.get */
  /* Wasm instruction 98: i32.const */
  /* Wasm instruction 99: i32.and */
  unsigned int t2 = 11U & 3U;
  /* Wasm instruction 100: local.set */
  /* Wasm instruction 101: i32.const */
  /* Wasm instruction 102: local.set */
  /* Wasm instruction 103: local.get */
  /* Wasm instruction 104: i32.const */
  /* Wasm instruction 105: i32.lt_u */
  unsigned int t3 = 11U < 4U;
  /* Wasm instruction 106: br_if */
  /*@ assert branch_7: t3 == 0; */
  /* Wasm instruction 107: local.get */
  /* Wasm instruction 108: i32.const */
  /* Wasm instruction 109: i32.and */
  unsigned int t4 = 11U & 4294967292U;
  /* Wasm instruction 110: local.set */
  /* Wasm instruction 111: i32.const */
  /* Wasm instruction 112: local.set */
  /* Wasm instruction 113: local.get */
  /* Wasm instruction 114: local.get */
  /* Wasm instruction 115: i32.add */
  unsigned int t5 = d + 0U;
  /*@ assert address_normalization: t5 == d + (0); */
  /* Wasm instruction 116: local.tee */
  /* Wasm instruction 117: local.get */
  /* Wasm instruction 118: local.get */
  /* Wasm instruction 119: i32.add */
  unsigned int t6 = s + 0U;
  /*@ assert address_normalization: t6 == s + (0); */
  /* Wasm instruction 120: local.tee */
  /* Wasm instruction 121: i32.load8_u */
  /*@ assert physical_bounds: t6 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t6 && t6 + 1 <= s + n; */
  unsigned int t7 = ((unsigned int)m[t6 + 0U] << 0);
  /* Wasm instruction 122: i32.store8 */
  /*@ assert physical_bounds: t5 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t5 && t5 + 1 <= d + n; */
  m[t5 + 0U] = (unsigned char)(t7 >> 0);
  /* Wasm instruction 123: local.get */
  /* Wasm instruction 124: i32.const */
  /* Wasm instruction 125: i32.add */
  unsigned int t8 = t5 + 1U;
  /*@ assert address_normalization: t8 == d + (1); */
  /* Wasm instruction 126: local.get */
  /* Wasm instruction 127: i32.const */
  /* Wasm instruction 128: i32.add */
  unsigned int t9 = t6 + 1U;
  /*@ assert address_normalization: t9 == s + (1); */
  /* Wasm instruction 129: i32.load8_u */
  /*@ assert physical_bounds: t9 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t9 && t9 + 1 <= s + n; */
  unsigned int t10 = ((unsigned int)m[t9 + 0U] << 0);
  /* Wasm instruction 130: i32.store8 */
  /*@ assert physical_bounds: t8 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t8 && t8 + 1 <= d + n; */
  m[t8 + 0U] = (unsigned char)(t10 >> 0);
  /* Wasm instruction 131: local.get */
  /* Wasm instruction 132: i32.const */
  /* Wasm instruction 133: i32.add */
  unsigned int t11 = t5 + 2U;
  /*@ assert address_normalization: t11 == d + (2); */
  /* Wasm instruction 134: local.get */
  /* Wasm instruction 135: i32.const */
  /* Wasm instruction 136: i32.add */
  unsigned int t12 = t6 + 2U;
  /*@ assert address_normalization: t12 == s + (2); */
  /* Wasm instruction 137: i32.load8_u */
  /*@ assert physical_bounds: t12 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t12 && t12 + 1 <= s + n; */
  unsigned int t13 = ((unsigned int)m[t12 + 0U] << 0);
  /* Wasm instruction 138: i32.store8 */
  /*@ assert physical_bounds: t11 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t11 && t11 + 1 <= d + n; */
  m[t11 + 0U] = (unsigned char)(t13 >> 0);
  /* Wasm instruction 139: local.get */
  /* Wasm instruction 140: i32.const */
  /* Wasm instruction 141: i32.add */
  unsigned int t14 = t5 + 3U;
  /*@ assert address_normalization: t14 == d + (3); */
  /* Wasm instruction 142: local.get */
  /* Wasm instruction 143: i32.const */
  /* Wasm instruction 144: i32.add */
  unsigned int t15 = t6 + 3U;
  /*@ assert address_normalization: t15 == s + (3); */
  /* Wasm instruction 145: i32.load8_u */
  /*@ assert physical_bounds: t15 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t15 && t15 + 1 <= s + n; */
  unsigned int t16 = ((unsigned int)m[t15 + 0U] << 0);
  /* Wasm instruction 146: i32.store8 */
  /*@ assert physical_bounds: t14 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t14 && t14 + 1 <= d + n; */
  m[t14 + 0U] = (unsigned char)(t16 >> 0);
  /* Wasm instruction 147: local.get */
  /* Wasm instruction 148: local.get */
  /* Wasm instruction 149: i32.const */
  /* Wasm instruction 150: i32.add */
  unsigned int t17 = 0U + 4U;
  /* Wasm instruction 151: local.tee */
  /* Wasm instruction 152: i32.ne */
  unsigned int t18 = t4 != t17;
  /* Wasm instruction 153: br_if */
  /*@ assert branch_8: t18 != 0; */
  /* Wasm instruction 113: local.get */
  /* Wasm instruction 114: local.get */
  /* Wasm instruction 115: i32.add */
  unsigned int t19 = d + t17;
  /*@ assert address_normalization: t19 == d + (4); */
  /* Wasm instruction 116: local.tee */
  /* Wasm instruction 117: local.get */
  /* Wasm instruction 118: local.get */
  /* Wasm instruction 119: i32.add */
  unsigned int t20 = s + t17;
  /*@ assert address_normalization: t20 == s + (4); */
  /* Wasm instruction 120: local.tee */
  /* Wasm instruction 121: i32.load8_u */
  /*@ assert physical_bounds: t20 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t20 && t20 + 1 <= s + n; */
  unsigned int t21 = ((unsigned int)m[t20 + 0U] << 0);
  /* Wasm instruction 122: i32.store8 */
  /*@ assert physical_bounds: t19 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t19 && t19 + 1 <= d + n; */
  m[t19 + 0U] = (unsigned char)(t21 >> 0);
  /* Wasm instruction 123: local.get */
  /* Wasm instruction 124: i32.const */
  /* Wasm instruction 125: i32.add */
  unsigned int t22 = t19 + 1U;
  /*@ assert address_normalization: t22 == d + (5); */
  /* Wasm instruction 126: local.get */
  /* Wasm instruction 127: i32.const */
  /* Wasm instruction 128: i32.add */
  unsigned int t23 = t20 + 1U;
  /*@ assert address_normalization: t23 == s + (5); */
  /* Wasm instruction 129: i32.load8_u */
  /*@ assert physical_bounds: t23 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t23 && t23 + 1 <= s + n; */
  unsigned int t24 = ((unsigned int)m[t23 + 0U] << 0);
  /* Wasm instruction 130: i32.store8 */
  /*@ assert physical_bounds: t22 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t22 && t22 + 1 <= d + n; */
  m[t22 + 0U] = (unsigned char)(t24 >> 0);
  /* Wasm instruction 131: local.get */
  /* Wasm instruction 132: i32.const */
  /* Wasm instruction 133: i32.add */
  unsigned int t25 = t19 + 2U;
  /*@ assert address_normalization: t25 == d + (6); */
  /* Wasm instruction 134: local.get */
  /* Wasm instruction 135: i32.const */
  /* Wasm instruction 136: i32.add */
  unsigned int t26 = t20 + 2U;
  /*@ assert address_normalization: t26 == s + (6); */
  /* Wasm instruction 137: i32.load8_u */
  /*@ assert physical_bounds: t26 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t26 && t26 + 1 <= s + n; */
  unsigned int t27 = ((unsigned int)m[t26 + 0U] << 0);
  /* Wasm instruction 138: i32.store8 */
  /*@ assert physical_bounds: t25 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t25 && t25 + 1 <= d + n; */
  m[t25 + 0U] = (unsigned char)(t27 >> 0);
  /* Wasm instruction 139: local.get */
  /* Wasm instruction 140: i32.const */
  /* Wasm instruction 141: i32.add */
  unsigned int t28 = t19 + 3U;
  /*@ assert address_normalization: t28 == d + (7); */
  /* Wasm instruction 142: local.get */
  /* Wasm instruction 143: i32.const */
  /* Wasm instruction 144: i32.add */
  unsigned int t29 = t20 + 3U;
  /*@ assert address_normalization: t29 == s + (7); */
  /* Wasm instruction 145: i32.load8_u */
  /*@ assert physical_bounds: t29 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t29 && t29 + 1 <= s + n; */
  unsigned int t30 = ((unsigned int)m[t29 + 0U] << 0);
  /* Wasm instruction 146: i32.store8 */
  /*@ assert physical_bounds: t28 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t28 && t28 + 1 <= d + n; */
  m[t28 + 0U] = (unsigned char)(t30 >> 0);
  /* Wasm instruction 147: local.get */
  /* Wasm instruction 148: local.get */
  /* Wasm instruction 149: i32.const */
  /* Wasm instruction 150: i32.add */
  unsigned int t31 = t17 + 4U;
  /* Wasm instruction 151: local.tee */
  /* Wasm instruction 152: i32.ne */
  unsigned int t32 = t4 != t31;
  /* Wasm instruction 153: br_if */
  /*@ assert branch_8: t32 == 0; */
  /* Wasm instruction 154: local.get */
  /* Wasm instruction 155: i32.eqz */
  unsigned int t33 = !t2;
  /* Wasm instruction 156: br_if */
  /*@ assert branch_9: t33 == 0; */
  /* Wasm instruction 157: local.get */
  /* Wasm instruction 158: local.get */
  /* Wasm instruction 159: i32.add */
  unsigned int t34 = s + t31;
  /*@ assert address_normalization: t34 == s + (8); */
  /* Wasm instruction 160: local.set */
  /* Wasm instruction 161: local.get */
  /* Wasm instruction 162: local.get */
  /* Wasm instruction 163: i32.add */
  unsigned int t35 = d + t31;
  /*@ assert address_normalization: t35 == d + (8); */
  /* Wasm instruction 164: local.set */
  /* Wasm instruction 165: local.get */
  /* Wasm instruction 166: local.get */
  /* Wasm instruction 167: i32.load8_u */
  /*@ assert physical_bounds: t34 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t34 && t34 + 1 <= s + n; */
  unsigned int t36 = ((unsigned int)m[t34 + 0U] << 0);
  /* Wasm instruction 168: i32.store8 */
  /*@ assert physical_bounds: t35 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t35 && t35 + 1 <= d + n; */
  m[t35 + 0U] = (unsigned char)(t36 >> 0);
  /* Wasm instruction 169: local.get */
  /* Wasm instruction 170: i32.const */
  /* Wasm instruction 171: i32.add */
  unsigned int t37 = t34 + 1U;
  /*@ assert address_normalization: t37 == s + (9); */
  /* Wasm instruction 172: local.set */
  /* Wasm instruction 173: local.get */
  /* Wasm instruction 174: i32.const */
  /* Wasm instruction 175: i32.add */
  unsigned int t38 = t35 + 1U;
  /*@ assert address_normalization: t38 == d + (9); */
  /* Wasm instruction 176: local.set */
  /* Wasm instruction 177: local.get */
  /* Wasm instruction 178: i32.const */
  /* Wasm instruction 179: i32.add */
  unsigned int t39 = t2 + 4294967295U;
  /* Wasm instruction 180: local.tee */
  /* Wasm instruction 181: br_if */
  /*@ assert branch_10: t39 != 0; */
  /* Wasm instruction 165: local.get */
  /* Wasm instruction 166: local.get */
  /* Wasm instruction 167: i32.load8_u */
  /*@ assert physical_bounds: t37 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t37 && t37 + 1 <= s + n; */
  unsigned int t40 = ((unsigned int)m[t37 + 0U] << 0);
  /* Wasm instruction 168: i32.store8 */
  /*@ assert physical_bounds: t38 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t38 && t38 + 1 <= d + n; */
  m[t38 + 0U] = (unsigned char)(t40 >> 0);
  /* Wasm instruction 169: local.get */
  /* Wasm instruction 170: i32.const */
  /* Wasm instruction 171: i32.add */
  unsigned int t41 = t37 + 1U;
  /*@ assert address_normalization: t41 == s + (10); */
  /* Wasm instruction 172: local.set */
  /* Wasm instruction 173: local.get */
  /* Wasm instruction 174: i32.const */
  /* Wasm instruction 175: i32.add */
  unsigned int t42 = t38 + 1U;
  /*@ assert address_normalization: t42 == d + (10); */
  /* Wasm instruction 176: local.set */
  /* Wasm instruction 177: local.get */
  /* Wasm instruction 178: i32.const */
  /* Wasm instruction 179: i32.add */
  unsigned int t43 = t39 + 4294967295U;
  /* Wasm instruction 180: local.tee */
  /* Wasm instruction 181: br_if */
  /*@ assert branch_10: t43 != 0; */
  /* Wasm instruction 165: local.get */
  /* Wasm instruction 166: local.get */
  /* Wasm instruction 167: i32.load8_u */
  /*@ assert physical_bounds: t41 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t41 && t41 + 1 <= s + n; */
  unsigned int t44 = ((unsigned int)m[t41 + 0U] << 0);
  /* Wasm instruction 168: i32.store8 */
  /*@ assert physical_bounds: t42 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t42 && t42 + 1 <= d + n; */
  m[t42 + 0U] = (unsigned char)(t44 >> 0);
  /* Wasm instruction 169: local.get */
  /* Wasm instruction 170: i32.const */
  /* Wasm instruction 171: i32.add */
  unsigned int t45 = t41 + 1U;
  /*@ assert address_normalization: t45 == s + (11); */
  /* Wasm instruction 172: local.set */
  /* Wasm instruction 173: local.get */
  /* Wasm instruction 174: i32.const */
  /* Wasm instruction 175: i32.add */
  unsigned int t46 = t42 + 1U;
  /*@ assert address_normalization: t46 == d + (11); */
  /* Wasm instruction 176: local.set */
  /* Wasm instruction 177: local.get */
  /* Wasm instruction 178: i32.const */
  /* Wasm instruction 179: i32.add */
  unsigned int t47 = t43 + 4294967295U;
  /* Wasm instruction 180: local.tee */
  /* Wasm instruction 181: br_if */
  /*@ assert branch_10: t47 == 0; */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  /*@ assert copied_byte_3: m[d+3] == \at(m[s+3],Pre); */
  /*@ assert copied_byte_4: m[d+4] == \at(m[s+4],Pre); */
  /*@ assert copied_byte_5: m[d+5] == \at(m[s+5],Pre); */
  /*@ assert copied_byte_6: m[d+6] == \at(m[s+6],Pre); */
  /*@ assert copied_byte_7: m[d+7] == \at(m[s+7],Pre); */
  /*@ assert copied_byte_8: m[d+8] == \at(m[s+8],Pre); */
  /*@ assert copied_byte_9: m[d+9] == \at(m[s+9],Pre); */
  /*@ assert copied_byte_10: m[d+10] == \at(m[s+10],Pre); */
  return d;
}
/*@
  requires specialization: n == 12 && d >= s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
  ensures byte_3: m[d+3] == \old(m[s+3]);
  ensures byte_4: m[d+4] == \old(m[s+4]);
  ensures byte_5: m[d+5] == \old(m[s+5]);
  ensures byte_6: m[d+6] == \old(m[s+6]);
  ensures byte_7: m[d+7] == \old(m[s+7]);
  ensures byte_8: m[d+8] == \old(m[s+8]);
  ensures byte_9: m[d+9] == \old(m[s+9]);
  ensures byte_10: m[d+10] == \old(m[s+10]);
  ensures byte_11: m[d+11] == \old(m[s+11]);
*/
unsigned int move4_12_0(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 12; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 == 0; */
  /* Wasm instruction 4: local.get */
  /* Wasm instruction 5: i32.eqz */
  unsigned int t1 = !12U;
  /* Wasm instruction 6: br_if */
  /*@ assert branch_1: t1 == 0; */
  /* Wasm instruction 7: local.get */
  /* Wasm instruction 8: local.set */
  /* Wasm instruction 9: local.get */
  /* Wasm instruction 10: i32.const */
  /* Wasm instruction 11: i32.and */
  unsigned int t2 = 12U & 3U;
  /* Wasm instruction 12: local.tee */
  /* Wasm instruction 13: i32.eqz */
  unsigned int t3 = !t2;
  /* Wasm instruction 14: br_if */
  /*@ assert branch_2: t3 != 0; */
  /* Wasm instruction 42: local.get */
  /* Wasm instruction 43: i32.const */
  /* Wasm instruction 44: i32.lt_u */
  unsigned int t4 = 12U < 4U;
  /* Wasm instruction 45: br_if */
  /*@ assert branch_4: t4 == 0; */
  /* Wasm instruction 46: local.get */
  /* Wasm instruction 47: i32.const */
  /* Wasm instruction 48: i32.add */
  unsigned int t5 = s + 4294967292U;
  /*@ assert address_normalization: t5 == s + (-4); */
  /* Wasm instruction 49: local.set */
  /* Wasm instruction 50: local.get */
  /* Wasm instruction 51: i32.const */
  /* Wasm instruction 52: i32.add */
  unsigned int t6 = d + 4294967292U;
  /*@ assert address_normalization: t6 == d + (-4); */
  /* Wasm instruction 53: local.set */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: local.get */
  /* Wasm instruction 56: i32.add */
  unsigned int t7 = t6 + 12U;
  /*@ assert address_normalization: t7 == d + (8); */
  /* Wasm instruction 57: local.tee */
  /* Wasm instruction 58: i32.const */
  /* Wasm instruction 59: i32.add */
  unsigned int t8 = t7 + 3U;
  /*@ assert address_normalization: t8 == d + (11); */
  /* Wasm instruction 60: local.get */
  /* Wasm instruction 61: local.get */
  /* Wasm instruction 62: i32.add */
  unsigned int t9 = t5 + 12U;
  /*@ assert address_normalization: t9 == s + (8); */
  /* Wasm instruction 63: local.tee */
  /* Wasm instruction 64: i32.const */
  /* Wasm instruction 65: i32.add */
  unsigned int t10 = t9 + 3U;
  /*@ assert address_normalization: t10 == s + (11); */
  /* Wasm instruction 66: i32.load8_u */
  /*@ assert physical_bounds: t10 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t10 && t10 + 1 <= s + n; */
  unsigned int t11 = ((unsigned int)m[t10 + 0U] << 0);
  /* Wasm instruction 67: i32.store8 */
  /*@ assert physical_bounds: t8 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t8 && t8 + 1 <= d + n; */
  m[t8 + 0U] = (unsigned char)(t11 >> 0);
  /* Wasm instruction 68: local.get */
  /* Wasm instruction 69: i32.const */
  /* Wasm instruction 70: i32.add */
  unsigned int t12 = t7 + 2U;
  /*@ assert address_normalization: t12 == d + (10); */
  /* Wasm instruction 71: local.get */
  /* Wasm instruction 72: i32.const */
  /* Wasm instruction 73: i32.add */
  unsigned int t13 = t9 + 2U;
  /*@ assert address_normalization: t13 == s + (10); */
  /* Wasm instruction 74: i32.load8_u */
  /*@ assert physical_bounds: t13 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t13 && t13 + 1 <= s + n; */
  unsigned int t14 = ((unsigned int)m[t13 + 0U] << 0);
  /* Wasm instruction 75: i32.store8 */
  /*@ assert physical_bounds: t12 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t12 && t12 + 1 <= d + n; */
  m[t12 + 0U] = (unsigned char)(t14 >> 0);
  /* Wasm instruction 76: local.get */
  /* Wasm instruction 77: i32.const */
  /* Wasm instruction 78: i32.add */
  unsigned int t15 = t7 + 1U;
  /*@ assert address_normalization: t15 == d + (9); */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: i32.const */
  /* Wasm instruction 81: i32.add */
  unsigned int t16 = t9 + 1U;
  /*@ assert address_normalization: t16 == s + (9); */
  /* Wasm instruction 82: i32.load8_u */
  /*@ assert physical_bounds: t16 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t16 && t16 + 1 <= s + n; */
  unsigned int t17 = ((unsigned int)m[t16 + 0U] << 0);
  /* Wasm instruction 83: i32.store8 */
  /*@ assert physical_bounds: t15 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t15 && t15 + 1 <= d + n; */
  m[t15 + 0U] = (unsigned char)(t17 >> 0);
  /* Wasm instruction 84: local.get */
  /* Wasm instruction 85: local.get */
  /* Wasm instruction 86: i32.load8_u */
  /*@ assert physical_bounds: t9 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t9 && t9 + 1 <= s + n; */
  unsigned int t18 = ((unsigned int)m[t9 + 0U] << 0);
  /* Wasm instruction 87: i32.store8 */
  /*@ assert physical_bounds: t7 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t7 && t7 + 1 <= d + n; */
  m[t7 + 0U] = (unsigned char)(t18 >> 0);
  /* Wasm instruction 88: local.get */
  /* Wasm instruction 89: i32.const */
  /* Wasm instruction 90: i32.add */
  unsigned int t19 = 12U + 4294967292U;
  /* Wasm instruction 91: local.tee */
  /* Wasm instruction 92: br_if */
  /*@ assert branch_5: t19 != 0; */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: local.get */
  /* Wasm instruction 56: i32.add */
  unsigned int t20 = t6 + t19;
  /*@ assert address_normalization: t20 == d + (4); */
  /* Wasm instruction 57: local.tee */
  /* Wasm instruction 58: i32.const */
  /* Wasm instruction 59: i32.add */
  unsigned int t21 = t20 + 3U;
  /*@ assert address_normalization: t21 == d + (7); */
  /* Wasm instruction 60: local.get */
  /* Wasm instruction 61: local.get */
  /* Wasm instruction 62: i32.add */
  unsigned int t22 = t5 + t19;
  /*@ assert address_normalization: t22 == s + (4); */
  /* Wasm instruction 63: local.tee */
  /* Wasm instruction 64: i32.const */
  /* Wasm instruction 65: i32.add */
  unsigned int t23 = t22 + 3U;
  /*@ assert address_normalization: t23 == s + (7); */
  /* Wasm instruction 66: i32.load8_u */
  /*@ assert physical_bounds: t23 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t23 && t23 + 1 <= s + n; */
  unsigned int t24 = ((unsigned int)m[t23 + 0U] << 0);
  /* Wasm instruction 67: i32.store8 */
  /*@ assert physical_bounds: t21 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t21 && t21 + 1 <= d + n; */
  m[t21 + 0U] = (unsigned char)(t24 >> 0);
  /* Wasm instruction 68: local.get */
  /* Wasm instruction 69: i32.const */
  /* Wasm instruction 70: i32.add */
  unsigned int t25 = t20 + 2U;
  /*@ assert address_normalization: t25 == d + (6); */
  /* Wasm instruction 71: local.get */
  /* Wasm instruction 72: i32.const */
  /* Wasm instruction 73: i32.add */
  unsigned int t26 = t22 + 2U;
  /*@ assert address_normalization: t26 == s + (6); */
  /* Wasm instruction 74: i32.load8_u */
  /*@ assert physical_bounds: t26 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t26 && t26 + 1 <= s + n; */
  unsigned int t27 = ((unsigned int)m[t26 + 0U] << 0);
  /* Wasm instruction 75: i32.store8 */
  /*@ assert physical_bounds: t25 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t25 && t25 + 1 <= d + n; */
  m[t25 + 0U] = (unsigned char)(t27 >> 0);
  /* Wasm instruction 76: local.get */
  /* Wasm instruction 77: i32.const */
  /* Wasm instruction 78: i32.add */
  unsigned int t28 = t20 + 1U;
  /*@ assert address_normalization: t28 == d + (5); */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: i32.const */
  /* Wasm instruction 81: i32.add */
  unsigned int t29 = t22 + 1U;
  /*@ assert address_normalization: t29 == s + (5); */
  /* Wasm instruction 82: i32.load8_u */
  /*@ assert physical_bounds: t29 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t29 && t29 + 1 <= s + n; */
  unsigned int t30 = ((unsigned int)m[t29 + 0U] << 0);
  /* Wasm instruction 83: i32.store8 */
  /*@ assert physical_bounds: t28 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t28 && t28 + 1 <= d + n; */
  m[t28 + 0U] = (unsigned char)(t30 >> 0);
  /* Wasm instruction 84: local.get */
  /* Wasm instruction 85: local.get */
  /* Wasm instruction 86: i32.load8_u */
  /*@ assert physical_bounds: t22 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t22 && t22 + 1 <= s + n; */
  unsigned int t31 = ((unsigned int)m[t22 + 0U] << 0);
  /* Wasm instruction 87: i32.store8 */
  /*@ assert physical_bounds: t20 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t20 && t20 + 1 <= d + n; */
  m[t20 + 0U] = (unsigned char)(t31 >> 0);
  /* Wasm instruction 88: local.get */
  /* Wasm instruction 89: i32.const */
  /* Wasm instruction 90: i32.add */
  unsigned int t32 = t19 + 4294967292U;
  /* Wasm instruction 91: local.tee */
  /* Wasm instruction 92: br_if */
  /*@ assert branch_5: t32 != 0; */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: local.get */
  /* Wasm instruction 56: i32.add */
  unsigned int t33 = t6 + t32;
  /*@ assert address_normalization: t33 == d + (0); */
  /* Wasm instruction 57: local.tee */
  /* Wasm instruction 58: i32.const */
  /* Wasm instruction 59: i32.add */
  unsigned int t34 = t33 + 3U;
  /*@ assert address_normalization: t34 == d + (3); */
  /* Wasm instruction 60: local.get */
  /* Wasm instruction 61: local.get */
  /* Wasm instruction 62: i32.add */
  unsigned int t35 = t5 + t32;
  /*@ assert address_normalization: t35 == s + (0); */
  /* Wasm instruction 63: local.tee */
  /* Wasm instruction 64: i32.const */
  /* Wasm instruction 65: i32.add */
  unsigned int t36 = t35 + 3U;
  /*@ assert address_normalization: t36 == s + (3); */
  /* Wasm instruction 66: i32.load8_u */
  /*@ assert physical_bounds: t36 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t36 && t36 + 1 <= s + n; */
  unsigned int t37 = ((unsigned int)m[t36 + 0U] << 0);
  /* Wasm instruction 67: i32.store8 */
  /*@ assert physical_bounds: t34 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t34 && t34 + 1 <= d + n; */
  m[t34 + 0U] = (unsigned char)(t37 >> 0);
  /* Wasm instruction 68: local.get */
  /* Wasm instruction 69: i32.const */
  /* Wasm instruction 70: i32.add */
  unsigned int t38 = t33 + 2U;
  /*@ assert address_normalization: t38 == d + (2); */
  /* Wasm instruction 71: local.get */
  /* Wasm instruction 72: i32.const */
  /* Wasm instruction 73: i32.add */
  unsigned int t39 = t35 + 2U;
  /*@ assert address_normalization: t39 == s + (2); */
  /* Wasm instruction 74: i32.load8_u */
  /*@ assert physical_bounds: t39 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t39 && t39 + 1 <= s + n; */
  unsigned int t40 = ((unsigned int)m[t39 + 0U] << 0);
  /* Wasm instruction 75: i32.store8 */
  /*@ assert physical_bounds: t38 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t38 && t38 + 1 <= d + n; */
  m[t38 + 0U] = (unsigned char)(t40 >> 0);
  /* Wasm instruction 76: local.get */
  /* Wasm instruction 77: i32.const */
  /* Wasm instruction 78: i32.add */
  unsigned int t41 = t33 + 1U;
  /*@ assert address_normalization: t41 == d + (1); */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: i32.const */
  /* Wasm instruction 81: i32.add */
  unsigned int t42 = t35 + 1U;
  /*@ assert address_normalization: t42 == s + (1); */
  /* Wasm instruction 82: i32.load8_u */
  /*@ assert physical_bounds: t42 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t42 && t42 + 1 <= s + n; */
  unsigned int t43 = ((unsigned int)m[t42 + 0U] << 0);
  /* Wasm instruction 83: i32.store8 */
  /*@ assert physical_bounds: t41 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t41 && t41 + 1 <= d + n; */
  m[t41 + 0U] = (unsigned char)(t43 >> 0);
  /* Wasm instruction 84: local.get */
  /* Wasm instruction 85: local.get */
  /* Wasm instruction 86: i32.load8_u */
  /*@ assert physical_bounds: t35 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t35 && t35 + 1 <= s + n; */
  unsigned int t44 = ((unsigned int)m[t35 + 0U] << 0);
  /* Wasm instruction 87: i32.store8 */
  /*@ assert physical_bounds: t33 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t33 && t33 + 1 <= d + n; */
  m[t33 + 0U] = (unsigned char)(t44 >> 0);
  /* Wasm instruction 88: local.get */
  /* Wasm instruction 89: i32.const */
  /* Wasm instruction 90: i32.add */
  unsigned int t45 = t32 + 4294967292U;
  /* Wasm instruction 91: local.tee */
  /* Wasm instruction 92: br_if */
  /*@ assert branch_5: t45 == 0; */
  /* Wasm instruction 93: br */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  /*@ assert copied_byte_3: m[d+3] == \at(m[s+3],Pre); */
  /*@ assert copied_byte_4: m[d+4] == \at(m[s+4],Pre); */
  /*@ assert copied_byte_5: m[d+5] == \at(m[s+5],Pre); */
  /*@ assert copied_byte_6: m[d+6] == \at(m[s+6],Pre); */
  /*@ assert copied_byte_7: m[d+7] == \at(m[s+7],Pre); */
  /*@ assert copied_byte_8: m[d+8] == \at(m[s+8],Pre); */
  /*@ assert copied_byte_9: m[d+9] == \at(m[s+9],Pre); */
  /*@ assert copied_byte_10: m[d+10] == \at(m[s+10],Pre); */
  /*@ assert copied_byte_11: m[d+11] == \at(m[s+11],Pre); */
  return d;
}
/*@
  requires specialization: n == 12 && d < s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
  ensures byte_3: m[d+3] == \old(m[s+3]);
  ensures byte_4: m[d+4] == \old(m[s+4]);
  ensures byte_5: m[d+5] == \old(m[s+5]);
  ensures byte_6: m[d+6] == \old(m[s+6]);
  ensures byte_7: m[d+7] == \old(m[s+7]);
  ensures byte_8: m[d+8] == \old(m[s+8]);
  ensures byte_9: m[d+9] == \old(m[s+9]);
  ensures byte_10: m[d+10] == \old(m[s+10]);
  ensures byte_11: m[d+11] == \old(m[s+11]);
*/
unsigned int move4_12_1(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 12; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 != 0; */
  /* Wasm instruction 94: local.get */
  /* Wasm instruction 95: i32.eqz */
  unsigned int t1 = !12U;
  /* Wasm instruction 96: br_if */
  /*@ assert branch_6: t1 == 0; */
  /* Wasm instruction 97: local.get */
  /* Wasm instruction 98: i32.const */
  /* Wasm instruction 99: i32.and */
  unsigned int t2 = 12U & 3U;
  /* Wasm instruction 100: local.set */
  /* Wasm instruction 101: i32.const */
  /* Wasm instruction 102: local.set */
  /* Wasm instruction 103: local.get */
  /* Wasm instruction 104: i32.const */
  /* Wasm instruction 105: i32.lt_u */
  unsigned int t3 = 12U < 4U;
  /* Wasm instruction 106: br_if */
  /*@ assert branch_7: t3 == 0; */
  /* Wasm instruction 107: local.get */
  /* Wasm instruction 108: i32.const */
  /* Wasm instruction 109: i32.and */
  unsigned int t4 = 12U & 4294967292U;
  /* Wasm instruction 110: local.set */
  /* Wasm instruction 111: i32.const */
  /* Wasm instruction 112: local.set */
  /* Wasm instruction 113: local.get */
  /* Wasm instruction 114: local.get */
  /* Wasm instruction 115: i32.add */
  unsigned int t5 = d + 0U;
  /*@ assert address_normalization: t5 == d + (0); */
  /* Wasm instruction 116: local.tee */
  /* Wasm instruction 117: local.get */
  /* Wasm instruction 118: local.get */
  /* Wasm instruction 119: i32.add */
  unsigned int t6 = s + 0U;
  /*@ assert address_normalization: t6 == s + (0); */
  /* Wasm instruction 120: local.tee */
  /* Wasm instruction 121: i32.load8_u */
  /*@ assert physical_bounds: t6 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t6 && t6 + 1 <= s + n; */
  unsigned int t7 = ((unsigned int)m[t6 + 0U] << 0);
  /* Wasm instruction 122: i32.store8 */
  /*@ assert physical_bounds: t5 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t5 && t5 + 1 <= d + n; */
  m[t5 + 0U] = (unsigned char)(t7 >> 0);
  /* Wasm instruction 123: local.get */
  /* Wasm instruction 124: i32.const */
  /* Wasm instruction 125: i32.add */
  unsigned int t8 = t5 + 1U;
  /*@ assert address_normalization: t8 == d + (1); */
  /* Wasm instruction 126: local.get */
  /* Wasm instruction 127: i32.const */
  /* Wasm instruction 128: i32.add */
  unsigned int t9 = t6 + 1U;
  /*@ assert address_normalization: t9 == s + (1); */
  /* Wasm instruction 129: i32.load8_u */
  /*@ assert physical_bounds: t9 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t9 && t9 + 1 <= s + n; */
  unsigned int t10 = ((unsigned int)m[t9 + 0U] << 0);
  /* Wasm instruction 130: i32.store8 */
  /*@ assert physical_bounds: t8 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t8 && t8 + 1 <= d + n; */
  m[t8 + 0U] = (unsigned char)(t10 >> 0);
  /* Wasm instruction 131: local.get */
  /* Wasm instruction 132: i32.const */
  /* Wasm instruction 133: i32.add */
  unsigned int t11 = t5 + 2U;
  /*@ assert address_normalization: t11 == d + (2); */
  /* Wasm instruction 134: local.get */
  /* Wasm instruction 135: i32.const */
  /* Wasm instruction 136: i32.add */
  unsigned int t12 = t6 + 2U;
  /*@ assert address_normalization: t12 == s + (2); */
  /* Wasm instruction 137: i32.load8_u */
  /*@ assert physical_bounds: t12 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t12 && t12 + 1 <= s + n; */
  unsigned int t13 = ((unsigned int)m[t12 + 0U] << 0);
  /* Wasm instruction 138: i32.store8 */
  /*@ assert physical_bounds: t11 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t11 && t11 + 1 <= d + n; */
  m[t11 + 0U] = (unsigned char)(t13 >> 0);
  /* Wasm instruction 139: local.get */
  /* Wasm instruction 140: i32.const */
  /* Wasm instruction 141: i32.add */
  unsigned int t14 = t5 + 3U;
  /*@ assert address_normalization: t14 == d + (3); */
  /* Wasm instruction 142: local.get */
  /* Wasm instruction 143: i32.const */
  /* Wasm instruction 144: i32.add */
  unsigned int t15 = t6 + 3U;
  /*@ assert address_normalization: t15 == s + (3); */
  /* Wasm instruction 145: i32.load8_u */
  /*@ assert physical_bounds: t15 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t15 && t15 + 1 <= s + n; */
  unsigned int t16 = ((unsigned int)m[t15 + 0U] << 0);
  /* Wasm instruction 146: i32.store8 */
  /*@ assert physical_bounds: t14 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t14 && t14 + 1 <= d + n; */
  m[t14 + 0U] = (unsigned char)(t16 >> 0);
  /* Wasm instruction 147: local.get */
  /* Wasm instruction 148: local.get */
  /* Wasm instruction 149: i32.const */
  /* Wasm instruction 150: i32.add */
  unsigned int t17 = 0U + 4U;
  /* Wasm instruction 151: local.tee */
  /* Wasm instruction 152: i32.ne */
  unsigned int t18 = t4 != t17;
  /* Wasm instruction 153: br_if */
  /*@ assert branch_8: t18 != 0; */
  /* Wasm instruction 113: local.get */
  /* Wasm instruction 114: local.get */
  /* Wasm instruction 115: i32.add */
  unsigned int t19 = d + t17;
  /*@ assert address_normalization: t19 == d + (4); */
  /* Wasm instruction 116: local.tee */
  /* Wasm instruction 117: local.get */
  /* Wasm instruction 118: local.get */
  /* Wasm instruction 119: i32.add */
  unsigned int t20 = s + t17;
  /*@ assert address_normalization: t20 == s + (4); */
  /* Wasm instruction 120: local.tee */
  /* Wasm instruction 121: i32.load8_u */
  /*@ assert physical_bounds: t20 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t20 && t20 + 1 <= s + n; */
  unsigned int t21 = ((unsigned int)m[t20 + 0U] << 0);
  /* Wasm instruction 122: i32.store8 */
  /*@ assert physical_bounds: t19 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t19 && t19 + 1 <= d + n; */
  m[t19 + 0U] = (unsigned char)(t21 >> 0);
  /* Wasm instruction 123: local.get */
  /* Wasm instruction 124: i32.const */
  /* Wasm instruction 125: i32.add */
  unsigned int t22 = t19 + 1U;
  /*@ assert address_normalization: t22 == d + (5); */
  /* Wasm instruction 126: local.get */
  /* Wasm instruction 127: i32.const */
  /* Wasm instruction 128: i32.add */
  unsigned int t23 = t20 + 1U;
  /*@ assert address_normalization: t23 == s + (5); */
  /* Wasm instruction 129: i32.load8_u */
  /*@ assert physical_bounds: t23 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t23 && t23 + 1 <= s + n; */
  unsigned int t24 = ((unsigned int)m[t23 + 0U] << 0);
  /* Wasm instruction 130: i32.store8 */
  /*@ assert physical_bounds: t22 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t22 && t22 + 1 <= d + n; */
  m[t22 + 0U] = (unsigned char)(t24 >> 0);
  /* Wasm instruction 131: local.get */
  /* Wasm instruction 132: i32.const */
  /* Wasm instruction 133: i32.add */
  unsigned int t25 = t19 + 2U;
  /*@ assert address_normalization: t25 == d + (6); */
  /* Wasm instruction 134: local.get */
  /* Wasm instruction 135: i32.const */
  /* Wasm instruction 136: i32.add */
  unsigned int t26 = t20 + 2U;
  /*@ assert address_normalization: t26 == s + (6); */
  /* Wasm instruction 137: i32.load8_u */
  /*@ assert physical_bounds: t26 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t26 && t26 + 1 <= s + n; */
  unsigned int t27 = ((unsigned int)m[t26 + 0U] << 0);
  /* Wasm instruction 138: i32.store8 */
  /*@ assert physical_bounds: t25 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t25 && t25 + 1 <= d + n; */
  m[t25 + 0U] = (unsigned char)(t27 >> 0);
  /* Wasm instruction 139: local.get */
  /* Wasm instruction 140: i32.const */
  /* Wasm instruction 141: i32.add */
  unsigned int t28 = t19 + 3U;
  /*@ assert address_normalization: t28 == d + (7); */
  /* Wasm instruction 142: local.get */
  /* Wasm instruction 143: i32.const */
  /* Wasm instruction 144: i32.add */
  unsigned int t29 = t20 + 3U;
  /*@ assert address_normalization: t29 == s + (7); */
  /* Wasm instruction 145: i32.load8_u */
  /*@ assert physical_bounds: t29 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t29 && t29 + 1 <= s + n; */
  unsigned int t30 = ((unsigned int)m[t29 + 0U] << 0);
  /* Wasm instruction 146: i32.store8 */
  /*@ assert physical_bounds: t28 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t28 && t28 + 1 <= d + n; */
  m[t28 + 0U] = (unsigned char)(t30 >> 0);
  /* Wasm instruction 147: local.get */
  /* Wasm instruction 148: local.get */
  /* Wasm instruction 149: i32.const */
  /* Wasm instruction 150: i32.add */
  unsigned int t31 = t17 + 4U;
  /* Wasm instruction 151: local.tee */
  /* Wasm instruction 152: i32.ne */
  unsigned int t32 = t4 != t31;
  /* Wasm instruction 153: br_if */
  /*@ assert branch_8: t32 != 0; */
  /* Wasm instruction 113: local.get */
  /* Wasm instruction 114: local.get */
  /* Wasm instruction 115: i32.add */
  unsigned int t33 = d + t31;
  /*@ assert address_normalization: t33 == d + (8); */
  /* Wasm instruction 116: local.tee */
  /* Wasm instruction 117: local.get */
  /* Wasm instruction 118: local.get */
  /* Wasm instruction 119: i32.add */
  unsigned int t34 = s + t31;
  /*@ assert address_normalization: t34 == s + (8); */
  /* Wasm instruction 120: local.tee */
  /* Wasm instruction 121: i32.load8_u */
  /*@ assert physical_bounds: t34 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t34 && t34 + 1 <= s + n; */
  unsigned int t35 = ((unsigned int)m[t34 + 0U] << 0);
  /* Wasm instruction 122: i32.store8 */
  /*@ assert physical_bounds: t33 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t33 && t33 + 1 <= d + n; */
  m[t33 + 0U] = (unsigned char)(t35 >> 0);
  /* Wasm instruction 123: local.get */
  /* Wasm instruction 124: i32.const */
  /* Wasm instruction 125: i32.add */
  unsigned int t36 = t33 + 1U;
  /*@ assert address_normalization: t36 == d + (9); */
  /* Wasm instruction 126: local.get */
  /* Wasm instruction 127: i32.const */
  /* Wasm instruction 128: i32.add */
  unsigned int t37 = t34 + 1U;
  /*@ assert address_normalization: t37 == s + (9); */
  /* Wasm instruction 129: i32.load8_u */
  /*@ assert physical_bounds: t37 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t37 && t37 + 1 <= s + n; */
  unsigned int t38 = ((unsigned int)m[t37 + 0U] << 0);
  /* Wasm instruction 130: i32.store8 */
  /*@ assert physical_bounds: t36 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t36 && t36 + 1 <= d + n; */
  m[t36 + 0U] = (unsigned char)(t38 >> 0);
  /* Wasm instruction 131: local.get */
  /* Wasm instruction 132: i32.const */
  /* Wasm instruction 133: i32.add */
  unsigned int t39 = t33 + 2U;
  /*@ assert address_normalization: t39 == d + (10); */
  /* Wasm instruction 134: local.get */
  /* Wasm instruction 135: i32.const */
  /* Wasm instruction 136: i32.add */
  unsigned int t40 = t34 + 2U;
  /*@ assert address_normalization: t40 == s + (10); */
  /* Wasm instruction 137: i32.load8_u */
  /*@ assert physical_bounds: t40 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t40 && t40 + 1 <= s + n; */
  unsigned int t41 = ((unsigned int)m[t40 + 0U] << 0);
  /* Wasm instruction 138: i32.store8 */
  /*@ assert physical_bounds: t39 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t39 && t39 + 1 <= d + n; */
  m[t39 + 0U] = (unsigned char)(t41 >> 0);
  /* Wasm instruction 139: local.get */
  /* Wasm instruction 140: i32.const */
  /* Wasm instruction 141: i32.add */
  unsigned int t42 = t33 + 3U;
  /*@ assert address_normalization: t42 == d + (11); */
  /* Wasm instruction 142: local.get */
  /* Wasm instruction 143: i32.const */
  /* Wasm instruction 144: i32.add */
  unsigned int t43 = t34 + 3U;
  /*@ assert address_normalization: t43 == s + (11); */
  /* Wasm instruction 145: i32.load8_u */
  /*@ assert physical_bounds: t43 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t43 && t43 + 1 <= s + n; */
  unsigned int t44 = ((unsigned int)m[t43 + 0U] << 0);
  /* Wasm instruction 146: i32.store8 */
  /*@ assert physical_bounds: t42 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t42 && t42 + 1 <= d + n; */
  m[t42 + 0U] = (unsigned char)(t44 >> 0);
  /* Wasm instruction 147: local.get */
  /* Wasm instruction 148: local.get */
  /* Wasm instruction 149: i32.const */
  /* Wasm instruction 150: i32.add */
  unsigned int t45 = t31 + 4U;
  /* Wasm instruction 151: local.tee */
  /* Wasm instruction 152: i32.ne */
  unsigned int t46 = t4 != t45;
  /* Wasm instruction 153: br_if */
  /*@ assert branch_8: t46 == 0; */
  /* Wasm instruction 154: local.get */
  /* Wasm instruction 155: i32.eqz */
  unsigned int t47 = !t2;
  /* Wasm instruction 156: br_if */
  /*@ assert branch_9: t47 != 0; */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  /*@ assert copied_byte_3: m[d+3] == \at(m[s+3],Pre); */
  /*@ assert copied_byte_4: m[d+4] == \at(m[s+4],Pre); */
  /*@ assert copied_byte_5: m[d+5] == \at(m[s+5],Pre); */
  /*@ assert copied_byte_6: m[d+6] == \at(m[s+6],Pre); */
  /*@ assert copied_byte_7: m[d+7] == \at(m[s+7],Pre); */
  /*@ assert copied_byte_8: m[d+8] == \at(m[s+8],Pre); */
  /*@ assert copied_byte_9: m[d+9] == \at(m[s+9],Pre); */
  /*@ assert copied_byte_10: m[d+10] == \at(m[s+10],Pre); */
  /*@ assert copied_byte_11: m[d+11] == \at(m[s+11],Pre); */
  return d;
}
/*@
  requires specialization: n == 13 && d >= s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
  ensures byte_3: m[d+3] == \old(m[s+3]);
  ensures byte_4: m[d+4] == \old(m[s+4]);
  ensures byte_5: m[d+5] == \old(m[s+5]);
  ensures byte_6: m[d+6] == \old(m[s+6]);
  ensures byte_7: m[d+7] == \old(m[s+7]);
  ensures byte_8: m[d+8] == \old(m[s+8]);
  ensures byte_9: m[d+9] == \old(m[s+9]);
  ensures byte_10: m[d+10] == \old(m[s+10]);
  ensures byte_11: m[d+11] == \old(m[s+11]);
  ensures byte_12: m[d+12] == \old(m[s+12]);
*/
unsigned int move4_13_0(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 13; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 == 0; */
  /* Wasm instruction 4: local.get */
  /* Wasm instruction 5: i32.eqz */
  unsigned int t1 = !13U;
  /* Wasm instruction 6: br_if */
  /*@ assert branch_1: t1 == 0; */
  /* Wasm instruction 7: local.get */
  /* Wasm instruction 8: local.set */
  /* Wasm instruction 9: local.get */
  /* Wasm instruction 10: i32.const */
  /* Wasm instruction 11: i32.and */
  unsigned int t2 = 13U & 3U;
  /* Wasm instruction 12: local.tee */
  /* Wasm instruction 13: i32.eqz */
  unsigned int t3 = !t2;
  /* Wasm instruction 14: br_if */
  /*@ assert branch_2: t3 == 0; */
  /* Wasm instruction 15: local.get */
  /* Wasm instruction 16: i32.const */
  /* Wasm instruction 17: i32.add */
  unsigned int t4 = s + 4294967295U;
  /*@ assert address_normalization: t4 == s + (-1); */
  /* Wasm instruction 18: local.set */
  /* Wasm instruction 19: local.get */
  /* Wasm instruction 20: i32.const */
  /* Wasm instruction 21: i32.add */
  unsigned int t5 = d + 4294967295U;
  /*@ assert address_normalization: t5 == d + (-1); */
  /* Wasm instruction 22: local.set */
  /* Wasm instruction 23: local.get */
  /* Wasm instruction 24: local.set */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: local.get */
  /* Wasm instruction 27: i32.add */
  unsigned int t6 = t5 + 13U;
  /*@ assert address_normalization: t6 == d + (12); */
  /* Wasm instruction 28: local.get */
  /* Wasm instruction 29: local.get */
  /* Wasm instruction 30: i32.add */
  unsigned int t7 = t4 + 13U;
  /*@ assert address_normalization: t7 == s + (12); */
  /* Wasm instruction 31: i32.load8_u */
  /*@ assert physical_bounds: t7 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t7 && t7 + 1 <= s + n; */
  unsigned int t8 = ((unsigned int)m[t7 + 0U] << 0);
  /* Wasm instruction 32: i32.store8 */
  /*@ assert physical_bounds: t6 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t6 && t6 + 1 <= d + n; */
  m[t6 + 0U] = (unsigned char)(t8 >> 0);
  /* Wasm instruction 33: local.get */
  /* Wasm instruction 34: i32.const */
  /* Wasm instruction 35: i32.add */
  unsigned int t9 = 13U + 4294967295U;
  /* Wasm instruction 36: local.set */
  /* Wasm instruction 37: local.get */
  /* Wasm instruction 38: i32.const */
  /* Wasm instruction 39: i32.add */
  unsigned int t10 = t2 + 4294967295U;
  /* Wasm instruction 40: local.tee */
  /* Wasm instruction 41: br_if */
  /*@ assert branch_3: t10 == 0; */
  /* Wasm instruction 42: local.get */
  /* Wasm instruction 43: i32.const */
  /* Wasm instruction 44: i32.lt_u */
  unsigned int t11 = 13U < 4U;
  /* Wasm instruction 45: br_if */
  /*@ assert branch_4: t11 == 0; */
  /* Wasm instruction 46: local.get */
  /* Wasm instruction 47: i32.const */
  /* Wasm instruction 48: i32.add */
  unsigned int t12 = s + 4294967292U;
  /*@ assert address_normalization: t12 == s + (-4); */
  /* Wasm instruction 49: local.set */
  /* Wasm instruction 50: local.get */
  /* Wasm instruction 51: i32.const */
  /* Wasm instruction 52: i32.add */
  unsigned int t13 = d + 4294967292U;
  /*@ assert address_normalization: t13 == d + (-4); */
  /* Wasm instruction 53: local.set */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: local.get */
  /* Wasm instruction 56: i32.add */
  unsigned int t14 = t13 + t9;
  /*@ assert address_normalization: t14 == d + (8); */
  /* Wasm instruction 57: local.tee */
  /* Wasm instruction 58: i32.const */
  /* Wasm instruction 59: i32.add */
  unsigned int t15 = t14 + 3U;
  /*@ assert address_normalization: t15 == d + (11); */
  /* Wasm instruction 60: local.get */
  /* Wasm instruction 61: local.get */
  /* Wasm instruction 62: i32.add */
  unsigned int t16 = t12 + t9;
  /*@ assert address_normalization: t16 == s + (8); */
  /* Wasm instruction 63: local.tee */
  /* Wasm instruction 64: i32.const */
  /* Wasm instruction 65: i32.add */
  unsigned int t17 = t16 + 3U;
  /*@ assert address_normalization: t17 == s + (11); */
  /* Wasm instruction 66: i32.load8_u */
  /*@ assert physical_bounds: t17 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t17 && t17 + 1 <= s + n; */
  unsigned int t18 = ((unsigned int)m[t17 + 0U] << 0);
  /* Wasm instruction 67: i32.store8 */
  /*@ assert physical_bounds: t15 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t15 && t15 + 1 <= d + n; */
  m[t15 + 0U] = (unsigned char)(t18 >> 0);
  /* Wasm instruction 68: local.get */
  /* Wasm instruction 69: i32.const */
  /* Wasm instruction 70: i32.add */
  unsigned int t19 = t14 + 2U;
  /*@ assert address_normalization: t19 == d + (10); */
  /* Wasm instruction 71: local.get */
  /* Wasm instruction 72: i32.const */
  /* Wasm instruction 73: i32.add */
  unsigned int t20 = t16 + 2U;
  /*@ assert address_normalization: t20 == s + (10); */
  /* Wasm instruction 74: i32.load8_u */
  /*@ assert physical_bounds: t20 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t20 && t20 + 1 <= s + n; */
  unsigned int t21 = ((unsigned int)m[t20 + 0U] << 0);
  /* Wasm instruction 75: i32.store8 */
  /*@ assert physical_bounds: t19 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t19 && t19 + 1 <= d + n; */
  m[t19 + 0U] = (unsigned char)(t21 >> 0);
  /* Wasm instruction 76: local.get */
  /* Wasm instruction 77: i32.const */
  /* Wasm instruction 78: i32.add */
  unsigned int t22 = t14 + 1U;
  /*@ assert address_normalization: t22 == d + (9); */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: i32.const */
  /* Wasm instruction 81: i32.add */
  unsigned int t23 = t16 + 1U;
  /*@ assert address_normalization: t23 == s + (9); */
  /* Wasm instruction 82: i32.load8_u */
  /*@ assert physical_bounds: t23 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t23 && t23 + 1 <= s + n; */
  unsigned int t24 = ((unsigned int)m[t23 + 0U] << 0);
  /* Wasm instruction 83: i32.store8 */
  /*@ assert physical_bounds: t22 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t22 && t22 + 1 <= d + n; */
  m[t22 + 0U] = (unsigned char)(t24 >> 0);
  /* Wasm instruction 84: local.get */
  /* Wasm instruction 85: local.get */
  /* Wasm instruction 86: i32.load8_u */
  /*@ assert physical_bounds: t16 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t16 && t16 + 1 <= s + n; */
  unsigned int t25 = ((unsigned int)m[t16 + 0U] << 0);
  /* Wasm instruction 87: i32.store8 */
  /*@ assert physical_bounds: t14 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t14 && t14 + 1 <= d + n; */
  m[t14 + 0U] = (unsigned char)(t25 >> 0);
  /* Wasm instruction 88: local.get */
  /* Wasm instruction 89: i32.const */
  /* Wasm instruction 90: i32.add */
  unsigned int t26 = t9 + 4294967292U;
  /* Wasm instruction 91: local.tee */
  /* Wasm instruction 92: br_if */
  /*@ assert branch_5: t26 != 0; */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: local.get */
  /* Wasm instruction 56: i32.add */
  unsigned int t27 = t13 + t26;
  /*@ assert address_normalization: t27 == d + (4); */
  /* Wasm instruction 57: local.tee */
  /* Wasm instruction 58: i32.const */
  /* Wasm instruction 59: i32.add */
  unsigned int t28 = t27 + 3U;
  /*@ assert address_normalization: t28 == d + (7); */
  /* Wasm instruction 60: local.get */
  /* Wasm instruction 61: local.get */
  /* Wasm instruction 62: i32.add */
  unsigned int t29 = t12 + t26;
  /*@ assert address_normalization: t29 == s + (4); */
  /* Wasm instruction 63: local.tee */
  /* Wasm instruction 64: i32.const */
  /* Wasm instruction 65: i32.add */
  unsigned int t30 = t29 + 3U;
  /*@ assert address_normalization: t30 == s + (7); */
  /* Wasm instruction 66: i32.load8_u */
  /*@ assert physical_bounds: t30 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t30 && t30 + 1 <= s + n; */
  unsigned int t31 = ((unsigned int)m[t30 + 0U] << 0);
  /* Wasm instruction 67: i32.store8 */
  /*@ assert physical_bounds: t28 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t28 && t28 + 1 <= d + n; */
  m[t28 + 0U] = (unsigned char)(t31 >> 0);
  /* Wasm instruction 68: local.get */
  /* Wasm instruction 69: i32.const */
  /* Wasm instruction 70: i32.add */
  unsigned int t32 = t27 + 2U;
  /*@ assert address_normalization: t32 == d + (6); */
  /* Wasm instruction 71: local.get */
  /* Wasm instruction 72: i32.const */
  /* Wasm instruction 73: i32.add */
  unsigned int t33 = t29 + 2U;
  /*@ assert address_normalization: t33 == s + (6); */
  /* Wasm instruction 74: i32.load8_u */
  /*@ assert physical_bounds: t33 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t33 && t33 + 1 <= s + n; */
  unsigned int t34 = ((unsigned int)m[t33 + 0U] << 0);
  /* Wasm instruction 75: i32.store8 */
  /*@ assert physical_bounds: t32 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t32 && t32 + 1 <= d + n; */
  m[t32 + 0U] = (unsigned char)(t34 >> 0);
  /* Wasm instruction 76: local.get */
  /* Wasm instruction 77: i32.const */
  /* Wasm instruction 78: i32.add */
  unsigned int t35 = t27 + 1U;
  /*@ assert address_normalization: t35 == d + (5); */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: i32.const */
  /* Wasm instruction 81: i32.add */
  unsigned int t36 = t29 + 1U;
  /*@ assert address_normalization: t36 == s + (5); */
  /* Wasm instruction 82: i32.load8_u */
  /*@ assert physical_bounds: t36 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t36 && t36 + 1 <= s + n; */
  unsigned int t37 = ((unsigned int)m[t36 + 0U] << 0);
  /* Wasm instruction 83: i32.store8 */
  /*@ assert physical_bounds: t35 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t35 && t35 + 1 <= d + n; */
  m[t35 + 0U] = (unsigned char)(t37 >> 0);
  /* Wasm instruction 84: local.get */
  /* Wasm instruction 85: local.get */
  /* Wasm instruction 86: i32.load8_u */
  /*@ assert physical_bounds: t29 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t29 && t29 + 1 <= s + n; */
  unsigned int t38 = ((unsigned int)m[t29 + 0U] << 0);
  /* Wasm instruction 87: i32.store8 */
  /*@ assert physical_bounds: t27 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t27 && t27 + 1 <= d + n; */
  m[t27 + 0U] = (unsigned char)(t38 >> 0);
  /* Wasm instruction 88: local.get */
  /* Wasm instruction 89: i32.const */
  /* Wasm instruction 90: i32.add */
  unsigned int t39 = t26 + 4294967292U;
  /* Wasm instruction 91: local.tee */
  /* Wasm instruction 92: br_if */
  /*@ assert branch_5: t39 != 0; */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: local.get */
  /* Wasm instruction 56: i32.add */
  unsigned int t40 = t13 + t39;
  /*@ assert address_normalization: t40 == d + (0); */
  /* Wasm instruction 57: local.tee */
  /* Wasm instruction 58: i32.const */
  /* Wasm instruction 59: i32.add */
  unsigned int t41 = t40 + 3U;
  /*@ assert address_normalization: t41 == d + (3); */
  /* Wasm instruction 60: local.get */
  /* Wasm instruction 61: local.get */
  /* Wasm instruction 62: i32.add */
  unsigned int t42 = t12 + t39;
  /*@ assert address_normalization: t42 == s + (0); */
  /* Wasm instruction 63: local.tee */
  /* Wasm instruction 64: i32.const */
  /* Wasm instruction 65: i32.add */
  unsigned int t43 = t42 + 3U;
  /*@ assert address_normalization: t43 == s + (3); */
  /* Wasm instruction 66: i32.load8_u */
  /*@ assert physical_bounds: t43 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t43 && t43 + 1 <= s + n; */
  unsigned int t44 = ((unsigned int)m[t43 + 0U] << 0);
  /* Wasm instruction 67: i32.store8 */
  /*@ assert physical_bounds: t41 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t41 && t41 + 1 <= d + n; */
  m[t41 + 0U] = (unsigned char)(t44 >> 0);
  /* Wasm instruction 68: local.get */
  /* Wasm instruction 69: i32.const */
  /* Wasm instruction 70: i32.add */
  unsigned int t45 = t40 + 2U;
  /*@ assert address_normalization: t45 == d + (2); */
  /* Wasm instruction 71: local.get */
  /* Wasm instruction 72: i32.const */
  /* Wasm instruction 73: i32.add */
  unsigned int t46 = t42 + 2U;
  /*@ assert address_normalization: t46 == s + (2); */
  /* Wasm instruction 74: i32.load8_u */
  /*@ assert physical_bounds: t46 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t46 && t46 + 1 <= s + n; */
  unsigned int t47 = ((unsigned int)m[t46 + 0U] << 0);
  /* Wasm instruction 75: i32.store8 */
  /*@ assert physical_bounds: t45 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t45 && t45 + 1 <= d + n; */
  m[t45 + 0U] = (unsigned char)(t47 >> 0);
  /* Wasm instruction 76: local.get */
  /* Wasm instruction 77: i32.const */
  /* Wasm instruction 78: i32.add */
  unsigned int t48 = t40 + 1U;
  /*@ assert address_normalization: t48 == d + (1); */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: i32.const */
  /* Wasm instruction 81: i32.add */
  unsigned int t49 = t42 + 1U;
  /*@ assert address_normalization: t49 == s + (1); */
  /* Wasm instruction 82: i32.load8_u */
  /*@ assert physical_bounds: t49 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t49 && t49 + 1 <= s + n; */
  unsigned int t50 = ((unsigned int)m[t49 + 0U] << 0);
  /* Wasm instruction 83: i32.store8 */
  /*@ assert physical_bounds: t48 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t48 && t48 + 1 <= d + n; */
  m[t48 + 0U] = (unsigned char)(t50 >> 0);
  /* Wasm instruction 84: local.get */
  /* Wasm instruction 85: local.get */
  /* Wasm instruction 86: i32.load8_u */
  /*@ assert physical_bounds: t42 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t42 && t42 + 1 <= s + n; */
  unsigned int t51 = ((unsigned int)m[t42 + 0U] << 0);
  /* Wasm instruction 87: i32.store8 */
  /*@ assert physical_bounds: t40 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t40 && t40 + 1 <= d + n; */
  m[t40 + 0U] = (unsigned char)(t51 >> 0);
  /* Wasm instruction 88: local.get */
  /* Wasm instruction 89: i32.const */
  /* Wasm instruction 90: i32.add */
  unsigned int t52 = t39 + 4294967292U;
  /* Wasm instruction 91: local.tee */
  /* Wasm instruction 92: br_if */
  /*@ assert branch_5: t52 == 0; */
  /* Wasm instruction 93: br */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  /*@ assert copied_byte_3: m[d+3] == \at(m[s+3],Pre); */
  /*@ assert copied_byte_4: m[d+4] == \at(m[s+4],Pre); */
  /*@ assert copied_byte_5: m[d+5] == \at(m[s+5],Pre); */
  /*@ assert copied_byte_6: m[d+6] == \at(m[s+6],Pre); */
  /*@ assert copied_byte_7: m[d+7] == \at(m[s+7],Pre); */
  /*@ assert copied_byte_8: m[d+8] == \at(m[s+8],Pre); */
  /*@ assert copied_byte_9: m[d+9] == \at(m[s+9],Pre); */
  /*@ assert copied_byte_10: m[d+10] == \at(m[s+10],Pre); */
  /*@ assert copied_byte_11: m[d+11] == \at(m[s+11],Pre); */
  /*@ assert copied_byte_12: m[d+12] == \at(m[s+12],Pre); */
  return d;
}
/*@
  requires specialization: n == 13 && d < s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
  ensures byte_3: m[d+3] == \old(m[s+3]);
  ensures byte_4: m[d+4] == \old(m[s+4]);
  ensures byte_5: m[d+5] == \old(m[s+5]);
  ensures byte_6: m[d+6] == \old(m[s+6]);
  ensures byte_7: m[d+7] == \old(m[s+7]);
  ensures byte_8: m[d+8] == \old(m[s+8]);
  ensures byte_9: m[d+9] == \old(m[s+9]);
  ensures byte_10: m[d+10] == \old(m[s+10]);
  ensures byte_11: m[d+11] == \old(m[s+11]);
  ensures byte_12: m[d+12] == \old(m[s+12]);
*/
unsigned int move4_13_1(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 13; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 != 0; */
  /* Wasm instruction 94: local.get */
  /* Wasm instruction 95: i32.eqz */
  unsigned int t1 = !13U;
  /* Wasm instruction 96: br_if */
  /*@ assert branch_6: t1 == 0; */
  /* Wasm instruction 97: local.get */
  /* Wasm instruction 98: i32.const */
  /* Wasm instruction 99: i32.and */
  unsigned int t2 = 13U & 3U;
  /* Wasm instruction 100: local.set */
  /* Wasm instruction 101: i32.const */
  /* Wasm instruction 102: local.set */
  /* Wasm instruction 103: local.get */
  /* Wasm instruction 104: i32.const */
  /* Wasm instruction 105: i32.lt_u */
  unsigned int t3 = 13U < 4U;
  /* Wasm instruction 106: br_if */
  /*@ assert branch_7: t3 == 0; */
  /* Wasm instruction 107: local.get */
  /* Wasm instruction 108: i32.const */
  /* Wasm instruction 109: i32.and */
  unsigned int t4 = 13U & 4294967292U;
  /* Wasm instruction 110: local.set */
  /* Wasm instruction 111: i32.const */
  /* Wasm instruction 112: local.set */
  /* Wasm instruction 113: local.get */
  /* Wasm instruction 114: local.get */
  /* Wasm instruction 115: i32.add */
  unsigned int t5 = d + 0U;
  /*@ assert address_normalization: t5 == d + (0); */
  /* Wasm instruction 116: local.tee */
  /* Wasm instruction 117: local.get */
  /* Wasm instruction 118: local.get */
  /* Wasm instruction 119: i32.add */
  unsigned int t6 = s + 0U;
  /*@ assert address_normalization: t6 == s + (0); */
  /* Wasm instruction 120: local.tee */
  /* Wasm instruction 121: i32.load8_u */
  /*@ assert physical_bounds: t6 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t6 && t6 + 1 <= s + n; */
  unsigned int t7 = ((unsigned int)m[t6 + 0U] << 0);
  /* Wasm instruction 122: i32.store8 */
  /*@ assert physical_bounds: t5 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t5 && t5 + 1 <= d + n; */
  m[t5 + 0U] = (unsigned char)(t7 >> 0);
  /* Wasm instruction 123: local.get */
  /* Wasm instruction 124: i32.const */
  /* Wasm instruction 125: i32.add */
  unsigned int t8 = t5 + 1U;
  /*@ assert address_normalization: t8 == d + (1); */
  /* Wasm instruction 126: local.get */
  /* Wasm instruction 127: i32.const */
  /* Wasm instruction 128: i32.add */
  unsigned int t9 = t6 + 1U;
  /*@ assert address_normalization: t9 == s + (1); */
  /* Wasm instruction 129: i32.load8_u */
  /*@ assert physical_bounds: t9 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t9 && t9 + 1 <= s + n; */
  unsigned int t10 = ((unsigned int)m[t9 + 0U] << 0);
  /* Wasm instruction 130: i32.store8 */
  /*@ assert physical_bounds: t8 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t8 && t8 + 1 <= d + n; */
  m[t8 + 0U] = (unsigned char)(t10 >> 0);
  /* Wasm instruction 131: local.get */
  /* Wasm instruction 132: i32.const */
  /* Wasm instruction 133: i32.add */
  unsigned int t11 = t5 + 2U;
  /*@ assert address_normalization: t11 == d + (2); */
  /* Wasm instruction 134: local.get */
  /* Wasm instruction 135: i32.const */
  /* Wasm instruction 136: i32.add */
  unsigned int t12 = t6 + 2U;
  /*@ assert address_normalization: t12 == s + (2); */
  /* Wasm instruction 137: i32.load8_u */
  /*@ assert physical_bounds: t12 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t12 && t12 + 1 <= s + n; */
  unsigned int t13 = ((unsigned int)m[t12 + 0U] << 0);
  /* Wasm instruction 138: i32.store8 */
  /*@ assert physical_bounds: t11 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t11 && t11 + 1 <= d + n; */
  m[t11 + 0U] = (unsigned char)(t13 >> 0);
  /* Wasm instruction 139: local.get */
  /* Wasm instruction 140: i32.const */
  /* Wasm instruction 141: i32.add */
  unsigned int t14 = t5 + 3U;
  /*@ assert address_normalization: t14 == d + (3); */
  /* Wasm instruction 142: local.get */
  /* Wasm instruction 143: i32.const */
  /* Wasm instruction 144: i32.add */
  unsigned int t15 = t6 + 3U;
  /*@ assert address_normalization: t15 == s + (3); */
  /* Wasm instruction 145: i32.load8_u */
  /*@ assert physical_bounds: t15 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t15 && t15 + 1 <= s + n; */
  unsigned int t16 = ((unsigned int)m[t15 + 0U] << 0);
  /* Wasm instruction 146: i32.store8 */
  /*@ assert physical_bounds: t14 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t14 && t14 + 1 <= d + n; */
  m[t14 + 0U] = (unsigned char)(t16 >> 0);
  /* Wasm instruction 147: local.get */
  /* Wasm instruction 148: local.get */
  /* Wasm instruction 149: i32.const */
  /* Wasm instruction 150: i32.add */
  unsigned int t17 = 0U + 4U;
  /* Wasm instruction 151: local.tee */
  /* Wasm instruction 152: i32.ne */
  unsigned int t18 = t4 != t17;
  /* Wasm instruction 153: br_if */
  /*@ assert branch_8: t18 != 0; */
  /* Wasm instruction 113: local.get */
  /* Wasm instruction 114: local.get */
  /* Wasm instruction 115: i32.add */
  unsigned int t19 = d + t17;
  /*@ assert address_normalization: t19 == d + (4); */
  /* Wasm instruction 116: local.tee */
  /* Wasm instruction 117: local.get */
  /* Wasm instruction 118: local.get */
  /* Wasm instruction 119: i32.add */
  unsigned int t20 = s + t17;
  /*@ assert address_normalization: t20 == s + (4); */
  /* Wasm instruction 120: local.tee */
  /* Wasm instruction 121: i32.load8_u */
  /*@ assert physical_bounds: t20 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t20 && t20 + 1 <= s + n; */
  unsigned int t21 = ((unsigned int)m[t20 + 0U] << 0);
  /* Wasm instruction 122: i32.store8 */
  /*@ assert physical_bounds: t19 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t19 && t19 + 1 <= d + n; */
  m[t19 + 0U] = (unsigned char)(t21 >> 0);
  /* Wasm instruction 123: local.get */
  /* Wasm instruction 124: i32.const */
  /* Wasm instruction 125: i32.add */
  unsigned int t22 = t19 + 1U;
  /*@ assert address_normalization: t22 == d + (5); */
  /* Wasm instruction 126: local.get */
  /* Wasm instruction 127: i32.const */
  /* Wasm instruction 128: i32.add */
  unsigned int t23 = t20 + 1U;
  /*@ assert address_normalization: t23 == s + (5); */
  /* Wasm instruction 129: i32.load8_u */
  /*@ assert physical_bounds: t23 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t23 && t23 + 1 <= s + n; */
  unsigned int t24 = ((unsigned int)m[t23 + 0U] << 0);
  /* Wasm instruction 130: i32.store8 */
  /*@ assert physical_bounds: t22 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t22 && t22 + 1 <= d + n; */
  m[t22 + 0U] = (unsigned char)(t24 >> 0);
  /* Wasm instruction 131: local.get */
  /* Wasm instruction 132: i32.const */
  /* Wasm instruction 133: i32.add */
  unsigned int t25 = t19 + 2U;
  /*@ assert address_normalization: t25 == d + (6); */
  /* Wasm instruction 134: local.get */
  /* Wasm instruction 135: i32.const */
  /* Wasm instruction 136: i32.add */
  unsigned int t26 = t20 + 2U;
  /*@ assert address_normalization: t26 == s + (6); */
  /* Wasm instruction 137: i32.load8_u */
  /*@ assert physical_bounds: t26 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t26 && t26 + 1 <= s + n; */
  unsigned int t27 = ((unsigned int)m[t26 + 0U] << 0);
  /* Wasm instruction 138: i32.store8 */
  /*@ assert physical_bounds: t25 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t25 && t25 + 1 <= d + n; */
  m[t25 + 0U] = (unsigned char)(t27 >> 0);
  /* Wasm instruction 139: local.get */
  /* Wasm instruction 140: i32.const */
  /* Wasm instruction 141: i32.add */
  unsigned int t28 = t19 + 3U;
  /*@ assert address_normalization: t28 == d + (7); */
  /* Wasm instruction 142: local.get */
  /* Wasm instruction 143: i32.const */
  /* Wasm instruction 144: i32.add */
  unsigned int t29 = t20 + 3U;
  /*@ assert address_normalization: t29 == s + (7); */
  /* Wasm instruction 145: i32.load8_u */
  /*@ assert physical_bounds: t29 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t29 && t29 + 1 <= s + n; */
  unsigned int t30 = ((unsigned int)m[t29 + 0U] << 0);
  /* Wasm instruction 146: i32.store8 */
  /*@ assert physical_bounds: t28 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t28 && t28 + 1 <= d + n; */
  m[t28 + 0U] = (unsigned char)(t30 >> 0);
  /* Wasm instruction 147: local.get */
  /* Wasm instruction 148: local.get */
  /* Wasm instruction 149: i32.const */
  /* Wasm instruction 150: i32.add */
  unsigned int t31 = t17 + 4U;
  /* Wasm instruction 151: local.tee */
  /* Wasm instruction 152: i32.ne */
  unsigned int t32 = t4 != t31;
  /* Wasm instruction 153: br_if */
  /*@ assert branch_8: t32 != 0; */
  /* Wasm instruction 113: local.get */
  /* Wasm instruction 114: local.get */
  /* Wasm instruction 115: i32.add */
  unsigned int t33 = d + t31;
  /*@ assert address_normalization: t33 == d + (8); */
  /* Wasm instruction 116: local.tee */
  /* Wasm instruction 117: local.get */
  /* Wasm instruction 118: local.get */
  /* Wasm instruction 119: i32.add */
  unsigned int t34 = s + t31;
  /*@ assert address_normalization: t34 == s + (8); */
  /* Wasm instruction 120: local.tee */
  /* Wasm instruction 121: i32.load8_u */
  /*@ assert physical_bounds: t34 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t34 && t34 + 1 <= s + n; */
  unsigned int t35 = ((unsigned int)m[t34 + 0U] << 0);
  /* Wasm instruction 122: i32.store8 */
  /*@ assert physical_bounds: t33 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t33 && t33 + 1 <= d + n; */
  m[t33 + 0U] = (unsigned char)(t35 >> 0);
  /* Wasm instruction 123: local.get */
  /* Wasm instruction 124: i32.const */
  /* Wasm instruction 125: i32.add */
  unsigned int t36 = t33 + 1U;
  /*@ assert address_normalization: t36 == d + (9); */
  /* Wasm instruction 126: local.get */
  /* Wasm instruction 127: i32.const */
  /* Wasm instruction 128: i32.add */
  unsigned int t37 = t34 + 1U;
  /*@ assert address_normalization: t37 == s + (9); */
  /* Wasm instruction 129: i32.load8_u */
  /*@ assert physical_bounds: t37 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t37 && t37 + 1 <= s + n; */
  unsigned int t38 = ((unsigned int)m[t37 + 0U] << 0);
  /* Wasm instruction 130: i32.store8 */
  /*@ assert physical_bounds: t36 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t36 && t36 + 1 <= d + n; */
  m[t36 + 0U] = (unsigned char)(t38 >> 0);
  /* Wasm instruction 131: local.get */
  /* Wasm instruction 132: i32.const */
  /* Wasm instruction 133: i32.add */
  unsigned int t39 = t33 + 2U;
  /*@ assert address_normalization: t39 == d + (10); */
  /* Wasm instruction 134: local.get */
  /* Wasm instruction 135: i32.const */
  /* Wasm instruction 136: i32.add */
  unsigned int t40 = t34 + 2U;
  /*@ assert address_normalization: t40 == s + (10); */
  /* Wasm instruction 137: i32.load8_u */
  /*@ assert physical_bounds: t40 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t40 && t40 + 1 <= s + n; */
  unsigned int t41 = ((unsigned int)m[t40 + 0U] << 0);
  /* Wasm instruction 138: i32.store8 */
  /*@ assert physical_bounds: t39 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t39 && t39 + 1 <= d + n; */
  m[t39 + 0U] = (unsigned char)(t41 >> 0);
  /* Wasm instruction 139: local.get */
  /* Wasm instruction 140: i32.const */
  /* Wasm instruction 141: i32.add */
  unsigned int t42 = t33 + 3U;
  /*@ assert address_normalization: t42 == d + (11); */
  /* Wasm instruction 142: local.get */
  /* Wasm instruction 143: i32.const */
  /* Wasm instruction 144: i32.add */
  unsigned int t43 = t34 + 3U;
  /*@ assert address_normalization: t43 == s + (11); */
  /* Wasm instruction 145: i32.load8_u */
  /*@ assert physical_bounds: t43 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t43 && t43 + 1 <= s + n; */
  unsigned int t44 = ((unsigned int)m[t43 + 0U] << 0);
  /* Wasm instruction 146: i32.store8 */
  /*@ assert physical_bounds: t42 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t42 && t42 + 1 <= d + n; */
  m[t42 + 0U] = (unsigned char)(t44 >> 0);
  /* Wasm instruction 147: local.get */
  /* Wasm instruction 148: local.get */
  /* Wasm instruction 149: i32.const */
  /* Wasm instruction 150: i32.add */
  unsigned int t45 = t31 + 4U;
  /* Wasm instruction 151: local.tee */
  /* Wasm instruction 152: i32.ne */
  unsigned int t46 = t4 != t45;
  /* Wasm instruction 153: br_if */
  /*@ assert branch_8: t46 == 0; */
  /* Wasm instruction 154: local.get */
  /* Wasm instruction 155: i32.eqz */
  unsigned int t47 = !t2;
  /* Wasm instruction 156: br_if */
  /*@ assert branch_9: t47 == 0; */
  /* Wasm instruction 157: local.get */
  /* Wasm instruction 158: local.get */
  /* Wasm instruction 159: i32.add */
  unsigned int t48 = s + t45;
  /*@ assert address_normalization: t48 == s + (12); */
  /* Wasm instruction 160: local.set */
  /* Wasm instruction 161: local.get */
  /* Wasm instruction 162: local.get */
  /* Wasm instruction 163: i32.add */
  unsigned int t49 = d + t45;
  /*@ assert address_normalization: t49 == d + (12); */
  /* Wasm instruction 164: local.set */
  /* Wasm instruction 165: local.get */
  /* Wasm instruction 166: local.get */
  /* Wasm instruction 167: i32.load8_u */
  /*@ assert physical_bounds: t48 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t48 && t48 + 1 <= s + n; */
  unsigned int t50 = ((unsigned int)m[t48 + 0U] << 0);
  /* Wasm instruction 168: i32.store8 */
  /*@ assert physical_bounds: t49 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t49 && t49 + 1 <= d + n; */
  m[t49 + 0U] = (unsigned char)(t50 >> 0);
  /* Wasm instruction 169: local.get */
  /* Wasm instruction 170: i32.const */
  /* Wasm instruction 171: i32.add */
  unsigned int t51 = t48 + 1U;
  /*@ assert address_normalization: t51 == s + (13); */
  /* Wasm instruction 172: local.set */
  /* Wasm instruction 173: local.get */
  /* Wasm instruction 174: i32.const */
  /* Wasm instruction 175: i32.add */
  unsigned int t52 = t49 + 1U;
  /*@ assert address_normalization: t52 == d + (13); */
  /* Wasm instruction 176: local.set */
  /* Wasm instruction 177: local.get */
  /* Wasm instruction 178: i32.const */
  /* Wasm instruction 179: i32.add */
  unsigned int t53 = t2 + 4294967295U;
  /* Wasm instruction 180: local.tee */
  /* Wasm instruction 181: br_if */
  /*@ assert branch_10: t53 == 0; */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  /*@ assert copied_byte_3: m[d+3] == \at(m[s+3],Pre); */
  /*@ assert copied_byte_4: m[d+4] == \at(m[s+4],Pre); */
  /*@ assert copied_byte_5: m[d+5] == \at(m[s+5],Pre); */
  /*@ assert copied_byte_6: m[d+6] == \at(m[s+6],Pre); */
  /*@ assert copied_byte_7: m[d+7] == \at(m[s+7],Pre); */
  /*@ assert copied_byte_8: m[d+8] == \at(m[s+8],Pre); */
  /*@ assert copied_byte_9: m[d+9] == \at(m[s+9],Pre); */
  /*@ assert copied_byte_10: m[d+10] == \at(m[s+10],Pre); */
  /*@ assert copied_byte_11: m[d+11] == \at(m[s+11],Pre); */
  /*@ assert copied_byte_12: m[d+12] == \at(m[s+12],Pre); */
  return d;
}
/*@
  requires specialization: n == 14 && d >= s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
  ensures byte_3: m[d+3] == \old(m[s+3]);
  ensures byte_4: m[d+4] == \old(m[s+4]);
  ensures byte_5: m[d+5] == \old(m[s+5]);
  ensures byte_6: m[d+6] == \old(m[s+6]);
  ensures byte_7: m[d+7] == \old(m[s+7]);
  ensures byte_8: m[d+8] == \old(m[s+8]);
  ensures byte_9: m[d+9] == \old(m[s+9]);
  ensures byte_10: m[d+10] == \old(m[s+10]);
  ensures byte_11: m[d+11] == \old(m[s+11]);
  ensures byte_12: m[d+12] == \old(m[s+12]);
  ensures byte_13: m[d+13] == \old(m[s+13]);
*/
unsigned int move4_14_0(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 14; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 == 0; */
  /* Wasm instruction 4: local.get */
  /* Wasm instruction 5: i32.eqz */
  unsigned int t1 = !14U;
  /* Wasm instruction 6: br_if */
  /*@ assert branch_1: t1 == 0; */
  /* Wasm instruction 7: local.get */
  /* Wasm instruction 8: local.set */
  /* Wasm instruction 9: local.get */
  /* Wasm instruction 10: i32.const */
  /* Wasm instruction 11: i32.and */
  unsigned int t2 = 14U & 3U;
  /* Wasm instruction 12: local.tee */
  /* Wasm instruction 13: i32.eqz */
  unsigned int t3 = !t2;
  /* Wasm instruction 14: br_if */
  /*@ assert branch_2: t3 == 0; */
  /* Wasm instruction 15: local.get */
  /* Wasm instruction 16: i32.const */
  /* Wasm instruction 17: i32.add */
  unsigned int t4 = s + 4294967295U;
  /*@ assert address_normalization: t4 == s + (-1); */
  /* Wasm instruction 18: local.set */
  /* Wasm instruction 19: local.get */
  /* Wasm instruction 20: i32.const */
  /* Wasm instruction 21: i32.add */
  unsigned int t5 = d + 4294967295U;
  /*@ assert address_normalization: t5 == d + (-1); */
  /* Wasm instruction 22: local.set */
  /* Wasm instruction 23: local.get */
  /* Wasm instruction 24: local.set */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: local.get */
  /* Wasm instruction 27: i32.add */
  unsigned int t6 = t5 + 14U;
  /*@ assert address_normalization: t6 == d + (13); */
  /* Wasm instruction 28: local.get */
  /* Wasm instruction 29: local.get */
  /* Wasm instruction 30: i32.add */
  unsigned int t7 = t4 + 14U;
  /*@ assert address_normalization: t7 == s + (13); */
  /* Wasm instruction 31: i32.load8_u */
  /*@ assert physical_bounds: t7 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t7 && t7 + 1 <= s + n; */
  unsigned int t8 = ((unsigned int)m[t7 + 0U] << 0);
  /* Wasm instruction 32: i32.store8 */
  /*@ assert physical_bounds: t6 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t6 && t6 + 1 <= d + n; */
  m[t6 + 0U] = (unsigned char)(t8 >> 0);
  /* Wasm instruction 33: local.get */
  /* Wasm instruction 34: i32.const */
  /* Wasm instruction 35: i32.add */
  unsigned int t9 = 14U + 4294967295U;
  /* Wasm instruction 36: local.set */
  /* Wasm instruction 37: local.get */
  /* Wasm instruction 38: i32.const */
  /* Wasm instruction 39: i32.add */
  unsigned int t10 = t2 + 4294967295U;
  /* Wasm instruction 40: local.tee */
  /* Wasm instruction 41: br_if */
  /*@ assert branch_3: t10 != 0; */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: local.get */
  /* Wasm instruction 27: i32.add */
  unsigned int t11 = t5 + t9;
  /*@ assert address_normalization: t11 == d + (12); */
  /* Wasm instruction 28: local.get */
  /* Wasm instruction 29: local.get */
  /* Wasm instruction 30: i32.add */
  unsigned int t12 = t4 + t9;
  /*@ assert address_normalization: t12 == s + (12); */
  /* Wasm instruction 31: i32.load8_u */
  /*@ assert physical_bounds: t12 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t12 && t12 + 1 <= s + n; */
  unsigned int t13 = ((unsigned int)m[t12 + 0U] << 0);
  /* Wasm instruction 32: i32.store8 */
  /*@ assert physical_bounds: t11 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t11 && t11 + 1 <= d + n; */
  m[t11 + 0U] = (unsigned char)(t13 >> 0);
  /* Wasm instruction 33: local.get */
  /* Wasm instruction 34: i32.const */
  /* Wasm instruction 35: i32.add */
  unsigned int t14 = t9 + 4294967295U;
  /* Wasm instruction 36: local.set */
  /* Wasm instruction 37: local.get */
  /* Wasm instruction 38: i32.const */
  /* Wasm instruction 39: i32.add */
  unsigned int t15 = t10 + 4294967295U;
  /* Wasm instruction 40: local.tee */
  /* Wasm instruction 41: br_if */
  /*@ assert branch_3: t15 == 0; */
  /* Wasm instruction 42: local.get */
  /* Wasm instruction 43: i32.const */
  /* Wasm instruction 44: i32.lt_u */
  unsigned int t16 = 14U < 4U;
  /* Wasm instruction 45: br_if */
  /*@ assert branch_4: t16 == 0; */
  /* Wasm instruction 46: local.get */
  /* Wasm instruction 47: i32.const */
  /* Wasm instruction 48: i32.add */
  unsigned int t17 = s + 4294967292U;
  /*@ assert address_normalization: t17 == s + (-4); */
  /* Wasm instruction 49: local.set */
  /* Wasm instruction 50: local.get */
  /* Wasm instruction 51: i32.const */
  /* Wasm instruction 52: i32.add */
  unsigned int t18 = d + 4294967292U;
  /*@ assert address_normalization: t18 == d + (-4); */
  /* Wasm instruction 53: local.set */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: local.get */
  /* Wasm instruction 56: i32.add */
  unsigned int t19 = t18 + t14;
  /*@ assert address_normalization: t19 == d + (8); */
  /* Wasm instruction 57: local.tee */
  /* Wasm instruction 58: i32.const */
  /* Wasm instruction 59: i32.add */
  unsigned int t20 = t19 + 3U;
  /*@ assert address_normalization: t20 == d + (11); */
  /* Wasm instruction 60: local.get */
  /* Wasm instruction 61: local.get */
  /* Wasm instruction 62: i32.add */
  unsigned int t21 = t17 + t14;
  /*@ assert address_normalization: t21 == s + (8); */
  /* Wasm instruction 63: local.tee */
  /* Wasm instruction 64: i32.const */
  /* Wasm instruction 65: i32.add */
  unsigned int t22 = t21 + 3U;
  /*@ assert address_normalization: t22 == s + (11); */
  /* Wasm instruction 66: i32.load8_u */
  /*@ assert physical_bounds: t22 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t22 && t22 + 1 <= s + n; */
  unsigned int t23 = ((unsigned int)m[t22 + 0U] << 0);
  /* Wasm instruction 67: i32.store8 */
  /*@ assert physical_bounds: t20 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t20 && t20 + 1 <= d + n; */
  m[t20 + 0U] = (unsigned char)(t23 >> 0);
  /* Wasm instruction 68: local.get */
  /* Wasm instruction 69: i32.const */
  /* Wasm instruction 70: i32.add */
  unsigned int t24 = t19 + 2U;
  /*@ assert address_normalization: t24 == d + (10); */
  /* Wasm instruction 71: local.get */
  /* Wasm instruction 72: i32.const */
  /* Wasm instruction 73: i32.add */
  unsigned int t25 = t21 + 2U;
  /*@ assert address_normalization: t25 == s + (10); */
  /* Wasm instruction 74: i32.load8_u */
  /*@ assert physical_bounds: t25 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t25 && t25 + 1 <= s + n; */
  unsigned int t26 = ((unsigned int)m[t25 + 0U] << 0);
  /* Wasm instruction 75: i32.store8 */
  /*@ assert physical_bounds: t24 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t24 && t24 + 1 <= d + n; */
  m[t24 + 0U] = (unsigned char)(t26 >> 0);
  /* Wasm instruction 76: local.get */
  /* Wasm instruction 77: i32.const */
  /* Wasm instruction 78: i32.add */
  unsigned int t27 = t19 + 1U;
  /*@ assert address_normalization: t27 == d + (9); */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: i32.const */
  /* Wasm instruction 81: i32.add */
  unsigned int t28 = t21 + 1U;
  /*@ assert address_normalization: t28 == s + (9); */
  /* Wasm instruction 82: i32.load8_u */
  /*@ assert physical_bounds: t28 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t28 && t28 + 1 <= s + n; */
  unsigned int t29 = ((unsigned int)m[t28 + 0U] << 0);
  /* Wasm instruction 83: i32.store8 */
  /*@ assert physical_bounds: t27 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t27 && t27 + 1 <= d + n; */
  m[t27 + 0U] = (unsigned char)(t29 >> 0);
  /* Wasm instruction 84: local.get */
  /* Wasm instruction 85: local.get */
  /* Wasm instruction 86: i32.load8_u */
  /*@ assert physical_bounds: t21 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t21 && t21 + 1 <= s + n; */
  unsigned int t30 = ((unsigned int)m[t21 + 0U] << 0);
  /* Wasm instruction 87: i32.store8 */
  /*@ assert physical_bounds: t19 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t19 && t19 + 1 <= d + n; */
  m[t19 + 0U] = (unsigned char)(t30 >> 0);
  /* Wasm instruction 88: local.get */
  /* Wasm instruction 89: i32.const */
  /* Wasm instruction 90: i32.add */
  unsigned int t31 = t14 + 4294967292U;
  /* Wasm instruction 91: local.tee */
  /* Wasm instruction 92: br_if */
  /*@ assert branch_5: t31 != 0; */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: local.get */
  /* Wasm instruction 56: i32.add */
  unsigned int t32 = t18 + t31;
  /*@ assert address_normalization: t32 == d + (4); */
  /* Wasm instruction 57: local.tee */
  /* Wasm instruction 58: i32.const */
  /* Wasm instruction 59: i32.add */
  unsigned int t33 = t32 + 3U;
  /*@ assert address_normalization: t33 == d + (7); */
  /* Wasm instruction 60: local.get */
  /* Wasm instruction 61: local.get */
  /* Wasm instruction 62: i32.add */
  unsigned int t34 = t17 + t31;
  /*@ assert address_normalization: t34 == s + (4); */
  /* Wasm instruction 63: local.tee */
  /* Wasm instruction 64: i32.const */
  /* Wasm instruction 65: i32.add */
  unsigned int t35 = t34 + 3U;
  /*@ assert address_normalization: t35 == s + (7); */
  /* Wasm instruction 66: i32.load8_u */
  /*@ assert physical_bounds: t35 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t35 && t35 + 1 <= s + n; */
  unsigned int t36 = ((unsigned int)m[t35 + 0U] << 0);
  /* Wasm instruction 67: i32.store8 */
  /*@ assert physical_bounds: t33 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t33 && t33 + 1 <= d + n; */
  m[t33 + 0U] = (unsigned char)(t36 >> 0);
  /* Wasm instruction 68: local.get */
  /* Wasm instruction 69: i32.const */
  /* Wasm instruction 70: i32.add */
  unsigned int t37 = t32 + 2U;
  /*@ assert address_normalization: t37 == d + (6); */
  /* Wasm instruction 71: local.get */
  /* Wasm instruction 72: i32.const */
  /* Wasm instruction 73: i32.add */
  unsigned int t38 = t34 + 2U;
  /*@ assert address_normalization: t38 == s + (6); */
  /* Wasm instruction 74: i32.load8_u */
  /*@ assert physical_bounds: t38 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t38 && t38 + 1 <= s + n; */
  unsigned int t39 = ((unsigned int)m[t38 + 0U] << 0);
  /* Wasm instruction 75: i32.store8 */
  /*@ assert physical_bounds: t37 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t37 && t37 + 1 <= d + n; */
  m[t37 + 0U] = (unsigned char)(t39 >> 0);
  /* Wasm instruction 76: local.get */
  /* Wasm instruction 77: i32.const */
  /* Wasm instruction 78: i32.add */
  unsigned int t40 = t32 + 1U;
  /*@ assert address_normalization: t40 == d + (5); */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: i32.const */
  /* Wasm instruction 81: i32.add */
  unsigned int t41 = t34 + 1U;
  /*@ assert address_normalization: t41 == s + (5); */
  /* Wasm instruction 82: i32.load8_u */
  /*@ assert physical_bounds: t41 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t41 && t41 + 1 <= s + n; */
  unsigned int t42 = ((unsigned int)m[t41 + 0U] << 0);
  /* Wasm instruction 83: i32.store8 */
  /*@ assert physical_bounds: t40 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t40 && t40 + 1 <= d + n; */
  m[t40 + 0U] = (unsigned char)(t42 >> 0);
  /* Wasm instruction 84: local.get */
  /* Wasm instruction 85: local.get */
  /* Wasm instruction 86: i32.load8_u */
  /*@ assert physical_bounds: t34 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t34 && t34 + 1 <= s + n; */
  unsigned int t43 = ((unsigned int)m[t34 + 0U] << 0);
  /* Wasm instruction 87: i32.store8 */
  /*@ assert physical_bounds: t32 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t32 && t32 + 1 <= d + n; */
  m[t32 + 0U] = (unsigned char)(t43 >> 0);
  /* Wasm instruction 88: local.get */
  /* Wasm instruction 89: i32.const */
  /* Wasm instruction 90: i32.add */
  unsigned int t44 = t31 + 4294967292U;
  /* Wasm instruction 91: local.tee */
  /* Wasm instruction 92: br_if */
  /*@ assert branch_5: t44 != 0; */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: local.get */
  /* Wasm instruction 56: i32.add */
  unsigned int t45 = t18 + t44;
  /*@ assert address_normalization: t45 == d + (0); */
  /* Wasm instruction 57: local.tee */
  /* Wasm instruction 58: i32.const */
  /* Wasm instruction 59: i32.add */
  unsigned int t46 = t45 + 3U;
  /*@ assert address_normalization: t46 == d + (3); */
  /* Wasm instruction 60: local.get */
  /* Wasm instruction 61: local.get */
  /* Wasm instruction 62: i32.add */
  unsigned int t47 = t17 + t44;
  /*@ assert address_normalization: t47 == s + (0); */
  /* Wasm instruction 63: local.tee */
  /* Wasm instruction 64: i32.const */
  /* Wasm instruction 65: i32.add */
  unsigned int t48 = t47 + 3U;
  /*@ assert address_normalization: t48 == s + (3); */
  /* Wasm instruction 66: i32.load8_u */
  /*@ assert physical_bounds: t48 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t48 && t48 + 1 <= s + n; */
  unsigned int t49 = ((unsigned int)m[t48 + 0U] << 0);
  /* Wasm instruction 67: i32.store8 */
  /*@ assert physical_bounds: t46 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t46 && t46 + 1 <= d + n; */
  m[t46 + 0U] = (unsigned char)(t49 >> 0);
  /* Wasm instruction 68: local.get */
  /* Wasm instruction 69: i32.const */
  /* Wasm instruction 70: i32.add */
  unsigned int t50 = t45 + 2U;
  /*@ assert address_normalization: t50 == d + (2); */
  /* Wasm instruction 71: local.get */
  /* Wasm instruction 72: i32.const */
  /* Wasm instruction 73: i32.add */
  unsigned int t51 = t47 + 2U;
  /*@ assert address_normalization: t51 == s + (2); */
  /* Wasm instruction 74: i32.load8_u */
  /*@ assert physical_bounds: t51 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t51 && t51 + 1 <= s + n; */
  unsigned int t52 = ((unsigned int)m[t51 + 0U] << 0);
  /* Wasm instruction 75: i32.store8 */
  /*@ assert physical_bounds: t50 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t50 && t50 + 1 <= d + n; */
  m[t50 + 0U] = (unsigned char)(t52 >> 0);
  /* Wasm instruction 76: local.get */
  /* Wasm instruction 77: i32.const */
  /* Wasm instruction 78: i32.add */
  unsigned int t53 = t45 + 1U;
  /*@ assert address_normalization: t53 == d + (1); */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: i32.const */
  /* Wasm instruction 81: i32.add */
  unsigned int t54 = t47 + 1U;
  /*@ assert address_normalization: t54 == s + (1); */
  /* Wasm instruction 82: i32.load8_u */
  /*@ assert physical_bounds: t54 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t54 && t54 + 1 <= s + n; */
  unsigned int t55 = ((unsigned int)m[t54 + 0U] << 0);
  /* Wasm instruction 83: i32.store8 */
  /*@ assert physical_bounds: t53 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t53 && t53 + 1 <= d + n; */
  m[t53 + 0U] = (unsigned char)(t55 >> 0);
  /* Wasm instruction 84: local.get */
  /* Wasm instruction 85: local.get */
  /* Wasm instruction 86: i32.load8_u */
  /*@ assert physical_bounds: t47 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t47 && t47 + 1 <= s + n; */
  unsigned int t56 = ((unsigned int)m[t47 + 0U] << 0);
  /* Wasm instruction 87: i32.store8 */
  /*@ assert physical_bounds: t45 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t45 && t45 + 1 <= d + n; */
  m[t45 + 0U] = (unsigned char)(t56 >> 0);
  /* Wasm instruction 88: local.get */
  /* Wasm instruction 89: i32.const */
  /* Wasm instruction 90: i32.add */
  unsigned int t57 = t44 + 4294967292U;
  /* Wasm instruction 91: local.tee */
  /* Wasm instruction 92: br_if */
  /*@ assert branch_5: t57 == 0; */
  /* Wasm instruction 93: br */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  /*@ assert copied_byte_3: m[d+3] == \at(m[s+3],Pre); */
  /*@ assert copied_byte_4: m[d+4] == \at(m[s+4],Pre); */
  /*@ assert copied_byte_5: m[d+5] == \at(m[s+5],Pre); */
  /*@ assert copied_byte_6: m[d+6] == \at(m[s+6],Pre); */
  /*@ assert copied_byte_7: m[d+7] == \at(m[s+7],Pre); */
  /*@ assert copied_byte_8: m[d+8] == \at(m[s+8],Pre); */
  /*@ assert copied_byte_9: m[d+9] == \at(m[s+9],Pre); */
  /*@ assert copied_byte_10: m[d+10] == \at(m[s+10],Pre); */
  /*@ assert copied_byte_11: m[d+11] == \at(m[s+11],Pre); */
  /*@ assert copied_byte_12: m[d+12] == \at(m[s+12],Pre); */
  /*@ assert copied_byte_13: m[d+13] == \at(m[s+13],Pre); */
  return d;
}
/*@
  requires specialization: n == 14 && d < s;
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures byte_0: m[d+0] == \old(m[s+0]);
  ensures byte_1: m[d+1] == \old(m[s+1]);
  ensures byte_2: m[d+2] == \old(m[s+2]);
  ensures byte_3: m[d+3] == \old(m[s+3]);
  ensures byte_4: m[d+4] == \old(m[s+4]);
  ensures byte_5: m[d+5] == \old(m[s+5]);
  ensures byte_6: m[d+6] == \old(m[s+6]);
  ensures byte_7: m[d+7] == \old(m[s+7]);
  ensures byte_8: m[d+8] == \old(m[s+8]);
  ensures byte_9: m[d+9] == \old(m[s+9]);
  ensures byte_10: m[d+10] == \old(m[s+10]);
  ensures byte_11: m[d+11] == \old(m[s+11]);
  ensures byte_12: m[d+12] == \old(m[s+12]);
  ensures byte_13: m[d+13] == \old(m[s+13]);
*/
unsigned int move4_14_1(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  /*@ assert fixed_parameter: n == 14; */
  /* Wasm instruction 0: local.get */
  /* Wasm instruction 1: local.get */
  /* Wasm instruction 2: i32.lt_u */
  unsigned int t0 = d < s;
  /* Wasm instruction 3: br_if */
  /*@ assert branch_0: t0 != 0; */
  /* Wasm instruction 94: local.get */
  /* Wasm instruction 95: i32.eqz */
  unsigned int t1 = !14U;
  /* Wasm instruction 96: br_if */
  /*@ assert branch_6: t1 == 0; */
  /* Wasm instruction 97: local.get */
  /* Wasm instruction 98: i32.const */
  /* Wasm instruction 99: i32.and */
  unsigned int t2 = 14U & 3U;
  /* Wasm instruction 100: local.set */
  /* Wasm instruction 101: i32.const */
  /* Wasm instruction 102: local.set */
  /* Wasm instruction 103: local.get */
  /* Wasm instruction 104: i32.const */
  /* Wasm instruction 105: i32.lt_u */
  unsigned int t3 = 14U < 4U;
  /* Wasm instruction 106: br_if */
  /*@ assert branch_7: t3 == 0; */
  /* Wasm instruction 107: local.get */
  /* Wasm instruction 108: i32.const */
  /* Wasm instruction 109: i32.and */
  unsigned int t4 = 14U & 4294967292U;
  /* Wasm instruction 110: local.set */
  /* Wasm instruction 111: i32.const */
  /* Wasm instruction 112: local.set */
  /* Wasm instruction 113: local.get */
  /* Wasm instruction 114: local.get */
  /* Wasm instruction 115: i32.add */
  unsigned int t5 = d + 0U;
  /*@ assert address_normalization: t5 == d + (0); */
  /* Wasm instruction 116: local.tee */
  /* Wasm instruction 117: local.get */
  /* Wasm instruction 118: local.get */
  /* Wasm instruction 119: i32.add */
  unsigned int t6 = s + 0U;
  /*@ assert address_normalization: t6 == s + (0); */
  /* Wasm instruction 120: local.tee */
  /* Wasm instruction 121: i32.load8_u */
  /*@ assert physical_bounds: t6 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t6 && t6 + 1 <= s + n; */
  unsigned int t7 = ((unsigned int)m[t6 + 0U] << 0);
  /* Wasm instruction 122: i32.store8 */
  /*@ assert physical_bounds: t5 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t5 && t5 + 1 <= d + n; */
  m[t5 + 0U] = (unsigned char)(t7 >> 0);
  /* Wasm instruction 123: local.get */
  /* Wasm instruction 124: i32.const */
  /* Wasm instruction 125: i32.add */
  unsigned int t8 = t5 + 1U;
  /*@ assert address_normalization: t8 == d + (1); */
  /* Wasm instruction 126: local.get */
  /* Wasm instruction 127: i32.const */
  /* Wasm instruction 128: i32.add */
  unsigned int t9 = t6 + 1U;
  /*@ assert address_normalization: t9 == s + (1); */
  /* Wasm instruction 129: i32.load8_u */
  /*@ assert physical_bounds: t9 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t9 && t9 + 1 <= s + n; */
  unsigned int t10 = ((unsigned int)m[t9 + 0U] << 0);
  /* Wasm instruction 130: i32.store8 */
  /*@ assert physical_bounds: t8 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t8 && t8 + 1 <= d + n; */
  m[t8 + 0U] = (unsigned char)(t10 >> 0);
  /* Wasm instruction 131: local.get */
  /* Wasm instruction 132: i32.const */
  /* Wasm instruction 133: i32.add */
  unsigned int t11 = t5 + 2U;
  /*@ assert address_normalization: t11 == d + (2); */
  /* Wasm instruction 134: local.get */
  /* Wasm instruction 135: i32.const */
  /* Wasm instruction 136: i32.add */
  unsigned int t12 = t6 + 2U;
  /*@ assert address_normalization: t12 == s + (2); */
  /* Wasm instruction 137: i32.load8_u */
  /*@ assert physical_bounds: t12 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t12 && t12 + 1 <= s + n; */
  unsigned int t13 = ((unsigned int)m[t12 + 0U] << 0);
  /* Wasm instruction 138: i32.store8 */
  /*@ assert physical_bounds: t11 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t11 && t11 + 1 <= d + n; */
  m[t11 + 0U] = (unsigned char)(t13 >> 0);
  /* Wasm instruction 139: local.get */
  /* Wasm instruction 140: i32.const */
  /* Wasm instruction 141: i32.add */
  unsigned int t14 = t5 + 3U;
  /*@ assert address_normalization: t14 == d + (3); */
  /* Wasm instruction 142: local.get */
  /* Wasm instruction 143: i32.const */
  /* Wasm instruction 144: i32.add */
  unsigned int t15 = t6 + 3U;
  /*@ assert address_normalization: t15 == s + (3); */
  /* Wasm instruction 145: i32.load8_u */
  /*@ assert physical_bounds: t15 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t15 && t15 + 1 <= s + n; */
  unsigned int t16 = ((unsigned int)m[t15 + 0U] << 0);
  /* Wasm instruction 146: i32.store8 */
  /*@ assert physical_bounds: t14 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t14 && t14 + 1 <= d + n; */
  m[t14 + 0U] = (unsigned char)(t16 >> 0);
  /* Wasm instruction 147: local.get */
  /* Wasm instruction 148: local.get */
  /* Wasm instruction 149: i32.const */
  /* Wasm instruction 150: i32.add */
  unsigned int t17 = 0U + 4U;
  /* Wasm instruction 151: local.tee */
  /* Wasm instruction 152: i32.ne */
  unsigned int t18 = t4 != t17;
  /* Wasm instruction 153: br_if */
  /*@ assert branch_8: t18 != 0; */
  /* Wasm instruction 113: local.get */
  /* Wasm instruction 114: local.get */
  /* Wasm instruction 115: i32.add */
  unsigned int t19 = d + t17;
  /*@ assert address_normalization: t19 == d + (4); */
  /* Wasm instruction 116: local.tee */
  /* Wasm instruction 117: local.get */
  /* Wasm instruction 118: local.get */
  /* Wasm instruction 119: i32.add */
  unsigned int t20 = s + t17;
  /*@ assert address_normalization: t20 == s + (4); */
  /* Wasm instruction 120: local.tee */
  /* Wasm instruction 121: i32.load8_u */
  /*@ assert physical_bounds: t20 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t20 && t20 + 1 <= s + n; */
  unsigned int t21 = ((unsigned int)m[t20 + 0U] << 0);
  /* Wasm instruction 122: i32.store8 */
  /*@ assert physical_bounds: t19 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t19 && t19 + 1 <= d + n; */
  m[t19 + 0U] = (unsigned char)(t21 >> 0);
  /* Wasm instruction 123: local.get */
  /* Wasm instruction 124: i32.const */
  /* Wasm instruction 125: i32.add */
  unsigned int t22 = t19 + 1U;
  /*@ assert address_normalization: t22 == d + (5); */
  /* Wasm instruction 126: local.get */
  /* Wasm instruction 127: i32.const */
  /* Wasm instruction 128: i32.add */
  unsigned int t23 = t20 + 1U;
  /*@ assert address_normalization: t23 == s + (5); */
  /* Wasm instruction 129: i32.load8_u */
  /*@ assert physical_bounds: t23 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t23 && t23 + 1 <= s + n; */
  unsigned int t24 = ((unsigned int)m[t23 + 0U] << 0);
  /* Wasm instruction 130: i32.store8 */
  /*@ assert physical_bounds: t22 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t22 && t22 + 1 <= d + n; */
  m[t22 + 0U] = (unsigned char)(t24 >> 0);
  /* Wasm instruction 131: local.get */
  /* Wasm instruction 132: i32.const */
  /* Wasm instruction 133: i32.add */
  unsigned int t25 = t19 + 2U;
  /*@ assert address_normalization: t25 == d + (6); */
  /* Wasm instruction 134: local.get */
  /* Wasm instruction 135: i32.const */
  /* Wasm instruction 136: i32.add */
  unsigned int t26 = t20 + 2U;
  /*@ assert address_normalization: t26 == s + (6); */
  /* Wasm instruction 137: i32.load8_u */
  /*@ assert physical_bounds: t26 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t26 && t26 + 1 <= s + n; */
  unsigned int t27 = ((unsigned int)m[t26 + 0U] << 0);
  /* Wasm instruction 138: i32.store8 */
  /*@ assert physical_bounds: t25 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t25 && t25 + 1 <= d + n; */
  m[t25 + 0U] = (unsigned char)(t27 >> 0);
  /* Wasm instruction 139: local.get */
  /* Wasm instruction 140: i32.const */
  /* Wasm instruction 141: i32.add */
  unsigned int t28 = t19 + 3U;
  /*@ assert address_normalization: t28 == d + (7); */
  /* Wasm instruction 142: local.get */
  /* Wasm instruction 143: i32.const */
  /* Wasm instruction 144: i32.add */
  unsigned int t29 = t20 + 3U;
  /*@ assert address_normalization: t29 == s + (7); */
  /* Wasm instruction 145: i32.load8_u */
  /*@ assert physical_bounds: t29 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t29 && t29 + 1 <= s + n; */
  unsigned int t30 = ((unsigned int)m[t29 + 0U] << 0);
  /* Wasm instruction 146: i32.store8 */
  /*@ assert physical_bounds: t28 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t28 && t28 + 1 <= d + n; */
  m[t28 + 0U] = (unsigned char)(t30 >> 0);
  /* Wasm instruction 147: local.get */
  /* Wasm instruction 148: local.get */
  /* Wasm instruction 149: i32.const */
  /* Wasm instruction 150: i32.add */
  unsigned int t31 = t17 + 4U;
  /* Wasm instruction 151: local.tee */
  /* Wasm instruction 152: i32.ne */
  unsigned int t32 = t4 != t31;
  /* Wasm instruction 153: br_if */
  /*@ assert branch_8: t32 != 0; */
  /* Wasm instruction 113: local.get */
  /* Wasm instruction 114: local.get */
  /* Wasm instruction 115: i32.add */
  unsigned int t33 = d + t31;
  /*@ assert address_normalization: t33 == d + (8); */
  /* Wasm instruction 116: local.tee */
  /* Wasm instruction 117: local.get */
  /* Wasm instruction 118: local.get */
  /* Wasm instruction 119: i32.add */
  unsigned int t34 = s + t31;
  /*@ assert address_normalization: t34 == s + (8); */
  /* Wasm instruction 120: local.tee */
  /* Wasm instruction 121: i32.load8_u */
  /*@ assert physical_bounds: t34 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t34 && t34 + 1 <= s + n; */
  unsigned int t35 = ((unsigned int)m[t34 + 0U] << 0);
  /* Wasm instruction 122: i32.store8 */
  /*@ assert physical_bounds: t33 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t33 && t33 + 1 <= d + n; */
  m[t33 + 0U] = (unsigned char)(t35 >> 0);
  /* Wasm instruction 123: local.get */
  /* Wasm instruction 124: i32.const */
  /* Wasm instruction 125: i32.add */
  unsigned int t36 = t33 + 1U;
  /*@ assert address_normalization: t36 == d + (9); */
  /* Wasm instruction 126: local.get */
  /* Wasm instruction 127: i32.const */
  /* Wasm instruction 128: i32.add */
  unsigned int t37 = t34 + 1U;
  /*@ assert address_normalization: t37 == s + (9); */
  /* Wasm instruction 129: i32.load8_u */
  /*@ assert physical_bounds: t37 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t37 && t37 + 1 <= s + n; */
  unsigned int t38 = ((unsigned int)m[t37 + 0U] << 0);
  /* Wasm instruction 130: i32.store8 */
  /*@ assert physical_bounds: t36 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t36 && t36 + 1 <= d + n; */
  m[t36 + 0U] = (unsigned char)(t38 >> 0);
  /* Wasm instruction 131: local.get */
  /* Wasm instruction 132: i32.const */
  /* Wasm instruction 133: i32.add */
  unsigned int t39 = t33 + 2U;
  /*@ assert address_normalization: t39 == d + (10); */
  /* Wasm instruction 134: local.get */
  /* Wasm instruction 135: i32.const */
  /* Wasm instruction 136: i32.add */
  unsigned int t40 = t34 + 2U;
  /*@ assert address_normalization: t40 == s + (10); */
  /* Wasm instruction 137: i32.load8_u */
  /*@ assert physical_bounds: t40 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t40 && t40 + 1 <= s + n; */
  unsigned int t41 = ((unsigned int)m[t40 + 0U] << 0);
  /* Wasm instruction 138: i32.store8 */
  /*@ assert physical_bounds: t39 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t39 && t39 + 1 <= d + n; */
  m[t39 + 0U] = (unsigned char)(t41 >> 0);
  /* Wasm instruction 139: local.get */
  /* Wasm instruction 140: i32.const */
  /* Wasm instruction 141: i32.add */
  unsigned int t42 = t33 + 3U;
  /*@ assert address_normalization: t42 == d + (11); */
  /* Wasm instruction 142: local.get */
  /* Wasm instruction 143: i32.const */
  /* Wasm instruction 144: i32.add */
  unsigned int t43 = t34 + 3U;
  /*@ assert address_normalization: t43 == s + (11); */
  /* Wasm instruction 145: i32.load8_u */
  /*@ assert physical_bounds: t43 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t43 && t43 + 1 <= s + n; */
  unsigned int t44 = ((unsigned int)m[t43 + 0U] << 0);
  /* Wasm instruction 146: i32.store8 */
  /*@ assert physical_bounds: t42 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t42 && t42 + 1 <= d + n; */
  m[t42 + 0U] = (unsigned char)(t44 >> 0);
  /* Wasm instruction 147: local.get */
  /* Wasm instruction 148: local.get */
  /* Wasm instruction 149: i32.const */
  /* Wasm instruction 150: i32.add */
  unsigned int t45 = t31 + 4U;
  /* Wasm instruction 151: local.tee */
  /* Wasm instruction 152: i32.ne */
  unsigned int t46 = t4 != t45;
  /* Wasm instruction 153: br_if */
  /*@ assert branch_8: t46 == 0; */
  /* Wasm instruction 154: local.get */
  /* Wasm instruction 155: i32.eqz */
  unsigned int t47 = !t2;
  /* Wasm instruction 156: br_if */
  /*@ assert branch_9: t47 == 0; */
  /* Wasm instruction 157: local.get */
  /* Wasm instruction 158: local.get */
  /* Wasm instruction 159: i32.add */
  unsigned int t48 = s + t45;
  /*@ assert address_normalization: t48 == s + (12); */
  /* Wasm instruction 160: local.set */
  /* Wasm instruction 161: local.get */
  /* Wasm instruction 162: local.get */
  /* Wasm instruction 163: i32.add */
  unsigned int t49 = d + t45;
  /*@ assert address_normalization: t49 == d + (12); */
  /* Wasm instruction 164: local.set */
  /* Wasm instruction 165: local.get */
  /* Wasm instruction 166: local.get */
  /* Wasm instruction 167: i32.load8_u */
  /*@ assert physical_bounds: t48 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t48 && t48 + 1 <= s + n; */
  unsigned int t50 = ((unsigned int)m[t48 + 0U] << 0);
  /* Wasm instruction 168: i32.store8 */
  /*@ assert physical_bounds: t49 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t49 && t49 + 1 <= d + n; */
  m[t49 + 0U] = (unsigned char)(t50 >> 0);
  /* Wasm instruction 169: local.get */
  /* Wasm instruction 170: i32.const */
  /* Wasm instruction 171: i32.add */
  unsigned int t51 = t48 + 1U;
  /*@ assert address_normalization: t51 == s + (13); */
  /* Wasm instruction 172: local.set */
  /* Wasm instruction 173: local.get */
  /* Wasm instruction 174: i32.const */
  /* Wasm instruction 175: i32.add */
  unsigned int t52 = t49 + 1U;
  /*@ assert address_normalization: t52 == d + (13); */
  /* Wasm instruction 176: local.set */
  /* Wasm instruction 177: local.get */
  /* Wasm instruction 178: i32.const */
  /* Wasm instruction 179: i32.add */
  unsigned int t53 = t2 + 4294967295U;
  /* Wasm instruction 180: local.tee */
  /* Wasm instruction 181: br_if */
  /*@ assert branch_10: t53 != 0; */
  /* Wasm instruction 165: local.get */
  /* Wasm instruction 166: local.get */
  /* Wasm instruction 167: i32.load8_u */
  /*@ assert physical_bounds: t51 <= 2097152 - 1; */
  /*@ assert read_footprint: s <= t51 && t51 + 1 <= s + n; */
  unsigned int t54 = ((unsigned int)m[t51 + 0U] << 0);
  /* Wasm instruction 168: i32.store8 */
  /*@ assert physical_bounds: t52 <= 2097152 - 1; */
  /*@ assert write_footprint: d <= t52 && t52 + 1 <= d + n; */
  m[t52 + 0U] = (unsigned char)(t54 >> 0);
  /* Wasm instruction 169: local.get */
  /* Wasm instruction 170: i32.const */
  /* Wasm instruction 171: i32.add */
  unsigned int t55 = t51 + 1U;
  /*@ assert address_normalization: t55 == s + (14); */
  /* Wasm instruction 172: local.set */
  /* Wasm instruction 173: local.get */
  /* Wasm instruction 174: i32.const */
  /* Wasm instruction 175: i32.add */
  unsigned int t56 = t52 + 1U;
  /*@ assert address_normalization: t56 == d + (14); */
  /* Wasm instruction 176: local.set */
  /* Wasm instruction 177: local.get */
  /* Wasm instruction 178: i32.const */
  /* Wasm instruction 179: i32.add */
  unsigned int t57 = t53 + 4294967295U;
  /* Wasm instruction 180: local.tee */
  /* Wasm instruction 181: br_if */
  /*@ assert branch_10: t57 == 0; */
  /* Wasm instruction 182: local.get */
  /* Wasm instruction 183: return */
  /*@ assert copied_byte_0: m[d+0] == \at(m[s+0],Pre); */
  /*@ assert copied_byte_1: m[d+1] == \at(m[s+1],Pre); */
  /*@ assert copied_byte_2: m[d+2] == \at(m[s+2],Pre); */
  /*@ assert copied_byte_3: m[d+3] == \at(m[s+3],Pre); */
  /*@ assert copied_byte_4: m[d+4] == \at(m[s+4],Pre); */
  /*@ assert copied_byte_5: m[d+5] == \at(m[s+5],Pre); */
  /*@ assert copied_byte_6: m[d+6] == \at(m[s+6],Pre); */
  /*@ assert copied_byte_7: m[d+7] == \at(m[s+7],Pre); */
  /*@ assert copied_byte_8: m[d+8] == \at(m[s+8],Pre); */
  /*@ assert copied_byte_9: m[d+9] == \at(m[s+9],Pre); */
  /*@ assert copied_byte_10: m[d+10] == \at(m[s+10],Pre); */
  /*@ assert copied_byte_11: m[d+11] == \at(m[s+11],Pre); */
  /*@ assert copied_byte_12: m[d+12] == \at(m[s+12],Pre); */
  /*@ assert copied_byte_13: m[d+13] == \at(m[s+13],Pre); */
  return d;
}
/*@
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures copy: \forall integer k; 0 <= k < n ==> m[d+k] == \old(m[s+k]);
*/
unsigned int move4(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  switch(n) {
  case 0: if (d < s) return move4_0_1(m,d,s,n); else return move4_0_0(m,d,s,n);
  case 1: if (d < s) return move4_1_1(m,d,s,n); else return move4_1_0(m,d,s,n);
  case 2: if (d < s) return move4_2_1(m,d,s,n); else return move4_2_0(m,d,s,n);
  case 3: if (d < s) return move4_3_1(m,d,s,n); else return move4_3_0(m,d,s,n);
  case 4: if (d < s) return move4_4_1(m,d,s,n); else return move4_4_0(m,d,s,n);
  case 5: if (d < s) return move4_5_1(m,d,s,n); else return move4_5_0(m,d,s,n);
  case 6: if (d < s) return move4_6_1(m,d,s,n); else return move4_6_0(m,d,s,n);
  case 7: if (d < s) return move4_7_1(m,d,s,n); else return move4_7_0(m,d,s,n);
  case 8: if (d < s) return move4_8_1(m,d,s,n); else return move4_8_0(m,d,s,n);
  case 9: if (d < s) return move4_9_1(m,d,s,n); else return move4_9_0(m,d,s,n);
  case 10: if (d < s) return move4_10_1(m,d,s,n); else return move4_10_0(m,d,s,n);
  case 11: if (d < s) return move4_11_1(m,d,s,n); else return move4_11_0(m,d,s,n);
  case 12: if (d < s) return move4_12_1(m,d,s,n); else return move4_12_0(m,d,s,n);
  case 13: if (d < s) return move4_13_1(m,d,s,n); else return move4_13_0(m,d,s,n);
  case 14: if (d < s) return move4_14_1(m,d,s,n); else return move4_14_0(m,d,s,n);
  default: /*@ assert \false; */ return 0;
  }
}
/*@
  requires specialization: cap == 0 && size == 1;
  requires memory: \valid(m + (0..2097151));
  requires source: 131072 <= s <= 2097151 && size <= 1966080 && s + size <= 2097152;
  requires destination: 131072 <= d <= 2097151 && cap <= 1966080 && d + cap <= 2097152;
  requires separate: d + cap <= s || s + size <= d;
  requires domain: cap == 0 || size == 0 ||
    (1 <= size <= 15 && m[s] / 16 == size - 1);
  assigns m[d..d+cap-1];
  ensures zero_capacity: cap == 0 ==>
    (\result == ((size == 1 && \old(m[s]) == 0) ? 0 : 4294967295));
  ensures empty_source: size == 0 ==> \result == 4294967295;
  ensures literals_fit: cap > 0 && size > 0 && size - 1 <= cap ==> \result == size - 1;
  ensures literals_large: cap > 0 && size > 0 && size - 1 > cap ==> \result == 4294967294;
  ensures content: cap > 0 && size > 0 && size - 1 <= cap ==>
    (\forall integer k; 0 <= k < size - 1 ==> m[d+k] == \old(m[s+1+k]));
*/
unsigned int decode_zero_one(unsigned char *m, unsigned int s, unsigned int d, unsigned int size, unsigned int cap) {
  /*@ assert fixed_parameter: size == 1; */
  /*@ assert fixed_parameter: cap == 0; */
  /* Wasm instruction 0: i32.const */
  /* Wasm instruction 1: local.set */
  /* Wasm instruction 2: local.get */
  /* Wasm instruction 3: i32.eqz */
  unsigned int t0 = !s;
  /* Wasm instruction 4: br_if */
  /*@ assert branch_0: t0 == 0; */
  /* Wasm instruction 5: local.get */
  /* Wasm instruction 6: i32.const */
  /* Wasm instruction 7: i32.lt_s */
  unsigned int t1 = (int)0U < (int)0U;
  /* Wasm instruction 8: br_if */
  /*@ assert branch_1: t1 == 0; */
  /* Wasm instruction 9: local.get */
  /* Wasm instruction 10: br_if */
  /*@ assert branch_2: 0U == 0; */
  /* Wasm instruction 11: local.get */
  /* Wasm instruction 12: i32.const */
  /* Wasm instruction 13: i32.ne */
  unsigned int t2 = 1U != 1U;
  /* Wasm instruction 14: br_if */
  /*@ assert branch_3: t2 == 0; */
  /* Wasm instruction 15: i32.const */
  /* Wasm instruction 16: i32.const */
  /* Wasm instruction 17: local.get */
  /* Wasm instruction 18: i32.load8_u */
  /*@ assert physical_bounds: s <= 2097152 - 1; */
  /*@ assert read_footprint: (d <= s && s + 1 <= d + cap) || (s <= s && s + 1 <= s + size); */
  unsigned int t3 = ((unsigned int)m[s + 0U] << 0);
  /* Wasm instruction 19: select */
  unsigned int t4 = t3 ? 4294967295U : 0U;
  /* Wasm instruction 20: return */
  return t4;
}
/*@
  requires specialization: cap == 0 && size != 1;
  requires memory: \valid(m + (0..2097151));
  requires source: 131072 <= s <= 2097151 && size <= 1966080 && s + size <= 2097152;
  requires destination: 131072 <= d <= 2097151 && cap <= 1966080 && d + cap <= 2097152;
  requires separate: d + cap <= s || s + size <= d;
  requires domain: cap == 0 || size == 0 ||
    (1 <= size <= 15 && m[s] / 16 == size - 1);
  assigns m[d..d+cap-1];
  ensures zero_capacity: cap == 0 ==>
    (\result == ((size == 1 && \old(m[s]) == 0) ? 0 : 4294967295));
  ensures empty_source: size == 0 ==> \result == 4294967295;
  ensures literals_fit: cap > 0 && size > 0 && size - 1 <= cap ==> \result == size - 1;
  ensures literals_large: cap > 0 && size > 0 && size - 1 > cap ==> \result == 4294967294;
  ensures content: cap > 0 && size > 0 && size - 1 <= cap ==>
    (\forall integer k; 0 <= k < size - 1 ==> m[d+k] == \old(m[s+1+k]));
*/
unsigned int decode_zero_other(unsigned char *m, unsigned int s, unsigned int d, unsigned int size, unsigned int cap) {
  /*@ assert fixed_parameter: cap == 0; */
  /* Wasm instruction 0: i32.const */
  /* Wasm instruction 1: local.set */
  /* Wasm instruction 2: local.get */
  /* Wasm instruction 3: i32.eqz */
  unsigned int t0 = !s;
  /* Wasm instruction 4: br_if */
  /*@ assert branch_0: t0 == 0; */
  /* Wasm instruction 5: local.get */
  /* Wasm instruction 6: i32.const */
  /* Wasm instruction 7: i32.lt_s */
  unsigned int t1 = (int)0U < (int)0U;
  /* Wasm instruction 8: br_if */
  /*@ assert branch_1: t1 == 0; */
  /* Wasm instruction 9: local.get */
  /* Wasm instruction 10: br_if */
  /*@ assert branch_2: 0U == 0; */
  /* Wasm instruction 11: local.get */
  /* Wasm instruction 12: i32.const */
  /* Wasm instruction 13: i32.ne */
  unsigned int t2 = size != 1U;
  /* Wasm instruction 14: br_if */
  /*@ assert branch_3: t2 != 0; */
  /* Wasm instruction 518: local.get */
  /* Wasm instruction 519: return */
  return 4294967295U;
}
/*@
  requires specialization: cap > 0 && size == 0;
  requires memory: \valid(m + (0..2097151));
  requires source: 131072 <= s <= 2097151 && size <= 1966080 && s + size <= 2097152;
  requires destination: 131072 <= d <= 2097151 && cap <= 1966080 && d + cap <= 2097152;
  requires separate: d + cap <= s || s + size <= d;
  requires domain: cap == 0 || size == 0 ||
    (1 <= size <= 15 && m[s] / 16 == size - 1);
  assigns m[d..d+cap-1];
  ensures zero_capacity: cap == 0 ==>
    (\result == ((size == 1 && \old(m[s]) == 0) ? 0 : 4294967295));
  ensures empty_source: size == 0 ==> \result == 4294967295;
  ensures literals_fit: cap > 0 && size > 0 && size - 1 <= cap ==> \result == size - 1;
  ensures literals_large: cap > 0 && size > 0 && size - 1 > cap ==> \result == 4294967294;
  ensures content: cap > 0 && size > 0 && size - 1 <= cap ==>
    (\forall integer k; 0 <= k < size - 1 ==> m[d+k] == \old(m[s+1+k]));
*/
unsigned int decode_empty(unsigned char *m, unsigned int s, unsigned int d, unsigned int size, unsigned int cap) {
  /*@ assert fixed_parameter: size == 0; */
  /* Wasm instruction 0: i32.const */
  /* Wasm instruction 1: local.set */
  /* Wasm instruction 2: local.get */
  /* Wasm instruction 3: i32.eqz */
  unsigned int t0 = !s;
  /* Wasm instruction 4: br_if */
  /*@ assert branch_0: t0 == 0; */
  /* Wasm instruction 5: local.get */
  /* Wasm instruction 6: i32.const */
  /* Wasm instruction 7: i32.lt_s */
  unsigned int t1 = (int)cap < (int)0U;
  /* Wasm instruction 8: br_if */
  /*@ assert branch_1: t1 == 0; */
  /* Wasm instruction 9: local.get */
  /* Wasm instruction 10: br_if */
  /*@ assert branch_2: cap != 0; */
  /* Wasm instruction 21: local.get */
  /* Wasm instruction 22: i32.eqz */
  unsigned int t2 = !0U;
  /* Wasm instruction 23: br_if */
  /*@ assert branch_4: t2 != 0; */
  /* Wasm instruction 518: local.get */
  /* Wasm instruction 519: return */
  return 4294967295U;
}
/*@
  requires specialization: cap > 0 && size > 0 && cap < size-1;
  requires memory: \valid(m + (0..2097151));
  requires source: 131072 <= s <= 2097151 && size <= 1966080 && s + size <= 2097152;
  requires destination: 131072 <= d <= 2097151 && cap <= 1966080 && d + cap <= 2097152;
  requires separate: d + cap <= s || s + size <= d;
  requires domain: cap == 0 || size == 0 ||
    (1 <= size <= 15 && m[s] / 16 == size - 1);
  assigns m[d..d+cap-1];
  ensures zero_capacity: cap == 0 ==>
    (\result == ((size == 1 && \old(m[s]) == 0) ? 0 : 4294967295));
  ensures empty_source: size == 0 ==> \result == 4294967295;
  ensures literals_fit: cap > 0 && size > 0 && size - 1 <= cap ==> \result == size - 1;
  ensures literals_large: cap > 0 && size > 0 && size - 1 > cap ==> \result == 4294967294;
  ensures content: cap > 0 && size > 0 && size - 1 <= cap ==>
    (\forall integer k; 0 <= k < size - 1 ==> m[d+k] == \old(m[s+1+k]));
*/
unsigned int decode_short_fail(unsigned char *m, unsigned int s, unsigned int d, unsigned int size, unsigned int cap) {
  /* Wasm instruction 0: i32.const */
  /* Wasm instruction 1: local.set */
  /* Wasm instruction 2: local.get */
  /* Wasm instruction 3: i32.eqz */
  unsigned int t0 = !s;
  /* Wasm instruction 4: br_if */
  /*@ assert branch_0: t0 == 0; */
  /* Wasm instruction 5: local.get */
  /* Wasm instruction 6: i32.const */
  /* Wasm instruction 7: i32.lt_s */
  unsigned int t1 = (int)cap < (int)0U;
  /* Wasm instruction 8: br_if */
  /*@ assert branch_1: t1 == 0; */
  /* Wasm instruction 9: local.get */
  /* Wasm instruction 10: br_if */
  /*@ assert branch_2: cap != 0; */
  /* Wasm instruction 21: local.get */
  /* Wasm instruction 22: i32.eqz */
  unsigned int t2 = !size;
  /* Wasm instruction 23: br_if */
  /*@ assert branch_4: t2 == 0; */
  /* Wasm instruction 24: local.get */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: i32.add */
  unsigned int t3 = d + cap;
  /* Wasm instruction 27: local.tee */
  /* Wasm instruction 28: i32.const */
  /* Wasm instruction 29: i32.add */
  unsigned int t4 = t3 + 4294967264U;
  /* Wasm instruction 30: local.set */
  /* Wasm instruction 31: local.get */
  /* Wasm instruction 32: local.get */
  /* Wasm instruction 33: i32.add */
  unsigned int t5 = s + size;
  /* Wasm instruction 34: local.tee */
  /* Wasm instruction 35: i32.const */
  /* Wasm instruction 36: i32.add */
  unsigned int t6 = t5 + 4294967280U;
  /* Wasm instruction 37: local.set */
  /* Wasm instruction 38: local.get */
  /* Wasm instruction 39: i32.const */
  /* Wasm instruction 40: i32.add */
  unsigned int t7 = t3 + 4294967291U;
  /* Wasm instruction 41: local.set */
  /* Wasm instruction 42: local.get */
  /* Wasm instruction 43: i32.const */
  /* Wasm instruction 44: i32.add */
  unsigned int t8 = t3 + 4294967289U;
  /* Wasm instruction 45: local.set */
  /* Wasm instruction 46: local.get */
  /* Wasm instruction 47: i32.const */
  /* Wasm instruction 48: i32.add */
  unsigned int t9 = t5 + 4294967292U;
  /* Wasm instruction 49: local.set */
  /* Wasm instruction 50: local.get */
  /* Wasm instruction 51: i32.const */
  /* Wasm instruction 52: i32.add */
  unsigned int t10 = t5 + 4294967288U;
  /* Wasm instruction 53: local.set */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: i32.const */
  /* Wasm instruction 56: i32.add */
  unsigned int t11 = t3 + 4294967284U;
  /* Wasm instruction 57: local.set */
  /* Wasm instruction 58: local.get */
  /* Wasm instruction 59: i32.const */
  /* Wasm instruction 60: i32.add */
  unsigned int t12 = t5 + 4294967281U;
  /* Wasm instruction 61: local.set */
  /* Wasm instruction 62: local.get */
  /* Wasm instruction 63: local.set */
  /* Wasm instruction 64: local.get */
  /* Wasm instruction 65: local.set */
  /* Wasm instruction 66: local.get */
  /* Wasm instruction 67: i32.const */
  /* Wasm instruction 68: i32.add */
  unsigned int t13 = s + 1U;
  /*@ assert address_normalization: t13 == s + (1); */
  /* Wasm instruction 69: local.set */
  /* Wasm instruction 70: local.get */
  /* Wasm instruction 71: i32.load8_u */
  /*@ assert physical_bounds: s <= 2097152 - 1; */
  /*@ assert read_footprint: (d <= s && s + 1 <= d + cap) || (s <= s && s + 1 <= s + size); */
  unsigned int t14 = ((unsigned int)m[s + 0U] << 0);
  /* Wasm instruction 72: local.tee */
  /* Wasm instruction 73: i32.const */
  /* Wasm instruction 74: i32.shr_u */
  unsigned int t15 = t14 >> (4U & 31U);
  /*@ assert literal_length: t15 == size - 1; */
  /* Wasm instruction 75: local.tee */
  /* Wasm instruction 76: i32.const */
  /* Wasm instruction 77: i32.eq */
  unsigned int t16 = t15 == 15U;
  /* Wasm instruction 78: br_if */
  /*@ assert branch_5: t16 == 0; */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: local.get */
  /* Wasm instruction 81: i32.lt_u */
  unsigned int t17 = t13 < t6;
  /* Wasm instruction 82: br_if */
  /*@ assert branch_6: t17 == 0; */
  /* Wasm instruction 83: local.get */
  /* Wasm instruction 84: local.set */
  /* Wasm instruction 85: br */
  /* Wasm instruction 224: local.get */
  /* Wasm instruction 225: local.get */
  /* Wasm instruction 226: i32.add */
  unsigned int t18 = d + t15;
  /* Wasm instruction 227: local.tee */
  /* Wasm instruction 228: local.get */
  /* Wasm instruction 229: i32.gt_u */
  unsigned int t19 = t18 > t11;
  /* Wasm instruction 230: br_if */
  /*@ assert branch_19: t19 != 0; */
  /* Wasm instruction 238: local.get */
  /* Wasm instruction 239: local.get */
  /* Wasm instruction 240: i32.add */
  unsigned int t20 = t13 + t15;
  /* Wasm instruction 241: local.get */
  /* Wasm instruction 242: i32.ne */
  unsigned int t21 = t20 != t5;
  /* Wasm instruction 243: br_if */
  /*@ assert branch_21: t21 == 0; */
  /* Wasm instruction 244: local.get */
  /* Wasm instruction 245: local.get */
  /* Wasm instruction 246: i32.gt_u */
  unsigned int t22 = t18 > t3;
  /* Wasm instruction 247: br_if */
  /*@ assert branch_22: t22 != 0; */
  /* Wasm instruction 512: local.get */
  /* Wasm instruction 513: i32.const */
  /* Wasm instruction 514: i32.xor */
  unsigned int t23 = t13 ^ 4294967295U;
  /* Wasm instruction 515: local.get */
  /* Wasm instruction 516: i32.add */
  unsigned int t24 = t23 + s;
  /* Wasm instruction 517: local.set */
  /* Wasm instruction 518: local.get */
  /* Wasm instruction 519: return */
  return t24;
}
/*@
  requires specialization: cap > 0 && size > 0 && size-1 <= cap < size+11;
  requires memory: \valid(m + (0..2097151));
  requires source: 131072 <= s <= 2097151 && size <= 1966080 && s + size <= 2097152;
  requires destination: 131072 <= d <= 2097151 && cap <= 1966080 && d + cap <= 2097152;
  requires separate: d + cap <= s || s + size <= d;
  requires domain: cap == 0 || size == 0 ||
    (1 <= size <= 15 && m[s] / 16 == size - 1);
  assigns m[d..d+cap-1];
  ensures zero_capacity: cap == 0 ==>
    (\result == ((size == 1 && \old(m[s]) == 0) ? 0 : 4294967295));
  ensures empty_source: size == 0 ==> \result == 4294967295;
  ensures literals_fit: cap > 0 && size > 0 && size - 1 <= cap ==> \result == size - 1;
  ensures literals_large: cap > 0 && size > 0 && size - 1 > cap ==> \result == 4294967294;
  ensures content: cap > 0 && size > 0 && size - 1 <= cap ==>
    (\forall integer k; 0 <= k < size - 1 ==> m[d+k] == \old(m[s+1+k]));
*/
unsigned int decode_short_tight(unsigned char *m, unsigned int s, unsigned int d, unsigned int size, unsigned int cap) {
  /* Wasm instruction 0: i32.const */
  /* Wasm instruction 1: local.set */
  /* Wasm instruction 2: local.get */
  /* Wasm instruction 3: i32.eqz */
  unsigned int t0 = !s;
  /* Wasm instruction 4: br_if */
  /*@ assert branch_0: t0 == 0; */
  /* Wasm instruction 5: local.get */
  /* Wasm instruction 6: i32.const */
  /* Wasm instruction 7: i32.lt_s */
  unsigned int t1 = (int)cap < (int)0U;
  /* Wasm instruction 8: br_if */
  /*@ assert branch_1: t1 == 0; */
  /* Wasm instruction 9: local.get */
  /* Wasm instruction 10: br_if */
  /*@ assert branch_2: cap != 0; */
  /* Wasm instruction 21: local.get */
  /* Wasm instruction 22: i32.eqz */
  unsigned int t2 = !size;
  /* Wasm instruction 23: br_if */
  /*@ assert branch_4: t2 == 0; */
  /* Wasm instruction 24: local.get */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: i32.add */
  unsigned int t3 = d + cap;
  /* Wasm instruction 27: local.tee */
  /* Wasm instruction 28: i32.const */
  /* Wasm instruction 29: i32.add */
  unsigned int t4 = t3 + 4294967264U;
  /* Wasm instruction 30: local.set */
  /* Wasm instruction 31: local.get */
  /* Wasm instruction 32: local.get */
  /* Wasm instruction 33: i32.add */
  unsigned int t5 = s + size;
  /* Wasm instruction 34: local.tee */
  /* Wasm instruction 35: i32.const */
  /* Wasm instruction 36: i32.add */
  unsigned int t6 = t5 + 4294967280U;
  /* Wasm instruction 37: local.set */
  /* Wasm instruction 38: local.get */
  /* Wasm instruction 39: i32.const */
  /* Wasm instruction 40: i32.add */
  unsigned int t7 = t3 + 4294967291U;
  /* Wasm instruction 41: local.set */
  /* Wasm instruction 42: local.get */
  /* Wasm instruction 43: i32.const */
  /* Wasm instruction 44: i32.add */
  unsigned int t8 = t3 + 4294967289U;
  /* Wasm instruction 45: local.set */
  /* Wasm instruction 46: local.get */
  /* Wasm instruction 47: i32.const */
  /* Wasm instruction 48: i32.add */
  unsigned int t9 = t5 + 4294967292U;
  /* Wasm instruction 49: local.set */
  /* Wasm instruction 50: local.get */
  /* Wasm instruction 51: i32.const */
  /* Wasm instruction 52: i32.add */
  unsigned int t10 = t5 + 4294967288U;
  /* Wasm instruction 53: local.set */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: i32.const */
  /* Wasm instruction 56: i32.add */
  unsigned int t11 = t3 + 4294967284U;
  /* Wasm instruction 57: local.set */
  /* Wasm instruction 58: local.get */
  /* Wasm instruction 59: i32.const */
  /* Wasm instruction 60: i32.add */
  unsigned int t12 = t5 + 4294967281U;
  /* Wasm instruction 61: local.set */
  /* Wasm instruction 62: local.get */
  /* Wasm instruction 63: local.set */
  /* Wasm instruction 64: local.get */
  /* Wasm instruction 65: local.set */
  /* Wasm instruction 66: local.get */
  /* Wasm instruction 67: i32.const */
  /* Wasm instruction 68: i32.add */
  unsigned int t13 = s + 1U;
  /*@ assert address_normalization: t13 == s + (1); */
  /* Wasm instruction 69: local.set */
  /* Wasm instruction 70: local.get */
  /* Wasm instruction 71: i32.load8_u */
  /*@ assert physical_bounds: s <= 2097152 - 1; */
  /*@ assert read_footprint: (d <= s && s + 1 <= d + cap) || (s <= s && s + 1 <= s + size); */
  unsigned int t14 = ((unsigned int)m[s + 0U] << 0);
  /* Wasm instruction 72: local.tee */
  /* Wasm instruction 73: i32.const */
  /* Wasm instruction 74: i32.shr_u */
  unsigned int t15 = t14 >> (4U & 31U);
  /*@ assert literal_length: t15 == size - 1; */
  /* Wasm instruction 75: local.tee */
  /* Wasm instruction 76: i32.const */
  /* Wasm instruction 77: i32.eq */
  unsigned int t16 = t15 == 15U;
  /* Wasm instruction 78: br_if */
  /*@ assert branch_5: t16 == 0; */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: local.get */
  /* Wasm instruction 81: i32.lt_u */
  unsigned int t17 = t13 < t6;
  /* Wasm instruction 82: br_if */
  /*@ assert branch_6: t17 == 0; */
  /* Wasm instruction 83: local.get */
  /* Wasm instruction 84: local.set */
  /* Wasm instruction 85: br */
  /* Wasm instruction 224: local.get */
  /* Wasm instruction 225: local.get */
  /* Wasm instruction 226: i32.add */
  unsigned int t18 = d + t15;
  /* Wasm instruction 227: local.tee */
  /* Wasm instruction 228: local.get */
  /* Wasm instruction 229: i32.gt_u */
  unsigned int t19 = t18 > t11;
  /* Wasm instruction 230: br_if */
  /*@ assert branch_19: t19 != 0; */
  /* Wasm instruction 238: local.get */
  /* Wasm instruction 239: local.get */
  /* Wasm instruction 240: i32.add */
  unsigned int t20 = t13 + t15;
  /* Wasm instruction 241: local.get */
  /* Wasm instruction 242: i32.ne */
  unsigned int t21 = t20 != t5;
  /* Wasm instruction 243: br_if */
  /*@ assert branch_21: t21 == 0; */
  /* Wasm instruction 244: local.get */
  /* Wasm instruction 245: local.get */
  /* Wasm instruction 246: i32.gt_u */
  unsigned int t22 = t18 > t3;
  /* Wasm instruction 247: br_if */
  /*@ assert branch_22: t22 == 0; */
  /* Wasm instruction 248: local.get */
  /* Wasm instruction 249: local.get */
  /* Wasm instruction 250: local.get */
  /* Wasm instruction 251: call */
  unsigned int t23 = move4(m, d, t13, t15);
  /* Wasm instruction 252: drop */
  /* Wasm instruction 253: local.get */
  /* Wasm instruction 254: local.get */
  /* Wasm instruction 255: i32.sub */
  unsigned int t24 = t18 - d;
  /* Wasm instruction 256: return */
  return t24;
}
/*@
  requires specialization: cap > 0 && size > 0 && cap >= size+11;
  requires memory: \valid(m + (0..2097151));
  requires source: 131072 <= s <= 2097151 && size <= 1966080 && s + size <= 2097152;
  requires destination: 131072 <= d <= 2097151 && cap <= 1966080 && d + cap <= 2097152;
  requires separate: d + cap <= s || s + size <= d;
  requires domain: cap == 0 || size == 0 ||
    (1 <= size <= 15 && m[s] / 16 == size - 1);
  assigns m[d..d+cap-1];
  ensures zero_capacity: cap == 0 ==>
    (\result == ((size == 1 && \old(m[s]) == 0) ? 0 : 4294967295));
  ensures empty_source: size == 0 ==> \result == 4294967295;
  ensures literals_fit: cap > 0 && size > 0 && size - 1 <= cap ==> \result == size - 1;
  ensures literals_large: cap > 0 && size > 0 && size - 1 > cap ==> \result == 4294967294;
  ensures content: cap > 0 && size > 0 && size - 1 <= cap ==>
    (\forall integer k; 0 <= k < size - 1 ==> m[d+k] == \old(m[s+1+k]));
*/
unsigned int decode_short_roomy(unsigned char *m, unsigned int s, unsigned int d, unsigned int size, unsigned int cap) {
  /* Wasm instruction 0: i32.const */
  /* Wasm instruction 1: local.set */
  /* Wasm instruction 2: local.get */
  /* Wasm instruction 3: i32.eqz */
  unsigned int t0 = !s;
  /* Wasm instruction 4: br_if */
  /*@ assert branch_0: t0 == 0; */
  /* Wasm instruction 5: local.get */
  /* Wasm instruction 6: i32.const */
  /* Wasm instruction 7: i32.lt_s */
  unsigned int t1 = (int)cap < (int)0U;
  /* Wasm instruction 8: br_if */
  /*@ assert branch_1: t1 == 0; */
  /* Wasm instruction 9: local.get */
  /* Wasm instruction 10: br_if */
  /*@ assert branch_2: cap != 0; */
  /* Wasm instruction 21: local.get */
  /* Wasm instruction 22: i32.eqz */
  unsigned int t2 = !size;
  /* Wasm instruction 23: br_if */
  /*@ assert branch_4: t2 == 0; */
  /* Wasm instruction 24: local.get */
  /* Wasm instruction 25: local.get */
  /* Wasm instruction 26: i32.add */
  unsigned int t3 = d + cap;
  /* Wasm instruction 27: local.tee */
  /* Wasm instruction 28: i32.const */
  /* Wasm instruction 29: i32.add */
  unsigned int t4 = t3 + 4294967264U;
  /* Wasm instruction 30: local.set */
  /* Wasm instruction 31: local.get */
  /* Wasm instruction 32: local.get */
  /* Wasm instruction 33: i32.add */
  unsigned int t5 = s + size;
  /* Wasm instruction 34: local.tee */
  /* Wasm instruction 35: i32.const */
  /* Wasm instruction 36: i32.add */
  unsigned int t6 = t5 + 4294967280U;
  /* Wasm instruction 37: local.set */
  /* Wasm instruction 38: local.get */
  /* Wasm instruction 39: i32.const */
  /* Wasm instruction 40: i32.add */
  unsigned int t7 = t3 + 4294967291U;
  /* Wasm instruction 41: local.set */
  /* Wasm instruction 42: local.get */
  /* Wasm instruction 43: i32.const */
  /* Wasm instruction 44: i32.add */
  unsigned int t8 = t3 + 4294967289U;
  /* Wasm instruction 45: local.set */
  /* Wasm instruction 46: local.get */
  /* Wasm instruction 47: i32.const */
  /* Wasm instruction 48: i32.add */
  unsigned int t9 = t5 + 4294967292U;
  /* Wasm instruction 49: local.set */
  /* Wasm instruction 50: local.get */
  /* Wasm instruction 51: i32.const */
  /* Wasm instruction 52: i32.add */
  unsigned int t10 = t5 + 4294967288U;
  /* Wasm instruction 53: local.set */
  /* Wasm instruction 54: local.get */
  /* Wasm instruction 55: i32.const */
  /* Wasm instruction 56: i32.add */
  unsigned int t11 = t3 + 4294967284U;
  /* Wasm instruction 57: local.set */
  /* Wasm instruction 58: local.get */
  /* Wasm instruction 59: i32.const */
  /* Wasm instruction 60: i32.add */
  unsigned int t12 = t5 + 4294967281U;
  /* Wasm instruction 61: local.set */
  /* Wasm instruction 62: local.get */
  /* Wasm instruction 63: local.set */
  /* Wasm instruction 64: local.get */
  /* Wasm instruction 65: local.set */
  /* Wasm instruction 66: local.get */
  /* Wasm instruction 67: i32.const */
  /* Wasm instruction 68: i32.add */
  unsigned int t13 = s + 1U;
  /*@ assert address_normalization: t13 == s + (1); */
  /* Wasm instruction 69: local.set */
  /* Wasm instruction 70: local.get */
  /* Wasm instruction 71: i32.load8_u */
  /*@ assert physical_bounds: s <= 2097152 - 1; */
  /*@ assert read_footprint: (d <= s && s + 1 <= d + cap) || (s <= s && s + 1 <= s + size); */
  unsigned int t14 = ((unsigned int)m[s + 0U] << 0);
  /* Wasm instruction 72: local.tee */
  /* Wasm instruction 73: i32.const */
  /* Wasm instruction 74: i32.shr_u */
  unsigned int t15 = t14 >> (4U & 31U);
  /*@ assert literal_length: t15 == size - 1; */
  /* Wasm instruction 75: local.tee */
  /* Wasm instruction 76: i32.const */
  /* Wasm instruction 77: i32.eq */
  unsigned int t16 = t15 == 15U;
  /* Wasm instruction 78: br_if */
  /*@ assert branch_5: t16 == 0; */
  /* Wasm instruction 79: local.get */
  /* Wasm instruction 80: local.get */
  /* Wasm instruction 81: i32.lt_u */
  unsigned int t17 = t13 < t6;
  /* Wasm instruction 82: br_if */
  /*@ assert branch_6: t17 == 0; */
  /* Wasm instruction 83: local.get */
  /* Wasm instruction 84: local.set */
  /* Wasm instruction 85: br */
  /* Wasm instruction 224: local.get */
  /* Wasm instruction 225: local.get */
  /* Wasm instruction 226: i32.add */
  unsigned int t18 = d + t15;
  /* Wasm instruction 227: local.tee */
  /* Wasm instruction 228: local.get */
  /* Wasm instruction 229: i32.gt_u */
  unsigned int t19 = t18 > t11;
  /* Wasm instruction 230: br_if */
  /*@ assert branch_19: t19 == 0; */
  /* Wasm instruction 231: local.get */
  /* Wasm instruction 232: local.get */
  /* Wasm instruction 233: i32.add */
  unsigned int t20 = t13 + t15;
  /* Wasm instruction 234: local.tee */
  /* Wasm instruction 235: local.get */
  /* Wasm instruction 236: i32.le_u */
  unsigned int t21 = t20 <= t10;
  /* Wasm instruction 237: br_if */
  /*@ assert branch_20: t21 == 0; */
  /* Wasm instruction 238: local.get */
  /* Wasm instruction 239: local.get */
  /* Wasm instruction 240: i32.add */
  unsigned int t22 = t13 + t15;
  /* Wasm instruction 241: local.get */
  /* Wasm instruction 242: i32.ne */
  unsigned int t23 = t22 != t5;
  /* Wasm instruction 243: br_if */
  /*@ assert branch_21: t23 == 0; */
  /* Wasm instruction 244: local.get */
  /* Wasm instruction 245: local.get */
  /* Wasm instruction 246: i32.gt_u */
  unsigned int t24 = t18 > t3;
  /* Wasm instruction 247: br_if */
  /*@ assert branch_22: t24 == 0; */
  /* Wasm instruction 248: local.get */
  /* Wasm instruction 249: local.get */
  /* Wasm instruction 250: local.get */
  /* Wasm instruction 251: call */
  unsigned int t25 = move4(m, d, t13, t15);
  /* Wasm instruction 252: drop */
  /* Wasm instruction 253: local.get */
  /* Wasm instruction 254: local.get */
  /* Wasm instruction 255: i32.sub */
  unsigned int t26 = t18 - d;
  /* Wasm instruction 256: return */
  return t26;
}
/*@
  requires memory: \valid(m + (0..2097151));
  requires source: 131072 <= s <= 2097151 && size <= 1966080 && s + size <= 2097152;
  requires destination: 131072 <= d <= 2097151 && cap <= 1966080 && d + cap <= 2097152;
  requires separate: d + cap <= s || s + size <= d;
  requires domain: cap == 0 || size == 0 ||
    (1 <= size <= 15 && m[s] / 16 == size - 1);
  assigns m[d..d+cap-1];
  ensures zero_capacity: cap == 0 ==>
    (\result == ((size == 1 && \old(m[s]) == 0) ? 0 : 4294967295));
  ensures empty_source: size == 0 ==> \result == 4294967295;
  ensures literals_fit: cap > 0 && size > 0 && size - 1 <= cap ==> \result == size - 1;
  ensures literals_large: cap > 0 && size > 0 && size - 1 > cap ==> \result == 4294967294;
  ensures content: cap > 0 && size > 0 && size - 1 <= cap ==>
    (\forall integer k; 0 <= k < size - 1 ==> m[d+k] == \old(m[s+1+k]));
*/
unsigned int decode2(unsigned char *m, unsigned int s, unsigned int d, unsigned int size, unsigned int cap) {
  if (cap == 0) {
    if (size == 1) return decode_zero_one(m,s,d,size,cap);
    return decode_zero_other(m,s,d,size,cap);
  }
  if (size == 0) return decode_empty(m,s,d,size,cap);
  if (cap < size-1) return decode_short_fail(m,s,d,size,cap);
  if (cap < size+11) return decode_short_tight(m,s,d,size,cap);
  return decode_short_roomy(m,s,d,size,cap);
}
