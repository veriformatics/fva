/* Independently checked base cases; generated from SHA256 8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6. */
_Static_assert(sizeof(unsigned int) == 4 && sizeof(int) == 4, "i32 machine model");
/*@
  requires specialization: d >= s;
  requires zero: n == 0;
  assigns \nothing;
  ensures result: \result == d;
*/
unsigned int move_zero_0(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
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
  requires specialization: d < s;
  requires zero: n == 0;
  assigns \nothing;
  ensures result: \result == d;
*/
unsigned int move_zero_1(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
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
  requires zero: n == 0;
  assigns \nothing;
  ensures result: \result == d;
*/
unsigned int move4(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  if (d < s) return move_zero_1(m,d,s,n);
  return move_zero_0(m,d,s,n);
}
/*@
  requires specialization: cap == 0 && size == 1;
  requires memory: \valid(m + (0..2097151));
  requires source: 131072 <= s <= 2097151 && size <= 1966080 && s + size <= 2097152;
  requires destination: 131072 <= d <= 2097151 && cap <= 1966080 && d + cap <= 2097152;
  requires domain: cap == 0 || size == 0 || (size == 1 && m[s] == 0);
  assigns \nothing;
  ensures result: \result == ((size == 1 && \old(m[s]) == 0) ? 0 : 4294967295);
*/
unsigned int base_zero_one(unsigned char *m, unsigned int s, unsigned int d, unsigned int size, unsigned int cap) {
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
  requires domain: cap == 0 || size == 0 || (size == 1 && m[s] == 0);
  assigns \nothing;
  ensures result: \result == ((size == 1 && \old(m[s]) == 0) ? 0 : 4294967295);
*/
unsigned int base_zero_other(unsigned char *m, unsigned int s, unsigned int d, unsigned int size, unsigned int cap) {
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
  requires domain: cap == 0 || size == 0 || (size == 1 && m[s] == 0);
  assigns \nothing;
  ensures result: \result == ((size == 1 && \old(m[s]) == 0) ? 0 : 4294967295);
*/
unsigned int base_empty(unsigned char *m, unsigned int s, unsigned int d, unsigned int size, unsigned int cap) {
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
  requires specialization: size == 1 && m[s] == 0 && 0 < cap < 12;
  requires memory: \valid(m + (0..2097151));
  requires source: 131072 <= s <= 2097151 && size <= 1966080 && s + size <= 2097152;
  requires destination: 131072 <= d <= 2097151 && cap <= 1966080 && d + cap <= 2097152;
  requires domain: cap == 0 || size == 0 || (size == 1 && m[s] == 0);
  assigns \nothing;
  ensures result: \result == ((size == 1 && \old(m[s]) == 0) ? 0 : 4294967295);
*/
unsigned int base_empty_tight(unsigned char *m, unsigned int s, unsigned int d, unsigned int size, unsigned int cap) {
  /*@ assert fixed_parameter: size == 1; */
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
  unsigned int t2 = !1U;
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
  unsigned int t5 = s + 1U;
  /*@ assert address_normalization: t5 == s + (1); */
  /* Wasm instruction 34: local.tee */
  /* Wasm instruction 35: i32.const */
  /* Wasm instruction 36: i32.add */
  unsigned int t6 = t5 + 4294967280U;
  /*@ assert address_normalization: t6 == s + (-15); */
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
  /*@ assert address_normalization: t9 == s + (-3); */
  /* Wasm instruction 49: local.set */
  /* Wasm instruction 50: local.get */
  /* Wasm instruction 51: i32.const */
  /* Wasm instruction 52: i32.add */
  unsigned int t10 = t5 + 4294967288U;
  /*@ assert address_normalization: t10 == s + (-7); */
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
  /*@ assert address_normalization: t12 == s + (-14); */
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
  requires specialization: size == 1 && m[s] == 0 && cap >= 12;
  requires memory: \valid(m + (0..2097151));
  requires source: 131072 <= s <= 2097151 && size <= 1966080 && s + size <= 2097152;
  requires destination: 131072 <= d <= 2097151 && cap <= 1966080 && d + cap <= 2097152;
  requires domain: cap == 0 || size == 0 || (size == 1 && m[s] == 0);
  assigns \nothing;
  ensures result: \result == ((size == 1 && \old(m[s]) == 0) ? 0 : 4294967295);
*/
unsigned int base_empty_roomy(unsigned char *m, unsigned int s, unsigned int d, unsigned int size, unsigned int cap) {
  /*@ assert fixed_parameter: size == 1; */
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
  unsigned int t2 = !1U;
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
  unsigned int t5 = s + 1U;
  /*@ assert address_normalization: t5 == s + (1); */
  /* Wasm instruction 34: local.tee */
  /* Wasm instruction 35: i32.const */
  /* Wasm instruction 36: i32.add */
  unsigned int t6 = t5 + 4294967280U;
  /*@ assert address_normalization: t6 == s + (-15); */
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
  /*@ assert address_normalization: t9 == s + (-3); */
  /* Wasm instruction 49: local.set */
  /* Wasm instruction 50: local.get */
  /* Wasm instruction 51: i32.const */
  /* Wasm instruction 52: i32.add */
  unsigned int t10 = t5 + 4294967288U;
  /*@ assert address_normalization: t10 == s + (-7); */
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
  /*@ assert address_normalization: t12 == s + (-14); */
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
  requires domain: cap == 0 || size == 0 || (size == 1 && m[s] == 0);
  assigns \nothing;
  ensures result: \result == ((size == 1 && \old(m[s]) == 0) ? 0 : 4294967295);
*/
unsigned int decode_base(unsigned char *m, unsigned int s, unsigned int d, unsigned int size, unsigned int cap) {
  if (cap == 0) {
    if (size == 1) return base_zero_one(m,s,d,size,cap);
    return base_zero_other(m,s,d,size,cap);
  }
  if (size == 0) return base_empty(m,s,d,size,cap);
  if (cap < 12) return base_empty_tight(m,s,d,size,cap);
  return base_empty_roomy(m,s,d,size,cap);
}
