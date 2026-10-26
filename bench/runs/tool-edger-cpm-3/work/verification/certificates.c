/*
 * Exact rational certificates, checked by Frama-C 33 WP.
 * These are NOT a translation of the whole Wasm or R interpreter.
 * No custom axioms, admitted lemmas, external calls, or FP-as-real model.
 * All multiplications in ACSL below are unbounded mathematical integers.
 */

/*@ predicate strict_nearest(integer n, integer d, integer q) =
      d > 0 && -d < 2 * (n - q*d) < d;

    predicate significand53(integer q) =
      4503599627370496 <= q < 9007199254740992;
*/

/* The exact double represented by 1e308 is S * 2^971,
   S=5010420900022432. The positive round-to-nearest overflow boundary is
   (2^54-1) * 2^970. Cancel the positive factor 2^970 below. */
/*@ assigns \nothing;
    ensures r1_overflow_boundary:
      2 * 5010420900022432 * 1000000 > 18014398509481983;
    ensures r1_reference:
      ((real)5010420900022432 / 5010420900022432) * 1000000
        == \result;
    ensures \result == 1000000;
*/
int r1_reference_and_overflow(void) {
    return 1000000;
}

/* raw = RN(10000000 / 1000009) = Q * 2^-49.
   This certificate proves the strict nearest lattice point, not merely
   that the displayed decimal string is close to the intended result. */
/*@ assigns \nothing;
    ensures raw_normal: significand53(\result);
    ensures raw_nearest:
      strict_nearest(10000000 * 562949953421312, 1000009, \result);
    ensures raw_residual:
      10000000 * 562949953421312 - \result * 1000009 == 440327;
    ensures raw_value: \result == 5629448869173297;
*/
long long raw_numerator(void) {
    return 5629448869173297LL;
}

/* RN(10 / 1000009) = S * 2^-69. */
/*@ assigns \nothing;
    ensures div_normal: significand53(\result);
    ensures div_nearest:
      strict_nearest(10 * 590295810358705651712, 1000009, \result);
    ensures div_residual:
      10 * 590295810358705651712 - \result * 1000009 == -463220;
    ensures div_value: \result == 5902904977442260;
*/
long long cutoff_div_numerator(void) {
    return 5902904977442260LL;
}

/* RN((S * 2^-69) * 1000000) = T * 2^-49.
   Scaling by 2^49 leaves the exact value S*1000000 / 2^20. */
/*@ requires input_value: s == 5902904977442260;
    assigns \nothing;
    ensures mul_normal: significand53(\result);
    ensures mul_nearest: strict_nearest(s * 1000000, 1048576, \result);
    ensures mul_residual:
      s * 1000000 - \result * 1048576 == -123648;
    ensures mul_value: \result == 5629448869173298;
*/
long long cutoff_mul_numerator(long long s) {
    return 5629448869173298LL;
}

/* Requirement at this input: two equal libraries equal their median,
   two counts of 10 reach min.count=10, required sample size=2, total=20.
   Include the documented min.total.count=15 condition as well. */
/*@ assigns \nothing;
    ensures documented_keep: \result == 1;
*/
int r2_documented_keep(void) {
    return ((10 >= 10) + (10 >= 10) >= 2) && (10 + 10 >= 15);
}

/* Compare the certified binary64 outputs using their common positive
   denominator 2^49. With zero passing samples the R tolerance 1e-14
   cannot change the decision against a required sample size of 2. */
/*@ assigns \nothing;
    ensures rounded_reject: \result == 0;
*/
int r2_rounded_keep(void) {
    long long raw = raw_numerator();
    long long s = cutoff_div_numerator();
    long long cutoff = cutoff_mul_numerator(s);
    int samples = (raw >= cutoff) + (raw >= cutoff);
    return (samples >= 2) && (10 + 10 >= 15);
}

/*@ assigns \nothing;
    ensures r2_disagreement: \result == 1;
*/
int r2_counterexample(void) {
    int expected = r2_documented_keep();
    int actual = r2_rounded_keep();
    return expected != actual;
}
