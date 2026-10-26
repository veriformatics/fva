/* Exact integer certificates for the two concrete IEEE-754 witnesses.
 * No floating operations are replaced by real arithmetic in WP.
 *
 * strict_nearest(n,d,k) means k is strictly within half a unit of n/d.
 * For a positive binary64 value on a fixed exponent's grid this certifies
 * round-to-nearest (no tie); the exponent/grid interpretation is documented
 * in VERIFICATION.md. All ACSL integer arithmetic is unbounded.
 */

/*@ predicate strict_nearest(integer n, integer d, integer k) =
      d > 0 && (2*k-1)*d < 2*n && 2*n < (2*k+1)*d;

    logic integer raw_sig = 4772185884444444;
    logic integer div_sig = 5003999585967218;
    logic integer cutoff_sig = 4772185884444445;

    logic integer overflow_count = 89884656743115795386465259539451236680898848947115328636715040578866337902750481566354238661203768010560056939935696678829394884407208311246423715319737062188883946712432742638151109800623047059726541476042502884419075341171231440736956555270413618581675255342293149119973622969239858152417678164812112068608;
    logic integer overflow_midpoint = 179769313486231580793728971405303415079934132710037826936173778980444968292764750946649017977587207096330286416692887910946555547851940402630657488671505820681908902000708383676273854845817711531764475730270069855571366959622842914819860834936475292719074168444365510704342711559699508093042880177904174497792;
*/

/*@ lemma nearest_unique_for_witness_grids:
      \forall integer n,d,k,j;
        (d == 18 || d == 1048576) &&
        strict_nearest(n,d,k) && strict_nearest(n,d,j) ==> k == j;
*/

/*@ assigns \nothing;
    ensures 4503599627370496 <= raw_sig < 9007199254740992;
    ensures 4503599627370496 <= div_sig < 9007199254740992;
    ensures 4503599627370496 <= cutoff_sig < 9007199254740992;
    // (10*1e6)/18, in units of 2^-33, is (1e7*2^33)/18.
    ensures strict_nearest(10000000*8589934592,18,raw_sig);
    // 10/18, in units of 2^-53, is (10*2^53)/18.
    ensures strict_nearest(10*9007199254740992,18,div_sig);
    // (div_sig/2^53)*1e6, in units of 2^-33.
    ensures strict_nearest(div_sig*1000000,1048576,cutoff_sig);
    ensures cutoff_sig == raw_sig+1;
    // Actual raw CPM is BELOW the exact target by precisely this amount.
    ensures 10000000*8589934592 - raw_sig*18 == 8;
    ensures 8*19327352832 == 8589934592*18;
    // Exact raw relative error is 1/10737418240000000.
    ensures 8*10737418240000000 == 10000000*8589934592;
*/
void rounding_certificate(void) {}

/*@ assigns \nothing;
    ensures overflow_count > 0;
    ensures overflow_count*1000000 > overflow_midpoint;
    ensures (overflow_count*1000000)/overflow_count == 1000000;
*/
void overflow_certificate(void) {}

/*@ assigns \nothing;
    ensures \result == 0;
*/
int filter_witness(void) {
    // Compare the certified CPM/cutoff significands on their common grid.
    long long raw = 4772185884444444LL;
    long long cutoff = 4772185884444445LL;
    int qualifying_samples = raw >= cutoff ? 2 : 0;
    int total_count = 20;
    return qualifying_samples >= 2 && total_count >= 15;
}

/*@ assigns \nothing;
    ensures \result == 1;
*/
int documented_witness(void) {
    // At L=median(L), the documented scaled count is exactly 10.
    int qualifying_samples = 10 >= 10 ? 2 : 0;
    return qualifying_samples >= 2 && 20 >= 15;
}
