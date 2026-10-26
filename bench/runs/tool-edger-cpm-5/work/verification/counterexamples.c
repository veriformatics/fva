/* Scalar models of the shipped arithmetic and final R predicate.
 * No claim that Frama-C verifies the full WebAssembly or R interpreter.
 */

/*@ assigns \nothing;
    ensures \is_finite(\result);
    ensures \result == (double)555555.5555555555;
    ensures \result == 1193046471111111.0 / 2147483648.0;
    ensures \result - 5000000.0 / 9.0 == -1.0 / 19327352832.0;
*/
double shipped_cpm_at_boundary(void) {
    double c = 10.0;
    double L = 18.0;
    return c * 1000000.0 / L;
}

/*@ assigns \nothing;
    ensures \is_finite(\result);
    ensures \result == (double)555555.5555555556;
    ensures \result == 4772185884444445.0 / 8589934592.0;
*/
double documented_cutoff_at_boundary(void) {
    double min_count = 10.0;
    double median_lib = 18.0;
    return min_count / median_lib * 1000000.0;
}

/*@ assigns \nothing;
    ensures \result == 0;
*/
int rejects_boundary_gene(void) {
    double cpm = 10.0 * 1000000.0 / 18.0;
    double cutoff = 10.0 / 18.0 * 1000000.0;
    int passing = (cpm >= cutoff) + (cpm >= cutoff);
    int keep_cpm = passing >= (2.0 - 1e-14);
    int keep_total = 20.0 >= (15.0 - 1e-14);
    return keep_cpm && keep_total;
}

/*@ assigns \nothing;
    ensures 10.0 / 18.0 * 1000000.0 == 5000000.0 / 9.0;
    ensures 10 >= 10 && 2 >= 2 && 20 >= 15;
*/
void ideal_boundary_gene_meets_threshold(void) {}

/*@ logic real witness = 11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576.0;
    logic real largest_double = 179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.0;
*/
/*@ assigns \nothing;
    ensures witness > 0;
    ensures witness / witness * 1000000 == 1000000;
    ensures witness * 1000000 > largest_double * 2;
*/
void overflow_witness_real_arithmetic(void) {}
