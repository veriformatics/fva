/* Concrete arithmetic models, not a replacement for execution of edgeR.so. */

/*@ assigns \nothing;
    ensures \is_finite(\result);
    ensures (real)\result == 1193046471111111.0 / 2147483648.0;
    ensures (real)\result - 5000000.0 / 9.0 == -1.0 / 19327352832.0;
*/
double raw_boundary(void) {
    return (10.0 * 1000000.0) / 18.0;
}

/*@ assigns \nothing;
    ensures \is_finite(\result);
    ensures (real)\result == 4772185884444445.0 / 8589934592.0;
    ensures (real)\result - 5000000.0 / 9.0 == 5.0 / 77309411328.0;
*/
double cutoff_boundary(void) {
    return (10.0 / 18.0) * 1000000.0;
}

/*@ assigns \nothing;
    ensures \result == 0;
*/
int filter_boundary(void) {
    double cpm = raw_boundary();
    double cutoff = cutoff_boundary();
    /*@ assert (real)cpm < (real)cutoff; */
    /*@ assert cpm < cutoff; */
    int passing = (cpm >= cutoff) + (cpm >= cutoff);
    /*@ assert passing == 0; */
    int enough_samples = passing >= (2.0 - 1e-14);
    /*@ assert enough_samples == 0; */
    int enough_total = 20.0 >= (15.0 - 1e-14);
    return enough_samples && enough_total;
}

/*@ assigns \nothing;
    ensures \result == 1;
*/
int specification_boundary(void) {
    /* Equal library sizes: the median is 18, so the scaled minimum is 10. */
    return (10 >= 10) && (10 >= 10) && (20 >= 15);
}

/*@ assigns \nothing;
    ensures \result == 1;
*/
int r2_disagreement(void) {
    int actual = filter_boundary();
    int required = specification_boundary();
    return actual != required;
}

/*@ requires \is_finite(c) && c > 0;
    assigns \nothing;
    ensures ((real)c / (real)c) * 1000000 == 1000000;
*/
void exact_reference(double c) { }

/*@ assigns \nothing;
    ensures \result == 1000000.0;
*/
double overflow_reference(void) {
    /* This is the binary64 value obtained by parsing the decimal 1e308. */
    double c = 0x1.1ccf385ebc8a0p+1023;
    double largest = 0x1.fffffffffffffp+1023;
    /*@ assert (real)c > 0; */
    /*@ assert (real)c * 1000000 > (real)largest; */
    /*@ assert ((real)c / (real)c) * 1000000 == 1000000; */
    return (c / c) * 1000000.0;
}
