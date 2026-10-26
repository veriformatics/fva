/* Small explicit models of the two counterexamples, not a replacement for
   execution of edgeR.so or R/filterByExpr.R. No axioms or external contracts. */

/*@ assigns \nothing;
    ensures reference_exact: \result == 1000000.0;
*/
double r1_reference_witness(void) {
    double c = 0x1p+1020;
    double lib = 0x1p+1020;
    return (c / lib) * 1000000.0;
}

/* Fixed numerical tail of filterByExpr.default, after MinSampleSize=1 and
   CPM=10 have been established by its input and the artifact witness. */
/*@ assigns \nothing;
    ensures rejected_by_total: \result == 0;
*/
int r2_rejects_witness(void) {
    double cpm = 10.0;
    double median_library_size = 1000000.0;
    double min_count = 10.0;
    double min_sample_size = 1.0;
    double min_total_count = 15.0;
    double tol = 1e-14;
    double cutoff = min_count / median_library_size * 1000000.0;
    int hits = cpm >= cutoff;
    int keep_cpm = hits >= min_sample_size - tol;
    int keep_total = 10.0 >= min_total_count - tol;
    /*@ assert threshold: cutoff == 10.0; */
    /*@ assert hits_required: hits == 1; */
    /*@ assert meets_R2_sample_condition: keep_cpm == 1; */
    /*@ assert fails_total_condition: keep_total == 0; */
    return keep_cpm && keep_total;
}

/* Numerical tail for the first gene in y=matrix(c(10,26,10,26),nrow=2).
   Column sums and median are 36; two samples required, row total is 20. */
/*@ assigns \nothing;
    ensures rejected_despite_counts_and_total: \result == 0;
*/
int r2_rounding_boundary(void) {
    double count = 10.0, lib = 36.0;
    double cpm = count * 1000000.0 / lib;
    double cutoff = 10.0 / lib * 1000000.0;
    double tol = 1e-14;
    int hits = (cpm >= cutoff) + (cpm >= cutoff);
    int keep_cpm = hits >= 2.0 - tol;
    int keep_total = 20.0 >= 15.0 - tol;
    /*@ assert counts_qualify: count >= 10.0; */
    /*@ assert exact_artifact_cell: cpm == 1193046471111111.0 / 4294967296.0; */
    /*@ assert exact_R_cutoff: cutoff == 4772185884444445.0 / 17179869184.0; */
    /*@ assert zero_hits: hits == 0; */
    /*@ assert sample_test_fails: keep_cpm == 0; */
    /*@ assert total_test_passes: keep_total == 1; */
    return keep_cpm && keep_total;
}
