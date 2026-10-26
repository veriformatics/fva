# Execute the shipped filterByExpr with the CPM dependency isolated explicitly.
# Its ordinary CPM=10 input is asserted on the exact Wasm in artifact_test.py.
# The boundary CPM is likewise asserted there; this is not an installed edgeR package.
stopifnot(system2("sha256sum", c("-c", "verification/sources.sha256")) == 0L)
source("R/filterByExpr.R")
run.case <- function(y, L, value) {
    env <- new.env(parent=environment(filterByExpr.default))
    env$cpm <- function(y, lib.size) {
        stopifnot(identical(y, matrix(10, 1, ncol(y))), all(lib.size == L))
        matrix(value, nrow(y), ncol(y))
    }
    fun <- filterByExpr.default
    environment(fun) <- env
    fun(y, lib.size=rep(L,ncol(y)), min.sample.size=ncol(y))
}
# All CPM/sample tests pass; the documented additional total-count test rejects 10 < 15.
a <- run.case(matrix(10, 1, 1), 1e6, 10)
stopifnot(identical(a, FALSE))
# Default large.n=10, max.n.samples=40 do not modify required sample size 2.
# Both counts meet min.count=10, and total=20 meets min.total.count=15.
# The median is exactly 18. The computed CPM lies one ULP below the R cutoff.
actual <- 10*1e6/18
cutoff <- 10/18*1e6
stopifnot(actual < cutoff, actual == 555555.5555555555,
          cutoff == 555555.5555555556)
b <- run.case(matrix(10, 1, 2), 18, actual)
stopifnot(identical(b, FALSE), 20 >= 15-1e-14)
cat("PASS: R2 total-count witness: sample condition TRUE, result FALSE\n")
cat("PASS: R2 rounding witness: both counts 10, total 20; result FALSE\n")
cat(sprintf("CPM %.17g < cutoff %.17g\n", actual, cutoff))
