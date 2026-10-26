# Run from repository root. The shipped R functions are sourced unchanged.
source("R/cpm.R")
source("R/filterByExpr.R")

# Replace only the absent R-to-Wasm FFI. Both numerical computation and all
# filtering decisions come from the supplied software, not an R CPM model.
bridge <- new.env(parent=globalenv())
bridge$.cxx_calculate_cpm_raw <- "raw-wasm"
bridge$makeCompressedMatrix <- function(x, dims, byrow) {
    stopifnot(isTRUE(byrow), length(x) == dims[2L])
    x
}
bridge$.Call <- function(symbol, y, lib.size, nthreads) {
    stopifnot(identical(symbol, "raw-wasm"), nrow(y) == 1L, nthreads == 1L)
    csv <- function(x) paste(sprintf("%.17g", x), collapse=",")
    output <- system2("python3", c("verification/artifact_cpm.py", csv(y), csv(lib.size)), stdout=TRUE)
    stopifnot(is.null(attr(output, "status")))
    matrix(as.numeric(output), nrow=1L)
}
environment(cpm.default) <- bridge

# R1: finite, exactly represented c = L = 2^1020. Exact answer = 10^6.
c <- 2^1020
actual <- cpm(matrix(c, 1L, 1L), lib.size=c)[1L,1L]
expected <- c/c*1e6
stopifnot(is.infinite(actual), actual > 0, expected == 1e6)
cat(sprintf("R1 COUNTEREXAMPLE: c=L=2^1020; artifact=%s; required=%.0f\n", actual, expected))

# R2: a single gene, two samples, default min.count=10, min.total.count=15.
# It has exactly min.count in both required samples and total count 20 >= 15.
y <- matrix(c(10,10), 1L, 2L)
lib <- c(36,36)
actual.cpm <- cpm(y, lib.size=lib)
cutoff <- 10/median(lib)*1e6
keep <- filterByExpr(y, lib.size=lib, min.sample.size=2)
stopifnot(all(y == 10), sum(y) >= 15, all(actual.cpm < cutoff), identical(keep, FALSE))
cat(sprintf("R2 COUNTEREXAMPLE: y=[10,10], lib.size=[36,36], required.samples=2, total=20\n"))
cat(sprintf("  artifact CPM=%.17g (%a); cutoff=%.17g (%a); keep=%s\n", actual.cpm[1L], actual.cpm[1L], cutoff, cutoff, keep))

cat("All counterexample assertions passed.\n")
