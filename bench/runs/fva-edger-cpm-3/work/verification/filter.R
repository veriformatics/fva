# Run from the project root. The package-specific .Call bridge below checks
# every returned CPM bit pattern against the unchanged Wasm artifact.
source("R/cpm.R")
source("R/filterByExpr.R")

# These two package integration shims cover only the double matrix/vector
# inputs used below. The actual cpm.default and filterByExpr.default run as shipped.
makeCompressedMatrix <- function(x, dims, byrow) {
    stopifnot(byrow, is.double(x), length(x) == dims[2])
    matrix(x, dims[1], dims[2], byrow=TRUE)
}
.cxx_calculate_cpm_raw <- "checked-calc-cpm-raw"
.Call <- function(symbol, y, lib.size, nthreads) {
    stopifnot(identical(symbol, .cxx_calculate_cpm_raw), nthreads == 1L,
              nrow(y) == 1L, all(is.finite(y)), all(is.finite(lib.size)))
    out <- y * 1e6 / lib.size
    triples <- as.vector(rbind(as.vector(y), as.vector(lib.size), as.vector(out)))
    path <- tempfile()
    on.exit(unlink(path))
    writeBin(triples, path, size=8L, endian="little")
    status <- system2("python3", c("verification/reproduce.py", "--check-cpm", shQuote(path)))
    stopifnot(status == 0L)
    out
}

# Also execute R1 through the shipped cpm.default wrapper.
large <- 2^1023
stopifnot(identical(as.vector(cpm(matrix(large,1,1), lib.size=large)), Inf),
          large / large * 1e6 == 1e6)
cat("R1 through shipped cpm.default: finite c=L=2^1023 produces Inf.\n")

# R2's literal equivalence omits the documented total-count condition.
a <- filterByExpr(matrix(10, 1, 1), lib.size=1e6, min.sample.size=1)
stopifnot(identical(a, FALSE))
cat("R2 total-count witness: count=10, L=1e6, required samples=1: FALSE (total=10 < 15).\n")

# Stronger witness: the documented total-count condition is also satisfied.
y <- matrix(c(10, 10), 1, 2)
lib <- c(18, 18)
actual <- cpm(y, lib.size=lib)
cutoff <- 10 / median(lib) * 1e6
required <- ncol(y)
expected <- sum(y >= 10) >= required && sum(y) >= 15
b <- filterByExpr(y, lib.size=lib)
stopifnot(expected, identical(b, FALSE), all(actual < cutoff), sum(y) == 20)
cat(sprintf("R2 rounding witness: counts=[10,10], libraries=[18,18], required samples=2: FALSE.\n"))
cat(sprintf("Actual CPM=%.17g; cutoff=%.17g; total count=20 >= 15.\n", actual[1], cutoff))

# A nearby positive control also exercises the same artifact and bridge.
stopifnot(identical(filterByExpr(matrix(c(20,20),1,2), lib.size=lib), TRUE))
cat("All R assertions and their unchanged-artifact CPM checks passed.\n")
