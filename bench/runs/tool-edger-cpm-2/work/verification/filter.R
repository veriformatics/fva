# Execute the supplied R code, using the shipped Wasm for its raw-CPM call.
# The full edgeR/R-Wasm host is absent, so makeCompressedMatrix and .Call
# below implement only the raw path exercised by these concrete witnesses.
source("R/cpm.R")
source("R/filterByExpr.R")
makeCompressedMatrix <- function(x, dims, byrow) {
    stopifnot(isTRUE(byrow), length(dims) == 2L,
              length(x) == dims[2L], all(is.finite(x)), all(x > 0))
    x
}
.cxx_calculate_cpm_raw <- "raw-cpm-wasm-bridge"
.Call <- function(symbol, y, lib.size, nthreads) {
    stopifnot(identical(symbol, .cxx_calculate_cpm_raw), nthreads == 1L,
              is.matrix(y), all(is.finite(y)))
    args <- c("verification/artifact.mjs", "--cpm", nrow(y), ncol(y),
              sprintf("%.17g", as.vector(y)), sprintf("%.17g", lib.size))
    answer <- system2("node", args, stdout=TRUE)
    stopifnot(is.null(attr(answer,"status")))
    matrix(as.numeric(answer), nrow=nrow(y), ncol=ncol(y))
}

# Complete defaults except for the explicitly supplied group and libraries.
y <- matrix(c(10,10), nrow=1)
libraries <- c(18,18)
cutoff <- 10 / median(libraries) * 1e6
actual.cpm <- cpm(y, lib.size=libraries)
actual <- filterByExpr(y, group=c("A","A"), lib.size=libraries)
# Documented scaled count condition, plus the documented total-count gate.
documented <- rowSums(sweep(y, 2, libraries/median(libraries), "/") >= 10) >= 2 &
              rowSums(y) >= 15
stopifnot(identical(as.vector(actual), FALSE), identical(as.vector(documented), TRUE),
          all(actual.cpm < cutoff), sum(y) == 20)
cat(sprintf("R2: CPM=%.17g; cutoff=%.17g; actual=FALSE; documented=TRUE; total=20 >= 15\n",
            actual.cpm[1], cutoff))
cat("R FILTER COUNTEREXAMPLE PASS\n")
