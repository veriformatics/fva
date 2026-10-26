# Run the two shipped R files unmodified. The missing package/native-R-Wasm
# integration is replaced ONLY at makeCompressedMatrix and .Call, for one
# checked fixture. The .Call result is transported from the ORIGINAL Wasm.
args <- commandArgs(trailingOnly=TRUE)
stopifnot(length(args) == 1L)
wasm.cpm <- matrix(scan(args[[1]], quiet=TRUE), nrow=2L, ncol=2L)
y <- matrix(c(10,8,10,8), nrow=2L, ncol=2L)
libs <- c(18,18)
e <- globalenv()
sys.source("R/cpm.R", envir=e)
sys.source("R/filterByExpr.R", envir=e)

# An explicit descriptor for the sole compressed-matrix case exercised.
# There is no replacement CPM arithmetic in this adapter.
e$makeCompressedMatrix <- function(x, dims, byrow) {
    stopifnot(identical(x, libs), identical(dims, dim(y)), identical(byrow, TRUE))
    list(data=x, dims=dims, byrow=byrow)
}
e$.cxx_calculate_cpm_raw <- "original-Wasm-fixture"
calls <- 0L
e$.Call <- function(symbol, counts, libraries, nthreads) {
    stopifnot(identical(symbol, "original-Wasm-fixture"), identical(counts, y),
              identical(libraries, list(data=libs, dims=dim(y), byrow=TRUE)),
              identical(nthreads, 1L))
    calls <<- calls + 1L
    wasm.cpm
}

actual.cpm <- e$cpm(y, lib.size=libs)
cutoff <- 10/median(libs)*1e6
stopifnot(identical(actual.cpm, wasm.cpm),
          identical(sprintf("%a", actual.cpm[1,1]), "0x1.0f4471c71c71cp+19"),
          identical(sprintf("%a", cutoff), "0x1.0f4471c71c71dp+19"),
          all(actual.cpm[1,] < cutoff))
# Two samples in one group: required size = 2; default min.total.count=15.
actual <- suppressMessages(e$filterByExpr(y, lib.size=libs))
# In exact arithmetic, equal L and median(L) cancel from both CPM expressions.
# Thus the documented threshold is exactly count >= 10 here.
expected <- rowSums(y >= 10) >= ncol(y) & rowSums(y) >= 15
stopifnot(identical(actual, c(FALSE,FALSE)), identical(expected, c(TRUE,FALSE)),
          all(y[1,] == 10), sum(y[1,]) == 20, all(colSums(y) == libs))
# Controls: the same real Wasm output crosses lower cutoffs as expected.
stopifnot(identical(suppressMessages(e$filterByExpr(y, lib.size=libs, min.count=9)),
                    c(TRUE,FALSE)),
          identical(suppressMessages(e$filterByExpr(y, lib.size=libs, min.count=8)),
                    c(TRUE,TRUE)), calls == 4L)
cat(sprintf("R2 boundary: artifact CPM=%.17g; R cutoff=%.17g\n",
            actual.cpm[1,1], cutoff))
cat("Shipped R wrapper/filter with checked Wasm-result adapter: PASS\n")
cat("R2 documented decision: TRUE,FALSE; actual decision: FALSE,FALSE\n")
