# Concrete R/Wasm bridge for the two checked matrices, not an edgeR installation.
args <- commandArgs(trailingOnly=TRUE)
stopifnot(length(args) == 1L)
source("R/cpm.R")
source("R/filterByExpr.R")
wasm.boundary <- readBin(args[[1L]], "double", n=2L, size=8L, endian="little")
stopifnot(length(wasm.boundary) == 2L)

# This missing package helper represents a repeated library-size row. The .Call
# adapter below checks its entire input and supplies only Wasm-checked results.
makeCompressedMatrix <- function(x, dims, byrow) {
    stopifnot(byrow, length(x) == dims[[2L]])
    matrix(x, nrow=dims[[1L]], ncol=dims[[2L]], byrow=TRUE)
}
.cxx_calculate_cpm_raw <- "checked-Wasm-calc_cpm_raw"
calls <- 0L
.Call <- function(symbol, y, lib.size, nthreads) {
    stopifnot(identical(symbol, .cxx_calculate_cpm_raw), nthreads == 1L,
              all(y == 10), nrow(y) == 1L)
    calls <<- calls + 1L
    if (identical(dim(y), c(1L, 2L)) && all(lib.size == 1000009)) {
        return(matrix(wasm.boundary, 1L, 2L))
    }
    if (identical(dim(y), c(1L, 1L)) && all(lib.size == 1000000)) {
        return(matrix(10, 1L, 1L))
    }
    stop("input not covered by the Wasm assertions")
}

# R2 counterexample even after including the documentation's total-count test.
# All parameters omitted below have their shipped defaults.
y <- matrix(c(10,10), nrow=1L)
L <- c(1000009,1000009)
actual.cpm <- cpm(y, lib.size=L)
cutoff <- 10/median(L)*1e6
stopifnot(identical(10/median(L), 0x1.4f8a92a52c5d4p-17),
          identical(cutoff, 0x1.3fff43420d832p+3))
documented <- rowSums(y / matrix(L,1L,2L) * median(L) >= 10) >= 2 & rowSums(y) >= 15
keep <- filterByExpr(y, lib.size=L, min.sample.size=2)
stopifnot(all(y == 10), all(y == 10 * L / median(L)),
          identical(documented, TRUE), identical(keep, FALSE),
          all(actual.cpm < cutoff), sum(y) == 20)
stopifnot(identical(writeBin(as.double(actual.cpm), raw(), size=8L, endian="little"),
                    readBin(args[[1L]], "raw", n=16L)))
cat(sprintf("R2 boundary: CPM=%.17g < cutoff=%.17g; documented=TRUE; actual=FALSE; total=20 >= 15\n",
            actual.cpm[1L], cutoff))

# Literal README iff also omits the independent total-count condition.
y <- matrix(10, nrow=1L)
keep <- filterByExpr(y, lib.size=1000000, min.sample.size=1)
stopifnot(identical(keep, FALSE), 10 >= 10, 10 < 15, calls == 3L)
cat("R2 literal iff: one count 10, L=1000000, required samples=1: CPM passes, total fails, keep=FALSE\n")
