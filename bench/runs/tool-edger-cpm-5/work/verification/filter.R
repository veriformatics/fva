# Run the unmodified shipped R function with CPM values from the original wasm.
source('R/filterByExpr.R')
source('R/cpm.R')
y <- matrix(c(10,8,10,8), nrow=2)
wasm.cpm <- as.matrix(read.csv('verification/cpm.csv', check.names=FALSE))
stopifnot(identical(dim(wasm.cpm),dim(y)))
# Fixture bridge for edgeR helpers absent from this source subset/native R.
# The .Call result is measured by artifact.cjs, not recomputed here.
makeCompressedMatrix <- function(x, dims, byrow) {
    stopifnot(identical(unname(x),c(18,18)),
              identical(dims,c(2L,2L)), identical(byrow,TRUE))
    x
}
.cxx_calculate_cpm_raw <- 'wasm-raw-fixture'
.Call <- function(symbol, y, lib.size, nthreads) {
    stopifnot(identical(symbol,.cxx_calculate_cpm_raw),
              identical(unname(y),matrix(c(10,8,10,8),nrow=2)),
              identical(unname(lib.size),c(18,18)), identical(nthreads,1L))
    wasm.cpm
}
actual <- filterByExpr(y)
# All libraries equal the median, so documented min.count=10 means count>=10.
expected <- rowSums(y >= 10) >= 2 & rowSums(y) >= 15
stopifnot(identical(actual,c(FALSE,FALSE)),
          identical(expected,c(TRUE,FALSE)), !identical(actual,expected))
cutoff <- 10/median(colSums(y))*1e6
stopifnot(wasm.cpm[1,1] < cutoff,
          sum(y[1,]) >= 15,
          all(y[1,] >= 10))
cat(sprintf('R2: actual=%s; documented count criterion=%s\n',
            paste(actual,collapse=','),paste(expected,collapse=',')))
cat(sprintf('CPM=%.17g; cutoff=%.17g; gene 1 total=20 >= 15\n',
            wasm.cpm[1,1],cutoff))
cat('Shipped R checks passed\n')
