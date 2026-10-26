# Run the shipped R functions. Only the absent R-to-Wasm .Call bridge is supplied.
source('R/cpm.R')
source('R/filterByExpr.R')
makeCompressedMatrix <- function(x, dims, byrow) {
    stopifnot(is.double(x), length(x) == dims[2], byrow)
    x
}
.cxx_calculate_cpm_raw <- 'raw'
.Call <- function(symbol, y, lib.size, nthreads) {
    stopifnot(identical(symbol, 'raw'), nthreads == 1L)
    # Counts are serialized in R's column-major order; 17 digits preserve binary64.
    fmt <- function(x) paste(sprintf('%.17g', x), collapse=',')
    input <- sprintf('{"counts":[%s],"libs":[%s],"nr":%d,"nc":%d}',
                     fmt(y), fmt(lib.size), nrow(y), ncol(y))
    values <- system2('node', c('verification/run-wasm.js', '--matrix'),
                      input=input, stdout=TRUE)
    stopifnot(is.null(attr(values, 'status')))
    matrix(as.numeric(values), nrow(y), ncol(y))
}
y <- matrix(c(10, 10), nrow=1)
lib <- c(18, 18)
actual <- filterByExpr(y, lib.size=lib, min.sample.size=2)
scaled.count <- y / matrix(lib / median(lib), nrow=1)
expected <- rowSums(scaled.count >= 10) >= 2 & rowSums(y) >= 15
stopifnot(identical(actual, FALSE), identical(expected, TRUE))
cpms <- cpm(y, lib.size=lib)
cutoff <- 10 / median(lib) * 1e6
stopifnot(all(cpms < cutoff), all(y == 10), sum(y) == 20)
cat(sprintf('R2: counts=(10,10), libraries=(18,18), required samples=2, total=20\n'))
cat(sprintf('CPM=%.17g; cutoff=%.17g; gap=%.17g\n', cpms[1], cutoff, cutoff-cpms[1]))
cat('actual keep=FALSE; documented threshold predicate=TRUE\n')
# Also expose the separate extra-total-count condition omitted by literal R2.
literal <- filterByExpr(matrix(10, 1, 1), lib.size=1e6, min.sample.size=1)
stopifnot(identical(literal, FALSE))
cat('Literal R2 also omits min.total.count: count=10, library=1e6 is rejected.\n')
cat('R COUNTEREXAMPLES PASS\n')
