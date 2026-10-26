# Run the shipped R sources. Bridge their unavailable package dependencies to
# calc_cpm_raw in the original Wasm; do not reimplement the filtering function.
e <- globalenv() # S3 dispatch locates the sourced methods in the global environment.
sys.source('R/cpm.R', envir=e)
sys.source('R/filterByExpr.R', envir=e)
e$makeCompressedMatrix <- function(x, dims, byrow) {
    stopifnot(byrow, length(x) == dims[2])
    list(sizes=x, dims=dims)
}
e$.cxx_calculate_cpm_raw <- 'original-wasm-raw'
e$.Call <- function(symbol, y, lib.size, nthreads) {
    stopifnot(identical(symbol, 'original-wasm-raw'), nthreads == 1L,
              identical(dim(y), lib.size$dims))
    path <- tempfile()
    on.exit(unlink(path))
    con <- file(path, 'wb')
    writeBin(as.integer(dim(y)), con, size=4, endian='little')
    writeBin(as.double(y), con, size=8, endian='little')
    writeBin(as.double(lib.size$sizes), con, size=8, endian='little')
    close(con)
    lines <- system2('node', c('verification/wasm.cjs', '--matrix', shQuote(path)),
                     stdout=TRUE)
    stopifnot(is.null(attr(lines, 'status')))
    matrix(scan(text=paste(lines, collapse='\n'), quiet=TRUE), nrow=nrow(y))
}

# All-default integer-count witness, with library sizes equal to column sums.
# Each column totals 18; the first gene reaches min.count=10 in both samples.
y <- matrix(c(10,8,10,8), 2, 2)
cpms <- e$cpm(y)
cutoff <- 10 / median(colSums(y)) * 1e6
got <- e$filterByExpr(y)
stopifnot(identical(colSums(y), c(18,18)),
          all(y[1,] >= 10), sum(y[1,]) >= 15,
          all(cpms[1,] == 1193046471111111 / 2^31),
          cutoff == 4772185884444445 / 2^33,
          all(cpms[1,] < cutoff), identical(unname(got[1]), FALSE))
cat(sprintf('R2 FAIL (integer counts, all defaults): y rows=[10,10],[8,8]; L=[18,18]; first gene total=20; CPM=%.17g < cutoff=%.17g; keep=FALSE\n', cpms[1,1], cutoff))

# Literal README R2: the expression condition is true, but total count vetoes it.
y <- matrix(10, 1, 1)
cpms <- e$cpm(y, lib.size=1e6)
got <- e$filterByExpr(y, lib.size=1e6, min.sample.size=1)
stopifnot(identical(unname(cpms), matrix(10,1,1)),
          sum(cpms >= 10) == 1, sum(y) == 10, identical(unname(got), FALSE))
cat('R2 FAIL (literal README): y=[10], L=[1000000], required=1, min.count=10; expression=TRUE, keep=FALSE (total 10 < 15)\n')

# Also fails an exact sample-number iff even when the documented total passes.
y <- matrix(c(20, 0), 1, 2)
required <- 1 + 2^-50
cpms <- e$cpm(y, lib.size=c(1e6,1e6))
got <- e$filterByExpr(y, lib.size=c(1e6,1e6), min.sample.size=required)
stopifnot(identical(unname(cpms), matrix(c(20,0),1,2)),
          sum(y) >= 15, sum(cpms >= 10) == 1, 1 < required,
          1e-14 == 6338253001141147 / 2^99,
          required - 1e-14 == 4503599627370455 / 2^52,
          1 >= required - 1e-14, identical(unname(got), TRUE))
cat(sprintf('R2 FAIL (exact documented sample condition): y=[20,0], L=[1000000,1000000], min.sample.size=%.17g; qualifying=1, total=20; exact condition=FALSE, keep=TRUE\n', required))
cat('PASS: shipped R sources with original Wasm CPM; all three R2 counterexample assertions\n')
