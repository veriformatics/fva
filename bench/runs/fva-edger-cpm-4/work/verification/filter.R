# Execute the shipped filter, with its raw CPM dependency provided by edgeR.so.
source('R/filterByExpr.R')
cpm <- function(y, lib.size) {
  request <- sprintf('{"counts":[%s],"libraries":[%s],"nrow":%d}',
    paste(sprintf('%.17g', as.numeric(y)), collapse=','),
    paste(sprintf('%.17g', as.numeric(lib.size)), collapse=','), nrow(y))
  input <- tempfile()
  on.exit(unlink(input))
  writeLines(request, input)
  result <- system2('node', c('verification/artifact.cjs', 'cpm'), stdin=input, stdout=TRUE)
  stopifnot(is.null(attr(result, 'status')))
  matrix(scan(text=result, quiet=TRUE), nrow=nrow(y))
}
y <- matrix(10, 1, 1)
L <- 1e6
cutoff <- 10 / median(L) * 1e6
required <- 1
passes.sample.rule <- rowSums(cpm(y, L) >= cutoff) >= required
actual <- filterByExpr.default(y, lib.size=L, min.sample.size=required)
stopifnot(identical(passes.sample.rule, TRUE), identical(actual, FALSE))
cat('R2 counterexample: y=[10], lib.size=[1000000], min.sample.size=1, defaults otherwise.\n')
cat('Sample/CPM criterion=TRUE; shipped filter=FALSE (total count 10 < 15 - 1e-14).\n')
stopifnot(identical(filterByExpr.default(y, lib.size=L,
  min.sample.size=required, min.total.count=0), TRUE))
cat('Control: min.total.count=0 makes the same gene pass.\n')

# A second witness keeps the documented total-count condition satisfied.
# The implementation's undocumented tolerance changes an exact sample cutoff.
y <- matrix(c(15, 0), 1, 2)
L <- c(1e6, 1e6)
required <- 1 + 2^-48
hits <- rowSums(cpm(y, L) >= 10)
actual <- filterByExpr.default(y, lib.size=L, min.sample.size=required)
stopifnot(hits == 1, hits < required, sum(y) >= 15, identical(actual, TRUE))
cat(sprintf('R2 tolerance witness: y=[15,0], L=[1e6,1e6], required=%.17g; hits=1; total=15; filter=TRUE.\n', required))
