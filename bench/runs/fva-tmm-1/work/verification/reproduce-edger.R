# Supplemental runtime check, not a Lean proof of the R interpreter or libm.
source('edgeR/R/calcNormFactors.R')
source('edgeR/R/normLibSizes.R')
x <- as.matrix(read.table('counts.tsv', sep='\t'))
f <- normLibSizes(x, method='TMM')
actual <- paste0(paste(sprintf('%.17g', f), collapse='\n'), '\n')
expected <- readBin('edger-factors.txt', 'raw', n=file.info('edger-factors.txt')$size)
stopifnot(identical(charToRaw(actual), expected))
cat('edgeR: exact byte reproduction PASS\n')
q <- .calcFactorQuantile(x, colSums(x))
r <- which.min(abs(q-mean(q)))
cat('reference sample:', r, '\n')
for (j in seq_len(ncol(x))) {
    obs <- x[,j]; ref <- x[,r]; nO <- sum(obs); nR <- sum(ref)
    M <- log2((obs/nO)/(ref/nR)); A <- (log2(obs/nO)+log2(ref/nR))/2
    ok <- is.finite(M) & is.finite(A) & A > -1e10
    M <- M[ok]; A <- A[ok]; n <- length(M)
    keep <- rank(M)>=floor(n*.3)+1 & rank(M)<=n-floor(n*.3) &
            rank(A)>=floor(n*.05)+1 & rank(A)<=n-floor(n*.05)
    cat('sample', j, 'positive pairs', n, 'kept', sum(keep), '\n')
}
