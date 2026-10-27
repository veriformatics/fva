# Execute the shipped R sources directly, without requiring the edgeR package.
source('edgeR/R/normLibSizes.R')
source('edgeR/R/calcNormFactors.R')
x <- as.matrix(read.table('counts.tsv', sep='\t'))
f <- normLibSizes(x, method='TMM')
stopifnot(identical(charToRaw(paste0(paste(sprintf('%.17g', f), collapse='\n'), '\n')),
                    readBin('edger-factors.txt', 'raw', n=file.info('edger-factors.txt')$size)))
lib <- colSums(x)
x <- x[rowSums(x)>0,,drop=FALSE]
f75 <- .calcFactorQuantile(x, lib)
j <- which.min(abs(f75-mean(f75)))
stopifnot(j == 4L)
for(i in seq_len(ncol(x))) {
  m <- log2((x[,i]/lib[i])/(x[,j]/lib[j]))
  a <- (log2(x[,i]/lib[i])+log2(x[,j]/lib[j]))/2
  fin <- is.finite(m)&is.finite(a)&a > -1e10
  n <- sum(fin)
  k <- rank(m[fin])>=floor(n*.3)+1 & rank(m[fin])<=n-floor(n*.3) &
       rank(a[fin])>=floor(n*.05)+1 & rank(a[fin])<=n-floor(n*.05)
  cat(paste(which(fin)[k]-1L, collapse=','), '\n', sep='')
}
