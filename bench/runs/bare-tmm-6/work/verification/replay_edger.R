# Runtime replay only; no installed edgeR package is needed.
source('edgeR/R/calcNormFactors.R')
source('edgeR/R/normLibSizes.R')
m <- as.matrix(read.table('counts.tsv', sep='\t'))
f <- normLibSizes(m, method='TMM')
actual <- charToRaw(paste0(paste(sprintf('%.17g', f), collapse='\n'), '\n'))
expected <- readBin('edger-factors.txt', 'raw', n=file.info('edger-factors.txt')$size)
stopifnot(identical(actual, expected))
cat('edgeR source replay, exact output bytes: PASS\n')
# A concrete boundary tie in the first comparison (1-based input row numbers).
pos <- m[,1] > 0 & m[,4] > 0
a <- m[pos,1]/sum(m[,1]); b <- m[pos,4]/sum(m[,4])
a_sum <- (log2(a)+log2(b))/2
a_product <- log2(a*b)/2
rows <- which(pos)
i <- match(c(163,355),rows)
stopifnot(identical(as.integer(m[c(163,355),1]*m[c(163,355),4]),c(104L,104L)))
cat('Rows 163,355: sum-of-logs A ranks =', rank(a_sum)[i],
    '; log-of-product A ranks =', rank(a_product)[i], '\n')
