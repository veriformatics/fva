# Execute the shipped edgeR functions, without writing either shipped factor file.
source('edgeR/R/normLibSizes.R')
source('edgeR/R/calcNormFactors.R')
x <- as.matrix(read.table('counts.tsv', sep='\t'))
f <- normLibSizes(x, method='TMM')
actual <- paste0(paste(sprintf('%.17g', f), collapse='\n'), '\n')
expected <- readBin('edger-factors.txt', 'raw', n=file.info('edger-factors.txt')$size)
stopifnot(identical(charToRaw(actual), expected))
cat('PASS: unmodified edgeR execution reproduces all artifact bytes\n')
