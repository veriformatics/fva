# Execute the shipped edgeR functions without installing or modifying edgeR.
source("edgeR/R/calcNormFactors.R")
source("edgeR/R/normLibSizes.R")
m <- as.matrix(read.table("counts.tsv", sep="\t"))
actual <- paste0(paste(sprintf("%.17g", normLibSizes(m, method="TMM")), collapse="\n"), "\n")
expected <- readBin("edger-factors.txt", "raw", file.info("edger-factors.txt")$size)
stopifnot(identical(charToRaw(actual), expected))
cat("Shipped edgeR source reproduces edger-factors.txt byte for byte\n")
