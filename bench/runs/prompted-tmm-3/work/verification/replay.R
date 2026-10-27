# Diagnostic only: execute the unmodified shipped R source, without edgeR installed.
source("edgeR/R/calcNormFactors.R")
source("edgeR/R/normLibSizes.R")
m <- as.matrix(read.table("counts.tsv", sep="\t"))
got <- charToRaw(paste0(paste(sprintf("%.17g", normLibSizes(m, method="TMM")), collapse="\n"), "\n"))
stopifnot(identical(got, readBin("edger-factors.txt", "raw", file.info("edger-factors.txt")$size)))
cat("R floating-point replay matches edger-factors.txt byte for byte\n")
