# Supplemental runtime check; the formal certificates do not depend on R.
source("edgeR/R/calcNormFactors.R")
source("edgeR/R/normLibSizes.R")
m <- as.matrix(read.table("counts.tsv", sep="\t"))
computed <- charToRaw(paste0(paste(sprintf("%.17g", normLibSizes(m, method="TMM")),
                               collapse="\n"), "\n"))
shipped <- readBin("edger-factors.txt", "raw", n=file.info("edger-factors.txt")$size)
stopifnot(identical(computed, shipped))
cat("edgeR runtime reproduction: exact output bytes match\n")
