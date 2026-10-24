# Produces edger-factors.txt from counts.tsv (genes x samples) with edgeR 4.99.10.
suppressMessages(library(edgeR))
m <- as.matrix(read.table("counts.tsv", sep = "\t"))
f <- normLibSizes(m, method = "TMM")
writeLines(sprintf("%.17g", f), "edger-factors.txt")
