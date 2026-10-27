# Execute the shipped edgeR functions; never write the shipped artifacts.
source("edgeR/R/calcNormFactors.R")
source("edgeR/R/normLibSizes.R")
m <- as.matrix(read.table("counts.tsv", sep="\t"))
stopifnot(identical(dim(m), c(454L, 7L)), all(m >= 0), all(m == floor(m)))
f <- normLibSizes(m, method="TMM")
expected <- scan("edger-factors.txt", quiet=TRUE)
stopifnot(length(expected) == 7L, all(is.finite(f)), max(abs(f-expected)) <= 1e-12)
bytes <- charToRaw(paste0(paste(sprintf("%.17g", f), collapse="\n"), "\n"))
stopifnot(identical(bytes, readBin("edger-factors.txt", "raw", file.info("edger-factors.txt")$size)))
f75 <- .calcFactorQuantile(m, colSums(m))
stopifnot(which.min(abs(f75-mean(f75))) == 4L)
cat(sprintf("R1 runtime reproduction: 7/7, max absolute error %.17g, exact file bytes\n", max(abs(f-expected))))
# Trace a COPY of the shipped TMM function to expose its actual retained rows.
calc <- .calcFactorTMM
capture <- function() {
  trace("calc", exit=quote({
    if (exists("keep", inherits=FALSE)) retained <<- which(fin)[keep]
  }), print=FALSE, where=environment())
  calc(obs=m[,1], ref=m[,4], libsize.obs=sum(m[,1]), libsize.ref=sum(m[,4]))
}
retained <- integer()
invisible(capture())
writeLines(paste(retained, collapse=" "), ".verification-build/edge-retained.txt")
cat("edgeR sample 1 retained rows:", paste(retained, collapse=" "), "\n")
