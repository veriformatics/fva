# Executes the shipped edgeR implementation, without writing its artifact.
source("edgeR/R/calcNormFactors.R")
source("edgeR/R/normLibSizes.R")
x <- as.matrix(read.table("counts.tsv", sep="\t"))
actual <- normLibSizes(x, method="TMM")
actual.bytes <- charToRaw(paste0(paste(sprintf("%.17g", actual), collapse="\n"), "\n"))
expected.bytes <- readBin("edger-factors.txt", "raw", n=file.info("edger-factors.txt")$size)
stopifnot(identical(actual.bytes, expected.bytes))
cat("PASS: shipped edgeR source reproduces edger-factors.txt byte for byte\n")

# Diagnose the two A-value evaluations with everything else held fixed.
ref <- 4L
j <- 1L
lib <- colSums(x)
o <- x[,j]; r <- x[,ref]
m <- log2((o/lib[j])/(r/lib[ref]))
a.sum <- (log2(o/lib[j]) + log2(r/lib[ref])) / 2
a.product <- log2((o/lib[j])*(r/lib[ref])) / 2
finite <- is.finite(m) & is.finite(a.sum)
keep <- function(a) {
  z <- which(finite)
  n <- length(z)
  rm <- rank(m[z]); ra <- rank(a[z])
  z[rm >= floor(n*.3)+1 & rm <= n-floor(n*.3) &
    ra >= floor(n*.05)+1 & ra <= n-floor(n*.05)]
}
cat("Diagnostic, sample 1: A-sum keeps", length(keep(a.sum)),
    "; A-product keeps", length(keep(a.product)), "genes\n")
cat("Changed gene rows:", setdiff(keep(a.sum), keep(a.product)), "\n")
