# Execute shipped filtering code. The cpm adapter returns ONLY the table
# checked cell by cell against the original wasm by build_witness.py.
source("R/filterByExpr.R")
y.boundary <- matrix(c(10,26,10,26), nrow=2)
artifact.cpm <- dget("verification/artifact_cpm.R")
cpm <- function(y, lib.size) {
    if (identical(y, matrix(10,1,1)) && identical(lib.size,10^6))
        return(matrix(10,1,1)) # independently checked first WAST invocation
    stopifnot(identical(y,y.boundary), identical(lib.size,c(36,36)))
    artifact.cpm
}

# Literal iff in R2 fails because of the documented extra total-count test.
y <- matrix(10,1,1)
keep <- filterByExpr(y,lib.size=10^6,min.sample.size=1)
stopifnot(identical(keep,FALSE))
cat("PASS: sample condition true, total count 10 < 15, filter returns FALSE\n")

# A rounding failure even when total count and all other documented rules hold.
cutoff <- 10 / median(colSums(y.boundary)) * 1e6
stopifnot(identical(artifact.cpm[1,1],0x1.0f4471c71c71cp+18),
          identical(cutoff,0x1.0f4471c71c71dp+18),
          all(y.boundary[1,] >= 10), sum(y.boundary[1,]) >= 15,
          all(artifact.cpm[1,] < cutoff))
keep <- filterByExpr(y.boundary)
stopifnot(identical(keep,c(FALSE,TRUE)))
cat(sprintf("PASS: c=10, L=36: CPM=%.17g < cutoff=%.17g; two qualifying counts, total=20, filter returns FALSE\n",artifact.cpm[1,1],cutoff))
