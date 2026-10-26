# Load both shipped R files unchanged. Supply only the missing package helpers
# for this plain-double-matrix, row-vector-lib.size, log=FALSE path.
source("R/cpm.R")
source("R/filterByExpr.R")
makeCompressedMatrix <- function(x, dims, byrow) {
    stopifnot(is.double(x), length(x) == dims[2], byrow)
    x
}
.cxx_calculate_cpm_raw <- "artifact.calc_cpm_raw"
.Call <- function(symbol, y, lib.size, nthreads) {
    stopifnot(identical(symbol, .cxx_calculate_cpm_raw), nthreads == 1L)
    input <- tempfile(); output <- tempfile()
    on.exit(unlink(c(input, output)))
    writeBin(c(as.double(y), lib.size), input, size=8, endian="little")
    status <- system2("node", c("verify/runtime.mjs", nrow(y), ncol(y), input, output))
    stopifnot(status == 0)
    matrix(readBin(output, "double", n=length(y), size=8, endian="little"), nrow(y), ncol(y))
}
# R2: equal count and min.count, one required sample, sufficient total count.
y <- matrix(c(20, 16), ncol=1)
libs <- colSums(y) # 36, the default library size
observed <- cpm(y, lib.size=libs)
cutoff <- 20/median(libs)*1e6
bits <- function(x) paste(sprintf("%02x", as.integer(rev(writeBin(as.double(x), raw(),
                           size=8, endian="little")))), collapse="")
stopifnot(bits(observed[1]) == "4120f4471c71c71c", bits(cutoff) == "4120f4471c71c71d")
keep <- filterByExpr(y, min.count=20)
stopifnot(libs == 36, observed[1] < cutoff, identical(keep, c(FALSE,FALSE)))
stopifnot(y[1] >= 20, sum(y[1,]) >= 15, ncol(y) == 1)
cat(sprintf("R2 boundary: CPM=%.17g cutoff=%.17g keep=%s (expected TRUE for first gene)\n",
            observed[1], cutoff, keep[1]))
# Even with well-separated CPM values, tolerance changes the exact sample rule.
y <- matrix(c(20, 0), nrow=1)
required <- 1 + 2^-50
keep <- filterByExpr(y, lib.size=c(1e6,1e6), min.sample.size=required)
stopifnot(required > 1, sum(cpm(y, lib.size=c(1e6,1e6)) >= 10) == 1, identical(keep, TRUE))
cat(sprintf("R2 tolerance: qualifying=1 required=%.17g keep=%s (exact rule FALSE)\n", required, keep))
