args <- commandArgs(trailingOnly=TRUE)
values <- read.delim(args[1], check.names=FALSE)
stopifnot(identical(values$count, c(10L,20L)),
          identical(values$library, c(1000000L,1000000L)))
y <- matrix(as.double(values$count[1]), ncol=1L)
control <- matrix(as.double(values$count[2]), ncol=1L)

# Run both supplied R files unchanged. The standalone WASM binary cannot be
# loaded into native R. These adapters supply the missing package plumbing,
# and return CPM values already obtained from its actual calc_cpm_raw export.
source("R/cpm.R")
source("R/filterByExpr.R")
makeCompressedMatrix <- function(x, dims, byrow) {
    stopifnot(identical(x, 1e6), identical(dims, c(1L,1L)), identical(byrow, TRUE))
    x
}
.cxx_calculate_cpm_raw <- "verified-WASM-bridge"
.Call <- function(symbol, counts, libraries, nthreads) {
    stopifnot(identical(symbol, "verified-WASM-bridge"),
              identical(counts, y) || identical(counts, control),
              identical(libraries, 1e6), identical(nthreads, 1L))
    matrix(values$cpm[match(as.double(counts), values$count)], ncol=1L)
}

cpm.values <- cpm(y, lib.size=1e6)
cutoff <- 10 / median(1e6) * 1e6
qualified <- rowSums(cpm.values >= cutoff)
kept <- filterByExpr(y, lib.size=1e6, min.sample.size=1)
without.total <- filterByExpr(y, lib.size=1e6, min.sample.size=1, min.total.count=0)
control.kept <- filterByExpr(control, lib.size=1e6, min.sample.size=1)
stopifnot(identical(as.double(cpm.values), 10), identical(cutoff, 10),
          identical(as.double(qualified), 1), identical(kept, FALSE),
          identical(without.total, TRUE), identical(control.kept, TRUE))
write.table(data.frame(count=values$count[1], qualified=qualified, required=1,
                       kept=as.integer(kept), without.total=as.integer(without.total)),
            args[2], sep="\t", row.names=FALSE, quote=FALSE)
cat("R2: count=10, library=1000000, min.count=10, required=1, qualified=1, kept=FALSE\n")
cat("R2 control: min.total.count=0 keeps it; count=20 passes default filtering\n")
