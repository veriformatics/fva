# Run the shipped R implementations. Only the absent package infrastructure is
# supplied: compressed-matrix construction and the .Call bridge to original Wasm.
source("R/cpm.R")
source("R/filterByExpr.R")
makeCompressedMatrix <- function(x, dims, byrow) {
    stopifnot(byrow, length(x) == dims[2L])
    x
}
.cxx_calculate_cpm_raw <- "raw_wasm_bridge"
.Call <- function(symbol, y, lib.size, nthreads) {
    stopifnot(identical(symbol, "raw_wasm_bridge"), nthreads == 1L)
    stopifnot(nrow(y) %in% 1:2, ncol(y) %in% 1:2,
              length(lib.size) == ncol(y))
    counts <- c(as.vector(y), rep(0, 4 - length(y)))
    libs <- c(lib.size, rep(0, 2 - length(lib.size)))
    out <- y
    for (j in seq_len(ncol(y))) for (i in seq_len(nrow(y))) {
        args <- c("run", "-C", "cache=n",
          "--preload", "env=verification/generated/env.wasm",
          "--preload", "GOT.mem=verification/generated/GOT.mem.wasm",
          "--preload", "GOT.func=verification/generated/GOT.func.wasm",
          "--preload", "edgeR=edgeR.so", "--invoke", "matrix_entry",
          "verification/generated/driver.wasm",
          nrow(y), ncol(y), sprintf("%.17g", counts),
          sprintf("%.17g", libs), (j - 1L)*nrow(y) + i - 1L)
        err <- tempfile()
        text <- system2("wasmtime", args, stdout=TRUE, stderr=err)
        stopifnot(is.null(attr(text, "status")))
        unlink(err)
        out[i,j] <- as.numeric(text)
    }
    out
}

# R2 witness: count exactly min.count in both samples, total cutoff satisfied.
y <- matrix(c(10, 10, 8, 8), nrow=2, byrow=TRUE)
libs <- colSums(y)
cpm.actual <- cpm(y, lib.size=libs)
cutoff <- 10 / median(libs) * 1e6
keep <- filterByExpr(y)
stopifnot(identical(libs, c(18,18)), all(y[1,] >= 10), sum(y[1,]) >= 15,
          all(cpm.actual[1,] == 0x1.0f4471c71c71cp+19),
          cutoff == 0x1.0f4471c71c71dp+19,
          all(cpm.actual[1,] < cutoff), identical(keep, c(FALSE,FALSE)))
cat(sprintf("R2: cpm=%.17g, cutoff=%.17g, keep=%s; scaled-count rule expects TRUE\n",
            cpm.actual[1], cutoff, keep[1]))
cat("R2: all defaults, column-sum libraries 18,18; target row counts 10,10 dropped\n")

# Control: the same threshold counts pass with libraries 10,10.
y <- matrix(c(10, 10, 0, 0), nrow=2, byrow=TRUE)
stopifnot(identical(filterByExpr(y), c(TRUE,FALSE)))
cat("Control: target row counts 10,10 with libraries 10,10 is kept\n")
cat("PASS: shipped R functions executed with original calc_cpm_raw via Wasmtime\n")
