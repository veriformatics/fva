# Execute both shipped R sources, supplying only the missing package/FFI pieces
# needed for plain numeric matrices, vector library sizes, and log=FALSE.
source("R/cpm.R")
source("R/filterByExpr.R")

makeCompressedMatrix <- function(x, dims, byrow) {
    stopifnot(is.double(x), length(x) == dims[2L], isTRUE(byrow))
    x
}
.cxx_calculate_cpm_raw <- "artifact.calc_cpm_raw"
.Call <- function(symbol, y, lib.size, nthreads) {
    stopifnot(identical(symbol, .cxx_calculate_cpm_raw),
              is.matrix(y), is.numeric(y), identical(nthreads, 1L))
    args <- c("verification/artifact.mjs", "cpm", nrow(y), ncol(y),
              sprintf("%.17g", as.double(y)), sprintf("%.17g", lib.size))
    output <- system2("node", args, stdout=TRUE)
    stopifnot(is.null(attr(output, "status")), length(output) == length(y))
    result <- as.double(output)
    stopifnot(!anyNA(result))
    matrix(result, nrow=nrow(y), ncol=ncol(y))
}

# Literal R2 equivalence fails: the sample criterion passes, but total count fails.
y <- matrix(10, 1L, 1L)
libs <- 1000000
cpms <- cpm(y, lib.size=libs)
stopifnot(identical(as.vector(cpms), 10))
actual <- filterByExpr(y, lib.size=libs, min.sample.size=1)
sample.criterion <- rowSums(cpms >= 10 / median(libs) * 1e6) >= 1
stopifnot(identical(unname(sample.criterion), TRUE), identical(unname(actual), FALSE))
cat("R2 total-count witness: y=[10], L=[1000000], required=1; sample criterion TRUE, result FALSE\n")

# Even when the documented total-count requirement passes, evaluation order
# places the CPM and its cutoff one ULP apart at the same mathematical boundary.
y <- matrix(c(10, 8, 10, 8), 2L, 2L)
libs <- colSums(y) # c(18,18), exactly the default library sizes
cpms <- cpm(y, lib.size=libs)
cutoff <- 10 / median(libs) * 1e6
actual <- filterByExpr(y) # all defaults, no group/design
stopifnot(all(y[1L, ] >= 10), rowSums(y)[1L] == 20,
          all(cpms[1L, ] < cutoff), identical(unname(actual), c(FALSE,FALSE)))
cat(sprintf("R2 boundary witness: y rows=[10,10];[8,8], L=[18,18], required=2; CPM=%.17g, cutoff=%.17g; first-row total=20; result FALSE\n",
            cpms[1], cutoff))

# Guard against attributing every rejection to the FFI: a normal accepted input.
stopifnot(isTRUE(unname(filterByExpr(matrix(c(11,11), 1L, 2L),
                                   lib.size=c(18,18)))))
cat("PASS: all shipped-R assertions (CPM supplied by the original WebAssembly)\n")
