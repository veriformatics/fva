# Run both shipped R files. Only the unavailable R-to-Wasm bridge is supplied.
args <- commandArgs(trailingOnly=TRUE)
stopifnot(length(args) == 1L)
bridge <- globalenv()
sys.source("R/cpm.R", envir=bridge)
sys.source("R/filterByExpr.R", envir=bridge)
bridge$.cxx_calculate_cpm_raw <- "verified-raw-bridge"
bridge$makeCompressedMatrix <- function(x, dims, byrow) {
    stopifnot(isTRUE(byrow), length(x) == dims[2])
    list(libraries=x, dims=dims)
}
bridge$.Call <- function(symbol, y, lib.size, nthreads) {
    stopifnot(identical(symbol, "verified-raw-bridge"), nthreads == 1L,
              identical(dim(y), lib.size$dims))
    if (identical(y, matrix(c(10,26,10,26), 2, 2)) &&
        identical(lib.size$libraries, c(36,36))) {
        name <- "boundary"
    } else if (identical(y, matrix(c(20,0), 1, 2)) &&
               identical(lib.size$libraries, c(1e6,1e6))) {
        name <- "tolerance"
    } else stop("input was not executed by the Wasm harness")
    con <- file(file.path(args[1], paste0(name,".bin")), "rb")
    on.exit(close(con))
    values <- readBin(con, "double", n=length(y), size=8, endian="little")
    stopifnot(length(values) == length(y))
    matrix(values, nrow(y), ncol(y))
}

# Ordinary integer counts, default tuning, column sums exactly equal lib.size.
y <- matrix(c(10,26,10,26), 2, 2)
libs <- colSums(y)
stopifnot(identical(libs, c(36,36)))
actual <- bridge$cpm(y, lib.size=libs)
cutoff <- 10/median(libs)*1e6
keep <- bridge$filterByExpr(y, group=c("a","a"))
stopifnot(identical(keep, c(FALSE,TRUE)),
          all(y[1,] >= 10), sum(y[1,]) >= 15,
          all(actual[1,] < cutoff),
          identical(actual[1,1], 1193046471111111/4294967296),
          identical(cutoff, 4772185884444445/17179869184))
cat(sprintf("R2 count-boundary witness: CPM=%a, cutoff=%a, keep=(FALSE,TRUE)\n",
            actual[1,1], cutoff))

# The documented CPM rule itself fails here, independently of count scaling.
y <- matrix(c(20,0), 1, 2)
libs <- c(1e6,1e6)
required <- 1 + 2^-50
actual <- bridge$cpm(y, lib.size=libs)
qualifying <- rowSums(actual >= 10/median(libs)*1e6)
documented <- qualifying >= required & rowSums(y) >= 15
keep <- bridge$filterByExpr(y, lib.size=libs, min.sample.size=required)
stopifnot(required > 1, qualifying == 1, identical(documented, FALSE),
          identical(keep, TRUE), qualifying >= required - 1e-14)
cat(sprintf("R2 sample-tolerance FAIL witness checked: required=%a, qualifying=1, documented=FALSE, actual=TRUE\n",
            required))
