# Execute both shipped R files unchanged. Supply only the missing package
# helpers / foreign-function boundary for this ordinary double matrix input.
# The .Call adapter invokes the *original* Wasm calc_cpm_raw through Node.
scope <- globalenv()
sys.source("R/cpm.R", envir=scope)
sys.source("R/filterByExpr.R", envir=scope)

scope$makeCompressedMatrix <- function(x, dims, byrow) {
    stopifnot(is.double(x), length(dims) == 2L, isTRUE(byrow),
              length(x) == dims[2L], all(is.finite(x)), all(x > 0))
    # Type-2 cmx: a library-size row repeated over the genes.
    list(libs=x, dims=dims)
}
scope$.cxx_calculate_cpm_raw <- "verification.calc_cpm_raw"
scope$.Call <- function(symbol, y, lib.size, nthreads) {
    stopifnot(identical(symbol, "verification.calc_cpm_raw"),
              is.matrix(y), is.double(y),
              identical(dim(y), lib.size$dims), identical(nthreads, 1L))
    # 17 significant digits preserve every binary64 value on round trip.
    numbers <- function(x) paste(sprintf("%.17g", x), collapse=",")
    input <- sprintf('{"counts":[%s],"libs":[%s],"nrow":%d,"ncol":%d}',
                     numbers(as.vector(y)), numbers(lib.size$libs), nrow(y), ncol(y))
    output <- system2("node", c("verification/artifact.cjs", "--matrix"),
                      input=input, stdout=TRUE)
    stopifnot(is.null(attr(output, "status")), length(output) == 1L)
    values <- scan(text=gsub("[][]", "", output), sep=",", quiet=TRUE)
    stopifnot(length(values) == length(y))
    matrix(values, nrow=nrow(y), ncol=ncol(y))
}

bits <- function(x) paste(sprintf("%02x", as.integer(rev(writeBin(x, raw(), size=8L,
                                                              endian="little")))), collapse="")
y <- matrix(c(10, 10), nrow=1L)
libs <- c(1000009, 1000009)
CPM <- scope$cpm(y, lib.size=libs)
cutoff <- 10 / median(libs) * 1e6
stopifnot(identical(bits(CPM[1L]), "4023fff43420d831"),
          identical(bits(CPM[2L]), "4023fff43420d831"),
          identical(bits(cutoff), "4023fff43420d832"))
actual <- scope$filterByExpr(y, group=c("A", "A"), lib.size=libs)
# Both libraries equal the median: the exact scaled minimum count is 10.
expected <- rowSums(y >= 10) >= 2 & rowSums(y) >= 15
stopifnot(identical(unname(actual), FALSE), identical(unname(expected), TRUE))
cat(sprintf("R2: counts=(10,10), libraries=(1000009,1000009), required samples=2, total=20\n"))
cat(sprintf("R2: documented count condition=%s, filterByExpr=%s\n", expected, actual))
cat("R FILTER COUNTEREXAMPLE PASS\n")
