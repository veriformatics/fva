# Execute the shipped R code. Bridge its native .Call boundary to the shipped
# Wasm export; these fixtures use finite numeric matrices and vector lib.size.
e <- globalenv()
sys.source("R/cpm.R", envir=e)
sys.source("R/filterByExpr.R", envir=e)
e$makeCompressedMatrix <- function(x, dims, byrow) {
    stopifnot(byrow, length(x) == dims[2])
    x
}
e$.cxx_calculate_cpm_raw <- "raw"
e$.Call <- function(symbol, y, lib.size, nthreads) {
    stopifnot(identical(symbol, "raw"), nthreads == 1L)
    request <- list(nrow=nrow(y), ncol=ncol(y), counts=as.vector(y), libs=as.vector(lib.size))
    path <- tempfile(fileext=".json")
    on.exit(unlink(path))
    # nrow/ncol must be scalars, counts/libs must remain arrays.
    request$nrow <- jsonlite::unbox(request$nrow)
    request$ncol <- jsonlite::unbox(request$ncol)
    jsonlite::write_json(request, path, digits=NA, auto_unbox=FALSE)
    output <- system2("python3", c("verify/runtime.py", shQuote(path)), stdout=TRUE)
    stopifnot(is.null(attr(output, "status")))
    matrix(scan(text=output, quiet=TRUE), nrow(y), ncol(y))
}

y <- matrix(10, 1, 1)
stopifnot(identical(e$cpm(y, lib.size=1e6), y))
actual <- e$filterByExpr(y, lib.size=1e6, min.sample.size=1)
stopifnot(identical(actual, FALSE))
cat("R2 literal: count=10, L=1000000, required samples=1; sample criterion TRUE, actual FALSE (total < 15)\n")

y <- matrix(c(20, 0), 1, 2)
k <- 1 + 2^-48
measured <- e$cpm(y, lib.size=c(1e6, 1e6))
stopifnot(identical(measured, y), k > 1)
documented <- rowSums(measured >= 10) >= k & rowSums(y) >= 15
actual <- e$filterByExpr(y, lib.size=c(1e6, 1e6), min.sample.size=k)
stopifnot(identical(documented, FALSE), identical(actual, TRUE))
cat(sprintf("R2 full documentation: counts=[20,0], L=[1000000,1000000], k=%.17g; documented FALSE, actual TRUE\n", k))
