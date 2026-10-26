# Source the shipped functions verbatim in this isolated R process.
args <- commandArgs(TRUE)
e <- globalenv()
sys.source("R/cpm.R", envir=e)
sys.source("R/filterByExpr.R", envir=e)
# Witness-only R/Wasm ABI adapter. Unknown calls fail instead of being modeled.
e$makeCompressedMatrix <- function(x, dims, byrow) {
    stopifnot(is.double(x), byrow)
    matrix(x, dims[1], dims[2], byrow=TRUE)
}
e$.cxx_calculate_cpm_raw <- "verified-Wasm-raw"
inputs <- list(matrix(c(10,8,10,8),2), matrix(c(11,7,11,7),2), matrix(10,1))
libs <- list(matrix(18,2,2), matrix(18,2,2), matrix(1e6,1))
e$.Call <- function(symbol, y, lib.size, nthreads) {
    stopifnot(identical(symbol,e$.cxx_calculate_cpm_raw), nthreads == 1L)
    k <- which(vapply(seq_along(inputs), function(i)
        identical(y,inputs[[i]]) && identical(lib.size,libs[[i]]), logical(1)))
    stopifnot(length(k)==1)
    values <- readBin(file.path(args[1],paste0("case",k+1,".bin")),
                      "double", n=length(y), size=8, endian="little")
    stopifnot(length(values)==length(y))
    matrix(values,nrow(y),ncol(y))
}
cp <- e$cpm(inputs[[1]],lib.size=c(18,18))
cutoff <- 10/median(c(18,18))*1e6
stopifnot(identical(writeBin(cutoff,raw(),size=8,endian="little"),
                   as.raw(c(0x1d,0xc7,0x71,0x1c,0x47,0xf4,0x20,0x41))))
keep <- e$filterByExpr(inputs[[1]])
stopifnot(all(colSums(inputs[[1]]) == 18), all(inputs[[1]][1,] == 10),
          sum(inputs[[1]][1,]) == 20, all(cp[1,] < cutoff),
          identical(unname(keep),c(FALSE,FALSE)))
cat(sprintf("R2 boundary: CPM=%.17g < cutoff=%.17g; keep=(%s)\n",
            cp[1,1],cutoff,paste(keep,collapse=",")))
stopifnot(identical(unname(e$filterByExpr(inputs[[2]])),c(TRUE,FALSE)))
# This second example refutes a reading of R2 that omits min.total.count.
total <- e$filterByExpr(inputs[[3]],lib.size=1e6,min.sample.size=1)
relaxed <- e$filterByExpr(inputs[[3]],lib.size=1e6,min.sample.size=1,min.total.count=0)
stopifnot(identical(unname(total),FALSE),identical(unname(relaxed),TRUE))
cat("PASS: unchanged R functions reject the boundary gene; above-cutoff control kept; total-count control checked\n")
