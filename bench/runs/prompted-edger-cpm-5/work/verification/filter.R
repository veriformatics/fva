# The two shipped R files run unchanged. Only their missing edgeR FFI helpers
# are supplied here; .Call sends the full matrix to the ORIGINAL Wasm binary.
suppressPackageStartupMessages(library(jsonlite))
e <- globalenv()
sys.source('R/cpm.R', envir=e)
sys.source('R/filterByExpr.R', envir=e)
registerS3method('cpm','default',e$cpm.default,envir=e)
registerS3method('filterByExpr','default',e$filterByExpr.default,envir=e)
e$makeCompressedMatrix <- function(x, dims, byrow) {
  stopifnot(byrow, length(dims)==2L, is.numeric(x))
  if (is.matrix(x)) { stopifnot(identical(dim(x),dims)); return(x) }
  stopifnot(length(x)==dims[2L])
  matrix(x,dims[1L],dims[2L],byrow=TRUE)
}
e$.cxx_calculate_cpm_raw <- 'original_wasm_raw'
e$.Call <- function(name, y, lib.size, nthreads) {
  stopifnot(identical(name,'original_wasm_raw'), nthreads==1L)
  request <- toJSON(list(nrow=nrow(y),ncol=ncol(y),
    counts=as.double(y),libs=as.double(lib.size)),auto_unbox=TRUE)
  result <- system2('node', c('verification/wasm.mjs','matrix'),
    input=request, stdout=TRUE)
  stopifnot(is.null(attr(result,'status')))
  matrix(fromJSON(paste(result,collapse='\n')),nrow(y),ncol(y))
}
bits <- function(x) paste(rev(format(writeBin(x,raw(),size=8,endian='little'))),collapse='')
# Ordinary integer count matrix, default thresholds and all samples one group.
y <- matrix(c(10,8,10,8),2,2)
L <- colSums(y)
CPM <- e$cpm(y,lib.size=L)
cutoff <- 10/median(L)*1e6
kept <- suppressMessages(e$filterByExpr(y))
stopifnot(identical(L,c(18,18)), all(y[1,]>=10), sum(y[1,])>=15,
  bits(CPM[1,1])=='4120f4471c71c71c',bits(cutoff)=='4120f4471c71c71d',
  all(CPM[1,]<cutoff),identical(kept,c(FALSE,FALSE)))
cat('R2 integer witness: y = [[10,10],[8,8]], L = [18,18], min.count = 10, min.total.count = 15\n')
cat(sprintf('R2 observed CPM = %.17g; cutoff = %.17g; keep = FALSE FALSE\n',CPM[1,1],cutoff))
# A second witness to the documentation's exact sample-number rule.
# CPM and total-count checks are far from their boundaries in this example.
z <- matrix(c(20,0),1,2)
k <- 1+2^-48
kept2 <- e$filterByExpr(z,lib.size=c(1e6,1e6),min.sample.size=k)
expressed <- sum(e$cpm(z,lib.size=c(1e6,1e6))>=10)
stopifnot(expressed==1L,k>1,expressed<k,identical(kept2,TRUE),sum(z)>=15)
cat(sprintf('R2 sample witness: y = [[20,0]], L = [1e6,1e6], required = %.17g, expressed = 1, keep = TRUE\n',k))
if ('negative' %in% commandArgs(TRUE)) stopifnot(all(kept))
