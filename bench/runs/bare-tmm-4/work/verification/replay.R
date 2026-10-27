# Run the supplied edgeR default method, without an installed edgeR package.
args <- commandArgs(trailingOnly=TRUE)
stopifnot(length(args) == 1L)
source("edgeR/R/calcNormFactors.R")
source("edgeR/R/normLibSizes.R")
m <- as.matrix(read.table("counts.tsv", sep="\t"))
stopifnot(identical(dim(m), c(454L, 7L)))
selected <- list()
invisible(capture.output(trace(".calcFactorTMM", print=FALSE, exit=quote({
    ids <- if (exists("keep", inherits=FALSE)) which(fin)[keep] else which(fin)
    selected[[length(selected)+1L]] <<- ids
    if (length(selected) == 1L) {
        j <- match(355L, which(fin))
        cat("edgeR sample 1, gene 355: A-rank", rank(absE)[j],
            "upper cutoff", hiS, "retained", 355L %in% ids, "\n")
    }
}))))
f <- normLibSizes(m, method="TMM")
# Check the exact text, including the final LF, not just parsed double equality.
actual <- charToRaw(paste0(paste(sprintf("%.17g", f), collapse="\n"), "\n"))
expected <- readBin("edger-factors.txt", "raw", file.info("edger-factors.txt")$size)
stopifnot(identical(actual, expected))
writeLines(vapply(selected, function(x) paste(x, collapse=","), ""), args[1])
cat("edgeR: exact output bytes reproduced; retained genes:", lengths(selected), "\n")
