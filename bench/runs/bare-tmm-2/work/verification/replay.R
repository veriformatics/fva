# Run the actual bundled R functions; do not load an installed edgeR package.
source("edgeR/R/calcNormFactors.R")
source("edgeR/R/normLibSizes.R")
m <- as.matrix(read.table("counts.tsv", sep="\t"))
# Trace only observes locals at function exit. It does not change arithmetic.
at <- 0L
invisible(trace(".calcFactorTMM", exit=quote({
    at <<- at + 1L
    rows <- if (exists("keep", inherits=FALSE)) which(fin)[keep] else which(fin)
    cat("MASK ", at, " ", paste(rows, collapse=" "), "\n", sep="")
    if (at == 1L) for (id in c(163L, 355L)) {
        j <- which(which(fin) == id)
        cat("TIE row ", id, ": A_R=", sprintf("%.17g", absE[j]),
            " rank_R=", rank(absE)[j], "\n", sep="")
    }
}), print=FALSE))
f <- normLibSizes(m, method="TMM")
for (i in seq_along(f)) cat("FACTOR ", i, " ", sprintf("%.17g", f[i]), "\n", sep="")
