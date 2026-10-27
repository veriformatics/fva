# Execute the supplied implementation, without loading or changing a package.
source("edgeR/R/calcNormFactors.R")
source("edgeR/R/normLibSizes.R")
x <- as.matrix(read.table("counts.tsv", sep="\t"))
actual <- normLibSizes(x, method="TMM")
shipped <- scan("edger-factors.txt", quiet=TRUE)
stopifnot(identical(dim(x), c(454L,7L)), length(actual)==7L,
          all(is.finite(actual)), max(abs(actual-shipped)) <= 1e-14)
cat(sprintf("edgeR source replay: max absolute error %.17g (tolerance 1e-14)\n",
            max(abs(actual-shipped))))
