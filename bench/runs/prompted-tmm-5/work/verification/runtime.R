# Execute the supplied source directly; no edgeR package installation is needed.
source("edgeR/R/calcNormFactors.R")
source("edgeR/R/normLibSizes.R")
x <- as.matrix(read.table("counts.tsv", sep="\t"))
y <- normLibSizes(x, method="TMM")
z <- scan("edger-factors.txt",quiet=TRUE)
stopifnot(identical(unname(y),z))
cat("Supplied edgeR source reproduces every shipped double exactly\n")
o <- x[,3]; r <- x[,4]; no <- sum(o); nr <- sum(r)
m <- log2((o/no)/(r/nr)); a <- (log2(o/no)+log2(r/nr))/2
ok <- is.finite(m)&is.finite(a)&a > -1e10
m <- m[ok]; a <- a[ok]; o <- o[ok]; r <- r[ok]
n <- length(m); lm <- floor(n*.3)+1; la <- floor(n*.05)+1
keep <- rank(m)>=lm & rank(m)<=n+1-lm & rank(a)>=la & rank(a)<=n+1-la
cat("Floating-point retained sample 3 / reference 4:",sum(keep),"of",n,"\n")
# Find an exact proportional-count tie that floating-point evaluation splits.
for(i in seq_along(o)) {
  same <- o*r[i] == o[i]*r
  if(length(unique(m[same]))>1) {
    cat("Exact count-ratio tie",o[i],"/",r[i],"splits into:\n")
    print(unique(data.frame(obs=o[same],ref=r[same],M=sprintf("%.17g",m[same]),rank=rank(m)[same],kept=keep[same])))
    break
  }
}
