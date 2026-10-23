x <- scan(file("stdin"), what = integer(), quiet = TRUE)
writeLines(sprintf("%d", sort(x)))
