x <- scan(file("stdin"), quiet = TRUE)
writeLines(as.character(sort(x)))
