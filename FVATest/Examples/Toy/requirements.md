Requirements for toy.wasm, a small C library compiled to WebAssembly. Integers are 32-bit.

## R1
clamp(x, lo, hi) reads its arguments as signed integers. It returns lo when x < lo, else hi
when x > hi, else x.

## R2
gcd(a, b) reads its arguments as unsigned integers and returns their greatest common divisor,
with gcd(a, 0) = a.

## R3
sum_to(n) reads n as an unsigned integer and returns 0 + 1 + ... + (n - 1), wrapped to 32 bits.
