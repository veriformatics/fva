//! Untrusted source: FVA verifies the compiled rust.wasm, never this file.
#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

/// On signed 32-bit ints: `lo` if `x < lo`, else `hi` if `x > hi`, else `x`.
#[no_mangle]
pub extern "C" fn clamp(x: i32, lo: i32, hi: i32) -> i32 {
    if x < lo {
        lo
    } else if x > hi {
        hi
    } else {
        x
    }
}

/// The greatest common divisor of unsigned 32-bit ints (`gcd(a, 0) = a`).
#[no_mangle]
pub extern "C" fn gcd(mut a: u32, mut b: u32) -> u32 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}
