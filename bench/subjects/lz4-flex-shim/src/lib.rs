#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

/// Caller supplies live, non-overlapping input/output buffers, lengths <= isize::MAX.
/// Returns bytes written, or -1 for an invalid block/insufficient output capacity.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lz4_decompress(
    src: *const u8,
    dst: *mut u8,
    n: usize,
    cap: usize,
) -> isize {
    let input = unsafe { core::slice::from_raw_parts(src, n) };
    let output = unsafe { core::slice::from_raw_parts_mut(dst, cap) };
    match lz4_flex::block::decompress_into(input, output) {
        Ok(written) => written as isize,
        Err(_) => -1,
    }
}

/// Same buffer contract as lz4_decompress; emits an LZ4 block without a size prefix.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lz4_compress(src: *const u8, dst: *mut u8, n: usize, cap: usize) -> isize {
    let input = unsafe { core::slice::from_raw_parts(src, n) };
    let output = unsafe { core::slice::from_raw_parts_mut(dst, cap) };
    match lz4_flex::block::compress_into(input, output) {
        Ok(written) => written as isize,
        Err(_) => -1,
    }
}
