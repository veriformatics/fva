//! C-ABI export of runorm's PFlog over a dense row-major cells × genes count matrix. The two
//! buffers are statics, so the caller's data never meets the allocator's heap.

const CAP: usize = 1 << 17;
static mut COUNTS: [f64; CAP] = [0.0; CAP];
static mut OUT: [f64; CAP] = [0.0; CAP];

/// Address of the input buffer: `CAP` f64 values, row-major, row = cell.
#[unsafe(no_mangle)]
pub extern "C" fn pflog_counts() -> *mut f64 {
    &raw mut COUNTS as *mut f64
}

/// Address of the output buffer: `CAP` f64 values, row-major, row = cell.
#[unsafe(no_mangle)]
pub extern "C" fn pflog_output() -> *const f64 {
    &raw const OUT as *const f64
}

/// Reads the first `n_cells·n_genes` values of the input buffer (non-negative counts) and
/// writes runorm's dense PFlog matrix `data[i,j] − row_center[i]` to the output buffer.
/// Returns 0, or −1 when the size exceeds `CAP` or runorm rejects the input.
#[unsafe(no_mangle)]
pub extern "C" fn pflog(n_cells: usize, n_genes: usize) -> i32 {
    let Some(len) = n_cells.checked_mul(n_genes).filter(|&l| l <= CAP) else { return -1 };
    let x = unsafe { &(&raw const COUNTS).as_ref().unwrap()[..len] };
    let (mut data, mut indices, mut indptr) = (Vec::new(), Vec::new(), vec![0usize]);
    for i in 0..n_cells {
        for j in 0..n_genes {
            let v = x[i * n_genes + j];
            if v != 0.0 {
                data.push(v);
                indices.push(j);
            }
        }
        indptr.push(data.len());
    }
    let Ok(c) = runorm::CsrCounts::new(n_cells, n_genes, data, indices, indptr) else { return -1 };
    let Ok(r) = runorm::pflog(&c) else { return -1 };
    unsafe { (&raw mut OUT).as_mut().unwrap()[..len].copy_from_slice(&r.densify()) };
    0
}
