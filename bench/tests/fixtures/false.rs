use vstd::prelude::*;
verus! {
fn add_one(x: u32) -> (r: u32)
    requires x < u32::MAX,
    ensures r == x + 2,
{
    x + 1
}
}
fn main() {}
