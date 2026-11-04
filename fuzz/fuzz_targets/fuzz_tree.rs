//! libFuzzer target for the tree contracts (C3, C5, C6). Raw bytes in; a panic is a finding.
#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    difffold_fuzz::check_tree(data);
});
