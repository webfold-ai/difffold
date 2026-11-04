//! libFuzzer target for the line differ: both algorithms must rebuild the new text (`replay_ok`).
#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    difffold_fuzz::check_lines(data);
});
