//! Handwritten edge cases: the byte certificate must hold under real `git apply`.

use gitcompat::edge::{cases, Expect};
use gitcompat::gitcheck::check_with_git;
use gitcompat::patch::{apply_patch, make_patch, Outcome};

#[test]
fn every_edge_case_round_trips_through_git_apply() {
    let mut failures = Vec::new();
    for case in cases() {
        let out = make_patch(&case.spec, &case.before, &case.after, case.binary);
        match (case.expect, out) {
            (Expect::Identical, Outcome::Identical) => {}
            (Expect::Refused, Outcome::Refused(_)) => {}
            (Expect::Text, Outcome::Text { patch, .. }) => {
                if let Err(e) = apply_patch(&case.before, &patch).and_then(|o| {
                    if o == case.after {
                        Ok(())
                    } else {
                        Err("own applier mismatch".into())
                    }
                }) {
                    failures.push(format!("{}: in-process replay: {e}", case.name));
                }
                let r = check_with_git(&case.spec, &case.before, &case.after, &patch);
                if !r.all_ok() {
                    failures.push(format!("{}: {}", case.name, r.detail));
                }
            }
            (Expect::GitBinary, Outcome::GitBinary { patch }) => {
                assert!(
                    !patch.starts_with(b"--- "),
                    "{}: text patch for binary",
                    case.name
                );
                let r = check_with_git(&case.spec, &case.before, &case.after, &patch);
                if !r.all_ok() {
                    failures.push(format!("{}: {}", case.name, r.detail));
                }
            }
            (e, o) => failures.push(format!(
                "{}: expected {e:?}, got {}",
                case.name,
                match o {
                    Outcome::Identical => "Identical".to_string(),
                    Outcome::Text { .. } => "Text".to_string(),
                    Outcome::GitBinary { .. } => "GitBinary".to_string(),
                    Outcome::Refused(r) => format!("Refused({r})"),
                }
            )),
        }
    }
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
}
