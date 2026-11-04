//! Vocabulary and small text generators.

use crate::rng::Rng;

pub const ADJ: &[&str] = &["Classic", "Modern", "Compact", "Premium", "Ultra", "Eco", "Smart", "Vintage", "Portable", "Rugged", "Slim", "Deluxe", "Essential", "Pro", "Lite", "Heritage"];
pub const NOUN: &[&str] = &["Backpack", "Kettle", "Lamp", "Headphones", "Jacket", "Sneakers", "Blender", "Notebook", "Speaker", "Watch", "Mug", "Chair", "Desk", "Camera", "Keyboard", "Bottle", "Sofa", "Tent", "Router", "Monitor"];
pub const WORDS: &[&str] = &[
    "market", "river", "signal", "window", "garden", "engine", "forest", "bridge", "pattern", "harbor", "silver", "motion", "candle", "planet", "ticket", "library", "season", "branch", "anchor", "valley", "orbit", "copper", "meadow", "thread", "summit", "ribbon", "lantern", "compass", "ledger", "puzzle", "voyage", "quartz", "timber", "canvas", "beacon", "harvest", "mirror", "pioneer", "cascade", "horizon",
];
pub const FILLER: &[&str] = &["the", "a", "of", "and", "to", "in", "for", "with", "on", "that", "this", "is", "was", "by", "from", "as", "an", "at", "it", "be"];
pub const FIRST: &[&str] = &["Ada", "Ben", "Chloe", "Dev", "Elif", "Farid", "Grace", "Hugo", "Ines", "Jonas", "Kira", "Leo", "Mina", "Noor", "Omar", "Priya", "Quinn", "Rosa", "Sam", "Tara"];
pub const LAST: &[&str] = &["Okafor", "Lindqvist", "Moreau", "Tanaka", "Silva", "Novak", "Haddad", "Brooks", "Kowalski", "Fischer", "Ng", "Rossi", "Patel", "Dubois", "Evans"];
pub const BRANDS: &[&str] = &["Northwind", "Brightfield", "Kestrel", "Lumen", "Harborline", "Oakridge", "Pinecrest", "Solace", "Tidewater", "Vantage", "Quillon", "Marlowe"];
pub const STATUS: &[&str] = &["Active", "Pending", "Shipped", "Cancelled", "Refunded", "On hold"];
pub const CITIES: &[&str] = &["Lisbon", "Osaka", "Toronto", "Nairobi", "Oslo", "Austin", "Lyon", "Perth"];

pub fn cap(s: &str) -> String {
    let mut c = s.chars();
    match c.next() {
        Some(f) => f.to_uppercase().collect::<String>() + c.as_str(),
        None => String::new(),
    }
}

pub fn word(r: &mut Rng) -> &'static str {
    r.pick(WORDS)
}

pub fn sentence(r: &mut Rng, lo: usize, hi: usize) -> String {
    let n = r.range(lo, hi + 1);
    let mut v: Vec<&str> = vec![];
    for i in 0..n {
        v.push(if i % 3 == 1 { r.pick(FILLER) } else { word(r) });
    }
    format!("{}.", cap(&v.join(" ")))
}

pub fn title(r: &mut Rng) -> String {
    format!("{} {} {}", cap(word(r)), r.pick(FILLER).to_string().replace("the", "of"), cap(word(r)))
}

pub fn product_name(r: &mut Rng) -> String {
    format!("{} {} {}", r.pick(ADJ), r.pick(NOUN), r.range(100, 999))
}

pub fn person(r: &mut Rng) -> String {
    format!("{} {}", r.pick(FIRST), r.pick(LAST))
}

pub fn slug(s: &str) -> String {
    let mut o = String::new();
    for c in s.chars() {
        if c.is_ascii_alphanumeric() {
            o.push(c.to_ascii_lowercase());
        } else if !o.ends_with('-') && !o.is_empty() {
            o.push('-');
        }
    }
    o.trim_end_matches('-').to_string()
}

pub fn price(r: &mut Rng, cur: &str) -> String {
    format!("{}{}.{:02}", cur, r.range(2, 480), r.range(0, 100))
}

pub fn date(r: &mut Rng) -> String {
    format!("2026-{:02}-{:02}", r.range(1, 13), r.range(1, 29))
}

pub fn rel_time(r: &mut Rng) -> String {
    match r.below(4) {
        0 => format!("{} minutes ago", r.range(2, 59)),
        1 => format!("{} hours ago", r.range(1, 23)),
        2 => format!("{} days ago", r.range(1, 28)),
        _ => format!("{} months ago", r.range(1, 11)),
    }
}

pub fn iso_time(r: &mut Rng) -> String {
    format!("2026-11-{:02}T{:02}:{:02}:{:02}Z", r.range(1, 4), r.below(24), r.below(60), r.below(60))
}

pub fn hrefs(r: &mut Rng, section: &str) -> String {
    format!("/{}/{}-{}", section, word(r), r.range(1000, 9999))
}

/// Rewrite words so the result differs from `s`, preserving outer whitespace.
pub fn rewrite_text(r: &mut Rng, s: &str) -> String {
    let lead = &s[..s.len() - s.trim_start().len()];
    let trail = &s[s.trim_end().len()..];
    let core = s.trim();
    let mut words: Vec<String> = core.split(' ').map(|w| w.to_string()).collect();
    for _ in 0..8 {
        let i = r.below(words.len());
        let w = &words[i];
        let nw = if w.chars().any(|c| c.is_ascii_digit()) {
            let mut cs: Vec<char> = w.chars().collect();
            let digits: Vec<usize> = cs.iter().enumerate().filter(|(_, c)| c.is_ascii_digit()).map(|(i, _)| i).collect();
            let k = digits[r.below(digits.len())];
            let d = cs[k].to_digit(10).unwrap();
            cs[k] = char::from_digit((d + 1 + r.below(8) as u32) % 10, 10).unwrap();
            cs.into_iter().collect()
        } else {
            let mut x = word(r).to_string();
            if w.chars().next().map(|c| c.is_uppercase()).unwrap_or(false) {
                x = cap(&x);
            }
            if let Some(p) = w.chars().last().filter(|c| matches!(c, '.' | ',' | '!' | '?')) {
                x.push(p);
            }
            x
        };
        if nw != *w {
            words[i] = nw;
            break;
        }
    }
    let out = format!("{}{}{}", lead, words.join(" "), trail);
    if out == s {
        format!("{}{} x{}", lead, core, trail)
    } else {
        out
    }
}

/// Rewrite every digit-bearing number in a price-like string; guaranteed different.
pub fn change_price(r: &mut Rng, s: &str) -> String {
    let first = s.find(|c: char| c.is_ascii_digit());
    let first = match first {
        Some(f) => f,
        None => return format!("{}1", s),
    };
    let rest = &s[first..];
    let end = rest.find(|c: char| !(c.is_ascii_digit() || c == '.' || c == ',')).unwrap_or(rest.len());
    let num = &rest[..end];
    for _ in 0..8 {
        let new = if num.contains('.') { format!("{}.{:02}", r.range(2, 990), r.below(100)) } else { format!("{}", r.range(2, 9990)) };
        if new != num {
            return format!("{}{}{}", &s[..first], new, &rest[end..]);
        }
    }
    format!("{}{}0{}", &s[..first], num, &rest[end..])
}
