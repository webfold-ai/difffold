//! Minimal JSON value, writer and parser (no dependencies).

#[derive(Clone, Debug, PartialEq)]
pub enum J {
    Null,
    Bool(bool),
    Int(i64),
    Num(f64),
    Str(String),
    Arr(Vec<J>),
    Obj(Vec<(String, J)>),
}

impl J {
    pub fn obj(v: Vec<(&str, J)>) -> J {
        J::Obj(v.into_iter().map(|(k, v)| (k.to_string(), v)).collect())
    }
    pub fn s(x: &str) -> J {
        J::Str(x.to_string())
    }
    pub fn opt_s(x: &Option<String>) -> J {
        match x {
            Some(s) => J::Str(s.clone()),
            None => J::Null,
        }
    }
    pub fn ints<I: IntoIterator<Item = usize>>(it: I) -> J {
        J::Arr(it.into_iter().map(|x| J::Int(x as i64)).collect())
    }
    pub fn get(&self, k: &str) -> Option<&J> {
        match self {
            J::Obj(v) => v.iter().find(|(kk, _)| kk == k).map(|(_, v)| v),
            _ => None,
        }
    }
    pub fn as_str(&self) -> Option<&str> {
        match self {
            J::Str(s) => Some(s),
            _ => None,
        }
    }
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            J::Int(i) => Some(*i),
            _ => None,
        }
    }
    pub fn as_usize(&self) -> Option<usize> {
        self.as_i64().filter(|i| *i >= 0).map(|i| i as usize)
    }
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            J::Bool(b) => Some(*b),
            _ => None,
        }
    }
    pub fn as_arr(&self) -> Option<&Vec<J>> {
        match self {
            J::Arr(a) => Some(a),
            _ => None,
        }
    }
    pub fn is_null(&self) -> bool {
        matches!(self, J::Null)
    }

    pub fn write(&self, out: &mut String) {
        match self {
            J::Null => out.push_str("null"),
            J::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            J::Int(i) => out.push_str(&i.to_string()),
            J::Num(f) => {
                if f.is_finite() {
                    out.push_str(&format!("{}", f))
                } else {
                    out.push_str("null")
                }
            }
            J::Str(s) => write_str(s, out),
            J::Arr(a) => {
                out.push('[');
                for (i, x) in a.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    x.write(out);
                }
                out.push(']');
            }
            J::Obj(o) => {
                out.push('{');
                for (i, (k, v)) in o.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    write_str(k, out);
                    out.push(':');
                    v.write(out);
                }
                out.push('}');
            }
        }
    }
    pub fn to_string(&self) -> String {
        let mut s = String::new();
        self.write(&mut s);
        s
    }
    /// One top-level key per line; arrays of objects get one element per line.
    pub fn to_pretty(&self) -> String {
        let o = match self {
            J::Obj(o) => o,
            _ => return self.to_string(),
        };
        let mut s = String::from("{\n");
        for (i, (k, v)) in o.iter().enumerate() {
            s.push_str("  ");
            write_str(k, &mut s);
            s.push_str(": ");
            match v {
                J::Arr(a) if a.iter().any(|x| matches!(x, J::Obj(_))) => {
                    s.push_str("[\n");
                    for (j, x) in a.iter().enumerate() {
                        s.push_str("    ");
                        x.write(&mut s);
                        if j + 1 < a.len() {
                            s.push(',');
                        }
                        s.push('\n');
                    }
                    s.push_str("  ]");
                }
                _ => v.write(&mut s),
            }
            if i + 1 < o.len() {
                s.push(',');
            }
            s.push('\n');
        }
        s.push_str("}\n");
        s
    }
}

fn write_str(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

pub fn parse(s: &str) -> Result<J, String> {
    let b = s.as_bytes();
    let mut p = 0usize;
    let v = val(b, &mut p)?;
    ws(b, &mut p);
    if p != b.len() {
        return Err(format!("trailing data at byte {}", p));
    }
    Ok(v)
}

fn ws(b: &[u8], p: &mut usize) {
    while *p < b.len() && matches!(b[*p], b' ' | b'\n' | b'\r' | b'\t') {
        *p += 1;
    }
}

fn val(b: &[u8], p: &mut usize) -> Result<J, String> {
    ws(b, p);
    if *p >= b.len() {
        return Err("unexpected end".into());
    }
    match b[*p] {
        b'n' => lit(b, p, "null", J::Null),
        b't' => lit(b, p, "true", J::Bool(true)),
        b'f' => lit(b, p, "false", J::Bool(false)),
        b'"' => Ok(J::Str(string(b, p)?)),
        b'[' => {
            *p += 1;
            let mut a = Vec::new();
            ws(b, p);
            if *p < b.len() && b[*p] == b']' {
                *p += 1;
                return Ok(J::Arr(a));
            }
            loop {
                a.push(val(b, p)?);
                ws(b, p);
                match b.get(*p) {
                    Some(b',') => *p += 1,
                    Some(b']') => {
                        *p += 1;
                        return Ok(J::Arr(a));
                    }
                    _ => return Err(format!("bad array at byte {}", p)),
                }
            }
        }
        b'{' => {
            *p += 1;
            let mut o = Vec::new();
            ws(b, p);
            if *p < b.len() && b[*p] == b'}' {
                *p += 1;
                return Ok(J::Obj(o));
            }
            loop {
                ws(b, p);
                if b.get(*p) != Some(&b'"') {
                    return Err(format!("expected key at byte {}", p));
                }
                let k = string(b, p)?;
                ws(b, p);
                if b.get(*p) != Some(&b':') {
                    return Err(format!("expected ':' at byte {}", p));
                }
                *p += 1;
                o.push((k, val(b, p)?));
                ws(b, p);
                match b.get(*p) {
                    Some(b',') => *p += 1,
                    Some(b'}') => {
                        *p += 1;
                        return Ok(J::Obj(o));
                    }
                    _ => return Err(format!("bad object at byte {}", p)),
                }
            }
        }
        _ => {
            let st = *p;
            while *p < b.len() && matches!(b[*p], b'-' | b'+' | b'.' | b'e' | b'E' | b'0'..=b'9') {
                *p += 1;
            }
            let t = std::str::from_utf8(&b[st..*p]).map_err(|e| e.to_string())?;
            if t.is_empty() {
                return Err(format!("unexpected byte at {}", st));
            }
            if t.contains(['.', 'e', 'E']) {
                t.parse::<f64>().map(J::Num).map_err(|e| e.to_string())
            } else {
                t.parse::<i64>().map(J::Int).map_err(|e| e.to_string())
            }
        }
    }
}

fn lit(b: &[u8], p: &mut usize, w: &str, v: J) -> Result<J, String> {
    if b[*p..].starts_with(w.as_bytes()) {
        *p += w.len();
        Ok(v)
    } else {
        Err(format!("bad literal at byte {}", p))
    }
}

fn string(b: &[u8], p: &mut usize) -> Result<String, String> {
    *p += 1;
    let mut out: Vec<u8> = Vec::new();
    loop {
        if *p >= b.len() {
            return Err("unterminated string".into());
        }
        let c = b[*p];
        *p += 1;
        match c {
            b'"' => break,
            b'\\' => {
                let e = *b.get(*p).ok_or("bad escape")?;
                *p += 1;
                match e {
                    b'n' => out.push(b'\n'),
                    b'r' => out.push(b'\r'),
                    b't' => out.push(b'\t'),
                    b'b' => out.push(8),
                    b'f' => out.push(12),
                    b'/' => out.push(b'/'),
                    b'\\' => out.push(b'\\'),
                    b'"' => out.push(b'"'),
                    b'u' => {
                        let mut cp = hex4(b, p)?;
                        if (0xD800..0xDC00).contains(&cp) && b.get(*p) == Some(&b'\\') && b.get(*p + 1) == Some(&b'u') {
                            *p += 2;
                            let lo = hex4(b, p)?;
                            cp = 0x10000 + ((cp - 0xD800) << 10) + (lo.wrapping_sub(0xDC00));
                        }
                        let ch = char::from_u32(cp).unwrap_or('\u{fffd}');
                        let mut buf = [0u8; 4];
                        out.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
                    }
                    _ => return Err("bad escape".into()),
                }
            }
            c => out.push(c),
        }
    }
    String::from_utf8(out).map_err(|e| e.to_string())
}

fn hex4(b: &[u8], p: &mut usize) -> Result<u32, String> {
    if *p + 4 > b.len() {
        return Err("bad \\u".into());
    }
    let t = std::str::from_utf8(&b[*p..*p + 4]).map_err(|e| e.to_string())?;
    *p += 4;
    u32::from_str_radix(t, 16).map_err(|e| e.to_string())
}
