fn main() {
    let a: Vec<String> = std::env::args().collect();
    let (x, y) = (std::fs::read(&a[1]).unwrap(), std::fs::read(&a[2]).unwrap());
    let t = std::time::Instant::now();
    let d = difffold::lines::diff_text(&x, &y);
    let dt = t.elapsed();
    let hwm = std::fs::read_to_string("/proc/self/status")
        .unwrap()
        .lines()
        .find(|l| l.starts_with("VmHWM"))
        .unwrap()
        .to_string();
    println!(
        "cost {} time {:?} {}",
        d.cost(),
        dt,
        hwm.split_whitespace().collect::<Vec<_>>().join(" ")
    );
}
