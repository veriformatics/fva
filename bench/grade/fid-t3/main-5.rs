fn main() {
    use std::io::BufRead;
    for line in std::io::stdin().lock().lines() {
        let line = line.unwrap();
        let mut it = line.split_whitespace();
        let cap: usize = it.next().unwrap().parse().unwrap();
        let hex = it.next().unwrap_or("-");
        let s: Vec<u8> = if hex == "-" { vec![] } else {
            (0..hex.len() / 2).map(|i| u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap()).collect() };
        match reference_decompress(&s, cap) {
            Some(out) => println!("{} {}", out.len(), out.iter().map(|b| format!("{:02x}", b)).collect::<String>()),
            None => println!("-1"),
        }
    }
}
