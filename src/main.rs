mod svg_parser;

fn main() {
    let file = std::fs::read_to_string("./test/tiger.svg").expect("Failed to open file");
    let svg = svg_parser::SvgImage::parse(&file).expect("Failed to parse to svg");
    let _ = svg;
}
