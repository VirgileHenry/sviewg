mod xml_parser;

pub struct SvgImage {}

impl SvgImage {
    pub fn parse(input: &str) -> Result<Self, String> {
        let xml = xml_parser::parse_xml(input)?;
        Ok(SvgImage {})
    }
}
