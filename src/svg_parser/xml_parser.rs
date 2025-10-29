/// XML declaration tag, optionnal at the start of a xml file.
///
/// https://www.w3.org/TR/xml/#NT-XMLDecl
pub struct XmlDeclaration<'src> {
    /// Version of XML used for this file.
    /// https://www.w3.org/TR/xml/#NT-VersionInfo
    version: XmlVersion<'src>,
    /// Character encoding in entities.
    /// https://www.w3.org/TR/xml/#NT-EncodingDecl
    /// This can later be replaced by an enum with different possible encodings.
    encoding: Option<&'src str>,
    /// Standalone document declaration. 'yes' is true, 'no' is false.
    /// https://www.w3.org/TR/xml/#NT-SDDecl
    standalone: Option<bool>,
}

/// Version info present in the XML declaration tag.
///
/// https://www.w3.org/TR/xml/#NT-VersionInfo
pub struct XmlVersion<'src> {
    /// References the version string in the source file.
    version: &'src str,
    /// Parsed major of the version.
    major: usize,
    /// Parsed minor of the version.
    minor: usize,
}

/// A comment whithin an XML file, such as <!-- comment -->
///
/// https://www.w3.org/TR/xml/#NT-Comment
pub struct XmlComment<'src> {
    /// reference to the comment in the original source file.
    comment: &'src str,
}

pub struct XmlTag<'src> {
    name: &'src str,
    args: arrayvec::ArrayVec<(&'src str, &'src str), 8>,
    children: Vec<XmlTag<'src>>,
}

/// Entire XML file, stored in a structured way to easily extract the useful data.
///
/// https://www.w3.org/TR/xml/
pub struct Xml<'src> {
    prologue: Option<XmlDeclaration<'src>>,
    root: XmlTag<'src>,
}

impl<'src> Xml<'src> {
    pub fn parse(input: &str) -> Result<Self, String> {
        let mut input = input;
    }
}

/// Advance the given input string to skip any number of spaces as defined
/// in the XML documentation: https://www.w3.org/TR/xml/#NT-S
fn skip_spaces(input: &mut &str) {
    loop {
        match input.as_bytes().first() {
            Some(0x20 /* Space */)
            | Some(0x09 /* Tabulation */)
            | Some(0x0D /* New line */)
            | Some(0x0A /* Carriage return */) => *input = &input[1..],
            _ => break,
        }
    }
}
