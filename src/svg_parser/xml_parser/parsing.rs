/// The character set trait allows to define characters set,
/// and create functions to expect chars and strings that are only chars from within the set.
/// This is useful to parse litterals that can only be from given sets.
trait CharacterSet {
    /// Returns whether the first character of the given string is in the given character set.
    /// If the character is in it, return Some with the number of bytes that characters takes.
    /// Otherwise, returns None when the first character is not in the character set.
    fn match_first(input: &str) -> Option<usize>;
}

/// Decimals digits character set, so 0-9.
pub struct DecimalDigits;

impl CharacterSet for DecimalDigits {
    fn match_first(input: &str) -> Option<usize> {
        match input.as_bytes().first()? {
            0x30..=0x39 => Some(1),
            _ => None,
        }
    }
}

/// Hexadecimal digits, 0-9 + a-f + A-F.
pub struct HexadecimalDigits;

impl CharacterSet for HexadecimalDigits {
    fn match_first(input: &str) -> Option<usize> {
        match input.as_bytes().first()? {
            0x30..=0x39 => Some(1),
            0x41..=0x46 => Some(1),
            0x61..=0x66 => Some(1),
            _ => None,
        }
    }
}

/// [2] - Char
///
/// https://www.w3.org/TR/xml/#NT-Char
pub struct XmlChar;

impl CharacterSet for XmlChar {
    fn match_first(input: &str) -> Option<usize> {
        let bytes = input.as_bytes();
        let word: u32 = match bytes.len() {
            0 => return None,
            1 => u32::from(bytes[0]) << 24,
            2 => (u32::from(bytes[0]) << 24) | (u32::from(bytes[1]) << 16),
            3 => (u32::from(bytes[0]) << 24) | (u32::from(bytes[1]) << 16) | (u32::from(bytes[2]) << 8),
            _ => (u32::from(bytes[0]) << 24) | (u32::from(bytes[1]) << 16) | (u32::from(bytes[2]) << 8) | u32::from(bytes[3]),
        };
        match word {
            0x09_000000..=0x09_FFFFFF => Some(1), /* Single point \t */
            0x0A_000000..=0x0A_FFFFFF => Some(1), /* Single point \n */
            0x0D_000000..=0x0D_FFFFFF => Some(1), /* Single point \r */
            0x20_000000..=0x7F_FFFFFF => Some(1), /* ASCII visible chars */
            0xC280_0000..=0xDFBF_FFFF => Some(2), /* Two-byte UTF-8 (U+0080–U+07FF) */
            0xE0A080_00..=0xED9FBF_FF => Some(3), /* Three-byte UTF-8 (U+0800–U+D7FF) */
            0xEE8080_00..=0xEFBFBF_FF => Some(3), /* Three-byte UTF-8 (U+E000–U+FFFD) */
            0xF0908080_..=0xF48FBFBF_ => Some(4), /* Four-byte UTF-8 (U+10000–U+10FFFF) */
            _ => None,
        }
    }
}

/// [3] - Spaces
///
/// https://www.w3.org/TR/xml/#NT-S
pub struct Spaces;

impl CharacterSet for Spaces {
    fn match_first(input: &str) -> Option<usize> {
        match input.as_bytes().first()? {
            0x20 | 0x09 | 0x0D | 0x0A => Some(1),
            _ => None,
        }
    }
}

/// [4] - Name Characters
///
/// https://www.w3.org/TR/xml/#NT-NameChar
pub struct NameChar;

impl CharacterSet for NameChar {
    fn match_first(input: &str) -> Option<usize> {
        let bytes = input.as_bytes();
        let word: u32 = match bytes.len() {
            0 => return None,
            1 => u32::from(bytes[0]) << 24,
            2 => (u32::from(bytes[0]) << 24) | (u32::from(bytes[1]) << 16),
            3 => (u32::from(bytes[0]) << 24) | (u32::from(bytes[1]) << 16) | (u32::from(bytes[2]) << 8),
            _ => (u32::from(bytes[0]) << 24) | (u32::from(bytes[1]) << 16) | (u32::from(bytes[2]) << 8) | u32::from(bytes[3]),
        };
        match word {
            0x3A_000000..=0x3A_FFFFFF => Some(1), /* ":" */
            0x41_000000..=0x5A_FFFFFF => Some(1), /* [A-Z] */
            0x5F_000000..=0x5F_FFFFFF => Some(1), /* "_" */
            0x61_000000..=0x7A_FFFFFF => Some(1), /* [a-z] */
            0x2D_000000..=0x2D_FFFFFF => Some(1), /* "-" */
            0x2E_000000..=0x2E_FFFFFF => Some(1), /* "." */
            0x30_000000..=0x39_FFFFFF => Some(1), /* [0-9] */
            0xC380_0000..=0xC396_FFFF => Some(2), /* Two-byte UTF-8 (U+00C0–U+00D6) */
            0xC398_0000..=0xC3B6_FFFF => Some(2), /* Two-byte UTF-8 (U+00D8–U+00F6) */
            0xC3B8_0000..=0xCBBF_FFFF => Some(2), /* Two-byte UTF-8 (U+00F8–U+02FF) */
            0xCDB0_0000..=0xCDBD_FFFF => Some(2), /* Two-byte UTF-8 (U+0370–U+037D) */
            0xCDBF_0000..=0xDFBF_FFFF => Some(2), /* Two-byte UTF-8 (U+037F–U+07FF) */
            0xC2B7_0000..=0xC2B7_FFFF => Some(2), /* Two-byte UTF-8 (U+00B7) */
            0xCC80_0000..=0xCDAF_FFFF => Some(2), /* Two-byte UTF-8 (U+0300–U+036F) */
            0xE0A080_00..=0xE1BFBF_FF => Some(3), /* Three-byte UTF-8 (U+0800–U+1FFF) */
            0xE2808C_00..=0xE2808D_FF => Some(3), /* Three-byte UTF-8 (U+200C–U+200D) */
            0xE281B0_00..=0xE2868F_FF => Some(3), /* Three-byte UTF-8 (U+2070–U+218F) */
            0xE2B080_00..=0xE2BFAF_FF => Some(3), /* Three-byte UTF-8 (U+2C00–U+2FEF) */
            0xE38081_00..=0xED9FBF_FF => Some(3), /* Three-byte UTF-8 (U+3001–U+D7FF) */
            0xEFA480_00..=0xEFB78F_FF => Some(3), /* Three-byte UTF-8 (U+F900–U+FDCF) */
            0xEFB7B0_00..=0xEFBFBD_FF => Some(3), /* Three-byte UTF-8 (U+FDF0–U+FFFD) */
            0xF0908080_..=0xF3AFBFBF_ => Some(4), /* Four-byte UTF-8 (U+10000–U+EFFFF) */
            0xE280BF_00..=0xE28180_FF => Some(3), /* Three-byte UTF-8 (U+203F–U+2040) */
            _ => None,
        }
    }
}

/// [4a] - Name Start Characters
///
/// https://www.w3.org/TR/xml/#NT-NameStartChar
pub struct NameStartChar;

impl CharacterSet for NameStartChar {
    fn match_first(input: &str) -> Option<usize> {
        let bytes = input.as_bytes();
        let word: u32 = match bytes.len() {
            0 => return None,
            1 => u32::from(bytes[0]) << 24,
            2 => (u32::from(bytes[0]) << 24) | (u32::from(bytes[1]) << 16),
            3 => (u32::from(bytes[0]) << 24) | (u32::from(bytes[1]) << 16) | (u32::from(bytes[2]) << 8),
            _ => (u32::from(bytes[0]) << 24) | (u32::from(bytes[1]) << 16) | (u32::from(bytes[2]) << 8) | u32::from(bytes[3]),
        };
        match word {
            0x3A_000000..=0x3A_FFFFFF => Some(1), /* ":" */
            0x41_000000..=0x5A_FFFFFF => Some(1), /* [A-Z] */
            0x5F_000000..=0x5F_FFFFFF => Some(1), /* "_" */
            0x61_000000..=0x7A_FFFFFF => Some(1), /* [a-z] */
            0xC380_0000..=0xC396_FFFF => Some(2), /* Two-byte UTF-8 (U+00C0–U+00D6) */
            0xC398_0000..=0xC3B6_FFFF => Some(2), /* Two-byte UTF-8 (U+00D8–U+00F6) */
            0xC3B8_0000..=0xCBBF_FFFF => Some(2), /* Two-byte UTF-8 (U+00F8–U+02FF) */
            0xCDB0_0000..=0xCDBD_FFFF => Some(2), /* Two-byte UTF-8 (U+0370–U+037D) */
            0xCDBF_0000..=0xDFBF_FFFF => Some(2), /* Two-byte UTF-8 (U+037F–U+07FF) */
            0xE0A080_00..=0xE1BFBF_FF => Some(3), /* Three-byte UTF-8 (U+0800–U+1FFF) */
            0xE2808C_00..=0xE2808D_FF => Some(3), /* Three-byte UTF-8 (U+200C–U+200D) */
            0xE281B0_00..=0xE2868F_FF => Some(3), /* Three-byte UTF-8 (U+2070–U+218F) */
            0xE2B080_00..=0xE2BFAF_FF => Some(3), /* Three-byte UTF-8 (U+2C00–U+2FEF) */
            0xE38081_00..=0xED9FBF_FF => Some(3), /* Three-byte UTF-8 (U+3001–U+D7FF) */
            0xEFA480_00..=0xEFB78F_FF => Some(3), /* Three-byte UTF-8 (U+F900–U+FDCF) */
            0xEFB7B0_00..=0xEFBFBD_FF => Some(3), /* Three-byte UTF-8 (U+FDF0–U+FFFD) */
            0xF0908080_..=0xF3AFBFBF_ => Some(4), /* Four-byte UTF-8 (U+10000–U+EFFFF) */
            _ => None,
        }
    }
}

/// [13] Public Id Character
///
/// https://www.w3.org/TR/xml/#NT-PubidChar
pub struct PubidChar;

impl CharacterSet for PubidChar {
    fn match_first(input: &str) -> Option<usize> {
        match input.as_bytes().first()? {
            0x20 | 0x0D | 0x0A => Some(1),
            0x41..=0x5A | 0x61..=0x7A | 0x30..=0x39 => Some(1),
            0x23..=0x25 => Some(1),
            0x27..=0x2F => Some(1),
            0x3A | 0x3B | 0x3D | 0x3F | 0x40 => Some(1),
            0x5F => Some(1),
            _ => None,
        }
    }
}

/// Alphabetical Character set.
///
/// Only contains a-z and A-Z.
pub struct LatinAlphabet;

impl CharacterSet for LatinAlphabet {
    fn match_first(input: &str) -> Option<usize> {
        match input.as_bytes().first()? {
            0x41..=0x5A | 0x61..=0x7A => Some(1),
            _ => None,
        }
    }
}

pub struct ExtendedLatinAlphabet;

impl CharacterSet for ExtendedLatinAlphabet {
    fn match_first(input: &str) -> Option<usize> {
        match input.as_bytes().first()? {
            0x30..=0x39 | 0x41..=0x5A | 0x61..=0x7A => Some(1),
            0x2D | 0x2E | 0x5F => Some(1),
            _ => None,
        }
    }
}

/// Parse the next literal from a given charset.
///

/// Expect a string literal.
///
/// The first character is from the `First` char set.
/// The rest of the string is from the `Rest` charset.
///
/// This will only fail if the first encounterd character is not in the First char set.
pub fn expect_string<'src, First: CharacterSet, Rest: CharacterSet>(input: &mut &'src str) -> Result<&'src str, String> {
    let start = *input;
    let mut length = First::match_first(input).ok_or_else(|| format!("First char not from character set"))?;
    while let Some(additional) = Rest::match_first(input) {
        length += additional;
    }
    Ok(&start[..length])
}

/// Advance the given input string to skip any number of spaces as defined
/// in the XML documentation: https://www.w3.org/TR/xml/#NT-S
///
/// The function returns the number of character / bytes skipped.
/// Since all space charaters are one byte, the skipped bytes and skipped chars are the same.
pub fn skip_whitespaces(input: &mut &str) -> usize {
    let mut result = 0;
    loop {
        match input.as_bytes().first() {
            Some(0x20 /* Space */)
            | Some(0x09 /* Tabulation */)
            | Some(0x0D /* New line */)
            | Some(0x0A /* Carriage return */) => {
                *input = &input[1..];
                result += 1;
            }
            _ => break,
        }
    }
    result
}

/// Skip the whitespaces, expecting to find at least one.
///
/// If no whitespaces are encountered, will return an error.
pub fn expect_whitespaces(input: &mut &str) -> Result<usize, String> {
    match skip_whitespaces(input) {
        0 => Err(format!("Expected whitespaces")),
        more => Ok(more),
    }
}

/// Expects a fixed byte sequence, or throws an error.
pub fn expect_bytes(input: &mut &str, expected: &str) -> Result<(), String> {
    *input = input
        .strip_prefix(expected)
        .ok_or_else(|| format!("Expected {}, found {}", expected, &input[..expected.len().min(input.len())]))?;
    Ok(())
}

/// Expect the "XML" literal, where any of the three letters can be either uppercased or lowercased.
pub fn is_litteral_xml(input: &str) -> bool {
    let bytes = input.as_bytes();
    if bytes.len() != 3 {
        return false;
    }
    match bytes[..3] {
        [0x58 | 0x78, 0x4D | 0x6D, 0x4C | 0x6C] => true,
        _ => false,
    }
}
