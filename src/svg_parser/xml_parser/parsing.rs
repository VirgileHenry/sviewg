/// Advance the given input string to skip any number of spaces as defined
/// in the XML documentation: https://www.w3.org/TR/xml/#NT-S
///
/// The function returns the number of chacarter / bytes skipped.
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

pub fn expect_whitespaces(input: &mut &str) -> Result<usize, String> {
    match skip_whitespaces(input) {
        0 => Err(format!("Expected whitespaces")),
        more => Ok(more),
    }
}

/// Expect to parse any quote kind, and return the quote kind parsed.
pub fn expect_quoted_litteral<'src>(input: &mut &'src str) -> Result<&'src str, String> {
    let quote_kind = match input.as_bytes().first() {
        Some(0x22 /* Double quotes */) => {
            *input = &input[1..];
            '"'
        }
        Some(0x27 /* Single quote */) => {
            *input = &input[1..];
            '\''
        }
        _ => return Err(format!("Expected \"\"\", \"'\"")),
    };
    let next_quote_pos = input
        .find(quote_kind)
        .ok_or_else(|| format!("Unable to find closing quote for {quote_kind}"))?;
    let (quoted, rest) = input.split_at(next_quote_pos);
    /* Skip the quote, therefore we take the rest at 1.. */
    *input = &rest[1..];
    Ok(quoted)
}

/// Expects a fixed byte sequence, or throws an error.
pub fn expect_bytes(input: &mut &str, expected: &str) -> Result<(), String> {
    *input = input
        .strip_prefix(expected)
        .ok_or_else(|| format!("Expected {}, found {}", expected, &input[..expected.len().min(input.len())]))?;
    Ok(())
}

/// Expect a fixed byte sequence, removing any whitespace before it.
pub fn expect_whitespaces_bytes(input: &mut &str, expected: &str) -> Result<(), String> {
    skip_whitespaces(input);
    expect_bytes(input, expected)
}

/// Function to check if a given byte sequence is a valid XML character.
/// The function also returns the number of bytes the character takes.
///
/// The characters are UTF-8, so we store them in a 32 bit integer, and match against that.
///
/// The valid characters are given at https://www.w3.org/TR/xml/#NT-Char
fn expect_xml_char(input: &mut &str) -> Option<usize> {
    let bytes = input.as_bytes();
    let word: u32 = match bytes.len() {
        0 => return None,
        1 => u32::from(bytes[0]) << 24,
        2 => (u32::from(bytes[0]) << 24) | (u32::from(bytes[1]) << 16),
        3 => (u32::from(bytes[0]) << 24) | (u32::from(bytes[1]) << 16) | (u32::from(bytes[2]) << 8),
        _ => (u32::from(bytes[0]) << 24) | (u32::from(bytes[1]) << 16) | (u32::from(bytes[2]) << 8) | u32::from(bytes[3]),
    };
    let byte_count = match word {
        0x09_000000..=0x09_FFFFFF => 1, /* Single point \t */
        0x0A_000000..=0x0A_FFFFFF => 1, /* Single point \n */
        0x0D_000000..=0x0D_FFFFFF => 1, /* Single point \r */
        0x20_000000..=0x7F_FFFFFF => 1, /* ASCII visible chars */
        0xC280_0000..=0xDFBF_FFFF => 2, /* Two-byte UTF-8 (U+0080–U+07FF) */
        0xE0A080_00..=0xED9FBF_FF => 3, /* Three-byte UTF-8 (U+0800–U+D7FF) */
        0xEE8080_00..=0xEFBFBF_FF => 3, /* Three-byte UTF-8 (U+E000–U+FFFD) */
        0xF0908080_..=0xF48FBFBF_ => 4, /* Four-byte UTF-8 (U+10000–U+10FFFF) */
        _ => return None,
    };
    *input = &input[byte_count..];
    Some(byte_count)
}

/// Function to check if a byte sequence is a valid character for the start of an XML name.
/// On Success, the function will return the number of bytes used by the character.
///
/// The characters are UTF-8, so we store them in a 32 bit integer, and match against that.
///
/// https://www.w3.org/TR/xml/#NT-Name
fn expect_xml_start_name_char(input: &mut &str) -> Option<usize> {
    let bytes = input.as_bytes();
    let word: u32 = match bytes.len() {
        0 => return None,
        1 => u32::from(bytes[0]) << 24,
        2 => (u32::from(bytes[0]) << 24) | (u32::from(bytes[1]) << 16),
        3 => (u32::from(bytes[0]) << 24) | (u32::from(bytes[1]) << 16) | (u32::from(bytes[2]) << 8),
        _ => (u32::from(bytes[0]) << 24) | (u32::from(bytes[1]) << 16) | (u32::from(bytes[2]) << 8) | u32::from(bytes[3]),
    };
    let byte_count = match word {
        0x3A_000000..=0x3A_FFFFFF => 1, /* ":" */
        0x41_000000..=0x5A_FFFFFF => 1, /* [A-Z] */
        0x5F_000000..=0x5F_FFFFFF => 1, /* "_" */
        0x61_000000..=0x7A_FFFFFF => 1, /* [a-z] */
        0xC380_0000..=0xC396_FFFF => 2, /* Two-byte UTF-8 (U+00C0–U+00D6) */
        0xC398_0000..=0xC3B6_FFFF => 2, /* Two-byte UTF-8 (U+00D8–U+00F6) */
        0xC3B8_0000..=0xCBBF_FFFF => 2, /* Two-byte UTF-8 (U+00F8–U+02FF) */
        0xCDB0_0000..=0xCDBD_FFFF => 2, /* Two-byte UTF-8 (U+0370–U+037D) */
        0xCDBF_0000..=0xDFBF_FFFF => 2, /* Two-byte UTF-8 (U+037F–U+07FF) */
        0xE0A080_00..=0xE1BFBF_FF => 3, /* Three-byte UTF-8 (U+0800–U+1FFF) */
        0xE2808C_00..=0xE2808D_FF => 3, /* Three-byte UTF-8 (U+200C–U+200D) */
        0xE281B0_00..=0xE2868F_FF => 3, /* Three-byte UTF-8 (U+2070–U+218F) */
        0xE2B080_00..=0xE2BFAF_FF => 3, /* Three-byte UTF-8 (U+2C00–U+2FEF) */
        0xE38081_00..=0xED9FBF_FF => 3, /* Three-byte UTF-8 (U+3001–U+D7FF) */
        0xEFA480_00..=0xEFB78F_FF => 3, /* Three-byte UTF-8 (U+F900–U+FDCF) */
        0xEFB7B0_00..=0xEFBFBD_FF => 3, /* Three-byte UTF-8 (U+FDF0–U+FFFD) */
        0xF0908080_..=0xF3AFBFBF_ => 4, /* Four-byte UTF-8 (U+10000–U+EFFFF) */
        _ => return None,
    };
    *input = &input[byte_count..];
    Some(byte_count)
}

/// Function to check if a byte sequence is a valid character for an XML name.
/// On Success, the function will return the number of bytes used by the character.
///
/// The characters are UTF-8, so we store them in a 32 bit integer, and match against that.
///
/// https://www.w3.org/TR/xml/#NT-Name
fn expect_xml_name_char(input: &mut &str) -> Option<usize> {
    let bytes = input.as_bytes();
    let word: u32 = match bytes.len() {
        0 => return None,
        1 => u32::from(bytes[0]) << 24,
        2 => (u32::from(bytes[0]) << 24) | (u32::from(bytes[1]) << 16),
        3 => (u32::from(bytes[0]) << 24) | (u32::from(bytes[1]) << 16) | (u32::from(bytes[2]) << 8),
        _ => (u32::from(bytes[0]) << 24) | (u32::from(bytes[1]) << 16) | (u32::from(bytes[2]) << 8) | u32::from(bytes[3]),
    };
    let byte_count = match word {
        0x3A_000000..=0x3A_FFFFFF => 1, /* ":" */
        0x41_000000..=0x5A_FFFFFF => 1, /* [A-Z] */
        0x5F_000000..=0x5F_FFFFFF => 1, /* "_" */
        0x61_000000..=0x7A_FFFFFF => 1, /* [a-z] */
        0x2D_000000..=0x2D_FFFFFF => 1, /* "-" */
        0x2E_000000..=0x2E_FFFFFF => 1, /* "." */
        0x30_000000..=0x39_FFFFFF => 1, /* [0-9] */
        0xC380_0000..=0xC396_FFFF => 2, /* Two-byte UTF-8 (U+00C0–U+00D6) */
        0xC398_0000..=0xC3B6_FFFF => 2, /* Two-byte UTF-8 (U+00D8–U+00F6) */
        0xC3B8_0000..=0xCBBF_FFFF => 2, /* Two-byte UTF-8 (U+00F8–U+02FF) */
        0xCDB0_0000..=0xCDBD_FFFF => 2, /* Two-byte UTF-8 (U+0370–U+037D) */
        0xCDBF_0000..=0xDFBF_FFFF => 2, /* Two-byte UTF-8 (U+037F–U+07FF) */
        0xC2B7_0000..=0xC2B7_FFFF => 2, /* Two-byte UTF-8 (U+00B7) */
        0xCC80_0000..=0xCDAF_FFFF => 2, /* Two-byte UTF-8 (U+0300–U+036F) */
        0xE0A080_00..=0xE1BFBF_FF => 3, /* Three-byte UTF-8 (U+0800–U+1FFF) */
        0xE2808C_00..=0xE2808D_FF => 3, /* Three-byte UTF-8 (U+200C–U+200D) */
        0xE281B0_00..=0xE2868F_FF => 3, /* Three-byte UTF-8 (U+2070–U+218F) */
        0xE2B080_00..=0xE2BFAF_FF => 3, /* Three-byte UTF-8 (U+2C00–U+2FEF) */
        0xE38081_00..=0xED9FBF_FF => 3, /* Three-byte UTF-8 (U+3001–U+D7FF) */
        0xEFA480_00..=0xEFB78F_FF => 3, /* Three-byte UTF-8 (U+F900–U+FDCF) */
        0xEFB7B0_00..=0xEFBFBD_FF => 3, /* Three-byte UTF-8 (U+FDF0–U+FFFD) */
        0xF0908080_..=0xF3AFBFBF_ => 4, /* Four-byte UTF-8 (U+10000–U+EFFFF) */
        0xE280BF_00..=0xE28180_FF => 3, /* Three-byte UTF-8 (U+203F–U+2040) */
        _ => return None,
    };
    *input = &input[byte_count..];
    Some(byte_count)
}

/// Function to parsse an XML name from the given input.
/// A name is composed of a name start character, followed by any number of name characters.
/// The function will only fail if the first character is not a name start character.
///
/// https://www.w3.org/TR/xml/#NT-Name
pub fn expect_name<'src>(input: &mut &'src str) -> Result<&'src str, String> {
    let start = *input;
    let mut name_length = expect_xml_start_name_char(input).ok_or_else(|| format!("Invalid start of name"))?;
    while let Some(byte_count) = expect_xml_name_char(input) {
        name_length += byte_count;
    }
    Ok(&start[..name_length])
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

/// Ensure all characters in the given input are all valid pubid characters.
///
/// https://www.w3.org/TR/xml/#NT-PubidChar
pub fn ensure_pid_chars(input: &str) -> Result<(), String> {
    for byte in input.as_bytes().iter() {
        match byte {
            0x20 | 0x0D | 0x0A => { /* new line, carriage return, space */ }
            0x41..=0x5A | 0x61..=0x7A | 0x30..=0x39 => { /* a-zA-Z0-9 */ }
            0x23..=0x25 => { /* #$% */ }
            0x27..=0x2F => { /* '()*+,-./ */ }
            0x3A | 0x3B | 0x3D | 0x3F | 0x40 => { /* :;=?@ */ }
            0x5F => { /* _ */ }
            other => return Err(format!("Unexpected character {} in pid literal", char::from(*other))),
        }
    }
    Ok(())
}
