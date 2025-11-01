mod parsing;
use std::fmt::Write;

pub use parsing::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuoteKind {
    Single,
    Double,
}

impl QuoteKind {
    fn parse(input: &mut &str) -> Result<Self, String> {
        match input.as_bytes().first() {
            Some(0x22) => {
                *input = &input[1..];
                Ok(QuoteKind::Double)
            }
            Some(0x27) => {
                *input = &input[1..];
                Ok(QuoteKind::Single)
            }
            Some(other) => Err(format!("Unexpected char for quote: {}", char::from(*other))),
            None => Err(format!("Unexpected char for quote: EOF")),
        }
    }
    fn char(self) -> char {
        match self {
            QuoteKind::Single => '\'',
            QuoteKind::Double => '"',
        }
    }
}

impl std::fmt::Display for QuoteKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char(self.char())
    }
}

/// Repetition modifiers, a special set of characters that are used in element definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RepetitionOperator {
    /// Zero or one element, the '?' repetition operator.
    ZeroOrOne,
    /// Zero or more element, the '*' repetition operator.
    ZeroOrMore,
    /// One or more element, the '+' repetition operator.
    OneOrMore,
}

impl RepetitionOperator {
    fn try_parse(input: &mut &str) -> Option<Self> {
        match input.as_bytes().first() {
            Some(0x3F) => {
                *input = &input[1..];
                Some(RepetitionOperator::ZeroOrOne)
            }
            Some(0x2A) => {
                *input = &input[1..];
                Some(RepetitionOperator::ZeroOrMore)
            }
            Some(0x2B) => {
                *input = &input[1..];
                Some(RepetitionOperator::OneOrMore)
            }
            _ => None,
        }
    }
    fn char(self) -> char {
        match self {
            RepetitionOperator::ZeroOrOne => '?',
            RepetitionOperator::ZeroOrMore => '*',
            RepetitionOperator::OneOrMore => '+',
        }
    }
}

impl std::fmt::Display for RepetitionOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char(self.char())
    }
}

trait XmlElement<'src>: Sized {
    fn parse(input: &mut &'src str) -> Result<Self, String>;
    fn write<W: std::io::Write>(&self, output: &mut W) -> std::io::Result<()>;
}

/// [11] - System Literal
///
/// https://www.w3.org/TR/xml/#NT-SystemLiteral
pub struct SystemLiteral<'src> {
    literal: &'src str,
    quote: QuoteKind,
}

impl<'src> XmlElement<'src> for SystemLiteral<'src> {
    fn parse(input: &mut &'src str) -> Result<Self, String> {
        let quote = QuoteKind::parse(input)?;
        let next_quote_pos = input.find(quote.char()).ok_or_else(|| format!("Unclosed literal"))?;
        let (literal, rest) = input.split_at(next_quote_pos);
        // fixme: check literal is legal characters only
        *input = &rest[1..];
        Ok(Self { literal, quote })
    }
    fn write<W: std::io::Write>(&self, output: &mut W) -> std::io::Result<()> {
        write!(output, "{}{}{}", self.quote, self.literal, self.quote)
    }
}

/// [12] - Public Id Literal
///
/// https://www.w3.org/TR/xml/#NT-PubidLiteral
pub struct PubidLiteral<'src> {
    literal: &'src str,
    quote: QuoteKind,
}

impl<'src> XmlElement<'src> for PubidLiteral<'src> {
    fn parse(input: &mut &'src str) -> Result<Self, String> {
        let quote = QuoteKind::parse(input)?;
        let next_quote_pos = input.find(quote.char()).ok_or_else(|| format!("Unclosed literal"))?;
        let (literal, rest) = input.split_at(next_quote_pos);
        ensure_pid_chars(literal)?;
        *input = &rest[1..];
        Ok(Self { literal, quote })
    }
    fn write<W: std::io::Write>(&self, output: &mut W) -> std::io::Result<()> {
        write!(output, "{}{}{}", self.quote, self.literal, self.quote)
    }
}

/// Prolog of a xml document. Contains information about the version, content, etc.
///
/// https://www.w3.org/TR/xml/#sec-prolog-dtd
pub struct Prolog<'src> {
    /// The first element of the prolog is the declaration, containging version, encoding, etc.
    declaration: Option<Declaration<'src>>,
    /// After the declaration, there can be any number of misc elements.
    misc: Vec<Miscellaneous<'src>>,
}

impl<'src> Prolog<'src> {
    fn parse(input: &mut &'src str) -> Result<Self, String> {
        /* Optionnal XML declaration */
        let declaration = if input.starts_with(Declaration::OPENING_TAG) {
            Some(Declaration::parse(input)?)
        } else {
            None
        };

        /* Followed by any number of Xml Miscellaneous */
        let mut misc = Vec::new();
        loop {
            skip_whitespaces(input);
            if input.starts_with(Comment::OPENING_TAG) || input.starts_with(ProcessingInstruction::OPENING_TAG) {
                misc.push(Miscellaneous::parse(input)?);
            } else {
                break;
            }
        }

        /* Optionnaly we can have a doctypedecl */

        Ok(Self { declaration, misc })
    }
}

/// XML declaration tag, optionnal at the start of a xml file.
///
/// https://www.w3.org/TR/xml/#NT-XMLDecl
pub struct Declaration<'src> {
    /// Version of XML used for this file.
    /// https://www.w3.org/TR/xml/#NT-VersionInfo
    version: Version,
    /// Character encoding in entities.
    /// https://www.w3.org/TR/xml/#NT-EncodingDecl
    /// This can later be replaced by an enum with different possible encodings.
    encoding: Option<&'src str>,
    /// Standalone document declaration. 'yes' is true, 'no' is false.
    /// https://www.w3.org/TR/xml/#NT-SDDecl
    standalone: Option<bool>,
}

impl<'src> Declaration<'src> {
    const OPENING_TAG: &'static str = "<?xml";
    const CLOSING_TAG: &'static str = "?>";

    fn parse(input: &mut &'src str) -> Result<Self, String> {
        expect_whitespaces_bytes(input, Self::OPENING_TAG)?;
        /* Parse the version */
        let version = Version::parse(input)?;

        /* Parse encoding if present */
        skip_whitespaces(input);
        let encoding = match input.strip_prefix("encoding") {
            Some(stripped) => {
                *input = stripped;
                expect_whitespaces_bytes(input, "=")?;
                skip_whitespaces(input);
                Some(expect_quoted_litteral(input)?)
            }
            None => None,
        };

        /* Parse standalone if present */
        skip_whitespaces(input);
        let standalone = match input.strip_prefix("standalone") {
            Some(stripped) => {
                *input = stripped;
                expect_whitespaces_bytes(input, "=")?;
                skip_whitespaces(input);
                let standalone = match expect_quoted_litteral(input)? {
                    "yes" => true,
                    "no" => true,
                    other => return Err(format!("Invalid standalone value: {other}")),
                };
                Some(standalone)
            }
            None => None,
        };

        expect_whitespaces_bytes(input, Self::CLOSING_TAG)?;

        Ok(Self {
            version,
            encoding,
            standalone,
        })
    }
}

/// Version info present in the XML declaration tag.
///
/// https://www.w3.org/TR/xml/#NT-VersionInfo
pub struct Version {
    /// Parsed major of the version.
    major: usize,
    /// Parsed minor of the version.
    minor: usize,
}

impl Version {
    fn parse(input: &mut &str) -> Result<Self, String> {
        /* hard parse the start part */
        expect_whitespaces_bytes(input, "version")?;
        expect_whitespaces_bytes(input, "=")?;
        skip_whitespaces(input);
        let version = expect_quoted_litteral(input)?;
        let (major, minor) = match version.split('.').collect::<Vec<_>>().as_slice() {
            [major, minor] => (
                major.parse().map_err(|e| format!("Failed to parse major \"{major}\": {e}"))?,
                minor.parse().map_err(|e| format!("Failed to parse minor \"{minor}\": {e}"))?,
            ),
            _ => return Err(format!("Invalid version: {version}")),
        };

        Ok(Self { major, minor })
    }
}

/// [15] - Comment
///
/// https://www.w3.org/TR/xml/#NT-Comment
pub struct Comment<'src> {
    /// reference to the comment in the original source file.
    comment: &'src str,
}

impl<'src> Comment<'src> {
    const OPENING_TAG: &'static str = "<!--";
    const CLOSING_TAG: &'static str = "-->";
}

impl<'src> XmlElement<'src> for Comment<'src> {
    fn parse(input: &mut &'src str) -> Result<Self, String> {
        expect_whitespaces_bytes(input, Self::OPENING_TAG)?;
        let comment_end = input.find(Self::CLOSING_TAG).ok_or_else(|| format!("Unclosed comment"))?;
        let (comment, rest) = input.split_at(comment_end);
        *input = &rest[Self::CLOSING_TAG.len()..];
        Ok(Self { comment })
    }
    fn write<W: std::io::Write>(&self, output: &mut W) -> std::io::Result<()> {
        write!(output, "{}{}{}", Self::OPENING_TAG, self.comment, Self::CLOSING_TAG)
    }
}

/// [16] - Processing Instruction (PI)
///
/// https://www.w3.org/TR/xml/#NT-PI
pub struct ProcessingInstruction<'src> {
    target: &'src str,
    instruction: Option<&'src str>,
}

impl<'src> ProcessingInstruction<'src> {
    const OPENING_TAG: &'static str = "<?";
    const CLOSING_TAG: &'static str = "?>";
}

impl<'src> XmlElement<'src> for ProcessingInstruction<'src> {
    fn parse(input: &mut &'src str) -> Result<Self, String> {
        expect_bytes(input, Self::OPENING_TAG)?;
        let target = expect_name(input)?;
        if is_litteral_xml(target) {
            return Err(format!("Target can't be \"XML\""));
        }

        let instruction = if input.starts_with(Self::CLOSING_TAG) {
            None /* Got closing delimiter, no instruction */
        } else {
            skip_whitespaces(input);
            let instruction_end = input.find(Self::CLOSING_TAG).ok_or_else(|| format!("Unclosed PI"))?;
            let (instruction, rest) = input.split_at(instruction_end);
            *input = &rest[Self::CLOSING_TAG.len()..];
            Some(instruction)
        };

        Ok(Self { target, instruction })
    }
    fn write<W: std::io::Write>(&self, output: &mut W) -> std::io::Result<()> {
        match self.instruction {
            None => write!(output, "{}{}{}", Self::OPENING_TAG, self.target, Self::CLOSING_TAG),
            Some(instruction) => write!(
                output,
                "{}{} {}{}",
                Self::OPENING_TAG,
                self.target,
                instruction,
                Self::CLOSING_TAG
            ),
        }
    }
}

/// [27] - Miscellaneous (Misc)
///
/// https://www.w3.org/TR/xml/#NT-Misc
pub enum Miscellaneous<'src> {
    Comment(Comment<'src>),
    Pi(ProcessingInstruction<'src>),
}

impl<'src> XmlElement<'src> for Miscellaneous<'src> {
    fn parse(input: &mut &'src str) -> Result<Self, String> {
        if input.starts_with(Comment::OPENING_TAG) {
            Ok(Miscellaneous::Comment(Comment::parse(input)?))
        } else if input.starts_with(ProcessingInstruction::OPENING_TAG) {
            Ok(Miscellaneous::Pi(ProcessingInstruction::parse(input)?))
        } else {
            Err(format!("Not a comment or PI"))
        }
    }
    fn write<W: std::io::Write>(&self, output: &mut W) -> std::io::Result<()> {
        match self {
            Self::Comment(comment) => comment.write(output),
            Self::Pi(pi) => pi.write(output),
        }
    }
}

/// [28] - Doctype Declaration
///
/// https://www.w3.org/TR/xml/#NT-doctypedecl
pub struct DoctypeDecl<'src> {
    name: &'src str,
    external_id: Option<ExternalId<'src>>,
    int_subset: Option<IntSubset<'src>>,
}

impl<'src> DoctypeDecl<'src> {
    const OPENING_TAG: &'static str = "<!DOCTYPE";
    const CLOSING_TAG: &'static str = ">";
}

impl<'src> XmlElement<'src> for DoctypeDecl<'src> {
    fn parse(input: &mut &'src str) -> Result<Self, String> {
        expect_bytes(input, Self::OPENING_TAG)?;
        skip_whitespaces(input);
        let name = expect_name(input)?;
        skip_whitespaces(input);
        let external_id = if input.starts_with(ExternalId::SYSTEM_TAG) || input.starts_with(ExternalId::PUBLIC_TAG) {
            Some(ExternalId::parse(input)?)
        } else {
            None
        };
        skip_whitespaces(input);
        let int_subset = if input.starts_with("[") {
            expect_bytes(input, "[")?;
            let subset = IntSubset::parse(input)?;
            expect_bytes(input, "]")?;
            skip_whitespaces(input);
            Some(subset)
        } else {
            None
        };
        expect_bytes(input, Self::CLOSING_TAG)?;
        Ok(Self {
            name,
            external_id,
            int_subset,
        })
    }
    fn write<W: std::io::Write>(&self, output: &mut W) -> std::io::Result<()> {
        write!(output, "{} {}", Self::OPENING_TAG, self.name)?;
        if let Some(external_id) = &self.external_id {
            write!(output, " ")?;
            external_id.write(output)?;
        }
        write!(output, " ")?;
        if let Some(int_subset) = &self.int_subset {
            write!(output, "[")?;
            int_subset.write(output)?;
            write!(output, "] ")?;
        }
        write!(output, "{}", Self::CLOSING_TAG)
    }
}

/// [28a] - Declaration Separator
///
/// https://www.w3.org/TR/xml/#NT-DeclSep
pub enum DeclSeparator<'src> {
    PeReference(ParameterEntityReference<'src>),
    Space,
}

impl<'src> DeclSeparator<'src> {
    fn parse(input: &mut &'src str) -> Result<Self, String> {
        if input.starts_with(ParameterEntityReference::OPENING_TAG) {
            Ok(Self::PeReference(ParameterEntityReference::parse(input)?))
        } else {
            expect_whitespaces(input)?;
            Ok(Self::Space)
        }
    }
}

/// [28b] - Int Subset
///
/// https://www.w3.org/TR/xml/#NT-intSubset
pub struct IntSubset<'src> {
    elements: Vec<IntSubsetElement<'src>>,
}

impl<'src> XmlElement<'src> for IntSubset<'src> {
    fn parse(input: &mut &'src str) -> Result<Self, String> {
        unimplemented!()
    }
    fn write<W: std::io::Write>(&self, output: &mut W) -> std::io::Result<()> {
        unimplemented!()
    }
}

pub enum IntSubsetElement<'src> {
    MarkupDecl(MarkupDeclaration<'src>),
    DeclSep(DeclSeparator<'src>),
}

/// [29] - Markup Declaration
///
/// https://www.w3.org/TR/xml/#NT-markupdecl
pub enum MarkupDeclaration<'src> {
    ElementDeclaration(ElementDeclaration<'src>),
    Pi(ProcessingInstruction<'src>),
    Comment(Comment<'src>),
}

impl<'src> XmlElement<'src> for MarkupDeclaration<'src> {
    fn parse(input: &mut &'src str) -> Result<Self, String> {
        if input.starts_with(ElementDeclaration::OPENING_TAG) {
            Ok(Self::ElementDeclaration(ElementDeclaration::parse(input)?))
        } else if input.starts_with(ProcessingInstruction::OPENING_TAG) {
            Ok(Self::Pi(ProcessingInstruction::parse(input)?))
        } else if input.starts_with(Comment::OPENING_TAG) {
            Ok(Self::Comment(Comment::parse(input)?))
        } else {
            Err(format!("Expected markup declaration"))
        }
    }
    fn write<W: std::io::Write>(&self, output: &mut W) -> std::io::Result<()> {
        match self {
            MarkupDeclaration::ElementDeclaration(element) => element.write(output),
            MarkupDeclaration::Pi(pi) => pi.write(output),
            MarkupDeclaration::Comment(comment) => comment.write(output),
        }
    }
}

/// [45] - Element declaration.
///
/// https://www.w3.org/TR/xml/#NT-elementdecl
pub struct ElementDeclaration<'src> {
    name: &'src str,
    content_spec: ContentSpec<'src>,
}

impl<'src> ElementDeclaration<'src> {
    const OPENING_TAG: &'static str = "<!ELEMENT";
    const CLOSING_TAG: &'static str = ">";
}

impl<'src> XmlElement<'src> for ElementDeclaration<'src> {
    fn parse(input: &mut &'src str) -> Result<Self, String> {
        expect_bytes(input, Self::OPENING_TAG)?;
        expect_whitespaces(input)?;
        let name = expect_name(input)?;
        expect_whitespaces(input)?;
        let content_spec = ContentSpec::parse(input)?;
        skip_whitespaces(input);
        expect_bytes(input, Self::CLOSING_TAG)?;
        Ok(Self { name, content_spec })
    }
    fn write<W: std::io::Write>(&self, output: &mut W) -> std::io::Result<()> {
        write!(output, "{} {} ", Self::OPENING_TAG, self.name)?;
        self.content_spec.write(output)?;
        write!(output, "{}", Self::CLOSING_TAG)
    }
}

/// [46] - Content Specification
///
/// https://www.w3.org/TR/xml/#NT-contentspec
pub enum ContentSpec<'src> {
    Empty,
    Any,
    Mixed(),
    Children(ElementContentChildren<'src>),
}

impl<'src> XmlElement<'src> for ContentSpec<'src> {
    fn parse(input: &mut &'src str) -> Result<Self, String> {
        if let Some(prefixed) = input.strip_prefix("EMPTY") {
            *input = prefixed;
            Ok(Self::Empty)
        } else if let Some(prefixed) = input.strip_prefix("ANY") {
            *input = prefixed;
            Ok(Self::Any)
        } else {
            // Fixme
            unimplemented!()
        }
    }
    fn write<W: std::io::Write>(&self, output: &mut W) -> std::io::Result<()> {
        match self {
            ContentSpec::Empty => output.write_all("EMPTY".as_bytes()),
            ContentSpec::Any => output.write_all("ANY".as_bytes()),
            ContentSpec::Mixed() => unimplemented!(),
            ContentSpec::Children(children) => children.write(output),
        }
    }
}

/// [47] - Children
///
/// https://www.w3.org/TR/xml/#NT-children
pub enum ElementContentChildren<'src> {
    Choice {
        choice: ElementContentChoice<'src>,
        repetition: Option<RepetitionOperator>,
    },
    Seq {
        seq: ElementContentSeq<'src>,
        repetition: Option<RepetitionOperator>,
    },
}

impl<'src> XmlElement<'src> for ElementContentChildren<'src> {
    fn parse(input: &mut &'src str) -> Result<Self, String> {
        expect_bytes(input, "(")?;
        skip_whitespaces(input);
        /* Fixme: will be moved into a vec anyway ? maybe something to gain here */
        let mut cps = Vec::new();
        cps.push(ElementContentParticle::parse(input)?);
        skip_whitespaces(input);
        match input.as_bytes().first() {
            /* Closing parens right after the first elem, it's a one element sequence */
            Some(0x29) => {
                *input = &input[1..];
                let repetition = RepetitionOperator::try_parse(input);
                Ok(Self::Seq {
                    seq: ElementContentSeq { sequence: cps },
                    repetition,
                })
            }
            /* A comma indicates a sequence of more than one element */
            Some(0x2C) => loop {
                expect_bytes(input, ",")?;
                skip_whitespaces(input);
                cps.push(ElementContentParticle::parse(input)?);
                skip_whitespaces(input);
                /* If we have a closing parens, terminate the sequence */
                if input.as_bytes().first().cloned() == Some(0x29) {
                    *input = &input[1..];
                    let repetition = RepetitionOperator::try_parse(input);
                    break Ok(Self::Seq {
                        seq: ElementContentSeq { sequence: cps },
                        repetition,
                    });
                }
                /* Otherwise, keep munching at the sequence */
            },
            /* A vertical bar indicate a choice of multiple elements */
            Some(0x7C) => loop {
                expect_bytes(input, ",")?;
                skip_whitespaces(input);
                cps.push(ElementContentParticle::parse(input)?);
                skip_whitespaces(input);
                /* If we have a closing parens, terminate the sequence */
                if input.as_bytes().first().cloned() == Some(0x29) {
                    *input = &input[1..];
                    let repetition = RepetitionOperator::try_parse(input);
                    break Ok(Self::Choice {
                        choice: ElementContentChoice { choices: cps },
                        repetition,
                    });
                }
                /* Otherwise, keep munching at the sequence */
            },
            _ => Err(format!("Ecpected sequence or choice")),
        }
    }
    fn write<W: std::io::Write>(&self, output: &mut W) -> std::io::Result<()> {
        match self {
            ElementContentChildren::Choice { choice, repetition } => {
                choice.write(output)?;
                if let Some(repetition) = repetition {
                    write!(output, "{repetition}")?;
                }
                Ok(())
            }
            ElementContentChildren::Seq { seq, repetition } => {
                seq.write(output)?;
                if let Some(repetition) = repetition {
                    write!(output, "{repetition}")?;
                }
                Ok(())
            }
        }
    }
}

/// [48] - Content Particle
///
/// https://www.w3.org/TR/xml/#NT-cp
pub enum ElementContentParticle<'src> {
    Name {
        name: &'src str,
        repetition: Option<RepetitionOperator>,
    },
    Choice {
        choice: ElementContentChoice<'src>,
        repetition: Option<RepetitionOperator>,
    },
    Seq {
        seq: ElementContentSeq<'src>,
        repetition: Option<RepetitionOperator>,
    },
}

impl<'src> XmlElement<'src> for ElementContentParticle<'src> {
    fn parse(input: &mut &'src str) -> Result<Self, String> {
        if input.starts_with('(') {
            /* Since a content particle that is not a name is basically a children, use it and unpack */
            Ok(match ElementContentChildren::parse(input)? {
                ElementContentChildren::Seq { seq, repetition } => Self::Seq { seq, repetition },
                ElementContentChildren::Choice { choice, repetition } => Self::Choice { choice, repetition },
            })
        } else {
            let name = expect_name(input)?;
            let repetition = RepetitionOperator::try_parse(input);
            Ok(Self::Name { name, repetition })
        }
    }
    fn write<W: std::io::Write>(&self, output: &mut W) -> std::io::Result<()> {
        match self {
            ElementContentParticle::Name { name, repetition } => match repetition {
                Some(repetition) => write!(output, "{name}{repetition}"),
                None => output.write_all(name.as_bytes()),
            },
            ElementContentParticle::Choice { choice, repetition } => {
                choice.write(output)?;
                if let Some(repetition) = repetition {
                    write!(output, "{repetition}")?;
                }
                Ok(())
            }
            ElementContentParticle::Seq { seq, repetition } => {
                seq.write(output)?;
                if let Some(repetition) = repetition {
                    write!(output, "{repetition}")?;
                }
                Ok(())
            }
        }
    }
}

/// [49] - Choice
///
/// https://www.w3.org/TR/xml/#NT-choice
pub struct ElementContentChoice<'src> {
    choices: Vec<ElementContentParticle<'src>>,
}

impl<'src> ElementContentChoice<'src> {
    fn write<W: std::io::Write>(&self, output: &mut W) -> std::io::Result<()> {
        for (i, choice) in self.choices.iter().enumerate() {
            choice.write(output)?;
            if i < self.choices.len() - 1 {
                write!(output, " | ")?;
            }
        }
        Ok(())
    }
}

/// [50] - Seq
///
/// https://www.w3.org/TR/xml/#NT-seq
pub struct ElementContentSeq<'src> {
    sequence: Vec<ElementContentParticle<'src>>,
}

impl<'src> ElementContentSeq<'src> {
    fn write<W: std::io::Write>(&self, output: &mut W) -> std::io::Result<()> {
        for (i, item) in self.sequence.iter().enumerate() {
            item.write(output)?;
            if i < self.sequence.len() - 1 {
                write!(output, ", ")?;
            }
        }
        Ok(())
    }
}

/// [69] - Parameter Entity Reference
///
/// https://www.w3.org/TR/xml/#NT-PEReference
pub struct ParameterEntityReference<'src> {
    name: &'src str,
}

impl<'src> ParameterEntityReference<'src> {
    const OPENING_TAG: &'static str = "%";
    const CLOSING_TAG: &'static str = ";";
}

impl<'src> XmlElement<'src> for ParameterEntityReference<'src> {
    fn parse(input: &mut &'src str) -> Result<Self, String> {
        expect_bytes(input, Self::OPENING_TAG)?;
        let end_pos = input.find(Self::CLOSING_TAG).ok_or_else(|| format!("Unclosed PeReference"))?;
        let (name, rest) = input.split_at(end_pos);
        *input = &rest[Self::CLOSING_TAG.len()..];
        Ok(Self { name })
    }
    fn write<W: std::io::Write>(&self, output: &mut W) -> std::io::Result<()> {
        write!(output, "{}{}{}", Self::OPENING_TAG, self.name, Self::CLOSING_TAG)
    }
}

/// [75] - External Id
///
/// https://www.w3.org/TR/xml/#NT-ExternalID
pub enum ExternalId<'src> {
    System {
        system: SystemLiteral<'src>,
    },
    Public {
        pubid: PubidLiteral<'src>,
        system: SystemLiteral<'src>,
    },
}

impl<'src> ExternalId<'src> {
    const SYSTEM_TAG: &'static str = "SYSTEM";
    const PUBLIC_TAG: &'static str = "PUBLIC";
}
impl<'src> XmlElement<'src> for ExternalId<'src> {
    fn parse(input: &mut &'src str) -> Result<Self, String> {
        if let Some(stripped) = input.strip_prefix(Self::SYSTEM_TAG) {
            *input = stripped;
            skip_whitespaces(input);
            let system = SystemLiteral::parse(input)?;
            Ok(Self::System { system })
        } else if let Some(stripped) = input.strip_prefix(Self::PUBLIC_TAG) {
            *input = stripped;
            skip_whitespaces(input);
            let pubid = PubidLiteral::parse(input)?;
            skip_whitespaces(input);
            let system = SystemLiteral::parse(input)?;
            Ok(Self::Public { pubid, system })
        } else {
            Err(format!("Expected {} or {}", Self::SYSTEM_TAG, Self::PUBLIC_TAG))
        }
    }
    fn write<W: std::io::Write>(&self, output: &mut W) -> std::io::Result<()> {
        match self {
            ExternalId::System { system } => {
                write!(output, "{} ", Self::SYSTEM_TAG)?;
                system.write(output)?;
            }
            ExternalId::Public { pubid, system } => {
                write!(output, "{} ", Self::PUBLIC_TAG)?;
                pubid.write(output)?;
                write!(output, " ")?;
                system.write(output)?;
            }
        }
        Ok(())
    }
}

/// Entire XML file, stored in a structured way to easily extract the useful data.
///
/// https://www.w3.org/TR/xml/
pub struct Xml<'src> {
    prolog: Prolog<'src>,
}

impl<'src> Xml<'src> {
    pub fn parse(input: &'src str) -> Result<Self, String> {
        let mut input = input;
        let prolog = Prolog::parse(&mut input)?;

        Ok(Xml { prolog })
    }
}
