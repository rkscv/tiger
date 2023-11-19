use ariadne::{ColorGenerator, Label, Report, ReportKind, Source};
use clap::Parser;
use pest::error::InputLocation;
use std::{borrow::Cow, fs, io};
use tiger::{ast::Span, error::Error, parser, vm};

/// Tiger language interpreter
#[derive(Parser, Debug)]
struct Args {
    file_name: String,
}

fn exec(src: &str) -> Result<(), Error> {
    let ast = parser::parse(src)?;
    vm::eval(&ast)?;
    Ok(())
}

fn main() -> io::Result<()> {
    let args = Args::parse();
    let file_name = args.file_name.as_str();
    let src = fs::read_to_string(file_name)?;
    if let Err(error) = exec(&src) {
        let span = match &error {
            Error::Variant(error) => error.span,
            Error::ParseError(error) => match error.location {
                InputLocation::Pos(pos) => Span(pos, pos),
                InputLocation::Span((start, end)) => Span(start, end),
            },
            Error::Break => unreachable!(),
        };
        Report::build(ReportKind::Error, file_name, span.0)
            .with_label(
                Label::new((file_name, span.0..span.1))
                    .with_message(match &error {
                        Error::Variant(error) => Cow::Owned(error.to_string()),
                        Error::ParseError(error) => error.variant.message(),
                        Error::Break => unreachable!(),
                    })
                    .with_color(ColorGenerator::new().next()),
            )
            .finish()
            .eprint((file_name, Source::from(src)))?;
    }
    Ok(())
}
