pub mod analysis;
pub mod parsing;
pub mod util;

use analysis::analyzer;
use parsing::ast;
use parsing::lexer;
use parsing::parser;
use parsing::tokens;

use crate::parsing::position::*;

use std::fs::File;
use std::io::prelude::*;

use std::env;

fn print_ln(input: &String, ln: usize) {
    print!("{: <4}| {}\n", ln + 1, input);
}

fn first_non_whitespace(input: &String, start: usize) -> Option<usize> {
    if start >= input.len() {
        return Some(start);
    }

    match input[start..].find(|c| c != ' ' && c != '\t') {
        Some(v) => Some(v + start),
        None => None,
    }
}

fn last_non_whitespace(input: &String, end: usize) -> Option<usize> {
    if end >= input.len() {
        return Some(end);
    }

    match input[..end].rfind(|c| c != ' ' && c != '\t') {
        Some(v) => Some(v + 1),
        None => None,
    }
}

fn print_ln_carets(input: &String, ln: usize, start: usize, end: usize, color: u32) {
    let start_pos = match first_non_whitespace(input, start) {
        Some(v) => v,
        None => start,
    };

    let end_pos = match last_non_whitespace(input, end) {
        Some(v) => v,
        None => end,
    };

    print_ln(input, ln);

    if input.trim().is_empty() {
        return;
    }

    print!("    | ");
    // don't laugh ok :(
    for _ in 0..start_pos {
        print!(" ")
    }
    print!("\x1b[1;{color}m");
    for _ in start_pos..end_pos {
        print!("^")
    }
    print!("\x1b[0m");
    print!("\n");
}

fn print_error_at(
    file_name: &String,
    input: &String,
    severity: &str,
    pos: &PositionRange,
    msg: &str,
    color: u32,
) {
    println!(
        "{}:{}:{}",
        file_name,
        pos.start.line_no + 1,
        pos.start.pos + 1
    );

    let chunks: Vec<&str> = input.lines().collect();

    if pos.start.line_no > 0 {
        print_ln(
            &chunks.get(pos.start.line_no - 1).unwrap().to_string(),
            pos.start.line_no - 1,
        );
    }

    let start_ln = pos.start.line_no;
    let end_ln = pos.end.line_no;

    let first_ln = chunks.get(start_ln).unwrap().to_string();
    let last_ln = chunks.get(end_ln).unwrap().to_string();

    let last_start;
    let last_end;

    // print first line
    // also set start pos
    if start_ln == end_ln {
        print_ln_carets(&first_ln, start_ln, pos.start.pos, pos.end.pos + 1, color);
    } else {
        print_ln_carets(&first_ln, start_ln, pos.start.pos, first_ln.len(), color);
    }

    if end_ln > 0 {
        // print in between lines
        for l in start_ln + 1..end_ln {
            let ln = chunks.get(l).unwrap().to_string();
            print_ln_carets(&ln, l, 0, ln.len(), color);
        }
    }

    // print last line, also set last line pos
    if start_ln != end_ln {
        print_ln_carets(&last_ln, end_ln, 0, pos.end.pos + 1, color);

        last_start = match first_non_whitespace(&last_ln, 0) {
            Some(v) => v,
            None => 0,
        };
    } else {
        last_start = match first_non_whitespace(&last_ln, pos.start.pos) {
            Some(v) => v,
            None => 0,
        };
    }

    last_end = match last_non_whitespace(&last_ln, pos.end.pos) {
        Some(v) => v,
        None => last_ln.len() - 1,
    };

    // determine best position to print error msg
    let mut start = (last_start + last_end) / 2;

    let l = (msg.len() + severity.len() + 2) / 2;

    start = if start >= l { start - l } else { 0 };
    print!("      ");
    for _ in 0..start {
        print!(" ")
    }

    print!("\x1b[1;{}m{}\x1b[0m: {}\n", color, severity, msg);
}

fn expected_to_str(expected: Vec<String>) -> String {
    let mut ret = "".to_string();
    ret += match expected.first() {
        Some(s) => s,
        None => unreachable!(),
    };

    if expected.len() == 1 {
        return ret;
    }

    for i in 1..expected.len() - 1 {
        ret += ", ".as_ref();
        ret += match expected.get(i) {
            Some(s) => s,
            None => unreachable!(),
        };
    }

    ret += " or ".as_ref();
    ret += match expected.last() {
        Some(s) => s,
        None => unreachable!(),
    };

    return ret;
}

fn single_posrange(line_no: usize, pos: usize) -> PositionRange {
    PositionRange {
        start: Position { line_no, pos },
        end: Position { line_no, pos },
    }
}

fn print_parse_error(file_name: &String, input: &String, error: parser::ParseError) {
    let chunks: Vec<&str> = input.lines().collect();

    match error {
        parser::ParseError::UnexpectedToken(got, expected, pos) => {
            let msg = format!(
                "unexpected token {}, possible token(s) contain {}",
                got,
                expected_to_str(expected)
            );
            print_error_at(file_name, input, "fatal", &pos, &msg, 31)
        }
        parser::ParseError::UnexpectedEOF(expected) => {
            let msg = "unexpected end of file";
            let dummy_inp = " ".to_string();
            let dummy_pos = single_posrange(0, 0);
            if input.len() == 0 {
                print_error_at(file_name, &dummy_inp, "fatal", &dummy_pos, &msg, 31);
                return;
            }
            let pos = lexer::string_index_to_pos(&chunks, input.len() - 1);
            let pos_new = single_posrange(pos.line_no, pos.pos + 1);
            let msg = format!(
                "unexpected end of file, possible token(s) contain {}",
                expected_to_str(expected)
            );
            print_error_at(file_name, input, "fatal", &pos_new, &msg, 31)
        }
        parser::ParseError::UnexpectedEOFOther => {
            let msg = "unexpected end of file";
            let pos = lexer::string_index_to_pos(&chunks, input.len() - 1);
            let pos_new = single_posrange(pos.line_no, pos.pos + 1);
            print_error_at(file_name, input, "fatal", &pos_new, &msg, 31)
        }
        parser::ParseError::Unfinished(got, pos) => {
            let msg = format!("unexpected token {}", got);
            print_error_at(file_name, input, "fatal", &pos, &msg, 31)
        }
    }
}

fn print_analysis_error(file_name: &String, input: &String, error: analyzer::AnalysisError) {
    match error {
        analyzer::AnalysisError::LocalNotFoundError(name, pos) => {
            let msg = format!(
                "use of possibly unbound local variable \x1b[1m{}\x1b[0m",
                name
            );
            print_error_at(file_name, input, "error", &pos, &msg, 31)
        }
        analyzer::AnalysisError::NoMemberError(name, pos) => {
            let msg = format!("member \x1b[1m{}\x1b[0m does not exist", name);
            print_error_at(file_name, input, "error", &pos, &msg, 31)
        }
        analyzer::AnalysisError::VariableRedefError(name, offending, original) => {
            let hint_msg = format!("local \x1b[1m{}\x1b[0m originally defined here", name);
            print_error_at(file_name, input, "hint", &original, &hint_msg, 33);

            let msg = format!("redefinition of local variable \x1b[1m{}\x1b[0m", name);
            print_error_at(file_name, input, "error", &offending, &msg, 31)
        }
        analyzer::AnalysisError::TypeNotFound(ty, pos) => {
            let msg = format!("type \x1b[1m{}\x1b[0m not found", ty);
            print_error_at(file_name, input, "error", &pos, &msg, 31)
        }
        analyzer::AnalysisError::FnNotFoundError(name, pos) => {
            let msg = format!("could not find function \x1b[1m{}\x1b[0m", name);
            print_error_at(file_name, input, "error", &pos, &msg, 31)
        }
        analyzer::AnalysisError::TooManyArgsError(name, pos) => {
            let msg = format!("too many arguments for function \x1b[1m{}\x1b[0m", name);
            print_error_at(file_name, input, "error", &pos, &msg, 31);
        }
        analyzer::AnalysisError::TooFewArgsError(name, pos) => {
            let msg = format!("not enough arguments for \x1b[1m{}\x1b[0m", name);
            print_error_at(file_name, input, "error", &pos, &msg, 31);
        }
        analyzer::AnalysisError::NameAlreadyUsedError(name, offending, original) => {
            let hint_msg = format!("name \x1b[1m{}\x1b[0m originally used here", name);
            print_error_at(file_name, input, "hint", &original, &hint_msg, 33);

            let msg = format!("name \x1b[1m{}\x1b[0m is already used", name);
            print_error_at(file_name, input, "error", &offending, &msg, 31)
        }
        analyzer::AnalysisError::DuplicateMemberError(name, adt_name, offending, original) => {
            let hint_msg = format!("name \x1b[1m{}\x1b[0m already used here", name);
            print_error_at(file_name, input, "hint", &original, &hint_msg, 33);

            let msg = format!("member \x1b[1m{}\x1b[0m already exists in {}", name, adt_name);
            print_error_at(file_name, input, "error", &offending, &msg, 31)
        },
        analyzer::AnalysisError::DuplicateVariantError(name, adt_name, offending, original) => {
            let hint_msg = format!("name \x1b[1m{}\x1b[0m already used here", name);
            print_error_at(file_name, input, "hint", &original, &hint_msg, 33);

            let msg = format!("duplicate variant name \x1b[1m{}\x1b[0m of ADT {}", name, adt_name);
            print_error_at(file_name, input, "error", &offending, &msg, 31)
        }
        analyzer::AnalysisError::InvalidCtorError(pos) => {
            let msg = format!("not a valid constructor");
            print_error_at(file_name, input, "error", &pos, &msg, 31)
        }
        analyzer::AnalysisError::AdtNotFoundError(name, pos) => {
            let msg = format!("could not find ADT \x1b[1m{}\x1b[0m", name);
            print_error_at(file_name, input, "error", &pos, &msg, 31)
        }
        analyzer::AnalysisError::AdtVariantNotFoundError(name, variant, pos) => {
            let msg = format!("ADT \x1b[1m{}\x1b[0m has no variant \x1b[1m{}\x1b[0m", name, variant);
            print_error_at(file_name, input, "error", &pos, &msg, 31)
        },
        analyzer::AnalysisError::AdtNoBaseError(name, pos, hint_pos) => {
            let hint_msg = format!("insert a \x1b[1mBase\x1b[0m variant");
            print_error_at(file_name, input, "hint", &hint_pos, &hint_msg, 33);

            let msg = format!("ADT \x1b[1m{}\x1b[0m has no default variant", name);
            print_error_at(file_name, input, "error", &pos, &msg, 31)
        },
    }
}

fn print_type_error(file_name: &String, input: &String, error: analyzer::TypeError) {
    match error {
        analyzer::TypeError::TypeNeededError(pos) => {
            let msg = format!("type annotation needed");
            print_error_at(file_name, input, "error", &pos, &msg, 31)
        }
        analyzer::TypeError::TypeMismatch(t1, t2, pos) => {
            let msg = format!(
                "expected type \x1b[1m{}\x1b[0m, got \x1b[1m{}\x1b[0m",
                t1, t2
            );
            print_error_at(file_name, input, "error", &pos, &msg, 31)
        },
        analyzer::TypeError::InvalidOperandError(pos) => {
            let msg = format!("invalid operand");
            print_error_at(file_name, input, "error", &pos, &msg, 31)
        }
    }
}

fn file_to_string(file_name: &str) -> Option<String> {
    let file = File::open(file_name);

    match file {
        Ok(mut f) => {
            let mut contents = String::new();
            match f.read_to_string(&mut contents) {
                Ok(_) => Some(contents),
                Err(_) => None,
            }
        }
        Err(_) => None,
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let file_name = match args.get(1) {
        Some(s) => s,
        None => {
            println!("Error: File not provided.");
            std::process::exit(1)
        }
    };

    let read = file_to_string(file_name);
    let contents = match read {
        Some(contents) => contents,
        None => {
            println!("Could not open file.");
            std::process::exit(1)
        }
    }
    .trim_end()
    .to_string();

    let tokens = match lexer::lex(&contents) {
        Ok(tokens) => tokens,
        Err(pos) => {
            print_error_at(
                file_name,
                &contents,
                "fatal",
                &single_posrange(pos.line_no, pos.pos),
                "invalid token",
                31,
            );
            std::process::exit(1)
        }
    };

    let mut parser = parser::new(tokens);
    let parsed = match parser.parse() {
        Ok(expr) => expr,
        Err(error) => {
            print_parse_error(file_name, &contents, error);
            std::process::exit(1);
        }
    };

    let mut analyzer = analyzer::init_analyzer();

    println!("{}", ast::format_tree(&parsed.expr, 0, true));

    let analyzed = match analyzer.convert_top(parsed) {
        Some(_) => {
            // println!("Name Analysis OK")
        }
        None => (),
    };
    println!();

    for e in analyzer.name_errors {
        print_analysis_error(file_name, &contents, e);
        println!()
    }

    for e in analyzer.type_errors {
        print_type_error(file_name, &contents, e);
        println!()
    }
}
