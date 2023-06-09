pub mod parsing;
pub mod analysis;
pub mod util;

use analysis::analyzer;
use parsing::lexer;
use parsing::tokens;
use parsing::parser;
use parsing::ast;

use crate::parsing::position::*;

use std::io::prelude::*;
use std::fs::File;

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
        None => None
    }
}

fn last_non_whitespace(input: &String, end: usize) -> Option<usize> {
    if end >= input.len() {
        return Some(end);
    }

    match input[..end + 1].rfind(|c| c != ' ' && c != '\t') {
        Some(v) => Some(v + input.len() - end - 1),
        None => None
    }
}

fn print_ln_carets(input: &String, ln: usize, start: usize, end: usize) {
    let start_pos = match first_non_whitespace(input, start) {
        Some(v) => v,
        None => 0,
    };

    let end_pos = match last_non_whitespace(input, end) {
        Some(v) => v,
        None => input.len() - 1
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
    for _ in start_pos..end_pos {
        print!("^")
    }
    print!("\n");
}

fn print_error_at(file_name: &String, input: &String, severity: &str, pos: &PositionRange, msg: &str) {
    println!("{}:{}:{}", file_name, pos.start.line_no + 1, pos.start.pos + 1);
    
    let chunks: Vec<&str> = input.lines().collect();

    if pos.start.line_no > 0 {
        print_ln(&chunks.get(pos.start.line_no - 1).unwrap().to_string(), pos.start.line_no - 1);
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
        print_ln_carets(&first_ln, start_ln, pos.start.pos, pos.end.pos + 1);
    } else {
        print_ln_carets(&first_ln, start_ln, pos.start.pos, first_ln.len());
    }

    if end_ln > 0 {
        // print in between lines
        for l in start_ln + 1..end_ln {
            let ln = chunks.get(l).unwrap().to_string();
            print_ln_carets(&ln, l, 0, ln.len());
        }
    }

    // print last line, also set last line pos
    if start_ln != end_ln {
        print_ln_carets(&last_ln, end_ln, 0, pos.end.pos + 1);

        last_start = match first_non_whitespace(&last_ln, 0) {
            Some(v) => v,
            None => 0
        };
    } else {
        last_start = match first_non_whitespace(&last_ln, pos.start.pos) {
            Some(v) => v,
            None => 0
        };
    }

    last_end = match last_non_whitespace(&last_ln, pos.end.pos) {
        Some(v) => v,
        None => last_ln.len() - 1
    };

    // determine best position to print error msg
    let mut start = (last_start + last_end) / 2;

    let l = (msg.len() + severity.len() + 2) / 2;

    start = if start >= l { start - l } else { 0 }; 
    print!("      ");
    for _ in 0..start {
        print!(" ")
    }

    print!("{}: {}\n", severity, msg);
    
}

fn expected_to_str(expected: Vec<String>) -> String {
    let mut ret = "".to_string();
    ret += match expected.first() {
        Some(s) => s,
        None => unreachable!()
    };

    if expected.len() == 1 {
        return ret
    }

    for i in 1..expected.len() - 1 {
        ret += ", ".as_ref();
        ret += match expected.get(i) {
            Some(s) => s,
            None => unreachable!()
        };
    }
    
    ret += " or ".as_ref();
    ret += match expected.last() {
        Some(s) => s,
        None => unreachable!()
    };

    return ret
}

fn single_posrange(line_no: usize, pos: usize) -> PositionRange {
    PositionRange {
        start: Position { line_no, pos },
        end: Position { line_no, pos }
    }
}

fn print_parse_error(file_name: &String, input: &String, error: parser::ParseError) {
    let chunks: Vec<&str> = input.lines().collect();

    match error {
        parser::ParseError::UnexpectedToken(got, expected, pos) => {
            let msg = format!("unexpected token {}, possible token(s) contain {}", got, expected_to_str(expected));
            print_error_at(file_name, input, "fatal", &pos, &msg)
        }
        parser::ParseError::UnexpectedEOF(expected) => {
            let msg = "unexpected end of file";
            let dummy_inp = " ".to_string();
            let dummy_pos = single_posrange(0, 0);
            if input.len() == 0 {
                print_error_at(file_name, &dummy_inp, "fatal", &dummy_pos, &msg);
                return;
            }
            let pos = lexer::string_index_to_pos(&chunks, input.len() - 1);
            let pos_new = single_posrange(pos.line_no, pos.pos + 1);
            let msg = format!("unexpected end of file, possible token(s) contain {}", expected_to_str(expected));
            print_error_at(file_name, input, "fatal", &pos_new, &msg)
        }
        parser::ParseError::UnexpectedEOFOther => {
            let msg = "unexpected end of file";
            let pos = lexer::string_index_to_pos(&chunks, input.len() - 1);
            let pos_new = single_posrange(pos.line_no, pos.pos + 1);
            print_error_at(file_name, input, "fatal", &pos_new, &msg)
        }
        parser::ParseError::Unfinished(got, pos) => {
            let msg = format!("unexpected token {}", got);
            print_error_at(file_name, input, "fatal", &pos, &msg)
        }
    }
}

fn print_analysis_error(file_name: &String, input: &String, error: analyzer::AnalysisError) {
    let chunks: Vec<&str> = input.lines().collect();

    match error {
        analyzer::AnalysisError::LocalNotFoundError(name, pos) => {
            let msg = format!("could not find variable {}", name);
            print_error_at(file_name, input, "error", &pos, &msg)
        },
        analyzer::AnalysisError::NoMemberError(name, pos) => {
            let msg = format!("member {} does not exist", name);
            print_error_at(file_name, input, "error", &pos, &msg)
        }
    }
}

fn print_type_error(file_name: &String, input: &String, error: analyzer::TypeError) {
    let chunks: Vec<&str> = input.lines().collect();

    match error {
        analyzer::TypeError::TypeNeededError(pos) => {
            let msg = format!("type annotation needed for this variable");
            print_error_at(file_name, input, "error", &pos, &msg)
        },
        analyzer::TypeError::TypeMismatch(t1, t2, pos) => {
            let msg = format!("expected type {}, got {}", t1, t2);
            print_error_at(file_name, input, "error", &pos, &msg)
        },
    }
}

fn file_to_string(file_name: &str) -> Option<String> {
    let file = File::open(file_name);

    match file {
        Ok(mut f) => {
            let mut contents = String::new();
            match f.read_to_string(&mut contents) {
                Ok(_) => Some(contents),
                Err(_) => None
            }
        }
        Err(_) => None
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
    }.trim_end().to_string();
    
    let tokens = match lexer::lex(&contents) {
        Ok(tokens) => tokens,
        Err(pos) => {
            print_error_at(file_name, &contents, "fatal", &single_posrange(pos.line_no, pos.pos), "invalid token");
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

    let analyzed = match analyzer.convert_top(&parsed) {
        Some(_) => {
            println!("Name Analysis OK")
        }
        None => ()
    };

    for e in analyzer.name_errors {
        print_analysis_error(file_name, &contents, e);
        println!()
    }

    for e in analyzer.type_errors {
        print_type_error(file_name, &contents, e);
        println!()
    }
}