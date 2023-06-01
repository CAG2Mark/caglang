pub mod parsing;

use parsing::lexer;
use parsing::tokens;
use parsing::parser;
use parsing::ast;

use parsing::tokens::Position;

use std::io::prelude::*;
use std::fs::File;

use std::env;

fn print_ln(chunks: &Vec<&str>, ln: usize) {
    print!("{: <4}| {}\n", ln + 1, chunks.get(ln).unwrap());
}

fn print_error_at(input: &String, severity: &str, pos: &Position, msg: &str) {
    let chunks: Vec<&str> = input.lines().collect();

    if pos.line_no > 0 {
        print_ln(&chunks, pos.line_no - 1);
    }

    match chunks.get(pos.line_no) {
        Some(_) => {
            print_ln(&chunks, pos.line_no);
            print!("      ");
            // don't laugh ok :(
            for _ in 0..pos.pos {
                print!(" ")
            }
            print!("^\n");

            // determine best position to print error msg
            let mut start = pos.pos;
            let l = (msg.len() + severity.len() + 2) / 2;

            start = if start >= l { start - l } else { 0 }; 
            print!("      ");
            for _ in 0..start {
                print!(" ")
            }

            print!("{}: {}\n", severity, msg);
        }
        None => panic!("Position out of bounds")
    }
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

fn print_parse_error(input: &String, error: parser::ParseError) {
    let chunks: Vec<&str> = input.lines().collect();

    match error {
        parser::ParseError::UnexpectedToken(got, expected, pos) => {
            let msg = format!("unexpected token {}, possible token(s) contain {}", got, expected_to_str(expected));
            print_error_at(input, "fatal", &pos, &msg)
        }
        parser::ParseError::UnexpectedEOF(expected) => {
            let msg = "unexpected end of file";
            let dummy_inp = " ".to_string();
            let dummy_pos = Position { line_no: 0, pos: 0 };
            if input.len() == 0 {
                print_error_at(&dummy_inp, "fatal", &dummy_pos, &msg);
                return;
            }
            let pos = lexer::string_index_to_pos(&chunks, input.len() - 1);
            let pos_new = Position{line_no: pos.line_no, pos: pos.pos + 1};
            let msg = format!("unexpected end of file, possible token(s) contain {}", expected_to_str(expected));
            print_error_at(input, "fatal", &pos_new, &msg)
        }
        parser::ParseError::UnexpectedEOFOther => {
            let msg = "unexpected end of file";
            let pos = lexer::string_index_to_pos(&chunks, input.len() - 1);
            let pos_new = Position{line_no: pos.line_no, pos: pos.pos + 1};
            print_error_at(input, "fatal", &pos_new, &msg)
        }
        parser::ParseError::Unfinished(got, pos) => {
            let msg = format!("unexpected token {}", got);
            print_error_at(input, "fatal", &pos, &msg)
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
            print_error_at(&contents, "fatal", &pos, "invalid token");
            std::process::exit(1)
        }
    };

    let mut parser = parser::new(tokens);
    let parsed = parser.parse();

    match parsed {
        Ok(expr) => println!("{}", ast::format_tree(&expr.expr, 0, true)),
        Err(error) => print_parse_error(&contents, error)
    }
}