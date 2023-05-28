use regex::Regex;
use Vec;

use crate::tokens::*;

fn try_parse(regex: &Regex, input: &String, pos: usize) -> Option<String> {
    match regex.captures_at(input, pos) {
        Some(captures) => {
            match captures.get(0) {
                Some(matched) => {
                    if matched.start() != pos {
                        None
                    } else {
                        Some(matched.as_str().to_string())
                    }
                }
                None => None
            }
        }
        None => None
    }
}

pub fn string_index_to_pos(spl: &Vec<&str>, pos: usize) -> Position {
    let mut explored = 1; // imaginary newline at start
    let mut line = 0;
    for ln in spl {
        explored += ln.len();
        if explored > pos {
            explored -= ln.len() + 1;
            return Position { line_no: line, pos: pos - explored }
        }
        line += 1;
        explored += 1; // account for newline character
    }

    panic!("Reached end of file after finding position.")
}

/*
fn delimiter_convert(delim: &str) -> DelimiterType {
    use crate::tokens::DelimiterType::*;
    // { } [ ] ( ) => = . , _ 
    match delim {
        "{" => CurlyOpen,
        "}" => CurlyClose,
        "[" => SquareOpen,
        "]" => SquareClose,
        "(" => Open,
        ")" => Close,
        "=>" => Arrow,
        "=" => Equal,
        "." => Dot,
        "," => Comma,
        "_" => Underscore,
        ":" => Colon,
        _ => unreachable!()
    }
}

fn kw_convert(kw: &str) -> KeywordType {
    // def|if|else|while|continue|break|match
    use crate::tokens::KeywordType::*;
    match kw {
        "def" => Def,
        "if" => If,
        "else" => Else,
        "while" => While,
        "continue" => Continue,
        "break" => Break,
        "match" => Match,
        _ => unreachable!()
    }
}
*/

fn float_lit_convert(val: String) -> f64 {
    let trimmed = if val.ends_with("f") {
        val[..val.len() - 1].to_string()
    } else {
        val
    };
        
    trimmed.parse::<f64>().unwrap()
}

fn int_lit_convert(val: String) -> i64 {
    if val.starts_with("0x") {
        let trimmed = val[2..].to_string();
        i64::from_str_radix(&trimmed, 16).unwrap()
    } else if val.starts_with("0o") {
        let trimmed = val[2..].to_string();
        i64::from_str_radix(&trimmed, 8).unwrap()
    } else if val.starts_with("0b") {
        let trimmed = val[2..].to_string();
        i64::from_str_radix(&trimmed, 2).unwrap()
    } else {
        val.parse::<i64>().unwrap()
    }
}

fn string_lit_convert(val: String) -> String {
    let mut cur = "".to_string();
    let mut changed = val[1..val.len()-1].to_string();
    
    let mut first = true;

    while first || cur != changed {
        first = false;
        cur = changed;
        changed = cur
        // todo: fix...
            .replacen("\\\\", "\\", 1)
            .replacen("\\n", "\n", 1)
            .replacen("\\t", "\t", 1)
            .replacen("\\r", "\r", 1)
            .replacen("\\\"", r#"\""#, 1)
    }
    
    cur
}


pub fn lex(input: &String) -> Result<Vec<TokenPos>, Position> {
    let mut ret: Vec<TokenPos> = Vec::new();

    let mut progress = true;

    let mut pos = 0;
    
    let keyword_re = Regex::new(r"def|if|else|while|continue|break|match").unwrap();
    // { } [ ] ( ) => = . , _ :
    let delimiter_re = Regex::new(r"\{|\}|\[|\]|\(|\)|=>|=|\.|,|_|:").unwrap();
    let ident_re = Regex::new(r"[a-zA-Z_][a-zA-Z0-9_]*").unwrap();
    let primitive_re = Regex::new(r"Int|Bool|String|Float|Unit").unwrap();
    let int_literal_re = Regex::new(r"0x[0-9a-fA-F]+|0o[0-7]+|0b[0-1]+|-?\d+").unwrap();
    let bool_literal_re = Regex::new(r"true|false").unwrap();
    let float_literal_re = Regex::new(r"\d+(?:\.\d+f?|f)").unwrap();
    let string_literal_re = Regex::new(r#""([^\\"]|\\\\|\\n|\\t|\\r|\\")*"|"""#).unwrap();
    let operator_re = Regex::new(r"\+|-|\*|/|%|!|\|\||&&|==|<|<=|>|>=").unwrap();
    let whitespace_re = Regex::new(r"( |\t)+").unwrap();
    let exprsep_re = Regex::new(r"(?: |\t|\n)*\n(?: |\t|\n)*;?(?: |\t|\n)*|;").unwrap();
    let comment_re = Regex::new(r"#[^\n]*?").unwrap();
    
    // order: 
    // 1. float literal
    // 2. int, bool literal
    // 3. string literal
    // 4. delimiter
    // 5. operator
    // 6. keyword, prim types
    // 7. identifier
    // 8. Newline
    // 9. comment, whitespace etc
    let spl = input.lines().collect();

    while progress && pos != input.len() {
        progress = false;
        let file_pos = string_index_to_pos(&spl, pos);
        // Try parsing all possible regexes, in order (highest priority first, then longest match)

        // Floats
        match try_parse(&float_literal_re, input, pos) {
            Some(val) => {
                pos += val.len();
                
                ret.push(TokenPos { tk: Token::FloatLiteral(float_lit_convert(val)), pos: file_pos });
                progress = true;
                continue
            }
            None => {}
        }

        // Ints
        match try_parse(&int_literal_re, input, pos) {
            Some(val) => {
                pos += val.len();

                ret.push(TokenPos { tk: Token::IntLiteral(int_lit_convert(val)), pos: file_pos });
                progress = true;
                continue
            }
            None => {}
        }

        // Bools
        match try_parse(&bool_literal_re, input, pos) {
            Some(val) => {
                pos += val.len();

                ret.push(TokenPos { tk: Token::BoolLiteral(if val == "true" { true } else { false }), pos: file_pos });
                progress = true;
                continue
            }
            None => {}
        }

        // Strings
        match try_parse(&string_literal_re, input, pos) {
            Some(val) => {
                pos += val.len();

                ret.push(TokenPos { tk: Token::StringLiteral(string_lit_convert(val)), pos: file_pos });
                progress = true;
                continue
            }
            None => {}
        }

        // Delimiters
        match try_parse(&delimiter_re, input, pos) {
            Some(val) => {
                pos += val.len();
                ret.push(TokenPos { tk: Token::Delimiter(val), pos: file_pos });
                progress = true;
                continue
            }
            None => {}
        }

        // Operators
        match try_parse(&operator_re, input, pos) {
            Some(val) => {
                pos += val.len();
                ret.push(TokenPos { tk: Token::Operator(val), pos: file_pos });
                progress = true;
                continue
            }
            None => {}
        }

        // Keywords
        match try_parse(&keyword_re, input, pos) {
            Some(val) => {
                pos += val.len();
                ret.push(TokenPos { tk: Token::Keyword(val), pos: file_pos });
                progress = true;
                continue
            }
            None => {}
        }

        // Prim types
        match try_parse(&primitive_re, input, pos) {
            Some(val) => {
                pos += val.len();
                ret.push(TokenPos { tk: Token::PrimType(val), pos: file_pos });
                progress = true;
                continue
            }
            None => {}
        }

        // Identifiers
        match try_parse(&ident_re, input, pos) {
            Some(val) => {
                pos += val.len();
                ret.push(TokenPos { tk: Token::Identifier(val), pos: file_pos });
                progress = true;
                continue
            }
            None => {}
        }

        // Exprsep
        match try_parse(&exprsep_re, input, pos) {
            Some(val) => {
                pos += val.len();
                ret.push(TokenPos { tk: Token::ExprSep, pos: file_pos });
                progress = true;
                continue
            }
            None => {}
        }

        // Whitespace
        match try_parse(&whitespace_re, input, pos) {
            Some(val) => {
                pos += val.len();
                // ignore whitespace.
                // ret.push(TokenPos { tk: Token::Whitespace, pos: file_pos });
                progress = true;
                continue
            }
            None => {}
        }

        // Comment
        match try_parse(&comment_re, input, pos) {
            Some(val) => {
                pos += val.len();
                ret.push(TokenPos { tk: Token::Comment, pos: file_pos });
                progress = true;
                continue
            }
            None => {}
        }
    }

    if progress {
        Ok(ret)
    } else {
        Err(string_index_to_pos(&spl, pos))
    }
}

