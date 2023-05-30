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

fn string_lit_convert(val: String) -> Result<String, usize> {
    let mut ret = "".to_string();
    let trimmed = val[1..val.len()-1].to_string();
    
    if !trimmed.contains("\\") { // no need to unescape
        return Ok(trimmed);
    }

    let len = val.len() - 2;
    let read : Vec<char> = trimmed.chars().collect();

    let mut i = 0;
    while i < len {
        let ch = read[i];

        if ch != '\\' {
            ret.push(ch);
            i += 1;
            continue;
        }

        i += 1;

        let next = read[i];

        let push = match next {
            '\\' => '\\',
            'n' => '\n',
            't' => '\t',
            'r' => '\r',
            '"' => '\"',
            _ => return Err(i + 1)
        };

        ret.push(push);
        i += 1;
    }

    Ok(ret)
}


pub fn lex(input: &String) -> Result<Vec<TokenPos>, Position> {
    let mut ret: Vec<TokenPos> = Vec::new();

    let mut progress = true;

    let mut pos = 0;
    
    let keyword_re = Regex::new(r"def|if|elif|else|while|continue|break|match").unwrap();
    // { } [ ] ( ) => = . , _ :
    let delimiter_re = Regex::new(r"\{|\}|\[|\]|\(|\)|=>|\.|,|_|:").unwrap();
    let ident_re = Regex::new(r"[a-zA-Z_][a-zA-Z0-9_]*").unwrap();
    let primitive_re = Regex::new(r"Int|Bool|String|Float|Unit").unwrap();
    let int_literal_re = Regex::new(r"0x[0-9a-fA-F]+|0o[0-7]+|0b[0-1]+|\d+").unwrap();
    let bool_literal_re = Regex::new(r"true|false").unwrap();
    let float_literal_re = Regex::new(r"\d+(?:\.\d+f?|f)").unwrap();
    let string_literal_re = Regex::new(r#""([^\\"]|\\\\|\\n|\\t|\\r|\\")*"|"""#).unwrap();
    let assignment_operator_re = Regex::new(r"\+=|-=|\*=|/=|%=|\|\|=|&&=").unwrap();
    let operator_re = Regex::new(r"\+|-|\*|/|%|!|!=|\|\||&&|==|<|<=|>|>=").unwrap();
    let equals = Regex::new(r"=").unwrap();
    // can "escape" away new lines using \
    let whitespace_re = Regex::new(r"( |\t)+|\\( |\t)*\n( |\t)*").unwrap();
    // semicolon with new lines or whitespace around it
    let explicit_exprsep_re = Regex::new(r"(?: |\t|\n)*\n(?: |\t|\n)*;(?: |\t|\n)*|;(?: |\t|\n)*").unwrap();
    // at least one new new line with whitespace around it
    let implicit_exprsep_re = Regex::new(r"(?: |\t|\n)*\n(?: |\t|\n)*").unwrap();
    let comment_re = Regex::new(r"#[^\n]*").unwrap();
    
    // order: 
    //  float literal
    //  int, bool literal
    //  string literal
    //  delimiter
    //  assignment ops
    //  operator
    //  equals
    //  keyword, prim types
    //  identifier
    //  explicit exprsep
    //  implicit exprsep
    // . comment, whitespace etc
    let spl = input.lines().collect();

    while progress && pos != input.len() {
        progress = false;
        let file_pos = string_index_to_pos(&spl, pos);
        let pos_temp = pos;
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

                match string_lit_convert(val) {
                    Ok(s) => {
                        ret.push(TokenPos { tk: Token::StringLiteral(s), pos: file_pos });
                        progress = true;
                        continue
                    }
                    Err(pos2) => { 
                        return Err(string_index_to_pos(&spl, pos + pos2)) 
                    }
                }
                
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

        // Assignment
        match try_parse(&assignment_operator_re, input, pos) {
            Some(val) => {
                pos += val.len();
                ret.push(TokenPos { tk: Token::AssignmentOperator(val), pos: file_pos });
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

        // Equals
        match try_parse(&equals, input, pos) {
            Some(val) => {
                pos += val.len();
                ret.push(TokenPos { tk: Token::Equals, pos: file_pos });
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

        // Explicit exprsep
        match try_parse(&explicit_exprsep_re, input, pos) {
            Some(val) => {
                pos += val.len();
                // find pos of first semicolon
                let inner_pos = val.find(";").unwrap();

                ret.push(TokenPos { tk: Token::ExplicitExprSep, pos: string_index_to_pos(&spl, pos_temp + inner_pos) });
                progress = true;
                continue
            }
            None => {}
        }

        // Implicit exprsep
        match try_parse(&implicit_exprsep_re, input, pos) {
            Some(val) => {
                pos += val.len();
                ret.push(TokenPos { tk: Token::ImplicitExprSep, pos: file_pos });
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
                // ret.push(TokenPos { tk: Token::Comment, pos: file_pos });
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

