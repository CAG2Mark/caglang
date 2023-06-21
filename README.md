# Caglang
Making my own language as an experiment.

Very unfinished. Currently, the parser is nearly done and I am working on the analyzer.

# Summary
- The language will be **expression-oriented**. That is, all statements explicitly evaluate to a value, even if it is a "void"-like value, which in this case is the Unit Literal.
- The language will be fully semicolon optional, and partially brace optional. Braces will be needed if you wish to chain expressions together or use the `match` statement.
- Indents are ignored.
- There will be type inference.
- There will be a single ADT declaration for declaring both product and sum types. Product types are like structs, while sum types are like enums in Rust. There is no distinction between product and sum types, and one can also create combined sum and product types.

# Status

| Feature                 | Parser        | Analyzer      |Interpreter  |Codegen     |
| -------------           | ------------- |---------------|-------------|------------|
| Basic control flow      |✔             |✔             |❌           |❌
| ADTs                    |✔             |✔             |❌           |❌
| Impors                    |❌             |❌             |❌           |❌
| Pattern matching        |✔             |✔             |❌           |❌
| Break, continue, return |✔             |✔             |❌           |❌
| Generics                |❌             |❌             |❌           |❌

# Syntax Examples
I have not defined a formal grammar for this language yet, but the below examples should be enough to get an idea of the syntax.

Functions:
```
def sum_of_cubes(n) = {
    sum = 0
    i = 1
    while (i < n)
        sum += i * i * i
    sum
}

def add(x, y) = x + y
```
ADTs:
```
# Product type
adt Player(hp: Int, name: String)

# Sum type
adt Road =
    Path,
    Street,
    Highway(speed_limit: Int)

# Combined sum and product type
adt Cell(x: Int, y: Int) =
    Empty,
    Block(id: Int),
    Entity(id: Int, hp: Float)

# Braces optional
adt Something = {
    First,
    Second
}

let x = new Cell::Entity(1, 2, 1, 2f)

match x {
    Cell::Empty => print("Empty")
    Cell::Block(id) => print(id)
    Cell::Entity(id, hp) => {
      print(id)
      print(hp)
    }
}
```
The way expressions without braces are treated are similar to how they are treated in C with if-else statements. For example:
```
if (cond)
    x + 1
    -2
    
if (cond)
    x + 1 - 2
```
is treated as:
```
if (cond) {
    x + 1
}
-2

if (cond) {
    x + 1 - 2
}
```
The parser will try to be as lenient as possible when dealing with such scenarios.
