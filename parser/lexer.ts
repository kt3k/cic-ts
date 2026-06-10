// Lexer (PARSER_SPEC §2).
//
// Turns surface-syntax source text into a flat token stream, skipping
// whitespace and comments (line `--` and nestable block `/- -/`). Identifiers
// may be dotted (`Nat.succ`); `.{` is split off as the universe-args opener so
// `Eq.{1}` lexes as `Eq` then `.{` then `1` then `}`.

import { ParseError, type Pos } from "./syntax.ts";

export type TokenKind = "ident" | "numeral" | "keyword" | "symbol" | "eof";

export interface Token {
  readonly kind: TokenKind;
  /** The lexeme (identifier text, digits, keyword, or symbol spelling). */
  readonly value: string;
  readonly pos: Pos;
  readonly end: Pos;
}

const KEYWORDS: ReadonlySet<string> = new Set([
  "inductive",
  "axiom",
  "def",
  "theorem",
  "opaque",
  "where",
  "fun",
  "Sort",
  "Type",
  "Prop",
  "#check",
]);

// Non-ASCII characters that are symbols, not identifier characters.
const RESERVED_UNICODE: ReadonlySet<string> = new Set(["→", "∀", "λ"]);

const ASCII_IDENT_START = /[A-Za-z_]/;
const ASCII_LETTER = /[A-Za-z]/;

function isDigit(c: string): boolean {
  return c >= "0" && c <= "9";
}

function isIdentStart(c: string): boolean {
  if (ASCII_IDENT_START.test(c)) return true;
  return c.codePointAt(0)! > 0x7f && !RESERVED_UNICODE.has(c);
}

function isIdentCont(c: string): boolean {
  return isIdentStart(c) || isDigit(c) || c === "'";
}

class Lexer {
  private readonly cs: string[];
  private i = 0;
  private line = 1;
  private col = 1;

  constructor(src: string) {
    this.cs = Array.from(src); // split by code point
  }

  private pos(): Pos {
    return { offset: this.i, line: this.line, col: this.col };
  }

  private peek(ahead = 0): string | undefined {
    return this.cs[this.i + ahead];
  }

  private advance(): string {
    const c = this.cs[this.i]!;
    this.i++;
    if (c === "\n") {
      this.line++;
      this.col = 1;
    } else {
      this.col++;
    }
    return c;
  }

  /** Skip whitespace and comments. Returns once positioned at real content. */
  private skipTrivia(): void {
    for (;;) {
      const c = this.peek();
      if (c === undefined) return;
      if (c === " " || c === "\t" || c === "\r" || c === "\n") {
        this.advance();
      } else if (c === "-" && this.peek(1) === "-") {
        while (this.peek() !== undefined && this.peek() !== "\n") this.advance();
      } else if (c === "/" && this.peek(1) === "-") {
        this.skipBlockComment();
      } else {
        return;
      }
    }
  }

  private skipBlockComment(): void {
    const start = this.pos();
    this.advance(); // /
    this.advance(); // -
    let depth = 1;
    while (depth > 0) {
      const c = this.peek();
      if (c === undefined) throw new ParseError(start, "unterminated block comment");
      if (c === "/" && this.peek(1) === "-") {
        this.advance();
        this.advance();
        depth++;
      } else if (c === "-" && this.peek(1) === "/") {
        this.advance();
        this.advance();
        depth--;
      } else {
        this.advance();
      }
    }
  }

  private token(kind: TokenKind, value: string, pos: Pos): Token {
    return { kind, value, pos, end: this.pos() };
  }

  private next(): Token {
    this.skipTrivia();
    const pos = this.pos();
    const c = this.peek();
    if (c === undefined) return this.token("eof", "", pos);

    if (isDigit(c)) return this.lexNumeral(pos);
    if (c === "#") return this.lexHashKeyword(pos);
    if (c === "." && this.peek(1) === "{") {
      this.advance();
      this.advance();
      return this.token("symbol", ".{", pos);
    }
    if (isIdentStart(c)) return this.lexIdent(pos);
    return this.lexSymbol(pos);
  }

  private lexNumeral(pos: Pos): Token {
    let s = "";
    while (this.peek() !== undefined && isDigit(this.peek()!)) s += this.advance();
    return this.token("numeral", s, pos);
  }

  private lexHashKeyword(pos: Pos): Token {
    let s = this.advance(); // '#'
    while (this.peek() !== undefined && ASCII_LETTER.test(this.peek()!)) s += this.advance();
    if (!KEYWORDS.has(s)) throw new ParseError(pos, `unknown command '${s}'`);
    return this.token("keyword", s, pos);
  }

  private lexIdent(pos: Pos): Token {
    let s = this.advance(); // first char (isIdentStart)
    for (;;) {
      const c = this.peek();
      if (c !== undefined && isIdentCont(c)) {
        s += this.advance();
      } else if (c === "." && this.peek(1) !== undefined && isIdentStart(this.peek(1)!)) {
        // dotted name segment, e.g. Nat.succ — but not `.{`
        s += this.advance(); // '.'
        s += this.advance(); // next segment start
      } else {
        break;
      }
    }
    return this.token(KEYWORDS.has(s) ? "keyword" : "ident", s, pos);
  }

  private lexSymbol(pos: Pos): Token {
    const c = this.advance();
    switch (c) {
      case "(":
      case ")":
      case "{":
      case "}":
      case ",":
      case "|":
      case "+":
      case "→":
      case "∀":
      case "λ":
        return this.token("symbol", c, pos);
      case ":":
        if (this.peek() === "=") {
          this.advance();
          return this.token("symbol", ":=", pos);
        }
        return this.token("symbol", ":", pos);
      case "=":
        if (this.peek() === ">") {
          this.advance();
          return this.token("symbol", "=>", pos);
        }
        throw new ParseError(pos, "unexpected '='; did you mean '=>'?");
      case "-":
        if (this.peek() === ">") {
          this.advance();
          return this.token("symbol", "→", pos); // '->' is an alias for '→'
        }
        throw new ParseError(pos, "unexpected '-'");
      default:
        throw new ParseError(pos, `unexpected character '${c}'`);
    }
  }

  tokenize(): Token[] {
    const out: Token[] = [];
    for (;;) {
      const t = this.next();
      out.push(t);
      if (t.kind === "eof") return out;
    }
  }
}

/** Tokenize `src`, returning all tokens terminated by a single `eof` token. */
export function tokenize(src: string): Token[] {
  return new Lexer(src).tokenize();
}
