// Recursive-descent parser (PARSER_SPEC §3–§4).
//
// Consumes the lexer's token stream and builds the surface AST (syntax.ts). It
// performs no name resolution or type checking — identifiers stay as names and
// are lowered to kernel terms later by the elaborator.

import { type Token, tokenize } from "./lexer.ts";
import {
  ParseError,
  type SBinder,
  type SCommand,
  type SCtor,
  type SExpr,
  type SLevel,
  type SModule,
} from "./syntax.ts";

class Parser {
  private i = 0;
  constructor(private readonly tokens: readonly Token[]) {}

  private peek(): Token {
    return this.tokens[this.i]!;
  }

  private advance(): Token {
    const t = this.tokens[this.i]!;
    if (t.kind !== "eof") this.i++;
    return t;
  }

  private atEof(): boolean {
    return this.peek().kind === "eof";
  }

  /** True if the next token is a keyword/symbol with the given spelling. */
  private at(value: string): boolean {
    const t = this.peek();
    return (t.kind === "keyword" || t.kind === "symbol") && t.value === value;
  }

  private eat(value: string): boolean {
    if (this.at(value)) {
      this.advance();
      return true;
    }
    return false;
  }

  private expect(value: string): Token {
    if (!this.at(value)) {
      throw new ParseError(
        this.peek().pos,
        `expected '${value}', got '${this.peek().value || "<eof>"}'`,
      );
    }
    return this.advance();
  }

  private expectIdent(what = "identifier"): Token {
    if (this.peek().kind !== "ident") {
      throw new ParseError(
        this.peek().pos,
        `expected ${what}, got '${this.peek().value || "<eof>"}'`,
      );
    }
    return this.advance();
  }

  // --- Module / commands ----------------------------------------------------

  parseModule(): SModule {
    const cmds: SCommand[] = [];
    while (!this.atEof()) cmds.push(this.parseCommand());
    return cmds;
  }

  private parseCommand(): SCommand {
    const t = this.peek();
    if (t.kind === "keyword") {
      switch (t.value) {
        case "axiom":
          return this.parseAxiom();
        case "def":
        case "theorem":
        case "opaque":
          return this.parseDefLike(t.value);
        case "inductive":
          return this.parseInductive();
        case "#check": {
          this.advance();
          return { kind: "check", expr: this.parseExpr(), pos: t.pos };
        }
      }
    }
    throw new ParseError(t.pos, `expected a command, got '${t.value || "<eof>"}'`);
  }

  private parseAxiom(): SCommand {
    const pos = this.expect("axiom").pos;
    const name = this.expectIdent("axiom name").value;
    const univParams = this.parseUnivParams();
    this.expect(":");
    return { kind: "axiom", name, univParams, type: this.parseExpr(), pos };
  }

  private parseDefLike(kw: "def" | "theorem" | "opaque"): SCommand {
    const pos = this.expect(kw).pos;
    const name = this.expectIdent(`${kw} name`).value;
    const univParams = this.parseUnivParams();
    const binders = this.parseBinders();
    this.expect(":");
    const type = this.parseExpr();
    this.expect(":=");
    const value = this.parseExpr();
    return { kind: kw, name, univParams, binders, type, value, pos };
  }

  private parseInductive(): SCommand {
    const pos = this.expect("inductive").pos;
    const name = this.expectIdent("inductive name").value;
    const univParams = this.parseUnivParams();
    const params = this.parseBinders();
    this.expect(":");
    const type = this.parseExpr();
    this.expect("where");
    const ctors: SCtor[] = [];
    while (this.at("|")) {
      const cpos = this.advance().pos;
      const cname = this.expectIdent("constructor name").value;
      this.expect(":");
      ctors.push({ name: cname, type: this.parseExpr(), pos: cpos });
    }
    return { kind: "inductive", name, univParams, params, type, ctors, pos };
  }

  /** `.{u, v}` declaration universe parameters (a list of names), or `[]`. */
  private parseUnivParams(): string[] {
    if (!this.at(".{")) return [];
    return this.braceList(() => this.expectIdent("universe parameter").value);
  }

  /** Parse a comma-separated `.{ item, … }` list (the opener must be next). */
  private braceList<T>(parseItem: () => T): T[] {
    this.expect(".{");
    const items: T[] = [];
    if (!this.at("}")) {
      items.push(parseItem());
      while (this.eat(",")) items.push(parseItem());
    }
    this.expect("}");
    return items;
  }

  // --- Binders --------------------------------------------------------------

  /** Zero or more binder groups: `(x y : T)` / `{x : T}`. */
  private parseBinders(): SBinder[] {
    const binders: SBinder[] = [];
    while (this.at("(") || this.at("{")) binders.push(this.parseBinder());
    return binders;
  }

  private parseBinder(): SBinder {
    const open = this.peek();
    const explicit = open.value === "(";
    const close = explicit ? ")" : "}";
    this.advance();
    const names: string[] = [this.expectIdent("binder name").value];
    while (this.peek().kind === "ident") names.push(this.advance().value);
    this.expect(":");
    const type = this.parseExpr();
    this.expect(close);
    return { names, type, info: explicit ? "explicit" : "implicit", pos: open.pos };
  }

  // --- Expressions ----------------------------------------------------------

  parseExpr(): SExpr {
    if (this.at("fun") || this.at("λ")) return this.parseLam();
    if (this.at("∀")) return this.parseForall();
    return this.parseArrow();
  }

  /** Parse one expression and require the input to be exhausted afterwards. */
  parseSingleExpr(): SExpr {
    const e = this.parseExpr();
    if (!this.atEof()) {
      throw new ParseError(
        this.peek().pos,
        `trailing input after expression: '${this.peek().value}'`,
      );
    }
    return e;
  }

  private parseLam(): SExpr {
    const pos = this.advance().pos; // fun / λ
    const binders = this.parseBinders();
    if (binders.length === 0) {
      throw new ParseError(this.peek().pos, "expected a binder after 'fun'");
    }
    this.expect("=>");
    return { kind: "lam", binders, body: this.parseExpr(), pos };
  }

  private parseForall(): SExpr {
    const pos = this.advance().pos; // ∀
    const binders = this.parseBinders();
    if (binders.length === 0) throw new ParseError(this.peek().pos, "expected a binder after '∀'");
    this.expect(",");
    return { kind: "pi", binders, body: this.parseExpr(), pos };
  }

  private parseArrow(): SExpr {
    const left = this.parseApp();
    if (this.at("→")) {
      const pos = this.advance().pos;
      return { kind: "arrow", from: left, to: this.parseArrow(), pos }; // right-assoc
    }
    return left;
  }

  private parseApp(): SExpr {
    let fn = this.parseAtom();
    while (this.atStartOfAtom()) {
      const arg = this.parseAtom();
      fn = { kind: "app", fn, arg, pos: fn.pos };
    }
    return fn;
  }

  private atStartOfAtom(): boolean {
    const t = this.peek();
    if (t.kind === "ident" || t.kind === "numeral") return true;
    if (t.kind === "keyword") return t.value === "Sort" || t.value === "Type" || t.value === "Prop";
    if (t.kind === "symbol") return t.value === "(";
    return false;
  }

  private parseAtom(): SExpr {
    const t = this.peek();
    if (t.kind === "ident") {
      this.advance();
      const univs = this.at(".{") ? this.parseUnivArgs() : undefined;
      return { kind: "ident", name: t.value, ...(univs ? { univs } : {}), pos: t.pos };
    }
    if (t.kind === "numeral") {
      this.advance();
      return { kind: "num", value: BigInt(t.value), pos: t.pos };
    }
    if (t.kind === "keyword") {
      if (t.value === "Sort") {
        this.advance();
        return { kind: "sort", level: this.parseLevel(), pos: t.pos };
      }
      if (t.value === "Type") {
        this.advance();
        const level = this.atSimpleLevel() ? this.parseLevel() : undefined;
        return { kind: "type", ...(level ? { level } : {}), pos: t.pos };
      }
      if (t.value === "Prop") {
        this.advance();
        return { kind: "prop", pos: t.pos };
      }
    }
    if (this.at("(")) {
      this.advance();
      const e = this.parseExpr();
      this.expect(")");
      return e;
    }
    throw new ParseError(t.pos, `expected an expression, got '${t.value || "<eof>"}'`);
  }

  /** Whether the next token can begin a (simple) level for `Type`'s optional arg. */
  private atSimpleLevel(): boolean {
    return this.peek().kind === "numeral" || this.peek().kind === "ident";
  }

  /** `.{l, m}` universe arguments on a constant. */
  private parseUnivArgs(): SLevel[] {
    return this.braceList(() => this.parseLevel());
  }

  // --- Levels ---------------------------------------------------------------

  private parseLevel(): SLevel {
    let l = this.parseAtomLevel();
    while (this.at("+")) {
      const pos = this.advance().pos;
      const t = this.peek();
      if (t.kind !== "numeral") throw new ParseError(t.pos, "expected a numeral after '+'");
      this.advance();
      l = { kind: "add", base: l, n: BigInt(t.value), pos };
    }
    return l;
  }

  private parseAtomLevel(): SLevel {
    const t = this.peek();
    if (t.kind === "numeral") {
      this.advance();
      return { kind: "num", value: BigInt(t.value), pos: t.pos };
    }
    if (this.at("(")) {
      this.advance();
      const l = this.parseLevel();
      this.expect(")");
      return l;
    }
    if (t.kind === "ident") {
      this.advance();
      if (t.value === "max" || t.value === "imax") {
        const lhs = this.parseAtomLevel();
        const rhs = this.parseAtomLevel();
        return { kind: t.value, lhs, rhs, pos: t.pos };
      }
      return { kind: "ident", name: t.value, pos: t.pos };
    }
    throw new ParseError(t.pos, `expected a universe level, got '${t.value || "<eof>"}'`);
  }
}

/** Parse a whole module (sequence of commands) from source text. */
export function parse(src: string): SModule {
  return new Parser(tokenize(src)).parseModule();
}

/** Parse a single expression from source text (handy for tests and #check). */
export function parseExpr(src: string): SExpr {
  return new Parser(tokenize(src)).parseSingleExpr();
}
