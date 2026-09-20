/-
# Reading kanata's s-expressions

kanata configs look like Lisp and are not.  The three rules that catch people
out, all copied from kanata's own `parser/src/cfg/sexpr.rs` rather than from
what a Lisp reader would do:

* An atom ends at `(`, `)`, `"` or ASCII whitespace -- and at nothing else.  So
  `S-,` and `@grv-mode` and `▶⏸` are each one atom, and a reader that stops at
  punctuation splits them.
* A **lone** `;` is an atom; only `;;` starts a comment.  A reader that treats
  `;` as a comment introducer eats the rest of the line, and the real config
  puts `;` in four different layers.
* Strings never span a line and carry no escapes: the lexer scans to the next
  `"` or newline and demands the `"`.

This reader works over `List Char`, not bytes, because the F-row of the fixture
is spelled with emoji.  A byte-oriented reader would split `🔅` into four atoms
that are not valid UTF-8 on their own.

Deliberately absent, and all hard errors downstream rather than silent
mis-reads: `r#"..."#` raw strings, `$var` substitution, and `deftemplate`
expansion.  None appears in any config this evaluator is aimed at.
-/

namespace CapslockMode.Kanata

/-- One datum.  `str` is kept apart from `atom` because `defcfg`'s
`macos-dev-names-include` holds device names with spaces in them, and rendering
the option back to text has to put the quotes back. -/
inductive Sexp where
  | atom (s : String)
  | str (s : String)
  | list (xs : List Sexp)
  deriving Repr, Inhabited

namespace Sexp

/-- Back to text.  Round-tripping is not exact -- comments and layout are gone,
and every list is re-spaced -- which is all `Cfg.options` needs, since it only
ever shows an option back to a reader.

No `DecidableEq` on `Sexp`: an inductive recursive through `List` is not a safe
bet for the deriving handler in Lean 4.34, and everything that wants to compare
two `Sexp`s can compare their renderings instead. -/
partial def render : Sexp → String
  | .atom s => s
  | .str s => "\"" ++ s ++ "\""
  | .list xs => "(" ++ String.intercalate " " (xs.map render) ++ ")"

end Sexp

/-- A character that ends an atom. -/
private def isDelim (c : Char) : Bool :=
  c == '(' || c == ')' || c == '"' || c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Collect an atom's characters.  Never consumes the delimiter. -/
private def takeAtom : List Char → List Char → (List Char × List Char)
  | acc, [] => (acc.reverse, [])
  | acc, c :: cs => if isDelim c then (acc.reverse, c :: cs) else takeAtom (c :: acc) cs

/-- Drop to the end of the line, for a `;;` comment. -/
private def toEol : List Char → Nat → (List Char × Nat)
  | [], ln => ([], ln)
  | '\n' :: cs, ln => (cs, ln + 1)
  | _ :: cs, ln => toEol cs ln

/-- Drop to `|#`.  Block comments do not nest, exactly as in kanata. -/
private def toBlockEnd : List Char → Nat → Except String (List Char × Nat)
  | [], ln => .error s!"line {ln}: unterminated block comment, expected |#"
  | '|' :: '#' :: cs, ln => .ok (cs, ln)
  | '\n' :: cs, ln => toBlockEnd cs (ln + 1)
  | _ :: cs, ln => toBlockEnd cs ln

/-- Read a string body, having already consumed the opening quote. -/
private def takeStr : List Char → List Char → Nat → Except String (String × List Char)
  | _, [], ln => .error s!"line {ln}: unterminated string"
  | _, '\n' :: _, ln => .error s!"line {ln}: unterminated string (a string may not span lines)"
  | acc, '"' :: cs, _ => .ok (String.ofList acc.reverse, cs)
  | acc, c :: cs, ln => takeStr (c :: acc) cs ln

/-- Skip whitespace and both comment forms. -/
private partial def skipBlank (cs : List Char) (ln : Nat) : Except String (List Char × Nat) :=
  match cs with
  | [] => .ok ([], ln)
  | '\n' :: rest => skipBlank rest (ln + 1)
  | ' ' :: rest | '\t' :: rest | '\r' :: rest => skipBlank rest ln
  | ';' :: ';' :: rest => let (rest, ln) := toEol rest ln; skipBlank rest ln
  | '#' :: '|' :: rest => do let (rest, ln) ← toBlockEnd rest ln; skipBlank rest ln
  | _ => .ok (cs, ln)

mutual

/-- Read forms until end of input, or until a `)` when `closing` is set.

`closing` is what makes an unbalanced paren an error on both sides: at top
level a `)` has nothing to close, and inside a list the end of input has
nothing that closed it. -/
private partial def readSeq (cs : List Char) (ln : Nat) (closing : Bool) (acc : List Sexp) :
    Except String (List Sexp × List Char × Nat) := do
  let (cs, ln) ← skipBlank cs ln
  match cs with
  | [] =>
    if closing then .error s!"line {ln}: unbalanced '(' — end of input inside a list"
    else .ok (acc.reverse, [], ln)
  | ')' :: rest =>
    if closing then .ok (acc.reverse, rest, ln)
    else .error s!"line {ln}: unbalanced ')'"
  | _ => do
    let (x, cs, ln) ← readOne cs ln
    readSeq cs ln closing (x :: acc)

/-- Read one form.  The caller has already skipped blanks, so `cs` starts on a
significant character. -/
private partial def readOne (cs : List Char) (ln : Nat) :
    Except String (Sexp × List Char × Nat) := do
  match cs with
  | '(' :: rest => do
    let (xs, cs, ln) ← readSeq rest ln true []
    .ok (.list xs, cs, ln)
  | '"' :: rest => do
    let (s, cs) ← takeStr [] rest ln
    .ok (.str s, cs, ln)
  | _ =>
    let (atom, cs') := takeAtom [] cs
    if atom.isEmpty then
      -- Unreachable while `readSeq` is the only caller, but an empty atom here
      -- would spin forever, so it is a stated error rather than a hang.
      .error s!"line {ln}: expected a form"
    else .ok (.atom (String.ofList atom), cs', ln)

end

/-- Every top-level form in a config, in file order. -/
def read (s : String) : Except String (List Sexp) := do
  let (xs, _, _) ← readSeq s.toList 1 false []
  return xs

end CapslockMode.Kanata
