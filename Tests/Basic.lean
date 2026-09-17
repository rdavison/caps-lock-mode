/-
# Tests

The proofs in `CapslockMode.Invariants` cover the properties that must hold for
*every* key and *every* state.  These tests cover the other half: that the key
map actually does what a vi user expects, judged by typing into an ordinary
text field (`CapslockMode.Screen`) and looking at the result.

Every `#guard` below is checked when this file is compiled, so `lake build`
runs the test suite.
-/
import CapslockMode

namespace CapslockMode.Tests
open CapslockMode

/-- Normal mode from the start, which is what a test wants. -/
private def N : Config := { startMode := .normal }

private def sample : String := "alpha beta\ngamma delta\nepsilon zeta"

/-- Type `script` into `text` and return the resulting buffer. -/
def edit (text script : String) (cfg : Config := N) : String :=
  let (_, out) := run cfg cfg.start (parseScript script)
  ((Screen.ofText text).applyAll out).text

/-- The mode a script leaves the machine in. -/
def modeAfter (script : String) (cfg : Config := N) : String :=
  (run cfg cfg.start (parseScript script)).1.describe

/-- The keystrokes a script produces. -/
def emitted (script : String) (cfg : Config := N) : String :=
  renderEvents (run cfg cfg.start (parseScript script)).2

/-! ## Motions -/

#guard emitted "h" == "left"
#guard emitted "j" == "down"
#guard emitted "w" == "ctrl+right"
#guard emitted "3j" == "down down down"
#guard emitted "$" == "end"
#guard emitted "gg" == "ctrl+home"
#guard emitted "G" == "ctrl+end"

/-! ## Edits -/

#guard edit sample "dw" == "beta\ngamma delta\nepsilon zeta"
#guard edit sample "3x" == "ha beta\ngamma delta\nepsilon zeta"
#guard edit sample "dd" == "gamma delta\nepsilon zeta"
#guard edit sample "2dd" == "epsilon zeta"
#guard edit sample "jdd" == "alpha beta\nepsilon zeta"
#guard edit sample "D" == "\ngamma delta\nepsilon zeta"
#guard edit sample "A!<Esc>" == "alpha beta!\ngamma delta\nepsilon zeta"
#guard edit sample "ihi <Esc>" == "hi alpha beta\ngamma delta\nepsilon zeta"
#guard edit sample "oNEW<Esc>" == "alpha beta\nNEW\ngamma delta\nepsilon zeta"
#guard edit sample "ONEW<Esc>" == "NEW\nalpha beta\ngamma delta\nepsilon zeta"
#guard edit sample "r_" == "_lpha beta\ngamma delta\nepsilon zeta"
#guard edit sample ">>" == "  alpha beta\ngamma delta\nepsilon zeta"
#guard edit sample "cwX<Esc>" == "Xbeta\ngamma delta\nepsilon zeta"
#guard edit sample "wD" == "alpha \ngamma delta\nepsilon zeta"

-- A count in front of an operator and a count in front of its motion multiply, as they do in vi: `d2w` and `2dw` both delete two words.
#guard edit sample "d2w" == "\ngamma delta\nepsilon zeta"
#guard edit sample "2dw" == "\ngamma delta\nepsilon zeta"
#guard emitted "3dd" == "home shift+down shift+down shift+down del"

/-! ## Copy, paste, undo, repeat -/

#guard edit sample "yyp" == "alpha beta\nalpha beta\ngamma delta\nepsilon zeta"
#guard edit sample "Vyp" == "alpha beta\nalpha beta\ngamma delta\nepsilon zeta"
#guard edit sample "ywP" == "alpha alpha beta\ngamma delta\nepsilon zeta"
#guard edit sample "ddu" == sample
#guard edit sample "x." == "pha beta\ngamma delta\nepsilon zeta"
-- `.` replays the keystrokes of the last edit, so `dw.` deletes two words
#guard edit sample "dw." == "\ngamma delta\nepsilon zeta"
#guard edit sample "Vd" == "gamma delta\nepsilon zeta"
#guard edit sample "vjd" == "gamma delta\nepsilon zeta"

/-! ## Modes -/

#guard modeAfter "" (cfg := {}) == "insert"
#guard modeAfter "<Caps>" (cfg := {}) == "normal"
#guard modeAfter "<Caps><Caps>" (cfg := {}) == "insert"
#guard modeAfter "i" == "insert"
#guard modeAfter "v" == "visual"
#guard modeAfter "V" == "visual-line"
#guard modeAfter "3" == "normal 3"
#guard modeAfter "3d" == "normal d"
#guard modeAfter "di" == "normal di"
#guard modeAfter "3d<Esc>" == "normal"
#guard modeAfter "v<Esc>" == "normal"
#guard modeAfter "i<Esc>" == "normal"

-- Caps Lock is a round trip, whatever was half-typed when you pressed it.
#guard modeAfter "2d<Caps><Caps>" == "normal"

/-! ## Insert mode is out of the way -/

#guard edit sample "X" (cfg := {}) == "Xalpha beta\ngamma delta\nepsilon zeta"
#guard edit sample "<Caps>dd<Caps>Z" (cfg := {}) == "Zgamma delta\nepsilon zeta"

-- Nothing is swallowed and nothing is invented while CapslockMode is off.
#guard
  let evs := parseScript "hello, world!"
  (run {} ({} : Config).start evs).2 == evs.map InputEvent.passthrough

/-! ## No stuck keys, checked rather than proved

`CapslockMode.step_balanced` proves this for every input.  Running the same
check over the key map is a cheap way to notice if the two ever disagree. -/

/-- Are all presses matched by releases, with no key pressed twice? -/
def balancedB (l : List OutputEvent) : Bool :=
  let rec go : List OutputEvent → List PhysKey → Bool
    | [], held => held.isEmpty
    | e :: rest, held =>
      match e.dir with
      | .down => if held.contains e.key then false else go rest (e.key :: held)
      | .up => if held.contains e.key then go rest (held.filter (· != e.key)) else false
  go l []

private def allScripts : List String :=
  [ "dd", "3dd", "dw", "d2w", "diw", "cw", "cc", "yy", "yw", "p", "P", "u", "<C-r>"
  , ">>", "<<", "x", "X", "D", "C", "J", "r_", "A", "I", "o", "O", "v", "V", "vjd"
  , "gg", "G", "5G", "<C-f>", "<C-b>", "/", "n", "N", ".", "x.", "2wdw", "vjy" ]

#guard allScripts.all fun s => balancedB (run N N.start (parseScript s)).2

/-! ## The wire protocol -/

#guard (parseLine? "down a").isSome
#guard (parseLine? "down r ctrl").map (fun l => match l with
  | .event ev => ev.mods.ctrl && ev.key == PhysKey.key (.char 'r')
  | _ => false) == some true
#guard (parseLine? "# a comment").isSome
#guard (parseLine? "sideways q").isNone
#guard (OutputEvent.down (.key .home)).line == "down home"
#guard (OutputEvent.up (.mod .ctrl)).line == "up ctrl"
#guard Chord.name { mods := { ctrl := true, shift := true }, key := .right } == "ctrl+shift+right"

-- Key scripts and the protocol agree about what a key is.
#guard parseScript "<C-r>" == [{ dir := .down, key := .key (.char 'r'), mods := { ctrl := true } },
                               { dir := .up, key := .key (.char 'r'), mods := { ctrl := true } }]
#guard (parseScript "<<").length == 4

end CapslockMode.Tests
