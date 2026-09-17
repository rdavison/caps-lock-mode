/-
# The modal machine

`step` is the whole of CapslockMode's behaviour: a pure function from
(configuration, state, keyboard event) to (new state, events to inject).
Everything else in the project — the stdin/stdout filter, the evdev driver, the
terminal demo, the proofs — is a wrapper around this function.

The vi flavour is deliberately that of a *remapper*: CapslockMode does not own
the text, so a command like `dd` is compiled into the editing keystrokes that
essentially every text widget already understands (`Home`, `Shift+Down`,
`Delete`).  That is what lets it work in a browser, a terminal and an IDE
without knowing anything about them.
-/
import CapslockMode.Key
import CapslockMode.Platform

namespace CapslockMode

/-! ## Modes -/

/-- The three modes. `insert` is "CapslockMode is out of the way". -/
inductive Mode where
  /-- Keys reach the application untouched. -/
  | insert
  /-- Keys are commands. -/
  | normal
  /-- Motions extend a selection; `linewise` records whether `V` started it. -/
  | visual (linewise : Bool)
  deriving DecidableEq, Repr, Inhabited

namespace Mode

def isInsert : Mode → Bool
  | .insert => true
  | _ => false

def isVisual : Mode → Bool
  | .visual _ => true
  | _ => false

/-- What Caps Lock does to a mode. -/
def toggle : Mode → Mode
  | .insert => .normal
  | _ => .insert

def name : Mode → String
  | .insert => "insert"
  | .normal => "normal"
  | .visual false => "visual"
  | .visual true => "visual-line"

end Mode

/-! ## Commands in flight -/

/-- An operator waits for a motion or a text object to tell it what to act on. -/
inductive Operator where
  | delete | change | yank | indent | outdent
  deriving DecidableEq, Repr, Inhabited

namespace Operator

/-- The keystrokes that perform the operator once a selection exists. -/
def apply (p : Platform) : Operator → List Chord
  | .delete => [p.chord false .deleteForward]
  | .change => [p.chord false .deleteForward]
  | .yank => [p.chord false .copy]
  | .indent => [p.chord false .indent]
  | .outdent => [p.chord false .outdent]

/-- `c` drops you into insert mode when it is done. -/
def entersInsert : Operator → Bool
  | .change => true
  | _ => false

/-- The key that selects this operator (and, doubled, makes it linewise). -/
def key : Operator → Char
  | .delete => 'd'
  | .change => 'c'
  | .yank => 'y'
  | .indent => '>'
  | .outdent => '<'

end Operator

/-- A partially typed command. -/
inductive Pending where
  /-- Nothing in flight. -/
  | idle
  /-- `g` has been typed. -/
  | gPrefix
  /-- An operator is waiting for a motion; `count` is the count typed before it. -/
  | operator (op : Operator) (count : Nat)
  /-- An operator saw `i` or `a` and is waiting for the object (`iw`, `aw`). -/
  | textObj (op : Operator) (count : Nat) (inner : Bool)
  /-- `r` is waiting for the replacement character. -/
  | replace
  deriving DecidableEq, Repr, Inhabited

/-- Everything CapslockMode remembers between key presses. -/
structure State where
  mode : Mode := .insert
  pending : Pending := .idle
  /-- The numeric prefix typed so far; `0` means "none typed". -/
  count : Nat := 0
  /-- The keystrokes of the last edit, replayed by `.`. -/
  lastEdit : List Chord := []
  /-- Physical keys whose press CapslockMode forwarded.  Their release has to be
  forwarded too, even if the mode changed in between — otherwise the
  application is left believing a key is still held. -/
  down : List PhysKey := []
  deriving DecidableEq, Repr, Inhabited

namespace State

/-- Settle into normal mode, forgetting any half-typed command. -/
def toNormal (st : State) : State := { st with mode := .normal, pending := .idle, count := 0 }

/-- Hand the keyboard back to the application. -/
def toInsert (st : State) : State := { st with mode := .insert, pending := .idle, count := 0 }

def toVisual (st : State) (linewise : Bool) : State :=
  { st with mode := .visual linewise, pending := .idle, count := 0 }

/-- Remember that we forwarded a press, so that we forward its release. -/
def press (st : State) (k : PhysKey) : State :=
  if st.down.contains k then st else { st with down := k :: st.down }

/-- Forget a forwarded press. -/
def release (st : State) (k : PhysKey) : State :=
  { st with down := st.down.filter (· != k) }

/-- Flip between command mode and typing, keeping physically held keys. -/
def toggleMode (st : State) : State :=
  { st with mode := st.mode.toggle, pending := .idle, count := 0 }

/-- Stay where you are, but remember `p` as the command in flight.  The count
moves into the pending command, so `3dd` is three lines and not nine. -/
def waiting (st : State) (p : Pending) : State :=
  { st with pending := p, count := 0 }

/-- Human-readable state, for the demo and for `mode?` queries. -/
def describe (st : State) : String :=
  let pend :=
    match st.pending with
    | .idle => ""
    | .gPrefix => " g"
    | .operator op _ => s!" {op.key}"
    | .textObj op _ inner => s!" {op.key}{if inner then "i" else "a"}"
    | .replace => " r"
  let cnt := if st.count == 0 then "" else s!" {st.count}"
  st.mode.name ++ cnt ++ pend

end State

/-- Tunables.  The defaults are the ones the README documents. -/
structure Config where
  /-- The key that flips between insert and normal mode. -/
  toggleKey : PhysKey := .capsLock
  /-- Whether `Esc` in insert mode also returns to normal mode. -/
  escapeToNormal : Bool := true
  /-- Mode to start in. -/
  startMode : Mode := .insert
  /-- Which keyboard conventions to compile commands into. -/
  platform : Platform := .pc
  /-- Upper bound on any count, so that a fat-fingered `99999dd` cannot flood
  the system with synthetic events.  Proved to be respected in
  `CapslockMode.Invariants`. -/
  maxCount : Nat := 100
  deriving DecidableEq, Repr, Inhabited

namespace Config

/-- Counts never exceed `maxCount`. -/
def clamp (cfg : Config) (n : Nat) : Nat := min n cfg.maxCount

end Config

/-- A count of `0` means "none typed", which acts as `1`. -/
def normCount (n : Nat) : Nat := max n 1

/-! ## Responses

A response is a little program: play `before` once, then `body` `repeats`
times, then `after` once.  Keeping the repetition explicit is what makes the
"no key storm" bound in `CapslockMode.Invariants` provable. -/

structure Response where
  before : List Chord := []
  body : List Chord := []
  repeats : Nat := 1
  after : List Chord := []
  /-- Whether this command should be remembered for `.`. -/
  records : Bool := false
  state : State
  deriving Inhabited

namespace Response

/-- The chords a response plays, in order. -/
def chords (r : Response) : List Chord :=
  r.before ++ (List.replicate r.repeats r.body).flatten ++ r.after

/-- The events a response injects. -/
def emit (r : Response) : List OutputEvent := emitChords r.chords

/-- The state a response leaves behind: edits are remembered so that `.` can
replay them. -/
def commit (r : Response) : State :=
  if r.records then { r.state with lastEdit := r.chords } else r.state

end Response

/-! ## The key map -/

/-- Selecting one line, ready for a linewise operator. -/
def lineDown (p : Platform) : Chord := p.chord true .lineDown

/-- Motions.  `extend` is set when the motion should drag a selection with it,
which is how operators (`dw`) and visual mode both work. -/
def motion (p : Platform) (extend : Bool) (c : Chord) : Option (List Chord) :=
  let go (i : Intent) : Option (List Chord) := some [p.chord extend i]
  if c.mods.ctrl then
    match c.key with
    | .char 'f' | .char 'd' => go .pageDown
    | .char 'b' | .char 'u' => go .pageUp
    | _ => none
  else if c.mods.alt || c.mods.super then none
  else
    match c.key with
    | .char 'h' | .left => go .charLeft
    | .char 'l' | .right | .space => go .charRight
    | .char 'j' | .down | .enter => go .lineDown
    | .char 'k' | .up => go .lineUp
    | .char 'w' | .char 'W' | .char 'e' | .char 'E' => go .wordRight
    | .char 'b' | .char 'B' => go .wordLeft
    | .char '0' | .home => go .lineStart
    | .char '^' => go .lineStart
    | .char '$' | .«end» => go .lineEnd
    | .char '{' => go .paraUp
    | .char '}' => go .paraDown
    | .pageUp => go .pageUp
    | .pageDown => go .pageDown
    | _ => none

/-- `gg` / `G`, which take a line number rather than a repeat count. -/
def gotoLine (p : Platform) (extend : Bool) (fromTop : Bool) (st : State) (count : Nat) :
    Response :=
  if count == 0 then
    { before := [p.chord extend (if fromTop then .docStart else .docEnd)]
      state := if st.mode.isVisual then st else st.toNormal }
  else
    { before := [p.chord extend .docStart]
      body := [p.chord extend .lineDown]
      repeats := count - 1
      state := if st.mode.isVisual then st.waiting .idle else st.toNormal }

/-- A digit that is part of a count rather than a command. -/
def countDigit? (st : State) (c : Chord) : Option Nat :=
  if c.mods.ctrl || c.mods.alt || c.mods.super then none
  else match c.key with
    | .char ch =>
      if '1' ≤ ch && ch ≤ '9' then some (ch.toNat - '0'.toNat)
      else if ch == '0' && st.count > 0 then some 0
      else none
    | _ => none

/-- Linewise form of an operator: `dd`, `cc`, `yy`, `>>`, `<<`. -/
def linewise (cfg : Config) (st : State) (op : Operator) (n : Nat) : Response :=
  let p := cfg.platform
  let n := cfg.clamp (normCount n)
  let ins := op.entersInsert
  match op with
  | .change =>
      -- select the text of the lines but not the final newline, so `cc` keeps
      -- the line and lets you retype it
      { before := [p.chord false .lineStart]
        body := [lineDown p]
        repeats := n - 1
        after := [p.chord true .lineEnd, p.chord false .deleteForward]
        state := st.toInsert }
  | .yank =>
      -- copy, then collapse the selection on to the next line, which is where
      -- `p` should paste
      { before := [p.chord false .lineStart]
        body := [lineDown p]
        repeats := n
        after := op.apply p ++ [p.chord false .lineStart]
        state := st.toNormal }
  | .indent | .outdent =>
      -- a selection that reaches into the next line would indent it too
      { before := [p.chord false .lineStart]
        body := [lineDown p]
        repeats := n - 1
        after := op.apply p
        records := true
        state := st.toNormal }
  | _ =>
      { before := [p.chord false .lineStart]
        body := [lineDown p]
        repeats := n
        after := op.apply p
        records := !ins && op != .yank
        state := st.toNormal }

/-- An operator applied to a selection made by `sel`. -/
def applyOver (p : Platform) (st : State) (op : Operator) (before body : List Chord)
    (repeats : Nat) : Response :=
  { before := before
    body := body
    repeats := repeats
    -- a charwise yank leaves the cursor at the start of the copied text, as vi does
    after := op.apply p ++ (if op == .yank then [p.chord false .charLeft] else [])
    records := !op.entersInsert && op != .yank
    state := if op.entersInsert then st.toInsert else st.toNormal }

/-- Normal mode: the key is a command. -/
def normalCmd (cfg : Config) (st : State) (c : Chord) : Response :=
  let p := cfg.platform
  let n := cfg.clamp (normCount st.count)
  if c.mods.ctrl then
    match c.key with
    | .char 'r' => { body := [p.chord false .redo], repeats := n, state := st.toNormal }
    | .char 'f' | .char 'd' => { body := [p.chord false .pageDown], repeats := n, state := st.toNormal }
    | .char 'b' | .char 'u' => { body := [p.chord false .pageUp], repeats := n, state := st.toNormal }
    | .char 'v' => { state := st.toVisual false }
    | _ => { before := [c], state := st.toNormal }
  else if c.mods.alt || c.mods.super then
    { before := [c], state := st.toNormal }
  else
    match c.key with
    -- entering insert mode
    | .char 'i' => { state := st.toInsert }
    | .char 'I' => { before := [p.chord false .lineStart], state := st.toInsert }
    | .char 'a' => { before := [p.chord false .charRight], state := st.toInsert }
    | .char 'A' => { before := [p.chord false .lineEnd], state := st.toInsert }
    | .char 'o' => { before := [p.chord false .lineEnd, p.chord false .newline], state := st.toInsert }
    | .char 'O' => { before := [p.chord false .lineStart, p.chord false .newline, p.chord false .lineUp]
                     state := st.toInsert }
    | .char 's' => { body := [p.chord false .deleteForward], repeats := n, state := st.toInsert }
    | .char 'S' => linewise cfg st .change st.count
    | .char 'C' => { before := [p.chord true .lineEnd, p.chord false .deleteForward]
                     state := st.toInsert }
    -- edits that stay in normal mode
    | .char 'x' => { body := [p.chord false .deleteForward], repeats := n, records := true
                     state := st.toNormal }
    | .char 'X' => { body := [p.chord false .deleteBack], repeats := n, records := true
                     state := st.toNormal }
    | .delete => { body := [p.chord false .deleteForward], repeats := n, records := true
                   state := st.toNormal }
    | .backspace => { body := [p.chord false .charLeft], repeats := n, state := st.toNormal }
    | .char 'D' => { before := [p.chord true .lineEnd, p.chord false .deleteForward], records := true
                     state := st.toNormal }
    | .char 'Y' => linewise cfg st .yank st.count
    | .char 'J' => { body := [p.chord false .lineEnd, p.chord false .deleteForward], repeats := n
                     records := true
                     state := st.toNormal }
    | .char 'p' => { body := [p.chord false .paste], repeats := n, records := true
                     state := st.toNormal }
    | .char 'P' => { before := [p.chord false .lineStart], body := [p.chord false .paste]
                     repeats := n, records := true, state := st.toNormal }
    | .char 'u' => { body := [p.chord false .undo], repeats := n, state := st.toNormal }
    | .char '.' => { before := st.lastEdit, state := st.toNormal }
    -- searching
    | .char '/' => { before := [p.chord false .find], state := st.toInsert }
    | .char 'n' => { body := [p.chord false .findNext], repeats := n, state := st.toNormal }
    | .char 'N' => { body := [p.chord false .findPrev], repeats := n, state := st.toNormal }
    -- visual mode
    | .char 'v' => { state := st.toVisual false }
    | .char 'V' => { before := [p.chord false .lineStart, lineDown p], state := st.toVisual true }
    -- commands that wait for more keys
    | .char 'd' => { state := st.waiting (.operator .delete st.count) }
    | .char 'c' => { state := st.waiting (.operator .change st.count) }
    | .char 'y' => { state := st.waiting (.operator .yank st.count) }
    | .char '>' => { state := st.waiting (.operator .indent st.count) }
    | .char '<' => { state := st.waiting (.operator .outdent st.count) }
    | .char 'r' => { state := st.waiting .replace }
    | .char 'g' => { state := st.waiting .gPrefix }
    | .char 'G' => gotoLine p false false st st.count
    | _ =>
      match motion p false c with
      | some ms => { body := ms, repeats := n, state := st.toNormal }
      | none => { state := st.toNormal }

/-- Visual mode: motions grow the selection, operators act on it at once. -/
def visualCmd (cfg : Config) (st : State) (c : Chord) : Response :=
  let p := cfg.platform
  let n := cfg.clamp (normCount st.count)
  let linewise := match st.mode with | .visual lw => lw | _ => false
  if c.mods.ctrl then
    match c.key with
    | .char 'f' | .char 'd' => { body := [p.chord true .pageDown], repeats := n
                                 state := st.waiting .idle }
    | .char 'b' | .char 'u' => { body := [p.chord true .pageUp], repeats := n
                                 state := st.waiting .idle }
    | _ => { before := [c], state := st.toNormal }
  else
    match c.key with
    | .char 'd' | .char 'x' | .delete =>
        { before := [p.chord false .deleteForward], records := true, state := st.toNormal }
    | .char 'c' | .char 's' => { before := [p.chord false .deleteForward], state := st.toInsert }
    | .char 'y' =>
        -- copy, then collapse the selection the way the linewise/charwise
        -- flavours of `y` do in normal mode
        { before := [p.chord false .copy,
                     p.chord false (if linewise then .lineStart else .charLeft)]
          state := st.toNormal }
    | .char '>' => { before := [p.chord false .indent], records := true, state := st.toNormal }
    | .char '<' => { before := [p.chord false .outdent], records := true, state := st.toNormal }
    | .char 'p' => { before := [p.chord false .paste], records := true
                     state := st.toNormal }
    | .char 'v' => if linewise then { state := st.toVisual false } else { state := st.toNormal }
    | .char 'V' => { before := [p.chord false .lineStart, lineDown p], state := st.toVisual true }
    | .char 'g' => { state := st.waiting .gPrefix }
    | .char 'G' => gotoLine p true false st st.count
    | _ =>
      match motion p true c with
      | some ms => { body := ms, repeats := n, state := st.waiting .idle }
      | none => { state := st.waiting .idle }

/-- An operator is pending: a doubled key makes it linewise, `i`/`a` start a
text object, a motion gives it a range, anything else cancels it. -/
def operatorCmd (cfg : Config) (st : State) (op : Operator) (opCount : Nat) (c : Chord) :
    Response :=
  let p := cfg.platform
  let n := cfg.clamp (normCount opCount * normCount st.count)
  if c.mods.ctrl || c.mods.alt || c.mods.super then { state := st.toNormal }
  else match c.key with
    | .char ch =>
        if ch == op.key then linewise cfg st op (normCount opCount * normCount st.count)
        else if ch == 'i' then { state := st.waiting (.textObj op opCount true) }
        else if ch == 'a' then { state := st.waiting (.textObj op opCount false) }
        else
          match motion p true c with
          | some ms => applyOver p st op [] ms n
          | none => { state := st.toNormal }
    | _ =>
      match motion p true c with
      | some ms => applyOver p st op [] ms n
      | none => { state := st.toNormal }

/-- `diw`, `caw`, ... : select the word under the cursor, then act. -/
def textObjCmd (cfg : Config) (st : State) (op : Operator) (opCount : Nat) (_inner : Bool)
    (c : Chord) : Response :=
  let p := cfg.platform
  let n := cfg.clamp (normCount opCount * normCount st.count)
  match c.key with
  | .char 'w' | .char 'W' =>
      applyOver p st op [p.chord false .wordLeft] [p.chord true .wordRight] n
  | _ => { state := st.toNormal }

/-- `g` is pending. -/
def gCmd (p : Platform) (st : State) (c : Chord) : Response :=
  let extend := st.mode.isVisual
  match c.key with
  | .char 'g' => gotoLine p extend true st st.count
  | .char 'e' => { before := [p.chord extend .wordLeft], state := st.waiting .idle }
  | _ => { state := if st.mode.isVisual then st.waiting .idle else st.toNormal }

/-- `r` is pending: the next character overwrites the one under the cursor. -/
def replaceCmd (p : Platform) (st : State) (c : Chord) : Response :=
  match c.key with
  | .char ch => { before := [p.chord true .charRight, Chord.plain (.char ch)]
                  records := true, state := st.toNormal }
  | _ => { state := st.toNormal }

/-- Interpret one key press while CapslockMode is in charge of the keyboard. -/
def command (cfg : Config) (st : State) (c : Chord) : Response :=
  if c.key == Key.esc then
    { state := st.toNormal }
  else match st.pending with
  | .replace => replaceCmd cfg.platform st c
  | pend =>
    match countDigit? st c with
    | some d => { state := { st with count := cfg.clamp (st.count * 10 + d) } }
    | none =>
      match pend with
      | .gPrefix => gCmd cfg.platform st c
      | .textObj op n inner => textObjCmd cfg st op n inner c
      | .operator op n => operatorCmd cfg st op n c
      | _ => if st.mode.isVisual then visualCmd cfg st c else normalCmd cfg st c

/-- The modifier state a chord is looked up with. -/
def InputEvent.chord? (ev : InputEvent) : Option Chord :=
  match ev.key with
  | .key k => some { mods := ev.mods, key := k }
  | _ => none

/-- **The** function: one keyboard event in, a new state and the events to
inject out.

Releases are handled first and uniformly: CapslockMode forwards a key-up
exactly when it forwarded the matching key-down, whatever has happened to the
mode in between.  That is what keeps a key from getting stuck when you hit Caps
Lock with a finger still down, and it is what `up_only_if_pressed` proves. -/
def step (cfg : Config) (st : State) (ev : InputEvent) : State × List OutputEvent :=
  if ev.injected then
    -- our own event, already on its way to the application: hands off
    (st, [ev.passthrough])
  else match ev.dir with
  | .up =>
    if st.down.contains ev.key then (st.release ev.key, [⟨.up, ev.key⟩]) else (st, [])
  | .down =>
    if ev.key == cfg.toggleKey then
      (st.toggleMode, [])
    else if st.mode.isInsert then
      if cfg.escapeToNormal && ev.key == PhysKey.key .esc then
        ({ st with mode := .normal, pending := .idle, count := 0 }, [])
      else
        (st.press ev.key, [ev.passthrough])
    else
      match ev.chord? with
      | none => (st, [])
      | some c => ((command cfg st c).commit, (command cfg st c).emit)

/-- Feed a whole stream of events through the machine. -/
def run (cfg : Config) (st : State) : List InputEvent → State × List OutputEvent
  | [] => (st, [])
  | ev :: evs =>
    let (st₁, out₁) := step cfg st ev
    let (st₂, out₂) := run cfg st₁ evs
    (st₂, out₁ ++ out₂)

/-- The initial state for a configuration. -/
def Config.start (cfg : Config) : State := { mode := cfg.startMode }

end CapslockMode
