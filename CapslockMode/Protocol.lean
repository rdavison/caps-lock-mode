/-
# The wire protocol

CapslockMode does not talk to the kernel itself.  It is a filter: keyboard
events arrive on stdin as text, injected events leave on stdout as text.  A
tiny platform-specific driver (see `drivers/`) does the privileged work of
grabbing a device and synthesising events.

    down a            -- key `a` pressed, no modifiers
    down r ctrl       -- Ctrl+R pressed
    up caps           -- Caps Lock released
    ?                 -- ask for the current mode (answered on stderr-ish `# ` line)

Output is the same vocabulary, minus modifier sets, because CapslockMode always
spells modifiers out as their own press/release events:

    down ctrl
    down right
    up right
    up ctrl
-/
import CapslockMode.Machine
import CapslockMode.Backend.Quartz

namespace CapslockMode

/-! ## Names -/

/-- Pad `s` on the right to `n` characters, for table output.  An over-long
field still gets one space, so columns never run together. -/
def pad (s : String) (n : Nat) : String :=
  s ++ String.ofList (List.replicate (max 1 (n - s.length)) ' ')

def Key.name : Key → String
  | .char c => if c == ' ' then "space" else String.singleton c
  | .esc => "esc"
  | .tab => "tab"
  | .enter => "enter"
  | .backspace => "bs"
  | .delete => "del"
  | .space => "space"
  | .left => "left"
  | .right => "right"
  | .up => "up"
  | .down => "down"
  | .home => "home"
  | .«end» => "end"
  | .pageUp => "pgup"
  | .pageDown => "pgdn"
  | .f n => s!"f{n}"

def Modifier.name : Modifier → String
  | .shift => "shift"
  | .ctrl => "ctrl"
  | .alt => "alt"
  | .super => "super"

def PhysKey.name : PhysKey → String
  | .key k => k.name
  | .mod m => m.name
  | .capsLock => "caps"

def Dir.name : Dir → String
  | .down => "down"
  | .up => "up"

def Mods.name (m : Mods) : String :=
  String.intercalate "+" (m.held.map Modifier.name)

def Chord.name (c : Chord) : String :=
  if c.mods.held.isEmpty then c.key.name else s!"{c.mods.name}+{c.key.name}"

def OutputEvent.line (e : OutputEvent) : String := s!"{e.dir.name} {e.key.name}"

/-! ## Parsing -/

private def parseNat? (s : String) : Option Nat :=
  if s.isEmpty || !s.all Char.isDigit then none else some s.toNat!

def parsePhysKey? (s : String) : Option PhysKey :=
  match s with
  | "esc" => some (.key .esc)
  | "tab" => some (.key .tab)
  | "enter" | "ret" | "cr" => some (.key .enter)
  | "bs" | "backspace" => some (.key .backspace)
  | "del" | "delete" => some (.key .delete)
  | "space" | "spc" => some (.key .space)
  | "left" => some (.key .left)
  | "right" => some (.key .right)
  | "up" => some (.key .up)
  | "down" => some (.key .down)
  | "home" => some (.key .home)
  | "end" => some (.key .«end»)
  | "pgup" | "pageup" => some (.key .pageUp)
  | "pgdn" | "pagedown" => some (.key .pageDown)
  | "caps" | "capslock" => some .capsLock
  | "shift" => some (.mod .shift)
  | "ctrl" | "control" => some (.mod .ctrl)
  | "alt" => some (.mod .alt)
  | "super" | "meta" | "win" | "cmd" => some (.mod .super)
  | _ =>
    match s.toList with
    | [c] => some (.key (.char c))
    | 'f' :: digits => (parseNat? (String.ofList digits)).map (fun n => .key (.f n))
    | _ => none

def parseMods? (s : String) : Option Mods :=
  let parts := (s.splitOn ",").filter (fun p => !p.isEmpty)
  parts.foldlM (init := ({} : Mods)) fun m p =>
    match p with
    | "shift" => some { m with shift := true }
    | "ctrl" | "control" => some { m with ctrl := true }
    | "alt" => some { m with alt := true }
    | "super" | "meta" | "win" | "cmd" => some { m with super := true }
    | _ => none

/-- One line of the input protocol. -/
inductive Line where
  /-- A keyboard event. -/
  | event (ev : InputEvent)
  /-- A request to print the current mode. -/
  | query
  /-- A request to return to a known state. -/
  | reset
  /-- A comment or blank line. -/
  | ignore
  deriving Repr, Inhabited

def parseLine? (s : String) : Option Line :=
  let s := s.trim
  if s.isEmpty || s.toList.head? == some '#' then some .ignore
  else if s == "?" then some .query
  else if s == "reset" then some .reset
  else
    match s.splitOn " " |>.filter (fun w => !w.isEmpty) with
    | [d, k] | [d, k, _] =>
      let dir? : Option Dir :=
        match d with
        | "down" | "d" | "press" => some .down
        | "up" | "u" | "release" => some .up
        | _ => none
      let mods? : Option Mods :=
        match s.splitOn " " |>.filter (fun w => !w.isEmpty) with
        | [_, _, m] => parseMods? m
        | _ => some {}
      match dir?, parsePhysKey? k, mods? with
      | some dir, some key, some mods => some (.event { dir, key, mods })
      | _, _, _ => none
    | _ => none

/-! ## Vim-style key scripts

`"ifoo<Esc>3dd"` is a far nicer way to write a test than twenty protocol lines,
and it is the notation everybody already knows from `:help key-notation`. -/

private def specialKey? (name : String) : Option InputEvent :=
  let lower := name.toLower
  -- `<C-r>`, `<A-x>`, `<S-Tab>`: a modifier prefix on a key
  let withMods (m : Mods) (rest : String) : Option InputEvent :=
    (parsePhysKey? rest.toLower).map fun k => { dir := .down, key := k, mods := m }
  if lower.startsWith "c-" then withMods { ctrl := true } (name.drop 2).toString
  else if lower.startsWith "a-" || lower.startsWith "m-" then withMods { alt := true } (name.drop 2).toString
  else if lower.startsWith "s-" then withMods { shift := true } (name.drop 2).toString
  else match lower with
    | "caps" | "capslock" => some { dir := .down, key := .capsLock }
    | "lt" => some { dir := .down, key := .key (.char '<') }
    | "gt" => some { dir := .down, key := .key (.char '>') }
    | "nop" => none
    | _ => (parsePhysKey? lower).map fun k => { dir := .down, key := k }

/-- Turn `"ihello<Esc>dd"` into the events a keyboard would produce.  Each key
is pressed and released, which is what real hardware does and what the
no-stuck-keys proof is about. -/
partial def parseScript (s : String) : List InputEvent :=
  let rec go (cs : List Char) (acc : List InputEvent) : List InputEvent :=
    match cs with
    | [] => acc.reverse
    | '<' :: rest =>
      -- `<C-r>`, `<Esc>`, ... but a bare `<` (as in `<<`) is just a key
      match rest.splitOnP (· == '>') with
      | name :: next :: tail =>
        -- there really was a closing `>`
        let tailStr := String.intercalate ">" ((next :: tail).map String.ofList)
        match specialKey? (String.ofList name) with
        | some ev => go tailStr.toList (ev :: acc)
        | none => go rest ({ dir := .down, key := .key (.char '<') } :: acc)
      | _ => go rest ({ dir := .down, key := .key (.char '<') } :: acc)
    | c :: rest =>
      let ev : InputEvent := { dir := .down, key := .key (.char c) }
      go rest (ev :: acc)
  -- every press is followed by its release
  (go s.toList []).flatMap fun ev => [ev, { ev with dir := .up }]

/-! ## Rendering events back as chords

Useful for `capslockmode keys` and for test output: turn a raw event stream
back into the readable `ctrl+shift+right` form. -/

/-- Fold a raw event stream into chord names, tracking modifier state. -/
def renderChords (es : List OutputEvent) : List String :=
  let rec go (es : List OutputEvent) (m : Mods) (acc : List String) : List String :=
    match es with
    | [] => acc.reverse
    | e :: rest =>
      match e.key, e.dir with
      | .mod k, .down => go rest (m.set k true) acc
      | .mod k, .up => go rest (m.set k false) acc
      | .key k, .down => go rest m (Chord.name { mods := m, key := k } :: acc)
      | _, _ => go rest m acc
  go es {} []

def renderEvents (es : List OutputEvent) : String :=
  " ".intercalate (renderChords es)

/-! ## The Quartz wire

macOS drivers speak keycodes and flag masks rather than key names, so
`--wire quartz` uses a second, equally boring line format.  Because the
keycodes travel on the wire, the driver needs no key table of its own:

    down 4 command          a tap saw kVK_ANSI_H pressed with Cmd held
    flags shift,command     a kCGEventFlagsChanged carrying a new mask
    key down 123 shift      inject Shift+Left
    text down x             type the character `x` (no keycode on this layout)
-/

namespace Quartz

def Flags.names (f : Flags) : String :=
  let parts :=
    (if f.control then ["ctrl"] else []) ++ (if f.option then ["alt"] else []) ++
    (if f.shift then ["shift"] else []) ++ (if f.command then ["command"] else [])
  if parts.isEmpty then "-" else String.intercalate "," parts

def parseFlags? (s : String) : Option Flags :=
  if s == "-" then some {}
  else
    ((s.splitOn ",").filter (fun p => !p.isEmpty)).foldlM (init := ({} : Flags)) fun f p =>
      match p with
      | "shift" => some { f with shift := true }
      | "ctrl" | "control" => some { f with control := true }
      | "alt" | "option" => some { f with option := true }
      | "command" | "cmd" | "super" | "meta" => some { f with command := true }
      | _ => none

/-- How CapslockMode spells an event it wants injected. -/
def Event.line : Event → String
  | .key dir code f => s!"key {dir.name} {code} {Flags.names f}"
  | .text dir ch f => s!"text {dir.name} {ch} {Flags.names f}"
  | .flagsChanged f => s!"flags {Flags.names f}"

/-- One line from a tap.  The optional trailing `injected` marks an event the
tap recognised as our own. -/
def parseLine? (s : String) : Option (Event × Bool) :=
  let ws := (s.trim.splitOn " ").filter (fun w => !w.isEmpty)
  let injected := ws.contains "injected"
  let ws := ws.filter (fun w => w != "injected")
  let dir? : String → Option Dir := fun w =>
    match w with
    | "down" | "d" | "press" => some .down
    | "up" | "u" | "release" => some .up
    | _ => none
  match ws with
  | ["flags", f] => (parseFlags? f).map (fun f => (.flagsChanged f, injected))
  | [d, code] =>
    match dir? d, parseNat? code with
    | some dir, some c => some (.key dir (UInt16.ofNat c) {}, injected)
    | _, _ => none
  | [d, code, f] =>
    match dir? d, parseNat? code, parseFlags? f with
    | some dir, some c, some fl => some (.key dir (UInt16.ofNat c) fl, injected)
    | _, _, _ => none
  | _ => none

end Quartz

/-- Every command CapslockMode documents, as a key script and a description.
`capslockmode keys` renders it by running each script through the machine, and
`Tests/Quartz.lean` checks that every chord they produce can be named to
macOS. -/
def keyTable : List (String × String) :=
  [ ("h", "left"), ("j", "down"), ("k", "up"), ("l", "right")
  , ("w", "next word"), ("b", "previous word"), ("0", "start of line"), ("$", "end of line")
  , ("gg", "top of file"), ("G", "end of file"), ("5G", "line 5"), ("{", "paragraph up")
  , ("}", "paragraph down"), ("<C-f>", "page down"), ("<C-b>", "page up")
  , ("i", "insert here"), ("a", "insert after"), ("I", "insert at line start")
  , ("A", "insert at line end"), ("o", "open line below"), ("O", "open line above")
  , ("x", "delete char"), ("3x", "delete 3 chars"), ("X", "backspace"), ("r", "replace char (r<char>)")
  , ("D", "delete to end of line"), ("C", "change to end of line"), ("J", "join lines")
  , ("dd", "delete line"), ("3dd", "delete 3 lines"), ("dw", "delete word")
  , ("d$", "delete to end of line"), ("diw", "delete inner word"), ("cw", "change word")
  , ("cc", "change line"), ("yy", "yank line"), ("yw", "yank word"), ("p", "paste")
  , ("P", "paste before"), ("u", "undo"), ("<C-r>", "redo"), (".", "repeat last edit")
  , (">>", "indent line"), ("<<", "outdent line"), ("v", "visual mode"), ("V", "visual line")
  , ("/", "search (then type in insert mode)"), ("n", "next match"), ("N", "previous match")
  ]

end CapslockMode
