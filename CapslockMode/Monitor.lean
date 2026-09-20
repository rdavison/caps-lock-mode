/-
`CapslockMode.Monitor` renders what the machine just did, one input event at a
time, as a line a driver can display without knowing anything about keys.

This exists because a driver *cannot* render these rows itself.  The Swift and
Python bridges deliberately carry no key table -- they see keycode 123, not
`left` -- so a human-readable monitor has to be written on this side.  The
division is: Lean decides what a row says, the driver decides how many rows to
keep and how to draw them.

Everything here is pure.  There is no clock: a driver that wants timestamps has
one already (macOS taps carry `CGEventTimestamp`), and keeping this module
timeless keeps it testable.

A note on naming.  `Chord.name` spells the Command key `super`, because that is
what the key map calls it on every platform, while the Quartz *wire* spells the
same modifier `command` in its flag masks.  Rows use `Chord.name`, so a monitor
agrees with `capslockmode trace` and `capslockmode keys` rather than with the
wire.  The two vocabularies meet only in `Protocol.Quartz`.
-/
import CapslockMode.Protocol

namespace CapslockMode
namespace Monitor

/-- What the machine did with one input event.

The distinction is the whole point of a monitor: a driver that swallows an event
and injects a replacement looks identical to a driver that is broken, unless you
can see which of the three happened. -/
inductive Verdict where
  /-- Handed straight back, unchanged. -/
  | passed
  /-- Swallowed, with something else emitted in its place. -/
  | rewritten
  /-- Swallowed, nothing emitted -- a half-typed command waiting for more. -/
  | held
  deriving DecidableEq, Repr, Inhabited

def Verdict.name : Verdict → String
  | .passed => "pass"
  | .rewritten => "rewrite"
  | .held => "hold"

/-- One input event and what it produced.  `state` is the state *after* the
event, which is what a reader wants to see next to it. -/
structure Entry where
  input : InputEvent
  state : State
  out : List OutputEvent
  /-- What the wire called this key, before any naming: the virtual keycode on
  the Quartz wire, empty elsewhere.

  It is here because the name alone can mislead.  Another remapper upstream --
  kanata, Karabiner -- substitutes keys before they reach us, so pressing `s`
  can legitimately arrive as the code for `i`; showing both makes the layering
  visible instead of looking like a bug in the naming. -/
  code : String := ""
  deriving Inhabited

/-- Which of the three things happened.  `passthrough` is the same function the
machine uses to pass an event on, so this cannot drift from the real definition
of "unchanged". -/
def Entry.verdict (e : Entry) : Verdict :=
  if e.out.isEmpty then .held
  else if e.out == [e.input.passthrough] then .passed
  else .rewritten

/-- The name of the key that arrived.

Modifiers and Caps Lock have no chord spelling, so they fall back to the plain
physical name; an ordinary key is named together with the modifiers the driver
reported, so `Ctrl+S` reads as one thing rather than two rows. -/
def inputName (ev : InputEvent) : String :=
  match ev.key with
  | .key k => Chord.name { mods := ev.mods, key := k }
  | k => k.name

/-- The shared table row: key, mode, emitted.  `capslockmode trace` prints
exactly this, so the monitor and the trace command cannot drift apart. -/
def row (name : String) (st : State) (out : List OutputEvent) : String :=
  s!"{pad name 8}{pad st.describe 14}{renderEvents out}"

/-- The monitor row: direction and verdict as well, since a monitor sees releases
and pass-throughs that `trace` hides. -/
def entryRow (e : Entry) : String :=
  let mark := if e.input.injected then "*" else " "
  let code := if e.code.isEmpty then "-" else e.code
  s!"{mark}{pad e.input.dir.name 5}{pad code 5}{pad (inputName e.input) 10}\
{pad e.verdict.name 8}{pad e.state.describe 14}{renderEvents e.out}"

/-! ## Wire

Monitor lines share stdout with the events a driver is meant to inject, so they
carry a prefix no injectable line can have.  A driver that does not understand
them can drop every line starting with `mon `. -/

/-- A row, as it travels to a driver. -/
def line (e : Entry) : String := s!"mon row {entryRow e}"

/-- The keycode a Quartz event carries, for the `code` column.  Flags and
synthesised text have none. -/
def codeOf : Quartz.Event → String
  | .key _ c _ => toString c
  | .text _ _ _ => ""
  | .flagsChanged _ => ""

/-- A wire line that produced no events at all.

Worth its own line because the alternative is silence, and silence is how a
missing entry in the keycode table hides: the key is pressed, nothing appears,
and nothing says why.  A dropped line is a fact about the table, not noise. -/
def dropLine (wire : String) : String := s!"mon drop {wire}"

/-! ## Where events came from

A driver may sit below other software that rewrites keys before we ever see
them -- kanata and Karabiner re-emit through a kernel HID driver, so an event
tap cannot observe the original press at all.  That makes two different
silences look alike: a key the layer above swallowed, and a key that arrived
with no entry in the keycode table.  Reporting the device the events carry
tells them apart, and shows a keyboard the layer above is *not* grabbing.

The driver only copies two integers off the event.  Remembering them, deciding
what counts as a change, and saying it in words are all here, so the platform
side stays a wire and nothing more. -/

/-- The device an event claims to come from.  `pid` is the process that posted
it; hardware and kernel drivers report 0. -/
structure Device where
  kbType : Nat
  pid : Nat
  deriving DecidableEq, Repr, Inhabited

def Device.describe (d : Device) : String :=
  let src := if d.pid == 0 then "a device or driver" else s!"pid {d.pid}"
  s!"keyboard type {d.kbType}, posted by {src}"

/-- `dev <keyboardType> <pid>`, as a driver spells it.

This is a control line rather than another token on the event line: the Quartz
event parser matches exact arities, so a fourth field would make every event
unparseable. -/
def parseDevice? (s : String) : Option Device :=
  match (s.trim.splitOn " ").filter (fun w => !w.isEmpty) with
  | ["dev", t, p] =>
    if !t.isEmpty && t.all Char.isDigit && !p.isEmpty && p.all Char.isDigit then
      some { kbType := t.toNat!, pid := p.toNat! }
    else none
  | _ => none

def deviceLine (d : Device) : String := s!"mon device {d.describe}"

/-- The whole reporting policy, kept pure so it can be checked: say something
the first time, and thereafter only when the device actually changes.  A line
per keystroke would bury the log it is meant to explain. -/
def deviceChange? (old : Option Device) (new : Device) : Option String :=
  if old == some new then none else some (deviceLine new)

/-- The summary line: the machine's current mode, count and pending operator. -/
def stateLine (st : State) : String := s!"mon state {st.describe}"

/-- The column header a driver can show above the rows.  Here rather than in the
driver so the widths cannot disagree with `entryRow`. -/
def header : String :=
  s!" {pad "dir" 5}{pad "code" 5}{pad "key" 10}{pad "did" 8}{pad "mode" 14}emitted"

/-- The header, as it travels to a driver. -/
def headerLine : String := s!"mon header {header}"

end Monitor
end CapslockMode
