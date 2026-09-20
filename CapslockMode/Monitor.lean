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
  s!"{mark}{pad e.input.dir.name 5}{pad (inputName e.input) 10}\
{pad e.verdict.name 8}{pad e.state.describe 14}{renderEvents e.out}"

/-! ## Wire

Monitor lines share stdout with the events a driver is meant to inject, so they
carry a prefix no injectable line can have.  A driver that does not understand
them can drop every line starting with `mon `. -/

/-- A row, as it travels to a driver. -/
def line (e : Entry) : String := s!"mon row {entryRow e}"

/-- The summary line: the machine's current mode, count and pending operator. -/
def stateLine (st : State) : String := s!"mon state {st.describe}"

/-- The column header a driver can show above the rows.  Here rather than in the
driver so the widths cannot disagree with `entryRow`. -/
def header : String :=
  s!" {pad "dir" 5}{pad "key" 10}{pad "did" 8}{pad "mode" 14}emitted"

/-- The header, as it travels to a driver. -/
def headerLine : String := s!"mon header {header}"

end Monitor
end CapslockMode
