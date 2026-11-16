/-
# Monitor tests

`CapslockMode.Monitor` is what a driver shows a human, so the thing worth
pinning down is that the three verdicts are told apart.  A monitor that reports
`pass` for a swallowed key is worse than no monitor at all: it would say the
layer is transparent at exactly the moment it is eating your keystrokes.

Every `#guard` below is checked when this file is compiled, so `lake build`
runs them.
-/
import CapslockMode

namespace CapslockMode.Tests.Monitor
open CapslockMode CapslockMode.Monitor

private def N : Config := { startMode := .normal }

/-- Step one event from a state and describe what happened. -/
private def entryOf (cfg : Config) (st : State) (ev : InputEvent) : Entry :=
  let (st', out) := step cfg st ev
  { input := ev, state := st', out := out }

private def down (k : PhysKey) (m : Mods := {}) : InputEvent := { dir := .down, key := k, mods := m }
private def up (k : PhysKey) (m : Mods := {}) : InputEvent := { dir := .up, key := k, mods := m }

private def ch (c : Char) : PhysKey := .key (.char c)

/-! ## Verdicts

The three cases the whole module exists to distinguish. -/

-- Insert mode is transparent, so an ordinary key is handed straight back.
#guard (entryOf {} {} (down (ch 'd'))).verdict == .passed

-- In normal mode `d` is an operator: swallowed, with nothing emitted yet.
#guard (entryOf N N.start (down (ch 'd'))).verdict == .held

-- Caps Lock is swallowed too -- it changes mode and types nothing.
#guard (entryOf N N.start (down .capsLock)).verdict == .held

-- A motion emits keystrokes that are not the key that was pressed.
#guard (entryOf N N.start (down (ch 'w'))).verdict == .rewritten

#guard Verdict.name .passed == "pass"
#guard Verdict.name .rewritten == "rewrite"
#guard Verdict.name .held == "hold"

/-! ## Naming the key that arrived -/

#guard inputName (down (ch 'd')) == "d"
#guard inputName (down .capsLock) == "caps"
#guard inputName (down (.mod .ctrl)) == "ctrl"
#guard inputName (down (.key .left)) == "left"

-- Modifiers reported by the driver are folded into the name, so `Ctrl+S` reads
-- as one thing.  This is why a monitor cannot just print the physical key.
#guard inputName (down (ch 's') { ctrl := true }) == "ctrl+s"
#guard inputName (down (.key .right) { ctrl := true, shift := true }) == "ctrl+shift+right"

/-! ## Rows

`trace` prints `row`, so these also pin down the trace table's shape. -/

#guard row "w" N.start [] == "w       normal        "

-- The emitted column is chord names, not raw press/release pairs.
#guard (entryOf N N.start (down (ch 'w'))).out.length == 4
#guard renderEvents (entryOf N N.start (down (ch 'w'))).out == "ctrl+right"

/-! ## Wire

A driver separates these from injectable events by prefix alone, so the
prefixes must be exactly what the drivers look for. -/

#guard (line (entryOf N N.start (down (ch 'w')))).startsWith "mon row "
#guard (stateLine N.start).startsWith "mon state "
#guard headerLine.startsWith "mon header "

#guard stateLine N.start == "mon state normal"

/-! ## The keycode column

The name alone can mislead when another remapper sits upstream, so the code the
wire carried is shown beside it. -/

#guard codeOf (.key .down 2 {}) == "2"
#guard codeOf (.flagsChanged {}) == ""
#guard codeOf (.text .down 'x' {}) == ""

-- An entry with no code reads as `-` rather than a blank the eye slides over.
#guard (entryRow { input := down (ch 'd'), state := N.start, out := [] }).startsWith " down -    d"
#guard (entryRow { input := down (ch 'd'), state := N.start, out := [], code := "2" }).startsWith " down 2    d"

-- The header must line up with the row it labels; both are built from `pad`
-- here so a driver cannot disagree about the widths.
#guard header.startsWith " dir  code key"

/-! ## Drops

A wire line that yields no events is the failure that hid the missing F13
entry: the key was pressed, nothing appeared, and nothing said why. -/

#guard dropLine "down 999 -" == "mon drop down 999 -"

/-! ## Devices

Another remapper may sit below us and re-emit through its own driver, so the
device an event claims matters. The policy is "say it once, then only on a
change" -- a line per keystroke would bury the log it exists to explain. -/

#guard parseDevice? "dev 45 0" == some { kbType := 45, pid := 0 }
#guard parseDevice? "dev 99 518" == some { kbType := 99, pid := 518 }
#guard parseDevice? "dev x y" == none
#guard parseDevice? "dev 45" == none
#guard parseDevice? "down 2 -" == none

-- Hardware and kernel drivers post with pid 0, which is what a virtual HID
-- device shows; anything else names the process.
#guard Device.describe { kbType := 45, pid := 0 } == "keyboard type 45, posted by a device or driver"
#guard Device.describe { kbType := 99, pid := 518 } == "keyboard type 99, posted by pid 518"

#guard deviceChange? none { kbType := 45, pid := 0 } |>.isSome
#guard deviceChange? (some { kbType := 45, pid := 0 }) { kbType := 45, pid := 0 } == none
#guard deviceChange? (some { kbType := 45, pid := 0 }) { kbType := 99, pid := 0 } |>.isSome
#guard deviceChange? (some { kbType := 45, pid := 0 }) { kbType := 45, pid := 518 } |>.isSome
#guard deviceChange? none { kbType := 45, pid := 0 } == some "mon device keyboard type 45, posted by a device or driver"
#guard stateLine (entryOf N N.start (down (ch 'd'))).state == "mon state normal d"

-- An injected event is marked, because a monitor that cannot show the machine
-- ignoring its own output makes `no_feedback` impossible to observe.
#guard (line { input := { dir := .down, key := ch 'd', injected := true },
               state := N.start, out := [] }).startsWith "mon row *"
#guard (line (entryOf N N.start (down (ch 'd')))).startsWith "mon row  "

end CapslockMode.Tests.Monitor
