/-
# Tests for the macOS backend

`CapslockMode/Backend/Quartz.lean` proves the general facts — two events per
chord, the flags settle, nothing is lost in translation.  What it cannot prove
is that the *particular* keys this key map uses are ones macOS can name, since
that is a fact about a table rather than about the encoding.  That is what the
guards below check, over every command `capslockmode keys` documents.
-/
import CapslockMode

namespace CapslockMode.Tests.Quartz
open CapslockMode CapslockMode.Quartz

private def N (p : Platform) : Config := { startMode := .normal, platform := p }

/-- Every chord a script produces on a platform. -/
def chordsFor (p : Platform) (script : String) : List Chord :=
  let evs := parseScript script
  let rec go (st : State) : List InputEvent → List Chord
    | [] => []
    | ev :: rest =>
      match ev.dir, ev.chord? with
      | .down, some c => (command (N p) st c).chords ++ go (step (N p) st ev).1 rest
      | _, _ => go (step (N p) st ev).1 rest
  go (N p).start evs

/-- Every chord the documented key map can play, on both platforms. -/
def allChords : List Chord :=
  (keyTable.flatMap fun (script, _) => chordsFor .mac script) ++
  (keyTable.flatMap fun (script, _) => chordsFor .pc script)

/-! ## The key map is expressible on macOS -/

-- Every key CapslockMode emits has a virtual keycode that reads back as itself,
-- so nothing falls through to unicode injection (which would lose shortcuts).
#guard allChords.all fun c => encodable c.key

-- ... and therefore the chords survive the round trip through Quartz events.
#guard (chordsOf (encode (emitChords allChords))) == allChords

/-! ## Two events per chord, and the flags settle -/

#guard (encode (emitChords allChords)).length == 2 * allChords.length
#guard flagsAfter {} (emitChords allChords) == ({} : Flags)

-- A modifier-heavy chord is still two events, where evdev needs eight.
#guard (encode (Chord.emit { mods := { ctrl := true, shift := true }, key := .right })).length == 2

/-! ## The mac key map is the Mac one -/

private def emittedMac (script : String) : String :=
  " ".intercalate ((encode (run (N .mac) (N .mac).start (parseScript script)).2).map Event.line)

-- `yy` copies with Cmd+C (keycode 8 = kVK_ANSI_C), not Ctrl+C.
#guard ((emittedMac "yy").splitOn "8 command").length == 3
-- `w` is Option+Right (keycode 124), not Ctrl+Right.
#guard emittedMac "w" == "key down 124 alt key up 124 alt"
-- redo is Cmd+Shift+Z (keycode 6), which on a PC is Ctrl+Y.
#guard emittedMac "<C-r>" == "key down 6 shift,command key up 6 shift,command"

/-! ## Shift and the US layout -/

#guard charTarget? '$' == some (21, true)     -- Shift+4
#guard charTarget? '4' == some (21, false)
#guard shiftChar '4' == '$'
#guard unshiftChar? '$' == some '4'
#guard applyShift (.char '4') true == Key.char '$'
#guard applyShift (.char '4') false == Key.char '4'

-- A shifted character is injected as its physical key plus the shift flag.
#guard keyEvent .down (.char '$') {} == Event.key .down 21 { shift := true }

/-! ## Caps Lock and the toggle key -/

#guard physOf? capsLockCode == some PhysKey.capsLock
#guard physOf? 79 == some (PhysKey.key (.f 18))   -- the hidutil remap target

/-! ## Decoding: masks become transitions -/

#guard (decode {} false (.flagsChanged { command := true })).2 ==
  [{ dir := .down, key := .mod .super, mods := { super := true } }]
#guard (decode { command := true } false (.flagsChanged {})).2 ==
  [{ dir := .up, key := .mod .super, mods := {} }]
#guard (decode {} false (.flagsChanged {})).2 == []

-- An event we injected ourselves is marked, and the machine passes it through.
#guard (decode {} true (.key .down 4 {})).2.all (fun ev => ev.injected) == true

/-! ## The wire -/

#guard Quartz.Flags.names { shift := true, command := true } == "shift,command"
#guard Quartz.parseFlags? "shift,command" == some { shift := true, command := true }
#guard Quartz.parseFlags? "-" == some ({} : Flags)
#guard (Quartz.parseLine? "down 4 command").isSome
#guard (Quartz.parseLine? "flags -").isSome
#guard (Quartz.parseLine? "down 4 command injected").map (·.injected) == some true

/-! ## The clock rides as a tag, not as a field

Both wire parsers match exact arities, so a fourth positional field would make
every event unparseable -- `Monitor.lean` settled that once already for the
`dev` line.  A stamp is tagged, like `injected`, and filtered out before the
arity match, which is what lets it sit anywhere and lets a line with no stamp
parse to exactly what it always did. -/

-- The canary for the md5 check, in the one form a `#guard` can state it.
#guard (Quartz.parseLine? "down 4 command").map (·.event)
     == (Quartz.parseLine? "down 4 command @99").map (·.event)
#guard (Quartz.parseLine? "down 4 command").map (·.time) == some 0

-- Every arity carries it.
#guard (Quartz.parseLine? "down 4 command @1234").map (·.time) == some 1234
#guard (Quartz.parseLine? "down 4 @7").map (·.time) == some 7
#guard (Quartz.parseLine? "flags shift @12").map (·.time) == some 12

-- Two tags, so they commute.
#guard (Quartz.parseLine? "down 4 command injected @7").map (fun i => (i.injected, i.time))
     == some (true, 7)
#guard (Quartz.parseLine? "down 4 command @7 injected").map (fun i => (i.injected, i.time))
     == some (true, 7)

-- A word that looks like a stamp and is not drops the line.  A driver whose
-- clock has broken must look broken: read as a silent zero it would turn every
-- tap-hold into a tap and leave nothing to find.
#guard (Quartz.parseLine? "down 4 @x").isNone
#guard (Quartz.parseLine? "down 4 @1 @2").isNone

-- Output is never stamped: the machine does not re-read what it wrote, and an
-- injectable line growing a fourth token is what would break `inject`.
#guard (Event.key .down 123 { shift := true }).line == "key down 123 shift"
#guard (Event.key .down 123 { shift := true }).line == "key down 123 shift"

/-! ## A `text` payload is a scalar, not a character

The driver splits an injectable line on spaces and reads the character out of
field 2.  A raw `' '` would shift the flags into that field and type a `-`; a
raw `'\n'` would end the line early and lose the rest.  `Quartz.keyEvent`'s own
fallback emits exactly `.text dir ' ' f`, so neither is hypothetical. -/

#guard Quartz.charCode 'x' == "120"
#guard Quartz.charCode ' ' == "32"
#guard Quartz.charCode '\n' == "10"
#guard Quartz.charCode '🚆' == "128646"

#guard (Event.text .down 'x' {}).line == "text down 120 -"
#guard (Event.text .down ' ' {}).line == "text down 32 -"

-- The property the driver actually depends on: four whitespace-free fields,
-- whatever the payload.  A character is checked here rather than a line format,
-- because it is the payload that varies.
#guard [' ', '\n', '\t', 'é', '🚆'].all fun c =>
         ((Event.text .down c { shift := true }).line.splitOn " ").length == 4

end CapslockMode.Tests.Quartz
