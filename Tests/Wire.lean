/-
# The dispatcher's wire, checked

`posts_of_emits` already says the vi channel is unchanged -- that an effect list
of nothing but `emit`s encodes to exactly what `runQuartz` writes.  What a proof
does not say is what the *other* five constructors spell, and that is what a
driver reads, so it is pinned here one constructor at a time.

Two of these guards are about failures rather than successes, and they are the
ones worth keeping: a position macOS cannot name must be said out loud rather
than dropped, and a `text` payload must survive a line that is split on spaces.
-/
import CapslockMode
import Tests.Fixtures.Kanata

namespace CapslockMode.Tests.Wire

open CapslockMode CapslockMode.Dispatch CapslockMode.Dispatch.Wire

/-- A run with no layer names, which is every arm but `setBase`. -/
private def go (f : Quartz.Flags) (es : List Effect) : Quartz.Flags × Out := many [] f es

private def posts (es : List Effect) : List String :=
  ((go {} es).2.posts).map Quartz.Event.line

/-! ## Off the wire

`Quartz.decode` answers in key space and this answers in position space; what
they share is the level-to-edge diff, so the modifier arms are the ones to
check. -/

-- A bare mask change is a modifier edge and nothing else.
#guard (edges {} (.flagsChanged { shift := true })).2
     == [(Dir.down, Kanata.Code.modifier .shift .left)]
#guard (edges { shift := true } (.flagsChanged {})).2
     == [(Dir.up, Kanata.Code.modifier .shift .left)]

-- An ordinary key is one position, named as `defsrc` would name it.
#guard (edges {} (.key .down 2 {})).2 == [(Dir.down, Kanata.Code.key (.char 'd'))]

-- A key arriving with a new mask is macOS saying two things at once, and the
-- modifier is the one that happened first.
#guard (edges {} (.key .down 1 { command := true })).2
     == [(Dir.down, Kanata.Code.modifier .super .left), (Dir.down, Kanata.Code.key (.char 's'))]

-- No transition, no edge: a key under a mask that did not move is just the key.
#guard (edges { shift := true } (.key .up 2 { shift := true })).2
     == [(Dir.up, Kanata.Code.key (.char 'd'))]

-- `codeOf?` is strictly more total than `physOf?`, so the modal path reaches
-- positions the vi path drops -- here a volume key, which has a real keycode.
#guard (edges {} (.key .down 72 {})).2 == [(Dir.down, Kanata.Code.extra .volumeUp)]

/-! ## On to the wire -/

-- A position goes out as the keycode `Bridge` gives it.
#guard posts [.emitCode ⟨.down, .key (.char 'd')⟩] == ["key down 2 -"]

-- A modifier folds into the level and posts nothing; the *next* key carries it.
#guard (go {} [.emitCode ⟨.down, .modifier .shift .left⟩]).1 == { shift := true }
#guard posts [.emitCode ⟨.down, .modifier .shift .left⟩] == []
#guard posts [.emitCode ⟨.down, .modifier .shift .left⟩, .emitCode ⟨.down, .key (.char 'a')⟩]
     == ["key down 0 shift"]

-- ... and it comes back off again, so a held modifier cannot strand.
#guard (go { shift := true } [.emitCode ⟨.up, .modifier .shift .left⟩]).1 == ({} : Quartz.Flags)

-- A position macOS has no keycode for is said twice, never swallowed.  The
-- fixture's whole F-row is these, so this arm is live rather than theoretical.
#guard posts [.emitCode ⟨.down, .extra .playPause⟩] == []
#guard (go {} [.emitCode ⟨.down, .extra .playPause⟩]).2.loud.length == 1
#guard (go {} [.emitCode ⟨.down, .extra .playPause⟩]).2.mon.length == 1

-- `unicode` expands to a down/up pair per character, and a character that has a
-- keycode on this layout keeps it rather than falling through to `text`.
#guard posts [.emitText ['a']] == ["key down 0 -", "key up 0 -"]
#guard (go {} [.emitText ['h', 'i']]).2.posts.length == 4
#guard posts [.emitText ['🚆']] == ["text down 128646 -", "text up 128646 -"]

-- A mode change renders to nothing here: the loop prints the *state*, which
-- carries the pending operator and the count that `Mode.name` would drop.
#guard (go {} [.enter .normal]).2 == ({} : Out)
#guard entered? [.emitCode ⟨.down, .capsLock⟩, .enter .normal] == some Mode.normal
#guard entered? [.emitCode ⟨.down, .capsLock⟩] == none

-- A layer switch and a refusal are commentary, not keystrokes.
#guard (many ["base", "nav"] {} [.setBase 1]).2.mon == ["mon base 1 nav"]
#guard (many ["base", "nav"] {} [.setBase 1]).2.posts == []
#guard posts [.refused "tap-hold" .clock] == []
#guard (go {} [.refused "tap-hold" .clock]).2.mon == ["mon refused tap-hold (needs a clock)"]
#guard (go {} [.refused "tap-hold" .clock]).2.loud.length == 1

/-! ## The row

`Monitor.Entry` could not be reused: a position handed back unchanged is an
`emitCode` of itself, whose `Effect.emitted` is `[]`, so every passed-through
key would have rendered as `hold`. -/

private def row (e : Edge) (es : List Effect) : Row :=
  { edge := e, state := {}, effects := es }

-- Handed straight back.
#guard (row { dir := .down, code := .key (.char 'd') } [.emitCode ⟨.down, .key (.char 'd')⟩]).verdict
     == Monitor.Verdict.passed
-- Swallowed, something else in its place.
#guard (row { dir := .down, code := .key (.char 'd') } [.emitCode ⟨.down, .key (.char 'x')⟩]).verdict
     == Monitor.Verdict.rewritten
-- Swallowed, nothing emitted.
#guard (row { dir := .down, code := .capsLock } [.enter .normal]).verdict == Monitor.Verdict.held
#guard (row { dir := .down, code := .capsLock } []).verdict == Monitor.Verdict.held

-- Every line a driver reads carries the prefix it filters on.
#guard (row { dir := .down, code := .key (.char 'd') } []).line.startsWith "mon row "

/-! ## The banner

Against the real config, because the point of leniency is that this file loads
at all -- and the point of the banner is that nothing it refuses is silent. -/

private def fx : Kanata.Sized :=
  (Kanata.parse Kanata.Fixture.kanataKbd).toOption.getD ⟨0, default⟩

private def fxBanner : List String :=
  banner "kanata.kbd" fx.1 (fx.2.layers.map (·.name)) fx.2.blocked

-- The fixture is 72 positions and 14 layers, and it does trip the frontier.
#guard fx.1 == 72
#guard fx.2.layers.length == 14
#guard fx.2.blocked.length == 7

-- Two header lines plus one line per refusal, every one of them a comment --
-- the prefix both wire parsers and the driver drop.
#guard fxBanner.length == 3 + 7
#guard fxBanner.all (·.startsWith "#")

-- The refusal a reader has to be able to find: the form, and the site.
#guard fxBanner.any fun l => (l.splitOn "tap-hold in alias @grv-mode").length > 1

end CapslockMode.Tests.Wire
