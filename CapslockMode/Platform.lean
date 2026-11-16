/-
# What a command wants, and what that costs on this platform

`dd` does not mean "Home, Shift+Down, Delete".  It means "select this line and
delete it", and the keystrokes that achieve that are a property of the platform:
`Home` on a PC, `Cmd+Left` on a Mac, where `Home` does nothing useful in most
text fields.  Copy is `Ctrl+C` or `Cmd+C`; redo is `Ctrl+Y` or `Cmd+Shift+Z`;
"next match" is `F3` or `Cmd+G`.

So the key map is written in `Intent`s, and a `Platform` lowers each intent to
a `Chord`.  Everything the proofs say about chords holds whichever platform is
in play, because none of them looks inside a chord.

`Platform` is an enumeration rather than a record of functions so that `Config`
stays decidable and `Repr`-able, and so that proofs can case-split on it.
-/
import CapslockMode.Key

namespace CapslockMode

/-- What a vi command wants the text widget to do, with no opinion about which
keystrokes that takes. -/
inductive Intent where
  -- Motions.  These are the intents for which `extend` matters.
  | charLeft | charRight | lineUp | lineDown
  | wordLeft | wordRight
  | lineStart | lineEnd | docStart | docEnd
  | paraUp | paraDown | pageUp | pageDown
  -- Edits.
  | deleteForward | deleteBack | newline | indent | outdent
  -- Clipboard and history.
  | copy | cut | paste | undo | redo
  -- Search.
  | find | findNext | findPrev
  deriving DecidableEq, Repr, Inhabited

/-- The keyboard conventions CapslockMode knows how to speak. -/
inductive Platform where
  /-- Windows, Linux, and every text widget that follows CUA. -/
  | pc
  /-- macOS, where the editing keys are Command- and Option-based. -/
  | mac
  deriving DecidableEq, Repr, Inhabited

namespace Platform

/-- The keystroke that carries out `i` on this platform.  `extend` asks the
motion to drag a selection along with it; it is ignored by intents that are not
motions, which is why `Operator.apply` can pass anything. -/
def chord : Platform → Bool → Intent → Chord
  | .pc, extend, i =>
    match i with
    | .charLeft => Chord.shifted extend .left
    | .charRight => Chord.shifted extend .right
    | .lineUp => Chord.shifted extend .up
    | .lineDown => Chord.shifted extend .down
    | .wordLeft => Chord.ctrled extend .left
    | .wordRight => Chord.ctrled extend .right
    | .lineStart => Chord.shifted extend .home
    | .lineEnd => Chord.shifted extend .«end»
    | .docStart => Chord.ctrled extend .home
    | .docEnd => Chord.ctrled extend .«end»
    | .paraUp => Chord.ctrled extend .up
    | .paraDown => Chord.ctrled extend .down
    | .pageUp => Chord.shifted extend .pageUp
    | .pageDown => Chord.shifted extend .pageDown
    | .deleteForward => Chord.plain .delete
    | .deleteBack => Chord.plain .backspace
    | .newline => Chord.plain .enter
    | .indent => Chord.plain .tab
    | .outdent => Chord.shifted true .tab
    | .copy => Chord.ctrled false (.char 'c')
    | .cut => Chord.ctrled false (.char 'x')
    | .paste => Chord.ctrled false (.char 'v')
    | .undo => Chord.ctrled false (.char 'z')
    | .redo => Chord.ctrled false (.char 'y')
    | .find => Chord.ctrled false (.char 'f')
    | .findNext => Chord.plain (.f 3)
    | .findPrev => Chord.shifted true (.f 3)
  | .mac, extend, i =>
    -- On macOS the Command key (our `super`) carries the editing verbs, and
    -- word motion is Option-based.  `Home`/`End` are deliberately unused: they
    -- scroll rather than move the caret in most Mac text views.
    let cmd : Bool → Key → Chord := fun ext k =>
      { mods := { super := true, shift := ext }, key := k }
    let opt : Bool → Key → Chord := fun ext k =>
      { mods := { alt := true, shift := ext }, key := k }
    match i with
    | .charLeft => Chord.shifted extend .left
    | .charRight => Chord.shifted extend .right
    | .lineUp => Chord.shifted extend .up
    | .lineDown => Chord.shifted extend .down
    | .wordLeft => opt extend .left
    | .wordRight => opt extend .right
    | .lineStart => cmd extend .left
    | .lineEnd => cmd extend .right
    | .docStart => cmd extend .up
    | .docEnd => cmd extend .down
    | .paraUp => opt extend .up
    | .paraDown => opt extend .down
    | .pageUp => Chord.shifted extend .pageUp
    | .pageDown => Chord.shifted extend .pageDown
    | .deleteForward => Chord.plain .delete
    | .deleteBack => Chord.plain .backspace
    | .newline => Chord.plain .enter
    | .indent => Chord.plain .tab
    | .outdent => Chord.shifted true .tab
    | .copy => cmd false (.char 'c')
    | .cut => cmd false (.char 'x')
    | .paste => cmd false (.char 'v')
    | .undo => cmd false (.char 'z')
    | .redo => cmd true (.char 'z')          -- Cmd+Shift+Z, not a separate key
    | .find => cmd false (.char 'f')
    | .findNext => cmd false (.char 'g')
    | .findPrev => cmd true (.char 'g')

def name : Platform → String
  | .pc => "pc"
  | .mac => "mac"

def ofName? : String → Option Platform
  | "pc" | "linux" | "windows" => some .pc
  | "mac" | "macos" | "darwin" => some .mac
  | _ => none

end Platform

end CapslockMode
