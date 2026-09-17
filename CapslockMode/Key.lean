/-
# Keys, chords and events

CapslockMode sits between the keyboard and the rest of the system: it consumes
*physical* key events and produces *synthetic* ones.  This module fixes the
vocabulary used on both sides.

The type discipline here is load bearing.  `Key` deliberately contains **no**
modifier keys, so a `Chord` (modifiers + key) can never name the same physical
key twice.  That is what makes `CapslockMode.Balance` able to prove — rather
than test — that CapslockMode never leaves a modifier stuck down.
-/

namespace CapslockMode

/-- A modifier key. -/
inductive Modifier where
  | shift | ctrl | alt | super
  deriving DecidableEq, Repr, Inhabited

/-- A non-modifier key, named the way keyboard drivers name it.

`char` carries the character the layout produces, i.e. the driver has already
applied Shift and the keymap: pressing `shift`+`d` on a US layout arrives as
`Key.char 'D'`.  That keeps CapslockMode layout agnostic. -/
inductive Key where
  /-- A key that produces a character. -/
  | char (c : Char)
  | esc | tab | enter | backspace | delete | space
  | left | right | up | down | home | «end» | pageUp | pageDown
  /-- Function key `F n`. -/
  | f (n : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A physical key as seen on the wire: an ordinary key, a modifier, or the
Caps Lock key itself. -/
inductive PhysKey where
  | key (k : Key)
  | mod (m : Modifier)
  | capsLock
  deriving DecidableEq, Repr, Inhabited

/-- Which modifiers are held. -/
structure Mods where
  ctrl : Bool := false
  alt : Bool := false
  shift : Bool := false
  super : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace Mods

/-- The modifier keys that are held, in press order.  The list is duplicate
free by construction, which the balance proofs rely on. -/
def held (m : Mods) : List Modifier :=
  (if m.ctrl then [Modifier.ctrl] else []) ++
  (if m.alt then [Modifier.alt] else []) ++
  (if m.shift then [Modifier.shift] else []) ++
  (if m.super then [Modifier.super] else [])

/-- How many modifiers are held. -/
def count (m : Mods) : Nat := m.held.length

/-- Set or clear one modifier. -/
def set (m : Mods) (k : Modifier) (b : Bool) : Mods :=
  match k with
  | .shift => { m with shift := b }
  | .ctrl => { m with ctrl := b }
  | .alt => { m with alt := b }
  | .super => { m with super := b }

end Mods

/-- A chord: a key pressed while some modifiers are held, e.g. `Ctrl+Shift+Right`. -/
structure Chord where
  mods : Mods := {}
  key : Key
  deriving DecidableEq, Repr, Inhabited

namespace Chord

/-- A bare key press with no modifiers. -/
def plain (k : Key) : Chord := { key := k }

/-- A key press with `Shift` held when `b` is true. -/
def shifted (b : Bool) (k : Key) : Chord := { mods := { shift := b }, key := k }

/-- A key press with `Ctrl` held, and `Shift` when `b` is true. -/
def ctrled (b : Bool) (k : Key) : Chord := { mods := { ctrl := true, shift := b }, key := k }

end Chord

/-- Direction of a key event. -/
inductive Dir where
  | down | up
  deriving DecidableEq, Repr, Inhabited

/-- An event arriving from the keyboard driver.  `mods` is the driver's view of
the modifier state at the time of the event; CapslockMode uses it to recognise
chords such as `Ctrl+R` but never trusts it for output. -/
structure InputEvent where
  dir : Dir
  key : PhysKey
  mods : Mods := {}
  /-- Set when this event is one CapslockMode itself injected.  Some platforms
  (macOS event taps, Windows low-level hooks) show a filter its own synthetic
  events, and re-interpreting them would feed the machine its own output. -/
  injected : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- An event CapslockMode hands back to the system. -/
structure OutputEvent where
  dir : Dir
  key : PhysKey
  deriving DecidableEq, Repr, Inhabited

namespace OutputEvent

def down (k : PhysKey) : OutputEvent := ⟨.down, k⟩
def up (k : PhysKey) : OutputEvent := ⟨.up, k⟩

end OutputEvent

/-- Press and release a single physical key. -/
def tap (k : PhysKey) : List OutputEvent := [.down k, .up k]

/-- Hold `k` down around `l`, then release it. -/
def wrap (k : PhysKey) (l : List OutputEvent) : List OutputEvent :=
  OutputEvent.down k :: (l ++ [OutputEvent.up k])

/-- The event sequence that plays a chord: press the modifiers outside in, tap
the key, release the modifiers inside out.

Defining it as a fold of `wrap` is what makes the well-nestedness proof in
`CapslockMode.Balance` a short induction instead of a case analysis. -/
def Chord.emit (c : Chord) : List OutputEvent :=
  c.mods.held.foldr (fun m l => wrap (.mod m) l) (tap (.key c.key))

/-- Play a sequence of chords. -/
def emitChords (cs : List Chord) : List OutputEvent := cs.flatMap Chord.emit

/-- The event a passed-through input event turns into. -/
def InputEvent.passthrough (ev : InputEvent) : OutputEvent := ⟨ev.dir, ev.key⟩

end CapslockMode
