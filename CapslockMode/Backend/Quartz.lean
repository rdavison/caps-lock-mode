/-
# The macOS backend: Quartz event taps

macOS does not describe a keystroke the way Linux does.  A `CGEvent` carries a
virtual keycode *and a flags bitmask*; modifiers are not separate press and
release events at all.  On input they arrive as `kCGEventFlagsChanged` carrying
a whole new mask, which a client has to diff against the previous one to learn
what actually changed.

So this module is two pure functions:

* `encode` folds CapslockMode's press/release stream into flags, giving exactly
  two Quartz events per chord where evdev needs up to ten;
* `decode` diffs incoming masks back into the press/release events the machine
  expects, leaving `CapslockMode.step` completely unaware of the platform.

The comparison is the interesting part.  `Balanced` is a real obligation on
evdev, where the kernel tracks per-key state and silently drops a release for a
key it thinks is up.  Here it is *vacuous* for modifiers — there are no
modifier transitions to get wrong — and what it buys instead is `flags_settle`:
because the stream is balanced, the accumulated flag state ends where it began,
so no chord can leave Command stuck on for the next one.
-/
import CapslockMode.Balance
import CapslockMode.Machine

namespace CapslockMode.Quartz

/-- A Carbon virtual keycode, as in `<Carbon/HIToolbox/Events.h>`. -/
abbrev KeyCode := UInt16

/-- The part of `CGEventFlags` CapslockMode uses. -/
structure Flags where
  shift : Bool := false
  control : Bool := false
  option : Bool := false
  command : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace Flags

/-- Set or clear one modifier. -/
def set (f : Flags) : Modifier → Bool → Flags
  | .shift, b => { f with shift := b }
  | .ctrl, b => { f with control := b }
  | .alt, b => { f with option := b }
  | .super, b => { f with command := b }

def get (f : Flags) : Modifier → Bool
  | .shift => f.shift
  | .ctrl => f.control
  | .alt => f.option
  | .super => f.command

/-- `CGEventFlags` as macOS spells it: `maskShift` and friends. -/
def toMask (f : Flags) : UInt32 :=
  (if f.shift then 0x00020000 else 0) |||
  (if f.control then 0x00040000 else 0) |||
  (if f.option then 0x00080000 else 0) |||
  (if f.command then 0x00100000 else 0)

end Flags

/-- `true` for a press. -/
def _root_.CapslockMode.Dir.isDown : Dir → Bool
  | .down => true
  | .up => false

/-- The flags a chord's modifiers ask for. -/
def flagsOf (m : Mods) : Flags :=
  { shift := m.shift, control := m.ctrl, option := m.alt, command := m.super }

/-- ... and back. -/
def modsOf (f : Flags) : Mods :=
  { shift := f.shift, ctrl := f.control, alt := f.option, super := f.command }

/-- What a tap sees, and what a client posts.

`text` is the escape hatch: a character with no virtual keycode on this layout
is injected with `CGEventKeyboardSetUnicodeString` instead.  It cannot carry
shortcut semantics, which is exactly why chords keep to `key`. -/
inductive Event where
  | key (dir : Dir) (code : KeyCode) (flags : Flags)
  | text (dir : Dir) (ch : Char) (flags : Flags)
  | flagsChanged (flags : Flags)
  deriving DecidableEq, Repr, Inhabited

/-! ## The keycode table

Cross-checked against `<Carbon/HIToolbox/Events.h>`; the ANSI block is a
US-layout table, which is all a virtual keycode can be. -/

/-- The virtual keycode for a key, when it has one. -/
def keyCode? : Key → Option KeyCode
  | .char c =>
    match c.toLower with
    | 'a' => some 0   | 's' => some 1   | 'd' => some 2   | 'f' => some 3
    | 'h' => some 4   | 'g' => some 5   | 'z' => some 6   | 'x' => some 7
    | 'c' => some 8   | 'v' => some 9   | 'b' => some 11  | 'q' => some 12
    | 'w' => some 13  | 'e' => some 14  | 'r' => some 15  | 'y' => some 16
    | 't' => some 17  | '1' => some 18  | '2' => some 19  | '3' => some 20
    | '4' => some 21  | '6' => some 22  | '5' => some 23  | '=' => some 24
    | '9' => some 25  | '7' => some 26  | '-' => some 27  | '8' => some 28
    | '0' => some 29  | ']' => some 30  | 'o' => some 31  | 'u' => some 32
    | '[' => some 33  | 'i' => some 34  | 'p' => some 35  | 'l' => some 37
    | 'j' => some 38  | '\'' => some 39 | 'k' => some 40  | ';' => some 41
    | '\\' => some 42 | ',' => some 43  | '/' => some 44  | 'n' => some 45
    | 'm' => some 46  | '.' => some 47  | '`' => some 50
    | _ => none
  | .enter => some 36
  | .tab => some 48
  | .space => some 49
  | .backspace => some 51
  | .esc => some 53
  | .delete => some 117
  | .home => some 115
  | .«end» => some 119
  | .pageUp => some 116
  | .pageDown => some 121
  | .left => some 123
  | .right => some 124
  | .down => some 125
  | .up => some 126
  | .f 1 => some 122 | .f 2 => some 120 | .f 3 => some 99  | .f 4 => some 118
  | .f 5 => some 96  | .f 6 => some 97  | .f 7 => some 98  | .f 8 => some 100
  | .f 9 => some 101 | .f 10 => some 109 | .f 11 => some 103 | .f 12 => some 111
  | .f 17 => some 64 | .f 18 => some 79 | .f 19 => some 80
  | .f _ => none

/-- The reverse direction, for events arriving from a tap. -/
def keyOf? (c : KeyCode) : Option Key :=
  if c == 36 then some .enter
  else if c == 48 then some .tab
  else if c == 49 then some .space
  else if c == 51 then some .backspace
  else if c == 53 then some .esc
  else if c == 117 then some .delete
  else if c == 115 then some .home
  else if c == 119 then some .«end»
  else if c == 116 then some .pageUp
  else if c == 121 then some .pageDown
  else if c == 123 then some .left
  else if c == 124 then some .right
  else if c == 125 then some .down
  else if c == 126 then some .up
  else if c == 122 then some (.f 1) else if c == 120 then some (.f 2)
  else if c == 99 then some (.f 3) else if c == 118 then some (.f 4)
  else if c == 96 then some (.f 5) else if c == 97 then some (.f 6)
  else if c == 98 then some (.f 7) else if c == 100 then some (.f 8)
  else if c == 101 then some (.f 9) else if c == 109 then some (.f 10)
  else if c == 103 then some (.f 11) else if c == 111 then some (.f 12)
  else if c == 64 then some (.f 17) else if c == 79 then some (.f 18)
  else if c == 80 then some (.f 19)
  else
    let letters : List (KeyCode × Char) :=
      [(0,'a'),(1,'s'),(2,'d'),(3,'f'),(4,'h'),(5,'g'),(6,'z'),(7,'x'),(8,'c'),(9,'v'),
       (11,'b'),(12,'q'),(13,'w'),(14,'e'),(15,'r'),(16,'y'),(17,'t'),(18,'1'),(19,'2'),
       (20,'3'),(21,'4'),(22,'6'),(23,'5'),(24,'='),(25,'9'),(26,'7'),(27,'-'),(28,'8'),
       (29,'0'),(30,']'),(31,'o'),(32,'u'),(33,'['),(34,'i'),(35,'p'),(37,'l'),(38,'j'),
       (39,'\''),(40,'k'),(41,';'),(42,'\\'),(43,','),(44,'/'),(45,'n'),(46,'m'),(47,'.'),
       (50,'`')]
    (letters.find? (fun p => p.1 == c)).map (fun p => .char p.2)

/-! ## Shift, and the US layout

A virtual keycode names a *physical* key, so `$` is "the 4 key with Shift".
CapslockMode's `Key.char` carries the character the layout produced, so the
encoder has to put the shift back and the decoder has to take it out again. -/

/-- The US-layout shifted forms of the number and punctuation rows. -/
def usShifted : List (Char × Char) :=
  [('1','!'), ('2','@'), ('3','#'), ('4','$'), ('5','%'), ('6','^'), ('7','&'),
   ('8','*'), ('9','('), ('0',')'), ('-','_'), ('=','+'), ('[','{'), (']','}'),
   ('\\','|'), (';',':'), ('\'','"'), (',','<'), ('.','>'), ('/','?'), ('`','~')]

/-- The character this key produces with Shift held. -/
def shiftChar (c : Char) : Char :=
  if c.isAlpha then c.toUpper
  else ((usShifted.find? (fun p => p.1 == c)).map (fun p => p.2)).getD c

/-- The unshifted character, when `c` needs Shift to type. -/
def unshiftChar? (c : Char) : Option Char :=
  if c.isAlpha && c.isUpper then some c.toLower
  else (usShifted.find? (fun p => p.2 == c)).map (fun p => p.1)

/-- The keycode for a character, and whether Shift is needed to produce it. -/
def charTarget? (c : Char) : Option (KeyCode × Bool) :=
  match unshiftChar? c with
  | some base => (keyCode? (.char base)).map (fun code => (code, true))
  | none => (keyCode? (.char c)).map (fun code => (code, false))

/-! ## Encoding: our events out to macOS -/

/-- One key event, carrying the flags accumulated so far.  A character that
needs Shift on this layout gets the shift bit added; a character with no
keycode at all is typed as text instead, which is what
`CGEventKeyboardSetUnicodeString` is for. -/
def keyEvent (dir : Dir) (k : Key) (f : Flags) : Event :=
  match k with
  | .char ch =>
    match charTarget? ch with
    | some (code, needsShift) => .key dir code { f with shift := f.shift || needsShift }
    | none => .text dir ch f
  | _ =>
    match keyCode? k with
    | some c => .key dir c f
    | none => .text dir ' ' f      -- unreachable: every named key has a keycode

/-- Does this key have a virtual keycode that names it back again, with no
Shift in the way? -/
def encodable (k : Key) : Bool :=
  match k with
  | .char ch =>
    match charTarget? ch with
    | some (code, false) => decide (keyOf? code = some k)
    | _ => false
  | _ =>
    match keyCode? k with
    | some code => decide (keyOf? code = some k)
    | none => false

/-- A key CapslockMode can name to macOS without falling back to typing text. -/
def Encodable (k : Key) : Prop := encodable k = true

instance : DecidablePred Encodable := fun k => inferInstanceAs (Decidable (_ = true))

/-- An encodable key is emitted as exactly one `key` event carrying that
keycode and the ambient flags, and reads back as itself. -/
theorem exists_code (k : Key) (h : Encodable k) :
    ∃ code, keyOf? code = some k ∧ ∀ dir f, keyEvent dir k f = .key dir code f := by
  unfold Encodable encodable at h
  match k with
  | .char ch =>
    dsimp only at h
    cases hc : charTarget? ch with
    | none => rw [hc] at h; exact absurd h (by simp)
    | some p =>
      obtain ⟨code, needsShift⟩ := p
      cases needsShift with
      | true => rw [hc] at h; exact absurd h (by simp)
      | false =>
        rw [hc] at h
        exact ⟨code, of_decide_eq_true h, by intro dir f; simp [keyEvent, hc]⟩
  | .esc | .tab | .enter | .backspace | .delete | .space | .left | .right | .up | .down
  | .home | .«end» | .pageUp | .pageDown | .f _ =>
    all_goals
      first
      | (dsimp only at h
         cases hc : keyCode? _ with
         | none => rw [hc] at h; exact absurd h (by simp)
         | some code =>
           rw [hc] at h
           exact ⟨code, of_decide_eq_true h, by intro dir f; simp [keyEvent, hc]⟩)

/-- Fold a stream into Quartz events, threading the flag state. -/
def encodeFrom (f : Flags) : List OutputEvent → List Event
  | [] => []
  | e :: rest =>
    match e.key with
    | .mod m => encodeFrom (f.set m e.dir.isDown) rest
    | .key k => keyEvent e.dir k f :: encodeFrom f rest
    | .capsLock => encodeFrom f rest

/-- The flag state a stream leaves behind. -/
def flagsAfter (f : Flags) : List OutputEvent → Flags
  | [] => f
  | e :: rest =>
    match e.key with
    | .mod m => flagsAfter (f.set m e.dir.isDown) rest
    | _ => flagsAfter f rest

def encode (l : List OutputEvent) : List Event := encodeFrom {} l

/-- The chords a Quartz stream plays, which is how a reader recovers what
CapslockMode meant. -/
def chordsOf : List Event → List Chord
  | [] => []
  | .key .down c f :: rest =>
    match keyOf? c with
    | some k => { mods := modsOf f, key := k } :: chordsOf rest
    | none => chordsOf rest
  | .text .down ch f :: rest => { mods := modsOf f, key := .char ch } :: chordsOf rest
  | _ :: rest => chordsOf rest

/-! ## Decoding: macOS events in -/

/-- `kVK_CapsLock`.  macOS normally reports Caps Lock as a `flagsChanged`
carrying `maskAlphaShift`, which is why the supported setup remaps it to F18;
a driver that does deliver it as a key event still works. -/
def capsLockCode : KeyCode := 57

/-- The physical key a keycode names, including Caps Lock itself. -/
def physOf? (c : KeyCode) : Option PhysKey :=
  if c == capsLockCode then some .capsLock else (keyOf? c).map PhysKey.key

/-- The tap reports the physical key; the machine wants the character the
layout produces, so Shift is applied on the way in. -/
def applyShift (k : Key) (shift : Bool) : Key :=
  match k, shift with
  | .char ch, true => .char (shiftChar ch)
  | _, _ => k

/-- The modifier transitions between two masks, as the machine's own events. -/
def diff (old new : Flags) : List InputEvent :=
  [Modifier.ctrl, Modifier.alt, Modifier.shift, Modifier.super].filterMap fun m =>
    if old.get m == new.get m then none
    else some { dir := if new.get m then .down else .up, key := .mod m, mods := modsOf new }

/-- One incoming tap event becomes the new flag state plus the events the
machine should see.  Modifier *transitions* are recovered by diffing, which is
the level-to-edge conversion macOS forces on every client. -/
def decode (f : Flags) (injected : Bool) : Event → Flags × List InputEvent
  | .flagsChanged f' => (f', diff f f')
  | .key dir c f' =>
    let pre := diff f f'
    match physOf? c with
    | some (.key k) =>
      (f', pre ++ [{ dir := dir, key := .key (applyShift k f'.shift), mods := modsOf f'
                     injected := injected }])
    | some pk => (f', pre ++ [{ dir := dir, key := pk, mods := modsOf f', injected := injected }])
    | none => (f', pre)
  | .text dir ch f' =>
    (f', diff f f' ++
      [{ dir := dir, key := .key (.char ch), mods := modsOf f', injected := injected }])

/-! ## Theorems -/

@[simp] theorem encodeFrom_nil (f : Flags) : encodeFrom f [] = [] := rfl

theorem encodeFrom_append (f : Flags) (l₁ l₂ : List OutputEvent) :
    encodeFrom f (l₁ ++ l₂) = encodeFrom f l₁ ++ encodeFrom (flagsAfter f l₁) l₂ := by
  induction l₁ generalizing f with
  | nil => rfl
  | cons e l ih =>
    cases hk : e.key <;> simp [encodeFrom, flagsAfter, hk, ih]

theorem flagsAfter_append (f : Flags) (l₁ l₂ : List OutputEvent) :
    flagsAfter f (l₁ ++ l₂) = flagsAfter (flagsAfter f l₁) l₂ := by
  induction l₁ generalizing f with
  | nil => rfl
  | cons e l ih => cases hk : e.key <;> simp [flagsAfter, hk, ih]

/-- **A chord is two events on macOS**, against up to ten on evdev: the
modifiers ride along as flags instead of being pressed and released. -/
theorem encode_chord (c : Chord) :
    encodeFrom {} c.emit =
      [keyEvent .down c.key (flagsOf c.mods), keyEvent .up c.key (flagsOf c.mods)] := by
  obtain ⟨⟨ctrl, alt, shift, super⟩, k⟩ := c
  cases ctrl <;> cases alt <;> cases shift <;> cases super <;>
    simp [Chord.emit, Mods.held, wrap, tap, encodeFrom, flagsOf, Flags.set, Dir.isDown,
      OutputEvent.down, OutputEvent.up]

/-- A chord releases every modifier it pressed, so it hands the encoder back
the empty flag state it started from. -/
theorem flagsAfter_chord (c : Chord) : flagsAfter {} c.emit = {} := by
  obtain ⟨⟨ctrl, alt, shift, super⟩, _⟩ := c
  cases ctrl <;> cases alt <;> cases shift <;> cases super <;>
    simp [Chord.emit, Mods.held, wrap, tap, flagsAfter, Flags.set, Dir.isDown,
      OutputEvent.down, OutputEvent.up]

/-- Encoding a chord sequence, chord by chord.  The ambient flag state returns
to empty after each one, which is what keeps the induction simple. -/
theorem encode_cons (c : Chord) (cs : List Chord) :
    encode (emitChords (c :: cs)) =
      [keyEvent .down c.key (flagsOf c.mods), keyEvent .up c.key (flagsOf c.mods)] ++
        encode (emitChords cs) := by
  rw [encode, emitChords, List.flatMap_cons, encodeFrom_append, encode_chord, flagsAfter_chord]
  rfl

/-- ... and therefore the length of a Quartz stream is exactly twice the number
of chords, whatever the modifiers. -/
theorem encode_length (cs : List Chord) : (encode (emitChords cs)).length = 2 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [encode_cons, List.length_append, ih]; simp; omega

/-- **The flags settle.**  On evdev, `Balanced` is what stops a modifier being
left held; here it is what stops the *flag state* drifting, so one chord can
never leave Command set for the next one. -/
theorem flags_settle (cs : List Chord) : flagsAfter {} (emitChords cs) = {} := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [emitChords, List.flatMap_cons, flagsAfter_append, flagsAfter_chord]
    simpa [emitChords] using ih

/-- **Nothing is lost in translation.**  A reader of the Quartz stream recovers
exactly the chords CapslockMode meant to play. -/
theorem chordsOf_encode (cs : List Chord) (h : ∀ c ∈ cs, Encodable c.key) :
    chordsOf (encode (emitChords cs)) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨code, hback, hev⟩ := exists_code c.key (h c (by simp))
    rw [encode_cons, hev, hev]
    simp [chordsOf, hback, modsOf, flagsOf, ih (fun c' hc' => h c' (by simp [hc']))]

/-- Diffing a mask against itself reports nothing. -/
@[simp] theorem diff_self (f : Flags) : diff f f = [] := by
  simp [diff, Flags.get]

/-- A decoded key event is the key that was pressed, with the flags as its
modifiers: the round trip through `decode` recovers the chord too. -/
theorem decode_key (f : Flags) (dir : Dir) (k : Key) (inj : Bool) (code : KeyCode)
    (hcaps : (code == capsLockCode) = false) (hcode : keyOf? code = some k) :
    (decode f inj (.key dir code f)).2 =
      [{ dir := dir, key := .key (applyShift k f.shift), mods := modsOf f, injected := inj }] := by
  simp [decode, physOf?, hcaps, hcode]

end CapslockMode.Quartz
