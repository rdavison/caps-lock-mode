/-
# The HID backend: usage reports

The third backend, and the one that forces a model the other two hide.

evdev and Quartz are both *edge* based: something happened, and the event says
what.  A HID keyboard is *level* based.  It does not report events at all -- it
reports a **snapshot** of everything currently held, and a reader recovers the
events by diffing consecutive snapshots.  Nothing in the report says which key
just moved; that is entirely the reader's inference.

So this module is the same two pure functions as `Backend.Quartz`, aimed at a
different shape:

* `encodeFrom` folds CapslockMode's press/release stream into successive
  reports -- exactly one report per transition, because every transition changes
  the snapshot;
* `decode` diffs two consecutive reports back into the press and release events
  the machine expects.

What the comparison buys: on Quartz, `Balanced` gives `flags_settle`, because
the risk is a modifier flag drifting.  Here the same obligation gives
`reports_settle` *and* `keys_nodup` -- a level-based protocol cannot express "the
same key pressed twice", so duplicate-freedom is not a nicety but a
well-formedness condition on the wire itself.  A stream that violated it would
describe a report no keyboard can produce.

The usages are the HID keyboard page (`0x07`).  Note this is deliberately *not*
the 8-byte boot protocol: the virtual device this targets carries a wider key
array, so there is no six-key rollover bound to prove.  A boot-protocol backend
would need one, and would be a different module.
-/
import CapslockMode.Balance
import CapslockMode.Machine

namespace CapslockMode.Hid

/-- A HID usage on the keyboard/keypad page (`0x07`). -/
abbrev Usage := UInt16

/-- What a keyboard reports: everything held, right now.

There is no direction and no "which key changed" -- that is the whole point of a
level-based protocol, and the reason `decode` needs the *previous* report to say
anything at all. -/
structure Report where
  mods : Mods := {}
  /-- Held usages, in press order.  Duplicate-free: see `press_nodup`. -/
  keys : List Usage := []
  deriving DecidableEq, Repr, Inhabited

/-! ## Usages -/

/-- The HID usage for a key, on the keyboard page. -/
def usageOf? : Key → Option Usage
  | .char c =>
    match c with
    | 'a' => some 0x04 | 'b' => some 0x05 | 'c' => some 0x06 | 'd' => some 0x07
    | 'e' => some 0x08 | 'f' => some 0x09 | 'g' => some 0x0A | 'h' => some 0x0B
    | 'i' => some 0x0C | 'j' => some 0x0D | 'k' => some 0x0E | 'l' => some 0x0F
    | 'm' => some 0x10 | 'n' => some 0x11 | 'o' => some 0x12 | 'p' => some 0x13
    | 'q' => some 0x14 | 'r' => some 0x15 | 's' => some 0x16 | 't' => some 0x17
    | 'u' => some 0x18 | 'v' => some 0x19 | 'w' => some 0x1A | 'x' => some 0x1B
    | 'y' => some 0x1C | 'z' => some 0x1D
    | '1' => some 0x1E | '2' => some 0x1F | '3' => some 0x20 | '4' => some 0x21
    | '5' => some 0x22 | '6' => some 0x23 | '7' => some 0x24 | '8' => some 0x25
    | '9' => some 0x26 | '0' => some 0x27
    | '-' => some 0x2D | '=' => some 0x2E | '[' => some 0x2F | ']' => some 0x30
    | '\\' => some 0x31 | ';' => some 0x33 | '\'' => some 0x34 | '`' => some 0x35
    | ',' => some 0x36 | '.' => some 0x37 | '/' => some 0x38
    | ' ' => some 0x2C
    | _ => none
  | .enter => some 0x28
  | .esc => some 0x29
  | .backspace => some 0x2A
  | .tab => some 0x2B
  | .space => some 0x2C
  | .delete => some 0x4C
  | .home => some 0x4A
  | .«end» => some 0x4D
  | .pageUp => some 0x4B
  | .pageDown => some 0x4E
  | .right => some 0x4F
  | .left => some 0x50
  | .down => some 0x51
  | .up => some 0x52
  | .f n =>
    if 1 ≤ n && n ≤ 12 then some (UInt16.ofNat (0x3A + (n - 1)))
    else if 13 ≤ n && n ≤ 24 then some (UInt16.ofNat (0x68 + (n - 13)))
    else none

/-- Caps Lock's own usage.  Unlike the Quartz backend, a HID reader sees this as
an ordinary key: the lock state and the LED live above a seized device, not
below it, so it can simply be swallowed. -/
def capsLockUsage : Usage := 0x39

/-- The physical key a usage names, Caps Lock included. -/
def physOf? (u : Usage) : Option PhysKey :=
  if u == capsLockUsage then some .capsLock
  else
    let keys : List Key :=
      [.enter, .esc, .backspace, .tab, .space, .delete, .home, .«end», .pageUp,
       .pageDown, .right, .left, .down, .up] ++
      (List.range 24).map (fun n => Key.f (n + 1)) ++
      "abcdefghijklmnopqrstuvwxyz0123456789-=[]\\;'`,./ ".toList.map Key.char
    (keys.find? (fun k => usageOf? k == some u)).map PhysKey.key

/-! ## Encoding: reports out -/

/-- Add a usage to a held set.  Idempotent, because a report *is* a set: a
level-based protocol has no way to say "held twice". -/
def press (u : Usage) (l : List Usage) : List Usage :=
  if l.contains u then l else l ++ [u]

/-- Remove a usage from a held set. -/
def release (u : Usage) (l : List Usage) : List Usage := l.erase u

/-- The snapshot after one transition. -/
def apply (r : Report) (e : OutputEvent) : Report :=
  match e.key with
  | .mod m => { r with mods := r.mods.set m e.dir.isDown }
  | .key k =>
    match usageOf? k with
    | some u => { r with keys := if e.dir.isDown then press u r.keys else release u r.keys }
    | none => r
  | .capsLock =>
    { r with keys := if e.dir.isDown then press capsLockUsage r.keys
                     else release capsLockUsage r.keys }

/-- Fold a stream into successive reports, threading the held state.

One report per transition.  That is the level-based counterpart of Quartz's
"exactly two events per chord": there, modifiers vanish into a mask; here every
press and release is its own snapshot, because a snapshot is all the protocol
can say. -/
def encodeFrom (r : Report) : List OutputEvent → List Report
  | [] => []
  | e :: rest => apply r e :: encodeFrom (apply r e) rest

/-- The report a stream leaves behind. -/
def reportAfter (r : Report) : List OutputEvent → Report
  | [] => r
  | e :: rest => reportAfter (apply r e) rest

def encode (l : List OutputEvent) : List Report := encodeFrom {} l

/-! ## Decoding: reports in -/

/-- The modifier transitions between two reports, as the machine's events. -/
def diffMods (old new : Mods) (injected : Bool) : List InputEvent :=
  [Modifier.ctrl, Modifier.alt, Modifier.shift, Modifier.super].filterMap fun m =>
    let was := match m with
      | .ctrl => old.ctrl | .alt => old.alt | .shift => old.shift | .super => old.super
    let now := match m with
      | .ctrl => new.ctrl | .alt => new.alt | .shift => new.shift | .super => new.super
    if was == now then none
    else some { dir := if now then .down else .up, key := .mod m, mods := new,
                injected := injected }

/-- Two consecutive reports become the events between them.

Releases are reported before presses, so a report that swaps one key for another
reads as "that one went up, this one went down" rather than the reverse. -/
def decode (old new : Report) (injected : Bool) : List InputEvent :=
  let ups := (old.keys.filter (fun u => !new.keys.contains u)).filterMap fun u =>
    (physOf? u).map fun pk => { dir := .up, key := pk, mods := new.mods, injected := injected }
  let downs := (new.keys.filter (fun u => !old.keys.contains u)).filterMap fun u =>
    (physOf? u).map fun pk => { dir := .down, key := pk, mods := new.mods, injected := injected }
  diffMods old.mods new.mods injected ++ ups ++ downs

/-! ## Theorems -/

@[simp] theorem encodeFrom_nil (r : Report) : encodeFrom r [] = [] := rfl

@[simp] theorem reportAfter_nil (r : Report) : reportAfter r [] = r := rfl

/-- **One report per transition.**  Quartz collapses a chord to two events by
hiding modifiers in a mask; a level-based protocol cannot hide anything, so the
report count is exactly the transition count. -/
theorem encodeFrom_length (r : Report) (l : List OutputEvent) :
    (encodeFrom r l).length = l.length := by
  induction l generalizing r with
  | nil => rfl
  | cons e rest ih => simp [encodeFrom, ih]

theorem reportAfter_append (r : Report) (l₁ l₂ : List OutputEvent) :
    reportAfter r (l₁ ++ l₂) = reportAfter (reportAfter r l₁) l₂ := by
  induction l₁ generalizing r with
  | nil => rfl
  | cons e l ih => simp [reportAfter, ih]

theorem encodeFrom_append (r : Report) (l₁ l₂ : List OutputEvent) :
    encodeFrom r (l₁ ++ l₂) = encodeFrom r l₁ ++ encodeFrom (reportAfter r l₁) l₂ := by
  induction l₁ generalizing r with
  | nil => rfl
  | cons e l ih => simp [encodeFrom, reportAfter, ih]

/-- Pressing preserves duplicate-freedom, because it checks first. -/
theorem press_nodup (u : Usage) (l : List Usage) (h : l.Nodup) : (press u l).Nodup := by
  unfold press
  split
  · exact h
  · rename_i hc
    have hu : u ∉ l := by simpa using hc
    simp [List.nodup_append, h]
    intro a ha heq
    subst heq
    exact hu ha

/-- Releasing preserves it too. -/
theorem release_nodup (u : Usage) (l : List Usage) (h : l.Nodup) : (release u l).Nodup :=
  h.erase u

/-- **A report is always a set.**  This is the well-formedness condition a
level-based wire imposes: a snapshot listing the same usage twice describes a
keyboard state that cannot exist. -/
theorem apply_nodup (r : Report) (e : OutputEvent) (h : r.keys.Nodup) :
    (apply r e).keys.Nodup := by
  cases hk : e.key with
  | mod m => simp [apply, hk, h]
  | key k =>
    cases hu : usageOf? k with
    | none => simp [apply, hk, hu, h]
    | some u =>
      by_cases hd : e.dir.isDown <;>
        simp [apply, hk, hu, hd, press_nodup, release_nodup, h]
  | capsLock =>
    by_cases hd : e.dir.isDown <;>
      simp [apply, hk, hd, press_nodup, release_nodup, h]

theorem reportAfter_nodup (r : Report) (l : List OutputEvent) (h : r.keys.Nodup) :
    (reportAfter r l).keys.Nodup := by
  induction l generalizing r with
  | nil => exact h
  | cons e rest ih => exact ih _ (apply_nodup r e h)

/-- A chord releases every modifier and every key it pressed, so it hands the
encoder back the empty report it started from. -/
theorem reportAfter_chord (c : Chord) : reportAfter {} c.emit = {} := by
  obtain ⟨⟨ctrl, alt, shift, super⟩, k⟩ := c
  cases hu : usageOf? k <;>
    cases ctrl <;> cases alt <;> cases shift <;> cases super <;>
      simp [Chord.emit, Mods.held, wrap, tap, reportAfter, apply, Mods.set, Dir.isDown,
        OutputEvent.down, OutputEvent.up, hu, press, release]

/-- **The reports settle.**  The evdev obligation `Balanced` shows up here as:
no chord can leave a key or a modifier held for the next one.  On Quartz the
same property is `flags_settle`; the difference is that here it covers the keys
too, because keys live in the snapshot rather than in an event. -/
theorem reports_settle (cs : List Chord) : reportAfter {} (emitChords cs) = {} := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [emitChords, List.flatMap_cons, reportAfter_append, reportAfter_chord]
    simpa [emitChords] using ih

/-- Diffing a report against itself reports nothing: a repeated snapshot is not
an event.  This is what stops a driver that re-sends state from injecting
phantom keystrokes. -/
@[simp] theorem decode_self (r : Report) (inj : Bool) : decode r r inj = [] := by
  simp [decode, diffMods]

end CapslockMode.Hid
