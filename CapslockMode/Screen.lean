/-
# A text field to aim CapslockMode at

CapslockMode emits the keystrokes that a text widget understands.  To show (and
to test) that those keystrokes do what vi users expect, this module models an
ordinary, unremarkable text field: arrows move, Shift extends a selection,
Ctrl+C/X/V/Z do the usual, Home/End go to the ends of a line.

Nothing here is part of the keyboard machine.  It is the *other* side of the
conversation, which is exactly why it is useful as an oracle in tests: if
`dd` really does delete a line, it must do so through keystrokes that a dumb
text field already implements.
-/
import CapslockMode.Machine

namespace CapslockMode

private def sTake (s : String) (n : Nat) : String := (s.take n).toString
private def sDrop (s : String) (n : Nat) : String := (s.drop n).toString

/-- A plain multi-line text field. -/
structure Screen where
  lines : Array String := #[""]
  row : Nat := 0
  col : Nat := 0
  /-- Where the selection started, if there is one. -/
  anchor : Option (Nat × Nat) := none
  clipboard : String := ""
  /-- Modifier state, tracked from the synthetic events themselves. -/
  mods : Mods := {}
  undo : List (Array String × Nat × Nat) := []
  redo : List (Array String × Nat × Nat) := []
  deriving Inhabited

namespace Screen

def lineAt (sc : Screen) (r : Nat) : String := sc.lines[r]?.getD ""
def curLine (sc : Screen) : String := sc.lineAt sc.row
def lastRow (sc : Screen) : Nat := sc.lines.size - 1

/-- Remember the current text so that Ctrl+Z can come back to it. -/
def snapshot (sc : Screen) : Screen :=
  { sc with undo := (sc.lines, sc.row, sc.col) :: sc.undo, redo := [] }

def clamp (sc : Screen) : Screen :=
  let row := min sc.row sc.lastRow
  { sc with row := row, col := min sc.col (sc.lineAt row).length }

/-- Move the cursor, extending or dropping the selection. -/
def moveTo (sc : Screen) (r c : Nat) (extend : Bool) : Screen :=
  let anchor := if extend then (sc.anchor.getD (sc.row, sc.col)) else (0, 0)
  { sc with row := r, col := c, anchor := if extend then some anchor else none }.clamp

/-- The selection, as an ordered pair of positions. -/
def selection (sc : Screen) : Option ((Nat × Nat) × (Nat × Nat)) :=
  match sc.anchor with
  | none => none
  | some a =>
    let b := (sc.row, sc.col)
    if a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2) then some (a, b) else some (b, a)

def selectedText (sc : Screen) : String :=
  match sc.selection with
  | none => ""
  | some ((r₁, c₁), (r₂, c₂)) =>
    if r₁ == r₂ then sTake (sDrop (sc.lineAt r₁) c₁) (c₂ - c₁)
    else
      let first := sDrop (sc.lineAt r₁) c₁
      let mid := (List.range (r₂ - r₁ - 1)).map fun i => sc.lineAt (r₁ + 1 + i)
      let last := sTake (sc.lineAt r₂) c₂
      String.intercalate "\n" (first :: mid ++ [last])

/-- Remove the selected text, leaving the cursor where it started. -/
def deleteSelection (sc : Screen) : Screen :=
  match sc.selection with
  | none => sc
  | some ((r₁, c₁), (r₂, c₂)) =>
    let joined := sTake (sc.lineAt r₁) c₁ ++ sDrop (sc.lineAt r₂) c₂
    let before := sc.lines.toList.take r₁
    let after := sc.lines.toList.drop (r₂ + 1)
    { sc with lines := (before ++ [joined] ++ after).toArray, row := r₁, col := c₁, anchor := none }.clamp

/-- Type a string at the cursor, replacing any selection. -/
def insertText (sc : Screen) (s : String) : Screen :=
  let sc := (sc.snapshot).deleteSelection
  let parts := s.splitOn "\n"
  match parts with
  | [] => sc
  | [one] =>
    let l := sc.curLine
    let l' := sTake l sc.col ++ one ++ sDrop l sc.col
    { sc with lines := sc.lines.set! sc.row l', col := sc.col + one.length }
  | first :: rest =>
    let l := sc.curLine
    let head := sTake l sc.col ++ first
    let tailStr := sDrop l sc.col
    let lastPart := rest.getLast!
    let middle := rest.dropLast
    let newLines := (head :: middle) ++ [lastPart ++ tailStr]
    let before := sc.lines.toList.take sc.row
    let after := sc.lines.toList.drop (sc.row + 1)
    { sc with lines := (before ++ newLines ++ after).toArray
              row := sc.row + rest.length, col := lastPart.length, anchor := none }

/-- Index of the next word boundary to the right. -/
def nextWord (l : String) (c : Nat) : Nat :=
  let cs := l.toList
  let rec skip (i : Nat) (p : Char → Bool) : Nat :=
    if h : i < cs.length then (if p cs[i] then skip (i + 1) p else i) else i
  termination_by cs.length - i
  let i := skip c (fun ch => ch.isAlphanum || ch == '_')
  let j := skip i (fun ch => !(ch.isAlphanum || ch == '_'))
  if j == c then min (c + 1) l.length else j

/-- Index of the previous word boundary to the left. -/
def prevWord (l : String) (c : Nat) : Nat :=
  let cs := l.toList
  let isw := fun (i : Nat) => match cs[i]? with
    | some ch => ch.isAlphanum || ch == '_'
    | none => false
  let rec back (i : Nat) (p : Nat → Bool) : Nat :=
    match i with
    | 0 => 0
    | i + 1 => if p i then back i p else i + 1
  let i := back c (fun i => !isw i)
  let j := back i isw
  if j == c then c - 1 else j

def copy (sc : Screen) : Screen :=
  match sc.selection with
  | none => sc
  | some _ => { sc with clipboard := sc.selectedText }

def cut (sc : Screen) : Screen := (sc.copy.snapshot).deleteSelection

def paste (sc : Screen) : Screen := sc.insertText sc.clipboard

def undoOnce (sc : Screen) : Screen :=
  match sc.undo with
  | [] => sc
  | (ls, r, c) :: rest =>
    { sc with lines := ls, row := r, col := c, anchor := none
              undo := rest, redo := (sc.lines, sc.row, sc.col) :: sc.redo }.clamp

def redoOnce (sc : Screen) : Screen :=
  match sc.redo with
  | [] => sc
  | (ls, r, c) :: rest =>
    { sc with lines := ls, row := r, col := c, anchor := none
              undo := (sc.lines, sc.row, sc.col) :: sc.undo, redo := rest }.clamp

/-- Indent (or, with Shift, outdent) every line the selection touches. -/
def indent (sc : Screen) (out : Bool) : Screen :=
  let (r₁, r₂) := match sc.selection with
    | none => (sc.row, sc.row)
    | some ((a, _), (b, _)) => (a, b)
  let sc := sc.snapshot
  let lines := sc.lines.mapIdx fun i l =>
    if r₁ ≤ i && i ≤ r₂ then
      if out then (if l.startsWith "  " then sDrop l 2 else l) else "  " ++ l
    else l
  { sc with lines := lines, anchor := none }

/-- Apply one synthetic key press. -/
def press (sc : Screen) (k : Key) : Screen :=
  let m := sc.mods
  let ext := m.shift
  let l := sc.curLine
  match k with
  | .char c =>
      if m.ctrl then
        match c with
        | 'c' => sc.copy
        | 'x' => sc.cut
        | 'v' => sc.paste
        | 'z' => sc.undoOnce
        | 'y' => sc.redoOnce
        | _ => sc
      else sc.insertText (String.singleton c)
  | .space => sc.insertText " "
  | .enter => sc.insertText "\n"
  | .tab =>
      if sc.selection.isSome then sc.indent m.shift
      else if m.shift then sc.indent true
      else sc.insertText "  "
  | .backspace =>
      if sc.selection.isSome then (sc.snapshot).deleteSelection
      else if sc.col > 0 then
        let sc := sc.snapshot
        { sc with lines := sc.lines.set! sc.row (sTake l (sc.col - 1) ++ sDrop l sc.col)
                  col := sc.col - 1 }
      else if sc.row > 0 then
        let prev := sc.lineAt (sc.row - 1)
        let sc := sc.snapshot
        let merged := prev ++ l
        let ls := sc.lines.toList
        { sc with lines := ((ls.take (sc.row - 1)) ++ [merged] ++ ls.drop (sc.row + 1)).toArray
                  row := sc.row - 1, col := prev.length }
      else sc
  | .delete =>
      if sc.selection.isSome then (sc.snapshot).deleteSelection
      else if sc.col < l.length then
        let sc := sc.snapshot
        { sc with lines := sc.lines.set! sc.row (sTake l sc.col ++ sDrop l (sc.col + 1)) }
      else if sc.row < sc.lastRow then
        let sc := sc.snapshot
        let ls := sc.lines.toList
        let merged := l ++ sc.lineAt (sc.row + 1)
        { sc with lines := ((ls.take sc.row) ++ [merged] ++ ls.drop (sc.row + 2)).toArray }
      else sc
  | .left =>
      match sc.selection, ext, m.ctrl with
      | some ((r, c), _), false, false => sc.moveTo r c false   -- collapse to the left edge
      | _, _, true => sc.moveTo sc.row (prevWord l sc.col) ext
      | _, _, _ =>
        if sc.col == 0 && sc.row > 0 then
          sc.moveTo (sc.row - 1) (sc.lineAt (sc.row - 1)).length ext
        else sc.moveTo sc.row (sc.col - 1) ext
  | .right =>
      match sc.selection, ext, m.ctrl with
      | some (_, (r, c)), false, false => sc.moveTo r c false   -- collapse to the right edge
      | _, _, true => sc.moveTo sc.row (nextWord l sc.col) ext
      | _, _, _ =>
        if sc.col ≥ l.length && sc.row < sc.lastRow then sc.moveTo (sc.row + 1) 0 ext
        else sc.moveTo sc.row (sc.col + 1) ext
  | .up => if m.ctrl then sc.moveTo 0 0 ext
           else if sc.row == 0 then sc.moveTo 0 0 ext
           else sc.moveTo (sc.row - 1) sc.col ext
  | .down => if m.ctrl then sc.moveTo sc.lastRow (sc.lineAt sc.lastRow).length ext
             else if sc.row ≥ sc.lastRow then sc.moveTo sc.lastRow l.length ext
             else sc.moveTo (sc.row + 1) sc.col ext
  | .home => if m.ctrl then sc.moveTo 0 0 ext else sc.moveTo sc.row 0 ext
  | .«end» => if m.ctrl then sc.moveTo sc.lastRow (sc.lineAt sc.lastRow).length ext
              else sc.moveTo sc.row l.length ext
  | .pageUp => sc.moveTo (sc.row - min sc.row 10) sc.col ext
  | .pageDown => sc.moveTo (sc.row + 10) sc.col ext
  | .esc => { sc with anchor := none }
  | .f _ => sc

/-- Apply one event from CapslockMode. -/
def apply (sc : Screen) (e : OutputEvent) : Screen :=
  match e.key, e.dir with
  | .mod m, .down => { sc with mods := sc.mods.set m true }
  | .mod m, .up => { sc with mods := sc.mods.set m false }
  | .capsLock, _ => sc
  | .key k, .down => sc.press k
  | .key _, .up => sc

def applyAll (sc : Screen) (es : List OutputEvent) : Screen := es.foldl apply sc

/-- The buffer as text, with `‸` marking the cursor. -/
def render (sc : Screen) : String :=
  let ls := sc.lines.toList.mapIdx fun i l =>
    if i == sc.row then sTake l sc.col ++ "‸" ++ sDrop l sc.col else l
  String.intercalate "\n" ls

/-- The buffer as plain text. -/
def text (sc : Screen) : String := String.intercalate "\n" sc.lines.toList

/-- Load a buffer from text. -/
def ofText (s : String) : Screen := { lines := (s.splitOn "\n").toArray }

end Screen

end CapslockMode
