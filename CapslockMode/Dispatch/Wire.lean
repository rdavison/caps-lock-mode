/-
# The dispatcher's wire

`Dispatch` emits a `List Effect`; the Quartz wire takes `Quartz.Event` lines and
a driver shows `mon ...` lines.  Nothing joined the two, so this is the seam --
and, like `Bridge.lean`, it is a module of its own because it is the only place
that imports both halves.

It cannot live anywhere that already exists:

* **not `Backend/Quartz.lean`**, because `Bridge` imports it and `Dispatch`
  imports `Bridge`, so the dependency would cycle;
* **not `Monitor.lean`**, which imports only `Protocol` and whose whole claim is
  to be a pure renderer -- giving it `Dispatch` would pull `Kanata` and
  `Invariants` into every consumer of a monitor line;
* **not `Main.lean`**, because `Main` is in no test's import graph and a `#guard`
  cannot reach it.  Everything here is pure for exactly that reason.

## Three channels, not one

An effect list goes to three places.  `posts` is the wire; `mon` is the running
commentary a driver displays; `loud` is stderr, which is free because stdout is
the wire.  Keeping them apart here means the loop in `Main` has no policy in it
at all -- it prints each channel to the place that channel goes.

## What is *not* here

`Effect.enter` renders to nothing.  The announcement a reader wants is the
`State`, not the mode alone -- `Monitor.stateLine` already spells one, with the
pending operator and the count that `Mode.name` would drop -- so the loop prints
that from the world it already has.  A second, poorer spelling of the same line
is the sort of drift this module exists to prevent.
-/
import CapslockMode.Dispatch
import CapslockMode.Monitor

namespace CapslockMode.Dispatch.Wire

/-! ## Off the wire

`Quartz.decode` answers in *key* space: a `PhysKey`, which has no side for a
modifier and no image at all for `🔊`.  The dispatcher's input is a `Code`, a
physical position, and keycode-to-`Code` is the direction that carries a round
trip (`Bridge.code_roundTrip`).  So the modal path does not go through `decode`.

What `decode` does that is still needed is the other half of its job: macOS
reports a modifier as a *level* (`flags shift`) and never as a key event, so the
transitions have to be recovered by diffing.  That half is reused rather than
re-tabulated, so the two converters cannot drift in which modifiers they check
or in what order they report them. -/

/-- The modifier edges between two masks, in position space.

A mask names no **side**, so a recovered modifier is always the left one.  That
is this wire's one real loss and it is worth naming: a `defsrc` that binds
`rsft` will never see a right Shift arrive, because the tap never said which it
was.  `Bridge` keeps the sides apart going *out* (`Code.toKeyCode?` gives 56 and
60), so only the incoming direction is collapsed, and the fix -- if it is ever
wanted -- is in the driver, which does have the keycode on a `flagsChanged`. -/
def modEdges (old new : Quartz.Flags) : List (Dir × Kanata.Code) :=
  (Quartz.diff old new).filterMap fun ev =>
    match ev.key with
    | .mod m => some (ev.dir, Kanata.Code.modifier m .left)
    | _ => none

/-- The positions one tap event names, and the level it leaves behind.

`Quartz.decode`'s shape, in position space.  The implied modifier transitions
come first, because a key arriving with a new mask is macOS telling us two
things at once and the modifier is the one that happened first. -/
def edges (f : Quartz.Flags) : Quartz.Event → Quartz.Flags × List (Dir × Kanata.Code)
  | .flagsChanged f' => (f', modEdges f f')
  | .key dir c f' =>
    (f', modEdges f f' ++ (Quartz.codeOf? c).toList.map fun k => (dir, k))
  | .text _ _ f' => (f', modEdges f f')

/-- The level an event reports, for the paths that take no edges from it. -/
def level : Quartz.Event → Quartz.Flags
  | .flagsChanged f => f
  | .key _ _ f => f
  | .text _ _ f => f

/-! ## On to the wire -/

/-- Everything one effect list puts on the three channels a run has.

Three lists and not one because the channels have different destinations:
`posts` and `mon` share stdout and are told apart by the `mon ` prefix, and
`loud` goes to stderr.  Order within a channel is preserved; order *between*
them is not, and need not be, because the loop emits one batch per input edge --
the same granularity `runQuartz` already works at. -/
structure Out where
  /-- Lines a driver is meant to inject. -/
  posts : List Quartz.Event := []
  /-- `mon ...` lines, shown only under `--monitor`. -/
  mon : List String := []
  /-- Lines that must be audible with no `--monitor` at all. -/
  loud : List String := []
  deriving DecidableEq, Repr, Inhabited

/-- Concatenate two batches, channel by channel.

Deliberately *not* an `Append` instance: `simp` unfolds `HAppend.hAppend` and
`Append.append` into `List.append_eq` and loops on the proof below.  A plain
function is one character longer at the call site and keeps the proofs legible.
-/
def Out.append (a b : Out) : Out :=
  { posts := a.posts ++ b.posts, mon := a.mon ++ b.mon, loud := a.loud ++ b.loud }

/-- One effect, under the flag level we have told macOS so far: the level after
it, and what it put on the wire.

`names` is the `deflayer` names, read by exactly one arm.  A plain `List String`
rather than the `Cfg n` so that this function is not width-dependent and a
`#guard` can call it without a config. -/
def one (names : List String) (f : Quartz.Flags) : Effect → Quartz.Flags × Out
  | .emit e =>
    -- Reused, not reimplemented: this *is* `runQuartz`'s inner two lines, one
    -- event at a time.  `posts_of_emits` below is the statement that says so.
    (Quartz.flagsAfter f [e], { posts := Quartz.encodeFrom f [e] })
  | .emitCode ⟨dir, .modifier m _⟩ =>
    -- A modifier is a *level* on this wire, not a key event, and it folds into
    -- the flag state exactly as `Quartz.encodeFrom` folds vi's `.mod`.
    --
    -- Two reasons it cannot post a `key down 56` instead.  A `CGEvent` carries
    -- its own flags field, and that is what an application reads -- so posting
    -- a bare modifier keycode and then `key down 0 -` types a lowercase `a`,
    -- because the second event's mask is empty.  Posting would therefore be
    -- this plus an extra line, never instead of it.  And one rule for both
    -- channels is what keeps a mode crossing honest: a position pressed under
    -- vi and released under the evaluator must not leave a flag behind.
    --
    -- The cost, recorded: an application watching `flagsChanged` sees nothing
    -- while a held modifier has no other key under it.  One line to change.
    (f.set m dir.isDown, {})
  | .emitCode e =>
    match toKeyCode? e with
    | some (dir, code) => (f, { posts := [.key dir code f] })
    | none =>
      -- A position macOS has no virtual keycode for: the mouse, and the
      -- `NSSystemDefined` block -- brightness, play/pause, track skip.  There is
      -- no honest line to write, because those are a different `CGEvent` type on
      -- a different field, and inventing one would be designing a driver
      -- feature nobody asked for.  So it is said twice instead of being
      -- swallowed, which is the failure `Monitor.dropLine` exists for.
      (f, { mon := [Monitor.dropLine s!"no macOS keycode for {e.key.name}"]
            loud := [s!"# no macOS keycode for {e.key.name} ({e.dir.name})"] })
  | .emitText cs =>
    -- Per character, and through `keyEvent` rather than straight to `.text`:
    -- `keyEvent` already decides whether a character has a keycode on this
    -- layout and adds the shift bit when it needs one.  So `(unicode a)` leaves
    -- as a key event and keeps its shortcut semantics, and only a genuinely
    -- unmappable character falls through to a `text` line.
    --
    -- Down and up, because `.text` carries a direction and the driver posts one
    -- event per line.  A `unicode` character has no release of its own to give
    -- back -- which is why `Action.text` is not folded into `Action.keys` -- so
    -- the pair is synthesised here and nothing is recorded as held.
    (f, { posts := cs.flatMap fun c =>
            [Quartz.keyEvent .down (.char c) f, Quartz.keyEvent .up (.char c) f] })
  | .enter _ => (f, {})
  | .setBase i =>
    (f, { mon := [s!"mon base {i} {(names[i]?).getD "?"}"] })
  | .refused form why =>
    (f, { mon := [s!"mon refused {form} ({why.describe})"]
          loud := [s!"# refused: {form} ({why.describe}); that position did nothing"] })

/-- Fold a batch, threading the flag level. -/
def many (names : List String) (f : Quartz.Flags) : List Effect → Quartz.Flags × Out
  | [] => (f, {})
  | e :: rest =>
    let (f₁, o₁) := one names f e
    let (f₂, o₂) := many names f₁ rest
    (f₂, Out.append o₁ o₂)

/-- Did this batch announce a mode change?  The trigger for `Monitor.stateLine`,
which the loop prints from the world rather than from the effect. -/
def entered? : List Effect → Option Mode
  | [] => none
  | .enter m :: _ => some m
  | _ :: es => entered? es

/-! ## The monitor row

Parallel to `Monitor.Entry` rather than a reuse of it, because below the layout
the verdict is a different question.  `Entry.verdict` asks whether the output is
`[input.passthrough]`, over `List OutputEvent` -- but a position the evaluator
handed back unchanged is an `Effect.emitCode` of itself, whose `Effect.emitted`
is `[]` (`Dispatch.emitted_map_emitCode` proves exactly that).  Every
passed-through key would render as `hold`, which is the one thing a monitor must
not do.

The vocabulary is shared: `Monitor.Verdict`, `Monitor.codeOf` and the column
widths all come from there, so `Monitor.header` still lines up over these rows.
-/

/-- What the dispatcher did with one edge. -/
structure Row where
  edge : Edge
  /-- What the wire called it: the virtual keycode, via `Monitor.codeOf`. -/
  code : String := ""
  /-- The vi state *after* the edge.  The evaluator's base layer is announced
  separately, by `mon base`, because the mode column is fourteen wide and a
  layer name is not a mode. -/
  state : State
  effects : List Effect
  deriving Inhabited

/-- Did anything at all reach the keyboard? -/
def reached (es : List Effect) : Bool :=
  !(Effect.emitted es).isEmpty || !(Effect.codes es).isEmpty
    || es.any fun e => match e with | .emitText _ => true | _ => false

def Row.verdict (r : Row) : Monitor.Verdict :=
  if r.effects == [Effect.emitCode ⟨r.edge.dir, r.edge.code⟩] then .passed
  else if reached r.effects then .rewritten
  else .held

/-- The emitted column, in both vocabularies at once: the keystrokes vi
synthesised above the layout, and the positions the evaluator resolved below it.
Both renderers already exist and are the ones the tests speak. -/
def Row.emitted (r : Row) : String :=
  String.intercalate "  "
    ([renderEvents (Effect.emitted r.effects), Kanata.render (Effect.codes r.effects)].filter
      (!·.isEmpty))

/-- The same six columns, at the same widths, as `Monitor.entryRow`.

The key column is `Code.name` -- the kanata spelling of the *position* (`grv`,
`lsft`, `🔊`), not the character the layout produces.  That is the honest name
here, because the dispatcher works in positions and the character is exactly
what a loaded config is free to change. -/
def Row.render (r : Row) : String :=
  s!" {pad r.edge.dir.name 5}{pad (if r.code.isEmpty then "-" else r.code) 5}\
{pad r.edge.code.name 10}{pad r.verdict.name 8}{pad r.state.describe 14}{r.emitted}"

def Row.line (r : Row) : String := s!"mon row {r.render}"

/-! ## The banner -/

/-- What a lenient load has to say for itself.

`Kanata.parse` is lenient on purpose, so a position whose form this evaluator
refuses still exists -- it just does nothing.  Every one is named here, with the
site it was written at, because the alternative is a dead key and no way to find
out why.

Every line starts `#`, which is the one prefix both the Lean parsers and the
Swift driver already drop, so a banner pointed at stdout by mistake cannot be
mistaken for an event. -/
def banner (path : String) (n : Nat) (layers : List String)
    (blocked : List Kanata.Blocked) : List String :=
  let head := s!"# kanata: {path}: {n} positions, {layers.length} layers"
  let names := s!"# kanata: layers: {String.intercalate " " layers}"
  if blocked.isEmpty then [head, names]
  else
    [head, names, s!"# kanata: {blocked.length} refused form(s); \
those positions fall through:"] ++ blocked.map fun b => s!"#   {b.describe}"

/-! ## The vi channel is unchanged -/

/-- **What `--kanata` cannot move.**  An effect list that is nothing but `emit`s
encodes to exactly what `runQuartz` writes today, and leaves exactly the flag
level `runQuartz` would leave.

That is the half of the dispatcher vi owns, so this is the statement behind the
claim that binding a config does not disturb the behaviour the md5 check pins.
`Effect.emitted_map_emit` is its sibling one layer up. -/
theorem posts_of_emits (names : List String) (f : Quartz.Flags) (out : List OutputEvent) :
    many names f (out.map Effect.emit)
      = (Quartz.flagsAfter f out, { posts := Quartz.encodeFrom f out }) := by
  induction out generalizing f with
  | nil => rfl
  | cons e l ih =>
    rw [show (e :: l) = [e] ++ l from rfl, Quartz.encodeFrom_append, Quartz.flagsAfter_append]
    simp only [List.singleton_append, List.map_cons, many, one, ih, Out.append,
               List.append_nil]

end CapslockMode.Dispatch.Wire
