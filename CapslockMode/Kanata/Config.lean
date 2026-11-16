/-
# A config, and how a file becomes one

The whole of `defsrc` / `deflayer` / `defalias` / `defcfg`, for the fragment of
kanata that does not need a clock.

## `Action` is a flat record, not a tree

The obvious encoding is an inductive with `| multi (as : List Action)`.  This is
not that, for three reasons and at two costs, all of which belong in the source
rather than in a plan nobody will read again.

1. **It is what the answer actually is.**  Once aliases are expanded and `multi`
   is flattened, pressing a key means: hold these codes, push these layers, and
   maybe change the base layer.  A tree would be surface syntax kept alive after
   it stopped saying anything new.
2. **`deriving DecidableEq` on an inductive recursive through `List` is not
   something to bet on in Lean 4.34**, and `DecidableEq` is not optional here --
   every `#guard` in `Tests/` needs it, and `HANDOFF.md` records what deriving
   `BEq` alongside it costs.  A flat record derives all three unconditionally.
3. It puts `(multi lsft (layer-while-held x))` and `S-,` into the same shape,
   which is also what kanata's own `MultipleKeyCodes` does with them.

The costs, stated rather than hidden: `(multi a b)` and `(multi b a)` survive
only as the order of `keys`, a `multi` holding two `layer-switch`es keeps the
last, a `multi` holding two tap-holds likewise keeps the last, and a
`use-defsrc` inside a `multi` always lands after the other codes rather than
where it was written.  None is exercised by any config here.

The record is split one level -- `Simple` for what a press does once the
decision is made, `Action` for that plus a decision still open -- which is what
lets `TapHold` hold two branches without `Action` becoming recursive and losing
the `DecidableEq` reason 2 is about.

## Transparency is not a field

A layer entry is `Option Action`.  `none` **is** `_`; `some {}` is `XX`, the
empty action, which is a real no-op and a different thing from falling through
to the layer below.  A `Bool` flag on `Action` would let those two be confused,
and telling them apart is the point of the whole module.

## Layer references are `Nat`

`Fin cfg.layers.length` would be the tighter type and is not available: the
index would depend on a *value* of the structure being defined, which kills
every `deriving` on `Cfg`.  So the bound is a parser obligation -- an unknown
layer name is a parse error -- and `Layer.resolve` treats an out-of-range index
as transparent so that it stays total either way.

The width `n`, by contrast, *is* at the type level.  A `deflayer` with 71
entries against a 72-wide `defsrc` never becomes a `Layer 72`; it is a parse
error naming the layer and both counts.
-/
import CapslockMode.Kanata.Keys
import CapslockMode.Kanata.Sexp

namespace CapslockMode.Kanata

/-- What pressing one position does, after aliases and `multi` are gone. -/
structure Simple where
  /-- Codes held for as long as the physical key is held, in press order. -/
  keys : List Code := []
  /-- Layer indices pushed for as long as the physical key is held. -/
  hold : List Nat := []
  /-- A new base layer, applied on press and surviving the release. -/
  switch : Option Nat := none
  /-- `use-defsrc`: also press whatever `defsrc` says at *this* position.

  A flag and not a `Code`, because the answer depends on where the action is
  used and an alias is shared by every position that names it.  `Layer.resolve`
  is the only thing that ever clears it -- see `Layer.expandSrc`. -/
  src : Bool := false
  /-- `unicode`: characters typed outright, in order.

  Deliberately *not* folded into `keys`.  A `Code` is a position that goes down
  and comes up, and `release` gives every code in `keys` back; a character has
  no release to give, so putting `é` there would make letting go of the key
  un-type it.  So `press` does not emit these, and a caller that can type text
  reads them off the resolved action -- which is exactly the seam a `Machine`
  integration has to fill anyway, since `CapslockMode.Key` has no `é` either. -/
  text : List Char := []
  /-- Forms recognised but not modelled.  Non-empty means pressing this is an
  error naming the form, rather than a silently wrong keystroke. -/
  blocked : List String := []
  deriving DecidableEq, Repr, Inhabited

/-- `(tap-hold <tap-ms> <hold-ms> <tap-action> <hold-action>)`.

The two branches are `Simple`, not `Action`, so a tap-hold inside a tap-hold is
not representable -- which is exactly right, because it is two clocks and a
question about which one owns the key, and the parser records it in `blocked`
rather than modelling it.  It is also what keeps `Action` non-recursive: this
file's header declines to bet on `deriving DecidableEq` through an inductive
recursive via `List`, and every `#guard` in `Tests/` depends on that bet not
being made. -/
structure TapHold where
  /-- Released inside this many milliseconds and it was a tap. -/
  tapTimeout : Nat
  /-- Held at least this long and it is a hold.

  **Stored and not read**, in this phase.  The release rule is a single
  comparison against `tapTimeout`, and in every config seen here the two numbers
  are equal -- `(tap-hold 200 200 ...)`.  The variants that make them differ,
  `tap-hold-press-timeout` and `tap-hold-release-timeout`, are still in
  `clockForms`, so nothing can yet reach a config where this matters. -/
  holdTimeout : Nat
  tap : Simple
  hold : Simple
  deriving DecidableEq, Repr, Inhabited

/-- What pressing one position does, after aliases and `multi` are gone. -/
structure Action extends Simple where
  /-- A decision this press does not make yet.

  `none` for every action that is already one, which is why `Layer.resolve`'s
  type and its three theorems are untouched by tap-hold existing. -/
  tapHold : Option TapHold := none
  deriving DecidableEq, Repr, Inhabited

/-- Combine two actions, as `(multi a b)` does. -/
def Action.merge (a b : Action) : Action :=
  { keys := a.keys ++ b.keys
  , hold := a.hold ++ b.hold
  , switch := match b.switch with | some i => some i | none => a.switch
  , src := a.src || b.src
  , text := a.text ++ b.text
  , blocked := a.blocked ++ b.blocked
  , tapHold := match b.tapHold with | some t => some t | none => a.tapHold }

/-- One `deflayer`.  `none` at a position is `_`. -/
structure Layer (n : Nat) where
  name : String
  acts : Vector (Option Action) n
  deriving DecidableEq, Repr, Inhabited

/-- Why a form is refused.

Three and not one, because "unsupported" is the least useful thing this
evaluator could say.  The three are the three different futures: `clock` is
fixed by giving `InputEvent` a timestamp -- though only half of them, since a
stamp lets a form *decide* by time and not *act* at one, which is why `macro`
and `one-shot` are still refused after `tap-hold` stopped being -- `history` by
giving the evaluator a memory of what it has already emitted, and `world` by
nothing in this project at all, which is the reason that says *do not wait for a
later phase*. -/
inductive Reason where
  /-- Decides by how long a key was held or how soon the next one came. -/
  | clock
  /-- Decides by what was typed before, which this evaluator does not keep. -/
  | history
  /-- Wants something outside the keyboard: a file, or a pointer. -/
  | world
  deriving DecidableEq, Repr, Inhabited

def Reason.describe : Reason → String
  | .clock => "needs a clock"
  | .history => "needs a history this evaluator does not keep"
  | .world => "needs the world outside the keyboard"

/-- A form this evaluator recognised and refused, where it was written, and why.

Kept as a record rather than a string so a test can assert the exact set
without depending on how an error message is phrased. -/
structure Blocked where
  /-- `"tap-hold"`, `"defchordsv2"`, `"lrld"`, ... -/
  form : String
  /-- `"top level"`, `"alias @grv-mode"`, `"deflayer layers"`. -/
  site : String
  /-- Filled in by `reasonOf` at the one place each `Blocked` is built, so the
  reason cannot drift from the list the form is in. -/
  reason : Reason
  deriving DecidableEq, Repr, Inhabited

def Blocked.describe (b : Blocked) : String :=
  s!"{b.form} in {b.site} ({b.reason.describe})"

/-- A whole config, `n` positions wide. -/
structure Cfg (n : Nat) where
  /-- What each position is on a bare keyboard.  Where the transparency chain
  stops; never itself transparent. -/
  src : Vector Code n
  /-- In file order.  The first is layer 0 and the starting base layer. -/
  layers : List (Layer n)
  /-- `defcfg`, rendered back to text.  Stored as strings rather than `Sexp` so
  that `Cfg` keeps `DecidableEq`; almost all of it is driver policy this
  evaluator has no opinion about. -/
  options : List (String × String) := []
  /-- kanata merges layer 0's non-transparent entries *into the defsrc layer*
  when this is on (`deflayer.rs`).  That is observationally the same as putting
  layer 0 at the bottom of the walk, just above `defsrc`, which is how
  `Layer.stack` does it -- but the equivalence is not obvious from the Rust, so
  it is written down here rather than discovered twice. -/
  delegateToFirstLayer : Bool := false
  /-- Every refused form, in file order: top-level blocks, then aliases, then
  layers. -/
  blocked : List Blocked := []
  deriving DecidableEq, Repr, Inhabited

/-- A config whose width is discovered rather than asserted. -/
abbrev Sized := (n : Nat) × Cfg n

/-- One layer, every position transparent.  By kanata's own semantics this
resolves to `defsrc` everywhere -- the identity function -- which is the result
the rest of the design rests on.  See `Layer.resolve_identity`. -/
def Cfg.identity (src : Vector Code n) : Cfg n :=
  { src := src
  , layers := [{ name := "identity", acts := Vector.replicate n none }] }

/-- Which layer a name refers to, if any. -/
def Cfg.layerIx? (cfg : Cfg n) (name : String) : Option Nat :=
  cfg.layers.findIdx? (·.name == name)

/-- A position, bounds-checked once so callers do not carry a proof. -/
def pos? (n : Nat) (i : Nat) : Option (Fin n) :=
  if h : i < n then some ⟨i, h⟩ else none

/-! ## Forms this evaluator refuses, and why they are three lists and not one

The lists are by *reason*, not by position.  A form that kanata only accepts in
one of the two positions -- `(tap-hold ...)` as a list, `sldr` as a bare atom --
is recorded as unmodelled in either, rather than as the syntax error kanata
reports for the wrong one.  Splitting each list in two would buy only that
distinction, and it is not worth having: the config does not run here either
way, and "needs a clock" is the more useful half of the answer. -/

/-- Needs a clock.  Every one of these decides what it does by how long a key
was held or how soon the next one came.

**`tap-hold` is no longer on this list**, and what is left is not simply waiting
its turn.  A timestamp was enough for `tap-hold` because its decision is made
*when the next event arrives*, and that event carries the clock.  The rest need
more than a stamp:

* `one-shot` is a latch with an expiry of its own -- a second kind of pending
  state with a different lifetime, not the same one renamed.
* `macro` emits *in the future*: `(macro \ S-, 100 spc ...)` has a delay between
  emissions, so it needs something that fires with no input to prompt it.
* `tap-dance`, `caps-word`, `sldr` and `scnl` are the same shape as one of those
  two.

`sldr` and `scnl` are here rather than with the history forms because a sequence
leader's first obligation is the sequence *timeout*; that it also has to
remember the sequence so far is the second problem, not the first.

The eleven `tap-hold-*` variants stay, because they differ from plain
`tap-hold` in exactly the part this evaluator decided by fiat: see the
divergence recorded in `Kanata/Eval.lean`. -/
def clockForms : List String :=
  [ "tap-hold-press", "tap-hold-release"
  , "tap-hold-press-timeout", "tap-hold-release-timeout"
  , "tap-hold-release-keys", "tap-hold-except-keys"
  , "one-shot", "one-shot-press", "one-shot-release"
  , "one-shot-press-pcancel", "one-shot-release-pcancel"
  , "tap-dance", "tap-dance-eager"
  , "macro", "macro-repeat", "macro-release-cancel", "macro-repeat-release-cancel"
  , "caps-word", "caps-word-custom"
  , "sldr", "scnl" ]

/-- Needs a history.  Each of these answers a question about what already
happened, and `St` remembers only which positions are down and what their press
resolved to -- deliberately, because that is all `release` needs.

`fork` and `switch` look like present-tense tests of what is held, and are not:
kanata answers them against its own output state, which is the press history
condensed, and `switch`'s `key-timing` conditions want the clock on top.  Giving
them the clock reason would point at the wrong phase. -/
def historyForms : List String :=
  [ "rpt", "rpt-any", "rpt-key", "repeat"
  , "fork", "switch"
  , "dynamic-macro-record", "dynamic-macro-play"
  , "dynamic-macro-record-stop", "dynamic-macro-record-stop-truncate" ]

/-- Needs a world.  `lrld` is perfectly timeless -- it just re-reads a file, and
a pure evaluator has no file.  The mouse is the same shape of problem with a
different noun: a pointer is no more part of a keyboard than a file is, and
there is no `Code` a click could be written as on the way out.

Kept apart from `clockForms` because giving these the clock reason would be a
lie, and phase 3 will not fix any of them.

Note that the *names* `mlft`, `mwu`, `mvmt` and the rest are perfectly good
`Code`s -- kanata's `defsrc` takes them as input positions, and `Keys.lean`
parses them.  It is only in action position that they are refused, which is why
`parseAtom` consults this list before the key table, exactly as kanata's
`parse_action_atom` runs before its `str_to_oscode`. -/
def worldForms : List String :=
  [ "lrld", "lrld-next", "lrnx", "lrld-prev", "lrpv"
  , "mlft", "mouseleft", "mrgt", "mouseright", "mmid", "mousemid"
  , "mfwd", "mouseforward", "mbck", "mousebackward"
  , "mltp", "mousetapleft", "mrtp", "mousetapright", "mmtp", "mousetapmid"
  , "mftp", "mousetapforward", "mbtp", "mousetapbackward"
  , "mwu", "mousewheelup", "mwd", "mousewheeldown"
  , "mwl", "mousewheelleft", "mwr", "mousewheelright"
  , "mvmt", "mousemovement"
  , "mwheel-up", "mwheel-down", "mwheel-left", "mwheel-right"
  , "mwheel-accel-up", "mwheel-accel-down", "mwheel-accel-left", "mwheel-accel-right"
  , "movemouse-up", "movemouse-down", "movemouse-left", "movemouse-right"
  , "movemouse-accel-up", "movemouse-accel-down"
  , "movemouse-accel-left", "movemouse-accel-right"
  , "movemouse-speed", "setmouse" ]

/-- Top-level blocks recognised and skipped whole.  All three are chord- or
sequence-timing machinery. -/
def blockedBlocks : List String :=
  ["defchordsv2", "defchordsv2-experimental", "defchords", "defseq"]

/-- The reason a refused form is refused.

Total, and the fall-through is `clock` because the two lists it stands for --
`clockForms` and the chord/sequence `blockedBlocks` -- are the timing ones.  A
form in none of the four never reaches here: nothing records a `Blocked` for a
form it did not first find in one of them. -/
def reasonOf (form : String) : Reason :=
  if historyForms.contains form then .history
  else if worldForms.contains form then .world
  else .clock

/-- Whether a form is refused at all, for the two parsers that have to ask
before they consult the key table. -/
def isBlockedForm (form : String) : Bool :=
  clockForms.contains form || historyForms.contains form || worldForms.contains form

/-- `_`, and the two Unicode spellings kanata also accepts for it. -/
def isTransAtom (a : String) : Bool := a == "_" || a == "‗" || a == "≝"

/-- `XX`, and the three Unicode spellings of the no-op. -/
def isNoOpAtom (a : String) : Bool := a == "XX" || a == "✗" || a == "∅" || a == "•"

/-! ## Parsing -/

/-- Strip a literal prefix.  Written over `List Char` rather than with
`String.drop`, which returns a `String.Slice` in Lean 4.34. -/
private def dropChars? : List Char → List Char → Option (List Char)
  | [], cs => some cs
  | _, [] => none
  | a :: as, c :: cs => if a == c then dropChars? as cs else none

private def dropPrefix? (p s : String) : Option String :=
  (dropChars? p.toList s.toList).map String.ofList

/-- kanata's `KEYMODI`, minus the Unicode spellings.

All nine are upper case, so none can collide with a lower-case key name like
`min`, and none is a prefix of another (`AG-` does not start with `A-`, because
`A-` is two characters).  Longest first anyway, so the table stays correct if
someone adds a spelling where that does matter. -/
def modPrefixes : List (String × Code) :=
  [ ("RS-", .modifier .shift .right)
  , ("RC-", .modifier .ctrl .right)
  , ("RA-", .modifier .alt .right)
  , ("RM-", .modifier .super .right)
  , ("AG-", .modifier .alt .right)
  , ("S-", .modifier .shift .left)
  , ("C-", .modifier .ctrl .left)
  , ("A-", .modifier .alt .left)
  , ("M-", .modifier .super .left) ]

/-- Peel modifier prefixes off an atom.  A repeat is an error, as in kanata. -/
private partial def stripMods (s : String) (acc : List Code) :
    Except String (List Code × String) :=
  match modPrefixes.find? (fun p => (dropPrefix? p.1 s).isSome) with
  | some (p, c) =>
    if acc.contains c then .error s!"redundant modifier {p} in {s}"
    else stripMods ((dropPrefix? p s).getD s) (acc ++ [c])
  | none => .ok (acc, s)

/-- What `parseAction` needs from the rest of the file: every layer name, so a
`layer-while-held` can name a layer defined later, and the aliases defined so
far, since an alias may only use an earlier one. -/
private structure Ctx where
  layerNames : List String
  aliases : List (String × Action)

/-- An atom in action position.

The order is kanata's `parse_action_atom`, and both halves of it are
load-bearing.  The action names come **before** the key table, which is what
makes `mlft` a click here and the mouse button in `defsrc` -- the same atom,
read twice, exactly as kanata reads it.  The key table then comes **before** the
modifier-prefix parser, so a key whose name happens to start with `S-` would
still be that key.  Getting either backwards is a cheap mistake with a very
confusing symptom. -/
private def parseAtom (ctx : Ctx) (a : String) : Except String (Action × List String) :=
  if isTransAtom a then
    .error "_ is only meaningful as a whole (deflayer) entry"
  else if isNoOpAtom a then
    .ok ({}, [])
  else if a == "use-defsrc" then
    -- No position here to resolve it against; `Layer.resolve` has one.
    .ok ({ src := true }, [])
  else if isBlockedForm a then
    .ok ({ blocked := [a] }, [a])
  else
    match Code.ofName? a with
    | some c => .ok ({ keys := [c] }, [])
    | none =>
      match dropPrefix? "@" a with
      | some nm =>
        match ctx.aliases.lookup nm with
        | some act =>
          -- The alias carries its `blocked` into the action, so pressing this
          -- still fails -- but it is not reported a second time, because it was
          -- already reported where the alias was defined.
          .ok (act, [])
        | none => .error s!"unknown alias @{nm} (aliases must be defined before use)"
      | none => do
        let (mods, rest) ← stripMods a []
        if mods.isEmpty then .error s!"unknown key or action: {a}"
        else match Code.ofName? rest with
          | some c => .ok ({ keys := mods ++ [c] }, [])
          | none => .error s!"unknown key '{rest}' after the modifiers in {a}"

private def hexDigit? (c : Char) : Option Nat :=
  let n := c.toNat
  if c.isDigit then some (n - '0'.toNat)
  else if 'a'.toNat ≤ n && n ≤ 'f'.toNat then some (n - 'a'.toNat + 10)
  else if 'A'.toNat ≤ n && n ≤ 'F'.toNat then some (n - 'A'.toNat + 10)
  else none

private def hexOfChars? : List Char → Option Nat
  | [] => none
  | cs => cs.foldlM (fun acc c => (hexDigit? c).map (fun d => acc * 16 + d)) 0

/-- `(unicode é)` and `(unicode U+00E9)`, which kanata treats as the same thing.

The round trip through `Char.ofNat` is the validity check: it is the identity on
a codepoint a `Char` can hold and lands somewhere else on a surrogate or a value
past `0x10FFFF`, so comparing the two rules those out without a second table. -/
private def unicodeArg? (s : String) : Option Char :=
  match s.toList with
  | [c] => some c
  | 'U' :: '+' :: ds | 'u' :: '+' :: ds => do
    let n ← hexOfChars? ds
    let c := Char.ofNat n
    if c.toNat == n then some c else none
  | _ => none

/-- A bare number in argument position, for the two timeouts. -/
private def natArg? : Sexp → Option Nat
  | .atom a => if !a.isEmpty && a.all Char.isDigit then some a.toNat! else none
  | _ => none

private def layerArg (ctx : Ctx) (head : String) : List Sexp → Except String Nat
  | [.atom nm] =>
    match ctx.layerNames.findIdx? (· == nm) with
    | some i => .ok i
    | none => .error s!"({head} {nm}): no layer is called {nm}"
  | _ => .error s!"({head} ...) takes exactly one layer name"

/-- Parse one action.

The second component is the blocked forms written **at this site**.  An
`@alias` reference contributes nothing to it, which is what keeps the reported
list one entry per definition rather than one per use: `@grv-mode` appears in
four layers and is refused once. -/
private partial def parseAction (ctx : Ctx) (e : Sexp) :
    Except String (Action × List String) := do
  match e with
  | .str s => .error s!"a string (\"{s}\") is not an action"
  | .atom a => parseAtom ctx a
  | .list [] => .error "() is not an action"
  | .list (.atom head :: args) =>
    if head == "multi" then do
      let rs ← args.mapM (parseAction ctx)
      .ok (rs.foldl (fun acc r => acc.merge r.1) ({} : Action), rs.flatMap (·.2))
    else if head == "layer-while-held" || head == "layer-toggle" then do
      -- Not a synonym recorded in a comment: literally the same `Action`, so
      -- `layer-toggle` cannot drift into being a latch.  kanata's own
      -- `layer-toggle` is the while-held one; the latching form is
      -- `layer-switch`.
      let i ← layerArg ctx head args
      .ok ({ hold := [i] }, [])
    else if head == "layer-switch" then do
      let i ← layerArg ctx head args
      .ok ({ switch := some i }, [])
    else if head == "unicode" || head == "🔣" then
      match args with
      | [.atom a] | [.str a] =>
        match unicodeArg? a with
        | some c => .ok ({ text := [c] }, [])
        | none => .error s!"({head} {a}): expected one character, or U+ and a hex codepoint"
      | _ => .error s!"({head} ...) takes exactly one character"
    else if head == "tap-hold" then
      match args with
      | [tapT, holdT, tapA, holdA] =>
        match natArg? tapT, natArg? holdT with
        | some tt, some ht => do
          let (ta, tb) ← parseAction ctx tapA
          let (ha, hb) ← parseAction ctx holdA
          if ta.tapHold.isSome || ha.tapHold.isSome then
            -- A tap-hold inside a tap-hold is two clocks and a question about
            -- which one owns the key.  Recorded and refused, exactly as this
            -- form was before the outer one was modelled.
            .ok ({ blocked := ["tap-hold"] }, ["tap-hold"])
          else
            .ok ({ tapHold := some { tapTimeout := tt, holdTimeout := ht
                                   , tap := ta.toSimple, hold := ha.toSimple } }, tb ++ hb)
        | _, _ =>
          .error s!"(tap-hold {tapT.render} {holdT.render} ...): \
the two timeouts are numbers of milliseconds"
      | _ =>
        .error "(tap-hold <tap-ms> <hold-ms> <tap-action> <hold-action>) takes four arguments"
    else if isBlockedForm head then
      .ok ({ blocked := [head] }, [head])
    else
      .error s!"unknown action: ({head} ...)"
  | .list _ => .error "an action list must start with an atom"

/-- One `deflayer` entry.  `_` is `none` here and nowhere else: inside a
`multi` it is an error, because kanata has nothing sensible to do with it. -/
private def parseEntry (ctx : Ctx) (e : Sexp) :
    Except String (Option Action × List String) := do
  match e with
  | .atom a =>
    if isTransAtom a then .ok (none, [])
    else do let (act, bl) ← parseAtom ctx a; .ok (some act, bl)
  | _ => do let (act, bl) ← parseAction ctx e; .ok (some act, bl)

/-- `(defcfg k v k v ...)` and `(defalias name act name act ...)` both take
pairs, and a missing half is the commonest way to break either. -/
private def pairsOf (what : String) : List Sexp → Except String (List (String × Sexp))
  | [] => .ok []
  | [e] => .error s!"({what} ...): {e.render} has no value — entries come in pairs"
  | .atom k :: v :: rest => do let ps ← pairsOf what rest; .ok ((k, v) :: ps)
  | e :: _ => .error s!"({what} ...): expected a name, got {e.render}"

/-- What one pass over the top-level forms collects. -/
private structure Scan where
  sawCfg : Bool := false
  src : Option (List Sexp) := none
  layerForms : List (String × List Sexp) := []
  aliasForms : List (String × Sexp) := []
  options : List (String × String) := []
  delegate : Bool := false
  blocked : List Blocked := []

private def scanForm (sc : Scan) (e : Sexp) : Except String Scan := do
  match e with
  | .list (.atom "defcfg" :: args) =>
    if sc.sawCfg then .error "more than one (defcfg)"
    else do
      let ps ← pairsOf "defcfg" args
      let dele := ((ps.lookup "delegate-to-first-layer").map
        (fun v => ["yes", "true", "1"].contains v.render)).getD false
      .ok { sc with sawCfg := true, delegate := dele
                  , options := ps.map (fun kv => (kv.1, kv.2.render)) }
  | .list (.atom "defsrc" :: args) =>
    if sc.src.isSome then .error "more than one (defsrc)"
    else .ok { sc with src := some args }
  | .list (.atom "defalias" :: args) => do
    let ps ← pairsOf "defalias" args
    .ok { sc with aliasForms := sc.aliasForms ++ ps }
  | .list (.atom "deflayer" :: .atom nm :: args) =>
    if sc.layerForms.any (·.1 == nm) then .error s!"more than one (deflayer {nm})"
    else .ok { sc with layerForms := sc.layerForms ++ [(nm, args)] }
  | .list (.atom "deflayer" :: _) => .error "(deflayer ...) needs a layer name"
  | .list (.atom head :: _) =>
    if blockedBlocks.contains head then
      .ok { sc with blocked :=
        sc.blocked ++ [{ form := head, site := "top level", reason := reasonOf head }] }
    else
      -- A typo must not be skipped.  `$var`, `deftemplate`, `defvar`,
      -- `deflocalkeys-*`, `defvirtualkeys` and `include` all land here, which
      -- is the honest answer: this evaluator does not implement them.
      .error s!"unknown top-level block: ({head} ...)"
  | _ => .error s!"expected a top-level block, got {e.render}"

/-- A config with its width still a runtime number.  The one step between the
file and `Cfg n`, so that `parse` and `parseAs` can differ only in where `n`
comes from. -/
structure Raw where
  src : List Code
  layers : List (String × List (Option Action))
  options : List (String × String)
  delegate : Bool
  blocked : List Blocked

/-- Everything except the width check. -/
def parseRaw (input : String) : Except String Raw := do
  let forms ← read input
  let sc ← forms.foldlM scanForm ({} : Scan)
  let some srcArgs := sc.src
    | .error "no (defsrc) block"
  if sc.layerForms.isEmpty then .error "no (deflayer ...) block"
  let srcCodes ← srcArgs.mapM fun e =>
    match e with
    | .atom a =>
      match Code.ofName? a with
      | some c => .ok c
      | none => .error s!"in (defsrc): unknown key {a}"
    | _ => .error s!"in (defsrc): expected a key name, got {e.render}"
  let names := sc.layerForms.map (·.1)
  -- Aliases resolve in one forward pass, so an alias may use an earlier alias
  -- but not a later one.  Layer names, by contrast, are all known already,
  -- which is why the scan is a separate pass at all.
  let aliasStep : List (String × Action) × List Blocked → String × Sexp →
      Except String (List (String × Action) × List Blocked) := fun st nv =>
    let (acc, bl) := st
    let (nm, e) := nv
    if (acc.lookup nm).isSome then .error s!"(defalias): @{nm} is defined twice"
    else match parseAction { layerNames := names, aliases := acc } e with
      | .error m => .error s!"in alias @{nm}: {m}"
      | .ok (act, forms) =>
        .ok (acc ++ [(nm, act)],
             bl ++ forms.map (fun f =>
               { form := f, site := s!"alias @{nm}", reason := reasonOf f }))
  let (aliases, aliasBlocked) ← sc.aliasForms.foldlM aliasStep
    (([] : List (String × Action)), ([] : List Blocked))
  let ctx : Ctx := { layerNames := names, aliases := aliases }
  let layerStep : List (String × List (Option Action)) × List Blocked → String × List Sexp →
      Except String (List (String × List (Option Action)) × List Blocked) := fun st nv =>
    let (acc, bl) := st
    let (nm, es) := nv
    let one : Sexp × Nat → Except String (Option Action × List String) := fun ei =>
      match parseEntry ctx ei.1 with
      | .error m => .error s!"in (deflayer {nm}) position {ei.2}: {m}"
      | .ok r => .ok r
    match (es.zip (List.range es.length)).mapM one with
    | .error m => .error m
    | .ok rs =>
      .ok (acc ++ [(nm, rs.map (·.1))],
           bl ++ (rs.flatMap (·.2)).map (fun f =>
             { form := f, site := s!"deflayer {nm}", reason := reasonOf f }))
  let (layers, layerBlocked) ← sc.layerForms.foldlM layerStep
    (([] : List (String × List (Option Action))), ([] : List Blocked))
  return { src := srcCodes, layers := layers, options := sc.options
         , delegate := sc.delegate, blocked := sc.blocked ++ aliasBlocked ++ layerBlocked }

/-- Impose a width.  Every length mismatch is reported with both numbers,
because "your layer is the wrong size" without them is useless in a 72-wide
table. -/
def Raw.sized (r : Raw) (n : Nat) : Except String (Cfg n) := do
  if hs : r.src.length = n then
    let layers ← r.layers.mapM fun nl =>
      if hl : nl.2.length = n then
        .ok ({ name := nl.1, acts := ⟨nl.2.toArray, by simpa using hl⟩ } : Layer n)
      else
        .error s!"(deflayer {nl.1}) has {nl.2.length} entries but (defsrc) has {n}"
    return { src := ⟨r.src.toArray, by simpa using hs⟩
           , layers := layers
           , options := r.options
           , delegateToFirstLayer := r.delegate
           , blocked := r.blocked }
  else
    .error s!"(defsrc) has {r.src.length} entries but {n} were expected"

/-- Parse at a width the caller asserts.  `parseAs 72 fixture` is how a test
says "72 wide" out loud. -/
def parseAs (n : Nat) (input : String) : Except String (Cfg n) := do
  (← parseRaw input).sized n

/-- Parse, taking the width from `defsrc`. -/
def parse (input : String) : Except String Sized := do
  let r ← parseRaw input
  let n := r.src.length
  return ⟨n, ← r.sized n⟩

/-- Parse, and refuse a config containing anything this evaluator does not
model.  The lenient `parse` is the useful one -- it lets the real config be
tested against -- and this is what a caller uses when a wrong answer would be
worse than no answer. -/
def parseStrict (input : String) : Except String Sized := do
  let c ← parse input
  if c.2.blocked.isEmpty then return c
  else .error s!"unmodelled forms: {String.intercalate ", " (c.2.blocked.map Blocked.describe)}"

end CapslockMode.Kanata
