/-
# capslockmode

    capslockmode run            filter keyboard events (the real thing)
    capslockmode run --kanata F  ... with a kanata config bound to insert mode
    capslockmode demo SCRIPT    type SCRIPT into a text field and show the result
    capslockmode trace SCRIPT   show what each key does, key by key
    capslockmode keys           print the key map (generated from the machine)

`run` speaks the line protocol described in `CapslockMode/Protocol.lean`; a
driver such as `drivers/evdev_bridge.py` connects it to a real keyboard.
-/
import CapslockMode

open CapslockMode

/-- Which wire format `run` speaks. -/
inductive Wire where
  /-- Key names and modifier sets: the evdev-shaped protocol. -/
  | raw
  /-- Virtual keycodes and flag masks: what a macOS event tap wants. -/
  | quartz
  deriving DecidableEq, Repr, Inhabited

/-- Command line options. -/
structure Opts where
  cfg : Config := {}
  wire : Wire := .raw
  text : String := "the quick brown fox\njumps over the lazy dog\nand then takes a nap"
  verbose : Bool := false
  /-- Interleave `mon ...` lines describing each event, for a driver to display. -/
  monitor : Bool := false
  /-- A kanata config to bind insert mode to.

  A path and not a parsed config: `parseOpts` is pure and `Except String`, and
  is the only part of this a `#guard` could ever reach.  Reading the file is the
  one piece that genuinely is `IO`, so it happens in `main`. -/
  kanata : Option System.FilePath := none
  deriving Inhabited

def usage : String :=
"capslockmode - a vi-like modal layer for your keyboard, toggled with Caps Lock

USAGE:
  capslockmode run [options]          read key events on stdin, write key events on stdout
  capslockmode demo <script> [opts]   apply a vim-style key script to a sample buffer
  capslockmode trace <script> [opts]  like demo, but show every step
  capslockmode keys                   print the key map
  capslockmode --help | --version

OPTIONS:
  --platform <name>   keystrokes to compile commands into: pc (default) or mac
  --wire <name>       protocol spoken by `run`: raw (default) or quartz
  --kanata <file>     run this kanata config in insert mode (needs --wire quartz)
  --toggle <key>      key that switches modes (default: caps); a name, a bare
                      keycode of 2+ digits, or code:<n> for any keycode
  --max-count <n>     largest accepted count prefix (default: 100)
  --start-normal      start in normal mode instead of insert
  --no-esc            do not let Esc return to normal mode from insert
  --text <string>     buffer contents for demo/trace
  --verbose           log mode changes on stderr
  --monitor           also emit `mon ...` lines describing each event, for a driver

SCRIPTS use vim key notation: 'ihello<Esc>dd', '<Caps>3jdw', '<C-r>'."

/-- A toggle key as a user spells it: a name (`caps`, `f18`, `esc`) or, for
`--wire quartz`, a bare virtual keycode.  Shared by the `--toggle` flag and the
`toggle` command, so the two cannot drift. -/
def parseToggle? (k : String) : Option PhysKey :=
  let asCode (n : String) : Option PhysKey :=
    if !n.isEmpty && n.all Char.isDigit then Quartz.physOf? (UInt16.ofNat n.toNat!) else none
  match k.splitOn ":" with
  -- `code:8` is keycode 8.  Bare `8` is the `8` key, because a single character
  -- is a key name first (`Protocol.parsePhysKey?`), which makes keycodes 0-9
  -- unreachable without this form.  Bare codes of two digits or more still
  -- work, so existing `--toggle 57` keeps meaning Caps Lock.
  | ["code", n] => asCode n
  | _ => parsePhysKey? k <|> asCode k

/-- Parse the options that may follow a subcommand. -/
partial def parseOpts (args : List String) (o : Opts) : Except String (Opts × List String) :=
  match args with
  | [] => .ok (o, [])
  | "--platform" :: n :: rest =>
    match Platform.ofName? n with
    | some p => parseOpts rest { o with cfg := { o.cfg with platform := p } }
    | none => .error s!"unknown platform: {n} (try pc or mac)"
  | "--wire" :: n :: rest =>
    match n with
    | "raw" => parseOpts rest { o with wire := .raw }
    | "quartz" | "mac" | "macos" => parseOpts rest { o with wire := .quartz }
    | _ => .error s!"unknown wire format: {n} (try raw or quartz)"
  | "--toggle" :: k :: rest =>
    match parseToggle? k with
    | some pk => parseOpts rest { o with cfg := { o.cfg with toggleKey := pk } }
    | none => .error s!"unknown key: {k}"
  | "--max-count" :: n :: rest =>
    if n.all Char.isDigit && !n.isEmpty then
      parseOpts rest { o with cfg := { o.cfg with maxCount := n.toNat! } }
    else .error s!"not a number: {n}"
  | "--kanata" :: f :: rest => parseOpts rest { o with kanata := some f }
  | "--text" :: t :: rest => parseOpts rest { o with text := t }
  | "--start-normal" :: rest => parseOpts rest { o with cfg := { o.cfg with startMode := .normal } }
  | "--no-esc" :: rest => parseOpts rest { o with cfg := { o.cfg with escapeToNormal := false } }
  | "--verbose" :: rest => parseOpts rest { o with verbose := true }
  | "--monitor" :: rest => parseOpts rest { o with monitor := true }
  | a :: rest =>
    if a.startsWith "--" then .error s!"unknown option: {a}"
    else do
      let (o, positional) ← parseOpts rest o
      return (o, a :: positional)

/-- Options that parse but cannot be honoured together.

Checked after the whole command line is read, so that `--kanata f --wire quartz`
and `--wire quartz --kanata f` cannot disagree -- which is exactly what would
happen if the check lived in `parseOpts`, where only one of them has been seen.

Rejecting rather than ignoring: only the Quartz wire carries keycodes, so a
`--kanata` under `--wire raw` can do nothing at all, and a flag that silently
does nothing is the failure `Monitor.dropLine` exists to prevent. -/
def optsError? (o : Opts) (cmd : String) : Option String :=
  match o.kanata with
  | none => none
  | some _ =>
    if cmd != "run" then
      some s!"--kanata applies to `run`, not `{cmd}`"
    else if o.wire != .quartz then
      some "--kanata needs --wire quartz: only the Quartz wire carries keycodes, \
so the raw wire has no way to name a position"
    else none

/-- The Quartz filter: keycodes and flag masks in, the same out.

Two flag states are threaded through: `fin` is what the tap last reported, so
that `Quartz.decode` can turn a new mask into the press and release events the
machine expects, and `fout` is what we have told macOS, so that a modifier held
across two keystrokes in insert mode is not dropped.  `Quartz.flags_settle` is
why command mode can share `fout` safely: an emitted command always hands the
flag state back as it found it. -/
partial def runQuartz (o : Opts) (st : State) (fin fout : Quartz.Flags)
    (dev : Option Monitor.Device := none) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr
  let line ← stdin.getLine
  if line.isEmpty then return ()
  let trimmed := line.trim
  if trimmed.isEmpty || trimmed.startsWith "#" then runQuartz o st fin fout dev
  else if trimmed == "?" then
    stdout.putStrLn s!"# mode: {st.describe}"
    stdout.flush
    runQuartz o st fin fout dev
  else if trimmed.startsWith "dev" then
    match Monitor.parseDevice? trimmed with
    | some d =>
      if o.monitor then
        if let some report := Monitor.deviceChange? dev d then
          stdout.putStrLn report
          stdout.flush
      runQuartz o st fin fout (some d)
    | none =>
      stderr.putStrLn s!"# ignored: {trimmed}"
      runQuartz o st fin fout dev
  else if trimmed.startsWith "toggle" then
    -- Rebinding resets the machine: changing the key that leaves normal mode
    -- while sitting in normal mode would otherwise strand the keyboard.
    match trimmed.splitOn " " with
    | ["toggle", k] =>
      match parseToggle? k with
      | some pk =>
        let o := { o with cfg := { o.cfg with toggleKey := pk } }
        stdout.putStrLn s!"# toggle: {pk.name}"
        if o.monitor then stdout.putStrLn (Monitor.stateLine o.cfg.start)
        stdout.flush
        -- The machine resets, but the device does not: rebinding a key says
        -- nothing about which keyboard the events are coming from, and
        -- re-announcing it would look like a device change that never happened.
        runQuartz o o.cfg.start fin fout dev
      | none =>
        stderr.putStrLn s!"# unknown key: {k}"
        runQuartz o st fin fout dev
    | _ =>
      stderr.putStrLn s!"# usage: toggle <key>"
      runQuartz o st fin fout dev
  else match Quartz.parseLine? trimmed with
    | none =>
      stderr.putStrLn s!"# ignored: {trimmed}"
      if o.monitor then
        stdout.putStrLn (Monitor.dropLine trimmed)
        stdout.flush
      runQuartz o st fin fout dev
    | some inc =>
      let (fin', evs) := Quartz.decode fin inc.injected inc.event inc.time
      -- A line that decodes to nothing is the failure that hides: a keycode
      -- absent from the table produces no events and, without this, no output
      -- either.  Say so rather than looking dead.
      if o.monitor && evs.isEmpty then
        stdout.putStrLn (Monitor.dropLine trimmed)
      let code := Monitor.codeOf inc.event
      let mut st := st
      let mut fout := fout
      for iev in evs do
        let (st', out) := step o.cfg st iev
        if o.monitor then
          stdout.putStrLn (Monitor.line { input := iev, state := st', out := out, code := code })
          if st'.describe != st.describe then
            stdout.putStrLn (Monitor.stateLine st')
        st := st'
        for qe in Quartz.encodeFrom fout out do
          stdout.putStrLn qe.line
        fout := Quartz.flagsAfter fout out
      stdout.flush
      runQuartz o st fin' fout dev

/-- The Quartz filter with a kanata config bound to insert mode.

Three states are threaded, one more than `runQuartz` and for the same reasons.
`fin` is the level the tap last reported, so a `flags` line can be turned back
into edges; `fout` is the level we have told macOS, so a modifier held across
two keystrokes is not dropped; `w` is the dispatcher's own world, which carries
the vi `State`, the evaluator's `St`, the recovered modifier level, and the
positions no backend claimed.

`mk` is the assembly as a function of the `Config` rather than a `Step`,
because the `toggle <key>` control line rebuilds the config at runtime and
`modal` has to be applied again.  `names` is the `deflayer` names, for the one
line that announces a `layer-switch`.

Note what this does *not* call: `Quartz.decode`.  It answers in key space --
a `PhysKey`, which has no side for a modifier and no image at all for `🔊` --
and the dispatcher's input is a position.  Keycode to `Code` is the direction
that carries a round trip (`Bridge.code_roundTrip`), so the modal path uses it
directly.  What `decode` does that is still needed, turning a mask into
transitions, is `Wire.edges`, which reuses `Quartz.diff` so the two converters
cannot drift. -/
partial def runModal (o : Opts) (names : List String)
    (mk : Config → Dispatch.Step (State × Kanata.St))
    (w : Dispatch.World (State × Kanata.St)) (fin fout : Quartz.Flags)
    (dev : Option Monitor.Device := none) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr
  let line ← stdin.getLine
  if line.isEmpty then return ()
  let trimmed := line.trim
  if trimmed.isEmpty || trimmed.startsWith "#" then runModal o names mk w fin fout dev
  else if trimmed == "?" then
    stdout.putStrLn s!"# mode: {w.backend.1.describe}  base: {w.backend.2.base}"
    stdout.flush
    runModal o names mk w fin fout dev
  else if trimmed.startsWith "dev" then
    match Monitor.parseDevice? trimmed with
    | some d =>
      if o.monitor then
        if let some report := Monitor.deviceChange? dev d then
          stdout.putStrLn report
          stdout.flush
      runModal o names mk w fin fout (some d)
    | none =>
      stderr.putStrLn s!"# ignored: {trimmed}"
      runModal o names mk w fin fout dev
  else if trimmed.startsWith "toggle" then
    match trimmed.splitOn " " with
    | ["toggle", k] =>
      match parseToggle? k with
      | some pk =>
        let o := { o with cfg := { o.cfg with toggleKey := pk } }
        stdout.putStrLn s!"# toggle: {pk.name}"
        if o.monitor then stdout.putStrLn (Monitor.stateLine o.cfg.start)
        stdout.flush
        -- The evaluator resets with the machine.  Rebinding the key that leaves
        -- normal mode while a position is held would stray either way, and
        -- `Kanata.release` of a position it never recorded is silent by design,
        -- so the quiet answer is to start both halves clean.
        runModal o names mk { backend := (o.cfg.start, {}) } fin fout dev
      | none =>
        stderr.putStrLn s!"# unknown key: {k}"
        runModal o names mk w fin fout dev
    | _ =>
      stderr.putStrLn s!"# usage: toggle <key>"
      runModal o names mk w fin fout dev
  else match Quartz.parseLine? trimmed with
    | none =>
      stderr.putStrLn s!"# ignored: {trimmed}"
      if o.monitor then
        stdout.putStrLn (Monitor.dropLine trimmed)
        stdout.flush
      runModal o names mk w fin fout dev
    | some inc =>
      if inc.injected then
      -- Our own event on its way back to the application, handed straight on
      -- exactly as `prelude` does.  The guard is here rather than below the
      -- loop because `Edge` has no `injected` field yet; once it has one, this
      -- branch should go and `prelude`'s `no_feedback` should do the work.
      stdout.putStrLn inc.event.line
      stdout.flush
      runModal o names mk w (Dispatch.Wire.level inc.event) fout dev
      else
      let (fin', eds) := Dispatch.Wire.edges fin inc.event
      -- A line that names no position is the failure that hides, same as in
      -- `runQuartz`: say so rather than looking dead.
      if o.monitor && eds.isEmpty then
        stdout.putStrLn (Monitor.dropLine trimmed)
      let code := Monitor.codeOf inc.event
      let back := mk o.cfg
      let mut w := w
      let mut fout := fout
      for (dir, c) in eds do
        let (w', eff) := Dispatch.dispatch back w dir c inc.time
        let (fout', out) := Dispatch.Wire.many names fout eff
        if o.monitor then
          stdout.putStrLn (Dispatch.Wire.Row.line
            { edge := { dir := dir, code := c, mods := w'.mods }
              code := code, state := w'.backend.1, effects := eff })
          for l in out.mon do stdout.putStrLn l
          if (Dispatch.Wire.entered? eff).isSome then
            stdout.putStrLn (Monitor.stateLine w'.backend.1)
        for qe in out.posts do stdout.putStrLn qe.line
        for l in out.loud do stderr.putStrLn l
        w := w'
        fout := fout'
      stdout.flush
      runModal o names mk w fin' fout dev

/-- Read a kanata config and say what it contains, or say why not.

`none` means the message is already printed and the exit code is 2.  The load
happens before any monitor header, so a config that does not parse cannot leave
a driver looking at a header over a run loop that will never answer.

`Kanata.parse` and not `parseStrict`: a form this evaluator refuses still leaves
a usable config, and refusing the file over one of them would be refusing the
whole layout over a binding.  A `.error` here is a genuine syntax or width
problem, which leniency should not swallow. -/
def loadKanata (path : System.FilePath) : IO (Option ((n : Nat) × Kanata.Cfg n)) := do
  let src? ←
    try
      pure (some (← IO.FS.readFile path))
    catch e =>
      IO.eprintln s!"capslockmode: cannot read {path}: {e}"
      pure none
  match src? with
  | none => return none
  | some src =>
    match Kanata.parse src with
    | .error e =>
      IO.eprintln s!"capslockmode: {path}: {e}"
      return none
    | .ok sized =>
      for l in Dispatch.Wire.banner (toString path) sized.1
                 (sized.2.layers.map (·.name)) sized.2.blocked do
        IO.eprintln l
      return some sized

/-- The filter: one line in, zero or more lines out. -/
partial def runFilter (o : Opts) (st : State) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr
  let line ← stdin.getLine
  if line.isEmpty then return ()          -- EOF
  if line.trim.startsWith "toggle" then
    match line.trim.splitOn " " with
    | ["toggle", k] =>
      match parseToggle? k with
      | some pk =>
        let o := { o with cfg := { o.cfg with toggleKey := pk } }
        stdout.putStrLn s!"# toggle: {pk.name}"
        if o.monitor then stdout.putStrLn (Monitor.stateLine o.cfg.start)
        stdout.flush
        runFilter o o.cfg.start
      | none =>
        stderr.putStrLn s!"# unknown key: {k}"
        runFilter o st
    | _ =>
      stderr.putStrLn s!"# usage: toggle <key>"
      runFilter o st
  else match parseLine? line with
  | none =>
    stderr.putStrLn s!"# ignored: {line.trim}"
    if o.monitor then
      stdout.putStrLn (Monitor.dropLine line.trim)
      stdout.flush
    runFilter o st
  | some .ignore => runFilter o st
  | some .query =>
    stdout.putStrLn s!"# mode: {st.describe}"
    stdout.flush
    runFilter o st
  | some .reset =>
    stdout.putStrLn "# reset"
    stdout.flush
    runFilter o o.cfg.start
  | some (.event ev) =>
    let (st', out) := step o.cfg st ev
    if o.monitor then
      stdout.putStrLn (Monitor.line { input := ev, state := st', out := out })
      if st'.describe != st.describe then
        stdout.putStrLn (Monitor.stateLine st')
    for e in out do
      stdout.putStrLn e.line
    stdout.flush
    if o.verbose && st'.mode != st.mode then
      stderr.putStrLn s!"# mode: {st'.describe}"
    runFilter o st'

/-- Run a script against a text field and print the buffer. -/
def demo (o : Opts) (script : String) : IO Unit := do
  let evs := parseScript script
  let (st, out) := run o.cfg o.cfg.start evs
  let sc := (Screen.ofText o.text).applyAll out
  IO.println s!"script : {script}"
  IO.println s!"keys   : {renderEvents out}"
  IO.println s!"mode   : {st.describe}"
  IO.println "buffer :"
  for l in sc.render.splitOn "\n" do
    IO.println s!"  {l}"

/-- Run a script one key at a time, showing the machine's reasoning. -/
def trace (o : Opts) (script : String) : IO Unit := do
  let evs := parseScript script
  let mut st := o.cfg.start
  let mut sc := Screen.ofText o.text
  IO.println s!"{pad "key" 8}{pad "mode" 14}emitted"
  IO.println (String.ofList (List.replicate 60 '-'))
  for ev in evs do
    let (st', out) := step o.cfg st ev
    sc := sc.applyAll out
    if ev.dir == .down then
      IO.println (Monitor.row (Monitor.inputName ev) st' out)
    st := st'
  IO.println ""
  for l in sc.render.splitOn "\n" do
    IO.println s!"  {l}"

def keys (o : Opts) : IO Unit := do
  IO.println "CapslockMode key map (generated by running each command through the machine)"
  IO.println ""
  IO.println s!"  {pad "keys" 8}{pad "emitted keystrokes" 34}what it does"
  IO.println s!"  {String.ofList (List.replicate 74 '-')}"
  for (script, what) in keyTable do
    let evs := parseScript script
    let (_, out) := run o.cfg { mode := .normal } evs
    let emitted := renderEvents out
    let emitted := if emitted.isEmpty then "(mode change only)" else emitted
    IO.println s!"  {pad script 8}{pad emitted 34}{what}"
  IO.println ""
  IO.println s!"  Caps Lock toggles normal/insert. Esc always returns to normal mode."
  IO.println s!"  platform: {o.cfg.platform.name}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["--help"] | ["-h"] | ["help"] => IO.println usage; return 0
  | ["--version"] | ["-v"] => IO.println "capslockmode 0.1.0"; return 0
  | cmd :: rest =>
    match parseOpts rest {} with
    | .error e => IO.eprintln s!"capslockmode: {e}"; return 2
    | .ok (o, positional) =>
      match optsError? o cmd with
      | some e => IO.eprintln s!"capslockmode: {e}"; return 2
      | none =>
      match cmd, positional with
      | "run", _ =>
        -- The config is read before anything is printed, so that a file which
        -- does not parse exits rather than leaving a driver watching a header.
        let kan? ← match o.kanata with
          | none => pure (some none)
          | some path => (Option.map some) <$> loadKanata path
        match kan? with
        | none => return 2
        | some kan =>
        if o.monitor then
          IO.println Monitor.headerLine
          IO.println (Monitor.stateLine o.cfg.start)
        match kan with
        | some ⟨_, kcfg⟩ =>
          -- `Kanata.Sized` is a sigma, but `modal`'s result type does not
          -- mention the width -- so destructuring here erases it and `runModal`
          -- is an ordinary non-dependent loop.
          runModal o (kcfg.layers.map (·.name))
            (fun c => Dispatch.modal c [.insert] kcfg)
            { backend := (o.cfg.start, {}) } {} {}
        | none =>
          match o.wire with
          | .raw => runFilter o o.cfg.start
          | .quartz => runQuartz o o.cfg.start {} {}
        return 0
      | "keys", _ => keys o; return 0
      | "demo", [s] => demo o s; return 0
      | "trace", [s] => trace o s; return 0
      | "demo", _ | "trace", _ =>
        IO.eprintln "capslockmode: expected exactly one script argument"; return 2
      | c, _ => IO.eprintln s!"capslockmode: unknown command '{c}'\n\n{usage}"; return 2
