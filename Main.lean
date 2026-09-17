/-
# capslockmode

    capslockmode run            filter keyboard events (the real thing)
    capslockmode demo SCRIPT    type SCRIPT into a text field and show the result
    capslockmode trace SCRIPT   show what each key does, key by key
    capslockmode keys           print the key map (generated from the machine)

`run` speaks the line protocol described in `CapslockMode/Protocol.lean`; a
driver such as `drivers/evdev_bridge.py` connects it to a real keyboard.
-/
import CapslockMode.Machine
import CapslockMode.Protocol
import CapslockMode.Screen

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
  --toggle <key>      key that switches modes (default: caps)
  --max-count <n>     largest accepted count prefix (default: 100)
  --start-normal      start in normal mode instead of insert
  --no-esc            do not let Esc return to normal mode from insert
  --text <string>     buffer contents for demo/trace
  --verbose           log mode changes on stderr

SCRIPTS use vim key notation: 'ihello<Esc>dd', '<Caps>3jdw', '<C-r>'."

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
    -- a name (`caps`, `f18`) or, for `--wire quartz`, a bare virtual keycode
    let byCode : Option PhysKey :=
      if !k.isEmpty && k.all Char.isDigit then Quartz.physOf? (UInt16.ofNat k.toNat!) else none
    match parsePhysKey? k <|> byCode with
    | some pk => parseOpts rest { o with cfg := { o.cfg with toggleKey := pk } }
    | none => .error s!"unknown key: {k}"
  | "--max-count" :: n :: rest =>
    if n.all Char.isDigit && !n.isEmpty then
      parseOpts rest { o with cfg := { o.cfg with maxCount := n.toNat! } }
    else .error s!"not a number: {n}"
  | "--text" :: t :: rest => parseOpts rest { o with text := t }
  | "--start-normal" :: rest => parseOpts rest { o with cfg := { o.cfg with startMode := .normal } }
  | "--no-esc" :: rest => parseOpts rest { o with cfg := { o.cfg with escapeToNormal := false } }
  | "--verbose" :: rest => parseOpts rest { o with verbose := true }
  | a :: rest =>
    if a.startsWith "--" then .error s!"unknown option: {a}"
    else do
      let (o, positional) ← parseOpts rest o
      return (o, a :: positional)

/-- The Quartz filter: keycodes and flag masks in, the same out.

Two flag states are threaded through: `fin` is what the tap last reported, so
that `Quartz.decode` can turn a new mask into the press and release events the
machine expects, and `fout` is what we have told macOS, so that a modifier held
across two keystrokes in insert mode is not dropped.  `Quartz.flags_settle` is
why command mode can share `fout` safely: an emitted command always hands the
flag state back as it found it. -/
partial def runQuartz (o : Opts) (st : State) (fin fout : Quartz.Flags) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr
  let line ← stdin.getLine
  if line.isEmpty then return ()
  let trimmed := line.trim
  if trimmed.isEmpty || trimmed.startsWith "#" then runQuartz o st fin fout
  else if trimmed == "?" then
    stdout.putStrLn s!"# mode: {st.describe}"
    stdout.flush
    runQuartz o st fin fout
  else match Quartz.parseLine? trimmed with
    | none =>
      stderr.putStrLn s!"# ignored: {trimmed}"
      runQuartz o st fin fout
    | some (ev, injected) =>
      let (fin', evs) := Quartz.decode fin injected ev
      let mut st := st
      let mut fout := fout
      for iev in evs do
        let (st', out) := step o.cfg st iev
        st := st'
        for qe in Quartz.encodeFrom fout out do
          stdout.putStrLn qe.line
        fout := Quartz.flagsAfter fout out
      stdout.flush
      runQuartz o st fin' fout

/-- The filter: one line in, zero or more lines out. -/
partial def runFilter (o : Opts) (st : State) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr
  let line ← stdin.getLine
  if line.isEmpty then return ()          -- EOF
  match parseLine? line with
  | none =>
    stderr.putStrLn s!"# ignored: {line.trim}"
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
      let name := match ev.key with
        | .key k => (Chord.name { mods := ev.mods, key := k })
        | k => k.name
      IO.println s!"{pad name 8}{pad st'.describe 14}{renderEvents out}"
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
      match cmd, positional with
      | "run", _ =>
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
