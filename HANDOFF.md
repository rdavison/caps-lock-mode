# Handoff

Where CapslockMode is, what is actually verified, and what it costs to pick up.

Branch `claude/capslockmode-vi-keyboard-fmlaeb`, open as
[PR #1](https://github.com/rdavison/caps-lock-mode/pull/1), pushed and current
as of 2026-11-16. Fifteen commits on top of the initial one: the machine and its
proofs, the macOS backend, a CI fix, the GUI monitor, the HID backend, the
kanata evaluator, the dispatcher, and the .app wrapper that finally made the
monitor launchable.

## What exists

About 2,900 lines of Lean, a Python driver, a Swift driver, and packaging.

| Piece | File | State |
| --- | --- | --- |
| The modal machine | `CapslockMode/Machine.lean` | `prelude` guards, then `step` -- the vi backend |
| Keys, chords, events | `CapslockMode/Key.lean` | Done |
| Intents and platforms | `CapslockMode/Platform.lean` | Two platforms: `pc`, `mac` |
| No-stuck-keys | `CapslockMode/Balance.lean` | 25 theorems |
| The promises | `CapslockMode/Invariants.lean` | 42 theorems |
| macOS event model | `CapslockMode/Backend/Quartz.lean` | 12 theorems |
| HID event model | `CapslockMode/Backend/Hid.lean` | Level-based; 12 theorems |
| kanata evaluator | `CapslockMode/Kanata/` | Pure and timeless; 5 theorems |
| Code ↔ keycode | `CapslockMode/Bridge.lean` | Physical to physical; round trip proved |
| Mode dispatch | `CapslockMode/Dispatch.lean` | Backends as parameters; 19 theorems |
| Wire formats, key notation | `CapslockMode/Protocol.lean` | Two wires: `raw`, `quartz` |
| Monitor rows | `CapslockMode/Monitor.lean` | What a driver displays; pure |
| Model text field | `CapslockMode/Screen.lean` | Demo and test oracle only |
| CLI | `Main.lean` | `run`, `demo`, `trace`, `keys` |
| Linux driver | `drivers/evdev_bridge.py` | Written, **never run** |
| macOS driver | `drivers/quartz_bridge.swift` | **Works on real hardware**; `dd` edits a real field |
| macOS app bundle | `scripts/build-app.sh` | Signed `.app`; the supported way to launch the monitor |
| Packaging | `packaging/homebrew/`, `.github/workflows/release.yml` | Blocked on a tap repo |

## Verification status — read this before trusting anything

Three different levels, and the difference matters.

**Proved.** 50 headline theorems, checked sorry-free by
`scripts/check-axioms.sh`; they depend only on Lean's three standard axioms.
The big ones: `step_balanced` (nothing synthesised leaves a key held),
`up_only_if_pressed` and `down_remembered` (releases match presses across mode
switches), `run_insert_transparent` (switched off, output is input),
`esc_resets` and `capsLock_twice` (silent routes back to a known state),
`step_count_le` and `command_repeats_le` (no key storms), `no_feedback`, the
five Quartz theorems, and `Kanata.resolve_identity` (a kanata config of one
layer of all `_` is the identity function).

**Tested.** `Tests/Basic.lean` and `Tests/Quartz.lean` are `#guard` assertions
run by `lake build` — vi behaviour judged by typing into `Screen`, plus the
check that every chord the key map plays is nameable to macOS.
`scripts/selftest.sh` and `scripts/selftest-quartz.sh` drive the real binary
over both wire protocols.

**Neither.** Both drivers. No keyboard was ever attached to this code, on either
platform. `drivers/evdev_bridge.py` was never run (no `/dev/input` in the
container it was written in). `drivers/quartz_bridge.swift` has now been
compiled — see below — but never run. They are written against documented APIs
and the Lean side they talk to is tested, but whoever runs them first should
expect to fix something. Do not let the proofs create false confidence here: the
proofs are about the machine, and the drivers are the part that is unproven.

**The Swift driver runs.** As of 2026-09-19 it has been run against a real
keyboard on macOS 26.5.2 / arm64: the tap installs, events arrive, the monitor
window shows them being classified, and the modal key can be rebound at runtime
and re-armed. That is the first end-to-end confirmation that the Lean machine
and a real keyboard talk to each other.

Edits confirmed too: `dd` in a real text field deletes the line, so the
`Screen` oracle and a real editor agree.

**Key repeat works**, contrary to what this document and the driver's own
comment claimed for a long time. The old reasoning was that a posted event does
not auto-repeat -- true, but about the wrong link in the chain. Repeat is
generated *upstream* of a session tap, and swallowing an event here tells that
generator nothing, so repeats keep arriving as ordinary events and each is
handled normally. Observed with kanata in the chain; a bare keyboard should
behave the same way for the same reason, but that has not been checked.

**Launching it: use the .app, not the binary.** This is the expensive one, and
what this document used to say about it was wrong in a way that wasted an
afternoon on 2026-11-15.

macOS attributes an Accessibility grant to the *responsible process* in the
launch chain. For a bare executable started from a shell that is the terminal,
not the executable -- so adding the binary under Privacy & Security does nothing
at all. The entry appears in the list, stays ticked, and is inert, and nothing
anywhere reports a problem. The old advice here, "launch it from your own
terminal", described the mechanism correctly and then drew the wrong conclusion
from it: your own terminal is not enough, because your own terminal is the
process being credited.

There is a second trap underneath that one, and it is worth checking first
because it is invisible. `swiftc` leaves a *linker-signed* signature
(`flags=0x20002(adhoc,linker-signed)`), and TCC will not bind a persistent grant
to one at all. `codesign -f -s -` replaces it with a plain ad-hoc signature
(`flags=0x2`). Run `codesign -dv` and read the flags before concluding anything
about a grant that will not stick.

So the supported launch is `scripts/build-app.sh`, which assembles
`.lake/build/CapslockMode.app`: the driver, the Lean binary copied in beside it
(copied, not linked -- codesign would follow a hard link back into `.lake` and
re-sign the build output in place), an Info.plist with a stable bundle
identifier, signed nested-executable-first and verified with `codesign --verify
--deep --strict`. Launched with `open`, the app is its own responsible process,
so pressing Start raises the system prompt and macOS adds the entry itself. No
path is ever typed by hand, which is the step that kept going wrong.

Granting the app also keeps the grant where it belongs. The other thing that
works -- granting Terminal.app -- hands the same power to everything you ever
run from a shell.

The bundle is still ad-hoc signed, so its identity still moves on every rebuild.
`build-app.sh` recompiles only when the source actually changed, and says plainly
when the identity shifted under a live grant.

**The monitor can stop kanata.** A switch in the window reads the daemon's state
and stops or starts it, which matters because kanata sits below the tap: while
it runs, the codes in the window are the ones *it* produced, not the keys that
were pressed. Why it is not simply a `kill`: Homebrew installs kanata as a
LaunchDaemon running as root with `KeepAlive` set, so killing the process only
makes launchd start it again. `launchctl bootout` is the mechanism; in the
`system` domain it needs root, so the toggle goes through osascript's
authorisation dialog, and the password is typed into the system dialog and never
passes through the driver. State is read with `pgrep` rather than from `brew
services`, which reports the job as `none` while it is plainly running.

It also compiles clean. First build, same machine, same day:

```sh
swiftc -O drivers/quartz_bridge.swift -o .lake/build/bin/capslockmode-quartz
```

Zero errors, zero warnings, unchanged source. The anticipated Swift 6
strict-concurrency objections to the file's global mutable state (`var
eventTap`, globals touched from the `CGEventTapCallBack` C function pointer and
the detached `readLoop` thread) did not appear: swiftc still defaults a
single-file build to the Swift 5 language mode. If that default ever moves, or
someone passes `-swift-version 6`, those globals are where it will break.
`otool -L` shows only `/usr/lib` and `/System` links, so it passes the gate in
`release.yml`. `--check` correctly reports `not trusted` and exits 1.

`scripts/monitor.sh` was the original launcher and is now superseded by
`build-app.sh`. Everything it says about rebuilds and code identity is right,
and its rebuild-only-when-changed logic is where `build-app.sh` got it from --
but its Accessibility instructions tell you to add the bare binary, which cannot
work, and it has not been updated.

## Building it somewhere new

This is the part that costs hours to rediscover, because the usual route does
not work behind a restrictive egress policy.

The normal route is `elan` + `lake exe cache get`. That needs
`release.lean-lang.org` (toolchains), `reservoir.lean-lang.org` (package name
resolution) and the Mathlib cache endpoint. If those are blocked but
`github.com` is not, here is what works:

1. **elan** from its GitHub release tarball
   (`github.com/leanprover/elan/releases/download/v4.1.2/elan-x86_64-unknown-linux-gnu.tar.gz`),
   installed with `--default-toolchain none`.
2. **The toolchain by hand.** `elan toolchain install` hits blocked hosts, so
   download `lean-4.34.0-linux.tar.zst` from the `leanprover/lean4` GitHub
   release, decompress it (`pip install zstandard` if `zstd` is missing) and
   extract it to `~/.elan/toolchains/leanprover--lean4---v4.34.0`. elan then
   finds it by name.
3. **Dependencies without Reservoir.** `lake update` resolves package *names*
   through Reservoir. Instead, `lake-manifest.json` in this repo is written by
   hand: it pins Mathlib (`v4.34.0`, rev `5ed29652`) plus its eight transitive
   dependencies at the exact revisions from Mathlib's own manifest, each with a
   git URL. Clone each into `.lake/packages/<name>` (shallow fetch of the
   specific rev works on GitHub) and `lake build` proceeds entirely offline.
4. **Mathlib from source**, if the cache is unreachable: only the import closure
   of `CapslockMode/Prelude.lean` is needed — 848 modules, about 15 minutes on
   4 cores. That file exists precisely to keep the Mathlib surface small and
   visible in one place. Adding an import there can be expensive; check the
   closure first.

On a normal machine with open network, none of this applies: `lake exe cache
get && lake build`.

## Gotchas already paid for

Lean 4.34 specifics that cost time here:

* `meta` is a keyword (the module system), so it cannot name a constructor or a
  field — the Super/Command modifier is called `super`.
* `Mod` collides with the core `Mod` class; the modifier type is `Modifier`.
* `String.take` / `drop` / `get` return `String.Slice` now, and `List.asString`
  is `String.ofList`.
* **Do not `deriving BEq`** alongside `DecidableEq`: the derived instance is not
  known lawful, so `beq_self_eq_true` fails and `simp` cannot discharge
  `x == x`. Letting `==` come from `DecidableEq` fixes it. This cost a round of
  broken proofs.
* A `/-! ... -/` module comment inside an inductive body breaks the constructor
  list; use `--`.
* A doc comment can only precede a declaration, so `#guard` cannot have one.

**The proofs in `Invariants.lean` are tactic-brittle.** `command_count_le`,
`command_repeats_le` and the progress theorems work by `repeat' split` over
every branch of the key map, then sequential `all_goals try ...` passes.
Changing the *shape* of `command` — adding an argument to `motion`, adding an
`if` inside a response — can leave goals unsplit. When that happens the fix is
usually another targeted pass (`cases hmotion : motion ...`) rather than
rethinking the proof. Budget for it when touching the key map, and note the
pattern of proving a `@[simp]` lemma once (`applyOver_pending`) instead of
unfolding a helper inside a big bash.

## Open work

**Needs you, not code:**

* **The Homebrew tap.** A tap repo must be named `homebrew-*`, so it cannot live
  in this repo. Create `rdavison/homebrew-capslockmode`, add a write token as
  the `TAP_TOKEN` secret, then uncomment the push step at the end of
  `.github/workflows/release.yml`. Until then the formula is published as a
  build artifact to copy across by hand.
* **A Developer ID ($99/yr): decided, and the answer is no.** Not publishing
  this for now (decided 2026-11-16), so the ad-hoc signature stays and its cost
  stays with it: every rebuild is a new code identity, and a grant made against
  the old one is dead rather than merely stale -- it has to be removed and
  re-added, never re-ticked. Revisit only if this is ever distributed.
  Notarisation would be a self-contained change: a signing identity in CI plus a
  notarytool step.

**Code, roughly in order of value:**

* **Fix `scripts/monitor.sh`, or delete it.** It still prints instructions to
  add the bare binary to Accessibility. That cannot work, for the reason in the
  verification section, and it is the most expensive wrong sentence in this
  repository.
* **Run the Linux driver.** `drivers/evdev_bridge.py` has still never been run.
  The macOS side is done (see above), so this is what is left of "run the
  drivers", and it is still the highest-value unknown on that platform.
* **Check key repeat without an upstream remapper.** It works with kanata in
  the chain (see above). The mechanism says a bare keyboard should be the same,
  since the window server's repeat generator also sits above a session tap, but
  nobody has run it that way.
* **More backends.** Two exist (`Platform.pc`/evdev and `Platform.mac`/Quartz).
  The value of a third is not coverage — it is that each API forces you to model
  something the others hide:

  | API | What it would make you model |
  | --- | --- |
  | Windows `WH_KEYBOARD_LL` + `SendInput` | `LLKHF_INJECTED` marking (loop prevention, already half-done via `no_feedback`), the extended-key flag, the hook deadline |
  | Wayland `wl_keyboard` | `enter`/`leave`: focus loss is the canonical stuck-modifier bug, and "on leave, release everything" is a recovery obligation worth proving |
  | Terminal: legacy vs Kitty `CSI u` | A *lossy* target — no key-up, no Caps Lock, `Ctrl+I == Tab`, ambiguous `Esc`. Supports a genuine impossibility result (the legacy encoding is not injective, so no faithful driver exists), and needs no privileges, so it is the one backend that could ship a runnable demo |
  | USB HID boot reports | Level-based rather than edge-based: 8-byte state *snapshots*, so the model is a `diff` of consecutive reports plus a round-trip proof, with a hard 6-key rollover bound |

  The seam they would plug into already exists: a backend is a pair of pure
  functions (`encode` out, `decode` in) plus proof obligations, exactly as
  `Backend/Quartz.lean` is laid out.
* **Known vi differences**, listed in the README: word motions swallow the
  trailing space, `aw` and `iw` are the same motion, `.` replays keystrokes
  rather than meaning, `V>` indents the following line too, linewise commands on
  the last line leave an empty line. Each is a deliberate compromise of driving
  a text widget you cannot see; revisit only with a specific editor in mind.

## The HID backend, and what a probe settled

`CapslockMode/Backend/Hid.lean` is a third backend: **level** based, where evdev
and Quartz are edge based. A HID keyboard does not report events, it reports a
snapshot of everything held, and a reader recovers events by diffing
consecutive snapshots. Nothing in a report says which key moved.

That difference is the reason to have it. `Balanced` buys `flags_settle` on
Quartz, because the risk there is a modifier flag drifting. Here the same
obligation buys `reports_settle` *and* `apply_nodup`: a level-based wire cannot
express "the same key held twice", so duplicate-freedom is a well-formedness
condition on the protocol rather than a tidiness property. Six theorems, all
sorry-free; `scripts/check-axioms.sh` covered 27 rather than 21 after it landed,
and 32 once the kanata evaluator was added (see below).

Two corrections to what this document used to say about it:

* **There is no six-key rollover bound.** The old note assumed the 8-byte boot
  protocol. The virtual device this targets carries `uint16_t keys[32]`, so the
  bound does not exist. A boot-protocol backend would need one and would be a
  different module.
* **Caps Lock is an ordinary usage here.** That is the practical payoff: an
  event tap cannot swallow Caps Lock, because the lock state and LED live in
  IOKit below it, which is why the Quartz driver remaps to F18 with `hidutil`.
  A seized HID device has no such layer above it.

### What a driver would cost, measured rather than guessed

Verified on a machine running kanata (which re-emits through
`org.pqrs.Karabiner-DriverKit-VirtualHIDDevice`):

* **Injection** goes through the Karabiner daemon over a UNIX **datagram**
  socket under `/Library/Application Support/org.pqrs/tmp/rootonly/`. That
  directory is `drwx------ root:wheel`, so **a client must run as root** -- the
  enforcement is filesystem, not entitlement. The client itself needs no
  entitlement and no signing, so the `otool -L` self-containment gate survives:
  it is `socket`/`sendto` on libSystem plus IOKit.
* The installed package version, not the `driver_version`, picks the protocol.
  Here that is package **v6.2.0 / client protocol 5**; upstream has moved to 7
  with a different socket layout and shifted enum ordinals, and there is no
  negotiation. A hand-rolled client must pin and assert the version or it fails
  silently into a log only root can read.
* **Reading is a separate mechanism** -- `IOHIDDeviceOpen` with
  `kIOHIDOptionsTypeSeizeDevice` -- needing Input Monitoring *and*
  Accessibility, both TCC-pinned to the binary path.

### Seizure is opaque, and that is a dead end worth knowing

`drivers/hid_listen.swift` is a diagnostic that opens keyboards with
`kIOHIDOptionsTypeNone` -- observing, never grabbing. The question was whether a
passive observer can watch a device some other process has seized, which would
let a driver see input *before* kanata rewrote it.

It cannot. `IOHIDDeviceOpen` returns `kIOReturnExclusiveAccess` (`0xe00002c5`).
A seized device is invisible even to a passive reader; only the process holding
it sees those keys. So there is no way to observe pre-kanata input while kanata
runs, and "watch what the layer below sees" is not an option -- the only way to
see those events is to stop that process and seize the device yourself, at which
point you *are* that layer and inherit everything it was doing.

Keep the probe. It is the fastest way to answer "is something holding the
keyboard, and which device", and it cannot break anything.

## The kanata evaluator, and the one theorem it exists for

`CapslockMode/Kanata/` is a pure, timeless evaluator for kanata configs: an
s-expression reader, a key-name table, `defsrc` / `deflayer` / `defalias` /
`defcfg`, the layer stack, and press/release. It imports **only**
`CapslockMode/Key.lean` -- no Mathlib, so `Prelude.lean`'s "the Mathlib surface
is visible in nine lines" property survives -- and nothing in `Machine.lean`,
`Invariants.lean`, `Balance.lean` or `Backend/` knows it exists yet.

It is there for `Kanata.resolve_identity`: **a config of one layer of all `_`
resolves every position to its `defsrc` key.** That makes the identity config
the identity function as a theorem rather than a coincidence, which is what
would let `insert` stop being a branch hardcoded in `step` and become a mode
*bound* to this evaluator running a particular config. That binding is not
built; only the result it would rest on.

The fixture is the real `~/.config/kanata/kanata.kbd`, embedded verbatim in
`Tests/Fixtures/Kanata.lean` as a raw string, because everything here is pure
and a `#guard` cannot read a file. It parses whole: 72 positions, 14 layers,
all exactly 72 wide.

What it refuses, and why the three reasons are kept apart: **needs a clock**
(`tap-hold`, `one-shot`, `macro`, `defchordsv2`), **needs a world** (`lrld`,
which is perfectly timeless and just re-reads a file), and **unrecognised**,
which is a hard error so a typo is never skipped. The first two are recorded in
`Cfg.blocked` and parsing continues, so the transparency results are about the
real config rather than a trimmed copy; pressing a position that resolves to one
is an error naming the form.

## Modes bound to backends: where this got to, and what is next

The idea: `insert` mode should not be a branch of the machine that passes keys
through. It should be a *binding* -- a mode bound to an evaluator running the
identity config -- so that transparency is a **consequence** rather than a
promise the machine hardcodes.

That now holds, in `CapslockMode/Dispatch.lean`:

```lean
theorem run_identity_transparent (src : Vector Kanata.Code n)
    (w : World (State × Kanata.St)) (cs : List Kanata.Code)
    (hm : w.backend.1.mode = .insert) (hc : ∀ c ∈ cs, c ≠ .capsLock) :
    (run (identity src) w (cs.map fun c => (Dir.down, c))).2
      = cs.map fun c => Effect.emitCode ⟨.down, c⟩
```

It follows from `Kanata.resolve_identity_any`. `Invariants.run_insert_transparent`
is deliberately untouched -- it is a promise the README makes and
`check-axioms.sh` names -- but it is no longer the reason the property holds.

### The shape, and the mistake that shaped it

A backend is a coalgebra passed as a **parameter**:

```lean
abbrev Step (σ : Type) := σ → Edge → Option (σ × List Effect)
def dispatch {σ : Type} (back : Step σ) (w : World σ) (dir : Dir) (c : Kanata.Code) :
    World σ × List Effect
```

`dispatch` names no backend. `vi` and `kanata` are instances; `select` combines
two; `guarded` applies `prelude` as a transformer; `modal` and `viAlone` are
assemblies.

The first attempt had `World` carry a `Backend` enum beside one field per
backend. That was wrong twice over, and both are worth remembering because the
reasoning that produced it is seductive:

* it hardcoded the backend set into the dispatcher's core type, which is the
  opposite of decoupling modes from backends;
* it *manufactured* an invariant. A tag beside the payloads can disagree with
  them, so an agreement predicate had to be proved. Derive the routing from the
  states instead and drift becomes unrepresentable.

The false constraint behind it: `Platform.lean:14-15` says `Platform` is an
enumeration "so that `Config` stays decidable", and that rule is about a
**field**. Function *parameters* never threatened `DecidableEq`. Generalising a
field rule into "no functions anywhere" is what pushed the design toward
enumerating backends.

`Effect.enter` carries only the mode for the same reason: the binding is a
function of the mode, so naming the mode already names the backend.

### What the design turned up

* **`World.through`** is the obligation that replaced the invented one. A
  position no backend claims is passed through, and nobody else accounts for
  that emission -- so the dispatcher keeps its own record, third of a family
  with `State.down` and `Kanata.St.holds`, carrying `up_only_if_through` and
  `down_through_remembered`. Not decoration: an intermediate version emitted a
  bare key-up when a `d` release in normal mode fell out of the bottom.
* **`Step`'s `Option` is load-bearing.** `none` means "not mine". `prelude`'s
  release guard consults `State.down`, so it can only speak for vi; a key-up it
  does not recognise must be handed on, because the evaluator keeps its own
  record. Press a layer key, hit Caps Lock before releasing, and without that
  fallthrough the codes strand.
* **`escapeToNormal` does not survive the binding.** A mode bound to the
  evaluator has no vi affordances, so `Esc` passes through and Caps Lock is the
  only way out.
* **The evaluator is the floor.** `kanata` claims every edge, so when vi is
  bound and declines a position it cannot name (`🔊`), a loaded config is still
  asked. That is deliberate layering -- kanata sits below the layout and does
  not stop because vi is in normal mode -- but it is a choice, not a neutral
  fact.
* **`Dispatch.kanata` keeps its name: considered and declined, 2026-11-16.**
  The name collides twice -- with the daemon, which the monitor can now stop,
  and with `CapslockMode.Kanata`, the config language this evaluates. `layered`
  was the candidate. Left alone because the collision is cheaper than churn in a
  proved module, and because every alternative loses the one fact a reader needs:
  that this evaluates a kanata config. Note while you are here that
  "passthrough" would be an actively *wrong* rename. `kanata` never returns
  `none`; it emits an unknown code unchanged while still claiming the edge,
  which is not the same as declining it into `World.through`.

### Next, in order

1. **Lift `Balanced` through `dispatch`.** `step_balanced` and
   `Kanata.release_undoes_press` both exist; neither has been transported into a
   single statement about an effect list. The transport looks cheap -- a key
   with no image is dropped on *both* its press and its release, because the
   mapping is a function, so filtering preserves balance.
2. **Wire `Main.lean`.** `--kanata <file>` would be the first `IO.FS.readFile`
   in the project; the parser is pure and already takes a `String`.
   `Bridge.ofKeyCode?` / `toKeyCode?` are the seam a driver uses.
3. **Phase 3: timestamps.** `InputEvent` gains `time : Nat := 0`, which is
   additive -- the deriving clauses survive and every construction site keeps
   compiling. That unlocks `tap-hold`, `one-shot` and `defchordsv2`, the three
   forms the evaluator records as blocked. Budget carefully: tap-hold has twelve
   documented variants and `concurrent-tap-hold` changes when timers start. The
   fallback, letting the driver resolve tap-hold and send a decided action,
   stays available.

Known gaps, none of them hidden: `viAlone_down` covers presses only, since on
release the dispatcher genuinely does something `step` does not; `select` is
binary on purpose, because an n-ary version over a heterogeneous list needs
dependent types the deriving would not survive; and the Quartz wire is the only
one wired -- the raw evdev wire has no keycode and needs its own position
mapping.

### Working on this with a fresh context

The phase plan lives at
`~/.claude/plans/actually-make-a-plan-declarative-kurzweil.md`.

Every piece of this was built to the same discipline, and it is worth keeping:

* **No `sorry`, ever.** A theorem that will not land is deleted and reported as
  a gap, never left as a hole.
* **Additive first.** Each phase landed as its own commit, and the proved
  modules were off limits until a step existed whose whole job was to touch them.
* **The behaviour check is mechanical**, not a judgement:

```sh
lake build && ./scripts/selftest.sh && ./scripts/selftest-quartz.sh && ./scripts/check-axioms.sh
printf 'down 57\ndown 2\nup 2\ndown 2\nup 2\n' | .lake/build/bin/capslockmode run --wire quartz --platform mac | md5
# 0240da6b8326956da9329504833087f4 -- unchanged through every phase so far
.lake/build/bin/capslockmode trace --start-normal 'ciwCAT<Esc>' | md5
# c4fb3f6fa122ebb7d317387b6637410c
```

For a refactor that claims to preserve behaviour, diff the theorem *signatures*
between `HEAD` and the working tree rather than reading the diff -- statements
changing is the failure that review misses.

## Dependencies: cslib in, fern deferred

Added 2026-09-19. Both were considered together; only one went in.

### cslib is a dependency now

```toml
[[require]]
name = "cslib"
git = "https://github.com/leanprover/cslib"
rev = "v4.34.0"
```

`leanprover/cslib` — the Lean Computer Science Library, from the `leanprover`
org (not `leanprover-community`, and not any of the several forks that share its
description string). Tag `v4.34.0` is commit `990e65a6`.

It went in because the version story is exact rather than merely workable: that
tag pins toolchain `leanprover/lean4:v4.34.0` **and** Mathlib rev `5ed29652` —
byte-identical to this project's pin. Lake unifies on one Mathlib checkout, the
existing `~/.cache/mathlib` stays valid, and `lake update cslib` left all nine
existing pins untouched (the large `lake-manifest.json` diff is Lake reformatting
the hand-written JSON, not a re-resolution; check it semantically, not by
eyeballing the diff).

Cost is small so far: `Cslib.Foundations.Semantics.LTS.Basic` pulls only **five**
cslib modules. Nothing in `CapslockMode/` imports it yet.

Two things to know before leaning on it:

* **There is no `lake exe cache get` for cslib.** It compiles from source, here
  and in CI. Lake builds only the transitive closure of what you import, so keep
  imports narrow.
* **Its releases track Lean's.** `main` is already on `v4.35.0-rc2`. You are
  pinned to a frozen snapshot; any cslib fix you want later means moving this
  project's toolchain too.

**Do not import cslib from `CapslockMode/Prelude.lean`.** That file exists so the
Mathlib surface is visible in nine lines; cslib is a separate concern and putting
it there destroys the property the file was built for.

**Honest fit assessment, recorded so it is not re-litigated.** cslib is probably
the wrong tool for the machine as it stands. `Cslib.LTS` is
`Tr : State → Label → State → Prop` — relational and possibly nondeterministic.
`step` is a deterministic total function; using `LTS` means wrapping it into a
relation and then proving `LTS.Deterministic` to recover what you started with.
The library's strengths — bisimulation, simulation, HML, CCS, divergence, Büchi
acceptance, ω-executions — are concurrency-theory tools, and this is one process
with no concurrency. For a deterministic total machine, `traces` is every list,
so it says nothing; `Execution` is `List.scanl`. "Event sourcing" over a finite
keystroke log is a `foldl`. The balance and invariant obligations here are list
inductions, which `Prelude.lean`'s nine Mathlib imports already cover.

The place it *would* earn its keep is proving two implementations equivalent —
which is exactly the shape `Quartz.chordsOf_encode` already has, proved without
it. `Simulation` / `TraceEq` / `Deterministic.traceEq_iff_simulationEquiv` is the
vocabulary to reach for if a third backend makes that argument worth generalising.
`OmegaSequence.Temporal` + `Divergence` is the other trigger: a liveness claim
over unbounded input ("hold the modifier forever and the layer never unsticks").

### fern is deferred, and why

`~/code/misc/fern` (**not** `~/code/fern`) is a Lean 4 project whose
`Fern/Frequency.lean` holds the interpreter idea this project was described as an
implementation of. It is not a dependency, for four verified reasons.

**The seam is `chord`, not `step`.** fern's abstraction is stateless:

```lean
def Interpreter (I K : Type) : Type := I → List K
def Interpreter.stream (T : Interpreter I K) (trace : List I) : List K := trace.flatMap T
```

`Machine.step` is `Config → State → InputEvent → State × List OutputEvent`, a
stateful Mealy transducer — strictly more general, and not an instance of
`I → List K` without quotienting the state away. But `Platform.lean:50` is
`chord : Platform → Bool → Intent → Chord`; fix the platform, compose with
`Chord.emit`, and that *is* `Interpreter Intent Event`. fern ships a worked
`normalMode : Interpreter NormalIntent Char` making the same point, and its
`LayoutIndependent` predicate is the direct analogue of a platform-independence
property over `pc`/`mac`. Anyone picking this up should aim at the intent→chord
lowering, not at the machine.

**Three blockers on a Lake `require`:**

| | fern | this project |
| --- | --- | --- |
| Toolchain | `leanprover/lean4:v4.29.0-rc4` | `leanprover/lean4:v4.34.0` |
| Mathlib inputRev | `master` (floating) | `v4.34.0` (tag) |
| Mathlib rev | `6e9770b3` | `5ed29652` |

Lake allows one toolchain and one `mathlib` per graph. fern also uses
`experimental.module` (`module`, `public import`, `@[expose] public section`),
the feature most likely to have shifted across five minor versions.

**The interpreter is unpushed.** fern's `main` is 9 commits ahead of
`origin/main`, and the interpreter arrived in one of them. On `origin/main`,
`Fern/Frequency.lean` is a stub that declares nothing — so a git `require`
against `github.com/rdavison/fern` would fetch a fern with no interpreter in it.
Push first, or the dependency is vapour.

**Why the toolchain did not move down to meet fern.** It was considered and
rejected on arithmetic, not taste. cslib has no `v4.29.0-rc4` tag at all (it
skips rc3 → rc6), and no cslib 4.29 tag pins fern's Mathlib: `v4.29.0-rc3` →
`9b1001cb`, `v4.29.0-rc6` → `5c8398df`, `v4.29.0` → `1a37cd3c`. So a downgrade
would *still* have required re-pinning fern, would have broken the exact cslib
match, and would have meant re-verifying 74 tactic-brittle theorems against older
Lean and Mathlib APIs — including ones this document lists as 4.34-specific
(`String.ofList`, `String.Slice`), which regress on 4.29. Moving fern *up* to
v4.34.0 and pinning its floating Mathlib is the cheaper direction if the
dependency is ever wanted; that work belongs in fern.

## Orientation

Read in this order: `CapslockMode/Key.lean` for the vocabulary (the `Key` /
`Modifier` split is load-bearing — it is what makes the balance proof possible),
then `Machine.lean` for `step`, then `Balance.lean` for what "no stuck keys"
means. `Invariants.lean` is the list of promises the README makes.

`capslockmode trace --start-normal 'ciwCAT<Esc>'` shows the machine thinking,
one key at a time, and is the fastest way to understand it.
