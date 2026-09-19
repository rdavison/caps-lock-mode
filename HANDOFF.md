# Handoff

Where CapslockMode is, what is actually verified, and what it costs to pick up.

Branch `claude/capslockmode-vi-keyboard-fmlaeb`, open as
[PR #1](https://github.com/rdavison/caps-lock-mode/pull/1). Three commits on top
of the initial one: the machine and its proofs, the macOS backend, a CI fix.

## What exists

About 2,900 lines of Lean, a Python driver, a Swift driver, and packaging.

| Piece | File | State |
| --- | --- | --- |
| The modal machine | `CapslockMode/Machine.lean` | Done. `step` is the whole behaviour |
| Keys, chords, events | `CapslockMode/Key.lean` | Done |
| Intents and platforms | `CapslockMode/Platform.lean` | Two platforms: `pc`, `mac` |
| No-stuck-keys | `CapslockMode/Balance.lean` | 25 theorems |
| The promises | `CapslockMode/Invariants.lean` | 37 theorems |
| macOS event model | `CapslockMode/Backend/Quartz.lean` | 12 theorems |
| Wire formats, key notation | `CapslockMode/Protocol.lean` | Two wires: `raw`, `quartz` |
| Model text field | `CapslockMode/Screen.lean` | Demo and test oracle only |
| CLI | `Main.lean` | `run`, `demo`, `trace`, `keys` |
| Linux driver | `drivers/evdev_bridge.py` | Written, **never run** |
| macOS driver | `drivers/quartz_bridge.swift` | Compiles clean; **never run** |
| Packaging | `packaging/homebrew/`, `.github/workflows/release.yml` | Blocked on a tap repo |

## Verification status — read this before trusting anything

Three different levels, and the difference matters.

**Proved.** 21 headline theorems, checked sorry-free by
`scripts/check-axioms.sh`; they depend only on Lean's three standard axioms.
The big ones: `step_balanced` (nothing synthesised leaves a key held),
`up_only_if_pressed` and `down_remembered` (releases match presses across mode
switches), `run_insert_transparent` (switched off, output is input),
`esc_resets` and `capsLock_twice` (silent routes back to a known state),
`step_count_le` and `command_repeats_le` (no key storms), `no_feedback`, and the
five Quartz theorems.

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

**The Swift driver compiles.** First build on macOS 26.5.2 / arm64 with Swift
6.3.3 (Command Line Tools, no full Xcode), 2026-09-19:

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

Still unrun: no event tap has ever been installed, and no keystroke has ever
been through it.

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
* **A Developer ID ($99/yr), or not.** The release signs ad-hoc, so macOS treats
  every upgrade as a new program and the Accessibility grant has to be removed
  and re-added after each `brew upgrade`. Notarisation would fix that and is a
  self-contained change: a signing identity in CI and a notarytool step.

**Code, roughly in order of value:**

* **Run the drivers.** The single highest-value next step, on either platform.
* **Key repeat on macOS.** The tap swallows the original event and re-posts a
  replacement, and posted events do not auto-repeat, so holding a key types it
  once. The fix is a synchronous answer inside the tap callback (returning the
  original event when the machine would pass it through), against the tap's
  deadline — which is also why it was not done this way to begin with.
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
