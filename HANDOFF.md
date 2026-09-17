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
| macOS driver | `drivers/quartz_bridge.swift` | Written, **never compiled** |
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
container it was written in); `drivers/quartz_bridge.swift` was never even
compiled (no macOS, no Swift). They are written against documented APIs and the
Lean side they talk to is tested, but whoever runs them first should expect to
fix something. Do not let the proofs create false confidence here: the proofs
are about the machine, and the drivers are the part that is unproven.

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

## Orientation

Read in this order: `CapslockMode/Key.lean` for the vocabulary (the `Key` /
`Modifier` split is load-bearing — it is what makes the balance proof possible),
then `Machine.lean` for `step`, then `Balance.lean` for what "no stuck keys"
means. `Invariants.lean` is the list of promises the README makes.

`capslockmode trace --start-normal 'ciwCAT<Esc>'` shows the machine thinking,
one key at a time, and is the fastest way to understand it.
