# CapslockMode

Turn your keyboard into a modal, vi-like input system, switched on and off with
the Caps Lock key.

Tap Caps Lock and `hjkl` move the cursor, `dd` deletes a line, `ciw` changes a
word — in your browser, your terminal, your IDE, your chat window. Tap it again
and your keyboard is an ordinary keyboard.

CapslockMode does not know anything about the application you are typing into.
It compiles vi commands into the plain editing keystrokes every text widget
already understands:

```
$ capslockmode keys
  keys    emitted keystrokes                what it does
  --------------------------------------------------------------------------
  w       ctrl+right                        next word
  dd      home shift+down del               delete line
  3dd     home shift+down shift+down shift+down del delete 3 lines
  diw     ctrl+left ctrl+shift+right del    delete inner word
  cw      ctrl+shift+right del              change word
  yy      home shift+down ctrl+c home       yank line
  5G      ctrl+home down down down down     line 5
```

It is written in Lean 4 with Mathlib, which is the other half of the point: the
properties that make a keyboard layer safe to leave running all day are
*proved*, not tested. See [What is proved](#what-is-proved).

Two platforms are supported, and they are genuinely different: `dd` on a Mac is
`Cmd+Left, Shift+Down, Delete`, because `Home` does nothing useful in a Mac text
field. See [Platforms and backends](#platforms-and-backends).

## Build

Needs [elan](https://github.com/leanprover/elan) (the Lean toolchain manager).
The pinned toolchain and Mathlib revision are checked in.

```sh
lake exe cache get      # optional: prebuilt Mathlib, much faster
lake build              # builds the library, the binary, and runs the tests
```

`lake build` compiles `Tests/Basic.lean`, whose `#guard` assertions are the test
suite; a failing test is a failing build.

```sh
./scripts/selftest.sh         # end-to-end check of the binary over its wire protocol
./scripts/selftest-quartz.sh  # the same, over the macOS wire
./scripts/check-axioms.sh     # confirm no theorem leans on a `sorry`
```

The macOS driver (`drivers/quartz_bridge.swift`) has **not been run on real
hardware**: it is written against the documented CoreGraphics API, and the Lean
side it talks to is tested, but expect to fix something the first time.

## Try it without touching your keyboard

`demo` types a vim-style key script into a sample buffer and shows the result:

```
$ capslockmode demo --start-normal --text 'alpha beta
gamma delta' '2wdw'
script : 2wdw
keys   : ctrl+right ctrl+right ctrl+shift+right del
mode   : normal
buffer :
  alpha beta‸
  gamma delta
```

`trace` shows the machine thinking, one key at a time:

```
$ capslockmode trace --start-normal 'ciwCAT<Esc>'
key     mode          emitted
------------------------------------------------------------
c       normal c
i       normal ci
w       insert        ctrl+left ctrl+shift+right del
C       insert        C
A       insert        A
T       insert        T
esc     normal
```

## Install on macOS

```sh
brew install rdavison/capslockmode/capslockmode
brew services start capslockmode        # not with sudo: an event tap needs your GUI session
```

Then add `capslockmode-quartz` under **System Settings → Privacy & Security →
Accessibility**; the service polls for the permission, so ticking the box is
enough, with no restart. `capslockmode-quartz --check` prints the status and the
exact path to add.

Two things to know:

* The binary is **ad-hoc signed**, so macOS treats each upgrade as a different
  program: after `brew upgrade` you have to remove the Accessibility entry and
  add it back. A Developer ID would fix that; there isn't one yet.
* **Caps Lock cannot be swallowed by an event tap** — the lock state and the LED
  live below it in IOKit — so the service remaps Caps Lock to F18 with `hidutil`
  while it runs and uses F18 as the toggle. `brew services stop` puts it back.
  Pass `--no-remap` to bind something else.

## Wire it to a real keyboard

CapslockMode itself is a filter: keyboard events in on stdin, keyboard events
out on stdout. A small driver does the platform-specific work.

```sh
sudo ./drivers/evdev_bridge.py --binary ./.lake/build/bin/capslockmode --led
```

The driver grabs your keyboard exclusively (so the original keystrokes never
reach applications), feeds every event to `capslockmode run`, and replays the
result through a virtual `uinput` keyboard. `--led` lights the Caps Lock LED
while you are in normal mode. Start with `--dry-run` to watch what it *would*
inject without injecting anything.

The protocol is deliberately boring, so a driver for another platform (a
Karabiner userspace hook on macOS, an `interception-tools` filter, an AutoHotkey
bridge on Windows) is a small program:

```
$ capslockmode run
down caps            ← you press Caps Lock
down d               ← nothing is emitted yet, `d` is an operator
down d
down home            ← ... and here is `dd`
up home
down shift
down down
up down
up shift
down del
up del
```

## Platforms and backends

The key map is written in *intents* — "next word", "copy", "start of line" — and
a `Platform` lowers each one to a chord. The same `dd` compiles differently:

| Command | PC | macOS |
| --- | --- | --- |
| `w` | `Ctrl+Right` | `Option+Right` |
| `0` / `$` | `Home` / `End` | `Cmd+Left` / `Cmd+Right` |
| `yy` | `Home Shift+Down Ctrl+C Home` | `Cmd+Left Shift+Down Cmd+C Cmd+Left` |
| `u` / `Ctrl+R` | `Ctrl+Z` / `Ctrl+Y` | `Cmd+Z` / `Cmd+Shift+Z` |
| `n` | `F3` | `Cmd+G` |

`capslockmode keys --platform mac` prints the whole table.

The two backends also disagree about what an event *is*, which is the more
interesting half:

| | Linux evdev | macOS Quartz |
| --- | --- | --- |
| Modifiers | their own press/release events | a flags bitmask on each event |
| A chord costs | up to 10 events | exactly 2 (`Quartz.encode_length`) |
| Modifier state arrives as | transitions | whole masks, diffed by the client |
| What keeps it honest | `Balanced`: the kernel drops unmatched releases | `flags_settle`: the flag state must return to empty |
| Loop risk | none: uinput is a separate device | the tap sees its own posts (`no_feedback`) |

`--wire quartz` makes `run` speak virtual keycodes and flag masks, so the macOS
driver needs no key table of its own:

```
$ capslockmode run --wire quartz --platform mac
down 57            ← Caps Lock (kVK_CapsLock)
down 2             ← `d`
down 2             ← `d` again
key down 123 command     ← Cmd+Left
key up 123 command
key down 125 shift       ← Shift+Down
key up 125 shift
key down 117 -           ← Delete
key up 117 -
```

## Key map

Motions `h j k l w b e 0 ^ $ { } gg G <C-f> <C-b>`, with counts (`3j`, `d2w`).
Operators `d c y > <`, doubled for linewise (`dd`, `cc`, `yy`, `>>`, `<<`), plus
the `iw`/`aw` text objects. Edits `x X D C J s S r p P u <C-r> .`. Entering
insert with `i I a A o O`. Visual mode with `v` and `V`. `/ n N` for search.
`Esc` returns to normal mode from anywhere.

`capslockmode keys` prints the full table, generated by running each command
through the machine — so it cannot drift from the implementation.

Unbound chords that hold Ctrl, Alt or Super are passed through, so `Ctrl+S`
still saves while you are in normal mode.

## What is proved

The proofs live in [`CapslockMode/Balance.lean`](CapslockMode/Balance.lean) and
[`CapslockMode/Invariants.lean`](CapslockMode/Invariants.lean).

| Theorem | In English |
| --- | --- |
| `step_balanced` | Every stream of events CapslockMode synthesises is *balanced*: each key it presses it releases, and it never presses a key that is already down. This is the bug that makes a remapper unusable — a stuck `Ctrl` turns every keystroke into a shortcut — and it cannot happen here. |
| `up_only_if_pressed` | A key release is forwarded only for a key whose press was forwarded. Applications never see a release for a key they never saw pressed. |
| `down_remembered` | A press that *is* forwarded is recorded, so its release will be forwarded too — even if you hit Caps Lock with a finger still down. |
| `run_insert_transparent` | With CapslockMode off, the output is exactly the input. Not "almost": the same events, in the same order. |
| `capsLock_twice` | Two taps of Caps Lock emit nothing, discard any half-typed command, and put you back in the mode you started in. `SettledMode.toggle_involutive` states the same thing as `Function.Involutive`. |
| `esc_resets` | From any state, Esc returns to normal mode with an empty count and no pending operator, and types nothing. |
| `step_count_le`, `command_repeats_le` | A count is clamped to `maxCount` and no key press repeats its keystrokes more than that, so a slipped `99999dd` cannot become a storm of synthetic events. |
| `Chord.emit_length_le` | A chord is at most ten events, which together with the above bounds the work one key press can cause. |
| `operator_progress`, `textObj_progress` | A half-typed command always resolves: `d` can wait for a motion or upgrade to `diw`, but it can never keep swallowing keys. |
| `no_feedback` | An event CapslockMode injected itself is passed straight through, never re-read as a command. macOS event taps and Windows hooks both observe their own output, so without this one `dd` could cascade. |
| `Quartz.encode_chord`, `Quartz.encode_length` | On macOS a chord is exactly two events, with the modifiers riding along as flags rather than being pressed and released. |
| `Quartz.flags_settle` | Because the evdev-shaped stream is balanced, the macOS flag state returns to empty after every chord: no command can leave Command set for the next one. |
| `Quartz.chordsOf_encode` | Nothing is lost in translation — a reader of the Quartz stream recovers exactly the chords CapslockMode meant. |

The `Balanced` predicate is the interesting definition. For a physical key `k`,
`net k` counts presses minus releases; a stream is balanced when every prefix
has `net k ∈ {0, 1}` and the whole stream has `net k = 0`. The proof that chords
satisfy it turns on a type distinction: `Key` (the keys a chord can tap) and
`Modifier` are different types, so a chord can never name the same physical key
twice, and `Mods.held_nodup` makes duplicate-freedom of the modifier list
automatic.

A proof containing `sorry` still compiles, so `scripts/check-axioms.sh` prints
what the headline theorems depend on; they use only Lean's three standard
axioms.

Test and proof meet in `Tests/Basic.lean`: `balancedB` is a runtime checker for
the same property, run over the whole key map. If it ever disagrees with the
theorem, one of them is wrong.

## Where vi purists will object

CapslockMode drives a text widget it cannot see, so some commands are
approximations. These are deliberate, and documented here rather than hidden:

* **Word motions** are the editor's `Ctrl+Arrow`, which usually swallows the
  trailing space: `cw` on `alpha beta` gives `beta`, not ` beta`.
* **`aw` and `iw`** are the same motion; there is no way to ask a text widget
  where a word really ends.
* **`.`** replays the *keystrokes* of the last edit, not its meaning, and does
  not capture text typed in insert mode.
* **`V>`** indents the line below as well, because a linewise visual selection
  has to reach into the next line for `d` to remove the line.
* **Linewise commands on the last line** leave an empty line behind, since
  `Shift+Down` has nowhere to go.
* **No registers, marks, macros or `:` commands.** There is nowhere to put
  them: CapslockMode does not own the text.
* **On macOS, holding a key does not repeat it.** The event tap swallows the
  original event and re-posts a replacement, and a posted event does not
  auto-repeat. Fixing it means answering inside the tap callback, against the
  tap's deadline.

## Picking this up

[`HANDOFF.md`](HANDOFF.md) has the current state, what is proved versus tested
versus never run, how to build it where the usual Lean toolchain hosts are
blocked, and the open work.

## Layout

```
CapslockMode/Key.lean         keys, chords, events, and how a chord is played
CapslockMode/Machine.lean     the modal machine: modes, counts, operators, `step`
CapslockMode/Balance.lean     "no stuck keys", defined and proved for chords
CapslockMode/Invariants.lean  the promises the README makes, as theorems
CapslockMode/Platform.lean    intents, and the PC and macOS keystrokes for them
CapslockMode/Backend/Quartz.lean  the macOS event model: flags, keycodes, proofs
CapslockMode/Protocol.lean    the two wire formats and vim key notation
CapslockMode/Screen.lean      a model text field, used by the demo and the tests
CapslockMode/Prelude.lean     the slice of Mathlib this project depends on
Main.lean                     run / demo / trace / keys
Tests/Basic.lean              behavioural tests, checked by `lake build`
Tests/Quartz.lean             every chord the key map plays is nameable to macOS
drivers/evdev_bridge.py       Linux keyboard driver (evdev in, uinput out)
drivers/quartz_bridge.swift   macOS keyboard driver (event tap in, CGEventPost out)
packaging/homebrew/           the formula, published to the tap on release
scripts/selftest.sh           end-to-end test of the binary
scripts/selftest-quartz.sh    the same, over the macOS wire
scripts/check-axioms.sh       confirms the theorems have no holes
HANDOFF.md                    state, verification status, gotchas, open work
```

## Configuration

```
--platform <name>   keystrokes to compile commands into: pc (default) or mac
--wire <name>       protocol spoken by `run`: raw (default) or quartz
--toggle <key>      key that switches modes (default: caps)
--max-count <n>     largest accepted count prefix (default: 100)
--start-normal      start in normal mode
--no-esc            do not let Esc return to normal mode from insert
```

Because the toggle key is configuration rather than a constant, the proofs hold
for whichever key you pick — including the perfectly reasonable choice of
binding it to something other than Caps Lock.
