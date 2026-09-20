/-
CapslockMode: a modal, vi-like keyboard layer that Caps Lock switches on and off.

* `CapslockMode.Key`        keys, chords, events
* `CapslockMode.Machine`    the modal state machine — all of the behaviour
* `CapslockMode.Backend.Hid` a level-based backend: reports, not events
* `CapslockMode.Protocol`   the stdin/stdout wire format and vim key notation
* `CapslockMode.Monitor`    rendering what the machine just did, for a driver to show
* `CapslockMode.Screen`     a model text field, to aim the machine at
* `CapslockMode.Balance`    what "no stuck keys" means, and why chords satisfy it
* `CapslockMode.Invariants` the promises: transparency, escape hatches, bounds
* `CapslockMode.Kanata`     a pure, timeless evaluator for kanata configs
-/
import CapslockMode.Key
import CapslockMode.Machine
import CapslockMode.Backend.Hid
import CapslockMode.Protocol
import CapslockMode.Monitor
import CapslockMode.Screen
import CapslockMode.Balance
import CapslockMode.Invariants
import CapslockMode.Kanata
