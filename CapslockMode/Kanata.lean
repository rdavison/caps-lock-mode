/-
# A timeless kanata evaluator

A kanata config, read and resolved, with no clock and no world.

* `CapslockMode.Kanata.Sexp`   the reader, and kanata's three tokenizer traps
* `CapslockMode.Kanata.Keys`   the key-name table, and the bridge to `PhysKey`
* `CapslockMode.Kanata.Config` `Action`, `Layer n`, `Cfg n`, and parsing
* `CapslockMode.Kanata.Layer`  the layer stack and what `_` means
* `CapslockMode.Kanata.Eval`   press, release, run

These modules import **only `CapslockMode.Key`**.  Nothing here pulls in Mathlib,
which is what keeps `CapslockMode/Prelude.lean`'s "the Mathlib surface is visible
in nine lines" property intact -- the reason that file exists at all.

The point of the whole directory is one theorem, `Layer.resolve_identity`: a
config of one layer of all `_` is the identity function.  That is what lets a
mode stop being a branch hardcoded in the machine and become a *binding* to an
evaluator running a particular config.
-/
import CapslockMode.Kanata.Sexp
import CapslockMode.Kanata.Keys
import CapslockMode.Kanata.Config
import CapslockMode.Kanata.Layer
import CapslockMode.Kanata.Eval
