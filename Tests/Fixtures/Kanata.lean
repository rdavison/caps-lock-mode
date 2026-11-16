/-
# The fixture: a kanata config someone actually runs

Copied verbatim from `~/.config/kanata/kanata.kbd` on 2026-09-19.  214 lines,
72 positions, 14 layers, every one of them exactly 72 wide.

It lives in a Lean module and not in a `.kbd` file beside it because everything
in `CapslockMode.Kanata` is pure: a `#guard` cannot read a file.  A checked-in
`.kbd` would be a second copy that no test could look at, and two copies of a
fixture drift.

One `#` of padding is enough for the raw string: the config contains `"` (the
macOS device names) but never the sequence `"#`.
-/

namespace CapslockMode.Kanata.Fixture

/-- The config, byte for byte. -/
def kanataKbd : String := r#"(defcfg
    concurrent-tap-hold yes
    macos-dev-names-include (
      "Apple Internal Keyboard / Trackpad"
      "Richard Davison’s Keyboard"
      "RF R1 8-9Xu"
      "Karabiner DriverKit VirtualHIDKeyboard 1.8.0"
    ))

(defchordsv2
  (lmet rmet) \ 80 first-release ()
)

(defsrc
  esc        f1         f2         f3         f4         f5         f6         f7         f8         f9         f10        f11        f12
  grv        1          2          3          4          5          6          7          8          9          0          -          =          bspc
  tab        q          w          e          r          t          y          u          i          o          p          [          ]          \
  caps       a          s          d          f          g          h          j          k          l          ;          '          ret
  lsft       z          x          c          v          b          n          m          ,          .          /          rsft
  lctl       lalt       lmet                             spc                              rmet       ralt
)

(defalias
  grv-mode  (tap-hold 200 200 grv (layer-while-held layers))
  nths-akl  (layer-switch nths-akl)
  nths-shft (multi lsft (layer-while-held nths-shft))
  asdf-akl  (layer-switch asdf-akl)
  inea-akl  (layer-switch inea-akl)
  inea-shft (multi lsft (layer-while-held inea-shft))
  aien-akl  (layer-switch aien-akl)
  aien-shft (multi lsft (layer-while-held aien-shft))
  mirror    (multi lmet bldn)

  nav       (layer-while-held nav)
  nav-ctl   (multi lctl (layer-while-held nav-ctl))
  cap       (tap-hold 200 200 caps lctl)
  win       (layer-while-held win)
  win-shift (multi lsft (layer-while-held win))
  rect      (one-shot 5000 (layer-while-held rect))
  rect-shft (layer-while-held rect-shft)

  s-left    (multi lsft left)
  s-rght    (multi lsft rght)
  s-up      (multi lsft up)
  s-down    (multi lsft down)

  cmd       (multi lmet (layer-while-held cmd-qwerty))
  ctl       (multi lctl (layer-while-held cmd-qwerty))
  shft      (multi lsft (layer-while-held aien-shft))

  notif     (multi lctl lalt n)
  next      (multi lmet lsft ])
  prev      (multi lmet lsft [)
  opt-left  (multi lalt left)
  opt-right (multi lalt rght)
  opt-bspc  (multi lalt bspc)
  opt-del   (multi lalt del)
  cmd-left  (multi lmet left)
  cmd-right (multi lmet rght)
  cmd-bspc  (multi lmet bspc)
  lchev     (macro \ S-, 100 spc 100 bspc)
  rchev     (macro \ S-. 100 spc 100 bspc)
  lt        S-,
  gt        S-.

  win-max   (multi lctl lalt ret)  ;; maximize
  win-l2    (multi lctl lalt left) ;; left half
  win-r2    (multi lctl lalt rght) ;; right half
  win-c2    (multi lctl lalt q)    ;; center half
  win-t2    (multi lctl lalt up)   ;; top half
  win-b2    (multi lctl lalt down) ;; bottom half
  win-tl4   (multi lctl lalt u)    ;; top left quarter
  win-tr4   (multi lctl lalt i)    ;; top right quarter
  win-bl4   (multi lctl lalt j)    ;; bottom left quarter
  win-br4   (multi lctl lalt k)    ;; bottom right quarter
  win-frst3 (multi lctl lalt d)    ;; first third
  win-cntr3 (multi lctl lalt f)    ;; center third
  win-last3 (multi lctl lalt g)    ;; last third
  win-fst23 (multi lctl lalt e)    ;; first two thirds
  win-ctr23 (multi lctl lalt r)    ;; center two thirds
  win-lst23 (multi lctl lalt t)    ;; last two thirds
)

;; -------------------------------------------------------------------------
;; BASE LAYERS (Updated bottom row to use @cmd)
;; -------------------------------------------------------------------------

(deflayer aien-akl
  esc        🔅         🔆         ✗          ✗          ✗          ✗          ◀◀         ▶⏸         ▶▶         🔇         🔉         🔊
  @grv-mode  1          2          3          4          5          6          7          8          9          0          [          ]          bspc
  tab        /          u          o          y          j          k          d          l          c          w          x          =          \
  @ctl       a          i          e          n          p          m          h          t          s          r          -          ret
  @aien-shft ,          ;          '          .          q          b          f          g          v          z          @aien-shft
  lalt       @cmd       @nav                             spc                              @nav       rmet
)

(deflayer aien-shft
  esc        🔅         🔆         ✗          ✗          ✗          ✗          ◀◀         ▶⏸         ▶▶         🔇         🔉         🔊
  _          _          _          _          _          _          _          _          _          _          _          _          _          _
  _          ,          _          _          _          _          _          _          _          _          _          _          _          _
  _          _          _          _          _          _          _          _          _          _          _          -          _
  @aien-shft ;          .          _          /          _          _          _          _          _          _          @aien-shft

  lalt       @cmd       @win                             _                                @nav       _
)

(deflayer inea-akl
  esc        🔅         🔆         ✗          ✗          ✗          ✗          ◀◀         ▶⏸         ▶▶         🔇         🔉         🔊
  @grv-mode  1          2          3          4          5          6          7          8          9          0          [          ]          bspc
  tab        y          p          o          u          j          k          d          l          c          w          x          =          \
  @ctl       i          n          e          a          ,          m          h          t          s          r          q          ret
  @inea-shft -          /          '          .          ;          b          f          g          v          z          @inea-shft
  lalt       @cmd       @nav                             spc                              @nav       rmet
)

(deflayer inea-shft
  esc        🔅         🔆         ✗          ✗          ✗          ✗          ◀◀         ▶⏸         ▶▶         🔇         🔉         🔊
  _          _          _          _          _          _          _          _          _          _          _          _          _          _
  _          _          _          _          _          _          _          _          _          _          _          _          .          _
  _          _          _          _          _          ;          _          _          _          _          _          _          _
  @inea-shft ,          _          _          _          -          _          _          _          _          _          @inea-shft
  lalt       @cmd       @win                             _                                @nav       _
)

(deflayer nths-akl
  esc        🔅         🔆         ✗          ✗          ✗          ✗          ◀◀         ▶⏸         ▶▶         🔇         🔉         🔊
  @grv-mode  1          2          3          4          5          6          7          8          9          0          [          ]          bspc
  tab        z          b          r          l          f          j          y          o          u          '          -          =          \
  @ctl       n          t          h          s          m          c          d          e          i          a          ,          ret
  @nths-shft q          x          w          k          v          p          g          /          .          ;          @nths-shft
  lalt       @cmd       @nav                             spc                              @nav       rmet
)

(deflayer nths-shft
  esc        🔅         🔆         ✗          ✗          ✗          ✗          ◀◀         ▶⏸         ▶▶         🔇         🔉         🔊
  _          _          _          _          _          _          _          _          _          _          _          _          _          _
  _          _          _          _          _          _          _          _          _          _          ,          ;          .          _
  _          _          _          _          _          _          _          _          _          _          _          '          _
  @nths-shft _          _          _          _          _          _          _          =          -          /          @nths-shft
  lalt       @cmd       @win                             _                                @nav       _
)

(deflayer asdf-akl
  esc        🔅         🔆         ✗          ✗          ✗          ✗          ◀◀         ▶⏸         ▶▶         🔇         🔉         🔊
  @grv-mode  1          2          3          4          5          6          7          8          9          0          -          =          bspc
  tab        q          w          e          r          t          y          u          i          o          p          [          ]          \
  @ctl       a          s          d          f          g          h          j          k          l          ;          '          ret
  lsft       z          x          c          v          b          n          m          ,          .          /          rsft
  lalt       @cmd       @nav                             spc                              @nav       rmet
)

(deflayer nav
  esc        🔅         🔆         ✗          ✗          ✗          ✗          ◀◀         ▶⏸         ▶▶         🔇         🔉         🔊
  _          _          _          _          _          _          _          _          _          _          _          _          _          _
  _          \          @prev      up         @next      _          @cmd-bspc  @cmd-left  up         @cmd-right _          @lt        @gt        _
  @nav-ctl   @notif     left       esc        rght       ret        bspc       left       ret        rght       del        \          _
  @win-shift _          _          down       _          _          @opt-bspc  @opt-left  down       @opt-right @opt-del   @win-shift
  lalt       @cmd       @nav                             _                                @nav       _
)

(deflayer nav-ctl
  esc        🔅         🔆         ✗          ✗          ✗          ✗          ◀◀         ▶⏸         ▶▶         🔇         🔉         🔊
  _          _          _          _          _          _          _          _          _          _          _          _          _          _
  _          _          _          _          _          _          _          _          up         _          _          _          _          _
  _          _          _          _          _          _          _          left       _          rght       _          _          _
  lsft       _          _          _          _          _          _          _          down       _          _          rsft
  _          _          _                                _                                _          _
)

(deflayer win
  esc        🔅         🔆         ✗          ✗          ✗          ✗          ◀◀         ▶⏸         ▶▶         🔇         🔉         🔊
  _          _          _          _          _          _          _          _          _          _          _          _          _          _
  _          _          _          _          _          _          _          _          _          _          _          _          _          _
  _          _          _          _          _          _          _          _          _          _          _          _          _
  _          _          _          _          _          _          _          _          _          _          _          _
  _          _          _                                @rect                        _          _
)

(deflayer rect
  esc        🔅         🔆         ✗          ✗          ✗          ✗          ◀◀         ▶⏸         ▶▶         🔇         🔉         🔊
  _          _          _          _          _          _          _          _          _          _          _          _          _          _
  _          _          _          _          _          _          @win-max   @win-tl4   @win-t2    @win-tr4   _          _          _          _
  _          _          @win-frst3 @win-cntr3 @win-last3 _          _          @win-l2    @win-c2    @win-r2    _          _          _
  @rect-shft _          _          _          _          _          _          @win-bl4   @win-b2    @win-br4   _          @rect-shft
  _          _          _                                @rect                            _          _
)


(deflayer rect-shft
  esc        🔅         🔆         ✗          ✗          ✗          ✗          ◀◀         ▶⏸         ▶▶         🔇         🔉         🔊
  _          _          _          _          _          _          _          _          _          _          _          _          _          _
  _          _          _          _          _          _          _          _          _          _          _          _          _          _
  _          _          @win-fst23 @win-ctr23 @win-lst23 _          _          _          _          _          _          _          _
  _          _          _          _          _          _          _          _          _          _          _          _
  _          _          _                                @rect-shft                       _          _
)

(deflayer layers
  esc        🔅         🔆         ✗          ✗          ✗          ✗          ◀◀         ▶⏸         ▶▶         🔇         🔉         🔊
  _          @asdf-akl  @nths-akl  @aien-akl  @inea-akl  lrld       _          _          _          _          _          _          _          _
  _          _          _          _          _          _          _          _          _          _          _          _          _          _
  _          _          _          _          _          _          _          _          _          _          _          _          _
  _          _          _          _          _          _          _          _          _          _          _          _
  _          @cmd       @nav                             _                                _          _
)

(deflayer cmd-qwerty
  esc        🔅         🔆         ✗          ✗          ✗          ✗          ◀◀         ▶⏸         ▶▶         🔇         🔉         🔊
  _          1          2          3          4          5          6          7          8          9          0          -         =          bspc
  tab        q          w          e          r          t          y          u          i          o          p          [         ]          \
  @ctl       a          s          d          f          g          h          j          k          l          ;          '         ret
  @shft      z          x          c          v          b          n          m          ,          .          /          @shft
  lctl       lalt       @nav-ctl                         spc                              @nav       rmet
)"#

end CapslockMode.Kanata.Fixture
