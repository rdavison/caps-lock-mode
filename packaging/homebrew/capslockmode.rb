# Source of truth for the Homebrew formula.  The release workflow rewrites the
# version and sha256 and pushes a copy to the tap repository
# (rdavison/homebrew-capslockmode); a tap repo has to be named `homebrew-*`, so
# it cannot live inside this one.
#
#   brew install rdavison/capslockmode/capslockmode
#   brew services start capslockmode
class Capslockmode < Formula
  desc "Vi-like modal keyboard layer toggled with Caps Lock, with proofs"
  homepage "https://github.com/rdavison/caps-lock-mode"
  url "https://github.com/rdavison/caps-lock-mode/releases/download/v0.2.0/capslockmode-macos-universal.tar.gz"
  sha256 "0000000000000000000000000000000000000000000000000000000000000000"
  license "MIT"

  depends_on :macos

  def install
    bin.install "capslockmode"
    bin.install "capslockmode-quartz"
  end

  # `brew services start capslockmode` writes the LaunchAgent and bootstraps it
  # into the user's GUI session.  Never `sudo brew services`: that installs a
  # system LaunchDaemon, which has no session to tap and the wrong permission
  # context.
  service do
    run [opt_bin/"capslockmode-quartz"]
    keep_alive true
    run_type :immediate
    environment_variables CAPSLOCKMODE_BIN: opt_bin/"capslockmode"
    log_path var/"log/capslockmode.log"
    error_log_path var/"log/capslockmode.err.log"
  end

  def caveats
    <<~EOS
      CapslockMode needs Accessibility permission to reshape keystrokes:

        System Settings -> Privacy & Security -> Accessibility
        add #{opt_bin}/capslockmode-quartz

      The binary is ad-hoc signed, so macOS treats every upgrade as a different
      program: after `brew upgrade` you must remove that entry and add it again.
      `capslockmode-quartz --check` reports the current status.

      Caps Lock itself cannot be swallowed by an event tap -- the lock state
      lives below it in IOKit -- so the service remaps Caps Lock to F18 with
      hidutil while it runs, and uses F18 as the toggle. Pass --no-remap if you
      would rather bind another key.

      Start it with:
        brew services start capslockmode     # not with sudo

      To stop, and restore Caps Lock:
        brew services stop capslockmode
    EOS
  end

  test do
    assert_match "capslockmode", shell_output("#{bin}/capslockmode --version")
    # the machine is a pure filter, so it can be tested without a keyboard
    output = pipe_output("#{bin}/capslockmode run --wire quartz --platform mac",
                         "down 57\ndown 2\nup 2\ndown 2\nup 2\n")
    assert_match "key down 123 command", output
  end
end
