"""
pq_verify.display -- text someone else wrote, shown without letting it act.

A response, a hybrid transcript and a harness's replies are written by the
party being checked, and pq-verify prints parts of them: the implementation a
vendor names, the hash it asserts, an identifier that did not match. Printed
as they came, control characters in those strings act on the terminal or the
CI log instead of appearing in it:

  - escape sequences erase lines, move the cursor and hide text, so a file
    could print a verdict pq-verify never reached and hide the real one;
  - a line break starts a new line, and in GitHub Actions a line that starts
    with "::" is a workflow command: an annotation, or a mask that hides
    later text in the log.

The exit status and the JSON and SARIF reports were never affected; what a
person reads was.

shown() escapes one value where it is printed. guarded_output() is the
backstop around the whole command line: whatever reaches sys.stdout or
sys.stderr without shown() still cannot act on the terminal, and no line can
start with "::". pq-verify itself prints neither.
"""

import contextlib
import re
import sys

# What acts on a terminal or a log viewer instead of appearing in it: C0
# controls but tab and newline, DEL and the C1 controls, the Unicode line and
# paragraph separators, and the bidirectional controls that reorder text.
_ACTS = re.compile("[\x00-\x08\x0b-\x1f\x7f-\x9f؜‎‏"
                   "  ‪-‮⁦-⁩]")
_NAMED = {"\n": "\\n", "\r": "\\r", "\t": "\\t"}


def _escape(ch):
    if ch in _NAMED:
        return _NAMED[ch]
    o = ord(ch)
    return f"\\x{o:02x}" if o < 0x100 else (f"\\u{o:04x}" if o < 0x10000 else f"\\U{o:08x}")


def shown(value, limit=200):
    """`value` as text that cannot act on a terminal or a CI log.

    Every character Python does not count as printable is written as its
    escape (\\x1b, \\n, \\u202e); a leading "::" cannot start a GitHub
    workflow command; more than `limit` characters are cut, saying how many
    were left out. A value that is not a string is shown as str() of it.
    """
    s = value if isinstance(value, str) else str(value)
    cut = len(s) - limit if limit and len(s) > limit else 0
    if cut:
        s = s[:limit]
    s = "".join(c if c.isprintable() else _escape(c) for c in s)
    body = s.lstrip()
    if body.startswith("::"):
        i = len(s) - len(body)
        s = s[:i] + "\\x3a" + s[i + 1:]
    return s + (f"… ({cut} more characters)" if cut else "")


class _Guard:
    """A text stream that escapes what would act on a terminal or a CI log,
    and the colon that starts a line, so no line can begin with "::" (GitHub
    skips any leading whitespace before it looks). pq-verify's own lines
    never start with a colon; everything else passes unchanged."""

    def __init__(self, stream):
        self._stream = stream
        self._at_start = True        # nothing but whitespace on this line yet

    def write(self, text):
        if not isinstance(text, str):
            return self._stream.write(text)
        out = []
        for piece in re.split(r"(\n)", _ACTS.sub(lambda m: _escape(m.group()), text)):
            if piece == "\n":
                self._at_start = True
            elif piece and self._at_start:
                body = piece.lstrip()
                if body:
                    if body[0] == ":":
                        i = len(piece) - len(body)
                        piece = piece[:i] + "\\x3a" + piece[i + 1:]
                    self._at_start = False
            out.append(piece)
        self._stream.write("".join(out))
        return len(text)

    def __getattr__(self, name):
        return getattr(self._stream, name)


@contextlib.contextmanager
def guarded_output():
    """Route sys.stdout and sys.stderr through _Guard for the block."""
    old_out, old_err = sys.stdout, sys.stderr
    sys.stdout, sys.stderr = _Guard(old_out), _Guard(old_err)
    try:
        yield
    finally:
        sys.stdout, sys.stderr = old_out, old_err
