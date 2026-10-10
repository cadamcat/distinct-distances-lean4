#!/usr/bin/env python3
"""Scan the target's dependency cone for forbidden constructs.

Scans every Lean source under DistinctDistances/, Audit/ and scripts/, and the root module
DistinctDistances.lean, for `sorry`, `admit`, `axiom` declarations, `native_decide`,
`implemented_by`, `extern` and `unsafe`. Challenge.lean states the target with `sorry` as its
proof by design; it is scanned for every construct except `sorry`. Line comments (`-- ...`) and block comments (`/- ... -/`, non-nested) are stripped
before matching, so prose that mentions these words in comments is not reported.

Exit 0 when no hit is found; 1 otherwise (each hit is printed as FILE:LINE: KIND: TEXT).
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

PATTERNS = [
    ("sorry", re.compile(r"\bsorry\b")),
    ("admit", re.compile(r"\badmit\b")),
    ("axiom-declaration", re.compile(r"^\s*axiom\b")),
    ("native_decide", re.compile(r"\bnative_decide\b")),
    ("implemented_by", re.compile(r"\bimplemented_by\b")),
    ("extern", re.compile(r"\bextern\b")),
    ("unsafe", re.compile(r"\bunsafe\b")),
]

BLOCK_COMMENT = re.compile(r"/-.*?-/", re.S)


def strip_comments(text: str) -> list:
    text = BLOCK_COMMENT.sub(lambda m: "\n" * m.group(0).count("\n"), text)
    out = []
    for line in text.splitlines():
        cut = line.find("--")
        out.append(line[:cut] if cut >= 0 else line)
    return out


CHALLENGE = ROOT / "Challenge.lean"


def files():
    found = [CHALLENGE, ROOT / "DistinctDistances.lean"]
    for d in ("DistinctDistances", "Audit", "scripts"):
        p = ROOT / d
        if p.is_dir():
            found += sorted(p.rglob("*.lean"))
    return found


def main() -> int:
    hits = 0
    scanned = 0
    for path in files():
        try:
            lines = strip_comments(path.read_text(encoding="utf-8", errors="replace"))
        except OSError as e:
            print(f"FAIL: cannot read {path}: {e}", file=sys.stderr)
            return 1
        scanned += 1
        for i, line in enumerate(lines, 1):
            for kind, rx in PATTERNS:
                if path == CHALLENGE and kind == "sorry":
                    continue
                if rx.search(line):
                    print(f"{path.relative_to(ROOT)}:{i}: {kind}: {line.strip()}")
                    hits += 1
    print(f"scanned {scanned} files: {'PASS: no forbidden constructs' if hits == 0 else f'FAIL: {hits} hits'}")
    return 1 if hits else 0


if __name__ == "__main__":
    raise SystemExit(main())
