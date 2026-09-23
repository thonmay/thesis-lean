#!/usr/bin/env python3
"""Copy the BEGIN DEFS/END DEFS block of ThesisLean/ChallengeDefs.lean into Challenge.lean."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
BEGIN, END = "-- BEGIN DEFS", "-- END DEFS"


def block(text: str, path: pathlib.Path) -> tuple[int, int]:
    try:
        start = text.index(BEGIN)
        stop = text.index(END) + len(END)
    except ValueError:
        sys.exit(f"error: no {BEGIN}/{END} block in {path}")
    return start, stop


defs_path = ROOT / "ThesisLean" / "ChallengeDefs.lean"
challenge_path = ROOT / "Challenge.lean"
defs = defs_path.read_text()
challenge = challenge_path.read_text()
d0, d1 = block(defs, defs_path)
c0, c1 = block(challenge, challenge_path)
challenge_path.write_text(challenge[:c0] + defs[d0:d1] + challenge[c1:])
print(f"synced definitions block into {challenge_path.name}")
