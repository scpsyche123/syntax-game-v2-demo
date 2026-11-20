# Demo page

`../index.html` is a self-contained, playable page with five levels: a linear grammar,
a string it cannot derive (*a very day*), an overgenerating grammar (*a a the this dog*),
X-bar theory with GB, and the workspace-era Minimalist Program.

The page cannot run Lean in the browser. Its `<script id="engine">` block is a JavaScript
transcription of `BareSyntax/` (rule tables, rule application, MERGE, labeling,
externalization, and the error messages of `BareSyntax/Tactics.lean`).

How the transcription is checked against Lean:

1. `python3 gen.py` runs every solution step, the listed wrong moves, and every attempt
   at *a very day* through Lean in `playground/` (which must build), and records Lean's
   hypotheses and messages in `truth.json`.
2. `node check_engine.js` runs the same commands through the page's engine and compares
   results and messages with `truth.json`, word for word. It exits non-zero on any mismatch.

Run both after changing a grammar, a tactic message, or the engine.

The one rule that is the page's own: in the three linear levels, a rule may only join
pieces that are adjacent in the sentence. Every rule there concatenates its inputs, so a
non-adjacent combination can never be part of a derivation of the sentence.
