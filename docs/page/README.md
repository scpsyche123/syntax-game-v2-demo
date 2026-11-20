# Demo page

`../index.html` is a self-contained page that steps through the three levels. Every
infoview state and message on it is real Lean output.

To regenerate after changing the grammars or tactics, run `python3 gen.py`. It runs each
level in `playground/` with `trace_state` after every step (plus the wrong moves), writes
`data.json`, and rebuilds `../index.html` from `template.html`. The playground must build.
