# Fonts

Subsets used by the research homepage, served from this folder so the page makes no
third-party requests. Both families are under the SIL Open Font License 1.1 (see the
`OFL-*.txt` files).

| File | Source | Contents |
|---|---|---|
| `stix-two-text.woff2`, `stix-two-text-italic.woff2` | STIX Two Text (variable, weights 400–700), google/fonts | Latin, Latin Extended-A, IPA (including tone letters and combining diacritics), Greek, punctuation, super/subscripts, letterlike symbols |
| `jetbrains-mono.woff2` | JetBrains Mono (weight 400), google/fonts | Latin, Greek, arrows, operators, subscripts (for Lean code) |

Made with fontTools, for example:

```
pyftsubset STIXTwoText[wght].ttf --flavor=woff2 --no-hinting \
  --unicodes='U+0020-007E,U+00A0-017F,U+0250-036F,U+0370-03FF,U+2000-206F,U+2070-209F,U+2100-214F' \
  --output-file=stix-two-text.woff2
```
