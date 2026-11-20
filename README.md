# Syntax Game v2 · Bare Grammar demo

Play: https://adam.math.hhu.de/#/g/scpsyche123/syntax-game-v2-demo

Three short levels showing one formal language — Bare Grammar (Keenan & Stabler 2003),
implemented in Lean 4 — expressing grammars from three eras of generative syntax:

| Level | Grammar | What it shows |
|---|---|---|
| 1 | `linear₁` | a grammar is categories, a lexicon and rules; one derivation step |
| 2 | `xbarGB` | X-bar schema as a function from GB data (c-selection, Case positions, EPP) to a rule table; Infl lowering as a non-concatenative rule |
| 3 | `mpWS` | workspace-era MERGE: an expression is a workspace, MERGE(P, Q, WS) = [{P, Q}, …]; labeling algorithm; externalization checked automatically |

## Layout

- `BareSyntax/Basic.lean` — the language: expressions, rules, `Deriv`, `CanYield`.
  Copied from `scpsyche123/syntax-game` (`BareSyntax/Basic.lean`, merged 2026-07-28) with one
  additive extension: a second rule form (`FRule`) whose domain is a decidable condition and
  which is indexed by an argument; `Deriv` gains the constructor `fapp`.
- `BareSyntax/Linear.lean`, `XBarGB.lean`, `MP.lean` — the three grammars.
- `BareSyntax/Show.lean` — how expressions and workspaces are displayed.
- `BareSyntax/Tactics.lean` — the player commands `rule`, `select`, `merge`.
- `Game/` — the lean4game levels. Each level's statement contains a solution, so
  `lake build` checks that every level can be completed.

## Design decisions

- Players build bottom-up. Strings (and, in level 3, workspaces) are computed by the rules;
  the player chooses rules and inputs, never types an output.
- Level 3 asks only for narrow syntax: one object in the workspace, every node labeled.
  Externalization (order, pronouncing the highest copy) is computed and checked by Lean.
- MERGE follows Chomsky (2020, *UCLA Lectures*) as quoted in V. J. Pan, *Lecture 10: The
  Minimalist Program*, §9: MERGE replaces P and Q by {P, Q}. Pan & Du's rendering
  [{P, Q}, P, Q, …] is not used.
- Stated simplifications in level 3: copies are identified by identity (no Form Copy);
  Agree is not modeled; no phases, Transfer or Minimal Search.

## Build

```
lake build
```

Toolchain and GameServer versions are pinned to those of `scpsyche123/syntax-game`
(`leanprover/lean4:v4.23.0`). Pushing to `main` builds the game in GitHub Actions and
triggers the import on adam.math.hhu.de.
