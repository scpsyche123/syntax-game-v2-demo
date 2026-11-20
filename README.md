# Syntax Game v2 · Bare Grammar demo

Playable page: `docs/index.html` (self-contained). It runs a JavaScript transcription of
`BareSyntax/`, checked against Lean's output case by case; see `docs/page/README.md`.

Play (once the lean4game server import works): https://adam.math.hhu.de/#/g/scpsyche123/syntax-game-v2-demo

Short levels showing one formal language — Bare Grammar (Keenan & Stabler 2003),
implemented in Lean 4 — expressing grammars from three eras of generative syntax:

| Level | Grammar | What it shows |
|---|---|---|
| 1 | `linear₁` | a grammar is categories, a lexicon and rules: *a very good day* as a D in three steps |
| — | `linear₁` | *a very day* is not in the language: every move is rejected (page and playground only; a lean4game level needs a solution) |
| 2 | `linear₂` | overgeneration: with D N → N alone the grammar derives *a a the this dog* as an N |
| 3 | `xbarTR` | Turkish, *kedi köpeği görüyor* 'the cat sees the dog'. X-bar schema as rules with variables X, Y, plus Move α, produced by a function from parameters (`xbarEN` is the English setting); Turkish sets the head parameter to final; GB data (c-selection, Case with accusative -I, EPP, the external θ-role of V) as conditions on the rules' domains; the subject moves from Spec-VP to Spec-TP; T's suffix joins the verb; an empty C makes CP |
| 4 | `mpWS` | Swahili, *mtoto atalala* 'the child will sleep'. Workspace-era MERGE: an expression is a workspace, MERGE(P, Q, WS) = [{P, Q}, …]; labeling algorithm (noun class as φ on n, valued φ on T); interface conditions; externalization, including the joining of prefixes, checked automatically |

## Layout

- `BareSyntax/Basic.lean` — the language: expressions, rules, `Deriv`, `CanYield`.
  Copied from `scpsyche123/syntax-game` (`BareSyntax/Basic.lean`, merged 2026-07-28) with one
  additive extension: a second rule form (`FRule`) whose domain is a decidable condition and
  which is indexed by an argument; `Deriv` gains the constructor `fapp`.
- `BareSyntax/Linear.lean` (`linear₁`, `linear₂`), `XBarGB.lean`, `MP.lean` — the grammars.
- `BareSyntax/Show.lean` — how expressions and workspaces are displayed.
- `BareSyntax/Tactics.lean` — the player commands `rule`, `select`, `merge`.
- `Game/` — the lean4game levels. Each level's statement contains a solution, so
  `lake build` checks that every level can be completed.

## Design decisions

- Players build bottom-up. Strings (and, in level 4, workspaces) are computed by the rules;
  the player chooses rules and inputs, never types an output.
- Level 4 asks only for narrow syntax: one object in the workspace, every node labeled.
  Externalization (order, pronouncing the highest copy) is computed and checked by Lean.
- MERGE is free; the finished object is filtered at CI by selection (T takes vP, n and v
  take a root), the θ-criterion (the subject nP first merges with vP) and a chain condition
  (only the subject moves, once, to the specifier of T). These are checked automatically with
  externalization. Without them, a search of all derivations with at most two Internal
  MERGEs (for the earlier English version of this level) found 1784 objects pronounced
  "the cat will sleep" with every node labeled; with them, exactly one. The same holds for
  the Swahili fragment: exactly one object converges, and none from a subset of the lexicon
  or with a repeated n or v.
- MERGE follows Chomsky (2020, *UCLA Lectures*) as quoted in V. J. Pan, *Lecture 10: The
  Minimalist Program*, §9: MERGE replaces P and Q by {P, Q}. Pan & Du's rendering
  [{P, Q}, P, Q, …] is not used.
- Stated simplifications in level 4: copies are identified by identity (no Form Copy);
  Agree is not modeled; no phases, Transfer or Minimal Search.

## Step through it in VS Code (no game server needed)

`playground/` is a separate Lake package with no dependencies: it compiles the language with
Lean core only. Open `playground/` in VS Code (Lean 4 extension installed), open `Demo.lean`,
and move the cursor through each proof; the infoview shows every step. `Demo.lean` also
contains the rejected attempts at *a very day*.

## Build

```
lake build
```

Toolchain and GameServer versions are pinned to those of `scpsyche123/syntax-game`
(`leanprover/lean4:v4.23.0`). Pushing to `main` builds the game in GitHub Actions and
triggers the import on adam.math.hhu.de.
