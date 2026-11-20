# Formalization of Syntactic Theory · Bare Grammar in Lean 4

**Research homepage:** https://scpsyche123.github.io/syntax-game-v2-demo/  
**Play the syntax game:** https://scpsyche123.github.io/syntax-game-v2-demo/game/

This repository holds the Lean 4 formalization behind a research project in theoretical
linguistics: Bare Grammar (Keenan & Stabler 2003) implemented in Lean, grammars from three
eras of generative syntax as instances of it, Lean-checked observations about expressive
power, and a five-level teaching game built on these grammars.

**Research:** The project asks whether generating the right expressions guarantees that a
grammar captures the relevant generalizations, which grammatical properties are invariant
under structure-preserving transformations (automorphisms), and what different syntactic
models can and cannot express. The first [Lean-checked expressive-power investigation](docs/research/expressive-power-2026-11-21.md)
and its [proof file](playground/Expressivity.lean) examine the current model's representation
of unordered MERGE, unrestricted rule arguments, and symmetry of linearization. This is
exploratory work, not a claimed equivalence or separation of full linguistic theories.

**Game:** The five-level interactive demo is a browser-based JavaScript simulation of the
Lean 4 implementation; the full game is still in development.

## GitHub Pages

The site is published from `main/docs`:

| Path | URL | What it is |
|---|---|---|
| `docs/index.html` (+ `docs/assets/fonts/`) | `/syntax-game-v2-demo/` | research homepage (one HTML file, self-hosted fonts) |
| `docs/game/index.html` | `/syntax-game-v2-demo/game/` | the playable game page (self-contained) |
| `docs/page/` | not a page | scripts that check the game's engine against Lean |
| `docs/research/` | not a page | research notes (Markdown) |

Old links to game levels (`/syntax-game-v2-demo/#mp` etc.) are forwarded to `game/`.

The game page runs a JavaScript transcription of `BareSyntax/`, checked against Lean's
output case by case; see `docs/page/README.md`.

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
  externalization. A previous bounded search for an earlier English fragment found
  1784 labeled objects pronounced "the cat will sleep" before these checks; its
  constrained uniqueness count depends on the chosen representation. The Swahili
  fragment also has a representation caveat: the current `SO.set a b` is a
  two-argument constructor rather than a commutative set. Two distinct raw
  objects (`merge m toto` vs `merge toto m`) pass all current interface
  checks and yield "mtoto atalala". Thus uniqueness under raw `SO` equality
  is **not** claimed; see [the Lean-checked comparison](docs/research/expressive-power-2026-11-21.md).
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
