import Game.Levels.Demo

Title "Syntax Game v2 · Bare Grammar demo"
Introduction "
This demo shows one formal language expressing grammars from three eras of generative syntax:

1. a linear grammar (English),
2. X-bar theory with GB modules — c-selection, Case, EPP, θ, Move α — for Turkish, head-final,
3. the Minimalist Program of the workspace era (MERGE on workspaces, labeling, interface
   conditions) for Swahili.

The language is Bare Grammar (Keenan & Stabler 2003), implemented in Lean 4. A grammar is
data — categories, a lexicon, rules — and an expression belongs to the language when there is
a derivation of it. Every step you take is checked by Lean's kernel.
"

Info "
**The language.** `BareSyntax/Basic.lean`: expressions ⟨string, category⟩, rules as partial
functions, the derivation relation `Deriv`, grammaticality `CanYield`. Rules come in two forms:
a domain given as a list of categories (levels 1–2), or a domain given by a pattern and a decidable
condition (levels 3–4: the X-bar schema, and MERGE, where categories are workspaces).

**References.**
Keenan, E. & Stabler, E. (2003). *Bare Grammar: Lectures on Linguistic Invariants.* CSLI.
Chomsky, N. (2013). Problems of projection. *Lingua* 130.
Chomsky, N. (2020). *The UCLA Lectures.*
Pan, V. J. *Lecture 10: The Minimalist Program* (§9).

Source: https://github.com/scpsyche123/syntax-game-v2-demo

---

*Build: `{{BUILD_VERSION}}`*
"

MakeGame
