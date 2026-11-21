# X-bar theory in Lean 4: English demo of the earlier formalization

The project's first formalization (July 2026) encoded X-bar phrase structure in
Lean 4 and turned it into a twelve-level teaching game for the lean4game
platform. This folder is an English demo version of that work. It contains the
theory library, the player commands and the twelve levels. Everything runs on
Lean core alone, without the game server, and each level can be stepped
through in VS Code.

## Design

A string is grammatical when a tree for it exists and ungrammatical when no
tree can be built. The type system rules out ill-formed structures in three
ways, so nothing has to mark them as errors afterwards.

Trees are indexed by bar level and category, `XTree : Bar → Pos → Type`. A
tree with the wrong bar level or category does not type-check.

Attaching a complement requires evidence `Selects c d`. The licensed pairs are
D selecting N, T selecting V, C selecting T, P selecting D, and V selecting D.
Any other pair has no evidence, so no tree contains it.

Placing a word requires evidence `Lexicon c w`. `Lexicon` has no constructors,
and each level supplies its words as hypotheses, so grammaticality is always
relative to a given lexicon.

Endocentricity is stated by a type:

```lean
def Head : XTree b c → LexicalEntry c
```

Every tree of category `c` has a head of category `c`. An earlier version stated
this as a theorem about trees; here a tree whose head has another category
cannot be constructed.

## Files

| File | Contents |
|---|---|
| `XSyntax/Basic.lean` | Categories (N, V, A, P, Adv, T, D, C, Conj) and category-indexed lexical entries |
| `XSyntax/Tree.lean` | `Bar`, `Selects`, `Lexicon`, `XTree` |
| `XSyntax/Operations.lean` | `cat`, `bar`, `Head`, `yield` (the string) and `plot` (labeled brackets) |
| `XSyntax/TypeNotation.lean`, `XSyntax/Display.lean` | Goals shown in linguistic notation: `NP`, `N′`, `N⁰` |
| `XSyntax/Tactics.lean` | The player commands, one per X-bar rule, and `CannotSelect` |
| `XSyntax/TreeView.lean` | An optional tree-state marker for a custom front end (off in the levels) |
| `XSyntax/Playground.lean` | The original five-scene walkthrough |
| `Levels.lean` | The twelve levels |

`Playground.lean` prints trees with `#eval`, which needs a closed lexicon, so it
declares a file-local axiom that every word belongs to every category. The root
file `XSyntax.lean` imports it so that `lake build` checks the walkthrough.
`Levels.lean` does not import it, and the levels use no axioms.

## The twelve levels

| Level | Target | Category | New in this level |
|---|---|---|---|
| I.1 | *ideas* | N⁰ | Words are heads |
| I.2 | *ideas* | NP | Projection: X⁰ → X′ → XP |
| I.3 | *hers* | DP | D is a category; function words are heads |
| I.4 | *sees the cat* | VP | Complements and selection |
| I.5 | ¬ Selects D V | | Proving that a licence does not exist |
| I.6 | *my big house* | DP | Left adjuncts; complement versus adjunct |
| I.7 | *the strange dog* | DP | The same choices without hints |
| I.8 | *sleep quickly* | VP | Right adjuncts and adverbs |
| II.1 | *cats will sleep* | TP | T as a head; the subject in Spec,TP |
| II.2 | *cats sleep* | CP | C; empty C and empty T |
| II.3 | *the big dog sees the cat* | CP | A full clause without hints |
| II.4 | *Colorless green ideas sleep furiously* | CP | Grammatical but meaningless |

## Known limitations

These come from the project's own review of the game in July 2026.

- Most levels ask the player to enter a tree they already know; they teach
  execution more than judgment. Level I.7 has the same structure as I.6.
- The DP hypothesis is built in without being marked as a theoretical choice.
- There is no movement. The clause level relies on empty heads, and the *-s* of
  *sees* is not analysed as T.
- `Selects` works on categories, not lexical items: it rules out *the sleeps*
  but not *sleep the cat*.
- When a phrase splits, the goal panel assigns substrings to the daughters by
  heuristics, which gives away part of the answer.

## Checking it

With the Lean 4.23.0 toolchain:

```bash
cd xbar
lake build
```

This checks the library, the walkthrough and all twelve levels. To step through
a level, open `xbar/` as a folder in VS Code with the Lean 4 extension, open
`Levels.lean`, and move the cursor through a solution.
