import Game.Metadata

open BareSyntax

World "Demo"
Level 1

Title "A linear grammar"

Introduction "
In Bare Grammar (Keenan & Stabler 2003), a grammar is data:

- a set of **categories**,
- a **lexicon** of expressions, where an expression is a pair ⟨string, category⟩,
- a set of **rules**, each a partial function from expressions to an expression.

The language L(G) is everything that can be built from the lexicon with the rules.

The grammar of this level is `linear₁`:

- Lexicon: ⟨a, D⟩, ⟨very, Adv⟩, ⟨good, A⟩, ⟨day, N⟩
- Rules: `N → D N`, `N → D A N`

**Goal:** show that ⟨a good day, N⟩ ∈ L(linear₁).

**Command:** `rule \"N → D A N\" a good day` applies a rule to expressions in your hypotheses.
The rule computes the result; you only choose the rule and its inputs.
ASCII works too: `rule \"N -> D A N\" a good day`.
"

/-- Build ⟨a good day, N⟩ in the linear grammar. -/
Statement (a : (["a"], Linear1Cat.D) ∈ linear₁.lexicon)
    (very : (["very"], Linear1Cat.Adv) ∈ linear₁.lexicon)
    (good : (["good"], Linear1Cat.A) ∈ linear₁.lexicon)
    (day : (["day"], Linear1Cat.N) ∈ linear₁.lexicon) :
    CanYield linear₁ ["a", "good", "day"] .N := by
  Hint "Which rule has three inputs: a D, an A and an N? Try `rule \"N -> D A N\" a good day`."
  rule "N -> D A N" a good day

Conclusion "
One rule, one step.

The same command — choose a rule, give it its inputs — runs every level of this demo.
What changes from level to level is only the grammar: its categories, its lexicon, its rules.
Nothing about linear grammar is built into the language.
"

NewTactic rule
