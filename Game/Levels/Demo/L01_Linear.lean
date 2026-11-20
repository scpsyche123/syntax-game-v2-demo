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

- Lexicon: a : D, very : Adv, good : A, day : N
- Rule 1: `Adv A → A`
- Rule 2: `A N → N`
- Rule 3: `D N → D`

**Goal:** show that ⟨a very good day, D⟩ ∈ L(linear₁).

**Command:** `rule \"Adv A -> A\" very good` applies Rule 1 to the expressions `very` and `good`.
The rule computes the result and names it (`very_good_A`); you only choose the rule and its inputs.
"

/-- Build ⟨a very good day, D⟩ in the linear grammar. -/
Statement (a : (["a"], Linear1Cat.D) ∈ linear₁.lexicon)
    (very : (["very"], Linear1Cat.Adv) ∈ linear₁.lexicon)
    (good : (["good"], Linear1Cat.A) ∈ linear₁.lexicon)
    (day : (["day"], Linear1Cat.N) ∈ linear₁.lexicon) :
    CanYield linear₁ ["a", "very", "good", "day"] .D := by
  Hint "Start inside: which rule can take `very` and `good`? Try `rule \"Adv A -> A\" very good`."
  rule "Adv A -> A" very good
  rule "A N -> N" very_good_A day
  rule "D N -> D" a very_good_day_N

Conclusion "
Three rule applications. The same command — choose a rule, give it its inputs — runs every level.
What changes from level to level is only the grammar: its categories, its lexicon, its rules.
"

NewTactic rule
