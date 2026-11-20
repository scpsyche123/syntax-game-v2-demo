import Game.Metadata

open BareSyntax

World "Demo"
Level 2

Title "A grammar that says too much"

Introduction "
`linear₂` is `linear₁` with three more words (the : D, this : D, dog : N) and one more rule:

- Rule 1: `A → Adv A`
- Rule 2: `N → A N`
- Rule 3: `D → D N`
- Rule 4: `N → D N`

Rule 4 looks harmless. But its output is an N, and Rule 4 also takes an N.

**Goal:** show that ⟨a a the this dog, D⟩ ∈ L(linear₂).
"

/-- Build ⟨a a the this dog, D⟩ with the extra rule. -/
Statement (a : (["a"], Linear1Cat.D) ∈ linear₂.lexicon)
    (the : (["the"], Linear1Cat.D) ∈ linear₂.lexicon)
    (this : (["this"], Linear1Cat.D) ∈ linear₂.lexicon)
    (dog : (["dog"], Linear1Cat.N) ∈ linear₂.lexicon) :
    CanYield linear₂ ["a", "a", "the", "this", "dog"] .D := by
  Hint "Start from the right: `rule \"N -> D N\" this dog`."
  rule "N -> D N" this dog
  rule "N -> D N" the this_dog_N
  rule "N -> D N" a the_this_dog_N
  rule "D -> D N" a a_the_this_dog_N

Conclusion "
The proof went through, and that is the problem: *a a the this dog* is not English, but
`linear₂` generates it. Rule 4 feeds itself, so determiners stack without limit.
The error is in the grammar, and Lean finds it by deriving the string.
"
