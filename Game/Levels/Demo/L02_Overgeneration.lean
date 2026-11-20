import Game.Metadata

open BareSyntax

World "Demo"
Level 2

Title "A grammar that says too much"

Introduction "
`linear₂` is `linear₁` with three more words (the : D, this : D, dog : N) and one more rule:

- Rule 4: `N → D N`

Rule 4 looks harmless. But its output is an N, and Rule 4 also takes an N.

**Goal:** show that ⟨a a the this dog, N⟩ ∈ L(linear₂), using only Rule 4.
"

/-- Build ⟨a a the this dog, N⟩ with Rule 4. -/
Statement (a : (["a"], Linear1Cat.D) ∈ linear₂.lexicon)
    (the : (["the"], Linear1Cat.D) ∈ linear₂.lexicon)
    (this : (["this"], Linear1Cat.D) ∈ linear₂.lexicon)
    (dog : (["dog"], Linear1Cat.N) ∈ linear₂.lexicon) :
    CanYield linear₂ ["a", "a", "the", "this", "dog"] .N := by
  Hint "Start from the right: `rule \"N -> D N\" this dog`."
  rule "N -> D N" this dog
  rule "N -> D N" the this_dog_N
  rule "N -> D N" a the_this_dog_N
  rule "N -> D N" a a_the_this_dog_N

Conclusion "
The proof went through, and that is the problem. *a a the this dog* is not an expression of
English, yet `linear₂` derives it, so the rule is too strong. Rule 4 takes an N and returns an N,
so it can apply again and again.

Suppose instead we keep only Rule 3, `D → D N`, and set the goal to D. Then *this dog* becomes a D,
no rule applies after that, and ⟨a a the this dog, D⟩ cannot be derived. That is the result we want.
Failing to derive is also a good result: a good model should not allow more than the natural
language does.
"
