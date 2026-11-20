import Game.Metadata

open BareSyntax

World "Demo"
Level 3

Title "X-bar theory with GB"

Introduction "
Same language, a different grammar.

Categories are now pairs ⟨head, bar level⟩: N⁰, N′, NP, and so on.
The rules are the **X-bar schema**: five rules with variables X and Y, which range over
head categories. Each rule's domain is fixed by the pattern on its left-hand side and by a
condition stated with GB's lexical information:

- Rule 1: `X⁰ → X′`. X takes no complement.
- Rule 2: `X′ → XP`. X needs no specifier (EPP: T needs one).
- Rule 3: `YP X′ → XP`. YP is the specifier of X; a DP needs Case from X.
- Rule 4: `X⁰ YP → X′`. X c-selects Y; a DP needs Case from X; T's affix lowers onto V.
- Rule 5: `X′ YP → X′`. YP is an adjunct of X.

GB's lexical information:

- **c-selection:** D selects NP, V selects DP, T selects VP.
- **Case:** V assigns accusative to its complement; finite T assigns nominative to its
  specifier. A DP is accepted only where Case is assigned, so the Case Filter is a
  property of the rules' domains.
- **EPP:** T needs a specifier, so Rule 2 does not apply to T′.
- **Infl lowering:** when X is T, Rule 4 does not just concatenate. It attaches the affix in
  T⁰ to the verb: see + -s = sees. A rule in Bare Grammar can be any partial function,
  not only concatenation.
- **Adjuncts:** none in this fragment, so Rule 5 never applies here.

**Goal:** ⟨the cat sees the dog, TP⟩ ∈ L(xbarGB).

Build from the bottom up, for example `rule \"X0 -> X'\" cat`. Each result gets a name you can
use in the next step (`cat_N'`, then `cat_NP`, …).
The lexicon is not used up: the same ⟨the, D⁰⟩ can go into both DPs.
"

/-- Build ⟨the cat sees the dog, TP⟩ in X-bar theory with GB modules. -/
Statement (the : (["the"], x0 .D) ∈ xbarGB.lexicon)
    (cat : (["cat"], x0 .N) ∈ xbarGB.lexicon)
    (dog : (["dog"], x0 .N) ∈ xbarGB.lexicon)
    (see : (["see"], x0 .V) ∈ xbarGB.lexicon)
    (s : (["-s"], x0 .T) ∈ xbarGB.lexicon) :
    CanYield xbarGB ["the", "cat", "sees", "the", "dog"] (xp .T) := by
  Hint "Start with a noun: `rule \"X0 -> X'\" cat`, then `rule \"X' -> XP\" cat_N'`."
  rule "X0 -> X'" cat
  rule "X' -> XP" cat_N'
  rule "X0 YP -> X'" the cat_NP
  rule "X' -> XP" the_cat_D'
  rule "X0 -> X'" dog
  rule "X' -> XP" dog_N'
  rule "X0 YP -> X'" the dog_NP
  rule "X' -> XP" the_dog_D'
  rule "X0 YP -> X'" see the_dog_DP
  rule "X' -> XP" see_the_dog_V'
  Hint "Now T: `rule \"X0 YP -> X'\" s see_the_dog_VP`. Watch what happens to *see*."
  rule "X0 YP -> X'" s see_the_dog_VP
  rule "YP X' -> XP" the_cat_DP sees_the_dog_T'

Conclusion "
Twelve applications of four schema rules, all with the command from levels 1 and 2.

GB's modules entered as conditions on the domains of the schema rules — which complement a
head selects, where a DP gets Case, which head needs a specifier, which rule lowers the
affix — not as new machinery in the language.
"
