import Game.Metadata

open BareSyntax

World "Demo"
Level 3

Title "X-bar theory with GB"

Introduction "
Same language, a different grammar.

Categories are now head and bar level: N⁰, N′, NP, and so on. A category can also carry a
phrase that waits inside it to move: VP/DP is a VP with a waiting DP.

The rules are the X-bar schema, five rules with variables X and Y over head categories,
plus Move α:

- Rule 1: `X⁰ → X′`
- Rule 2: `X′ → XP`
- Rule 3: `YP X′ → XP`
- Rule 4: `X⁰ YP → X′`
- Rule 5: `X′ YP → X′`
- Rule 6: `Move α: YP X′ → XP`

GB enters as conditions on their domains:

- **c-selection:** C selects TP, T selects VP, V selects DP, D selects NP.
- **VP-internal subject:** the subject is merged in Spec-VP (Rule 3). V assigns it no Case,
  so it leaves a trace there and waits: the result is VP/DP.
- **Case:** V assigns accusative to its complement; finite T assigns nominative to its
  specifier. **Move α** puts the waiting DP into Spec-TP.
- **EPP:** T needs a specifier, so Rule 2 does not apply to T′; only Move α makes TP.
- **Suffix lowering:** when X is T, Rule 4 attaches the suffix in T⁰ to the verb:
  see + -s = sees.
- **C** is empty. **Adjuncts:** none in this fragment, so Rule 5 never applies here.

**Goal:** ⟨the cat sees the dog, CP⟩ ∈ L(xbarGB).

Build from the bottom up, for example `rule \"X0 -> X'\" cat`. Each result gets a name you can
use in the next step (`cat_N'`, then `cat_NP`, …). The lexicon is not used up.
"

/-- Build ⟨the cat sees the dog, CP⟩ in X-bar theory with GB modules. -/
Statement (the : (["the"], x0 .D) ∈ xbarGB.lexicon)
    (cat : (["cat"], x0 .N) ∈ xbarGB.lexicon)
    (dog : (["dog"], x0 .N) ∈ xbarGB.lexicon)
    (see : (["see"], x0 .V) ∈ xbarGB.lexicon)
    (s : (["-s"], x0 .T) ∈ xbarGB.lexicon)
    (c : (([] : List String), x0 .C) ∈ xbarGB.lexicon) :
    CanYield xbarGB ["the", "cat", "sees", "the", "dog"] (xp .C) := by
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
  Hint "Merge the subject in Spec-VP: `rule \"YP X' -> XP\" the_cat_DP see_the_dog_V'`. It gets no Case there."
  rule "YP X' -> XP" the_cat_DP see_the_dog_V'
  rule "X0 YP -> X'" s see_the_dog_VP_DP
  Hint "T′ cannot become TP by Rule 2 (EPP). Move the waiting DP: `rule \"Move α: YP X' -> XP\" the_cat_DP sees_the_dog_T'_DP`."
  rule "Move α: YP X' -> XP" the_cat_DP sees_the_dog_T'_DP
  rule "X0 YP -> X'" c the_cat_sees_the_dog_TP
  rule "X' -> XP" the_cat_sees_the_dog_C'

Conclusion "
Fourteen rule applications, one of them Move α: the subject was merged in Spec-VP, where V
gives it no Case, and moved to Spec-TP, where finite T assigns nominative. It left a trace.

Suffix lowering is not the only analysis of *sees*. In Chomsky (1957) the same effect is
Affix Hopping, a transformation. Emonds (1978) and Pollock (1989) have the finite verb raise
to T in French, while in English only auxiliaries raise. In Chomsky (1993) the verb comes from
the lexicon already inflected and checks its features against T, so nothing lowers. Bobaljik
(1995) treats English tense and the verb as joining under adjacency at PF, and in Distributed
Morphology lowering is an operation after syntax (Halle & Marantz 1993; Embick & Noyer 2001).
Here lowering is a property of one rule: a different analysis changes that rule, not the
language.
"
