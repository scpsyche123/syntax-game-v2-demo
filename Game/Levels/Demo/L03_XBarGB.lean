import Game.Metadata

open BareSyntax

World "Demo"
Level 3

Title "X-bar theory with GB"

Introduction "
Same language, a different grammar.

Categories are now pairs ⟨head, bar level⟩: N⁰, N′, NP, and so on.
The rule table is not written by hand. A function — the **X-bar schema** — produces it
from GB's lexical information:

- **X-bar schema:** X′ → X⁰ (YP), XP → (YP) X′.
- **c-selection:** D selects NP, V selects DP, T selects VP.
- **Case:** a DP may only stand where Case is assigned: as the complement of V (accusative)
  or the specifier of finite T (nominative). No other rule accepts a DP,
  so the Case Filter is a property of the rule table.
- **EPP:** there is no rule TP → T′.
- **Infl lowering:** T′ → T⁰ VP does not just concatenate. It attaches the affix in T⁰ to
  the verb: see + -s = sees. A rule in Bare Grammar can be any partial function,
  not only concatenation.

The rules this produces:

`N′ → N⁰` · `NP → N′` · `D′ → D⁰ NP` · `DP → D′` · `V′ → V⁰ DP` · `VP → V′` · `T′ → T⁰ VP` · `TP → DP T′`

**Goal:** ⟨the cat sees the dog, TP⟩ ∈ L(xbarGB).

Build from the bottom up, for example `rule \"N' -> N0\" cat`. Each result gets a name you can
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
  Hint "Start with a noun: `rule \"N' -> N0\" cat`, then `rule \"NP -> N'\" cat_N'`."
  rule "N' -> N0" cat
  rule "NP -> N'" cat_N'
  rule "D' -> D0 NP" the cat_NP
  rule "DP -> D'" the_cat_D'
  rule "N' -> N0" dog
  rule "NP -> N'" dog_N'
  rule "D' -> D0 NP" the dog_NP
  rule "DP -> D'" the_dog_D'
  rule "V' -> V0 DP" see the_dog_DP
  rule "VP -> V'" see_the_dog_V'
  Hint "Now T: `rule \"T' -> T0 VP\" s see_the_dog_VP`. Watch what happens to *see*."
  rule "T' -> T0 VP" s see_the_dog_VP
  rule "TP -> DP T'" the_cat_DP sees_the_dog_T'

Conclusion "
Twelve rule applications, all with the command from levels 1 and 2.

GB's modules entered as data — what the schema generates, which positions accept a DP,
which rule lowers the affix — not as new machinery in the language.
"
