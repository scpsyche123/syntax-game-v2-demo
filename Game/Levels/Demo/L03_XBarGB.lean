import Game.Metadata

open BareSyntax

World "Demo"
Level 3

Title "X-bar theory with GB: Turkish"

Introduction "
Same language, a different grammar, and a different human language:

  *Kedi köpeği görüyor.*   kedi köpeğ-i gör-üyor   cat dog-ACC see-PROG   'The cat sees the dog.'

Categories are head and bar level: N⁰, N′, NP, and so on. A category can also carry a
phrase that waits inside it to move: VP/NP is a VP with a waiting NP.

The rules are the X-bar schema, five rules with variables X and Y over head categories,
plus Move α. They are produced by a function from parameters; English and Turkish are two
settings of it. Turkish is **head-final**: the complement comes before its head.

- Rule 1: `X⁰ → X′`
- Rule 2: `X′ → XP`
- Rule 3: `YP X′ → XP`
- Rule 4: `YP X⁰ → X′` (English: `X⁰ YP → X′`)
- Rule 5: `X′ YP → X′`
- Rule 6: `Move α: YP X′ → XP`

GB enters as conditions on their domains:

- **c-selection:** C selects TP, T selects VP, V selects NP. Turkish has no articles; the
  nominal arguments here are NPs.
- **VP-internal subject:** the subject is merged in Spec-VP (Rule 3). V assigns it no Case,
  so it leaves a trace there and waits: the result is VP/NP.
- **Case:** V assigns accusative to its complement, spelled as the suffix -I:
  köpek → köpeği. Finite T assigns nominative (no suffix) to its specifier.
  **Move α** puts the waiting NP into Spec-TP.
- **EPP:** T needs a specifier, so Rule 2 does not apply to T′; only Move α makes TP.
- **θ:** V assigns an external θ-role, so Rule 2 does not apply to V′: VP needs its subject.
- **The suffix:** when X is T, Rule 4 joins T's suffix to the verb: gör + -Iyor = görüyor.
- **C** is empty. **Adjuncts:** none in this fragment.

**Goal:** ⟨kedi köpeği görüyor, CP⟩ ∈ L(xbarTR).

Build from the bottom up, for example `rule \"X0 -> X'\" kedi`. Each result gets a name you
can use in the next step (`kedi_N'`, then `kedi_NP`, …). The lexicon is not used up.
"

/-- Build ⟨kedi köpeği görüyor, CP⟩ in X-bar theory with GB modules, head-final. -/
Statement (kedi : (["kedi"], x0 .N) ∈ xbarTR.lexicon)
    (köpek : (["köpek"], x0 .N) ∈ xbarTR.lexicon)
    (gör : (["gör"], x0 .V) ∈ xbarTR.lexicon)
    (yor : (["-Iyor"], x0 .T) ∈ xbarTR.lexicon)
    (c : (([] : List String), x0 .C) ∈ xbarTR.lexicon) :
    CanYield xbarTR ["kedi", "köpeği", "görüyor"] (xp .C) := by
  Hint "Start with a noun: `rule \"X0 -> X'\" kedi`, then `rule \"X' -> XP\" kedi_N'`."
  rule "X0 -> X'" kedi
  rule "X' -> XP" kedi_N'
  rule "X0 -> X'" köpek
  rule "X' -> XP" köpek_N'
  Hint "Head-final: the complement comes first. `rule \"YP X0 -> X'\" köpek_NP gör`. Watch the accusative."
  rule "YP X0 -> X'" köpek_NP gör
  Hint "Merge the subject in Spec-VP: `rule \"YP X' -> XP\" kedi_NP köpeği_gör_V'`. It gets no Case there."
  rule "YP X' -> XP" kedi_NP köpeği_gör_V'
  rule "YP X0 -> X'" köpeği_gör_VP_NP yor
  Hint "T′ cannot become TP by Rule 2 (EPP). Move the waiting NP: `rule \"Move α: YP X' -> XP\" kedi_NP köpeği_görüyor_T'_NP`."
  rule "Move α: YP X' -> XP" kedi_NP köpeği_görüyor_T'_NP
  rule "YP X0 -> X'" kedi_köpeği_görüyor_TP c
  rule "X' -> XP" kedi_köpeği_görüyor_C'

Conclusion "
Ten rule applications, one of them Move α: the subject was merged in Spec-VP, where V gives
it no Case, and moved to Spec-TP, where finite T assigns nominative. In a head-final
language this movement does not change the word order — the subject is first either way —
but the grammar still requires it.

The same rules with the head parameter set the other way, and an English lexicon, derive
*the cat sees the dog* (`xbarEN` in the playground).

Suffix lowering is not the only analysis of the verb's suffix. In a head-final language V
and T are adjacent, so lowering T's suffix and raising the verb to T give the same string.
In Chomsky (1957) the English effect is Affix Hopping, a transformation; Emonds (1978) and
Pollock (1989) have the finite verb raise to T in French; in Chomsky (1993) the verb comes
from the lexicon already inflected and checks its features against T; Bobaljik (1995) joins
tense and verb under adjacency at PF; in Distributed Morphology lowering is an operation after
syntax (Halle & Marantz 1993; Embick & Noyer 2001). Here the joining is a property of one
rule: a different analysis changes that rule, not the language.
"
