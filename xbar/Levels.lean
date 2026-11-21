/-
The twelve levels of the X-bar syntax game (July 2026), in English.

The original ran on the lean4game server, with each level's text shown beside
the goal panel. Here every level is an ordinary Lean definition: the level's
lexicon is given as hypotheses, the goal is a tree that reads as the target
string, and the body is the solution, one X-bar rule per line. Open this file
in VS Code and move the cursor through a solution to watch the goal panel.

Player commands, one per X-bar rule:
  `nospec`         XP → X′            (no specifier)
  `specifier YP`   XP → YP + X′
  `nocomp`         X′ → X⁰            (no complement)
  `complement YP`  X′ → X⁰ + YP       (selection is checked at this keystroke)
  `adjoinL YP`     X′ → YP + X′       (left adjunct; bar level unchanged)
  `adjoinR YP`     X′ → X′ + YP       (right adjunct)
  `head "w"`       X⁰ → w             (`head ""` for an empty head)
and one refutation command, `CannotSelect`, for goals of the form ¬ Selects c d.
-/

import XSyntax.Tactics

set_option XSyntax.treeView.enabled false

namespace XSyntax.Levels

open XSyntax

/-! # World I: inside the phrase -/

/-- **I.1 Words and heads.** Every tree starts from a word. A word enters the
    syntax at a head position, X⁰; the goal `N⁰` is an empty nominal head. -/
def phraseI_1 (ideas : Lexicon .N "ideas") :
    Parses .zero .N "ideas" := by
  head "ideas"

/-- **I.2 Projection.** The goal is now `NP`, but `head` only works at X⁰.
    X-bar theory says a word cannot be used directly as a phrase: even a
    one-word phrase goes through X⁰ → X′ → XP. Trying `head "ideas"` first
    shows the rejection. -/
def phraseI_2 (ideas : Lexicon .N "ideas") :
    Parses .two .N "ideas" := by
  nospec            -- XP to X′
  nocomp            -- X′ to X⁰
  head "ideas"

/-- **I.3 Function words: D is a category too.** Determiners such as *the*,
    *my*, *hers* head their own phrase, DP, and project exactly as nouns do. -/
def phraseI_3 (hers : Lexicon .D "hers") :
    Parses .two .D "hers" := by
  nospec
  nocomp
  head "hers"

/-- **I.4 Complements and selection.** *sees* is transitive: it selects a
    complement of category D. `complement YP` opens two goals, the head and
    the complement, and checks the selection licence at once. At `V′`, try
    `complement AP` first: the answer is
    `✗ selection violation: V does not select A`. -/
def phraseI_4 (sees : Lexicon .V "sees") (the : Lexicon .D "the")
    (cat : Lexicon .N "cat") :
    Parses .two .V "sees the cat" := by
  nospec
  complement DP     -- V selects D: licensed
  head "sees"
  nospec            -- *the cat*: D selects NP, the same mechanism one level down
  complement NP
  head "the"
  nospec
  nocomp
  head "cat"

/-- **I.5 Why it cannot be built.** No tree this time: prove that the licence
    for D selecting V does not exist, the structural reason behind strings like
    *the sleep*. `CannotSelect` checks every entry of the selection table and
    finds none that matches. On a licensed pair it refuses, in the same terms
    `complement` uses. -/
theorem phraseI_5 : ¬ Selects .D .V := by
  CannotSelect

/-- **I.6 Adjuncts: optional, and the bar level stays.** *my big house*. A
    complement is selected by its head and takes X⁰ to X′; an adjunct is not
    selected and leaves the bar level unchanged (X′ + adjunct is still X′), so
    adjuncts can stack (*big old red house*) or be absent. The adjunct must
    be a full phrase: *big* projects to AP first. -/
def phraseI_6 (my : Lexicon .D "my") (big : Lexicon .A "big")
    (house : Lexicon .N "house") :
    Parses .two .D "my big house" := by
  nospec
  complement NP
  head "my"
  nospec
  adjoinL AP        -- goals: AP and N′ (still N′)
  nospec
  nocomp
  head "big"
  nocomp
  head "house"

/-- **I.7 You decide.** *the strange dog*, without hints. *the* selects a
    nominal complement; *strange* modifies and is not selected. (In the review
    of July 2026 this level was noted to have the same structure as I.6.) -/
def phraseI_7 (the : Lexicon .D "the") (strange : Lexicon .A "strange")
    (dog : Lexicon .N "dog") :
    Parses .two .D "the strange dog" := by
  nospec
  complement NP
  head "the"
  nospec
  adjoinL AP
  nospec
  nocomp
  head "strange"
  nocomp
  head "dog"

/-- **I.8 Right adjuncts and adverbs.** *sleep quickly*. An adverb phrase
    adjoins to V′ as adjectives adjoin to N′, but on the right. Which side an
    adjunct takes is set by the language and the item; the X-bar geometry
    allows both. -/
def phraseI_8 (sleep : Lexicon .V "sleep") (quickly : Lexicon .Adv "quickly") :
    Parses .two .V "sleep quickly" := by
  nospec
  adjoinR AdvP      -- goals: V′ and AdvP
  nocomp
  head "sleep"
  nospec
  nocomp
  head "quickly"

/-! # World II: from phrase to clause -/

/-- **II.1 Meeting T.** *cats will sleep*. The head of the clause is not the
    verb but T, which carries tense; *will* is an overt T, so the clause is a
    TP. T selects VP, and the subject stands in the specifier of TP. (Subjects
    in Spec,TP is a mainstream analysis in generative grammar, not the only
    one.) -/
def phraseII_1 (cats : Lexicon .N "cats") (will : Lexicon .T "will")
    (sleep : Lexicon .V "sleep") :
    Parses .two .T "cats will sleep" := by
  specifier NP      -- goals: the subject NP and T′
  nospec
  nocomp
  head "cats"
  complement VP     -- T selects VP
  head "will"
  nospec
  nocomp
  head "sleep"

/-- **II.2 Meeting C.** *cats sleep* as a CP. Tense is always there, even when
    silent: present-tense T is an empty head in the same position as *will*.
    The clause also has an outer layer, C, as in *I think that cats sleep*; in a
    declarative main clause C is empty. C selects TP. -/
def phraseII_2 (cats : Lexicon .N "cats") (sleep : Lexicon .V "sleep")
    (nullC : Lexicon .C "") (nullT : Lexicon .T "") :
    Parses .two .C "cats sleep" := by
  nospec
  complement TP
  head ""           -- empty C
  specifier NP
  nospec
  nocomp
  head "cats"
  complement VP
  head ""           -- empty T
  nospec
  nocomp
  head "sleep"

/-- **II.3 Putting it together.** *the big dog sees the cat*, a full CP with
    empty C and T, a subject DP with an adjunct, and a transitive verb with an
    object DP. -/
def phraseII_3 (the : Lexicon .D "the") (big : Lexicon .A "big")
    (dog : Lexicon .N "dog") (sees : Lexicon .V "sees")
    (cat : Lexicon .N "cat")
    (nullC : Lexicon .C "") (nullT : Lexicon .T "") :
    Parses .two .C "the big dog sees the cat" := by
  nospec
  complement TP
  head ""
  specifier DP      -- the subject *the big dog*
  nospec
  complement NP
  head "the"
  nospec
  adjoinL AP
  nospec
  nocomp
  head "big"
  nocomp
  head "dog"
  complement VP     -- T′: empty present-tense T
  head ""
  nospec
  complement DP     -- *sees* selects its object
  head "sees"
  nospec
  complement NP
  head "the"
  nospec
  nocomp
  head "cat"

/-- **II.4 Colorless green ideas sleep furiously.** Chomsky's 1957 sentence:
    semantically absurd, syntactically well formed. No new commands. The
    subject is a DP with an empty D and two stacked left adjuncts; the
    predicate has a right-adjoined AdvP; C, T and D are all empty. The tree
    exists, so the sentence is grammatical. -/
def phraseII_4 (Colorless : Lexicon .A "Colorless") (green : Lexicon .A "green")
    (ideas : Lexicon .N "ideas") (sleep : Lexicon .V "sleep")
    (furiously : Lexicon .Adv "furiously")
    (nullC : Lexicon .C "") (nullD : Lexicon .D "") (nullT : Lexicon .T "") :
    Parses .two .C "Colorless green ideas sleep furiously" := by
  nospec
  complement TP
  head ""
  specifier DP
  nospec
  complement NP
  head ""
  nospec
  adjoinL AP
  nospec
  nocomp
  head "Colorless"
  adjoinL AP
  nospec
  nocomp
  head "green"
  nocomp
  head "ideas"
  complement VP
  head ""
  nospec
  adjoinR AdvP
  nocomp
  head "sleep"
  nospec
  nocomp
  head "furiously"

end XSyntax.Levels
