/-
# Bare Grammar demo — step through in VS Code

Open this folder (`playground/`) in VS Code with the Lean 4 extension.
Put the cursor at the end of each line inside a proof; the infoview shows the
hypotheses (expressions built so far) and the goal.

These are the three levels of the online demo, without the game interface.
-/
import BareSyntax

set_option linter.unusedVariables false

open BareSyntax

/-! ## Level 1 — a linear grammar

`linear₁`: lexicon a : D, very : Adv, good : A, day : N;
Rule 1: Adv A → A, Rule 2: A N → N, Rule 3: D N → D. -/
example (a : (["a"], Linear1Cat.D) ∈ linear₁.lexicon)
    (very : (["very"], Linear1Cat.Adv) ∈ linear₁.lexicon)
    (good : (["good"], Linear1Cat.A) ∈ linear₁.lexicon)
    (day : (["day"], Linear1Cat.N) ∈ linear₁.lexicon) :
    CanYield linear₁ ["a", "very", "good", "day"] .D := by
  rule "Adv A -> A" very good
  rule "A N -> N" very_good_A day
  rule "D N -> D" a very_good_day_N

/-! ## Not in the language: ⟨a very day, D⟩

`very` is an Adv, and the only rule that takes an Adv is Rule 1, which needs an A
after it. Every attempt fails; uncomment a line to see one. (No proof of
impossibility here — this is a place to try.) -/
example (a : (["a"], Linear1Cat.D) ∈ linear₁.lexicon)
    (very : (["very"], Linear1Cat.Adv) ∈ linear₁.lexicon)
    (day : (["day"], Linear1Cat.N) ∈ linear₁.lexicon) :
    CanYield linear₁ ["a", "very", "day"] .D := by
  -- rule "Adv A -> A" very day
  -- rule "A N -> N" very day
  -- rule "D N -> D" a very
  sorry

/-! ## Overgeneration — `linear₂` adds Rule 4: D N → N

With Rule 4 alone it derives a string no speaker accepts, as an N. -/
example (a : (["a"], Linear1Cat.D) ∈ linear₂.lexicon)
    (the : (["the"], Linear1Cat.D) ∈ linear₂.lexicon)
    (this : (["this"], Linear1Cat.D) ∈ linear₂.lexicon)
    (dog : (["dog"], Linear1Cat.N) ∈ linear₂.lexicon) :
    CanYield linear₂ ["a", "a", "the", "this", "dog"] .N := by
  rule "D N -> N" this dog
  rule "D N -> N" the this_dog_N
  rule "D N -> N" a the_this_dog_N
  rule "D N -> N" a a_the_this_dog_N

/-! ## Level 4 — X-bar theory with GB, Turkish (head-final)

*Kedi köpeği görüyor* — cat dog-ACC see-PROG — 'The cat sees the dog.'
The rules are the X-bar schema with variables X and Y, plus Move α, produced from
parameters; Turkish sets the head parameter to final. GB's data (c-selection, Case,
EPP, θ) are conditions on the rules' domains. The subject is merged in Spec-VP, gets
no Case there, waits (VP/NP), and Move α puts it in Spec-TP. -/
example (kedi : (["kedi"], x0 .N) ∈ xbarTR.lexicon)
    (köpek : (["köpek"], x0 .N) ∈ xbarTR.lexicon)
    (gör : (["gör"], x0 .V) ∈ xbarTR.lexicon)
    (yor : (["-Iyor"], x0 .T) ∈ xbarTR.lexicon)
    (c : (([] : List String), x0 .C) ∈ xbarTR.lexicon) :
    CanYield xbarTR ["kedi", "köpeği", "görüyor"] (xp .C) := by
  rule "X0 -> X'" kedi
  rule "X' -> XP" kedi_N'
  rule "X0 -> X'" köpek
  rule "X' -> XP" köpek_N'
  rule "YP X0 -> X'" köpek_NP gör
  rule "YP X' -> XP" kedi_NP köpeği_gör_V'
  rule "YP X0 -> X'" köpeği_gör_VP_NP yor
  rule "Move α: YP X' -> XP" kedi_NP köpeği_görüyor_T'_NP
  rule "YP X0 -> X'" kedi_köpeği_görüyor_TP c
  rule "X' -> XP" kedi_köpeği_görüyor_C'

/-! The same schema with the head parameter set to initial, and an English lexicon. -/
example (the : (["the"], x0 .D) ∈ xbarEN.lexicon)
    (cat : (["cat"], x0 .N) ∈ xbarEN.lexicon)
    (dog : (["dog"], x0 .N) ∈ xbarEN.lexicon)
    (see : (["see"], x0 .V) ∈ xbarEN.lexicon)
    (s : (["-s"], x0 .T) ∈ xbarEN.lexicon)
    (c : (([] : List String), x0 .C) ∈ xbarEN.lexicon) :
    CanYield xbarEN ["the", "cat", "sees", "the", "dog"] (xp .C) := by
  rule "X0 -> X'" cat
  rule "X' -> XP" cat_N'
  rule "X0 YP -> X'" the cat_NP
  rule "X' -> XP" the_cat_D'
  rule "X0 -> X'" dog
  rule "X' -> XP" dog_N'
  rule "X0 YP -> X'" the dog_NP
  rule "X' -> XP" the_dog_D'
  rule "X0 YP -> X'" see the_dog_DP
  rule "YP X' -> XP" the_cat_DP see_the_dog_V'
  rule "X0 YP -> X'" s see_the_dog_VP_DP
  rule "Move α: YP X' -> XP" the_cat_DP sees_the_dog_T'_DP
  rule "X0 YP -> X'" c the_cat_sees_the_dog_TP
  rule "X' -> XP" the_cat_sees_the_dog_C'

/-! ## Level 5 — the Minimalist Program, workspace era, Swahili

*Mtoto atalala* — m-toto a-ta-lala — 1-child 1SM-FUT-sleep — 'The child will sleep.'
Externalization (order, the higher copy, prefixes joined) and the interface conditions
are checked automatically after the last MERGE. -/
example : MP.Converges ["mtoto", "atalala"] := by
  select m toto ata v lala
  merge m toto
  merge v lala
  merge nP vP
  merge ata {nP, vP}     -- one object left, but {nP, vP} has no label
  merge nP TP            -- Internal MERGE: the lower nP becomes a copy

/-! ## Rejections

Uncomment the first line to see how the grammar rejects a step. -/
example (very : (["very"], Linear1Cat.Adv) ∈ linear₁.lexicon)
    (good : (["good"], Linear1Cat.A) ∈ linear₁.lexicon) :
    CanYield linear₁ ["very", "good"] .A := by
  -- rule "A N -> N" very good        -- Rule 2 needs an A and an N
  rule "Adv A -> A" very good
