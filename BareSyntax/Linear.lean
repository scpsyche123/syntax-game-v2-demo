/-
Levels 1–3 grammars: linear (string-concatenating) grammars.

`linear₁`
  Lexicon: a : D, very : Adv, good : A, day : N
  Rule 1: A → Adv A
  Rule 2: N → A N
  Rule 3: D → D N
  It derives ⟨a very good day, D⟩ in three steps, and cannot derive
  ⟨a very day, D⟩: `very` can only combine with an A on its right.

`linear₂` = `linear₁` plus the, this, dog : D/N and
  Rule 4: N → D N
  The new rule lets determiners stack: it derives ⟨a a the this dog, D⟩.
  The grammar now generates too much.

Rules are written in phrase-structure notation (mother → daughters); as
functions they read right to left: Rule 1 takes an Adv and an A and gives an A.
-/
import BareSyntax.Basic

namespace BareSyntax

inductive Linear1Cat | D | Adv | A | N
  deriving DecidableEq, Repr

def rule1 : Rule Linear1Cat :=
  { name := "A → Adv A", posCat := [.Adv, .A], result := .A, build := List.flatten }
def rule2 : Rule Linear1Cat :=
  { name := "N → A N",   posCat := [.A, .N],   result := .N, build := List.flatten }
def rule3 : Rule Linear1Cat :=
  { name := "D → D N",   posCat := [.D, .N],   result := .D, build := List.flatten }
def rule4 : Rule Linear1Cat :=
  { name := "N → D N",   posCat := [.D, .N],   result := .N, build := List.flatten }

def linear₁ : BareGrammar where
  Cat     := Linear1Cat
  decCat  := inferInstance
  lexicon := [(["a"], .D), (["very"], .Adv), (["good"], .A), (["day"], .N)]
  rules   := [rule1, rule2, rule3]

def linear₂ : BareGrammar where
  Cat     := Linear1Cat
  decCat  := inferInstance
  lexicon := [(["a"], .D), (["very"], .Adv), (["good"], .A), (["day"], .N),
              (["the"], .D), (["this"], .D), (["dog"], .N)]
  rules   := [rule1, rule2, rule3, rule4]

end BareSyntax
