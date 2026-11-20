/-
Level 1 grammar: `linear₁` — a linear (flat) grammar.

Copied from `scpsyche123/syntax-game`, `BareSyntax/Linear.lean` (grammar part
only; the negative-proof material is not needed for this demo).

Lexicon a:D, very:Adv, good:A, day:N. Rule table `N → D (A) N`, written as two
rules because the optional A is expanded.
-/
import BareSyntax.Basic

namespace BareSyntax

inductive Linear1Cat | D | Adv | A | N
  deriving DecidableEq, Repr

def ruleDN : Rule Linear1Cat :=
  { name := "N → D N",   posCat := [.D, .N],     result := .N, build := List.flatten }
def ruleDAN : Rule Linear1Cat :=
  { name := "N → D A N", posCat := [.D, .A, .N], result := .N, build := List.flatten }

def linear₁ : BareGrammar where
  Cat     := Linear1Cat
  decCat  := inferInstance
  lexicon := [(["a"], .D), (["very"], .Adv), (["good"], .A), (["day"], .N)]
  rules   := [ruleDN, ruleDAN]

end BareSyntax
