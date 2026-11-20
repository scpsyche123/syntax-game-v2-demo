/-
Bare Grammar — the base language.

Copied from `scpsyche123/syntax-game`, `BareSyntax/Basic.lean` (merged 2026-07-28),
with ONE additive extension, marked [EXT] below. Nothing in the original part
was changed.

The whole grammar is DATA: a category type, a finite lexicon, and a rule table.
No theory lives in the constructors. Generation is the inductive `Deriv`;
grammaticality is `CanYield := Nonempty (Deriv …)`.

Two kinds of rule:
* `Rule` (original): the domain is explicit data (`posCat`, one required
  category per input position). Used by the linear grammar and by X-bar + GB.
* `FRule` [EXT]: the domain is a decidable condition, written inside `apply`
  (a partial function: `none` outside the domain). A family of such functions
  is indexed by an argument `a : G.Arg`; choosing a rule means choosing the
  function AND its argument, so ambiguity still lives only in rule selection.
  Needed when categories are structured objects and no finite list of
  categories can describe the domain (MERGE on workspaces).
-/

namespace BareSyntax

/-- An expression is a string (list of lexemes) paired with a category. -/
abbrev Expr (Cat : Type) := List String × Cat

/-- A rule whose domain is explicit data (original form). -/
structure Rule (Cat : Type) where
  name    : String
  posCat  : List Cat                           -- required category at each position
  result  : Cat                                -- output category
  build   : List (List String) → List String   -- how the output string is assembled

/-- [EXT] A rule whose domain is a decidable condition: `apply a inputs` is
    `none` outside the domain. `a` selects one function from the family. -/
structure FRule (Cat Arg : Type) where
  name  : String
  apply : Arg → List (Expr Cat) → Option (Expr Cat)

/-- A grammar as data. `Arg`/`frules` [EXT] default to "no such rules", so every
    grammar written for the original base is still a grammar here. -/
structure BareGrammar where
  Cat     : Type
  decCat  : DecidableEq Cat
  lexicon : List (Expr Cat)
  rules   : List (Rule Cat)
  Arg     : Type := Unit
  frules  : List (FRule Cat Arg) := []

instance (priority := low) instDecEqCat (G : BareGrammar) : DecidableEq G.Cat := G.decCat

/-- Apply a data-domain rule: succeeds iff the input categories are exactly
    `r.posCat`; then builds the string and stamps `r.result`. -/
def applyRule (G : BareGrammar) (r : Rule G.Cat)
    (inputs : List (Expr G.Cat)) : Option (Expr G.Cat) :=
  haveI := G.decCat
  if inputs.map Prod.snd = r.posCat then
    some (r.build (inputs.map Prod.fst), r.result)
  else
    none

mutual
/-- Generation. An expression is derivable if it is a lexicon entry (`lex`),
    the result of a data-domain rule on derivable inputs (`app`), or [EXT] the
    result of a condition-domain rule on derivable inputs (`fapp`). -/
inductive Deriv (G : BareGrammar) : Expr G.Cat → Type where
  | lex {e : Expr G.Cat} : e ∈ G.lexicon → Deriv G e
  | app {r : Rule G.Cat} {inputs : List (Expr G.Cat)} {out : Expr G.Cat} :
      r ∈ G.rules → DerivList G inputs → applyRule G r inputs = some out → Deriv G out
  | fapp {r : FRule G.Cat G.Arg} (a : G.Arg) {inputs : List (Expr G.Cat)} {out : Expr G.Cat} :
      r ∈ G.frules → DerivList G inputs → r.apply a inputs = some out → Deriv G out

inductive DerivList (G : BareGrammar) : List (Expr G.Cat) → Type where
  | nil  : DerivList G []
  | cons {e : Expr G.Cat} {es : List (Expr G.Cat)} :
      Deriv G e → DerivList G es → DerivList G (e :: es)
end

/-- Grammaticality: string `s` yields category `C` iff some derivation exists. -/
def CanYield (G : BareGrammar) (s : List String) (C : G.Cat) : Prop :=
  Nonempty (Deriv G (s, C))

end BareSyntax
