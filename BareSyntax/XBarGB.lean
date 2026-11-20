/-
Level 3 grammar: `xbarGB` — X-bar theory with GB modules, as a Bare Grammar.

Categories are pairs ⟨head category, bar level⟩. Nothing about X-bar lives in a
constructor. The X-bar schema is five rules with variables X and Y over head
categories. Each is a condition-domain rule (`FRule`): its domain is fixed by
the pattern on its right-hand side (X⁰, X′, YP) and by a condition stated with
GB's lexical information.

* X′ → X⁰       X takes no complement.
* XP → X′       X needs no specifier (EPP: T needs one).
* XP → YP X′    YP is the specifier of X; a DP needs Case from X.
* X′ → X⁰ YP    X c-selects Y; a DP needs Case from X. When X is T, the affix
                in T⁰ lowers onto the verb (Infl lowering) instead of
                concatenating: see + -s = sees.
* X′ → X′ YP    YP is an adjunct of X. This fragment lists no adjuncts.

GB data: c-selection (D selects NP, V selects DP, T selects VP); Case (V assigns
accusative to its complement, finite T nominative to its specifier); EPP (T
needs a specifier). Because a DP is accepted only where Case is assigned, the
Case Filter is a property of the rules' domains.

What is out: theta theory, binding, movement chains.
-/
import BareSyntax.Basic

namespace BareSyntax

inductive Pos | N | D | V | T
  deriving DecidableEq, Repr

inductive Bar | zero | one | two
  deriving DecidableEq, Repr

/-- An X-bar category: head category and bar level. Shown as N⁰, N′, NP. -/
structure XCat where
  pos : Pos
  bar : Bar
  deriving DecidableEq, Repr

def Pos.text : Pos → String
  | .N => "N" | .D => "D" | .V => "V" | .T => "T"

def XCat.text (c : XCat) : String :=
  c.pos.text ++ (match c.bar with | .zero => "⁰" | .one => "′" | .two => "P")

def x0 (p : Pos) : XCat := ⟨p, .zero⟩
def x1 (p : Pos) : XCat := ⟨p, .one⟩
def xp (p : Pos) : XCat := ⟨p, .two⟩

/-! ## GB's lexical information (data) -/

/-- c-selection: (head, category of its complement phrase). -/
def cSelection : List (Pos × Pos) := [(.D, .N), (.V, .D), (.T, .V)]

/-- Specifiers: (head, category of its specifier phrase). -/
def specifiers : List (Pos × Pos) := [(.T, .D)]

/-- EPP: heads whose phrase must have a specifier. -/
def epp : List Pos := [.T]

/-- Case: heads that assign Case to their complement (V: accusative) and to
    their specifier (finite T: nominative). -/
def caseToComplement : List Pos := [.V]
def caseToSpecifier : List Pos := [.T]

/-- Adjuncts: (head, category of the adjoined phrase). None in this fragment. -/
def adjuncts : List (Pos × Pos) := []

/-! ## Morphology for Infl lowering -/

def attachAffix (verb affix : String) : String :=
  match verb, affix with
  | "see", "-s" => "sees"
  | v, _ => v ++ "s"

/-- The affix in T⁰ lowers onto the first word of VP (the verb). -/
def lowerAffix : List (List String) → List String
  | [[affix], v :: rest] => attachAffix v affix :: rest
  | xs => xs.flatten

/-! ## The X-bar schema: five rules with variables -/

/-- A DP needs Case from the head X. -/
def caseOK (assigners : List Pos) (x y : Pos) : Bool := y != .D || assigners.contains x

def barRule : FRule XCat Unit where
  name := "X′ → X⁰  [X takes no complement]"
  apply := fun _ ins => match ins with
    | [(s, ⟨x, .zero⟩)] => if cSelection.any (·.1 == x) then none else some (s, x1 x)
    | _ => none

def projRule : FRule XCat Unit where
  name := "XP → X′  [X needs no specifier (EPP)]"
  apply := fun _ ins => match ins with
    | [(s, ⟨x, .one⟩)] => if epp.contains x then none else some (s, xp x)
    | _ => none

def specRule : FRule XCat Unit where
  name := "XP → YP X′  [YP is the specifier of X; a DP needs Case from X]"
  apply := fun _ ins => match ins with
    | [(s₁, ⟨y, .two⟩), (s₂, ⟨x, .one⟩)] =>
      if specifiers.contains (x, y) && caseOK caseToSpecifier x y then some (s₁ ++ s₂, xp x) else none
    | _ => none

def compRule : FRule XCat Unit where
  name := "X′ → X⁰ YP  [X c-selects Y; a DP needs Case from X; T's affix lowers onto V]"
  apply := fun _ ins => match ins with
    | [(s₁, ⟨x, .zero⟩), (s₂, ⟨y, .two⟩)] =>
      if cSelection.contains (x, y) && caseOK caseToComplement x y then
        some (if x == .T then lowerAffix [s₁, s₂] else s₁ ++ s₂, x1 x)
      else none
    | _ => none

def adjRule : FRule XCat Unit where
  name := "X′ → X′ YP  [YP is an adjunct of X]"
  apply := fun _ ins => match ins with
    | [(s₁, ⟨x, .one⟩), (s₂, ⟨y, .two⟩)] =>
      if adjuncts.contains (x, y) then some (s₁ ++ s₂, x1 x) else none
    | _ => none

def xbarGB : BareGrammar where
  Cat     := XCat
  decCat  := inferInstance
  lexicon := [(["the"], x0 .D), (["cat"], x0 .N), (["dog"], x0 .N),
              (["see"], x0 .V), (["-s"], x0 .T)]
  rules   := []
  Arg     := Unit
  frules  := [barRule, projRule, specRule, compRule, adjRule]

end BareSyntax
