/-
Level 3 grammar: `xbarGB` — X-bar theory with GB modules, as a Bare Grammar.

Categories are triples ⟨head category, bar level, waiting phrase⟩. Nothing about
X-bar lives in a constructor. The rules are the X-bar schema, five rules with
variables X and Y over head categories, plus Move α. Each is a condition-domain
rule (`FRule`): its domain is fixed by the pattern on its left-hand side and by a
condition stated with GB's lexical information.

* X⁰ → X′              X takes no complement.
* X′ → XP              X needs no specifier (EPP: T needs one; θ: V needs its
                       external argument).
* YP X′ → XP           YP is the specifier of X. A DP that gets no Case there
                       (the subject in Spec-VP) leaves a trace: its string is
                       held in the category, waiting to move.
* X⁰ YP → X′           X c-selects Y; a DP needs Case from X. When X is T, the
                       suffix in T⁰ lowers onto the verb: see + -s = sees.
* X′ YP → X′           YP is an adjunct of X. This fragment lists no adjuncts.
* Move α: YP X′ → XP   YP is the phrase waiting inside X′; it lands in the
                       specifier of X, where a DP needs Case from X.

GB data: c-selection (C selects TP, T selects VP, V selects DP, D selects NP);
the subject is merged in Spec-VP (VP-internal subject, Koopman & Sportiche
1991); Case (V assigns accusative to its complement, finite T nominative to its
specifier); EPP (T needs a specifier, filled here only by Move α); θ (V assigns
an external θ-role, so VP needs its subject). C is empty.

What is out: the rest of theta theory, binding, chains beyond one waiting phrase.
-/
import BareSyntax.Basic

namespace BareSyntax

inductive Pos | N | D | V | T | C
  deriving DecidableEq, Repr

inductive Bar | zero | one | two
  deriving DecidableEq, Repr

/-- An X-bar category: head category, bar level, and the phrase (string and
    head category) that waits inside it to move, if any. Shown as N⁰, N′, NP,
    and VP/DP for a VP with a waiting DP. -/
structure XCat where
  pos : Pos
  bar : Bar
  mover : Option (List String × Pos) := none
  deriving DecidableEq, Repr

def Pos.text : Pos → String
  | .N => "N" | .D => "D" | .V => "V" | .T => "T" | .C => "C"

def XCat.text (c : XCat) : String :=
  c.pos.text ++ (match c.bar with | .zero => "⁰" | .one => "′" | .two => "P") ++
    (match c.mover with | some (_, p) => "/" ++ p.text ++ "P" | none => "")

def x0 (p : Pos) : XCat := ⟨p, .zero, none⟩
def x1 (p : Pos) : XCat := ⟨p, .one, none⟩
def xp (p : Pos) : XCat := ⟨p, .two, none⟩

/-! ## GB's lexical information (data) -/

/-- c-selection: (head, category of its complement phrase). -/
def cSelection : List (Pos × Pos) := [(.C, .T), (.T, .V), (.V, .D), (.D, .N)]

/-- Specifiers merged in place: (head, category of its specifier phrase).
    The subject is merged in Spec-VP. -/
def specifiers : List (Pos × Pos) := [(.V, .D)]

/-- Landing sites of Move α: (head, category of the phrase that lands in its
    specifier). The subject moves to Spec-TP. -/
def landingSites : List (Pos × Pos) := [(.T, .D)]

/-- EPP: heads whose phrase must have a specifier. -/
def epp : List Pos := [.T]

/-- θ: heads that assign an external θ-role, so their specifier must be filled
    (see takes a subject). -/
def externalTheta : List Pos := [.V]

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

/-- Suffix lowering: the suffix in T⁰ lowers onto the first word of VP (the verb). -/
def lowerAffix : List (List String) → List String
  | [[affix], v :: rest] => attachAffix v affix :: rest
  | xs => xs.flatten

/-! ## The X-bar schema and Move α -/

/-- A DP needs Case from the head X. -/
def caseOK (assigners : List Pos) (x y : Pos) : Bool := y != .D || assigners.contains x

abbrev Mover := Option (List String × Pos)

/-- Two daughters may carry at most one waiting phrase between them. -/
def oneMover : Mover → Mover → Option Mover
  | none, m => some m
  | m, none => some m
  | some _, some _ => none

def barRule : FRule XCat Unit where
  name := "X⁰ → X′  [X takes no complement]"
  apply := fun _ ins => match ins with
    | [(s, ⟨x, .zero, m⟩)] => if cSelection.any (·.1 == x) then none else some (s, ⟨x, .one, m⟩)
    | _ => none

def projRule : FRule XCat Unit where
  name := "X′ → XP  [X needs no specifier (EPP: T needs one; θ: V needs its external argument)]"
  apply := fun _ ins => match ins with
    | [(s, ⟨x, .one, m⟩)] => if epp.contains x || externalTheta.contains x then none else some (s, ⟨x, .two, m⟩)
    | _ => none

def specRule : FRule XCat Unit where
  name := "YP X′ → XP  [YP is the specifier of X; a DP that gets no Case there leaves a trace and waits to move]"
  apply := fun _ ins => match ins with
    | [(s₁, ⟨y, .two, none⟩), (s₂, ⟨x, .one, none⟩)] =>
      if specifiers.contains (x, y) then
        if caseOK caseToSpecifier x y then some (s₁ ++ s₂, ⟨x, .two, none⟩)
        else some (s₂, ⟨x, .two, some (s₁, y)⟩)
      else none
    | _ => none

def compRule : FRule XCat Unit where
  name := "X⁰ YP → X′  [X c-selects Y; a DP needs Case from X; T's suffix lowers onto V]"
  apply := fun _ ins => match ins with
    | [(s₁, ⟨x, .zero, none⟩), (s₂, ⟨y, .two, m⟩)] =>
      if cSelection.contains (x, y) && caseOK caseToComplement x y then
        some (if x == .T then lowerAffix [s₁, s₂] else s₁ ++ s₂, ⟨x, .one, m⟩)
      else none
    | _ => none

def adjRule : FRule XCat Unit where
  name := "X′ YP → X′  [YP is an adjunct of X]"
  apply := fun _ ins => match ins with
    | [(s₁, ⟨x, .one, m₁⟩), (s₂, ⟨y, .two, m₂⟩)] =>
      if adjuncts.contains (x, y) then (oneMover m₁ m₂).map fun m => (s₁ ++ s₂, ⟨x, .one, m⟩)
      else none
    | _ => none

def moveRule : FRule XCat Unit where
  name := "Move α: YP X′ → XP  [YP is the phrase waiting inside X′; it lands in the specifier of X, where a DP needs Case from X]"
  apply := fun _ ins => match ins with
    | [(s₁, ⟨y, .two, none⟩), (s₂, ⟨x, .one, some (sm, pm)⟩)] =>
      if sm == s₁ && pm == y && landingSites.contains (x, y) && caseOK caseToSpecifier x y then
        some (s₁ ++ s₂, ⟨x, .two, none⟩)
      else none
    | _ => none

def xbarGB : BareGrammar where
  Cat     := XCat
  decCat  := inferInstance
  lexicon := [(["the"], x0 .D), (["cat"], x0 .N), (["dog"], x0 .N),
              (["see"], x0 .V), (["-s"], x0 .T), ([], x0 .C)]
  rules   := []
  Arg     := Unit
  frules  := [barRule, projRule, specRule, compRule, adjRule, moveRule]

end BareSyntax
