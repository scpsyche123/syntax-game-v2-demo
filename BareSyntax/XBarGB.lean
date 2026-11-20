/-
Level 4 grammar: X-bar theory with GB modules, as a Bare Grammar.

Categories are triples ⟨head category, bar level, waiting phrase⟩. Nothing about
X-bar lives in a constructor. The rules are the X-bar schema, five rules with
variables X and Y over head categories, plus Move α. Each is a condition-domain
rule (`FRule`): its domain is fixed by the pattern on its left-hand side and by a
condition stated with GB's lexical information.

The schema is a FUNCTION of `GBParams`: what varies between languages in this
fragment is GB's lexical information and one parameter of the schema itself,
the head direction. Two instances:

* `xbarEN` — English, head-initial: X⁰ YP → X′. *the cat sees the dog*.
* `xbarTR` — Turkish, head-final: YP X⁰ → X′. *kedi köpeği görüyor*
  (cat dog-ACC see-PROG, "the cat sees / is seeing the dog"). Turkish has no
  articles; nominal arguments here are NPs.

The rules (head-initial form of Rule 4 in brackets):

* X⁰ → X′              X takes no complement.
* X′ → XP              X needs no specifier (EPP: T needs one; θ: V needs its
                       external argument).
* YP X′ → XP           YP is the specifier of X. A nominal argument that gets no
                       Case there (the subject in Spec-VP) leaves a trace: its
                       string is held in the category, waiting to move.
* YP X⁰ → X′ (X⁰ YP)   X c-selects Y; a nominal argument needs Case from X. V's
                       accusative is spelled on its complement (Turkish -I).
                       When X is T, T's suffix joins the verb: see + -s = sees,
                       gör + -Iyor = görüyor.
* X′ YP → X′           YP is an adjunct of X. This fragment lists no adjuncts.
* Move α: YP X′ → XP   YP is the phrase waiting inside X′; it lands in the
                       specifier of X, where a nominal argument needs Case.

GB data shared by both: the subject is merged in Spec-VP (VP-internal subject,
Koopman & Sportiche 1991); V assigns accusative to its complement, finite T
nominative to its specifier; EPP; C is empty.

Morphophonology (Turkish vowel harmony, k → ğ before a vowel; English -s) is
given by small tables for the words of this fragment.

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

abbrev Mover := Option (List String × Pos)

/-! ## What varies between languages -/

structure GBParams where
  /-- The head-direction parameter: does the head follow its complement? -/
  headFinal : Bool
  /-- Category of nominal arguments (D in English, N in Turkish), and how the
      rule names refer to them. -/
  nominal : Pos
  argText : String
  /-- c-selection: (head, category of its complement phrase). -/
  cSelection : List (Pos × Pos)
  /-- Specifiers merged in place: (head, category of the specifier phrase). -/
  specifiers : List (Pos × Pos)
  /-- Landing sites of Move α. -/
  landingSites : List (Pos × Pos)
  /-- EPP: heads whose phrase must have a specifier. -/
  epp : List Pos
  /-- θ: heads that assign an external θ-role, so their specifier is filled. -/
  externalTheta : List Pos
  /-- Case: heads that assign Case to their complement / to their specifier. -/
  caseToComplement : List Pos
  caseToSpecifier : List Pos
  /-- Adjuncts: (head, category of the adjoined phrase). -/
  adjuncts : List (Pos × Pos)
  /-- How T's suffix joins the verb. -/
  attachSuffix : String → String → String
  /-- How V's accusative is spelled on its complement. -/
  accusative : List String → List String

/-! ## Morphology of the two fragments -/

def attachEN : String → String → String
  | "see", "-s" => "sees"
  | v, _ => v ++ "s"

def attachTR : String → String → String
  | "gör", "-Iyor" => "görüyor"
  | v, s => v ++ s

def accusativeWordTR : String → String
  | "köpek" => "köpeği"
  | "kedi" => "kediyi"
  | w => w ++ "i"

def accusativeTR (ws : List String) : List String :=
  match ws.reverse with
  | w :: rest => (accusativeWordTR w :: rest).reverse
  | [] => []

/-! ## The X-bar schema and Move α, as functions of the parameters -/

/-- A nominal argument needs Case from the head X. -/
def caseOK (p : GBParams) (assigners : List Pos) (x y : Pos) : Bool :=
  y != p.nominal || assigners.contains x

/-- Head and complement in the order the head parameter fixes. -/
def headOrder (p : GBParams) (head comp : List String) : List String :=
  if p.headFinal then comp ++ head else head ++ comp

/-- T⁰ with its VP: the suffix in T⁰ joins the verb, the VP word next to T. -/
def joinTV (p : GBParams) (sT sVP : List String) : List String :=
  if p.headFinal then
    match sT, sVP.reverse with
    | [a], v :: rest => (p.attachSuffix v a :: rest).reverse
    | _, _ => sVP ++ sT
  else
    match sT, sVP with
    | [a], v :: rest => p.attachSuffix v a :: rest
    | _, _ => sT ++ sVP

def barRule (p : GBParams) : FRule XCat Unit where
  name := "X⁰ → X′  [X takes no complement]"
  apply := fun _ ins => match ins with
    | [(s, ⟨x, .zero, m⟩)] => if p.cSelection.any (·.1 == x) then none else some (s, ⟨x, .one, m⟩)
    | _ => none

def projRule (p : GBParams) : FRule XCat Unit where
  name := "X′ → XP  [X needs no specifier (EPP: T needs one; θ: V needs its external argument)]"
  apply := fun _ ins => match ins with
    | [(s, ⟨x, .one, m⟩)] =>
      if p.epp.contains x || p.externalTheta.contains x then none else some (s, ⟨x, .two, m⟩)
    | _ => none

def specRule (p : GBParams) : FRule XCat Unit where
  name := s!"YP X′ → XP  [YP is the specifier of X; {p.argText} that gets no Case there leaves a trace and waits to move]"
  apply := fun _ ins => match ins with
    | [(s₁, ⟨y, .two, none⟩), (s₂, ⟨x, .one, none⟩)] =>
      if p.specifiers.contains (x, y) then
        if caseOK p p.caseToSpecifier x y then some (s₁ ++ s₂, ⟨x, .two, none⟩)
        else some (s₂, ⟨x, .two, some (s₁, y)⟩)
      else none
    | _ => none

/-- Rule 4 on (head, complement), whatever their order in the input list. -/
def compApply (p : GBParams) : (List String × XCat) → (List String × XCat) → Option (List String × XCat)
  | (s₁, ⟨x, .zero, none⟩), (s₂, ⟨y, .two, m⟩) =>
    if p.cSelection.contains (x, y) && caseOK p p.caseToComplement x y then
      let c := if x == .V && y == p.nominal then p.accusative s₂ else s₂
      some (if x == .T then joinTV p s₁ c else headOrder p s₁ c, ⟨x, .one, m⟩)
    else none
  | _, _ => none

def compRule (p : GBParams) : FRule XCat Unit where
  name := (if p.headFinal then "YP X⁰ → X′" else "X⁰ YP → X′") ++
    s!"  [X c-selects Y; {p.argText} needs Case from X; T's suffix joins V]"
  apply := fun _ ins => match ins with
    | [a, b] => if p.headFinal then compApply p b a else compApply p a b
    | _ => none

def adjRule (p : GBParams) : FRule XCat Unit where
  name := "X′ YP → X′  [YP is an adjunct of X]"
  apply := fun _ ins => match ins with
    | [(s₁, ⟨x, .one, none⟩), (s₂, ⟨y, .two, none⟩)] =>
      if p.adjuncts.contains (x, y) then some (s₁ ++ s₂, ⟨x, .one, none⟩) else none
    | _ => none

def moveRule (p : GBParams) : FRule XCat Unit where
  name := s!"Move α: YP X′ → XP  [YP is the phrase waiting inside X′; it lands in the specifier of X, where {p.argText} needs Case from X]"
  apply := fun _ ins => match ins with
    | [(s₁, ⟨y, .two, none⟩), (s₂, ⟨x, .one, some (sm, pm)⟩)] =>
      if sm == s₁ && pm == y && p.landingSites.contains (x, y) && caseOK p p.caseToSpecifier x y then
        some (s₁ ++ s₂, ⟨x, .two, none⟩)
      else none
    | _ => none

def xbarSchema (p : GBParams) : List (FRule XCat Unit) :=
  [barRule p, projRule p, specRule p, compRule p, adjRule p, moveRule p]

/-! ## Two settings -/

def english : GBParams where
  headFinal := false
  nominal := .D
  argText := "a DP"
  cSelection := [(.C, .T), (.T, .V), (.V, .D), (.D, .N)]
  specifiers := [(.V, .D)]
  landingSites := [(.T, .D)]
  epp := [.T]
  externalTheta := [.V]
  caseToComplement := [.V]
  caseToSpecifier := [.T]
  adjuncts := []
  attachSuffix := attachEN
  accusative := id

def turkish : GBParams where
  headFinal := true
  nominal := .N
  argText := "an NP"
  cSelection := [(.C, .T), (.T, .V), (.V, .N)]
  specifiers := [(.V, .N)]
  landingSites := [(.T, .N)]
  epp := [.T]
  externalTheta := [.V]
  caseToComplement := [.V]
  caseToSpecifier := [.T]
  adjuncts := []
  attachSuffix := attachTR
  accusative := accusativeTR

def xbarEN : BareGrammar where
  Cat     := XCat
  decCat  := inferInstance
  lexicon := [(["the"], x0 .D), (["cat"], x0 .N), (["dog"], x0 .N),
              (["see"], x0 .V), (["-s"], x0 .T), ([], x0 .C)]
  rules   := []
  Arg     := Unit
  frules  := xbarSchema english

def xbarTR : BareGrammar where
  Cat     := XCat
  decCat  := inferInstance
  lexicon := [(["kedi"], x0 .N), (["köpek"], x0 .N), (["gör"], x0 .V),
              (["-Iyor"], x0 .T), ([], x0 .C)]
  rules   := []
  Arg     := Unit
  frules  := xbarSchema turkish

end BareSyntax
