/-
Level 2 grammar: `xbarGB` — X-bar theory with GB modules, as a Bare Grammar.

Categories are pairs ⟨head category, bar level⟩. Nothing about X-bar lives in a
constructor: the X-bar schema is a FUNCTION that turns GB's lexical
information (c-selection, Case positions) into an ordinary rule table.

What is in:
* X-bar schema: X′ → X⁰ (no complement), X′ → X⁰ YP (complement),
  XP → X′ (no specifier), XP → YP X′ (specifier).
* c-selection: D selects NP, V selects DP, T selects VP.
* Case: a DP can only stand where Case is assigned — complement of V
  (accusative) and specifier of finite T (nominative). No other rule takes a
  DP, so the Case Filter is a property of the rule table.
* EPP: TP must have a specifier, so there is no rule TP → T′.
* Infl lowering (affix hopping): the rule T′ → T⁰ VP does not concatenate; its
  `build` attaches T's affix to the verb (see + -s = sees). Rules in Bare
  Grammar are arbitrary partial functions, not only concatenation.

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

/-! ## GB's lexical information (data) -/

/-- c-selection: (head, category of its complement phrase). -/
def cSelection : List (Pos × Pos) := [(.D, .N), (.V, .D), (.T, .V)]

/-- Heads that project without a complement in this fragment. -/
def noComplement : List Pos := [.N]

/-- Specifier positions, with the Case they assign: (head, specifier, note). -/
def specifiers : List (Pos × Pos × String) := [(.T, .D, "finite T assigns nominative")]

/-- Heads whose phrase may lack a specifier. T is absent: EPP. -/
def noSpecifier : List Pos := [.N, .D, .V]

/-- Case notes on complement positions. -/
def complementNote : Pos → Pos → String
  | .V, .D => "  [V assigns accusative]"
  | .T, .V => "  [Infl lowering: T's affix attaches to V]"
  | _, _   => ""

/-! ## Morphology for Infl lowering -/

def attachAffix (verb affix : String) : String :=
  match verb, affix with
  | "see", "-s" => "sees"
  | v, _ => v ++ "s"

/-- T′ → T⁰ VP: the affix in T⁰ lowers onto the first word of VP (the verb). -/
def lowerAffix : List (List String) → List String
  | [[affix], v :: rest] => attachAffix v affix :: rest
  | xs => xs.flatten

/-! ## The X-bar schema: GB data ↦ rule table -/

def x0 (p : Pos) : XCat := ⟨p, .zero⟩
def x1 (p : Pos) : XCat := ⟨p, .one⟩
def xp (p : Pos) : XCat := ⟨p, .two⟩

def xbarRules : List (Rule XCat) :=
  (noComplement.map fun p =>
    { name := s!"{(x1 p).text} → {(x0 p).text}", posCat := [x0 p], result := x1 p,
      build := List.flatten }) ++
  (cSelection.map fun (h, c) =>
    { name := s!"{(x1 h).text} → {(x0 h).text} {(xp c).text}" ++ complementNote h c,
      posCat := [x0 h, xp c], result := x1 h,
      build := if h = .T then lowerAffix else List.flatten }) ++
  (noSpecifier.map fun p =>
    { name := s!"{(xp p).text} → {(x1 p).text}", posCat := [x1 p], result := xp p,
      build := List.flatten }) ++
  (specifiers.map fun (h, s, note) =>
    { name := s!"{(xp h).text} → {(xp s).text} {(x1 h).text}  [{note}]",
      posCat := [xp s, x1 h], result := xp h, build := List.flatten })

def xbarGB : BareGrammar where
  Cat     := XCat
  decCat  := inferInstance
  lexicon := [(["the"], x0 .D), (["cat"], x0 .N), (["dog"], x0 .N),
              (["see"], x0 .V), (["-s"], x0 .T)]
  rules   := xbarRules

end BareSyntax
