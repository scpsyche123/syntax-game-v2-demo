/-
Display layer: how expressions, goals and workspaces appear in the infoview.

* `Deriv G (s, C)`           ↦ ⟨s, C⟩            (a derived expression)
* `e ∈ G.lexicon`            ↦ ⟨s, C⟩ ∈ Lex(G)   (a lexicon entry)
* `CanYield G s C`           ↦ ⟨s, C⟩ ∈ L(G)     (the goal of levels 1–2)
* `MP.WS.mk items`           ↦ [ n:{m-, √toto}, a-ta-, … ]
* `MP.Converges s`           ↦ the goal of level 3

The text is produced by plain functions; the delaborators only wrap it.
-/
import Lean
import BareSyntax.Linear
import BareSyntax.XBarGB
import BareSyntax.MP

namespace BareSyntax

open Lean Meta PrettyPrinter Delaborator SubExpr

/-! ## Workspace rendering (pure) -/

namespace MP

def Feat.text : Feat → String
  | .n => "n" | .v => "v" | .T => "T" | .root => "√"

def LI.text : LI → String
  | .m => "m-" | .ata => "a-ta-" | x => if x.feat = .root then "√" ++ x.form else x.form

def labelText : Option (Label × Option LI) → String
  | some (.cat f, _) => f.text
  | some (.phiphi, _) => "⟨φ,φ⟩"
  | none => "?"

/-- Render the occurrence `s` at depth `d` inside root `R`. A set is shown as
    `label:{a, b}`; `?` means no label yet; a lower copy is shown as
    `copy(label)`. -/
def render (R : SO) : SO → Nat → String
  | .li x, _ => x.text
  | s@(.set a b), d =>
    if lowerCopy R s d then s!"copy({labelText (labelAt R s d)})"
    else s!"{labelText (labelAt R s d)}:\{{render R a (d+1)}, {render R b (d+1)}}"

def renderWS (ws : List SO) : String :=
  "[" ++ ", ".intercalate (ws.map fun R => render R R 0) ++ "]"

end MP

/-! ## Reading values back from expressions (meta) -/

def strListOfExpr? (e : Lean.Expr) : Option (List String) := do
  let some (_, xs) := e.listLit? | none
  xs.mapM fun x => match x with
    | .lit (.strVal s) => some s
    | _ => none

def nameLast (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => n.toString

def posText? (e : Lean.Expr) : Option String :=
  match e.constName? with
  | some ``Pos.N => some "N" | some ``Pos.D => some "D"
  | some ``Pos.V => some "V" | some ``Pos.T => some "T"
  | some ``Pos.C => some "C"
  | _ => none

def barText? (e : Lean.Expr) : Option String :=
  match e.constName? with
  | some ``Bar.zero => some "⁰" | some ``Bar.one => some "′" | some ``Bar.two => some "P"
  | _ => none

/-- Text of a category expression (after reduction). -/
def catText (e : Lean.Expr) : MetaM String := do
  let e ← reduce (← instantiateMVars e)
  if e.isAppOfArity ``XCat.mk 3 then
    if let (some p, some b) := (posText? (e.getArg! 0), barText? (e.getArg! 1)) then
      let m := e.getArg! 2
      if m.isAppOfArity ``Option.some 2 then
        let pr := m.getArg! 1
        if pr.isAppOfArity ``Prod.mk 4 then
          if let some q := posText? (pr.getArg! 3) then
            return p ++ b ++ "/" ++ q ++ "P"
      return p ++ b
  if let some n := e.constName? then
    return nameLast n
  return toString (← Meta.ppExpr e)

def liOfExpr? (e : Lean.Expr) : Option MP.LI :=
  match e.constName? with
  | some ``MP.LI.m => some .m | some ``MP.LI.toto => some .toto
  | some ``MP.LI.ata => some .ata | some ``MP.LI.v => some .v
  | some ``MP.LI.lala => some .lala
  | _ => none

partial def soOfExpr? (e : Lean.Expr) : Option MP.SO :=
  if e.isAppOfArity ``MP.SO.li 1 then (liOfExpr? (e.getArg! 0)).map .li
  else if e.isAppOfArity ``MP.SO.set 2 then do
    let a ← soOfExpr? (e.getArg! 0)
    let b ← soOfExpr? (e.getArg! 1)
    pure (.set a b)
  else none

def wsOfExpr? (e : Lean.Expr) : MetaM (Option (List MP.SO)) := do
  let e ← reduce (← instantiateMVars e)
  if e.isAppOfArity ``MP.WS.mk 1 then
    let some (_, xs) := (e.getArg! 0).listLit? | return none
    return xs.mapM soOfExpr?
  return none

def liExpr : MP.LI → Lean.Expr
  | .m => mkConst ``MP.LI.m | .toto => mkConst ``MP.LI.toto | .ata => mkConst ``MP.LI.ata
  | .v => mkConst ``MP.LI.v | .lala => mkConst ``MP.LI.lala

def soExpr : MP.SO → Lean.Expr
  | .li x => mkApp (mkConst ``MP.SO.li) (liExpr x)
  | .set a b => mkApp2 (mkConst ``MP.SO.set) (soExpr a) (soExpr b)

def wsExpr (ws : List MP.SO) : Lean.Expr :=
  mkApp (mkConst ``MP.WS.mk) (ws.foldr (fun s acc =>
    mkApp3 (mkConst ``List.cons [0]) (mkConst ``MP.SO) (soExpr s) acc)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``MP.SO)))

/-- Text shown for a pair ⟨s, C⟩. -/
def pairText (s C : Lean.Expr) : MetaM String := do
  if let some ws ← wsOfExpr? C then
    return MP.renderWS ws
  let s ← reduce (← instantiateMVars s)
  let str := match strListOfExpr? s with
    | some [] => "∅"
    | some ws => " ".intercalate ws
    | none => "…"
  return s!"⟨{str}, {← catText C}⟩"

def grammarText (G : Lean.Expr) : String :=
  match G.constName? with
  | some n => nameLast n
  | none => "G"

/-- Show `text` verbatim (a numeric-literal node prints its atom as is). -/
def rawText (text : String) : Term := ⟨Syntax.mkNumLit text⟩

/-! ## Delaborators -/

@[delab app.BareSyntax.Deriv]
def delabDeriv : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 2)
  let pair := e.getArg! 1
  guard (pair.isAppOfArity ``Prod.mk 4)
  return rawText (← pairText (pair.getArg! 2) (pair.getArg! 3))

@[delab app.BareSyntax.CanYield]
def delabCanYield : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 3)
  let t ← pairText (e.getArg! 1) (e.getArg! 2)
  return rawText s!"{t} ∈ L({grammarText (e.getArg! 0)})"

@[delab app.Membership.mem]
def delabLexMem : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 5)
  let coll := e.getArg! 3
  let elt := e.getArg! 4
  guard (coll.isAppOfArity ``BareGrammar.lexicon 1)
  guard (elt.isAppOfArity ``Prod.mk 4)
  let t ← pairText (elt.getArg! 2) (elt.getArg! 3)
  return rawText s!"{t} ∈ Lex({grammarText (coll.getArg! 0)})"

@[delab app.BareSyntax.MP.WS.mk]
def delabWS : Delab := do
  let some ws ← wsOfExpr? (← getExpr) | failure
  return rawText (MP.renderWS ws)

@[delab app.BareSyntax.MP.Converges]
def delabConverges : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 1)
  let s ← reduce (e.getArg! 0)
  let str := match strListOfExpr? s with
    | some ws => " ".intercalate ws
    | none => "…"
  return rawText s!"WS = [one object, every node labeled]   (externalization must give “{str}”, checked automatically)"

end BareSyntax
