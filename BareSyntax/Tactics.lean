/-
Player commands.

* `rule "A N → N" good day` — apply a rule to expressions in the hypothesis
  panel: a data-domain rule (the linear levels) or a condition-domain rule
  without an argument (the X-bar schema, `rule "X0 YP -> X'" the cat_NP`). The result is COMPUTED by the rule and
  added as a new hypothesis; the player never types the output. When the
  result is the goal expression, the level closes.
  Rule names may be typed in ASCII: `"X0 YP -> X'"` = `"X⁰ YP → X′"`.
* `select the n cat will v sleep` — draw lexical items into the workspace
  (level 3, rule `Select`).
* `merge P Q` — MERGE(P, Q, WS) (level 3). P and Q are written as lexical
  items (`the`, `cat`), as phrases named by their label (`DP`, `nP`, `vP`,
  `TP`), or as a set of two such names (`{DP, vP}`). When the workspace holds a
  single fully labeled object, externalization is checked automatically.

The commands only hide Lean bookkeeping. Each step's linguistic content — which
rule, which inputs, which two objects to MERGE — is the player's choice, and
the kernel checks it.
-/
import BareSyntax.Show

namespace BareSyntax

open Lean Meta Elab Tactic

/-! ## Helpers evaluated at tactic time -/

def BareGrammar.ruleNames (G : BareGrammar) : List String := G.rules.map (·.name)
def BareGrammar.fruleNames (G : BareGrammar) : List String := G.frules.map (·.name)

/-- Output string and category of a condition-domain rule (used at tactic time). -/
def fapplyStr (G : BareGrammar) (r : FRule G.Cat G.Arg) (a : G.Arg) (inputs : List (Expr G.Cat)) :
    Option (List String) :=
  (r.apply a inputs).map Prod.fst
def fapplyCat (G : BareGrammar) (r : FRule G.Cat G.Arg) (a : G.Arg) (inputs : List (Expr G.Cat)) :
    Option G.Cat :=
  (r.apply a inputs).map Prod.snd

/-- A rule's name without its bracketed condition. -/
def ruleMain (name : String) : String := (name.splitOn "  [").head!

/-- The condition of a rule: the text in its brackets. -/
def ruleCondition (name : String) : String :=
  match name.splitOn "[" with
  | _ :: rest :: _ => (rest.splitOn "]").head!
  | _ => ""

def applyRuleStr (G : BareGrammar) (r : Rule G.Cat) (inputs : List (Expr G.Cat)) :
    Option (List String) :=
  (applyRule G r inputs).map Prod.fst

unsafe def evalStrListUnsafe (e : Lean.Expr) : MetaM (List String) :=
  Meta.evalExpr (List String) (mkApp (mkConst ``List [0]) (mkConst ``String)) e

@[implemented_by evalStrListUnsafe]
opaque evalStrList (e : Lean.Expr) : MetaM (List String)

unsafe def evalOptStrListUnsafe (e : Lean.Expr) : MetaM (Option (List String)) :=
  Meta.evalExpr (Option (List String))
    (mkApp (mkConst ``Option [0]) (mkApp (mkConst ``List [0]) (mkConst ``String))) e

@[implemented_by evalOptStrListUnsafe]
opaque evalOptStrList (e : Lean.Expr) : MetaM (Option (List String))

/-- Normalize a rule name so ASCII spellings match: drop the bracketed note,
    map ′→', ⁰→0, →→->, collapse spaces. -/
def normRuleName (s : String) : String :=
  let s := (s.splitOn "[").head!
  let s := s.replace "′" "'" |>.replace "⁰" "0" |>.replace "→" "->"
  " ".intercalate ((s.splitOn " ").filter (· ≠ ""))

def mkStrList (xs : List String) : Lean.Expr :=
  xs.foldr (fun s acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``String) (mkStrLit s) acc)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``String))

def asciiCat (s : String) : String :=
  s.replace "⁰" "0" |>.replace "′" "'"

/-- Readable hypothesis name: words joined by `_`, then the category. -/
def autoName (words : List String) (cat : String) : Name :=
  let ws := words.map fun w => w.replace "-" ""
  Name.mkSimple ("_".intercalate ws ++ "_" ++ asciiCat cat)

/-- An input to `rule`: a derived expression (`Deriv G e`) or a lexicon entry
    (`e ∈ G.lexicon`, turned into `Deriv.lex`). Returns (G, e, derivation term). -/
def readInput (x : Ident) : TacticM (Lean.Expr × Lean.Expr × Lean.Expr) := do
  let decl ← getLocalDeclFromUserName x.getId
  let ty := (← instantiateMVars decl.type).consumeMData
  if ty.isAppOfArity ``Deriv 2 then
    return (ty.getArg! 0, ty.getArg! 1, decl.toExpr)
  if ty.isAppOfArity ``Membership.mem 5 then
    let coll := ty.getArg! 3
    if coll.isAppOfArity ``BareGrammar.lexicon 1 then
      let G := coll.getArg! 0
      let e := ty.getArg! 4
      return (G, e, ← mkAppOptM ``Deriv.lex #[G, e, decl.toExpr])
  throwError "`{x.getId}` is not an expression of the grammar."

/-! ## `rule` -/

syntax (name := ruleTac) "rule " str (ppSpace colGt ident)+ (" as " ident)? : tactic

elab_rules : tactic
  | `(tactic| rule $nm:str $xs:ident* $[as $out?:ident]?) => withMainContext do
    let ins ← xs.mapM readInput
    let (G, _, _) := ins[0]!
    let Gname := grammarText G
    -- find the rule by name: data-domain rules first, then condition-domain rules
    let names ← evalStrList (mkApp (mkConst ``BareGrammar.ruleNames) G)
    let fnames ← evalStrList (mkApp (mkConst ``BareGrammar.fruleNames) G)
    let want := normRuleName nm.getString
    let catTy := mkApp (mkConst ``BareGrammar.Cat) G
    let exprTy := mkApp (mkConst ``BareSyntax.Expr) catTy
    let inputsE ← mkListLit exprTy (ins.toList.map (·.2.1))
    let givenCats : TacticM String := do
      let cs ← ins.toList.mapM fun (_, e, _) => do
        let e ← reduce e
        catText (e.getArg! 3)
      pure (", ".intercalate cs)
    let dl ← ins.toList.foldrM (fun (_, e, d) acc => do
        mkAppOptM ``DerivList.cons #[G, e, none, d, acc])
      (mkApp (mkConst ``DerivList.nil) G)
    let (outStr, outCat, outE, d) ← match names.findIdx? (fun n => normRuleName n == want) with
    | some i => do
      let ruleName := names[i]!
      let rulesE := mkApp (mkConst ``BareGrammar.rules) G
      let ruleTy := mkApp (mkConst ``Rule) catTy
      let iE := mkNatLit i
      let hlt ← mkDecideProof (← mkAppM ``LT.lt #[iE, ← mkAppM ``List.length #[rulesE]])
      let finE ← mkAppOptM ``Fin.mk #[none, iE, hlt]
      let rE ← mkAppOptM ``List.get #[ruleTy, rulesE, finE]
      -- compute the output string; reject if the rule is undefined on these inputs
      let some outStr ← evalOptStrList (mkApp3 (mkConst ``applyRuleStr) G rE inputsE)
        | throwError m!"The rule \"{ruleMain ruleName}\" is not defined on inputs of category " ++
            m!"{← givenCats}. Its domain is fixed by the categories on its left-hand side."
      let outCat ← reduce (← mkAppM ``Rule.result #[rE])
      let outE ← mkAppM ``Prod.mk #[mkStrList outStr, outCat]
      let hmem ← mkAppOptM ``List.get_mem #[ruleTy, rulesE, finE]
      let heq ← mkDecideProof (← mkEq (mkApp3 (mkConst ``applyRule) G rE inputsE)
        (← mkAppM ``Option.some #[outE]))
      pure (outStr, outCat, outE, ← mkAppOptM ``Deriv.app #[G, rE, inputsE, outE, hmem, dl, heq])
    | none =>
      match fnames.findIdx? (fun n => normRuleName n == want) with
      | none => throwError m!"{Gname} has no rule \"{nm.getString}\". Its rules are:\n" ++
          "\n".intercalate ((names ++ fnames).map ("  " ++ ·))
      | some j => do
        -- a condition-domain rule; `rule` handles those whose argument type is Unit
        let ruleName := fnames[j]!
        let argTy := mkApp (mkConst ``BareGrammar.Arg) G
        unless (← whnf argTy).isConstOf ``Unit || (← whnf argTy).isAppOf ``PUnit do
          throwError m!"The rule \"{ruleName}\" takes an argument; it is not used with `rule`."
        let unitE := mkConst ``Unit.unit
        let frulesE := mkApp (mkConst ``BareGrammar.frules) G
        let fruleTy := mkApp2 (mkConst ``FRule) catTy argTy
        let jE := mkNatLit j
        let hlt ← mkDecideProof (← mkAppM ``LT.lt #[jE, ← mkAppM ``List.length #[frulesE]])
        let finE ← mkAppOptM ``Fin.mk #[none, jE, hlt]
        let rE ← mkAppOptM ``List.get #[fruleTy, frulesE, finE]
        let some outStr ← evalOptStrList (mkApp4 (mkConst ``fapplyStr) G rE unitE inputsE)
          | throwError m!"The rule \"{ruleMain ruleName}\" is not defined on inputs of category " ++
              m!"{← givenCats}. Its domain is fixed by the pattern on its left-hand side " ++
              m!"and by its condition: {ruleCondition ruleName}."
        let outCat := (← reduce (mkApp4 (mkConst ``fapplyCat) G rE unitE inputsE)).getArg! 1
        let outE ← mkAppM ``Prod.mk #[mkStrList outStr, outCat]
        let hmem ← mkAppOptM ``List.get_mem #[fruleTy, frulesE, finE]
        let heq ← mkDecideProof (← mkEq (← mkAppM ``FRule.apply #[rE, unitE, inputsE])
          (← mkAppM ``Option.some #[outE]))
        pure (outStr, outCat, outE, ← mkAppOptM ``Deriv.fapp #[G, rE, unitE, inputsE, outE, hmem, dl, heq])
    let outTy := mkApp2 (mkConst ``Deriv) G outE
    let catT ← catText outCat
    let n := match out? with
      | some o => o.getId
      | none => autoName outStr catT
    let goal ← getMainGoal
    let (_, g') ← (← goal.assert n outTy d).intro1P
    replaceMainGoal [g']
    -- close the level when the goal expression has been built
    withMainContext do
      let gty := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
      if gty.isAppOfArity ``CanYield 3 then
        let target ← mkAppM ``Prod.mk #[gty.getArg! 1, gty.getArg! 2]
        if ← isDefEq target outE then
          let h ← getLocalDeclFromUserName n
          (← getMainGoal).assign (← mkAppM ``Nonempty.intro #[h.toExpr])
          replaceMainGoal []

/-! ## Level 3: `select` and `merge` -/

open MP in
def liOfName? : String → Option LI
  | "the" => some .the | "n" => some .n | "cat" => some .cat
  | "will" => some .will | "v" => some .v | "sleep" => some .sleep
  | _ => none

/-- The workspace hypothesis, if any: its derivation and its current items. -/
def getWS? : TacticM (Option (Lean.Expr × List MP.SO)) := withMainContext do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if decl.userName == `WS then
      let ty := (← instantiateMVars decl.type).consumeMData
      if ty.isAppOfArity ``Deriv 2 then
        let pair := ty.getArg! 1
        if let some ws ← wsOfExpr? (pair.getArg! 3) then
          return some (decl.toExpr, ws)
  return none

def wsPair (ws : List MP.SO) : MetaM Lean.Expr :=
  mkAppM ``Prod.mk #[mkStrList [], wsExpr ws]

def frulesMem (which : Nat) : MetaM Lean.Expr := do
  -- selectRule is the first FRule of mpWS, mergeRule the second
  let G := mkConst ``MP.mpWS
  let frulesE := mkApp (mkConst ``BareGrammar.frules) G
  let rE := if which == 0 then mkConst ``MP.selectRule else mkConst ``MP.mergeRule
  let ty ← mkAppM ``Membership.mem #[frulesE, rE]
  let mvar ← mkFreshExprMVar ty
  let ok ← Term.TermElabM.run' do
    try
      let stx ← `(tactic| simp [MP.mpWS])
      let gs ← Tactic.run mvar.mvarId! (Tactic.evalTactic stx)
      pure gs.isEmpty
    catch _ => pure false
  unless ok do throwError "internal: membership of the rule failed"
  instantiateMVars mvar

/-- One condition-domain rule step on the workspace: from `prev : Deriv mpWS
    ([], ⟨ws⟩)` to a derivation of `([], ⟨ws'⟩)`. -/
def fstep (which : Nat) (arg : Lean.Expr) (prev : Lean.Expr) (ws ws' : List MP.SO) :
    MetaM Lean.Expr := do
  let G := mkConst ``MP.mpWS
  let rE := if which == 0 then mkConst ``MP.selectRule else mkConst ``MP.mergeRule
  let inE ← wsPair ws
  let outE ← wsPair ws'
  let inputsE ← mkListLit (← mkAppM ``BareSyntax.Expr #[mkConst ``MP.WS]) [inE]
  let dl ← mkAppOptM ``DerivList.cons #[G, inE, none, prev, mkApp (mkConst ``DerivList.nil) G]
  let heq ← mkDecideProof (← mkEq (← mkAppM ``FRule.apply #[rE, arg, inputsE])
    (← mkAppM ``Option.some #[outE]))
  mkAppOptM ``Deriv.fapp #[G, rE, arg, inputsE, outE, ← frulesMem which, dl, heq]

def setWS (d : Lean.Expr) (ws : List MP.SO) : TacticM Unit := withMainContext do
  let ty := mkApp2 (mkConst ``Deriv) (mkConst ``MP.mpWS) (← wsPair ws)
  let goal ← getMainGoal
  let lctx ← getLCtx
  let goal ← match lctx.findFromUserName? `WS with
    | some decl => goal.clear decl.fvarId
    | none => pure goal
  let (_, g') ← (← goal.assert `WS ty d).intro1P
  replaceMainGoal [g']

syntax (name := selectTac) "select" (ppSpace colGt ident)+ : tactic

elab_rules : tactic
  | `(tactic| select $xs:ident*) => withMainContext do
    let (d0, ws0) ← match ← getWS? with
      | some p => pure p
      | none => do
        -- the lexicon's only entry: the empty workspace
        let e ← wsPair []
        let ty ← mkAppM ``Membership.mem #[mkApp (mkConst ``BareGrammar.lexicon) (mkConst ``MP.mpWS), e]
        pure (← mkAppOptM ``Deriv.lex #[mkConst ``MP.mpWS, e, ← mkDecideProof ty], [])
    let mut d := d0
    let mut ws := ws0
    for x in xs do
      let some li := liOfName? x.getId.toString
        | throwError "`{x.getId}` is not a lexical item. The lexicon has: the, n, cat, will, v, sleep."
      let ws' := ws ++ [.li li]
      d ← fstep 0 (mkApp (mkConst ``MP.Arg.sel) (liExpr li)) d ws ws'
      ws := ws'
    setWS d ws

/-! References to objects in the workspace. -/

declare_syntax_cat soref
syntax ident : soref
syntax "{" soref ", " soref "}" : soref

inductive SORef | name (s : String) | pair (a b : SORef)

partial def parseRef : TSyntax `soref → TacticM SORef
  | `(soref| $x:ident) => pure (.name x.getId.toString)
  | `(soref| { $a, $b }) => return .pair (← parseRef a) (← parseRef b)
  | _ => throwUnsupportedSyntax

partial def SORef.text : SORef → String
  | .name s => s
  | .pair a b => "{" ++ a.text ++ ", " ++ b.text ++ "}"

/-- Every occurrence in the workspace: (root, object, depth). -/
def occurrences (ws : List MP.SO) : List (MP.SO × MP.SO × Nat) :=
  ws.flatMap fun R =>
    let rec go (s : MP.SO) (d : Nat) : List (MP.SO × MP.SO × Nat) :=
      match s with
      | .li _ => [(R, s, d)]
      | .set a b => (R, s, d) :: (go a (d+1) ++ go b (d+1))
    go R 0

def dedup (xs : List MP.SO) : List MP.SO :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def phraseName? (lab : Option (MP.Label × Option MP.LI)) : Option String :=
  match lab with
  | some (.cat f, _) => some (MP.Feat.text f ++ "P")
  | _ => none

partial def resolve (ws : List MP.SO) : SORef → Except String MP.SO
  | .name s =>
    match liOfName? s with
    | some li =>
      if (occurrences ws).any (fun (_, o, _) => o == .li li) then .ok (.li li)
      else .error s!"There is no `{s}` in the workspace."
    | none =>
      let hits := dedup <| (occurrences ws).filterMap fun (R, o, d) =>
        match o with
        | .set _ _ => if phraseName? (MP.labelAt R o d) == some s then some o else none
        | _ => none
      match hits with
      | [o] => .ok o
      | [] => .error s!"There is no `{s}` in the workspace (no object labeled {s.dropRight 1})."
      | _ => .error s!"`{s}` is ambiguous: more than one object in the workspace has that label."
  | .pair a b => do
    let A ← resolve ws a
    let B ← resolve ws b
    let hits := dedup <| (occurrences ws).filterMap fun (_, o, _) =>
      if o == .set A B || o == .set B A then some o else none
    match hits with
    | [o] => .ok o
    | _ => .error s!"There is no object \{{a.text}, {b.text}} in the workspace."

syntax (name := mergeTac) "merge " soref ppSpace soref : tactic

elab_rules : tactic
  | `(tactic| merge $p:soref $q:soref) => withMainContext do
    let some (d, ws) ← getWS?
      | throwError "There is no workspace yet. Start with `select`."
    let rp ← parseRef p
    let rq ← parseRef q
    let P ← match resolve ws rp with | .ok o => pure o | .error m => throwError m
    let Q ← match resolve ws rq with | .ok o => pure o | .error m => throwError m
    let some ws' := MP.mergeWS P Q ws
      | throwError m!"MERGE({rp.text}, {rq.text}, WS) is undefined: the two objects must both " ++
          m!"be members of WS (External MERGE), or one must be a term of the other (Internal MERGE)."
    let d' ← fstep 1 (mkApp2 (mkConst ``MP.Arg.mrg) (soExpr P) (soExpr Q)) d ws ws'
    setWS d' ws'
    -- narrow syntax finished? then check labels and externalization automatically
    match ws' with
    | [R] =>
      withMainContext do
        let gty := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
        unless gty.isAppOfArity ``MP.Converges 1 do return
        let some target := strListOfExpr? (← reduce (gty.getArg! 0)) | return
        if !(MP.allLabeled R R 0) then
          logInfo m!"The workspace holds one object, but some node is still unlabeled (shown as ?)."
          return
        let out := MP.ext R R 0
        if out != target then
          logInfo m!"Narrow syntax is done, but externalization gives “{" ".intercalate out}”, not “{" ".intercalate target}”."
          return
        let some wsDecl := (← getLCtx).findFromUserName? `WS | return
        let hlab ← mkDecideProof (← mkEq (mkApp3 (mkConst ``MP.allLabeled) (soExpr R) (soExpr R)
          (mkNatLit 0)) (mkConst ``Bool.true))
        let hext ← mkDecideProof (← mkEq (mkApp3 (mkConst ``MP.ext) (soExpr R) (soExpr R)
          (mkNatLit 0)) (gty.getArg! 0))
        let ne ← mkAppM ``Nonempty.intro #[wsDecl.toExpr]
        let ex ← whnfD gty   -- unfold `Converges` to its ∃
        let pf ← mkAppOptM ``Exists.intro #[mkConst ``MP.SO,
          ex.getArg! 1, soExpr R, ← mkAppM ``And.intro #[ne, ← mkAppM ``And.intro #[hlab, hext]]]
        (← getMainGoal).assign pf
        replaceMainGoal []
        logInfo m!"Converged. Externalization: “{" ".intercalate out}”."
    | _ => pure ()

end BareSyntax
