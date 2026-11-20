/-
Level 3 grammar: `mpWS` — the Minimalist Program, workspace era, as a Bare
Grammar.

Source for the operation: Chomsky 2020 (UCLA Lectures), as quoted in Victor
Junnan Pan, *Lecture 10: The Minimalist Program*, §9:

    MERGE(P, Q, WS) = [{P, Q}, …] = WS′

MERGE replaces P and Q by {P, Q}; there is no separate Remove. External MERGE
(P, Q both members of WS) leaves WS one member smaller; Internal MERGE (P is a
term of Q) leaves its size unchanged. (Pan & Du's rendering [{P,Q}, P, Q, …],
which keeps P and Q, is NOT the one used here.)

How this sits in Bare Grammar:
* An EXPRESSION is a workspace. Its category is the workspace itself (a list of
  syntactic objects); its string is empty, because narrow syntax has no linear
  order. Externalization is a separate function `ext`, applied at the end.
* The lexicon has one entry: the empty workspace. `Select x` (draw a lexical
  item x into the workspace) and `MERGE(P, Q)` are condition-domain rules
  (`FRule`), indexed by their arguments.
* Labels come from a labeling algorithm in the style of Chomsky 2013
  ("Problems of Projection"), computed on the finished object:
    - {H, XP}: H labels;
    - {R, H} with R a root: H labels (roots cannot label);
    - {XP, YP}: labeled ⟨φ,φ⟩ if both labeling heads carry φ; otherwise
      unlabeled, unless one of them is a lower copy, which is invisible.

Simplifications (stated, not hidden):
* Copy vs. repetition: two occurrences of the same object count as copies; the
  one closer to the root is the higher copy. (Form Copy is not modeled.)
* Agree is not modeled: T's φ is treated as already valued.
* No phases, no Transfer, no Minimal Search / Resource Restriction.
* Externalization order: a head precedes its sister; a DP precedes its sister;
  only the highest copy is pronounced; n and v are silent.
-/
import BareSyntax.Basic

namespace BareSyntax.MP

/-- Lexical items of this fragment. -/
inductive LI | the | n | cat | will | v | sleep
  deriving DecidableEq, Repr

/-- Categorial features. `root` items cannot label. -/
inductive Feat | D | n | v | T | root
  deriving DecidableEq, Repr

def LI.feat : LI → Feat
  | .the => .D | .n => .n | .cat => .root | .will => .T | .v => .v | .sleep => .root

def LI.phi : LI → Bool
  | .the => true | .will => true | _ => false

def LI.form : LI → String
  | .the => "the" | .n => "n" | .cat => "cat" | .will => "will" | .v => "v" | .sleep => "sleep"

def LI.pronounced : LI → Bool
  | .n => false | .v => false | _ => true

/-- Syntactic objects: lexical items and two-member sets {a, b}. -/
inductive SO | li (x : LI) | set (a b : SO)
  deriving DecidableEq, Repr

/-- A workspace. Written [ … ] to keep it apart from the sets MERGE builds. -/
structure WS where
  items : List SO
  deriving DecidableEq, Repr

inductive Label | cat (f : Feat) | phiphi
  deriving DecidableEq, Repr

/-! ## Terms and copies -/

def SO.terms : SO → List SO
  | s@(.li _) => [s]
  | s@(.set a b) => s :: (a.terms ++ b.terms)

/-- Depths (root = 0) at which `X` occurs inside `R`. -/
def occDepths (X : SO) : SO → Nat → List Nat
  | R@(.li _), d => if R = X then [d] else []
  | R@(.set a b), d => (if R = X then [d] else []) ++ occDepths X a (d+1) ++ occDepths X b (d+1)

/-- The occurrence of `X` at depth `d` in `R` is a lower copy: `X` also occurs
    closer to the root. -/
def lowerCopy (R X : SO) (d : Nat) : Bool := (occDepths X R 0).any (· < d)

/-! ## Labeling algorithm -/

/-- Label of the occurrence `s` at depth `d` inside root `R`, together with the
    lexical item that supplies it (none for ⟨φ,φ⟩). -/
def labelAt (R : SO) : SO → Nat → Option (Label × Option LI)
  | .li x, _ => some (.cat x.feat, some x)
  | .set a b, d =>
    let la := labelAt R a (d+1)
    let lb := labelAt R b (d+1)
    if lowerCopy R a (d+1) && !lowerCopy R b (d+1) then lb
    else if lowerCopy R b (d+1) && !lowerCopy R a (d+1) then la
    else match a, b with
      | .li x, .li y =>
        if x.feat = .root && y.feat != .root then some (.cat y.feat, some y)
        else if y.feat = .root && x.feat != .root then some (.cat x.feat, some x)
        else none
      | .li x, .set _ _ => if x.feat != .root then some (.cat x.feat, some x) else none
      | .set _ _, .li y => if y.feat != .root then some (.cat y.feat, some y) else none
      | .set _ _, .set _ _ =>
        let phiOf : Option (Label × Option LI) → Bool
          | some (_, some h) => h.phi
          | _ => false
        if phiOf la && phiOf lb then some (.phiphi, none) else none

/-- Every set node (outside lower copies) has a label. -/
def allLabeled (R : SO) : SO → Nat → Bool
  | .li _, _ => true
  | s@(.set a b), d =>
    (labelAt R s d).isSome &&
    (lowerCopy R a (d+1) || allLabeled R a (d+1)) &&
    (lowerCopy R b (d+1) || allLabeled R b (d+1))

/-! ## Externalization -/

def isDP (R : SO) (s : SO) (d : Nat) : Bool :=
  match labelAt R s d with
  | some (.cat .D, _) => true
  | _ => false

def isHead : SO → Bool
  | .li x => x.feat != .root
  | _ => false

def ext (R : SO) : SO → Nat → List String
  | .li x, _ => if x.pronounced then [x.form] else []
  | .set a b, d =>
    if lowerCopy R a (d+1) then ext R b (d+1)
    else if lowerCopy R b (d+1) then ext R a (d+1)
    else if isHead b && !isHead a then ext R b (d+1) ++ ext R a (d+1)
    else if isDP R b (d+1) && !isDP R a (d+1) then ext R b (d+1) ++ ext R a (d+1)
    else ext R a (d+1) ++ ext R b (d+1)

/-! ## The two rules -/

inductive Arg | sel (x : LI) | mrg (P Q : SO)

/-- MERGE(P, Q, WS). External: P and Q are members of WS. Internal: one is a
    term of the other, which is a member of WS. Otherwise undefined. -/
def mergeWS (P Q : SO) (ws : List SO) : Option (List SO) :=
  if P ∈ ws ∧ Q ∈ ws.erase P then some (SO.set P Q :: (ws.erase P).erase Q)
  else if Q ∈ ws ∧ P ∈ Q.terms ∧ P ≠ Q then some (SO.set P Q :: ws.erase Q)
  else if P ∈ ws ∧ Q ∈ P.terms ∧ P ≠ Q then some (SO.set P Q :: ws.erase P)
  else none

def selectRule : FRule WS Arg where
  name := "Select"
  apply
    | .sel x, [([], ⟨ws⟩)] => some ([], ⟨ws ++ [.li x]⟩)
    | _, _ => none

def mergeRule : FRule WS Arg where
  name := "MERGE"
  apply
    | .mrg P Q, [([], ⟨ws⟩)] => (mergeWS P Q ws).map fun ws' => ([], ⟨ws'⟩)
    | _, _ => none

def mpWS : BareGrammar where
  Cat     := WS
  decCat  := inferInstance
  lexicon := [([], ⟨[]⟩)]
  rules   := []
  Arg     := Arg
  frules  := [selectRule, mergeRule]

/-- The level goal. Narrow syntax: derive a workspace holding exactly one
    object, every node of which is labeled. Then externalization must give `s`
    — this part is checked automatically. -/
def Converges (s : List String) : Prop :=
  ∃ R : SO, Nonempty (Deriv mpWS ([], ⟨[R]⟩)) ∧ allLabeled R R 0 = true ∧ ext R R 0 = s

end BareSyntax.MP
