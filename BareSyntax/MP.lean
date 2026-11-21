/-
Level 5 grammar: `mpWS` — the Minimalist Program, workspace era, as a Bare
Grammar, for a Swahili sentence:

    Mtoto atalala.      m-toto   a-ta-lala
                        1-child  1SM-FUT-sleep     'The child will sleep.'

Lexical items: n = m- (the class-1 prefix; noun class is a φ-feature on n),
the root √toto, T = a-ta- (future -ta- with the class-1 subject marker a-;
Agree is not modeled, so T's φ is already valued), a silent v, the root √lala.

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

MERGE is free; what it builds is filtered at the interfaces. Conditions at CI,
checked on the finished object:
* Selection: T takes a vP, n and v each take a root, and every root is
  categorized by n or v.
* θ-criterion: the subject nP is first merged as the sister of vP {v, √}, where
  v assigns its θ-role, and that vP has such an nP.
* Chains (Last Resort): only the nP is merged twice — from its θ-position to the
  specifier of T — and nothing else moves.
Without these, free MERGE plus labeling and word order accepts many objects
that are not the intended one (for the earlier English fragment, a search of all
derivations with at most two Internal MERGEs found 1784; the search script is not
part of this repository). With them the intended object is accepted. It is not
unique under raw `SO` equality, however: `SO.set` records argument order, and two
objects for "mtoto atalala" that differ only in the order inside nP both pass
(`playground/Expressivity.lean`).

Simplifications (stated, not hidden):
* Copy vs. repetition: two occurrences of the same object count as copies; the
  one closer to the root is the higher copy. (Form Copy is not modeled.)
* Agree is not modeled: T's φ is treated as already valued.
* No phases, no Transfer, no Minimal Search / Resource Restriction.
* Externalization order: a head precedes its sister; the nP precedes its
  sister; only the highest copy is pronounced; v is silent; a prefix (m-,
  a-ta-) joins the next pronounced item into one word.
-/
import BareSyntax.Basic

namespace BareSyntax.MP

/-- Lexical items of this fragment. -/
inductive LI | m | toto | ata | v | lala
  deriving DecidableEq, Repr

/-- Categorial features. `root` items cannot label. -/
inductive Feat | n | v | T | root
  deriving DecidableEq, Repr

def LI.feat : LI → Feat
  | .m => .n | .toto => .root | .ata => .T | .v => .v | .lala => .root

/-- φ: noun class on n, the valued subject agreement on T. -/
def LI.phi : LI → Bool
  | .m => true | .ata => true | _ => false

def LI.form : LI → String
  | .m => "m" | .toto => "toto" | .ata => "ata" | .v => "v" | .lala => "lala"

def LI.pronounced : LI → Bool
  | .v => false | _ => true

/-- A prefix joins the next pronounced item into one word. -/
def LI.prefix : LI → Bool
  | .m => true | .ata => true | _ => false

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

/-- The nominal argument: an object labeled n. -/
def isArg (R : SO) (s : SO) (d : Nat) : Bool :=
  match labelAt R s d with
  | some (.cat .n, _) => true
  | _ => false

def isHead : SO → Bool
  | .li x => x.feat != .root
  | _ => false

/-- Linear order: the pronounced items, each with whether it is a prefix. -/
def linearize (R : SO) : SO → Nat → List (String × Bool)
  | .li x, _ => if x.pronounced then [(x.form, x.prefix)] else []
  | .set a b, d =>
    if lowerCopy R a (d+1) then linearize R b (d+1)
    else if lowerCopy R b (d+1) then linearize R a (d+1)
    else if isHead b && !isHead a then linearize R b (d+1) ++ linearize R a (d+1)
    else if isArg R b (d+1) && !isArg R a (d+1) then linearize R b (d+1) ++ linearize R a (d+1)
    else linearize R a (d+1) ++ linearize R b (d+1)

/-- Words: a prefix joins the next item. -/
def joinPrefixes : List (String × Bool) → List String
  | [] => []
  | (p, true) :: rest => match joinPrefixes rest with
    | w :: ws => (p ++ w) :: ws
    | [] => [p]
  | (w, false) :: rest => w :: joinPrefixes rest

/-- Externalization: the words of the object rooted at `s`. -/
def ext (R s : SO) (d : Nat) : List String := joinPrefixes (linearize R s d)

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

/-! ## Interface conditions (CI) -/

/-- Every occurrence below the root: (object, its sister, its depth, its mother). -/
def occs : SO → Nat → List (SO × SO × Nat × SO)
  | .li _, _ => []
  | s@(.set a b), d => (a, b, d+1, s) :: (b, a, d+1, s) :: (occs a (d+1) ++ occs b (d+1))

def labelIs (R s : SO) (d : Nat) (f : Feat) : Bool :=
  match labelAt R s d with
  | some (.cat g, _) => g == f
  | _ => false

def isRoot : SO → Bool
  | .li x => x.feat == .root
  | _ => false

def isSet : SO → Bool
  | .set _ _ => true
  | _ => false

/-- What a head takes as its sister. -/
def selects (R : SO) (h : LI) (X : SO) (d : Nat) : Bool :=
  match h.feat with
  | .T => isSet X && labelIs R X d .v
  | .n | .v => isRoot X
  | .root => true

/-- Selection: every head occurrence has the sister it selects, and every root
    is the sister of n or v. -/
def selectionOK (R : SO) : Bool :=
  (occs R 0).all fun (x, y, d, _) => match x with
    | .li h =>
      if h.feat == .root then (match y with | .li g => g.feat == .n || g.feat == .v | _ => false)
      else selects R h y d
    | _ => true

/-- The minimal vP: v with its root. -/
def minVP : SO → Bool
  | .set a b => (a == .li .v && isRoot b) || (b == .li .v && isRoot a)
  | _ => false

/-- The occurrence with the greatest (`low`) or smallest depth; ties keep the first. -/
def pick (low : Bool) (xs : List (SO × SO × Nat × SO)) : Option (SO × SO × Nat × SO) :=
  xs.foldl (fun acc o => match acc with
    | none => some o
    | some m => if (if low then o.2.2.1 > m.2.2.1 else o.2.2.1 < m.2.2.1) then some o else some m) none

/-- θ-criterion: the nP's lowest occurrence is the sister of the minimal vP, and
    the minimal vP has an nP sister. -/
def thetaOK (R : SO) : Bool :=
  R.terms.all fun X =>
    let mine := (occs R 0).filter (·.1 == X)
    (match mine with
     | [] => true
     | (_, _, d₀, _) :: _ =>
       if isSet X && labelIs R X d₀ .n then
         match pick true mine with
         | some (_, sis, _, _) => minVP sis
         | none => false
       else true) &&
    (!minVP X || mine.any fun (_, sis, d, _) => isSet sis && labelIs R sis d .n)

def dedupSO (xs : List SO) : List SO :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- Chains (Last Resort): an object that occurs under two different mothers was
    merged twice. Only the nP may be, exactly twice, its higher copy in the
    specifier of T. -/
def chainsOK (R : SO) : Bool :=
  R.terms.all fun X =>
    let mine := (occs R 0).filter (·.1 == X)
    if (dedupSO (mine.map (·.2.2.2))).length < 2 then true
    else match pick false mine with
      | some (_, sis, d, _) => isSet X && labelIs R X d .n && mine.length == 2 && isSet sis && labelIs R sis d .T
      | none => true

def ciOK (R : SO) : Bool := selectionOK R && thetaOK R && chainsOK R

/-- The level goal. Narrow syntax: derive a workspace holding exactly one
    object, every node of which is labeled. Then the interface conditions at CI
    must hold and externalization must give `s` — this part is checked
    automatically. -/
def Converges (s : List String) : Prop :=
  ∃ R : SO, Nonempty (Deriv mpWS ([], ⟨[R]⟩)) ∧ allLabeled R R 0 = true ∧ ciOK R = true ∧ ext R R 0 = s

end BareSyntax.MP
