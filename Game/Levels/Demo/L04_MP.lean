import Game.Metadata

open BareSyntax

World "Demo"
Level 4

Title "The Minimalist Program: Swahili"

Introduction "
Same language, a grammar from a later era, and another human language:

  *Mtoto atalala.*   m-toto a-ta-lala   1-child 1SM-FUT-sleep   'The child will sleep.'

The class-1 prefix m- is n; noun class is a φ-feature on n. T is a-ta-: future -ta- with the
class-1 subject marker a-. Here **an expression is a workspace**.
Following Chomsky (2020, *UCLA Lectures*):

  MERGE(P, Q, WS) = [{P, Q}, …] = WS′

MERGE replaces P and Q by the set {P, Q}. If P and Q are both members of WS, this is
External MERGE, and WS loses one member. If P is a term of Q, it is Internal MERGE,
and WS keeps its size. One operation, not two.

In Bare Grammar terms: the lexicon has one expression, the empty workspace.
Select and MERGE are rules whose domain is a decidable condition rather than a list
of categories.

MERGE neither labels nor linearizes. Labels come from a labeling algorithm (after Chomsky 2013):

- {H, XP}: H labels.
- {n, √root}, {v, √root}: a root cannot label, so n or v does.
- {XP, YP}: labeled ⟨φ,φ⟩ if both heads carry φ; otherwise no label —
  unless one of the two is a lower copy, which the algorithm does not see.

MERGE is free; the finished object must meet conditions at the interface: selection (T takes
vP, n and v take a root), the θ-criterion (the subject nP first merges with vP) and chains (only
the nP moves, once, to the specifier of T).

Unlabeled nodes show as `?`, lower copies as `copy(…)`.

**Goal:** a workspace with one object, every node labeled. Externalization — word order,
which copy is pronounced — is checked automatically. You only do narrow syntax.

**Commands:**

- `select m toto ata v lala` draws lexical items into WS.
- `merge P Q`, where P and Q are lexical items (`m`, `toto`), phrases named by their label
  (`nP`, `vP`, `TP`), or a set of two such names (`{nP, vP}`).

*Simplifications:* two occurrences of the same object count as copies;
Agree is not modeled (T's φ counts as valued); no phases.
"

/-- Narrow syntax for *mtoto atalala*. -/
Statement : MP.Converges ["mtoto", "atalala"] := by
  Hint "Begin by drawing the lexical items into the workspace: `select m toto ata v lala`."
  select m toto ata v lala
  Hint "Build the noun first: `merge m toto`."
  merge m toto
  merge v lala
  merge nP vP
  merge ata {nP, vP}
  Hint "One object is left, but \{nP, vP} has no label. What can MERGE do that makes the nP inside invisible there?"
  merge nP TP

Conclusion "
Look at the last step. The subject has to start in vP (θ-criterion), but there {nP, vP}
has no label: n carries φ (noun class 1), v does not. After Internal MERGE the lower nP is a
copy, the labeling algorithm sees only vP, and the new root {nP, TP} is labeled ⟨φ,φ⟩: the
class-1 φ of m- and of the subject marker a-. Externalization pronounced only the higher
copy and joined the prefixes: *mtoto atalala*.

Four levels, three generations of generative syntax, three human languages, one formal language.
In each, a grammar is categories, a lexicon and rules — data — and Lean checks every step.
"

NewTactic select merge
DisabledTactic rule
