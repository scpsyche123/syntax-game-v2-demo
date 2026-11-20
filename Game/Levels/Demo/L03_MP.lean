import Game.Metadata

open BareSyntax

World "Demo"
Level 3

Title "The Minimalist Program: MERGE on workspaces"

Introduction "
Same language, a grammar from a later era. Here **an expression is a workspace**.
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

Unlabeled nodes show as `?`, lower copies as `copy(…)`.

**Goal:** a workspace with one object, every node labeled. Externalization — word order,
which copy is pronounced — is checked automatically. You only do narrow syntax.

**Commands:**

- `select the n cat will v sleep` draws lexical items into WS.
- `merge P Q`, where P and Q are lexical items (`the`, `cat`), phrases named by their label
  (`DP`, `vP`, `TP`), or a set of two such names (`{DP, vP}`).

*Simplifications:* two occurrences of the same object count as copies;
Agree is not modeled (T's φ counts as valued); no phases.
"

/-- Narrow syntax for *the cat will sleep*. -/
Statement : MP.Converges ["the", "cat", "will", "sleep"] := by
  Hint "Begin by drawing the lexical items into the workspace: `select the n cat will v sleep`."
  select the n cat will v sleep
  Hint "Build the noun first: `merge n cat`."
  merge n cat
  merge the nP
  merge v sleep
  merge DP vP
  merge will {DP, vP}
  Hint "One object is left, but \{DP, vP} has no label. What can MERGE do that makes the DP inside invisible there?"
  merge DP TP

Conclusion "
Look at the last step. Before Internal MERGE, {DP, vP} had no label: neither D nor v
shares a feature with the other. After it, the lower DP is a copy, the labeling algorithm
sees only vP, and the new root {DP, TP} is labeled ⟨φ,φ⟩ by shared φ.
Externalization pronounced only the higher copy: *the cat will sleep*.

Three levels, three generations of generative syntax, one language.
In each, a grammar is categories, a lexicon and rules — data — and Lean checks every step.
"

NewTactic select merge
DisabledTactic rule
