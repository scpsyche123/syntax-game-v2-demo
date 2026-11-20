import GameServer.Commands
import BareSyntax

/-! Documentation for the three player commands. -/

/-- `rule "NAME" x y …` applies the rule NAME to the expressions x, y, … in
your hypotheses. The rule computes the result, which appears as a new
hypothesis with a readable name (for example `the_cat_DP`). If the rule is not
defined on those inputs, it is rejected.

Rule names may be typed with ASCII: `"X0 YP -> X'"` means `"X⁰ YP → X′"`.
Add `as NAME` at the end to choose the name of the result yourself. -/
TacticDoc rule

/-- `select x y …` draws lexical items into the workspace WS (rule Select).
The lexicon of this grammar: `the`, `n`, `cat`, `will`, `v`, `sleep`. -/
TacticDoc select

/-- `merge P Q` performs MERGE(P, Q, WS): it replaces P and Q by {P, Q}.

P and Q can be written as
* a lexical item: `the`, `n`, `cat`, `will`, `v`, `sleep`;
* a phrase named by its label: `DP`, `nP`, `vP`, `TP`;
* a set of two such names: `{DP, vP}`.

External MERGE: P and Q are both members of WS. Internal MERGE: one is a term
of the other. Anything else is rejected. -/
TacticDoc merge
