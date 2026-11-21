# Comparing syntactic models' expressive power — initial investigation

**Date:** 2026-11-21  
**Status:** exploratory; several small claims checked by Lean 4.23.0, not a result about the expressive power of whole GB, MP, or Bare Grammar theory.  
**Proofs:** [`playground/Expressivity.lean`](../../playground/Expressivity.lean).

## Research priority

The main question is **what syntactic models can and cannot express**, not the construction of a syntax game. Proofs of `CanYield`/`CannotYield` and structural representations are tools, not the eventual contribution. A public research demo should present precise model comparisons and their assumptions.

## Distinctions that must not be conflated

1. **A pair of fixed grammars:** compare `W(G) = { (s, c) | CanYield G s c }`, only after aligning vocabularies and relevant categories. The existence of a separating expression establishes a difference between those particular grammars, not between the expressive powers of whole theory classes.
2. **Classes of grammars:** compare the families of languages definable when lexical inventories, rule schemata, parameter types, feature sets, and allowable operations are specified. Without these restrictions, the result is likely uninformative.
3. **Structural descriptions:** weakly equivalent grammars may assign different structures; comparison requires a declared common interpretation domain or a structure-preserving translation, not just equality of terminal strings.
4. **Invariance:** determine which properties or operations survive automorphisms/renamings when the models represent different kinds of syntactic objects.

## Lean-checked findings

Theorems below are all in `ExpressivityPilot`. Ran `lake build BareSyntax` and `lake env lean Expressivity.lean` in the repository's dependency-free `playground/`, with pinned `leanprover/lean4:v4.23.0`, exit code 0.

### A. The current MERGE representation records argument order

`BareSyntax/MP.lean` has `SO.set (a b : SO)`, which is an **ordered binary constructor**, although prose describes `MERGE(P,Q)` as an unordered two-element set.

- `merge_constructor_remembers_order`: `SO.set a b ≠ SO.set b a` for two different roots (`√toto`, `√lala`).
- `merge_rule_accepts_both_orders`: both orders are actual outputs of `mergeWS` from the same workspace.
- `merge_yields_different_order`: `ext (set a b) = ["toto","lala"]` and `ext (set b a) = ["lala","toto"]`.

The preceding `√toto/√lala` structures are *not* valid whole sentences under the Swahili interface conditions. But the next four checked facts strengthen the finding:

- `distinct_narrow_syntax_objects`: let `nP₁ = set m toto` and `nP₂ = set toto m`, and consistently use the selected `nP` as both the lower and higher occurrence inside the full Swahili object; the resulting roots `r₁ ≠ r₂`.
- `both_satisfy_interface`: **both** objects satisfy `allLabeled = true` and `ciOK = true`.
- `same_surface_string`: both externally realize `["mtoto","atalala"]`.
- `standard_subject_order_converges` and `reversed_subject_order_converges`: the original and reversed `merge m toto` / `merge toto m` scripts **both compile** as complete Lean proofs of `MP.Converges ["mtoto","atalala"]`. The two results have the same proposition: `Converges` only asserts that *some* object converges.
- `r₁_derivable` and `r₂_derivable` (added 2026-11-21): each of `r₁` and `r₂` is itself the single object of a complete derivation from the empty workspace, `Nonempty (Deriv MP.mpWS ([], ⟨[rᵢ]⟩))`. Together with the two previous facts, both objects satisfy every clause of `Converges`.

**Consequences:** the README's historical finite-search statement of \"exactly one object converges\" should *not* be interpreted as uniqueness under raw Lean `SO` equality; the current representation distinguishes multiple orders of the same intended set. Uniqueness *modulo unordered-MERGE equivalence* is a different, unproved claim.

**Next question:** if `q` identifies `set a b` with `set b a`, does the existing `ext` factor through `q`? On *all* objects, the `√toto/√lala` pair is already a counterexample. On the **subset of convergent objects**, the two known `r₁,r₂` share the same output, so the factorization question remains open.

### B. Unrestricted `FRule` can trivialize weak yield comparison

In `Basic.lean`, `FRule.apply : Arg → List (Expr Cat) → Option (Expr Cat)`. The type `Arg` and output provenance are unrestricted at this abstraction level.

- `all_strings_generated`: construct a `BareGrammar` with `Arg := List String`, one rule that takes an empty list of inputs and emits its argument, and no lexical entries. For **every** `s : List String`, prove `CanYield unrestrictedGrammar s ()`.

This is a theorem about **one permissive instance of the ambient `BareGrammar` type**, not a theorem about `MP.mpWS`, and not a proof that arbitrary *proper subsets* of `Σ*` are definable. It demonstrates why comparing unrestricted `FRule` instances by string yield alone cannot distinguish the intended syntax operations.

Relevant restrictions for the next stage: finite or otherwise explicitly bounded lexical resources and rule arguments, stated output provenance, specified merge/movement/linearization operations, and an observation function fixed independently of the theory being tested. A finite `Arg` alone does not constrain the `apply` function sufficiently.

### C. A two-atom symmetry obstruction to ordering

- `swap_cannot_fix_an_ordered_pair`: neither `[true,false]` nor `[false,true]` stays fixed under swapping the two atoms.
- `no_equivariant_orderer`: for the *single unordered two-atom object* (represented abstractly by `Unit`), no orderer can enumerate both distinct atoms and remain invariant under their swap.

Argument: the unordered pair `{a,b}` is unchanged by exchanging `a` and `b`, but either linear enumeration changes. This is a **conditional result**: it assumes the two atoms are otherwise indistinguishable in the input structure and the ordering function respects the swap. It does **not** establish that actual MP cannot linearize expressions when head features, category labels, or interface conditions break the symmetry.

## Next research step (not yet proved)

**Primary:** replace the order-bearing `SO.set` with a genuinely unordered representation or quotient **without losing tokens/occurrences needed for Internal MERGE and copies**. Then ask whether a theory-neutral externalization can preserve the relevant structured observations under a translation from X-bar to MP. A simple `Finset SO` substitution may collapse copies and therefore requires careful design.

A precise next theorem to test:

> Under explicitly stated interface conditions, does every convergent unordered-MERGE structure admit a linearization that preserves the required word order, labels, and occurrence relations? If not, find a minimal counterexample; if yes, identify exactly which features break the symmetry.

**Secondary:** formulate two small grammars over the same lexical inventory and compare a shared observation set (strings, categorial projections, movement/copy relations), proving an inclusion, equivalence, or separation. Comparing the current Turkish X-bar fragment directly with the Swahili MP fragment would confound grammar theory with differences in lexical inventory.

No claim of academic novelty is made at this stage; the symmetric linearization difficulty, structural equivalence of grammars, and equivalence of minimalist grammar classes have substantial prior literature.

## Literature to examine next

- Keenan & Stabler, *Bare Grammar: A Study of Language Invariants* (2003/2004 editions): https://web.stanford.edu/group/cslipublications/cslipublications/site/1575861887.shtml
- Rogers (1996), *A Model-Theoretic Framework for Theories of Syntax*: https://aclanthology.org/P96-1002/
- Collins & Stabler (2016), *A Formalization of Minimalist Syntax*: https://onlinelibrary.wiley.com/doi/10.1111/synt.12117
- Michaelis (2001), *Derivational Minimalism Is Mildly Context-Sensitive*: https://wwwhomes.uni-bielefeld.de/~jmichaelis/papers/Mich-98.html
- *Sortal Equivalence of Bare Grammars* (2009), in *The Mathematics of Language*: https://link.springer.com/book/10.1007/978-3-642-14322-9
- *Strong Equivalence of TAG and CCG* (2021): https://aclanthology.org/2021.tacl-1.43/

## Verification and limits

```bash
cd playground
lake build BareSyntax
lake env lean Expressivity.lean
```

Both commands were run successfully against the pinned toolchain in a temporary checkout. The proof file has no `sorry` or `admit`. Two distinct ordered representatives are each derivable and satisfy the Swahili interface conditions (`r₁_derivable`, `r₂_derivable`, `both_satisfy_interface`); this has not yet been reformulated as uniqueness/equivalence classes under true unordered Merge. This experiment does **not** repair `MP.SO` or make the present syntax demo an honest unordered-MERGE model. Changes to the model and interface are future research work, not part of the current checked claims.
