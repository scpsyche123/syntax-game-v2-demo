import Lake
open Lake DSL

/-! English demo of the project's earlier X-bar formalization.
    Lean core only: no GameServer, nothing to download except the toolchain.
    `lake build` checks the theory library, the walkthrough and all twelve levels. -/
package XBar

@[default_target]
lean_lib XSyntax

@[default_target]
lean_lib Levels
