import Lake
open Lake DSL

/-! A dependency-free package for stepping through the demo in VS Code.
    It compiles the language (`../BareSyntax`) with Lean core only — no GameServer,
    nothing to download except the Lean toolchain. -/
package Playground

lean_lib BareSyntax where
  srcDir := ".."

@[default_target]
lean_lib Demo
