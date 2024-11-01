import Lake
open Lake DSL

package «expr_graph» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require lean_extras from git
  "https://github.com/adamtopaz/lean_extras.git"

@[default_target]
lean_lib «ExprGraph» where

@[default_target]
lean_lib Utils where

@[default_target]
lean_exe entrypoint where
  root := `Main
  supportInterpreter := true

