import Lake

open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.0"

require subverso from git
  "https://github.com/leanprover/subverso" @
    "0076a9e8a3670d83c54c93414b2b26d3a8aba08d"

package SerreNumberTheory where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib SerreNumberTheory

/-- Convert SubVerso semantic highlighting data into lightweight JSON for the Notion viewer. -/
lean_exe «notion-highlight-export» where
  root := `NotionHighlightExport
