import Lake
open Lake DSL

package «adeu_lean» where

@[default_target]
lean_lib «AdeuCore» where
  globs := #[.submodules `AdeuCore]
