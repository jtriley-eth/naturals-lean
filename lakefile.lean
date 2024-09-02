import Lake
open Lake DSL

package «naturals» where
  -- add package configuration options here

lean_lib «Naturals» where
  -- add library configuration options here

@[default_target]
lean_exe «naturals» where
  root := `Main
