import Lake
open Lake DSL

package «ct-lean» where
  -- add package configuration options here

lean_lib «CtLean» where
  -- add library configuration options here

@[default_target]
lean_exe «ct-lean» where
  root := `Main
