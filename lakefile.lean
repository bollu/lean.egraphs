import Lake
open Lake DSL

package «egg» {
  -- add package configuration options here
}

lean_lib «Egg» {
  -- add library configuration options here
}

@[default_target]
lean_exe «egg» {
  root := `Main
}

require std from git "https://github.com/leanprover/std4" @ "main"
require Mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"
