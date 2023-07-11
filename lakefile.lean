import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package «ant-lorentz» {
  -- add package configuration options here
}

@[default_target]
lean_lib «AntLorentz» {
  -- add library configuration options here
  globs := #[
    .andSubmodules `AntLorentz]
}
