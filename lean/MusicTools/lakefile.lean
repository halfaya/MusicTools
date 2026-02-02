import Lake
open Lake DSL

package «MusicTools» {
  -- add any package configuration options here
}

lean_lib «Xml»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «MusicTools» {
  -- add any library configuration options here
}
