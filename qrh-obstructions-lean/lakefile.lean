import Lake
open Lake DSL

package qrh_obstructions_lean where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "6015dbbfc399f4548bafd46f9560ff61595fd328"

@[default_target]
lean_lib Obstructions

@[default_target]
lean_lib MetaplecticDictionary
