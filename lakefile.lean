import Lake
open Lake DSL

package «Poe» where

require PlutusCore from git
  "https://github.com/input-output-hk/PlutusCoreBlaster" @ "main"

@[default_target]
lean_lib «Poe» where
