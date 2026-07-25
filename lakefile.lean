import Lake
open Lake DSL

package «Poe» where
  -- Deliberately dependency-free for increment 1 (see PLAN.md).
  -- Increment 2 adds:
  --   require PlutusCore from git
  --     "https://github.com/input-output-hk/PlutusCoreBlaster" @ "main"

@[default_target]
lean_lib «Poe» where
