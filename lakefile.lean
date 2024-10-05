import Lake
open Lake DSL

package mil where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]
  -- moreLinkArgs := #[
  --   "-L./.lake/packages/LeanCopilot/.lake/build/lib",
  --   "-lctranslate2"
  -- ]
@[default_target]
lean_lib MIL where

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v4.14.0"
