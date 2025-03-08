import Lake

open Lake DSL

package «MutualInduction» where

@[default_target]
lean_lib «MutualInduction» where
  leanOptions := #[⟨`autoImplicit, false⟩]

lean_lib «Examples» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.fieldNotation, false⟩,
    ⟨`pp.proofs, true⟩
  ]
