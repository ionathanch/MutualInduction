import Lake

open Lake DSL

package «MutualInduction» where

@[default_target]
lean_lib «MutualInduction» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «MkAll» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[test_driver]
lean_lib «Test» where
  globs := #[`MutualInductionTest.+, `AllTest.+]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.fieldNotation, false⟩,
    ⟨`pp.proofs, true⟩
  ]
