import Lake

open Lake DSL

package «MutualInduction» where

@[default_target]
lean_lib «MutualInduction» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[test_driver]
lean_lib «MutualInductionTest» where
  globs := #[`MutualInductionTest.+]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.fieldNotation, false⟩,
    ⟨`pp.proofs, true⟩
  ]
