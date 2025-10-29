import Lake

open Lake DSL

package «MutualInduction» where

version := v!"0.1.0"
description := "A mutual induction tactic for Lean 4."
license := "Zlib"
reservoir := true

@[default_target]
lean_lib «MutualInduction» where
  roots := #[`MutualInduction, `Joint]
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «MkAll» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[test_driver]
lean_lib «Test» where
  globs := #[`MutualInductionTest.+, `JointTest.+, `AllTest.+]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.fieldNotation, false⟩,
    ⟨`pp.proofs, true⟩
  ]
