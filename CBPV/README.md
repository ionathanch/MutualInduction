# Call-by-Push-Value

This is an example proof development on the metatheory of call-by-push-value,
which makes heavy use of mutual induction,
since the syntax of terms is mutually defined.

```
A ::= Unit | A + A | U B
B ::= A → B | B & B | F A

v ::= x | () | inl v | inr v | {v}
m ::= v! | λx. m | m v | return v | let x ← m in m
  | case v of {inl x => m ; inr x => m}
  | (m, m) | m.1 | m.2
```

This means that everything from reduction to typing to the logical relation
are all mutually defined, and eliminating them generally requires mutual induction.

## Development structure and dependency graph

The structure of the proofs begins with the usual basics.

* RTC.lean: Reflexive, transitive closure of binary relations
* Syntax.lean: Syntax, renaming, substitution, and contexts
* Typing.lean: Typing rules, renaming, and weakening
* Evaluation.lean: Evaluation of (closed) commands,
  which doesn't evaluate under binders and branches
* Reduction.lean: Small-step reduction semantics for values and commands,
  which reduces everywhere to normal form

The primary goal of the development is to prove strong normalization:
all reduction paths are normalizing.

* NormalInd.lean: An inductive characterization of strongly normal and neutral terms,
  as well as a notion of strong reduction.
* NormalAcc.lean: The traditional definition of strong normalization
  as an accessibility predicate with respect to reduction.
* OpenSemantics.lean: A logical relation between types and sets of terms
  that are backwards closed with respect to strong reduction.
* Soundness.lean: Semantic typing, defined in terms of the logical relation,
  and the fundamental theorem that syntactic typing implies semantic typing.
* Normalization.lean: Syntactic typing implies semantic typing
  implies strong normalization (inductive)
  implies strong normalization (traditional).

Remaining proof files show interesting properties of CBPV.

* LeftmostOutermost.lean: A deterministic single-step reduction semantics
  based on strong reduction, proven to step to normal forms.
* ClosedSemantics.lean: A logical relations proof that closed, well-typed terms
  are strongly normalizing with respect to evaluation.
* CBV.lean, CBN.lean: Translations from STLC with fine-grained CBV and CBN semantics,
  along with proofs that they preserve well-typedness and CK machine semantics.
* Antisubstitution.lean (fails checking): An unused substitution lemma,
  similar to the antirenaming lemma.

```
        ╭──────────RTC──────┬─────────╮
        ├───────┬──Syntax───┼─────────┤
        │       │           │         │
        ▼       ▼           ▼         ▼
Evaluation    Typing    NormalInd    Reduction
   │          │ │  │        │  │         │    
   ▼          ▼ │  │        ▼  ╰─────────│─────► LeftmostOutermost
ClosedSemantics │  │  OpenSemantics      │       Antisubstitution
                │  │    │                │
                ▼  ▼    ▼                ▼
              CBV  Soundness         NormalAcc
              CBN         │           │
                          ▼           ▼
                          Normalization
```