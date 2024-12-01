This is a public repository for a prototype cubical proof assistant. The type theory is a two level type theory with a cubical "inner" layer and an "outer" layer which validates uniqueness of identity proofs. The cubical layer currently includes extension and partial types and systems. 

This prototype is for experimenting with conversion checking in cubical type theory. We want to develop a conversion checking algorithm that is similar to one used in practice (in Cubical Agda, redtt) while also being able to reason about the properties of the algorithm (soundness, completeness). The conversion checking algorithm that is currently implemented in inspired by the algorithm in [Harper-Stone ](https://www.cs.cmu.edu/~rwh/papers/singletons/tocl-revised.pdf).

see notes.pdf for operational semantics

todo for public repo
- define conversion monad, typechecking monad, typechecking/conversion environments, and monadic operations on cofib environment
- more documentation
- upload cubical examples
