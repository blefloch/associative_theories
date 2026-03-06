# Associative equational theories

A project to determine implications between conjunctions of 738 equational laws of semigroups, and formalize them in the Lean4 proof assistant language. Sequel to the Equational Theories Project.

Running `lake exe cache get` (the first time only?) before `lake build` seems useful as it avoids having to recompile Mathlib from source.  It makes the `.lake/` directory somewhat smaller, at «only» 6.8GB.
