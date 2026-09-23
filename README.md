# Associative equational theories

A project to determine implications between conjunctions of 738 equational laws of semigroups, and formalize them in the Lean4 proof assistant language. Sequel to the Equational Theories Project.

Running `lake exe cache get` (the first time only?) before `lake build` seems useful as it avoids having to recompile Mathlib from source.  It makes the `.lake/` directory somewhat smaller, at «only» 6.8GB.

## Lean-related files
- `associative_theories.lean` is the main Lean file
- `associative_theories` is the directory containing all new proofs and countermodels
- `equational_theories` is code imported from the ETP
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` are bookkeeping files for Lean

## Other files
- `CITATION.cff` gives information on how to cite this project
- `commentary` describes some features of individual associative theories
- `data` contains the output of the project, mostly as json files
- `LICENSE` has the license
- `paper` contains the TeX files for the paper
- `README-Lean.md` describes how the Lean code is organized
- `scripts` has (mostly) Python scripts to generate the data
