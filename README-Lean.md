# Organization of the Lean4 code

The main file is `associative_theories.lean`, which loads files containing various theorems.

## The equational_theories directory comes from the Equational Theories Project

### Set up
- `Magma.lean` defines the class `Magma` and conversions to `Add` and `Mul`
- `Homomorphisms.lean` defines `MagmaHom` and `MagmaEquiv`, and various theorems about composition
- `FreeMagma.lean` defines free magmas as binary trees with leaves of any given type, conversion to JSON or to strings, maps from free magmas to magmas, universal properties, the notion of evaluating an expression (element of a free magma over α) in a given magma (using a map from α to the magma), length, left-most/right-most leaf, etc.
- `MagmaLaw.lean` defines the structure `MagmaLaw` consisting of a pair of free magma elements, and `NatMagmaLaw` as the important case where leaves are natural numbers.  It defines the notion for a magma to satisfy a magma law.  The rest is **still mysterious**.

### About implications
- `Preorder.lean` defines implication/equivalence between magma laws
- `ParseImplications.lean`
- `EquationalResult.lean` defines the `@[equational_result]` attribute and related tools

### Listing equations
- `EquationLawConversion.lean` (only depends on `MagmaLaw.lean`)
- `Equations/Command.lean`
- `Equations/Basic.lean`, `Equations/Eqns1_999.lean` (etc for higher numbers) just list `equation 1 := x=x` etc.
- `Equations/All.lean` loads all of these and `EquationalResult.lean`.
- `Equations/LawsComplete.lean` proves `laws_complete`, namely the list of laws of order ≤4 is complete.

## The associative_theories directory

### Conjectures (to be proven with Vampire)
- `ConjecturesOneEquiv.lean` are cyclic implications in each equivalence class of associative equation
- `ConjecturesOneImpli.lean` are a minimal set of implication to generate the single-equation implication graph
- `ConjecturesTwo.lean` are minimal implications of the form E∧E'∧E4512 ⊨ E''

### Countermodels
- `Countermodels.lean` imports all of the models
- `Model0.lean` etc. each contain one model, with the information of which equations it satisfies

### Theorems
- `OneImpliDeduced.lean` are implications between single equations that are deduced from others
