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

### Proofs converted from Vampire output and consequences
- `VampireProvenEquiv.lean` are cyclic implications in each equivalence class of associative equation
- `VampireProvenOne.lean` are a minimal set of implication to generate the single-equation implication graph
- `VampireProvenTwo.lean` are minimal implications of the form
  E∧E'∧E4512 ⊨ E'' (and similar with more equations)
- `OneImpliDeduced.lean` are implications between single equations that
  are deduced by assembling Vampire-proven basic implications

### Associative theories set-up
- `EquationIndex.lean` defines the type `EQIndex` with 122 values,
  and a mapping from this type to the equations themselves
- `AssociativeTheoriesIndex.lean` defines the type `ATIndex` with 456
  values, labelling the equivalence classes of conjunctions
- `AssociativeTheoriesEarly.lean` maps each `ATIndex` to the conjunction
  of the equations in its early representative
- `AssociativeTheoriesLong.lean` maps each `ATIndex` to the conjunction
  of the equations in its long representative
- `EarlyLongEquiv.lean` proves the theorem `AT_equiv` stating that the
  conjunctions defined by the early and long representatives are
  equivalent in any magma

### Pure logic consequences
- `ImplicationsAT/ImplicationsAT1.lean` (for indices from 1 to 24)
  defines functions such as `AT15_impliesQ` (and likewise with indices
  from 1 to 456) mapping each `ATIndex` to a boolean stating whether
  `at15` implies it, and defines the corresponding theorem stating that
  the associative theory `AssociativeTheory15` implies another one
  whenever the boolean test gives true; this relies only on `AT_equiv`
- `ImplicationsAT.lean` assembles these boolean functions into
  `AT_impliesQ` and individual theorems into a single theorem
  `AT_implies`

### Individual equations and conjunctions
- `Conjunction/Conjunction10.lean` (for indices from 1 to 456) defines a
  map `conj10 : EQIndex -> ATIndex` mapping an equation to the
  associative theory resulting from adding that equation to the given
  theory.  For each equation (and each associative theory) it proves the
  equivalence to the appropriate associative theory.  These are
  assembled into a theorem `AT10_conj`
- `Conjunction.lean` assembles the theorems into the main theorem
  `AT_conj` which states that for any associative theory and any
  equation there exists an associative theory that is equivalent to it
- `EQATEquiv.lean` gives a corolloray stating that any equation is
  equivalent to some associative theory

### Countermodels
- `Countermodels/Model0.lean` etc. each contain one model, with the
  information of which equations it satisfies
- `Countermodels.lean` imports all of the models
