- `find_equation_id.py` comes directly from the Equational
  Theories Project https://github.com/teorth/equational_theories/

- `ATP_utils.py` is a collection of tools to call the Mace4/Prover9
  automated model builder and theorem prover

- `list_semigroup_equations.py` produces a list of semigroup
  equations.  It is saved as `data/associative-equations-list.txt`

- `semigroups-1.py` seeks implications between semigroup equations
  and their conjunctions and determines a list of 121 inequivalent
  equations (excluding the tautological one) and 456 equivalence
  classes of conjunctions thereof

- `countermodels.py` provides a list of countermodels used by
  `semigroups-1.py`

- `countermodels_5.py` provides more countermodels that are useful
  for some implications at order 5
