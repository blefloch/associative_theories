# Scripts used to determine classes and generate Lean code

## Scripts used to find 456 associative theories

- `find_equation_id.py` comes directly from the Equational
  Theories Project https://github.com/teorth/equational_theories/

- `ATP_utils.py` is a collection of tools to call the Mace4/Prover9
  automated model builder and theorem prover; the paths to these
  scripts is hard-coded, they should be mace4, prover9, isofilter
  in the scripts/ directory

- `list_semigroup_equations.py` produces a list of semigroup
  equations.  It is saved as `data/associative-equations-list.txt`

- `semigroups-1.py` seeks implications between semigroup equations
  and their conjunctions and determines a list of 121 inequivalent
  equations (excluding the tautological one) and 456 equivalence
  classes of conjunctions thereof.  The output is written to
  `semigroups_to_rep_out.py` and `../data/long_classes.json` and
  `../data/eq_to_long_class.json`

- `countermodels.py` is generated (if absent) when running
  `semigroups-1.py` and collects countermodels used there

- `countermodels_5.py` provides more countermodels that are useful
  for some implications at order 5 (not used)

- `semigroups_to_rep_out.py` can be used as a Python module to
  access some of the information produced by `semigroups-1.py`

## Scripts to construct a comprehensive data file

- `organize_associative_theories.py` produces the main data file with
  all of the available information, `../data/associative_theories.json`

- `minimal_implications.py`

## Scripts producing Lean code for the formalization

- `generate_models.py` generates the Lean files for all countermodels
  used to disprove implications between associative theories

- `generate_theories.py` produces two Lean files, with the "early" and
  "long" representatives of associative theories

- `generate_equiv.py` produces Lean files with the proof that
  the "early" and "long" representatives of associative theories
  are equivalent
