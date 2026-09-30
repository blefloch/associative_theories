import equational_theories.Equations.All
import associative_theories.Countermodels
import associative_theories.VampireProvenEquiv
import associative_theories.VampireProvenOne
import associative_theories.VampireProvenTwo
import associative_theories.OneImpliDeduced
import associative_theories.AssociativeTheoriesEarly
import associative_theories.AssociativeTheoriesLong
import associative_theories.EarlyLongEquiv
import associative_theories.ImplicationsAT
import associative_theories.Conjunction
import associative_theories.EQATEquiv

open VampireProven in
#check (Equation613_4512_implies_Equation2 : ∀ (G : Type*) [Magma G],
  (Equation613 G) -> (Equation4512 G) -> Equation2 G)

open ATIndex
open EQIndex

#check (AT_conj : ∀ (atid : ATIndex), ∀ (eqid : EQIndex), ∃ (atid2 : ATIndex),
  ∀ (G: Type*) [Magma G], (ATearly atid G) ∧ (EQeq eqid G) <-> (ATearly atid2 G))

#check (EQ_equiv : ∀ (eqid : EQIndex), ∀ (G : Type*) [Magma G],
  (Equation4512 G) ∧ (EQeq eqid G) <-> ATearly (EQ_to_AT eqid) G)
