import associative_theories.Conjunction

open ATIndex
open EQIndex

def EQand (eqids : List EQIndex) (G : Type*) [Magma G] : Prop :=
match eqids with
| [] => True
| eqid::rest => (EQeq eqid G) ∧ (EQand rest G)

def reduce_conj : List EQIndex -> ATIndex
| [] => at1
| eqid::rest => conj (reduce_conj rest) eqid

theorem conj_equiv_AT (eqids : List EQIndex) :
  ∀ (G : Type*) [Magma G], (Equation4512 G) ∧ (EQand eqids G) <-> ATearly (reduce_conj eqids) G :=
match eqids with
| [] => by
  unfold EQand reduce_conj ATearly
  simp
  tauto
| eqid::rest => fun G inst => ⟨by
  intro ⟨h4512, heqid, hrest⟩
  have atrest := (conj_equiv_AT rest G).mp ⟨h4512, hrest⟩
  exact (AT_conj (reduce_conj rest) eqid G).mp ⟨atrest, heqid⟩
  ,
  by
  intro h
  have ⟨atrest, heqid⟩ := (AT_conj (reduce_conj rest) eqid G).mpr h
  have ⟨h4512, hrest⟩ := (conj_equiv_AT rest G).mpr atrest
  exact ⟨h4512, heqid, hrest⟩
⟩
