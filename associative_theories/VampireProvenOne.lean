import equational_theories.Superposition
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
import equational_theories.Equations.All

/- Generated file collecting results about single equations -/

namespace VampireProven

theorem Equation2_4512_implies_Equation4 (G : Type*) [Magma G]
    (h2 : Equation2 G) (_ : Equation4512 G) : Equation4 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : X0 = X1 := mod_symm (h2 ..)
  have eq13 : sK0 ≠ (sK0 ◇ sK1) := mod_symm nh
  subsumption eq13 eq11

theorem Equation2_4512_implies_Equation5 (G : Type*) [Magma G]
    (h2 : Equation2 G) (_ : Equation4512 G) : Equation5 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : X0 = X1 := mod_symm (h2 ..)
  have eq13 : sK0 ≠ (sK1 ◇ sK0) := mod_symm nh
  subsumption eq13 eq11

theorem Equation2_4512_implies_Equation14 (G : Type*) [Magma G]
    (h2 : Equation2 G) (_ : Equation4512 G) : Equation14 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : X0 = X1 := mod_symm (h2 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation2_4512_implies_Equation41 (G : Type*) [Magma G]
    (h2 : Equation2 G) (_ : Equation4512 G) : Equation41 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : X0 = X1 := mod_symm (h2 ..)
  have eq13 : (sK1 ◇ sK2) ≠ (sK0 ◇ sK0) := mod_symm nh
  subsumption eq13 eq11

theorem Equation2_4512_implies_Equation66 (G : Type*) [Magma G]
    (h2 : Equation2 G) (_ : Equation4512 G) : Equation66 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : X0 = X1 := mod_symm (h2 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3_4512_implies_Equation8 (G : Type*) [Magma G]
    (h3 : Equation3 G) (_ : Equation4512 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq9 (X0 : G) : (X0 ◇ X0) = X0 := mod_symm (h3 ..)
  have eq11 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 : sK0 ≠ (sK0 ◇ sK0) := superpose eq9 eq11 -- forward demodulation 11,9
  subsumption eq12 eq9

theorem Equation3_4512_implies_Equation47 (G : Type*) [Magma G]
    (h3 : Equation3 G) (_ : Equation4512 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq9 (X0 : G) : (X0 ◇ X0) = X0 := mod_symm (h3 ..)
  have eq11 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq9 eq12 -- forward demodulation 12,9
  subsumption eq13 eq9

theorem Equation3_4512_implies_Equation3309 (G : Type*) [Magma G]
    (h3 : Equation3 G) (h4512 : Equation4512 G) : Equation3309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq10 (X0 : G) : (X0 ◇ X0) = X0 := mod_symm (h3 ..)
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq12 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq10 eq12 -- forward demodulation 12,10
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq10 eq11 -- superposition 11,10
  have eq25 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq13 -- superposition 13,14
  subsumption eq25 rfl

theorem Equation4_4512_implies_Equation10 (G : Type*) [Magma G]
    (h4 : Equation4 G) (_ : Equation4512 G) : Equation10 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = X0 := mod_symm (h4 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4_4512_implies_Equation11 (G : Type*) [Magma G]
    (h4 : Equation4 G) (_ : Equation4512 G) : Equation11 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = X0 := mod_symm (h4 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4_4512_implies_Equation38 (G : Type*) [Magma G]
    (h4 : Equation4 G) (_ : Equation4512 G) : Equation38 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = X0 := mod_symm (h4 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq16 eq11

theorem Equation4_4512_implies_Equation56 (G : Type*) [Magma G]
    (h4 : Equation4 G) (_ : Equation4512 G) : Equation56 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = X0 := mod_symm (h4 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation5_4512_implies_Equation10 (G : Type*) [Magma G]
    (h5 : Equation5 G) (_ : Equation4512 G) : Equation10 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = X0 := mod_symm (h5 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq16 eq11

theorem Equation5_4512_implies_Equation16 (G : Type*) [Magma G]
    (h5 : Equation5 G) (_ : Equation4512 G) : Equation16 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = X0 := mod_symm (h5 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq16 : sK0 ≠ (sK1 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq16 eq11

theorem Equation5_4512_implies_Equation39 (G : Type*) [Magma G]
    (h5 : Equation5 G) (_ : Equation4512 G) : Equation39 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = X0 := mod_symm (h5 ..)
  have eq13 : (sK1 ◇ sK0) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq16 : sK0 ≠ (sK1 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq16 eq11

theorem Equation5_4512_implies_Equation75 (G : Type*) [Magma G]
    (h5 : Equation5 G) (_ : Equation4512 G) : Equation75 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = X0 := mod_symm (h5 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq16 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq17 : sK0 ≠ (sK1 ◇ sK0) := superpose eq11 eq16 -- forward demodulation 16,11
  subsumption eq17 eq11

theorem Equation8_4512_implies_Equation411 (G : Type*) [Magma G]
    (h8 : Equation8 G) (_ : Equation4512 G) : Equation411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq9 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := mod_symm (h8 ..)
  have eq11 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq12 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq11 -- forward demodulation 11,9
  subsumption eq12 eq9

theorem Equation8_4512_implies_Equation3306 (G : Type*) [Magma G]
    (h8 : Equation8 G) (h4512 : Equation4512 G) : Equation3306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := mod_symm (h8 ..)
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq12 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq10 eq11 -- superposition 11,10
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq29 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq12 -- superposition 12,18
  subsumption eq29 rfl

theorem Equation8_4512_implies_Equation3319 (G : Type*) [Magma G]
    (h8 : Equation8 G) (_ : Equation4512 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := mod_symm (h8 ..)
  have eq12 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq10 eq12 -- forward demodulation 12,10
  subsumption eq13 rfl

theorem Equation10_4512_implies_Equation3 (G : Type*) [Magma G]
    (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h10 ..)
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq12 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq24 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq11 eq10 -- superposition 10,11
  have eq34 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq24 -- superposition 24,10
  have eq84 : sK0 ≠ sK0 := superpose eq34 eq12 -- superposition 12,34
  subsumption eq84 rfl

theorem Equation10_4512_implies_Equation329 (G : Type*) [Magma G]
    (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation329 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h10 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq25 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq27 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq51 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ (X2 ◇ X0)) := superpose eq25 eq27 -- superposition 27,25
  have eq112 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq51 eq13 -- superposition 13,51
  subsumption eq112 rfl

theorem Equation10_4512_implies_Equation419 (G : Type*) [Magma G]
    (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation419 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h10 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq25 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq31 : sK0 ≠ (sK0 ◇ sK0) := superpose eq25 eq13 -- backward demodulation 13,25
  have eq36 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq25 -- superposition 25,11
  have eq54 : sK0 ≠ sK0 := superpose eq36 eq31 -- superposition 31,36
  subsumption eq54 rfl

theorem Equation11_4512_implies_Equation419 (G : Type*) [Magma G]
    (h11 : Equation11 G) (h4512 : Equation4512 G) : Equation419 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := mod_symm (h11 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq21 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq20 eq13 -- backward demodulation 13,20
  subsumption eq21 eq11

theorem Equation11_4512_implies_Equation440 (G : Type*) [Magma G]
    (h11 : Equation11 G) (_ : Equation4512 G) : Equation440 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := mod_symm (h11 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq14 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation11_4512_implies_Equation3331 (G : Type*) [Magma G]
    (h11 : Equation11 G) (h4512 : Equation4512 G) : Equation3331 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := mod_symm (h11 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq49 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq18 eq20 -- superposition 20,18
  have eq93 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq49 eq13 -- superposition 13,49
  subsumption eq93 rfl

theorem Equation14_4512_implies_Equation11 (G : Type*) [Magma G]
    (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation11 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := mod_symm (h14 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq54 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq11 eq25 -- superposition 25,11
  have eq87 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq54 eq11 -- superposition 11,54
  have eq91 (X0 : G) : sK0 ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq54 eq13 -- superposition 13,54
  subsumption eq91 eq87

theorem Equation14_4512_implies_Equation16 (G : Type*) [Magma G]
    (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation16 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := mod_symm (h14 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq54 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq11 eq25 -- superposition 25,11
  have eq83 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq54 eq25 -- superposition 25,54
  have eq87 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq54 eq11 -- superposition 11,54
  have eq102 (X0 X2 : G) : (X0 ◇ X2) = (X2 ◇ X0) := superpose eq87 eq83 -- backward demodulation 83,87
  have eq103 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq102 eq13 -- backward demodulation 13,102
  subsumption eq103 eq11

theorem Equation14_4512_implies_Equation477 (G : Type*) [Magma G]
    (h14 : Equation14 G) (_ : Equation4512 G) : Equation477 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := mod_symm (h14 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq14 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation14_4512_implies_Equation3350 (G : Type*) [Magma G]
    (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation3350 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := mod_symm (h14 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq54 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq11 eq25 -- superposition 25,11
  have eq83 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq54 eq25 -- superposition 25,54
  have eq87 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq54 eq11 -- superposition 11,54
  have eq104 (X0 X2 : G) : (X0 ◇ X2) = (X2 ◇ X0) := superpose eq87 eq83 -- backward demodulation 83,87
  have eq105 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq87 eq13 -- backward demodulation 13,87
  subsumption eq105 eq104

theorem Equation16_4512_implies_Equation419 (G : Type*) [Magma G]
    (h16 : Equation16 G) (_ : Equation4512 G) : Equation419 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h16 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation16_4512_implies_Equation513 (G : Type*) [Magma G]
    (h16 : Equation16 G) (_ : Equation4512 G) : Equation513 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h16 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq14 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation16_4512_implies_Equation3388 (G : Type*) [Magma G]
    (h16 : Equation16 G) (h4512 : Equation4512 G) : Equation3388 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h16 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = X2 := superpose eq11 eq12 -- superposition 12,11
  have eq22 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := superpose eq12 eq16 -- forward demodulation 16,12
  have eq65 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq11 eq22 -- superposition 22,11
  have eq251 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq65 eq13 -- superposition 13,65
  subsumption eq251 rfl

theorem Equation38_4512_implies_Equation311 (G : Type*) [Magma G]
    (h38 : Equation38 G) (_ : Equation4512 G) : Equation311 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := mod_symm (h38 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK2)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation38_4512_implies_Equation327 (G : Type*) [Magma G]
    (h38 : Equation38 G) (_ : Equation4512 G) : Equation327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := mod_symm (h38 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation38_4512_implies_Equation329 (G : Type*) [Magma G]
    (h38 : Equation38 G) (_ : Equation4512 G) : Equation329 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := mod_symm (h38 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation38_4512_implies_Equation3331 (G : Type*) [Magma G]
    (h38 : Equation38 G) (_ : Equation4512 G) : Equation3331 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := mod_symm (h38 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation39_4512_implies_Equation318 (G : Type*) [Magma G]
    (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := mod_symm (h39 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq14 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 : G) : (X0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ sK0)) := superpose eq11 eq14 -- superposition 14,11
  have eq39 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ X2) := superpose eq15 eq12 -- superposition 12,15
  have eq52 (X0 X1 : G) : (X0 ◇ (X1 ◇ sK0)) ≠ (sK1 ◇ (X0 ◇ (X1 ◇ sK0))) := superpose eq12 eq16 -- superposition 16,12
  subsumption eq52 eq39

theorem Equation39_4512_implies_Equation329 (G : Type*) [Magma G]
    (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation329 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := mod_symm (h39 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq11 eq14 -- superposition 14,11
  have eq39 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ X2) := superpose eq15 eq12 -- superposition 12,15
  have eq53 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X1 ◇ (X0 ◇ sK1)) := superpose eq15 eq16 -- superposition 16,15
  subsumption eq53 eq39

theorem Equation39_4512_implies_Equation343 (G : Type*) [Magma G]
    (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := mod_symm (h39 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq25 (X0 : G) : (X0 ◇ sK1) ≠ (sK2 ◇ (X0 ◇ sK1)) := superpose eq14 eq13 -- superposition 13,14
  have eq37 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ X2) := superpose eq14 eq12 -- superposition 12,14
  have eq50 (X0 X1 : G) : (X0 ◇ (X1 ◇ sK1)) ≠ (sK2 ◇ (X0 ◇ (X1 ◇ sK1))) := superpose eq12 eq25 -- superposition 25,12
  subsumption eq50 eq37

theorem Equation39_4512_implies_Equation3388 (G : Type*) [Magma G]
    (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation3388 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := mod_symm (h39 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq14 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq41 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ X2) := superpose eq15 eq12 -- superposition 12,15
  have eq77 (X0 : G) : (sK0 ◇ sK1) ≠ (sK2 ◇ (X0 ◇ sK1)) := superpose eq41 eq14 -- superposition 14,41
  subsumption eq77 eq41

theorem Equation40_4512_implies_Equation3259 (G : Type*) [Magma G]
    (h40 : Equation40 G) (h4512 : Equation4512 G) : Equation3259 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := mod_symm (h40 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq21 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq81 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq21 eq13 -- superposition 13,21
  subsumption eq81 eq11

theorem Equation40_4512_implies_Equation3271 (G : Type*) [Magma G]
    (h40 : Equation40 G) (h4512 : Equation4512 G) : Equation3271 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := mod_symm (h40 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq21 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq11 eq12 -- superposition 12,11
  have eq88 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq21 eq13 -- superposition 13,21
  subsumption eq88 eq11

theorem Equation40_4512_implies_Equation4297 (G : Type*) [Magma G]
    (h40 : Equation40 G) (h4512 : Equation4512 G) : Equation4297 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := mod_symm (h40 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq18 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq32 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq20 -- superposition 20,11
  have eq162 (X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ X1) ◇ sK1) := superpose eq32 eq18 -- superposition 18,32
  subsumption eq162 eq20

theorem Equation41_4512_implies_Equation38 (G : Type*) [Magma G]
    (h41 : Equation41 G) (_ : Equation4512 G) : Equation38 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ X2) := mod_symm (h41 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK1) := mod_symm nh
  subsumption eq13 eq11

theorem Equation41_4512_implies_Equation39 (G : Type*) [Magma G]
    (h41 : Equation41 G) (_ : Equation4512 G) : Equation39 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ X2) := mod_symm (h41 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := mod_symm nh
  subsumption eq13 eq11

theorem Equation41_4512_implies_Equation314 (G : Type*) [Magma G]
    (h41 : Equation41 G) (_ : Equation4512 G) : Equation314 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ X2) := mod_symm (h41 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation41_4512_implies_Equation332 (G : Type*) [Magma G]
    (h41 : Equation41 G) (_ : Equation4512 G) : Equation332 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ X2) := mod_symm (h41 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 (X1 X2 X3 X4 : G) : (X1 ◇ X2) = (X3 ◇ X4) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (X0 ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq18 eq14

theorem Equation41_4512_implies_Equation3350 (G : Type*) [Magma G]
    (h41 : Equation41 G) (_ : Equation4512 G) : Equation3350 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ X2) := mod_symm (h41 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq14 (X1 X2 X3 X4 : G) : (X1 ◇ X2) = (X3 ◇ X4) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (X0 ◇ X1))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq18 eq14

theorem Equation43_4512_implies_Equation4358 (G : Type*) [Magma G]
    (h43 : Equation43 G) (_ : Equation4512 G) : Equation4358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h43 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 rfl

theorem Equation43_4512_implies_Equation4362 (G : Type*) [Magma G]
    (h43 : Equation43 G) (h4512 : Equation4512 G) : Equation4362 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h43 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11
  have eq72 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := superpose eq17 eq13 -- superposition 13,17
  have eq87 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq11 eq72 -- forward demodulation 72,11
  subsumption eq87 rfl

theorem Equation43_4512_implies_Equation4364 (G : Type*) [Magma G]
    (h43 : Equation43 G) (h4512 : Equation4512 G) : Equation4364 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h43 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11
  have eq73 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := superpose eq18 eq14 -- superposition 14,18
  have eq88 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq11 eq73 -- forward demodulation 73,11
  subsumption eq88 rfl

theorem Equation43_4512_implies_Equation4369 (G : Type*) [Magma G]
    (h43 : Equation43 G) (h4512 : Equation4512 G) : Equation4369 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h43 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK0 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11
  have eq74 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq18 eq14 -- superposition 14,18
  subsumption eq74 rfl

theorem Equation47_4512_implies_Equation1 (G : Type*) [Magma G]
    (_ : Equation47 G) (_ : Equation4512 G) : Equation1 G := by
  intro x
  rfl
theorem Equation56_4512_implies_Equation47 (G : Type*) [Magma G]
    (h56 : Equation56 G) (_ : Equation4512 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h56 ..)
  have eq12 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  subsumption eq12 eq10

theorem Equation66_4512_implies_Equation43 (G : Type*) [Magma G]
    (h66 : Equation66 G) (h4512 : Equation4512 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h66 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq14 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq14 eq11 -- superposition 11,14
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq12 eq26 -- forward demodulation 26,12
  have eq38 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq12 eq15 -- superposition 15,12
  have eq39 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq12 eq15 -- superposition 15,12
  have eq53 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq14 eq24 -- superposition 24,14
  have eq121 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq39 eq27 -- superposition 27,39
  have eq286 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq53 eq53 -- superposition 53,53
  have eq331 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq38 eq286 -- forward demodulation 286,38
  have eq332 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) := superpose eq53 eq331 -- forward demodulation 331,53
  have eq333 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq121 eq332 -- forward demodulation 332,121
  have eq334 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq11 eq333 -- forward demodulation 333,11
  have eq546 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq334 eq13 -- superposition 13,334
  subsumption eq546 rfl

theorem Equation66_4512_implies_Equation56 (G : Type*) [Magma G]
    (h66 : Equation66 G) (h4512 : Equation4512 G) : Equation56 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h66 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq12 eq26 -- forward demodulation 26,12
  have eq124 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose eq24 eq27 -- superposition 27,24
  have eq604 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := superpose eq124 eq11 -- superposition 11,124
  have eq620 (X0 : G) : sK0 ≠ (sK0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq124 eq13 -- superposition 13,124
  subsumption eq620 eq604

theorem Equation66_4512_implies_Equation75 (G : Type*) [Magma G]
    (h66 : Equation66 G) (h4512 : Equation4512 G) : Equation75 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h66 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq14 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq14 eq11 -- superposition 11,14
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq12 eq26 -- forward demodulation 26,12
  have eq39 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq12 eq15 -- superposition 15,12
  have eq121 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq39 eq27 -- superposition 27,39
  have eq136 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := superpose eq121 eq13 -- backward demodulation 13,121
  subsumption eq136 eq39

theorem Equation66_4512_implies_Equation4276 (G : Type*) [Magma G]
    (h66 : Equation66 G) (h4512 : Equation4512 G) : Equation4276 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h66 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq12 eq26 -- forward demodulation 26,12
  have eq124 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := superpose eq24 eq27 -- superposition 27,24
  have eq619 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq124 eq13 -- superposition 13,124
  subsumption eq619 eq124

theorem Equation75_4512_implies_Equation47 (G : Type*) [Magma G]
    (h75 : Equation75 G) (_ : Equation4512 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq10 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h75 ..)
  have eq12 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  subsumption eq12 eq10

theorem Equation307_4512_implies_Equation3253 (G : Type*) [Magma G]
    (h307 : Equation307 G) (_ : Equation4512 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq9 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h307 ..)
  have eq11 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq11 -- forward demodulation 11,9
  subsumption eq12 eq9

theorem Equation308_4512_implies_Equation3255 (G : Type*) [Magma G]
    (h308 : Equation308 G) (_ : Equation4512 G) : Equation3255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h308 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation308_4512_implies_Equation3256 (G : Type*) [Magma G]
    (h308 : Equation308 G) (_ : Equation4512 G) : Equation3256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h308 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation308_4512_implies_Equation4268 (G : Type*) [Magma G]
    (h308 : Equation308 G) (_ : Equation4512 G) : Equation4268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h308 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation309_4512_implies_Equation3264 (G : Type*) [Magma G]
    (h309 : Equation309 G) (h4512 : Equation4512 G) : Equation3264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h309 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq18 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12
  have eq39 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq18 eq13 -- superposition 13,18
  subsumption eq39 rfl

theorem Equation309_4512_implies_Equation4269 (G : Type*) [Magma G]
    (h309 : Equation309 G) (_ : Equation4512 G) : Equation4269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h309 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation310_4512_implies_Equation308 (G : Type*) [Magma G]
    (h310 : Equation310 G) (h4512 : Equation4512 G) : Equation308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h310 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq63 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq11 eq15 -- superposition 15,11
  have eq91 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq15 eq16 -- superposition 16,15
  have eq150 (X0 X3 : G) : (X0 ◇ X0) = ((X0 ◇ (X3 ◇ X3)) ◇ X0) := superpose eq63 eq91 -- forward demodulation 91,63
  have eq208 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq11 eq150 -- superposition 150,11
  have eq345 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq208 eq12 -- superposition 12,208
  have eq349 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq12 eq345 -- forward demodulation 345,12
  have eq398 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq15 eq24 -- superposition 24,15
  have eq497 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq398 eq349 -- backward demodulation 349,398
  have eq788 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq497 eq13 -- superposition 13,497
  subsumption eq788 rfl

theorem Equation310_4512_implies_Equation3258 (G : Type*) [Magma G]
    (h310 : Equation310 G) (_ : Equation4512 G) : Equation3258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h310 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation310_4512_implies_Equation3259 (G : Type*) [Magma G]
    (h310 : Equation310 G) (h4512 : Equation4512 G) : Equation3259 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h310 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X2 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq21 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq398 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq15 eq24 -- superposition 24,15
  have eq588 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq398 -- superposition 398,12
  have eq822 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ X2)) := superpose eq21 eq19 -- superposition 19,21
  have eq927 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq588 eq822 -- forward demodulation 822,588
  have eq928 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq927 -- forward demodulation 927,11
  have eq1666 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq928 eq13 -- superposition 13,928
  subsumption eq1666 rfl

theorem Equation310_4512_implies_Equation4288 (G : Type*) [Magma G]
    (h310 : Equation310 G) (h4512 : Equation4512 G) : Equation4288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h310 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq64 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq11 eq16 -- superposition 16,11
  have eq92 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq16 eq17 -- superposition 17,16
  have eq151 (X0 X3 : G) : (X0 ◇ X0) = ((X0 ◇ (X3 ◇ X3)) ◇ X0) := superpose eq64 eq92 -- forward demodulation 92,64
  have eq209 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq11 eq151 -- superposition 151,11
  have eq346 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq209 eq12 -- superposition 12,209
  have eq350 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq12 eq346 -- forward demodulation 346,12
  have eq399 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq16 eq25 -- superposition 25,16
  have eq498 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq399 eq350 -- backward demodulation 350,399
  have eq789 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq498 eq14 -- superposition 14,498
  subsumption eq789 rfl

theorem Equation311_4512_implies_Equation309 (G : Type*) [Magma G]
    (h311 : Equation311 G) (_ : Equation4512 G) : Equation309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h311 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation311_4512_implies_Equation3267 (G : Type*) [Magma G]
    (h311 : Equation311 G) (_ : Equation4512 G) : Equation3267 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h311 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation311_4512_implies_Equation4271 (G : Type*) [Magma G]
    (h311 : Equation311 G) (_ : Equation4512 G) : Equation4271 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h311 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation312_4512_implies_Equation3258 (G : Type*) [Magma G]
    (h312 : Equation312 G) (_ : Equation4512 G) : Equation3258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h312 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation312_4512_implies_Equation3278 (G : Type*) [Magma G]
    (h312 : Equation312 G) (_ : Equation4512 G) : Equation3278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h312 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq14 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation312_4512_implies_Equation4272 (G : Type*) [Magma G]
    (h312 : Equation312 G) (_ : Equation4512 G) : Equation4272 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h312 ..)
  have eq13 : (sK1 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation313_4512_implies_Equation309 (G : Type*) [Magma G]
    (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h313 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq53 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq14 eq13 -- superposition 13,14
  have eq125 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq15 -- superposition 15,15
  have eq146 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq12 eq125 -- forward demodulation 125,12
  have eq147 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq146 -- forward demodulation 146,15
  have eq148 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq147 -- forward demodulation 147,11
  have eq182 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq16 eq148 -- superposition 148,16
  have eq199 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq148 eq53 -- superposition 53,148
  subsumption eq199 eq182

theorem Equation313_4512_implies_Equation3273 (G : Type*) [Magma G]
    (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation3273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h313 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ X1) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq75 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq12 eq16 -- superposition 16,12
  have eq115 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq15 -- superposition 15,15
  have eq135 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq12 eq115 -- forward demodulation 115,12
  have eq136 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq135 -- forward demodulation 135,15
  have eq137 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq136 -- forward demodulation 136,11
  have eq139 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq137 eq75 -- backward demodulation 75,137
  have eq723 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X2))) = ((X2 ◇ (X2 ◇ X2)) ◇ X1) := superpose eq139 eq25 -- superposition 25,139
  have eq772 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq25 eq13 -- superposition 13,25
  have eq841 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X2)) = ((X2 ◇ X2) ◇ X1) := superpose eq11 eq723 -- forward demodulation 723,11
  have eq842 (X1 X2 : G) : (X2 ◇ X2) = ((X2 ◇ X2) ◇ X1) := superpose eq137 eq841 -- forward demodulation 841,137
  subsumption eq772 eq842

theorem Equation313_4512_implies_Equation3275 (G : Type*) [Magma G]
    (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation3275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h313 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq28 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq12 eq20 -- forward demodulation 20,12
  have eq77 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq11 eq16 -- superposition 16,11
  have eq100 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq77 -- forward demodulation 77,12
  have eq121 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq12 eq15 -- superposition 15,12
  have eq122 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq12 eq15 -- superposition 15,12
  have eq126 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq15 eq12 -- superposition 12,15
  have eq153 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq12 eq122 -- forward demodulation 122,12
  have eq154 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq153 eq121 -- backward demodulation 121,153
  have eq157 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq12 eq126 -- forward demodulation 126,12
  have eq158 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq157 -- forward demodulation 157,12
  have eq199 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X2 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq11 eq17 -- superposition 17,11
  have eq211 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq11 eq17 -- superposition 17,11
  have eq233 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = ((X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X3) := superpose eq12 eq17 -- superposition 17,12
  have eq238 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq11 eq17 -- superposition 17,11
  have eq244 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2) = (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) := superpose eq17 eq17 -- superposition 17,17
  have eq285 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq211 eq199 -- backward demodulation 199,211
  have eq309 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) := superpose eq154 eq233 -- forward demodulation 233,154
  have eq319 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq15 eq238 -- forward demodulation 238,15
  have eq320 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq12 eq319 -- forward demodulation 319,12
  have eq321 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq12 eq320 -- forward demodulation 320,12
  have eq322 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq15 eq321 -- forward demodulation 321,15
  have eq332 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq12 eq244 -- forward demodulation 244,12
  have eq333 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq12 eq332 -- forward demodulation 332,12
  have eq334 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2) := superpose eq158 eq333 -- forward demodulation 333,158
  have eq335 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = ((X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3))) ◇ X2) := superpose eq12 eq334 -- forward demodulation 334,12
  have eq336 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq309 eq335 -- forward demodulation 335,309
  have eq337 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq336 eq158 -- backward demodulation 158,336
  have eq341 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq337 eq322 -- backward demodulation 322,337
  have eq343 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq100 eq341 -- forward demodulation 341,100
  have eq346 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq343 eq28 -- backward demodulation 28,343
  have eq364 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq343 eq285 -- backward demodulation 285,343
  have eq1122 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq346 eq13 -- superposition 13,346
  subsumption eq1122 eq364

theorem Equation313_4512_implies_Equation3290 (G : Type*) [Magma G]
    (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation3290 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h313 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq14 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq16 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq116 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq16 eq16 -- superposition 16,16
  have eq136 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq12 eq116 -- forward demodulation 116,12
  have eq137 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq16 eq136 -- forward demodulation 136,16
  have eq138 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq137 -- forward demodulation 137,11
  have eq187 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq138 eq14 -- superposition 14,138
  subsumption eq187 rfl

theorem Equation313_4512_implies_Equation4301 (G : Type*) [Magma G]
    (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation4301 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h313 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq16 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq19 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ X1) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq12 eq19 -- forward demodulation 19,12
  have eq76 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq12 eq17 -- superposition 17,12
  have eq78 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq11 eq17 -- superposition 17,11
  have eq101 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq78 -- forward demodulation 78,12
  have eq116 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq16 eq16 -- superposition 16,16
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq12 eq16 -- superposition 16,12
  have eq123 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq12 eq16 -- superposition 16,12
  have eq127 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq16 eq12 -- superposition 12,16
  have eq136 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq12 eq116 -- forward demodulation 116,12
  have eq137 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq16 eq136 -- forward demodulation 136,16
  have eq138 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq137 -- forward demodulation 137,11
  have eq140 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq138 eq76 -- backward demodulation 76,138
  have eq154 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq12 eq123 -- forward demodulation 123,12
  have eq155 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq154 eq122 -- backward demodulation 122,154
  have eq158 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq12 eq127 -- forward demodulation 127,12
  have eq159 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq158 -- forward demodulation 158,12
  have eq209 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq18 eq18 -- superposition 18,18
  have eq217 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2) = (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) := superpose eq18 eq18 -- superposition 18,18
  have eq234 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = ((X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X3) := superpose eq12 eq18 -- superposition 18,12
  have eq239 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq11 eq18 -- superposition 18,11
  have eq245 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2) = (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) := superpose eq18 eq18 -- superposition 18,18
  have eq284 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X2))) = ((X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3))) ◇ X2) := superpose eq12 eq209 -- forward demodulation 209,12
  have eq285 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X2))) = ((X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X2) := superpose eq12 eq284 -- forward demodulation 284,12
  have eq289 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq12 eq217 -- forward demodulation 217,12
  have eq290 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq12 eq289 -- forward demodulation 289,12
  have eq291 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2) := superpose eq159 eq290 -- forward demodulation 290,159
  have eq292 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = ((X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3))) ◇ X2) := superpose eq12 eq291 -- forward demodulation 291,12
  have eq293 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = ((X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X2) := superpose eq12 eq292 -- forward demodulation 292,12
  have eq294 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = ((X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X2) := superpose eq159 eq293 -- forward demodulation 293,159
  have eq295 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq294 eq285 -- backward demodulation 285,294
  have eq310 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) := superpose eq155 eq234 -- forward demodulation 234,155
  have eq320 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq16 eq239 -- forward demodulation 239,16
  have eq321 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq12 eq320 -- forward demodulation 320,12
  have eq322 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq12 eq321 -- forward demodulation 321,12
  have eq323 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq16 eq322 -- forward demodulation 322,16
  have eq333 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq12 eq245 -- forward demodulation 245,12
  have eq334 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq12 eq333 -- forward demodulation 333,12
  have eq335 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2) := superpose eq159 eq334 -- forward demodulation 334,159
  have eq336 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = ((X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3))) ◇ X2) := superpose eq12 eq335 -- forward demodulation 335,12
  have eq337 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq310 eq336 -- forward demodulation 336,310
  have eq338 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq337 eq159 -- backward demodulation 159,337
  have eq341 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq338 eq295 -- backward demodulation 295,338
  have eq342 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq338 eq323 -- backward demodulation 323,338
  have eq344 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq101 eq342 -- forward demodulation 342,101
  have eq371 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq344 eq341 -- backward demodulation 341,344
  have eq724 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X2))) = ((X2 ◇ (X2 ◇ X2)) ◇ X1) := superpose eq140 eq26 -- superposition 26,140
  have eq841 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X2)) = ((X2 ◇ X2) ◇ X1) := superpose eq11 eq724 -- forward demodulation 724,11
  have eq842 (X1 X2 : G) : (X2 ◇ X2) = ((X2 ◇ X2) ◇ X1) := superpose eq138 eq841 -- forward demodulation 841,138
  have eq843 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq842 eq371 -- backward demodulation 371,842
  have eq1955 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq843 eq14 -- superposition 14,843
  subsumption eq1955 rfl

theorem Equation313_4512_implies_Equation4331 (G : Type*) [Magma G]
    (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation4331 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h313 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq14 : (sK1 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq16 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq116 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq16 eq16 -- superposition 16,16
  have eq136 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq12 eq116 -- forward demodulation 116,12
  have eq137 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq16 eq136 -- forward demodulation 136,16
  have eq138 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq137 -- forward demodulation 137,11
  have eq187 : (sK1 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq138 eq14 -- superposition 14,138
  subsumption eq187 rfl

theorem Equation314_4512_implies_Equation311 (G : Type*) [Magma G]
    (h314 : Equation314 G) (_ : Equation4512 G) : Equation311 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h314 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq76 (X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ X4)) = (X2 ◇ X2) := superpose eq17 eq14 -- superposition 14,17
  have eq102 (X0 X1 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (sK1 ◇ X1)) := superpose eq14 eq13 -- superposition 13,14
  subsumption eq102 eq76

theorem Equation314_4512_implies_Equation313 (G : Type*) [Magma G]
    (h314 : Equation314 G) (_ : Equation4512 G) : Equation313 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h314 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation314_4512_implies_Equation318 (G : Type*) [Magma G]
    (h314 : Equation314 G) (_ : Equation4512 G) : Equation318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h314 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq76 (X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ X4)) = (X2 ◇ X2) := superpose eq17 eq14 -- superposition 14,17
  have eq102 (X0 X1 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (sK2 ◇ X1)) := superpose eq14 eq13 -- superposition 13,14
  subsumption eq102 eq76

theorem Equation314_4512_implies_Equation3277 (G : Type*) [Magma G]
    (h314 : Equation314 G) (_ : Equation4512 G) : Equation3277 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h314 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation314_4512_implies_Equation4274 (G : Type*) [Magma G]
    (h314 : Equation314 G) (_ : Equation4512 G) : Equation4274 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h314 ..)
  have eq13 : (sK1 ◇ (sK0 ◇ sK2)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 : (sK1 ◇ (sK0 ◇ sK2)) ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation315_4512_implies_Equation312 (G : Type*) [Magma G]
    (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation312 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h315 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq15 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12
  have eq65 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq11 eq15 -- superposition 15,11
  have eq84 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq23 eq65 -- forward demodulation 65,23
  have eq135 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq84 eq13 -- superposition 13,84
  subsumption eq135 rfl

theorem Equation315_4512_implies_Equation3255 (G : Type*) [Magma G]
    (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation3255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h315 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12
  have eq52 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) := superpose eq14 eq13 -- superposition 13,14
  have eq64 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ (X0 ◇ sK0))) := superpose eq14 eq52 -- superposition 52,14
  have eq73 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq11 eq64 -- forward demodulation 64,11
  have eq82 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq11 eq15 -- superposition 15,11
  have eq101 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq23 eq82 -- forward demodulation 82,23
  have eq169 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq101 eq73 -- superposition 73,101
  subsumption eq169 rfl

theorem Equation315_4512_implies_Equation3271 (G : Type*) [Magma G]
    (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation3271 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h315 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq15 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12
  have eq65 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq11 eq15 -- superposition 15,11
  have eq84 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq23 eq65 -- forward demodulation 65,23
  have eq85 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq84 eq16 -- backward demodulation 16,84
  have eq100 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq85 -- superposition 85,12
  have eq328 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq100 eq13 -- superposition 13,100
  subsumption eq328 rfl

theorem Equation315_4512_implies_Equation4304 (G : Type*) [Magma G]
    (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation4304 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h315 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq14 : (sK1 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq16 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq24 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12
  have eq66 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq11 eq16 -- superposition 16,11
  have eq85 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq24 eq66 -- forward demodulation 66,24
  have eq136 : (sK1 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq85 eq14 -- superposition 14,85
  subsumption eq136 rfl

theorem Equation316_4512_implies_Equation40 (G : Type*) [Magma G]
    (h316 : Equation316 G) (_ : Equation4512 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := mod_symm (h316 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq16 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq23 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq23 eq16

theorem Equation316_4512_implies_Equation310 (G : Type*) [Magma G]
    (h316 : Equation316 G) (_ : Equation4512 G) : Equation310 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := mod_symm (h316 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq23 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq16 eq13 -- superposition 13,16
  have eq50 (X1 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq11 eq23 -- superposition 23,11
  subsumption eq50 eq15

theorem Equation316_4512_implies_Equation315 (G : Type*) [Magma G]
    (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := mod_symm (h316 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq16 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq27 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ X2) := superpose eq16 eq12 -- superposition 12,16
  have eq278 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X0) := superpose eq11 eq27 -- superposition 27,11
  have eq486 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq278 -- superposition 278,12
  have eq805 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq486 eq13 -- superposition 13,486
  subsumption eq805 eq16

theorem Equation316_4512_implies_Equation4299 (G : Type*) [Magma G]
    (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation4299 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := mod_symm (h316 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq16 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ X1)) := superpose eq16 eq11 -- superposition 11,16
  have eq29 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ X2) := superpose eq16 eq12 -- superposition 12,16
  have eq80 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq23 eq13 -- superposition 13,23
  have eq303 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X0) := superpose eq11 eq29 -- superposition 29,11
  have eq513 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ X2) := superpose eq12 eq303 -- superposition 303,12
  have eq835 (X0 X1 : G) : (X0 ◇ X0) ≠ (X1 ◇ X1) := superpose eq513 eq80 -- superposition 80,513
  subsumption eq835 eq16

theorem Equation318_4512_implies_Equation309 (G : Type*) [Magma G]
    (h318 : Equation318 G) (_ : Equation4512 G) : Equation309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h318 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation318_4512_implies_Equation3300 (G : Type*) [Magma G]
    (h318 : Equation318 G) (_ : Equation4512 G) : Equation3300 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h318 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq14 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation318_4512_implies_Equation4278 (G : Type*) [Magma G]
    (h318 : Equation318 G) (_ : Equation4512 G) : Equation4278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h318 ..)
  have eq13 : (sK1 ◇ (sK2 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 : (sK1 ◇ (sK2 ◇ sK0)) ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation323_4512_implies_Equation307 (G : Type*) [Magma G]
    (h323 : Equation323 G) (_ : Equation4512 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq10 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h323 ..)
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  subsumption eq12 eq10

theorem Equation323_4512_implies_Equation3306 (G : Type*) [Magma G]
    (h323 : Equation323 G) (_ : Equation4512 G) : Equation3306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h323 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation325_4512_implies_Equation326 (G : Type*) [Magma G]
    (h325 : Equation325 G) (h4512 : Equation4512 G) : Equation326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h325 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq21 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq119 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose eq11 eq22 -- superposition 22,11
  have eq138 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq11 eq119 -- forward demodulation 119,11
  have eq200 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq138 eq13 -- superposition 13,138
  subsumption eq200 rfl

theorem Equation325_4512_implies_Equation3315 (G : Type*) [Magma G]
    (h325 : Equation325 G) (h4512 : Equation4512 G) : Equation3315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h325 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq19 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12
  have eq81 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq19 eq13 -- superposition 13,19
  subsumption eq81 eq11

theorem Equation325_4512_implies_Equation3316 (G : Type*) [Magma G]
    (h325 : Equation325 G) (_ : Equation4512 G) : Equation3316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h325 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation325_4512_implies_Equation4314 (G : Type*) [Magma G]
    (h325 : Equation325 G) (h4512 : Equation4512 G) : Equation4314 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h325 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ sK1) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq23 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq120 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose eq11 eq23 -- superposition 23,11
  have eq139 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq11 eq120 -- forward demodulation 120,11
  have eq201 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq139 eq14 -- superposition 14,139
  subsumption eq201 rfl

theorem Equation326_4512_implies_Equation307 (G : Type*) [Magma G]
    (h326 : Equation326 G) (_ : Equation4512 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq10 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h326 ..)
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  subsumption eq12 eq10

theorem Equation326_4512_implies_Equation3319 (G : Type*) [Magma G]
    (h326 : Equation326 G) (_ : Equation4512 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h326 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation327_4512_implies_Equation308 (G : Type*) [Magma G]
    (h327 : Equation327 G) (_ : Equation4512 G) : Equation308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h327 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation327_4512_implies_Equation325 (G : Type*) [Magma G]
    (h327 : Equation327 G) (_ : Equation4512 G) : Equation325 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h327 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation327_4512_implies_Equation3322 (G : Type*) [Magma G]
    (h327 : Equation327 G) (_ : Equation4512 G) : Equation3322 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h327 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation327_4512_implies_Equation3323 (G : Type*) [Magma G]
    (h327 : Equation327 G) (_ : Equation4512 G) : Equation3323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h327 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation327_4512_implies_Equation4315 (G : Type*) [Magma G]
    (h327 : Equation327 G) (_ : Equation4512 G) : Equation4315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h327 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq15 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK1) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq15 eq11

theorem Equation329_4512_implies_Equation309 (G : Type*) [Magma G]
    (h329 : Equation329 G) (_ : Equation4512 G) : Equation309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X1)) := mod_symm (h329 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation329_4512_implies_Equation3309 (G : Type*) [Magma G]
    (h329 : Equation329 G) (_ : Equation4512 G) : Equation3309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X1)) := mod_symm (h329 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq15 eq11

theorem Equation329_4512_implies_Equation3322 (G : Type*) [Magma G]
    (h329 : Equation329 G) (_ : Equation4512 G) : Equation3322 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X1)) := mod_symm (h329 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq15 eq11

theorem Equation329_4512_implies_Equation3326 (G : Type*) [Magma G]
    (h329 : Equation329 G) (_ : Equation4512 G) : Equation3326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X1)) := mod_symm (h329 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq15 eq11

theorem Equation329_4512_implies_Equation3334 (G : Type*) [Magma G]
    (h329 : Equation329 G) (_ : Equation4512 G) : Equation3334 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X1)) := mod_symm (h329 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq15 eq11

theorem Equation329_4512_implies_Equation4287 (G : Type*) [Magma G]
    (h329 : Equation329 G) (_ : Equation4512 G) : Equation4287 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X1)) := mod_symm (h329 ..)
  have eq13 : (sK0 ◇ (sK2 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq15 : (sK0 ◇ (sK2 ◇ sK1)) ≠ (sK0 ◇ sK1) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq15 eq11

theorem Equation332_4512_implies_Equation325 (G : Type*) [Magma G]
    (h332 : Equation332 G) (h4512 : Equation4512 G) : Equation325 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h332 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := superpose eq11 eq14 -- forward demodulation 14,11
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose eq11 eq15 -- forward demodulation 15,11
  have eq19 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq16 -- superposition 16,11
  have eq22 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := superpose eq11 eq19 -- forward demodulation 19,11
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq16 eq12 -- superposition 12,16
  have eq49 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq11 eq22 -- superposition 22,11
  have eq59 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq49 eq13 -- backward demodulation 13,49
  subsumption eq59 eq29

theorem Equation332_4512_implies_Equation333 (G : Type*) [Magma G]
    (h332 : Equation332 G) (h4512 : Equation4512 G) : Equation333 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h332 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := superpose eq11 eq14 -- forward demodulation 14,11
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose eq11 eq15 -- forward demodulation 15,11
  have eq19 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq16 -- superposition 16,11
  have eq22 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := superpose eq11 eq19 -- forward demodulation 19,11
  have eq26 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((X1 ◇ X0) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq16 eq12 -- superposition 12,16
  have eq35 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq12 eq26 -- forward demodulation 26,12
  have eq36 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq12 eq35 -- forward demodulation 35,12
  have eq40 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq29 eq36 -- backward demodulation 36,29
  have eq96 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq40 eq13 -- superposition 13,40
  subsumption eq96 eq22

theorem Equation332_4512_implies_Equation3309 (G : Type*) [Magma G]
    (h332 : Equation332 G) (h4512 : Equation4512 G) : Equation3309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h332 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq15 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := superpose eq11 eq15 -- forward demodulation 15,11
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose eq11 eq16 -- forward demodulation 16,11
  have eq20 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq17 -- superposition 17,11
  have eq23 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := superpose eq11 eq20 -- forward demodulation 20,11
  have eq30 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq17 eq12 -- superposition 12,17
  have eq50 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq11 eq23 -- superposition 23,11
  have eq60 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq50 eq14 -- backward demodulation 14,50
  subsumption eq60 eq30

theorem Equation332_4512_implies_Equation3342 (G : Type*) [Magma G]
    (h332 : Equation332 G) (_ : Equation4512 G) : Equation3342 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h332 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq14 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation332_4512_implies_Equation4293 (G : Type*) [Magma G]
    (h332 : Equation332 G) (h4512 : Equation4512 G) : Equation4293 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h332 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := superpose eq11 eq14 -- forward demodulation 14,11
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose eq11 eq15 -- forward demodulation 15,11
  have eq19 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq16 -- superposition 16,11
  have eq22 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := superpose eq11 eq19 -- forward demodulation 19,11
  have eq26 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((X1 ◇ X0) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq16 eq12 -- superposition 12,16
  have eq35 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq12 eq26 -- forward demodulation 26,12
  have eq36 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq12 eq35 -- forward demodulation 35,12
  have eq40 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq29 eq36 -- backward demodulation 36,29
  have eq41 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq29 eq13 -- backward demodulation 13,29
  have eq114 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq11 eq22 -- superposition 22,11
  have eq136 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq114 eq41 -- backward demodulation 41,114
  have eq148 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq40 eq136 -- superposition 136,40
  subsumption eq148 eq22

theorem Equation332_4512_implies_Equation4321 (G : Type*) [Magma G]
    (h332 : Equation332 G) (h4512 : Equation4512 G) : Equation4321 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h332 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := superpose eq11 eq14 -- forward demodulation 14,11
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose eq11 eq15 -- forward demodulation 15,11
  have eq19 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq16 -- superposition 16,11
  have eq22 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := superpose eq11 eq19 -- forward demodulation 19,11
  have eq26 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((X1 ◇ X0) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq16 eq12 -- superposition 12,16
  have eq35 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq12 eq26 -- forward demodulation 26,12
  have eq36 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq12 eq35 -- forward demodulation 35,12
  have eq40 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq29 eq36 -- backward demodulation 36,29
  have eq49 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq11 eq22 -- superposition 22,11
  have eq59 : (sK1 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq49 eq13 -- backward demodulation 13,49
  have eq60 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq29 eq59 -- forward demodulation 59,29
  have eq126 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq40 eq60 -- superposition 60,40
  subsumption eq126 eq22

theorem Equation332_4512_implies_Equation4343 (G : Type*) [Magma G]
    (h332 : Equation332 G) (_ : Equation4512 G) : Equation4343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h332 ..)
  have eq13 : (sK1 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq14 : (sK1 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq15 : (sK1 ◇ sK0) ≠ (sK0 ◇ sK1) := superpose eq11 eq14 -- forward demodulation 14,11
  have eq16 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := superpose eq11 eq16 -- forward demodulation 16,11
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose eq11 eq17 -- forward demodulation 17,11
  have eq21 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq18 -- superposition 18,11
  have eq24 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := superpose eq11 eq21 -- forward demodulation 21,11
  have eq51 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq11 eq24 -- superposition 24,11
  have eq165 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq51 eq15 -- superposition 15,51
  subsumption eq165 rfl

theorem Equation333_4512_implies_Equation323 (G : Type*) [Magma G]
    (h333 : Equation333 G) (h4512 : Equation4512 G) : Equation323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h333 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq14 -- superposition 14,12
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq28 -- forward demodulation 28,11
  have eq39 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq32 eq13 -- superposition 13,32
  subsumption eq39 rfl

theorem Equation333_4512_implies_Equation3316 (G : Type*) [Magma G]
    (h333 : Equation333 G) (h4512 : Equation4512 G) : Equation3316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h333 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq15 -- superposition 15,12
  have eq33 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq29 -- forward demodulation 29,11
  have eq40 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq33 eq14 -- superposition 14,33
  subsumption eq40 rfl

theorem Equation333_4512_implies_Equation3353 (G : Type*) [Magma G]
    (h333 : Equation333 G) (_ : Equation4512 G) : Equation3353 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h333 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq14 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation333_4512_implies_Equation4291 (G : Type*) [Magma G]
    (h333 : Equation333 G) (h4512 : Equation4512 G) : Equation4291 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h333 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK1 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq15 -- superposition 15,12
  have eq33 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq29 -- forward demodulation 29,11
  have eq40 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq33 eq14 -- superposition 14,33
  subsumption eq40 rfl

theorem Equation343_4512_implies_Equation312 (G : Type*) [Magma G]
    (h343 : Equation343 G) (_ : Equation4512 G) : Equation312 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := mod_symm (h343 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation343_4512_implies_Equation333 (G : Type*) [Magma G]
    (h343 : Equation343 G) (_ : Equation4512 G) : Equation333 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := mod_symm (h343 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation343_4512_implies_Equation3326 (G : Type*) [Magma G]
    (h343 : Equation343 G) (_ : Equation4512 G) : Equation3326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := mod_symm (h343 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq15 eq11

theorem Equation343_4512_implies_Equation3414 (G : Type*) [Magma G]
    (h343 : Equation343 G) (_ : Equation4512 G) : Equation3414 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := mod_symm (h343 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq15 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq15 eq11

theorem Equation343_4512_implies_Equation4300 (G : Type*) [Magma G]
    (h343 : Equation343 G) (_ : Equation4512 G) : Equation4300 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := mod_symm (h343 ..)
  have eq13 : (sK2 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq15 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq15 eq11

theorem Equation411_4512_implies_Equation1 (G : Type*) [Magma G]
    (_ : Equation411 G) (_ : Equation4512 G) : Equation1 G := by
  intro x
  rfl
theorem Equation419_4512_implies_Equation429 (G : Type*) [Magma G]
    (h419 : Equation419 G) (h4512 : Equation4512 G) : Equation429 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h419 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq21 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2)) = (X0 ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq28 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq29 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq12 eq28 -- forward demodulation 28,12
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq12 eq29 -- forward demodulation 29,12
  have eq34 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) = X2 := superpose eq12 eq24 -- forward demodulation 24,12
  have eq81 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq34 -- superposition 34,11
  have eq90 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) := superpose eq34 eq30 -- superposition 30,34
  have eq480 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq90 eq13 -- superposition 13,90
  subsumption eq480 eq81

theorem Equation419_4512_implies_Equation3334 (G : Type*) [Magma G]
    (h419 : Equation419 G) (h4512 : Equation4512 G) : Equation3334 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h419 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq21 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2)) = (X0 ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq28 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq29 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq12 eq28 -- forward demodulation 28,12
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq12 eq29 -- forward demodulation 29,12
  have eq34 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) = X2 := superpose eq12 eq24 -- forward demodulation 24,12
  have eq41 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq30 eq30 -- superposition 30,30
  have eq90 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) := superpose eq34 eq30 -- superposition 30,34
  have eq151 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = (X0 ◇ (X0 ◇ X2)) := superpose eq90 eq41 -- backward demodulation 41,90
  have eq163 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq151 eq30 -- backward demodulation 30,151
  have eq472 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq90 eq90 -- superposition 90,90
  have eq504 (X0 X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq163 eq472 -- forward demodulation 472,163
  have eq560 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq504 eq13 -- superposition 13,504
  subsumption eq560 rfl

theorem Equation429_4512_implies_Equation8 (G : Type*) [Magma G]
    (h429 : Equation429 G) (h4512 : Equation4512 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h429 ..)
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq12 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq20 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) = X2 := superpose eq11 eq10 -- superposition 10,11
  have eq31 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))))) = X2 := superpose eq11 eq20 -- forward demodulation 20,11
  have eq71 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq31 -- superposition 31,10
  have eq200 : sK0 ≠ sK0 := superpose eq71 eq12 -- superposition 12,71
  subsumption eq200 rfl

theorem Equation440_4512_implies_Equation411 (G : Type*) [Magma G]
    (h440 : Equation440 G) (_ : Equation4512 G) : Equation411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h440 ..)
  have eq12 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  subsumption eq12 eq10

theorem Equation477_4512_implies_Equation43 (G : Type*) [Magma G]
    (h477 : Equation477 G) (h4512 : Equation4512 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h477 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) = X2 := superpose eq11 eq12 -- superposition 12,11
  have eq19 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))) := superpose eq12 eq11 -- superposition 11,12
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2)))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2))))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq26 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))))) = X2 := superpose eq12 eq16 -- forward demodulation 16,12
  have eq27 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))))) = X2 := superpose eq12 eq26 -- forward demodulation 26,12
  have eq34 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq19 eq19 -- superposition 19,19
  have eq38 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq19 eq11 -- superposition 11,19
  have eq39 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X3)) := superpose eq19 eq12 -- superposition 12,19
  have eq43 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq12 eq34 -- forward demodulation 34,12
  have eq44 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq11 eq43 -- forward demodulation 43,11
  have eq48 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq12 eq38 -- forward demodulation 38,12
  have eq49 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq48 -- forward demodulation 48,11
  have eq50 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X3))) := superpose eq12 eq39 -- forward demodulation 39,12
  have eq51 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X3)))) := superpose eq12 eq50 -- forward demodulation 50,12
  have eq52 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X3))))) := superpose eq12 eq51 -- forward demodulation 51,12
  have eq53 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X3)))))) := superpose eq12 eq52 -- forward demodulation 52,12
  have eq54 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X3)))))) := superpose eq12 eq53 -- forward demodulation 53,12
  have eq80 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := superpose eq11 eq23 -- superposition 23,11
  have eq81 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq23 eq23 -- superposition 23,23
  have eq121 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq12 eq80 -- superposition 80,12
  have eq126 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) := superpose eq80 eq23 -- superposition 23,80
  have eq144 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq12 eq121 -- forward demodulation 121,12
  have eq187 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))))))) = X1 := superpose eq49 eq27 -- superposition 27,49
  have eq194 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose eq11 eq27 -- superposition 27,11
  have eq288 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))))))) = X1 := superpose eq12 eq187 -- forward demodulation 187,12
  have eq289 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))))))) = X1 := superpose eq81 eq288 -- forward demodulation 288,81
  have eq290 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))))))))) = X1 := superpose eq12 eq289 -- forward demodulation 289,12
  have eq291 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))))))))) = X1 := superpose eq12 eq290 -- forward demodulation 290,12
  have eq292 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))))) = X1 := superpose eq54 eq291 -- forward demodulation 291,54
  have eq293 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))))))) = X1 := superpose eq12 eq292 -- forward demodulation 292,12
  have eq294 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))))))) = X1 := superpose eq12 eq293 -- forward demodulation 293,12
  have eq295 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) = X1 := superpose eq23 eq294 -- forward demodulation 294,23
  have eq296 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) = X1 := superpose eq12 eq295 -- forward demodulation 295,12
  have eq297 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X1 := superpose eq12 eq296 -- forward demodulation 296,12
  have eq298 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := superpose eq11 eq297 -- forward demodulation 297,11
  have eq319 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X1)) := superpose eq194 eq126 -- backward demodulation 126,194
  have eq614 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X1 := superpose eq12 eq298 -- superposition 298,12
  have eq720 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose eq319 eq614 -- forward demodulation 614,319
  have eq721 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := superpose eq12 eq720 -- forward demodulation 720,12
  have eq799 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq12 eq44 -- superposition 44,12
  have eq871 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq144 eq799 -- forward demodulation 799,144
  have eq872 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq319 eq871 -- forward demodulation 871,319
  have eq873 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq12 eq872 -- forward demodulation 872,12
  have eq874 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq721 eq873 -- forward demodulation 873,721
  have eq967 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq874 eq13 -- superposition 13,874
  subsumption eq967 rfl

theorem Equation477_4512_implies_Equation504 (G : Type*) [Magma G]
    (h477 : Equation477 G) (h4512 : Equation4512 G) : Equation504 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h477 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2)))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2))))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq76 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq11 eq23 -- superposition 23,11
  have eq95 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := superpose eq76 eq13 -- backward demodulation 13,76
  subsumption eq95 eq11

theorem Equation504_4512_implies_Equation440 (G : Type*) [Magma G]
    (h504 : Equation504 G) (h4512 : Equation4512 G) : Equation440 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h504 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := superpose eq12 eq11 -- superposition 11,12
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2)))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2))))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq34 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq11 eq18 -- superposition 18,11
  have eq42 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq12 eq34 -- forward demodulation 34,12
  have eq228 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose eq42 eq23 -- superposition 23,42
  have eq249 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := superpose eq11 eq228 -- forward demodulation 228,11
  have eq561 : sK0 ≠ sK0 := superpose eq249 eq13 -- superposition 13,249
  subsumption eq561 rfl

theorem Equation504_4512_implies_Equation513 (G : Type*) [Magma G]
    (h504 : Equation504 G) (h4512 : Equation4512 G) : Equation513 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h504 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2)))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2))))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq63 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq11 eq23 -- superposition 23,11
  have eq76 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := superpose eq63 eq13 -- backward demodulation 13,63
  subsumption eq76 eq11

theorem Equation504_4512_implies_Equation4290 (G : Type*) [Magma G]
    (h504 : Equation504 G) (h4512 : Equation4512 G) : Equation4290 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h504 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := superpose eq12 eq11 -- superposition 11,12
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2)))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2))))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq34 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq11 eq18 -- superposition 18,11
  have eq42 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq12 eq34 -- forward demodulation 34,12
  have eq228 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose eq42 eq23 -- superposition 23,42
  have eq249 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := superpose eq11 eq228 -- forward demodulation 228,11
  have eq546 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := superpose eq249 eq23 -- superposition 23,249
  have eq5292 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq546 eq13 -- superposition 13,546
  subsumption eq5292 rfl

theorem Equation513_4512_implies_Equation411 (G : Type*) [Magma G]
    (h513 : Equation513 G) (_ : Equation4512 G) : Equation411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq10 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h513 ..)
  have eq12 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  subsumption eq12 eq10

theorem Equation3253_4512_implies_Equation1 (G : Type*) [Magma G]
    (_ : Equation3253 G) (_ : Equation4512 G) : Equation1 G := by
  intro x
  rfl
theorem Equation3255_4512_implies_Equation307 (G : Type*) [Magma G]
    (h3255 : Equation3255 G) (h4512 : Equation4512 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h3255 ..)
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq11 eq10 -- superposition 10,11
  have eq41 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq10 eq22 -- superposition 22,10
  have eq87 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq41 eq12 -- superposition 12,41
  subsumption eq87 rfl

theorem Equation3256_4512_implies_Equation3253 (G : Type*) [Magma G]
    (h3256 : Equation3256 G) (_ : Equation4512 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h3256 ..)
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  subsumption eq12 eq10

theorem Equation3258_4512_implies_Equation307 (G : Type*) [Magma G]
    (h3258 : Equation3258 G) (h4512 : Equation4512 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3258 ..)
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq11 eq10 -- superposition 10,11
  have eq30 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq10 eq17 -- superposition 17,10
  have eq50 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq30 eq12 -- superposition 12,30
  subsumption eq50 rfl

theorem Equation3259_4512_implies_Equation3256 (G : Type*) [Magma G]
    (h3259 : Equation3259 G) (h4512 : Equation4512 G) : Equation3256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3259 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq24 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq25 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq82 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := superpose eq11 eq25 -- superposition 25,11
  have eq102 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq82 eq13 -- backward demodulation 13,82
  subsumption eq102 eq11

theorem Equation3259_4512_implies_Equation3261 (G : Type*) [Magma G]
    (h3259 : Equation3259 G) (h4512 : Equation4512 G) : Equation3261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3259 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq17 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq24 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq25 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq26 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq25 eq16 -- backward demodulation 16,25
  have eq44 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq26 eq13 -- superposition 13,26
  subsumption eq44 rfl

theorem Equation3259_4512_implies_Equation4270 (G : Type*) [Magma G]
    (h3259 : Equation3259 G) (h4512 : Equation4512 G) : Equation4270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3259 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq24 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq25 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq82 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := superpose eq11 eq25 -- superposition 25,11
  have eq135 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq82 eq13 -- superposition 13,82
  subsumption eq135 rfl

theorem Equation3260_4512_implies_Equation310 (G : Type*) [Magma G]
    (h3260 : Equation3260 G) (_ : Equation4512 G) : Equation310 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h3260 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq15 eq13 -- superposition 13,15
  subsumption eq20 rfl

theorem Equation3261_4512_implies_Equation3253 (G : Type*) [Magma G]
    (h3261 : Equation3261 G) (_ : Equation4512 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h3261 ..)
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  subsumption eq12 eq10

theorem Equation3264_4512_implies_Equation3255 (G : Type*) [Magma G]
    (h3264 : Equation3264 G) (_ : Equation4512 G) : Equation3255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h3264 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3264_4512_implies_Equation3258 (G : Type*) [Magma G]
    (h3264 : Equation3264 G) (_ : Equation4512 G) : Equation3258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h3264 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3264_4512_implies_Equation3261 (G : Type*) [Magma G]
    (h3264 : Equation3264 G) (_ : Equation4512 G) : Equation3261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h3264 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3264_4512_implies_Equation4284 (G : Type*) [Magma G]
    (h3264 : Equation3264 G) (h4512 : Equation4512 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h3264 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq22 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq23 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq229 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq11 eq24 -- superposition 24,11
  have eq328 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq229 eq13 -- superposition 13,229
  subsumption eq328 rfl

theorem Equation3265_4512_implies_Equation310 (G : Type*) [Magma G]
    (h3265 : Equation3265 G) (h4512 : Equation4512 G) : Equation310 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ X1))) := mod_symm (h3265 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq21 (X0 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ X0)) := superpose eq11 eq20 -- forward demodulation 20,11
  have eq28 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq21 eq13 -- superposition 13,21
  subsumption eq28 rfl

theorem Equation3267_4512_implies_Equation3260 (G : Type*) [Magma G]
    (h3267 : Equation3267 G) (_ : Equation4512 G) : Equation3260 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h3267 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3267_4512_implies_Equation3264 (G : Type*) [Magma G]
    (h3267 : Equation3267 G) (_ : Equation4512 G) : Equation3264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h3267 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3267_4512_implies_Equation3265 (G : Type*) [Magma G]
    (h3267 : Equation3267 G) (_ : Equation4512 G) : Equation3265 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h3267 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3271_4512_implies_Equation3261 (G : Type*) [Magma G]
    (h3271 : Equation3271 G) (h4512 : Equation4512 G) : Equation3261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h3271 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = ((X1 ◇ X1) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X1 ◇ (X1 ◇ X2)) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq129 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq25 -- superposition 25,11
  have eq145 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq129 eq13 -- backward demodulation 13,129
  subsumption eq145 eq11

theorem Equation3271_4512_implies_Equation3278 (G : Type*) [Magma G]
    (h3271 : Equation3271 G) (h4512 : Equation4512 G) : Equation3278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h3271 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = ((X1 ◇ X1) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X1 ◇ (X1 ◇ X2)) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq129 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq25 -- superposition 25,11
  have eq182 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq129 eq129 -- superposition 129,129
  have eq186 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq129 eq11 -- superposition 11,129
  have eq286 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X2 ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq129 eq182 -- superposition 182,129
  have eq339 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq182 eq13 -- superposition 13,182
  have eq361 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq186 eq286 -- forward demodulation 286,186
  subsumption eq339 eq361

theorem Equation3271_4512_implies_Equation4275 (G : Type*) [Magma G]
    (h3271 : Equation3271 G) (h4512 : Equation4512 G) : Equation4275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h3271 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = ((X1 ◇ X1) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X1 ◇ (X1 ◇ X2)) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq129 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq25 -- superposition 25,11
  have eq196 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq129 eq13 -- superposition 13,129
  subsumption eq196 rfl

theorem Equation3273_4512_implies_Equation316 (G : Type*) [Magma G]
    (h3273 : Equation3273 G) (_ : Equation4512 G) : Equation316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := mod_symm (h3273 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq25 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq17 eq17 -- superposition 17,17
  have eq29 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq17 eq13 -- superposition 13,17
  subsumption eq29 eq25

theorem Equation3273_4512_implies_Equation3260 (G : Type*) [Magma G]
    (h3273 : Equation3273 G) (_ : Equation4512 G) : Equation3260 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := mod_symm (h3273 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq19 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq11 eq13 -- superposition 13,11
  have eq47 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq17 eq17 -- superposition 17,17
  have eq125 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq47 eq19 -- superposition 19,47
  subsumption eq125 eq47

theorem Equation3273_4512_implies_Equation3292 (G : Type*) [Magma G]
    (h3273 : Equation3273 G) (_ : Equation4512 G) : Equation3292 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := mod_symm (h3273 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq19 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq11 eq13 -- superposition 13,11
  have eq47 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq17 eq17 -- superposition 17,17
  have eq125 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq47 eq19 -- superposition 19,47
  subsumption eq125 eq47

theorem Equation3274_4512_implies_Equation315 (G : Type*) [Magma G]
    (h3274 : Equation3274 G) (h4512 : Equation4512 G) : Equation315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h3274 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq20 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) = ((X1 ◇ X1) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq22 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) := superpose eq11 eq12 -- superposition 12,11
  have eq26 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) = (X1 ◇ (X1 ◇ X3)) := superpose eq12 eq20 -- forward demodulation 20,12
  have eq27 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))) := superpose eq12 eq26 -- forward demodulation 26,12
  have eq28 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := superpose eq12 eq27 -- forward demodulation 27,12
  have eq31 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X2 ◇ X2)) := superpose eq11 eq22 -- forward demodulation 22,11
  have eq38 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq31 -- superposition 31,12
  have eq44 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ X1)) := superpose eq28 eq38 -- forward demodulation 38,28
  have eq127 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq44 -- superposition 44,11
  have eq271 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq127 eq13 -- superposition 13,127
  subsumption eq271 rfl

theorem Equation3275_4512_implies_Equation316 (G : Type*) [Magma G]
    (h3275 : Equation3275 G) (h4512 : Equation4512 G) : Equation316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h3275 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq48 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq12 eq17 -- superposition 17,12
  have eq77 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) := superpose eq17 eq48 -- superposition 48,17
  have eq118 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2)))) := superpose eq12 eq77 -- forward demodulation 77,12
  have eq119 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq48 eq118 -- forward demodulation 118,48
  have eq122 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (X2 ◇ X2)) := superpose eq119 eq48 -- backward demodulation 48,119
  have eq265 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq122 eq122 -- superposition 122,122
  have eq285 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq122 eq13 -- superposition 13,122
  subsumption eq285 eq265

theorem Equation3275_4512_implies_Equation3264 (G : Type*) [Magma G]
    (h3275 : Equation3275 G) (h4512 : Equation4512 G) : Equation3264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h3275 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq19 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq11 eq13 -- superposition 13,11
  have eq27 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq59 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := superpose eq17 eq11 -- superposition 11,17
  have eq93 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq27 -- superposition 27,11
  have eq150 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq11 eq93 -- superposition 93,11
  have eq178 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ (X1 ◇ X1)) := superpose eq150 eq59 -- backward demodulation 59,150
  have eq179 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq178 eq16 -- backward demodulation 16,178
  have eq262 (X3 X4 : G) : (X3 ◇ X3) = (X4 ◇ X4) := superpose eq179 eq179 -- superposition 179,179
  have eq382 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq262 eq19 -- superposition 19,262
  subsumption eq382 eq262

theorem Equation3277_4512_implies_Equation3267 (G : Type*) [Magma G]
    (h3277 : Equation3277 G) (_ : Equation4512 G) : Equation3267 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := mod_symm (h3277 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq18 (X0 X1 X4 : G) : (X0 ◇ X0) = (X4 ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq21 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq11 eq13 -- superposition 13,11
  have eq51 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq18 eq18 -- superposition 18,18
  have eq164 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq51 eq21 -- superposition 21,51
  subsumption eq164 eq51

theorem Equation3277_4512_implies_Equation3273 (G : Type*) [Magma G]
    (h3277 : Equation3277 G) (_ : Equation4512 G) : Equation3273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := mod_symm (h3277 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3277_4512_implies_Equation3275 (G : Type*) [Magma G]
    (h3277 : Equation3277 G) (_ : Equation4512 G) : Equation3275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := mod_symm (h3277 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3277_4512_implies_Equation3290 (G : Type*) [Magma G]
    (h3277 : Equation3277 G) (_ : Equation4512 G) : Equation3290 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := mod_symm (h3277 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq18 (X0 X1 X4 : G) : (X0 ◇ X0) = (X4 ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq21 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq11 eq13 -- superposition 13,11
  have eq51 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq18 eq18 -- superposition 18,18
  have eq164 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq51 eq21 -- superposition 21,51
  subsumption eq164 eq51

theorem Equation3277_4512_implies_Equation3300 (G : Type*) [Magma G]
    (h3277 : Equation3277 G) (_ : Equation4512 G) : Equation3300 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := mod_symm (h3277 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq18 (X0 X1 X4 : G) : (X0 ◇ X0) = (X4 ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq21 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq11 eq13 -- superposition 13,11
  have eq51 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq18 eq18 -- superposition 18,18
  have eq164 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq51 eq21 -- superposition 21,51
  subsumption eq164 eq51

theorem Equation3278_4512_implies_Equation3253 (G : Type*) [Magma G]
    (h3278 : Equation3278 G) (_ : Equation4512 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3278 ..)
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  subsumption eq12 eq10

theorem Equation3290_4512_implies_Equation316 (G : Type*) [Magma G]
    (h3290 : Equation3290 G) (_ : Equation4512 G) : Equation316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ X2))) := mod_symm (h3290 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq34 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq18 eq18 -- superposition 18,18
  have eq40 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq18 eq13 -- superposition 13,18
  subsumption eq40 eq34

theorem Equation3290_4512_implies_Equation3265 (G : Type*) [Magma G]
    (h3290 : Equation3290 G) (_ : Equation4512 G) : Equation3265 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ X2))) := mod_symm (h3290 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq11 eq13 -- superposition 13,11
  have eq55 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq18 eq18 -- superposition 18,18
  have eq154 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq55 eq20 -- superposition 20,55
  subsumption eq154 eq55

theorem Equation3290_4512_implies_Equation3274 (G : Type*) [Magma G]
    (h3290 : Equation3290 G) (_ : Equation4512 G) : Equation3274 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ X2))) := mod_symm (h3290 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq11 eq13 -- superposition 13,11
  have eq55 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq18 eq18 -- superposition 18,18
  have eq154 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq55 eq20 -- superposition 20,55
  subsumption eq154 eq55

theorem Equation3292_4512_implies_Equation315 (G : Type*) [Magma G]
    (h3292 : Equation3292 G) (h4512 : Equation4512 G) : Equation315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X1 ◇ X0))) := mod_symm (h3292 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X2)) = (X1 ◇ (X2 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X3)) = ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq60 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X3)) = (((X2 ◇ X1) ◇ (X2 ◇ X1)) ◇ X3) := superpose eq17 eq12 -- superposition 12,17
  have eq106 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X3)) = ((X2 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3) := superpose eq12 eq60 -- forward demodulation 60,12
  have eq107 (X0 X1 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X3)) = (X1 ◇ (X1 ◇ X3)) := superpose eq19 eq106 -- forward demodulation 106,19
  have eq108 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := superpose eq12 eq107 -- forward demodulation 107,12
  have eq357 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq108 -- superposition 108,11
  have eq687 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq357 eq13 -- superposition 13,357
  subsumption eq687 rfl

theorem Equation3300_4512_implies_Equation3264 (G : Type*) [Magma G]
    (h3300 : Equation3300 G) (_ : Equation4512 G) : Equation3264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ X0))) := mod_symm (h3300 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3300_4512_implies_Equation3274 (G : Type*) [Magma G]
    (h3300 : Equation3300 G) (_ : Equation4512 G) : Equation3274 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ X0))) := mod_symm (h3300 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3300_4512_implies_Equation3292 (G : Type*) [Magma G]
    (h3300 : Equation3300 G) (_ : Equation4512 G) : Equation3292 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ X0))) := mod_symm (h3300 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3306_4512_implies_Equation3253 (G : Type*) [Magma G]
    (h3306 : Equation3306 G) (_ : Equation4512 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq10 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := mod_symm (h3306 ..)
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  subsumption eq12 eq10

theorem Equation3308_4512_implies_Equation3306 (G : Type*) [Magma G]
    (h3308 : Equation3308 G) (h4512 : Equation4512 G) : Equation3306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h3308 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq12 eq19 -- forward demodulation 19,12
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq12 eq25 -- forward demodulation 25,12
  have eq27 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq12 eq26 -- forward demodulation 26,12
  have eq83 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq11 eq27 -- superposition 27,11
  have eq265 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq83 eq13 -- superposition 13,83
  subsumption eq265 rfl

theorem Equation3308_4512_implies_Equation3315 (G : Type*) [Magma G]
    (h3308 : Equation3308 G) (h4512 : Equation4512 G) : Equation3315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h3308 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq16 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq17 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq18 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq22 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq23 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq12 eq11 -- superposition 11,12
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq12 eq19 -- forward demodulation 19,12
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq12 eq25 -- forward demodulation 25,12
  have eq27 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq12 eq26 -- forward demodulation 26,12
  have eq32 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq81 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) = (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq27 eq27 -- superposition 27,27
  have eq83 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq11 eq27 -- superposition 27,11
  have eq92 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) := superpose eq27 eq12 -- superposition 12,27
  have eq99 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) = (X0 ◇ (X3 ◇ (X1 ◇ X2))) := superpose eq27 eq81 -- forward demodulation 81,27
  have eq121 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3))) := superpose eq12 eq92 -- forward demodulation 92,12
  have eq122 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3)))) := superpose eq12 eq121 -- forward demodulation 121,12
  have eq123 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) := superpose eq12 eq122 -- forward demodulation 122,12
  have eq124 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq27 eq123 -- forward demodulation 123,27
  have eq259 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq83 -- superposition 83,11
  have eq261 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq27 eq83 -- superposition 83,27
  have eq264 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq12 eq83 -- superposition 83,12
  have eq267 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq83 eq32 -- superposition 32,83
  have eq280 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))) := superpose eq12 eq264 -- forward demodulation 264,12
  have eq281 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) := superpose eq12 eq280 -- forward demodulation 280,12
  have eq282 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq99 eq281 -- forward demodulation 281,99
  have eq283 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq282 eq18 -- backward demodulation 18,282
  have eq284 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq261 eq267 -- forward demodulation 267,261
  have eq285 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq12 eq284 -- forward demodulation 284,12
  have eq286 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq83 eq285 -- forward demodulation 285,83
  have eq287 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq259 eq286 -- forward demodulation 286,259
  have eq288 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq83 eq287 -- forward demodulation 287,83
  have eq319 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))))) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) := superpose eq83 eq283 -- superposition 283,83
  have eq384 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))))) := superpose eq124 eq319 -- forward demodulation 319,124
  have eq385 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))))) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)))))) := superpose eq12 eq384 -- forward demodulation 384,12
  have eq386 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))))) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)))))) := superpose eq261 eq385 -- forward demodulation 385,261
  have eq387 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))))))) := superpose eq12 eq386 -- forward demodulation 386,12
  have eq388 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))))) := superpose eq83 eq387 -- forward demodulation 387,83
  have eq389 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))))) := superpose eq12 eq388 -- forward demodulation 388,12
  have eq390 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))))) := superpose eq261 eq389 -- forward demodulation 389,261
  have eq391 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq11 eq390 -- forward demodulation 390,11
  have eq392 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq22 eq391 -- forward demodulation 391,22
  have eq393 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) := superpose eq282 eq392 -- forward demodulation 392,282
  have eq394 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq12 eq393 -- forward demodulation 393,12
  have eq395 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq12 eq394 -- forward demodulation 394,12
  have eq396 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq83 eq395 -- forward demodulation 395,83
  have eq397 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq288 eq396 -- forward demodulation 396,288
  have eq1407 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq397 eq13 -- superposition 13,397
  subsumption eq1407 rfl

theorem Equation3308_4512_implies_Equation4283 (G : Type*) [Magma G]
    (h3308 : Equation3308 G) (h4512 : Equation4512 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h3308 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq12 eq19 -- forward demodulation 19,12
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq12 eq25 -- forward demodulation 25,12
  have eq27 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq12 eq26 -- forward demodulation 26,12
  have eq83 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq11 eq27 -- superposition 27,11
  have eq259 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq83 -- superposition 83,11
  have eq556 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq259 eq13 -- superposition 13,259
  subsumption eq556 rfl

theorem Equation3309_4512_implies_Equation323 (G : Type*) [Magma G]
    (h3309 : Equation3309 G) (h4512 : Equation4512 G) : Equation323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h3309 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq14 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq17 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq16 -- forward demodulation 16,11
  have eq37 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq12 eq17 -- superposition 17,12
  have eq45 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq37 -- forward demodulation 37,11
  have eq46 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq45 eq17 -- backward demodulation 17,45
  have eq73 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq46 eq11 -- superposition 11,46
  have eq77 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq11 eq73 -- forward demodulation 73,11
  have eq80 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq77 eq11 -- backward demodulation 11,77
  have eq89 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq80 eq13 -- superposition 13,80
  subsumption eq89 rfl

theorem Equation3309_4512_implies_Equation326 (G : Type*) [Magma G]
    (h3309 : Equation3309 G) (h4512 : Equation4512 G) : Equation326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h3309 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq14 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq17 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq16 -- forward demodulation 16,11
  have eq37 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq12 eq17 -- superposition 17,12
  have eq45 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq37 -- forward demodulation 37,11
  have eq46 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq45 eq17 -- backward demodulation 17,45
  have eq73 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq46 eq11 -- superposition 11,46
  have eq77 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq11 eq73 -- forward demodulation 73,11
  have eq142 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq77 eq13 -- superposition 13,77
  subsumption eq142 rfl

theorem Equation3309_4512_implies_Equation3316 (G : Type*) [Magma G]
    (h3309 : Equation3309 G) (h4512 : Equation4512 G) : Equation3316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h3309 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq14 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq17 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq16 -- forward demodulation 16,11
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2)))) := superpose eq11 eq12 -- superposition 12,11
  have eq29 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := superpose eq12 eq20 -- forward demodulation 20,12
  have eq30 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := superpose eq12 eq29 -- forward demodulation 29,12
  have eq37 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq12 eq17 -- superposition 17,12
  have eq45 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq37 -- forward demodulation 37,11
  have eq46 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq45 eq17 -- backward demodulation 17,45
  have eq73 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq46 eq11 -- superposition 11,46
  have eq77 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq11 eq73 -- forward demodulation 73,11
  have eq79 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq77 eq30 -- backward demodulation 30,77
  have eq162 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq77 eq79 -- superposition 79,77
  have eq418 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq162 eq13 -- superposition 13,162
  subsumption eq418 rfl

theorem Equation3309_4512_implies_Equation4284 (G : Type*) [Magma G]
    (h3309 : Equation3309 G) (h4512 : Equation4512 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h3309 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq14 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq17 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq16 -- forward demodulation 16,11
  have eq37 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq12 eq17 -- superposition 17,12
  have eq45 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq37 -- forward demodulation 37,11
  have eq46 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq45 eq17 -- backward demodulation 17,45
  have eq73 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq46 eq11 -- superposition 11,46
  have eq77 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq11 eq73 -- forward demodulation 73,11
  have eq80 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq77 eq11 -- backward demodulation 11,77
  have eq81 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq77 eq13 -- backward demodulation 13,77
  subsumption eq81 eq80

theorem Equation3315_4512_implies_Equation3319 (G : Type*) [Magma G]
    (h3315 : Equation3315 G) (h4512 : Equation4512 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3315 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq20 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq23 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq24 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq81 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq20 eq24 -- superposition 24,20
  have eq99 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq81 -- forward demodulation 81,11
  have eq135 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq99 eq13 -- superposition 13,99
  subsumption eq135 rfl

theorem Equation3316_4512_implies_Equation307 (G : Type*) [Magma G]
    (h3316 : Equation3316 G) (h4512 : Equation4512 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq10 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3316 ..)
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq11 eq10 -- superposition 10,11
  have eq58 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq10 eq20 -- superposition 20,10
  have eq62 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq10 eq20 -- superposition 20,10
  have eq93 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq11 eq58 -- forward demodulation 58,11
  have eq94 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq10 eq93 -- forward demodulation 93,10
  have eq101 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq94 eq62 -- forward demodulation 62,94
  have eq200 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq101 eq12 -- superposition 12,101
  subsumption eq200 rfl

theorem Equation3319_4512_implies_Equation3253 (G : Type*) [Magma G]
    (h3319 : Equation3319 G) (_ : Equation4512 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq10 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := mod_symm (h3319 ..)
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  subsumption eq12 eq10

theorem Equation3322_4512_implies_Equation326 (G : Type*) [Magma G]
    (h3322 : Equation3322 G) (h4512 : Equation4512 G) : Equation326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X1))) := mod_symm (h3322 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq37 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq18 -- superposition 18,11
  have eq69 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq37 eq13 -- superposition 13,37
  subsumption eq69 rfl

theorem Equation3322_4512_implies_Equation3255 (G : Type*) [Magma G]
    (h3322 : Equation3322 G) (_ : Equation4512 G) : Equation3255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X1))) := mod_symm (h3322 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3322_4512_implies_Equation3316 (G : Type*) [Magma G]
    (h3322 : Equation3322 G) (_ : Equation4512 G) : Equation3316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X1))) := mod_symm (h3322 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3323_4512_implies_Equation3256 (G : Type*) [Magma G]
    (h3323 : Equation3323 G) (_ : Equation4512 G) : Equation3256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := mod_symm (h3323 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3323_4512_implies_Equation3315 (G : Type*) [Magma G]
    (h3323 : Equation3323 G) (_ : Equation4512 G) : Equation3315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := mod_symm (h3323 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3326_4512_implies_Equation323 (G : Type*) [Magma G]
    (h3326 : Equation3326 G) (h4512 : Equation4512 G) : Equation323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := mod_symm (h3326 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq11 -- superposition 11,12
  have eq34 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ X2)) := superpose eq11 eq19 -- superposition 19,11
  have eq68 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq34 eq13 -- superposition 13,34
  subsumption eq68 rfl

theorem Equation3326_4512_implies_Equation3258 (G : Type*) [Magma G]
    (h3326 : Equation3326 G) (_ : Equation4512 G) : Equation3258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := mod_symm (h3326 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3326_4512_implies_Equation3316 (G : Type*) [Magma G]
    (h3326 : Equation3326 G) (_ : Equation4512 G) : Equation3316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := mod_symm (h3326 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3331_4512_implies_Equation3259 (G : Type*) [Magma G]
    (h3331 : Equation3331 G) (_ : Equation4512 G) : Equation3259 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := mod_symm (h3331 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3331_4512_implies_Equation3308 (G : Type*) [Magma G]
    (h3331 : Equation3331 G) (_ : Equation4512 G) : Equation3308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := mod_symm (h3331 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3331_4512_implies_Equation3323 (G : Type*) [Magma G]
    (h3331 : Equation3331 G) (h4512 : Equation4512 G) : Equation3323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := mod_symm (h3331 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X2)))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq22 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq31 (X0 X1 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq22 eq17 -- backward demodulation 17,22
  have eq40 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq31 eq11 -- superposition 11,31
  have eq51 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq12 eq40 -- forward demodulation 40,12
  have eq202 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq51 eq13 -- superposition 13,51
  subsumption eq202 rfl

theorem Equation3331_4512_implies_Equation3334 (G : Type*) [Magma G]
    (h3331 : Equation3331 G) (h4512 : Equation4512 G) : Equation3334 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := mod_symm (h3331 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X2)))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq22 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq31 (X0 X1 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq22 eq17 -- backward demodulation 17,22
  have eq44 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq31 eq13 -- superposition 13,31
  subsumption eq44 rfl

theorem Equation3331_4512_implies_Equation4358 (G : Type*) [Magma G]
    (h3331 : Equation3331 G) (h4512 : Equation4512 G) : Equation4358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := mod_symm (h3331 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X2)))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq22 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq31 (X0 X1 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq22 eq17 -- backward demodulation 17,22
  have eq37 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq31 -- superposition 31,11
  have eq84 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq37 eq13 -- superposition 13,37
  subsumption eq84 rfl

theorem Equation3334_4512_implies_Equation3261 (G : Type*) [Magma G]
    (h3334 : Equation3334 G) (_ : Equation4512 G) : Equation3261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X2 ◇ X1))) := mod_symm (h3334 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3334_4512_implies_Equation3306 (G : Type*) [Magma G]
    (h3334 : Equation3334 G) (_ : Equation4512 G) : Equation3306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X2 ◇ X1))) := mod_symm (h3334 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3334_4512_implies_Equation3319 (G : Type*) [Magma G]
    (h3334 : Equation3334 G) (_ : Equation4512 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X2 ◇ X1))) := mod_symm (h3334 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3342_4512_implies_Equation43 (G : Type*) [Magma G]
    (h3342 : Equation3342 G) (h4512 : Equation4512 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h3342 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq14 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq16 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq17 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq11 eq16 -- forward demodulation 16,11
  have eq18 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq11 eq17 -- forward demodulation 17,11
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq11 eq18 -- forward demodulation 18,11
  have eq47 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq11 eq19 -- superposition 19,11
  have eq70 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ X0) := superpose eq11 eq47 -- forward demodulation 47,11
  have eq361 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq11 eq70 -- superposition 70,11
  have eq451 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq361 eq13 -- superposition 13,361
  subsumption eq451 rfl

theorem Equation3342_4512_implies_Equation3308 (G : Type*) [Magma G]
    (h3342 : Equation3342 G) (h4512 : Equation4512 G) : Equation3308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h3342 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq16 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq17 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq11 eq16 -- forward demodulation 16,11
  have eq18 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq11 eq17 -- forward demodulation 17,11
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq11 eq18 -- forward demodulation 18,11
  have eq22 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq11 eq12 -- superposition 12,11
  have eq23 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq12 eq11 -- superposition 11,12
  have eq31 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X1)) := superpose eq11 eq22 -- forward demodulation 22,11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq31 eq23 -- forward demodulation 23,31
  have eq33 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := superpose eq31 eq32 -- forward demodulation 32,31
  have eq34 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))))) := superpose eq31 eq33 -- forward demodulation 33,31
  have eq35 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) := superpose eq12 eq34 -- forward demodulation 34,12
  have eq36 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) := superpose eq12 eq35 -- forward demodulation 35,12
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq12 eq19 -- superposition 19,12
  have eq68 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq46 -- forward demodulation 46,12
  have eq174 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq19 eq36 -- superposition 36,19
  have eq276 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))))) := superpose eq11 eq174 -- forward demodulation 174,11
  have eq297 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq68 -- superposition 68,11
  have eq304 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq36 eq68 -- superposition 68,36
  have eq326 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq297 eq304 -- forward demodulation 304,297
  have eq327 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq326 eq276 -- backward demodulation 276,326
  have eq330 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := superpose eq327 eq13 -- backward demodulation 13,327
  subsumption eq330 eq68

theorem Equation3342_4512_implies_Equation3346 (G : Type*) [Magma G]
    (h3342 : Equation3342 G) (h4512 : Equation4512 G) : Equation3346 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h3342 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq14 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq16 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq17 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq11 eq16 -- forward demodulation 16,11
  have eq18 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq11 eq17 -- forward demodulation 17,11
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq11 eq18 -- forward demodulation 18,11
  have eq22 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq11 eq12 -- superposition 12,11
  have eq31 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X1)) := superpose eq11 eq22 -- forward demodulation 22,11
  have eq47 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq11 eq19 -- superposition 19,11
  have eq70 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ X0) := superpose eq11 eq47 -- forward demodulation 47,11
  have eq103 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := superpose eq31 eq13 -- superposition 13,31
  subsumption eq103 eq70

theorem Equation3346_4512_implies_Equation3319 (G : Type*) [Magma G]
    (h3346 : Equation3346 G) (h4512 : Equation4512 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h3346 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq16 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X1 ◇ X0) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq22 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq43 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq24 -- superposition 24,11
  have eq54 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq43 -- forward demodulation 43,11
  have eq129 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq54 eq13 -- superposition 13,54
  subsumption eq129 rfl

theorem Equation3346_4512_implies_Equation3353 (G : Type*) [Magma G]
    (h3346 : Equation3346 G) (h4512 : Equation4512 G) : Equation3353 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h3346 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq16 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X1 ◇ X0) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq22 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq43 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq24 -- superposition 24,11
  have eq54 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq43 -- forward demodulation 43,11
  have eq118 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq54 eq24 -- superposition 24,54
  have eq142 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := superpose eq118 eq13 -- backward demodulation 13,118
  subsumption eq142 eq11

theorem Equation3346_4512_implies_Equation4320 (G : Type*) [Magma G]
    (h3346 : Equation3346 G) (h4512 : Equation4512 G) : Equation4320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h3346 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq16 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X1 ◇ X0) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq22 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq43 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq24 -- superposition 24,11
  have eq54 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq43 -- forward demodulation 43,11
  have eq118 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq54 eq24 -- superposition 24,54
  have eq703 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq118 eq13 -- superposition 13,118
  subsumption eq703 rfl

theorem Equation3350_4512_implies_Equation40 (G : Type*) [Magma G]
    (h3350 : Equation3350 G) (h4512 : Equation4512 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X2))) := mod_symm (h3350 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) = ((X1 ◇ X0) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) = (X1 ◇ (X0 ◇ X3)) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq25 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq26 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := superpose eq12 eq25 -- forward demodulation 25,12
  have eq27 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X3 ◇ X1)) := superpose eq17 eq26 -- forward demodulation 26,17
  have eq61 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq17 eq27 -- superposition 27,17
  have eq97 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq12 eq61 -- forward demodulation 61,12
  have eq1092 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq11 eq97 -- superposition 97,11
  have eq1187 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq1092 eq13 -- superposition 13,1092
  subsumption eq1187 eq1092

theorem Equation3350_4512_implies_Equation3331 (G : Type*) [Magma G]
    (h3350 : Equation3350 G) (h4512 : Equation4512 G) : Equation3331 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X2))) := mod_symm (h3350 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) = ((X1 ◇ X0) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) = (X1 ◇ (X0 ◇ X3)) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq25 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq26 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := superpose eq12 eq25 -- forward demodulation 25,12
  have eq27 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X3 ◇ X1)) := superpose eq17 eq26 -- forward demodulation 26,17
  have eq28 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := superpose eq27 eq13 -- backward demodulation 13,27
  have eq34 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose eq11 eq28 -- superposition 28,11
  have eq62 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ ((X2 ◇ X2) ◇ X0)) := superpose eq11 eq27 -- superposition 27,11
  have eq98 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq12 eq62 -- forward demodulation 62,12
  have eq851 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq11 eq98 -- superposition 98,11
  have eq1054 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq851 eq34 -- superposition 34,851
  subsumption eq1054 rfl

theorem Equation3350_4512_implies_Equation3342 (G : Type*) [Magma G]
    (h3350 : Equation3350 G) (_ : Equation4512 G) : Equation3342 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X2))) := mod_symm (h3350 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3350_4512_implies_Equation3388 (G : Type*) [Magma G]
    (h3350 : Equation3350 G) (h4512 : Equation4512 G) : Equation3388 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X2))) := mod_symm (h3350 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) = ((X1 ◇ X0) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) = (X1 ◇ (X0 ◇ X3)) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq25 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq26 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := superpose eq12 eq25 -- forward demodulation 25,12
  have eq27 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X3 ◇ X1)) := superpose eq17 eq26 -- forward demodulation 26,17
  have eq30 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq11 eq20 -- forward demodulation 20,11
  have eq60 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ ((X2 ◇ X2) ◇ X0)) := superpose eq11 eq27 -- superposition 27,11
  have eq97 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq12 eq60 -- forward demodulation 60,12
  have eq153 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := superpose eq30 eq13 -- superposition 13,30
  subsumption eq153 eq97

theorem Equation3350_4512_implies_Equation4305 (G : Type*) [Magma G]
    (h3350 : Equation3350 G) (h4512 : Equation4512 G) : Equation4305 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X2))) := mod_symm (h3350 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) = ((X1 ◇ X0) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) = (X1 ◇ (X0 ◇ X3)) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq25 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq26 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := superpose eq12 eq25 -- forward demodulation 25,12
  have eq27 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X3 ◇ X1)) := superpose eq17 eq26 -- forward demodulation 26,17
  have eq36 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ X2) := superpose eq11 eq17 -- superposition 17,11
  have eq61 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq17 eq27 -- superposition 27,17
  have eq81 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK2 ◇ sK2)) := superpose eq27 eq13 -- superposition 13,27
  have eq98 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq12 eq61 -- forward demodulation 61,12
  have eq341 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ X2)) := superpose eq12 eq36 -- superposition 36,12
  have eq997 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq11 eq98 -- superposition 98,11
  have eq1443 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq997 eq81 -- superposition 81,997
  subsumption eq1443 eq341

theorem Equation3350_4512_implies_Equation4325 (G : Type*) [Magma G]
    (h3350 : Equation3350 G) (h4512 : Equation4512 G) : Equation4325 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X2))) := mod_symm (h3350 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) = ((X1 ◇ X0) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) = (X1 ◇ (X0 ◇ X3)) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq25 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq26 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := superpose eq12 eq25 -- forward demodulation 25,12
  have eq27 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X3 ◇ X1)) := superpose eq17 eq26 -- forward demodulation 26,17
  have eq28 : (sK1 ◇ (sK2 ◇ sK2)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq27 eq13 -- backward demodulation 13,27
  have eq37 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ X2) := superpose eq11 eq17 -- superposition 17,11
  have eq62 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq17 eq27 -- superposition 27,17
  have eq98 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq12 eq62 -- forward demodulation 62,12
  have eq339 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq37 -- superposition 37,12
  have eq995 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq11 eq98 -- superposition 98,11
  have eq1441 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq995 eq28 -- superposition 28,995
  subsumption eq1441 eq339

theorem Equation3353_4512_implies_Equation3306 (G : Type*) [Magma G]
    (h3353 : Equation3353 G) (h4512 : Equation4512 G) : Equation3306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3353 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = ((X1 ◇ X0) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq33 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq11 eq20 -- superposition 20,11
  have eq46 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq12 eq33 -- forward demodulation 33,12
  have eq184 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq46 eq25 -- superposition 25,46
  have eq469 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq184 eq13 -- superposition 13,184
  subsumption eq469 rfl

theorem Equation3388_4512_implies_Equation3271 (G : Type*) [Magma G]
    (h3388 : Equation3388 G) (_ : Equation4512 G) : Equation3271 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h3388 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3388_4512_implies_Equation3334 (G : Type*) [Magma G]
    (h3388 : Equation3388 G) (_ : Equation4512 G) : Equation3334 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h3388 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X1 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X1))) = (X3 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq15 eq15 -- superposition 15,15
  have eq36 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq11 eq15 -- superposition 15,11
  have eq53 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ (X0 ◇ sK1))) := superpose eq15 eq13 -- superposition 13,15
  have eq60 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X2 ◇ X1))) := superpose eq36 eq33 -- backward demodulation 33,36
  subsumption eq53 eq60

theorem Equation3388_4512_implies_Equation3346 (G : Type*) [Magma G]
    (h3388 : Equation3388 G) (_ : Equation4512 G) : Equation3346 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h3388 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3388_4512_implies_Equation3414 (G : Type*) [Magma G]
    (h3388 : Equation3388 G) (_ : Equation4512 G) : Equation3414 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h3388 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X1 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11
  have eq33 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X0 ◇ (X2 ◇ (X2 ◇ X1))) := superpose eq15 eq15 -- superposition 15,15
  have eq36 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq11 eq15 -- superposition 15,11
  have eq51 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X0 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1)))) := superpose eq15 eq11 -- superposition 11,15
  have eq60 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X2 ◇ X1))) := superpose eq36 eq33 -- backward demodulation 33,36
  have eq69 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq60 eq51 -- forward demodulation 51,60
  have eq70 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := superpose eq69 eq13 -- backward demodulation 13,69
  subsumption eq70 eq11

theorem Equation3388_4512_implies_Equation4362 (G : Type*) [Magma G]
    (h3388 : Equation3388 G) (_ : Equation4512 G) : Equation4362 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h3388 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X1 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11
  have eq33 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X0 ◇ (X2 ◇ (X2 ◇ X1))) := superpose eq15 eq15 -- superposition 15,15
  have eq36 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq11 eq15 -- superposition 15,11
  have eq51 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X0 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1)))) := superpose eq15 eq11 -- superposition 11,15
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X2 ◇ X1))) := superpose eq36 eq33 -- backward demodulation 33,36
  have eq67 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq58 eq51 -- forward demodulation 51,58
  have eq742 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq67 eq13 -- superposition 13,67
  subsumption eq742 rfl

theorem Equation3414_4512_implies_Equation3278 (G : Type*) [Magma G]
    (h3414 : Equation3414 G) (_ : Equation4512 G) : Equation3278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := mod_symm (h3414 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3414_4512_implies_Equation3353 (G : Type*) [Magma G]
    (h3414 : Equation3414 G) (_ : Equation4512 G) : Equation3353 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := mod_symm (h3414 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4268_4512_implies_Equation1 (G : Type*) [Magma G]
    (_ : Equation4268 G) (_ : Equation4512 G) : Equation1 G := by
  intro x
  rfl
theorem Equation4269_4512_implies_Equation1 (G : Type*) [Magma G]
    (_ : Equation4269 G) (_ : Equation4512 G) : Equation1 G := by
  intro x
  rfl
theorem Equation4270_4512_implies_Equation1 (G : Type*) [Magma G]
    (_ : Equation4270 G) (_ : Equation4512 G) : Equation1 G := by
  intro x
  rfl
theorem Equation4271_4512_implies_Equation4286 (G : Type*) [Magma G]
    (h4271 : Equation4271 G) (_ : Equation4512 G) : Equation4286 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h4271 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation4271_4512_implies_Equation4287 (G : Type*) [Magma G]
    (h4271 : Equation4271 G) (_ : Equation4512 G) : Equation4287 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h4271 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation4271_4512_implies_Equation4288 (G : Type*) [Magma G]
    (h4271 : Equation4271 G) (_ : Equation4512 G) : Equation4288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h4271 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation4271_4512_implies_Equation4315 (G : Type*) [Magma G]
    (h4271 : Equation4271 G) (_ : Equation4512 G) : Equation4315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h4271 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation4271_4512_implies_Equation4318 (G : Type*) [Magma G]
    (h4271 : Equation4271 G) (_ : Equation4512 G) : Equation4318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h4271 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation4271_4512_implies_Equation4358 (G : Type*) [Magma G]
    (h4271 : Equation4271 G) (_ : Equation4512 G) : Equation4358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h4271 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation4272_4512_implies_Equation1 (G : Type*) [Magma G]
    (_ : Equation4272 G) (_ : Equation4512 G) : Equation1 G := by
  intro x
  rfl
theorem Equation4273_4512_implies_Equation1 (G : Type*) [Magma G]
    (_ : Equation4273 G) (_ : Equation4512 G) : Equation1 G := by
  intro x
  rfl
theorem Equation4274_4512_implies_Equation4271 (G : Type*) [Magma G]
    (h4274 : Equation4274 G) (_ : Equation4512 G) : Equation4271 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h4274 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq38 (X0 X1 X3 X4 X5 X6 X7 : G) : (X6 ◇ (X0 ◇ X7)) = (X5 ◇ (X3 ◇ (X1 ◇ X4))) := superpose eq15 eq15 -- superposition 15,15
  have eq63 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ X1)) := superpose eq15 eq13 -- superposition 13,15
  have eq76 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X2 ◇ (X0 ◇ (sK1 ◇ X1))) := superpose eq11 eq63 -- superposition 63,11
  subsumption eq76 eq38

theorem Equation4274_4512_implies_Equation4278 (G : Type*) [Magma G]
    (h4274 : Equation4274 G) (_ : Equation4512 G) : Equation4278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h4274 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq38 (X0 X1 X3 X4 X5 X6 X7 : G) : (X6 ◇ (X0 ◇ X7)) = (X5 ◇ (X3 ◇ (X1 ◇ X4))) := superpose eq15 eq15 -- superposition 15,15
  have eq63 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ X1)) := superpose eq15 eq13 -- superposition 13,15
  have eq76 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X2 ◇ (X0 ◇ (sK2 ◇ X1))) := superpose eq11 eq63 -- superposition 63,11
  subsumption eq76 eq38

theorem Equation4274_4512_implies_Equation4299 (G : Type*) [Magma G]
    (h4274 : Equation4274 G) (_ : Equation4512 G) : Equation4299 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h4274 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation4274_4512_implies_Equation4301 (G : Type*) [Magma G]
    (h4274 : Equation4274 G) (_ : Equation4512 G) : Equation4301 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h4274 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation4274_4512_implies_Equation4331 (G : Type*) [Magma G]
    (h4274 : Equation4274 G) (_ : Equation4512 G) : Equation4331 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h4274 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq18 eq15

theorem Equation4274_4512_implies_Equation4364 (G : Type*) [Magma G]
    (h4274 : Equation4274 G) (_ : Equation4512 G) : Equation4364 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h4274 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq38 (X0 X1 X3 X4 X5 X6 X7 : G) : (X6 ◇ (X0 ◇ X7)) = (X5 ◇ (X3 ◇ (X1 ◇ X4))) := superpose eq15 eq15 -- superposition 15,15
  have eq63 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK2 ◇ X1)) := superpose eq15 eq13 -- superposition 13,15
  have eq75 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X2 ◇ (X0 ◇ (sK2 ◇ X1))) := superpose eq11 eq63 -- superposition 63,11
  subsumption eq75 eq38

theorem Equation4274_4512_implies_Equation4369 (G : Type*) [Magma G]
    (h4274 : Equation4274 G) (_ : Equation4512 G) : Equation4369 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h4274 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq18 eq15

theorem Equation4275_4512_implies_Equation1 (G : Type*) [Magma G]
    (_ : Equation4275 G) (_ : Equation4512 G) : Equation1 G := by
  intro x
  rfl
theorem Equation4276_4512_implies_Equation1 (G : Type*) [Magma G]
    (_ : Equation4276 G) (_ : Equation4512 G) : Equation1 G := by
  intro x
  rfl
theorem Equation4277_4512_implies_Equation4268 (G : Type*) [Magma G]
    (h4277 : Equation4277 G) (_ : Equation4512 G) : Equation4268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X2)) := mod_symm (h4277 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4277_4512_implies_Equation4275 (G : Type*) [Magma G]
    (h4277 : Equation4277 G) (_ : Equation4512 G) : Equation4275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X2)) := mod_symm (h4277 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4277_4512_implies_Equation4276 (G : Type*) [Magma G]
    (h4277 : Equation4277 G) (_ : Equation4512 G) : Equation4276 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X2)) := mod_symm (h4277 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4277_4512_implies_Equation4293 (G : Type*) [Magma G]
    (h4277 : Equation4277 G) (_ : Equation4512 G) : Equation4293 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X2)) := mod_symm (h4277 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq20 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq11

theorem Equation4278_4512_implies_Equation4287 (G : Type*) [Magma G]
    (h4278 : Equation4278 G) (_ : Equation4512 G) : Equation4287 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h4278 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X0)) = (X3 ◇ (X4 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq61 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (X1 ◇ sK1)) := superpose eq15 eq13 -- superposition 13,15
  subsumption eq61 eq15

theorem Equation4278_4512_implies_Equation4296 (G : Type*) [Magma G]
    (h4278 : Equation4278 G) (_ : Equation4512 G) : Equation4296 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h4278 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X0)) = (X3 ◇ (X4 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq18 eq15

theorem Equation4278_4512_implies_Equation4300 (G : Type*) [Magma G]
    (h4278 : Equation4278 G) (_ : Equation4512 G) : Equation4300 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h4278 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X0)) = (X3 ◇ (X4 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq18 eq15

theorem Equation4278_4512_implies_Equation4304 (G : Type*) [Magma G]
    (h4278 : Equation4278 G) (_ : Equation4512 G) : Equation4304 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h4278 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X0)) = (X3 ◇ (X4 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq18 eq15

theorem Equation4278_4512_implies_Equation4327 (G : Type*) [Magma G]
    (h4278 : Equation4278 G) (_ : Equation4512 G) : Equation4327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h4278 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation4278_4512_implies_Equation4362 (G : Type*) [Magma G]
    (h4278 : Equation4278 G) (_ : Equation4512 G) : Equation4362 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h4278 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X0)) = (X3 ◇ (X4 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq61 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (X1 ◇ sK2)) := superpose eq15 eq13 -- superposition 13,15
  subsumption eq61 eq15

theorem Equation4279_4512_implies_Equation4269 (G : Type*) [Magma G]
    (h4279 : Equation4279 G) (_ : Equation4512 G) : Equation4269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X1)) := mod_symm (h4279 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4279_4512_implies_Equation4273 (G : Type*) [Magma G]
    (h4279 : Equation4279 G) (_ : Equation4512 G) : Equation4273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X1)) := mod_symm (h4279 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4279_4512_implies_Equation4276 (G : Type*) [Magma G]
    (h4279 : Equation4279 G) (_ : Equation4512 G) : Equation4276 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X1)) := mod_symm (h4279 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4279_4512_implies_Equation4321 (G : Type*) [Magma G]
    (h4279 : Equation4279 G) (_ : Equation4512 G) : Equation4321 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X1)) := mod_symm (h4279 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq20 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq11

theorem Equation4280_4512_implies_Equation4270 (G : Type*) [Magma G]
    (h4280 : Equation4280 G) (_ : Equation4512 G) : Equation4270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X2)) := mod_symm (h4280 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4280_4512_implies_Equation4272 (G : Type*) [Magma G]
    (h4280 : Equation4280 G) (_ : Equation4512 G) : Equation4272 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X2)) := mod_symm (h4280 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4280_4512_implies_Equation4276 (G : Type*) [Magma G]
    (h4280 : Equation4280 G) (_ : Equation4512 G) : Equation4276 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X2)) := mod_symm (h4280 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4280_4512_implies_Equation4343 (G : Type*) [Magma G]
    (h4280 : Equation4280 G) (_ : Equation4512 G) : Equation4343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X2)) := mod_symm (h4280 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq20 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq11

theorem Equation4283_4512_implies_Equation1 (G : Type*) [Magma G]
    (_ : Equation4283 G) (_ : Equation4512 G) : Equation1 G := by
  intro x
  rfl
theorem Equation4284_4512_implies_Equation1 (G : Type*) [Magma G]
    (_ : Equation4284 G) (_ : Equation4512 G) : Equation1 G := by
  intro x
  rfl
theorem Equation4286_4512_implies_Equation4268 (G : Type*) [Magma G]
    (h4286 : Equation4286 G) (_ : Equation4512 G) : Equation4268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X0)) := mod_symm (h4286 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4286_4512_implies_Equation4269 (G : Type*) [Magma G]
    (h4286 : Equation4286 G) (_ : Equation4512 G) : Equation4269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X0)) := mod_symm (h4286 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4286_4512_implies_Equation4283 (G : Type*) [Magma G]
    (h4286 : Equation4286 G) (_ : Equation4512 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X0)) := mod_symm (h4286 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4287_4512_implies_Equation4269 (G : Type*) [Magma G]
    (h4287 : Equation4287 G) (_ : Equation4512 G) : Equation4269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X1)) := mod_symm (h4287 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4287_4512_implies_Equation4284 (G : Type*) [Magma G]
    (h4287 : Equation4287 G) (_ : Equation4512 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X1)) := mod_symm (h4287 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4288_4512_implies_Equation4268 (G : Type*) [Magma G]
    (h4288 : Equation4288 G) (_ : Equation4512 G) : Equation4268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := mod_symm (h4288 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4288_4512_implies_Equation4270 (G : Type*) [Magma G]
    (h4288 : Equation4288 G) (_ : Equation4512 G) : Equation4270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := mod_symm (h4288 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4288_4512_implies_Equation4284 (G : Type*) [Magma G]
    (h4288 : Equation4288 G) (_ : Equation4512 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := mod_symm (h4288 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4290_4512_implies_Equation1 (G : Type*) [Magma G]
    (_ : Equation4290 G) (_ : Equation4512 G) : Equation1 G := by
  intro x
  rfl
theorem Equation4291_4512_implies_Equation1 (G : Type*) [Magma G]
    (_ : Equation4291 G) (_ : Equation4512 G) : Equation1 G := by
  intro x
  rfl
theorem Equation4293_4512_implies_Equation1 (G : Type*) [Magma G]
    (_ : Equation4293 G) (_ : Equation4512 G) : Equation1 G := by
  intro x
  rfl
theorem Equation4296_4512_implies_Equation4269 (G : Type*) [Magma G]
    (h4296 : Equation4296 G) (_ : Equation4512 G) : Equation4269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ X1)) := mod_symm (h4296 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4296_4512_implies_Equation4275 (G : Type*) [Magma G]
    (h4296 : Equation4296 G) (_ : Equation4512 G) : Equation4275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ X1)) := mod_symm (h4296 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4296_4512_implies_Equation4291 (G : Type*) [Magma G]
    (h4296 : Equation4296 G) (_ : Equation4512 G) : Equation4291 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ X1)) := mod_symm (h4296 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4297_4512_implies_Equation4270 (G : Type*) [Magma G]
    (h4297 : Equation4297 G) (_ : Equation4512 G) : Equation4270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ X2)) := mod_symm (h4297 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4297_4512_implies_Equation4275 (G : Type*) [Magma G]
    (h4297 : Equation4297 G) (_ : Equation4512 G) : Equation4275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ X2)) := mod_symm (h4297 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4297_4512_implies_Equation4290 (G : Type*) [Magma G]
    (h4297 : Equation4297 G) (_ : Equation4512 G) : Equation4290 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ X2)) := mod_symm (h4297 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4299_4512_implies_Equation4277 (G : Type*) [Magma G]
    (h4299 : Equation4299 G) (h4512 : Equation4512 G) : Equation4277 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h4299 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- superposition 13,11
  have eq27 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq11 eq12 -- superposition 12,11
  have eq43 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq11 eq21 -- superposition 21,11
  have eq382 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X3)) := superpose eq15 eq27 -- superposition 27,15
  have eq437 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) ≠ (X2 ◇ (sK1 ◇ sK1)) := superpose eq27 eq43 -- superposition 43,27
  subsumption eq437 eq382

theorem Equation4299_4512_implies_Equation4280 (G : Type*) [Magma G]
    (h4299 : Equation4299 G) (h4512 : Equation4512 G) : Equation4280 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h4299 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = (X3 ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq26 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq11 eq12 -- superposition 12,11
  have eq61 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq16 eq13 -- superposition 13,16
  have eq183 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ X0)) ≠ (X1 ◇ (sK2 ◇ sK2)) := superpose eq20 eq61 -- superposition 61,20
  have eq346 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X3)) := superpose eq15 eq26 -- superposition 26,15
  have eq399 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) ≠ (X2 ◇ (sK2 ◇ sK2)) := superpose eq26 eq183 -- superposition 183,26
  subsumption eq399 eq346

theorem Equation4299_4512_implies_Equation4288 (G : Type*) [Magma G]
    (h4299 : Equation4299 G) (h4512 : Equation4512 G) : Equation4288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h4299 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = (X3 ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq26 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq11 eq12 -- superposition 12,11
  have eq61 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq16 eq13 -- superposition 13,16
  have eq183 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ X0)) ≠ (X1 ◇ (sK2 ◇ sK2)) := superpose eq20 eq61 -- superposition 61,20
  have eq343 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X3)) := superpose eq15 eq26 -- superposition 26,15
  have eq396 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) ≠ (X2 ◇ (sK2 ◇ sK2)) := superpose eq26 eq183 -- superposition 183,26
  subsumption eq396 eq343

theorem Equation4299_4512_implies_Equation4297 (G : Type*) [Magma G]
    (h4299 : Equation4299 G) (h4512 : Equation4512 G) : Equation4297 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h4299 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = (X3 ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq26 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq11 eq12 -- superposition 12,11
  have eq61 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq16 eq13 -- superposition 13,16
  have eq183 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ X0)) ≠ (X1 ◇ (sK2 ◇ sK2)) := superpose eq20 eq61 -- superposition 61,20
  have eq343 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X3)) := superpose eq15 eq26 -- superposition 26,15
  have eq396 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) ≠ (X2 ◇ (sK2 ◇ sK2)) := superpose eq26 eq183 -- superposition 183,26
  subsumption eq396 eq343

theorem Equation4299_4512_implies_Equation4304 (G : Type*) [Magma G]
    (h4299 : Equation4299 G) (h4512 : Equation4512 G) : Equation4304 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h4299 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  have eq27 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq11 eq12 -- superposition 12,11
  have eq44 (X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq11 eq21 -- superposition 21,11
  have eq140 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq20 eq44 -- superposition 44,20
  have eq379 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X3)) := superpose eq15 eq27 -- superposition 27,15
  have eq434 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) ≠ (X2 ◇ (sK1 ◇ sK1)) := superpose eq27 eq140 -- superposition 140,27
  subsumption eq434 eq379

theorem Equation4300_4512_implies_Equation4272 (G : Type*) [Magma G]
    (h4300 : Equation4300 G) (_ : Equation4512 G) : Equation4272 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := mod_symm (h4300 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4300_4512_implies_Equation4291 (G : Type*) [Magma G]
    (h4300 : Equation4300 G) (_ : Equation4512 G) : Equation4291 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := mod_symm (h4300 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4301_4512_implies_Equation4277 (G : Type*) [Magma G]
    (h4301 : Equation4301 G) (_ : Equation4512 G) : Equation4277 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := mod_symm (h4301 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq16 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X3)) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  have eq42 (X0 X1 : G) : (X0 ◇ (sK0 ◇ X0)) ≠ (X1 ◇ (sK1 ◇ X1)) := superpose eq11 eq22 -- superposition 22,11
  have eq516 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X3)) = (X2 ◇ (X1 ◇ X2)) := superpose eq16 eq18 -- superposition 18,16
  have eq564 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) ≠ (X2 ◇ (sK1 ◇ X2)) := superpose eq18 eq42 -- superposition 42,18
  subsumption eq564 eq516

theorem Equation4301_4512_implies_Equation4279 (G : Type*) [Magma G]
    (h4301 : Equation4301 G) (_ : Equation4512 G) : Equation4279 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := mod_symm (h4301 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq16 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X3)) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq67 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq16 eq13 -- superposition 13,16
  have eq221 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ X0)) ≠ (X1 ◇ (sK2 ◇ X1)) := superpose eq21 eq67 -- superposition 67,21
  have eq463 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ X3)) := superpose eq11 eq18 -- superposition 18,11
  have eq505 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) ≠ (sK0 ◇ (sK0 ◇ X2)) := superpose eq18 eq221 -- superposition 221,18
  subsumption eq505 eq463

theorem Equation4301_4512_implies_Equation4286 (G : Type*) [Magma G]
    (h4301 : Equation4301 G) (_ : Equation4512 G) : Equation4286 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := mod_symm (h4301 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq16 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X3)) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq67 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq16 eq13 -- superposition 13,16
  have eq221 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ X0)) ≠ (X1 ◇ (sK2 ◇ X1)) := superpose eq21 eq67 -- superposition 67,21
  have eq460 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ X3)) := superpose eq11 eq18 -- superposition 18,11
  have eq502 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) ≠ (sK0 ◇ (sK0 ◇ X2)) := superpose eq18 eq221 -- superposition 221,18
  subsumption eq502 eq460

theorem Equation4301_4512_implies_Equation4296 (G : Type*) [Magma G]
    (h4301 : Equation4301 G) (_ : Equation4512 G) : Equation4296 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := mod_symm (h4301 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq16 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X3)) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq67 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq16 eq13 -- superposition 13,16
  have eq221 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ X0)) ≠ (X1 ◇ (sK2 ◇ X1)) := superpose eq21 eq67 -- superposition 67,21
  have eq460 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ X3)) := superpose eq11 eq18 -- superposition 18,11
  have eq502 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) ≠ (sK0 ◇ (sK0 ◇ X2)) := superpose eq18 eq221 -- superposition 221,18
  subsumption eq502 eq460

theorem Equation4301_4512_implies_Equation4305 (G : Type*) [Magma G]
    (h4301 : Equation4301 G) (_ : Equation4512 G) : Equation4305 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := mod_symm (h4301 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq16 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X3)) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  have eq44 (X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X1 ◇ (sK1 ◇ X1)) := superpose eq11 eq22 -- superposition 22,11
  have eq154 (X0 X1 : G) : (X1 ◇ (sK1 ◇ X1)) ≠ (X0 ◇ (sK0 ◇ X0)) := superpose eq11 eq44 -- superposition 44,11
  have eq513 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ X3)) := superpose eq16 eq18 -- superposition 18,16
  have eq561 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) ≠ (X2 ◇ (sK1 ◇ X2)) := superpose eq18 eq154 -- superposition 154,18
  subsumption eq561 eq513

theorem Equation4304_4512_implies_Equation4272 (G : Type*) [Magma G]
    (h4304 : Equation4304 G) (_ : Equation4512 G) : Equation4272 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := mod_symm (h4304 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4304_4512_implies_Equation4275 (G : Type*) [Magma G]
    (h4304 : Equation4304 G) (_ : Equation4512 G) : Equation4275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := mod_symm (h4304 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4304_4512_implies_Equation4284 (G : Type*) [Magma G]
    (h4304 : Equation4304 G) (_ : Equation4512 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := mod_symm (h4304 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4305_4512_implies_Equation4273 (G : Type*) [Magma G]
    (h4305 : Equation4305 G) (_ : Equation4512 G) : Equation4273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X2)) := mod_symm (h4305 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4305_4512_implies_Equation4275 (G : Type*) [Magma G]
    (h4305 : Equation4305 G) (_ : Equation4512 G) : Equation4275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X2)) := mod_symm (h4305 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4305_4512_implies_Equation4283 (G : Type*) [Magma G]
    (h4305 : Equation4305 G) (_ : Equation4512 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X2)) := mod_symm (h4305 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4314_4512_implies_Equation1 (G : Type*) [Magma G]
    (_ : Equation4314 G) (_ : Equation4512 G) : Equation1 G := by
  intro x
  rfl
theorem Equation4315_4512_implies_Equation4268 (G : Type*) [Magma G]
    (h4315 : Equation4315 G) (_ : Equation4512 G) : Equation4268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h4315 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4315_4512_implies_Equation4314 (G : Type*) [Magma G]
    (h4315 : Equation4315 G) (_ : Equation4512 G) : Equation4314 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h4315 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4318_4512_implies_Equation4269 (G : Type*) [Magma G]
    (h4318 : Equation4318 G) (_ : Equation4512 G) : Equation4269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X2)) := mod_symm (h4318 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4318_4512_implies_Equation4270 (G : Type*) [Magma G]
    (h4318 : Equation4318 G) (_ : Equation4512 G) : Equation4270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X2)) := mod_symm (h4318 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4318_4512_implies_Equation4314 (G : Type*) [Magma G]
    (h4318 : Equation4318 G) (_ : Equation4512 G) : Equation4314 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X2)) := mod_symm (h4318 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4320_4512_implies_Equation1 (G : Type*) [Magma G]
    (_ : Equation4320 G) (_ : Equation4512 G) : Equation1 G := by
  intro x
  rfl
theorem Equation4321_4512_implies_Equation1 (G : Type*) [Magma G]
    (_ : Equation4321 G) (_ : Equation4512 G) : Equation1 G := by
  intro x
  rfl
theorem Equation4325_4512_implies_Equation4270 (G : Type*) [Magma G]
    (h4325 : Equation4325 G) (_ : Equation4512 G) : Equation4270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X2 ◇ X2)) := mod_symm (h4325 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4325_4512_implies_Equation4273 (G : Type*) [Magma G]
    (h4325 : Equation4325 G) (_ : Equation4512 G) : Equation4273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X2 ◇ X2)) := mod_symm (h4325 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4325_4512_implies_Equation4320 (G : Type*) [Magma G]
    (h4325 : Equation4325 G) (_ : Equation4512 G) : Equation4320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X2 ◇ X2)) := mod_symm (h4325 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4327_4512_implies_Equation4269 (G : Type*) [Magma G]
    (h4327 : Equation4327 G) (_ : Equation4512 G) : Equation4269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h4327 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4327_4512_implies_Equation4272 (G : Type*) [Magma G]
    (h4327 : Equation4327 G) (_ : Equation4512 G) : Equation4272 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h4327 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4327_4512_implies_Equation4320 (G : Type*) [Magma G]
    (h4327 : Equation4327 G) (_ : Equation4512 G) : Equation4320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h4327 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4331_4512_implies_Equation4279 (G : Type*) [Magma G]
    (h4331 : Equation4331 G) (h4512 : Equation4512 G) : Equation4279 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X1)) := mod_symm (h4331 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq20 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  have eq27 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq11 eq12 -- superposition 12,11
  have eq39 (X0 X1 : G) : (X1 ◇ (sK2 ◇ sK2)) ≠ (X0 ◇ (sK0 ◇ X0)) := superpose eq11 eq21 -- superposition 21,11
  have eq177 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (X0 ◇ X3)) := superpose eq20 eq27 -- superposition 27,20
  have eq221 (X0 X1 : G) : (X1 ◇ (sK0 ◇ X1)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq20 eq39 -- superposition 39,20
  subsumption eq221 eq177

theorem Equation4331_4512_implies_Equation4280 (G : Type*) [Magma G]
    (h4331 : Equation4331 G) (_ : Equation4512 G) : Equation4280 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X1)) := mod_symm (h4331 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  have eq41 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq11 eq21 -- superposition 21,11
  subsumption eq41 eq15

theorem Equation4331_4512_implies_Equation4318 (G : Type*) [Magma G]
    (h4331 : Equation4331 G) (_ : Equation4512 G) : Equation4318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X1)) := mod_symm (h4331 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq16 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  have eq38 (X0 X1 : G) : (X0 ◇ (sK1 ◇ sK1)) ≠ (X1 ◇ (sK2 ◇ X1)) := superpose eq11 eq21 -- superposition 21,11
  have eq62 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq16 eq11 -- superposition 11,16
  have eq142 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ≠ (X2 ◇ (sK1 ◇ sK1)) := superpose eq16 eq38 -- superposition 38,16
  subsumption eq142 eq62

theorem Equation4331_4512_implies_Equation4325 (G : Type*) [Magma G]
    (h4331 : Equation4331 G) (_ : Equation4512 G) : Equation4325 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X1)) := mod_symm (h4331 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq16 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  have eq38 (X0 X1 : G) : (X0 ◇ (sK1 ◇ sK1)) ≠ (X1 ◇ (sK2 ◇ X1)) := superpose eq11 eq21 -- superposition 21,11
  have eq62 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq16 eq11 -- superposition 11,16
  have eq142 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ≠ (X2 ◇ (sK1 ◇ sK1)) := superpose eq16 eq38 -- superposition 38,16
  subsumption eq142 eq62

theorem Equation4331_4512_implies_Equation4327 (G : Type*) [Magma G]
    (h4331 : Equation4331 G) (_ : Equation4512 G) : Equation4327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X1)) := mod_symm (h4331 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq16 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  have eq38 (X0 X1 : G) : (X0 ◇ (sK1 ◇ sK1)) ≠ (X1 ◇ (sK0 ◇ X1)) := superpose eq11 eq21 -- superposition 21,11
  have eq60 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq16 eq11 -- superposition 11,16
  have eq139 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ≠ (X2 ◇ (sK1 ◇ sK1)) := superpose eq16 eq38 -- superposition 38,16
  subsumption eq139 eq60

theorem Equation4343_4512_implies_Equation1 (G : Type*) [Magma G]
    (_ : Equation4343 G) (_ : Equation4512 G) : Equation1 G := by
  intro x
  rfl
theorem Equation4358_4512_implies_Equation4283 (G : Type*) [Magma G]
    (h4358 : Equation4358 G) (_ : Equation4512 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := mod_symm (h4358 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4362_4512_implies_Equation4320 (G : Type*) [Magma G]
    (h4362 : Equation4362 G) (_ : Equation4512 G) : Equation4320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h4362 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4364_4512_implies_Equation4283 (G : Type*) [Magma G]
    (h4364 : Equation4364 G) (_ : Equation4512 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h4364 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4364_4512_implies_Equation4290 (G : Type*) [Magma G]
    (h4364 : Equation4364 G) (_ : Equation4512 G) : Equation4290 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h4364 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4364_4512_implies_Equation4320 (G : Type*) [Magma G]
    (h4364 : Equation4364 G) (_ : Equation4512 G) : Equation4320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h4364 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation4369_4512_implies_Equation4290 (G : Type*) [Magma G]
    (h4369 : Equation4369 G) (_ : Equation4512 G) : Equation4290 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := mod_symm (h4369 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11


end VampireProven

