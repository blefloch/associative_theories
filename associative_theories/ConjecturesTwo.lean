import equational_theories.Superposition
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
import equational_theories.Equations.All

/- Generated file collecting conjectures about pairs of equations -/

namespace Conjectures

theorem Equation3_56_4512_implies_Equation4 (G : Type*) [Magma G]
    (h3 : Equation3 G) (h56 : Equation56 G) (_ : Equation4512 G) : Equation4 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := mod_symm (h3 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h56 ..)
  have eq15 : sK0 ≠ (sK0 ◇ sK1) := mod_symm nh
  have eq16 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq12 eq13 -- forward demodulation 13,12
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq16 -- forward demodulation 16,12
  subsumption eq15 eq17

theorem Equation3_75_4512_implies_Equation5 (G : Type*) [Magma G]
    (h3 : Equation3 G) (h75 : Equation75 G) (h4512 : Equation4512 G) : Equation5 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := mod_symm (h3 ..)
  have eq13 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h75 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq15 : sK0 ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq14 -- superposition 14,12
  have eq27 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq18 eq13 -- backward demodulation 13,18
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq27 eq18 -- backward demodulation 18,27
  have eq50 : sK0 ≠ sK0 := superpose eq28 eq15 -- superposition 15,28
  subsumption eq50 rfl

theorem Equation3_429_4512_implies_Equation10 (G : Type*) [Magma G]
    (h3 : Equation3 G) (h429 : Equation429 G) (h4512 : Equation4512 G) : Equation10 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := mod_symm (h3 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h429 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq14 -- superposition 14,12
  have eq41 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq28 eq13 -- backward demodulation 13,28
  have eq54 : sK0 ≠ sK0 := superpose eq41 eq15 -- superposition 15,41
  subsumption eq54 rfl

theorem Equation8_440_4512_implies_Equation11 (G : Type*) [Magma G]
    (h8 : Equation8 G) (h440 : Equation440 G) (_ : Equation4512 G) : Equation11 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := mod_symm (h8 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h440 ..)
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq16 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq15 eq16

theorem Equation8_513_4512_implies_Equation16 (G : Type*) [Magma G]
    (h8 : Equation8 G) (h513 : Equation513 G) (h4512 : Equation4512 G) : Equation16 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := mod_symm (h8 ..)
  have eq13 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h513 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq15 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq12 eq14 -- superposition 14,12
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq14 eq18 -- forward demodulation 18,14
  have eq30 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq29 eq13 -- backward demodulation 13,29
  have eq49 : sK0 ≠ sK0 := superpose eq30 eq15 -- superposition 15,30
  subsumption eq49 rfl

theorem Equation8_3261_4512_implies_Equation419 (G : Type*) [Magma G]
    (h8 : Equation8 G) (h3261 : Equation3261 G) (_ : Equation4512 G) : Equation419 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := mod_symm (h8 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h3261 ..)
  have eq15 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq16 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq13 eq15 -- forward demodulation 15,13
  subsumption eq16 eq12

theorem Equation10_325_4512_implies_Equation4 (G : Type*) [Magma G]
    (h10 : Equation10 G) (h325 : Equation325 G) (_ : Equation4512 G) : Equation4 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h10 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X1) := mod_symm (h325 ..)
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := mod_symm nh
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq13 eq14 -- forward demodulation 14,13
  subsumption eq16 eq17

theorem Equation10_333_4512_implies_Equation5 (G : Type*) [Magma G]
    (h10 : Equation10 G) (h333 : Equation333 G) (_ : Equation4512 G) : Equation5 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h10 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h333 ..)
  have eq16 : sK0 ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq13 eq14 -- forward demodulation 14,13
  subsumption eq16 eq17

theorem Equation11_3353_4512_implies_Equation14 (G : Type*) [Magma G]
    (h11 : Equation11 G) (h3353 : Equation3353 G) (h4512 : Equation4512 G) : Equation14 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := mod_symm (h11 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3353 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq18 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) = X0 := superpose eq13 eq14 -- superposition 14,13
  have eq20 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq15 eq18 -- forward demodulation 18,15
  have eq28 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := superpose eq15 eq13 -- superposition 13,15
  have eq45 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq20 eq20 -- superposition 20,20
  have eq60 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq45 -- forward demodulation 45,15
  have eq61 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq13 eq60 -- forward demodulation 60,13
  have eq62 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq20 eq61 -- forward demodulation 61,20
  have eq174 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq62 eq28 -- superposition 28,62
  have eq304 : sK0 ≠ sK0 := superpose eq174 eq16 -- superposition 16,174
  subsumption eq304 rfl

theorem Equation38_39_4512_implies_Equation41 (G : Type*) [Magma G]
    (h38 : Equation38 G) (h39 : Equation39 G) (_ : Equation4512 G) : Equation41 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := mod_symm (h38 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := mod_symm (h39 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK2) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq13 eq13 -- superposition 13,13
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq14 eq14 -- superposition 14,14
  have eq49 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ X2) := superpose eq14 eq17 -- superposition 17,14
  have eq93 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK2) := superpose eq19 eq16 -- superposition 16,19
  subsumption eq93 eq49

theorem Equation40_307_4512_implies_Equation316 (G : Type*) [Magma G]
    (h40 : Equation40 G) (h307 : Equation307 G) (_ : Equation4512 G) : Equation316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := mod_symm (h40 ..)
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h307 ..)
  have eq15 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq24 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq13 eq15 -- superposition 15,13
  subsumption eq24 eq12

theorem Equation40_309_4512_implies_Equation313 (G : Type*) [Magma G]
    (h40 : Equation40 G) (h309 : Equation309 G) (_ : Equation4512 G) : Equation313 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := mod_symm (h40 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h309 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq24 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq24 eq13

theorem Equation40_311_4512_implies_Equation314 (G : Type*) [Magma G]
    (h40 : Equation40 G) (h311 : Equation311 G) (_ : Equation4512 G) : Equation314 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := mod_symm (h40 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h311 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq30 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq30 eq13

theorem Equation40_3260_4512_implies_Equation3273 (G : Type*) [Magma G]
    (h40 : Equation40 G) (h3260 : Equation3260 G) (_ : Equation4512 G) : Equation3273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := mod_symm (h40 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h3260 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq27 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq27 eq13

theorem Equation40_3264_4512_implies_Equation3275 (G : Type*) [Magma G]
    (h40 : Equation40 G) (h3264 : Equation3264 G) (_ : Equation4512 G) : Equation3275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := mod_symm (h40 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h3264 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq27 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq27 eq13

theorem Equation40_3265_4512_implies_Equation3290 (G : Type*) [Magma G]
    (h40 : Equation40 G) (h3265 : Equation3265 G) (_ : Equation4512 G) : Equation3290 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := mod_symm (h40 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ X1))) := mod_symm (h3265 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq31 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq31 eq13

theorem Equation40_3267_4512_implies_Equation3277 (G : Type*) [Magma G]
    (h40 : Equation40 G) (h3267 : Equation3267 G) (_ : Equation4512 G) : Equation3277 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := mod_symm (h40 ..)
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h3267 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq34 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq34 eq13

theorem Equation40_3274_4512_implies_Equation3265 (G : Type*) [Magma G]
    (h40 : Equation40 G) (h3274 : Equation3274 G) (_ : Equation4512 G) : Equation3265 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := mod_symm (h40 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h3274 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq29 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq29 eq13

theorem Equation40_3292_4512_implies_Equation3260 (G : Type*) [Magma G]
    (h40 : Equation40 G) (h3292 : Equation3292 G) (_ : Equation4512 G) : Equation3260 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := mod_symm (h40 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X1 ◇ X0))) := mod_symm (h3292 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq34 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq34 eq13

theorem Equation40_3300_4512_implies_Equation3267 (G : Type*) [Magma G]
    (h40 : Equation40 G) (h3300 : Equation3300 G) (_ : Equation4512 G) : Equation3267 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := mod_symm (h40 ..)
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ X0))) := mod_symm (h3300 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq40 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq40 eq13

theorem Equation40_3306_4512_implies_Equation3350 (G : Type*) [Magma G]
    (h40 : Equation40 G) (h3306 : Equation3306 G) (h4512 : Equation4512 G) : Equation3350 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := mod_symm (h40 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := mod_symm (h3306 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq21 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (X0 ◇ X0))) := superpose eq13 eq16 -- superposition 16,13
  have eq23 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq13 eq14 -- superposition 14,13
  have eq26 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq30 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq13 eq15 -- superposition 15,13
  have eq35 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq14 -- superposition 14,15
  have eq44 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq15 eq35 -- forward demodulation 35,15
  have eq58 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) := superpose eq23 eq15 -- superposition 15,23
  have eq62 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := superpose eq15 eq58 -- forward demodulation 58,15
  have eq63 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq15 eq62 -- forward demodulation 62,15
  have eq65 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ X2) ◇ X0) := superpose eq13 eq26 -- superposition 26,13
  have eq69 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ (X0 ◇ X1)) = (X0 ◇ ((X2 ◇ X2) ◇ X1)) := superpose eq26 eq26 -- superposition 26,26
  have eq72 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq14 eq26 -- superposition 26,14
  have eq75 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = ((X3 ◇ X3) ◇ X2) := superpose eq15 eq26 -- superposition 26,15
  have eq92 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X3)) = (((X2 ◇ X2) ◇ X1) ◇ X3) := superpose eq26 eq15 -- superposition 15,26
  have eq100 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X3)) = ((X2 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq26 eq15 -- superposition 15,26
  have eq106 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ (X2 ◇ X1))) := superpose eq15 eq69 -- forward demodulation 69,15
  have eq107 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X2 ◇ X1))) := superpose eq72 eq106 -- backward demodulation 106,72
  have eq108 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X1 ◇ X2)) := superpose eq107 eq63 -- backward demodulation 63,107
  have eq109 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = ((X3 ◇ X3) ◇ X2) := superpose eq15 eq75 -- forward demodulation 75,15
  have eq120 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X3)) = ((X2 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq15 eq92 -- forward demodulation 92,15
  have eq121 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ X3))) := superpose eq15 eq120 -- forward demodulation 120,15
  have eq127 (X1 X2 X3 : G) : (X1 ◇ X3) = ((X2 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq72 eq100 -- forward demodulation 100,72
  have eq128 (X0 X1 X3 : G) : (X1 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ X3))) := superpose eq127 eq121 -- backward demodulation 121,127
  have eq344 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = ((X3 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq15 eq65 -- superposition 65,15
  have eq355 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ X2)) := superpose eq15 eq65 -- superposition 65,15
  have eq387 (X1 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ ((X1 ◇ X1) ◇ sK0)) := superpose eq65 eq21 -- superposition 21,65
  have eq415 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq72 eq344 -- forward demodulation 344,72
  have eq447 (X1 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (X1 ◇ (X1 ◇ sK0))) := superpose eq15 eq387 -- forward demodulation 387,15
  have eq485 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ X2) ◇ X1)) = ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X3 ◇ ((X2 ◇ X2) ◇ X1))))) := superpose eq26 eq44 -- superposition 44,26
  have eq582 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X2 ◇ X1))) = ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1)))))) := superpose eq15 eq485 -- forward demodulation 485,15
  have eq583 (X0 X1 X3 : G) : (X3 ◇ X1) = ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X3 ◇ X1)))) := superpose eq107 eq582 -- forward demodulation 582,107
  have eq1150 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X1))) = (X3 ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq30 eq107 -- superposition 107,30
  have eq1229 (X0 X1 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq415 eq1150 -- forward demodulation 1150,415
  have eq2736 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) := superpose eq108 eq447 -- superposition 447,108
  have eq5473 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X2))))) = ((X4 ◇ X4) ◇ (X0 ◇ X1)) := superpose eq355 eq109 -- superposition 109,355
  have eq5845 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X3 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X2))))) := superpose eq72 eq5473 -- forward demodulation 5473,72
  have eq5846 (X0 X1 X3 : G) : (X0 ◇ X1) = (X3 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq415 eq5845 -- forward demodulation 5845,415
  have eq5848 (X0 X1 X3 : G) : (X3 ◇ X1) = ((X3 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq5846 eq583 -- backward demodulation 583,5846
  have eq11227 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) := superpose eq5848 eq1229 -- superposition 1229,5848
  have eq11498 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq15 eq11227 -- forward demodulation 11227,15
  have eq11499 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X1 ◇ X0)) := superpose eq1229 eq11498 -- forward demodulation 11498,1229
  have eq11500 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := superpose eq11499 eq2736 -- backward demodulation 2736,11499
  subsumption eq11500 eq128

theorem Equation40_4321_4512_implies_Equation3264 (G : Type*) [Magma G]
    (h40 : Equation40 G) (h4321 : Equation4321 G) (h4512 : Equation4512 G) : Equation3264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := mod_symm (h40 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4321 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq31 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq34 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq13 eq15 -- superposition 15,13
  have eq36 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq14 eq15 -- superposition 15,14
  have eq44 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq15 eq31 -- forward demodulation 31,15
  have eq48 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq36 -- forward demodulation 36,15
  have eq267 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq14 eq44 -- superposition 44,14
  have eq362 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))))) = (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq15 eq267 -- forward demodulation 267,15
  have eq363 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq15 eq362 -- forward demodulation 362,15
  have eq1724 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))))) := superpose eq48 eq48 -- superposition 48,48
  have eq1726 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) = (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0))) := superpose eq48 eq48 -- superposition 48,48
  have eq1740 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq34 eq48 -- superposition 48,34
  have eq1743 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq48 eq48 -- superposition 48,48
  have eq1937 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))))) := superpose eq15 eq1724 -- forward demodulation 1724,15
  have eq1938 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))))) := superpose eq15 eq1937 -- forward demodulation 1937,15
  have eq1942 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0)))) := superpose eq15 eq1726 -- forward demodulation 1726,15
  have eq1943 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) = (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq15 eq1942 -- forward demodulation 1942,15
  have eq1944 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) = (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))))) := superpose eq15 eq1943 -- forward demodulation 1943,15
  have eq1945 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))))) := superpose eq15 eq1944 -- forward demodulation 1944,15
  have eq2075 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))))) := superpose eq1740 eq1938 -- backward demodulation 1938,1740
  have eq2304 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))))) := superpose eq1740 eq2075 -- forward demodulation 2075,1740
  have eq2305 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))))) := superpose eq1740 eq2304 -- forward demodulation 2304,1740
  have eq2306 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq2305 eq1945 -- backward demodulation 1945,2305
  have eq2310 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq2306 eq363 -- backward demodulation 363,2306
  have eq2335 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq1740 eq2310 -- forward demodulation 2310,1740
  have eq9563 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq15 eq2335 -- superposition 2335,15
  have eq9794 (X0 X1 X2 : G) : (X1 ◇ X1) = (X1 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9563 eq1743 -- backward demodulation 1743,9563
  have eq10235 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq9794 eq16 -- superposition 16,9794
  subsumption eq10235 rfl

theorem Equation43_56_4512_implies_Equation66 (G : Type*) [Magma G]
    (h43 : Equation43 G) (h56 : Equation56 G) (h4512 : Equation4512 G) : Equation66 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h43 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h56 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq27 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := superpose eq13 eq15 -- superposition 15,13
  have eq221 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := superpose eq27 eq16 -- superposition 16,27
  have eq268 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := superpose eq13 eq221 -- forward demodulation 221,13
  subsumption eq268 eq14

theorem Equation43_75_4512_implies_Equation56 (G : Type*) [Magma G]
    (h43 : Equation43 G) (h75 : Equation75 G) (h4512 : Equation4512 G) : Equation56 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h43 ..)
  have eq14 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h75 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq23 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := superpose eq13 eq15 -- superposition 15,13
  have eq122 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq23 eq14 -- superposition 14,23
  have eq295 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose eq23 eq122 -- superposition 122,23
  have eq310 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose eq13 eq295 -- forward demodulation 295,13
  have eq1392 : sK0 ≠ sK0 := superpose eq310 eq16 -- superposition 16,310
  subsumption eq1392 rfl

theorem Equation43_323_4512_implies_Equation332 (G : Type*) [Magma G]
    (h43 : Equation43 G) (h323 : Equation323 G) (h4512 : Equation4512 G) : Equation332 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h43 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h323 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq24 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := superpose eq13 eq15 -- superposition 15,13
  have eq103 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq14 eq24 -- superposition 24,14
  have eq120 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq24 eq16 -- superposition 16,24
  subsumption eq120 eq103

theorem Equation43_440_4512_implies_Equation477 (G : Type*) [Magma G]
    (h43 : Equation43 G) (h440 : Equation440 G) (h4512 : Equation4512 G) : Equation477 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h43 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h440 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq31 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := superpose eq13 eq15 -- superposition 15,13
  have eq246 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := superpose eq31 eq16 -- superposition 16,31
  have eq304 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := superpose eq13 eq246 -- forward demodulation 246,13
  subsumption eq304 eq14

theorem Equation43_3306_4512_implies_Equation3342 (G : Type*) [Magma G]
    (h43 : Equation43 G) (h3306 : Equation3306 G) (h4512 : Equation4512 G) : Equation3342 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h43 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := mod_symm (h3306 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq24 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := superpose eq13 eq15 -- superposition 15,13
  have eq131 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq24 eq14 -- superposition 14,24
  have eq151 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := superpose eq24 eq16 -- superposition 16,24
  have eq175 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq13 eq151 -- forward demodulation 151,13
  subsumption eq175 eq131

theorem Equation47_411_4512_implies_Equation3 (G : Type*) [Magma G]
    (h47 : Equation47 G) (h411 : Equation411 G) (_ : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h47 ..)
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h411 ..)
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq11 -- forward demodulation 11,10
  subsumption eq13 eq14

theorem Equation47_3253_4512_implies_Equation3 (G : Type*) [Magma G]
    (h47 : Equation47 G) (h3253 : Equation3253 G) (_ : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h47 ..)
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h3253 ..)
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq11 -- forward demodulation 11,10
  subsumption eq13 eq14

theorem Equation47_4268_4512_implies_Equation3 (G : Type*) [Magma G]
    (h47 : Equation47 G) (h4268 : Equation4268 G) (_ : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h47 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4268 ..)
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq16 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq12 -- superposition 12,11
  have eq23 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq16 eq11 -- backward demodulation 11,16
  have eq25 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq23 eq16 -- backward demodulation 16,23
  have eq31 : sK0 ≠ sK0 := superpose eq25 eq14 -- superposition 14,25
  subsumption eq31 rfl

theorem Equation47_4269_4512_implies_Equation3 (G : Type*) [Magma G]
    (h47 : Equation47 G) (h4269 : Equation4269 G) (h4512 : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h47 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4269 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq16 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq12 eq11 -- superposition 11,12
  have eq51 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := superpose eq13 eq16 -- superposition 16,13
  have eq136 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq51 -- superposition 51,11
  have eq234 : sK0 ≠ sK0 := superpose eq136 eq14 -- superposition 14,136
  subsumption eq234 rfl

theorem Equation47_4270_4512_implies_Equation3 (G : Type*) [Magma G]
    (h47 : Equation47 G) (h4270 : Equation4270 G) (h4512 : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h47 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4270 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq12 eq12 -- superposition 12,12
  have eq16 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq12 eq11 -- superposition 11,12
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq13 eq31 -- forward demodulation 31,13
  have eq88 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X2 := superpose eq15 eq16 -- superposition 16,15
  have eq107 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) = X2 := superpose eq13 eq88 -- forward demodulation 88,13
  have eq108 (X0 X2 : G) : (X2 ◇ (X2 ◇ X0)) = X2 := superpose eq16 eq107 -- forward demodulation 107,16
  have eq109 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq108 eq32 -- backward demodulation 32,108
  have eq152 : sK0 ≠ sK0 := superpose eq109 eq14 -- superposition 14,109
  subsumption eq152 rfl

theorem Equation47_4272_4512_implies_Equation3 (G : Type*) [Magma G]
    (h47 : Equation47 G) (h4272 : Equation4272 G) (h4512 : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h47 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4272 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq12 eq11 -- superposition 11,12
  have eq27 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq12 eq13 -- superposition 13,12
  have eq50 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq12 eq17 -- superposition 17,12
  have eq59 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq27 eq50 -- forward demodulation 50,27
  have eq68 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq17 eq15 -- superposition 15,17
  have eq100 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq12 eq68 -- forward demodulation 68,12
  have eq101 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq100 eq59 -- backward demodulation 59,100
  have eq103 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq101 eq12 -- backward demodulation 12,101
  have eq114 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq101 eq103 -- forward demodulation 103,101
  have eq207 : sK0 ≠ sK0 := superpose eq114 eq14 -- superposition 14,114
  subsumption eq207 rfl

theorem Equation47_4273_4512_implies_Equation2 (G : Type*) [Magma G]
    (h47 : Equation47 G) (h4273 : Equation4273 G) (h4512 : Equation4512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h47 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4273 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq15 : sK0 ≠ sK1 := mod_symm nh
  have eq20 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq13 eq12 -- superposition 12,13
  have eq21 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq12 eq14 -- superposition 14,12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq13 eq14 -- superposition 14,13
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq13 eq14 -- superposition 14,13
  have eq26 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq13 eq14 -- superposition 14,13
  have eq35 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq14 eq21 -- forward demodulation 21,14
  have eq36 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq14 eq35 -- forward demodulation 35,14
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq14 eq22 -- forward demodulation 22,14
  have eq38 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq14 eq23 -- forward demodulation 23,14
  have eq44 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq14 eq26 -- forward demodulation 26,14
  have eq45 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq20 eq44 -- forward demodulation 44,20
  have eq46 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq14 eq45 -- forward demodulation 45,14
  have eq60 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq12 eq20 -- superposition 20,12
  have eq61 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq13 eq20 -- superposition 20,13
  have eq72 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq14 eq60 -- forward demodulation 60,14
  have eq73 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq14 eq72 -- forward demodulation 72,14
  have eq74 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq73 -- forward demodulation 73,12
  have eq76 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose eq74 eq13 -- backward demodulation 13,74
  have eq81 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq74 eq38 -- backward demodulation 38,74
  have eq83 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq74 eq76 -- forward demodulation 76,74
  have eq86 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq83 eq37 -- backward demodulation 37,83
  have eq87 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X1 := superpose eq83 eq46 -- backward demodulation 46,83
  have eq89 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq86 eq36 -- backward demodulation 36,86
  have eq96 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq74 eq81 -- forward demodulation 81,74
  have eq97 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = X0 := superpose eq14 eq61 -- forward demodulation 61,14
  have eq98 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq89 eq97 -- forward demodulation 97,89
  have eq99 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq96 eq98 -- forward demodulation 98,96
  have eq100 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq74 eq99 -- forward demodulation 99,74
  have eq102 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq100 eq87 -- backward demodulation 87,100
  have eq109 (X2 X3 : G) : X2 = X3 := superpose eq102 eq102 -- superposition 102,102
  have eq111 (X0 : G) : sK0 ≠ X0 := superpose eq109 eq15 -- superposition 15,109
  subsumption eq111 eq109

theorem Equation47_4275_4512_implies_Equation3 (G : Type*) [Magma G]
    (h47 : Equation47 G) (h4275 : Equation4275 G) (h4512 : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h47 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4275 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq16 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq12 eq11 -- superposition 11,12
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq13 eq31 -- forward demodulation 31,13
  have eq54 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq12 eq16 -- superposition 16,12
  have eq66 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq16 eq54 -- forward demodulation 54,16
  have eq125 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq13 eq66 -- superposition 66,13
  have eq132 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq125 eq11 -- backward demodulation 11,125
  have eq138 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq132 eq12 -- backward demodulation 12,132
  have eq144 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq138 eq32 -- backward demodulation 32,138
  have eq158 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq138 eq144 -- forward demodulation 144,138
  have eq211 : sK0 ≠ sK0 := superpose eq158 eq14 -- superposition 14,158
  subsumption eq211 rfl

theorem Equation47_4276_4512_implies_Equation56 (G : Type*) [Magma G]
    (h47 : Equation47 G) (h4276 : Equation4276 G) (_ : Equation4512 G) : Equation56 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h47 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := mod_symm (h4276 ..)
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq20 (X0 : G) : sK0 ≠ (sK0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq13 eq15 -- superposition 15,13
  have eq54 : sK0 ≠ sK0 := superpose eq12 eq20 -- superposition 20,12
  subsumption eq54 rfl

theorem Equation47_4276_4512_implies_Equation75 (G : Type*) [Magma G]
    (h47 : Equation47 G) (h4276 : Equation4276 G) (h4512 : Equation4512 G) : Equation75 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h47 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := mod_symm (h4276 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq15 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq20 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := superpose eq13 eq12 -- superposition 12,13
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = ((X1 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq13 eq14 -- superposition 14,13
  have eq38 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq14 eq23 -- forward demodulation 23,14
  have eq172 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = ((X2 ◇ (X2 ◇ X2)) ◇ X0) := superpose eq13 eq38 -- superposition 38,13
  have eq259 (X0 X2 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X0) = X0 := superpose eq20 eq172 -- forward demodulation 172,20
  have eq262 (X0 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X2))) = X2 := superpose eq259 eq38 -- backward demodulation 38,259
  have eq367 : sK0 ≠ sK0 := superpose eq262 eq15 -- superposition 15,262
  subsumption eq367 rfl

theorem Equation47_4284_4512_implies_Equation3 (G : Type*) [Magma G]
    (h47 : Equation47 G) (h4284 : Equation4284 G) (h4512 : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h47 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq12 eq12 -- superposition 12,12
  have eq16 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq11 eq16 -- forward demodulation 16,11
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq13 eq18 -- forward demodulation 18,13
  have eq33 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq13 eq32 -- forward demodulation 32,13
  have eq34 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq17 eq33 -- forward demodulation 33,17
  have eq35 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq34 eq11 -- backward demodulation 11,34
  have eq37 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq34 eq12 -- backward demodulation 12,34
  have eq79 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq35 eq37 -- superposition 37,35
  have eq94 : sK0 ≠ sK0 := superpose eq79 eq14 -- superposition 14,79
  subsumption eq94 rfl

theorem Equation47_4290_4512_implies_Equation43 (G : Type*) [Magma G]
    (h47 : Equation47 G) (h4290 : Equation4290 G) (h4512 : Equation4512 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h47 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq15 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq17 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq13 eq13 -- superposition 13,13
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq14 eq19 -- forward demodulation 19,14
  have eq23 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq12 eq14 -- superposition 14,12
  have eq29 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq13 eq14 -- superposition 14,13
  have eq37 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq14 eq23 -- forward demodulation 23,14
  have eq38 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq14 eq37 -- forward demodulation 37,14
  have eq62 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq13 eq20 -- superposition 20,13
  have eq127 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq13 eq62 -- superposition 62,13
  have eq140 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq12 eq127 -- forward demodulation 127,12
  have eq701 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq29 eq140 -- superposition 140,29
  have eq784 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq14 eq701 -- forward demodulation 701,14
  have eq785 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq38 eq784 -- forward demodulation 784,38
  have eq786 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq13 eq785 -- forward demodulation 785,13
  have eq787 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq12 eq786 -- forward demodulation 786,12
  have eq1200 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq787 eq15 -- superposition 15,787
  subsumption eq1200 rfl

theorem Equation47_4291_4512_implies_Equation3 (G : Type*) [Magma G]
    (h47 : Equation47 G) (h4291 : Equation4291 G) (h4512 : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h47 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq15 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq11 eq12 -- superposition 12,11
  have eq55 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq13 eq15 -- superposition 15,13
  have eq65 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq13 eq55 -- forward demodulation 55,13
  have eq66 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq65 -- forward demodulation 65,11
  have eq109 : sK0 ≠ sK0 := superpose eq66 eq14 -- superposition 14,66
  subsumption eq109 rfl

theorem Equation47_4293_4512_implies_Equation3 (G : Type*) [Magma G]
    (h47 : Equation47 G) (h4293 : Equation4293 G) (h4512 : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h47 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4293 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq12 eq13 -- superposition 13,12
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq30 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq13 eq29 -- forward demodulation 29,13
  have eq31 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq56 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq12 eq30 -- superposition 30,12
  have eq120 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) := superpose eq31 eq11 -- superposition 11,31
  have eq240 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) := superpose eq13 eq120 -- forward demodulation 120,13
  have eq241 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq13 eq240 -- forward demodulation 240,13
  have eq242 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq13 eq241 -- forward demodulation 241,13
  have eq267 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq56 -- superposition 56,11
  have eq270 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) := superpose eq56 eq56 -- superposition 56,56
  have eq277 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq31 eq56 -- superposition 56,31
  have eq321 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq13 eq267 -- forward demodulation 267,13
  have eq330 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq13 eq270 -- forward demodulation 270,13
  have eq331 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq13 eq330 -- forward demodulation 330,13
  have eq332 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq56 eq331 -- forward demodulation 331,56
  have eq333 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq13 eq332 -- forward demodulation 332,13
  have eq334 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq13 eq333 -- forward demodulation 333,13
  have eq341 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq277 eq334 -- backward demodulation 334,277
  have eq343 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq341 eq242 -- backward demodulation 242,341
  have eq345 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq343 eq321 -- backward demodulation 321,343
  have eq347 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq345 eq11 -- backward demodulation 11,345
  have eq348 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq347 eq345 -- backward demodulation 345,347
  have eq637 : sK0 ≠ sK0 := superpose eq348 eq14 -- superposition 14,348
  subsumption eq637 rfl

theorem Equation47_4314_4512_implies_Equation3 (G : Type*) [Magma G]
    (h47 : Equation47 G) (h4314 : Equation4314 G) (h4512 : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h47 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4314 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq15 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq11 eq12 -- superposition 12,11
  have eq18 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq13 eq18 -- forward demodulation 18,13
  have eq20 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq19 -- forward demodulation 19,11
  have eq60 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq13 eq20 -- superposition 20,13
  have eq67 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq13 eq60 -- forward demodulation 60,13
  have eq68 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq67 -- forward demodulation 67,11
  have eq122 : sK0 ≠ sK0 := superpose eq68 eq14 -- superposition 14,68
  subsumption eq122 rfl

theorem Equation47_4321_4512_implies_Equation3 (G : Type*) [Magma G]
    (h47 : Equation47 G) (h4321 : Equation4321 G) (h4512 : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h47 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4321 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq15 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq11 eq12 -- superposition 12,11
  have eq21 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq22 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq13 eq21 -- forward demodulation 21,13
  have eq23 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq22 -- forward demodulation 22,11
  have eq57 : sK0 ≠ sK0 := superpose eq23 eq14 -- superposition 14,23
  subsumption eq57 rfl

theorem Equation47_4343_4512_implies_Equation3 (G : Type*) [Magma G]
    (h47 : Equation47 G) (h4343 : Equation4343 G) (h4512 : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h47 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4343 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq12 eq13 -- superposition 13,12
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq30 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq13 eq29 -- forward demodulation 29,13
  have eq31 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq96 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq31 -- superposition 31,11
  have eq103 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq11 eq31 -- superposition 31,11
  have eq256 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq103 eq103 -- superposition 103,103
  have eq280 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq13 eq256 -- forward demodulation 256,13
  have eq281 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq13 eq280 -- forward demodulation 280,13
  have eq282 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq13 eq281 -- forward demodulation 281,13
  have eq283 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq30 eq282 -- forward demodulation 282,30
  have eq284 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq96 eq283 -- forward demodulation 283,96
  have eq285 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq13 eq284 -- forward demodulation 284,13
  have eq286 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := superpose eq11 eq285 -- forward demodulation 285,11
  have eq290 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq286 eq11 -- backward demodulation 11,286
  have eq291 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ X1) := superpose eq286 eq12 -- backward demodulation 12,286
  have eq540 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq290 eq291 -- superposition 291,290
  have eq569 : sK0 ≠ sK0 := superpose eq540 eq14 -- superposition 14,540
  subsumption eq569 rfl

theorem Equation56_75_4512_implies_Equation4276 (G : Type*) [Magma G]
    (h56 : Equation56 G) (h75 : Equation75 G) (_ : Equation4512 G) : Equation4276 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h56 ..)
  have eq14 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h75 ..)
  have eq16 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq19 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq59 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq19 eq16 -- superposition 16,19
  subsumption eq59 eq19

theorem Equation56_4283_4512_implies_Equation4358 (G : Type*) [Magma G]
    (h56 : Equation56 G) (h4283 : Equation4283 G) (h4512 : Equation4512 G) : Equation4358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h56 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq25 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) := superpose eq15 eq25 -- forward demodulation 25,15
  have eq40 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq15 eq39 -- forward demodulation 39,15
  have eq84 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq14 eq40 -- superposition 40,14
  have eq100 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq40 eq84 -- forward demodulation 84,40
  have eq162 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq100 eq16 -- superposition 16,100
  subsumption eq162 rfl

theorem Equation56_4320_4512_implies_Equation43 (G : Type*) [Magma G]
    (h56 : Equation56 G) (h4320 : Equation4320 G) (h4512 : Equation4512 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h56 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK1 ◇ sK0) ≠ (sK0 ◇ sK1) := mod_symm nh
  have eq19 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) = ((X1 ◇ (X1 ◇ X1)) ◇ X0) := superpose eq13 eq14 -- superposition 14,13
  have eq27 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) = (X1 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq15 eq19 -- forward demodulation 19,15
  have eq28 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq15 eq27 -- forward demodulation 27,15
  have eq29 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq28 -- forward demodulation 28,13
  have eq30 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq13 eq29 -- forward demodulation 29,13
  have eq51 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq14 eq15 -- superposition 15,14
  have eq66 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq51 -- forward demodulation 51,15
  have eq72 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose eq13 eq30 -- superposition 30,13
  have eq73 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq14 eq30 -- superposition 30,14
  have eq152 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq14 eq72 -- superposition 72,14
  have eq183 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq15 eq152 -- forward demodulation 152,15
  have eq184 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose eq13 eq183 -- forward demodulation 183,13
  have eq1550 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X1) ◇ X1)) = (X0 ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq184 eq66 -- superposition 66,184
  have eq1703 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq15 eq1550 -- forward demodulation 1550,15
  have eq1704 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq13 eq1703 -- forward demodulation 1703,13
  have eq1705 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq1704 eq73 -- backward demodulation 73,1704
  have eq2238 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq1705 eq16 -- superposition 16,1705
  subsumption eq2238 rfl

theorem Equation75_4283_4512_implies_Equation43 (G : Type*) [Magma G]
    (h75 : Equation75 G) (h4283 : Equation4283 G) (_ : Equation4512 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h75 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq16 : (sK1 ◇ sK0) ≠ (sK0 ◇ sK1) := mod_symm nh
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq14 eq13 -- superposition 13,14
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq13 eq19 -- forward demodulation 19,13
  have eq58 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq16 -- superposition 16,20
  subsumption eq58 rfl

theorem Equation75_4320_4512_implies_Equation4362 (G : Type*) [Magma G]
    (h75 : Equation75 G) (h4320 : Equation4320 G) (h4512 : Equation4512 G) : Equation4362 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h75 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq22 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq14 eq13 -- superposition 13,14
  have eq36 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq37 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq39 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)))) = X2 := superpose eq13 eq15 -- superposition 15,13
  have eq42 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq14 -- superposition 14,15
  have eq51 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq15 eq36 -- forward demodulation 36,15
  have eq52 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq37 -- forward demodulation 37,15
  have eq55 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))) = X2 := superpose eq15 eq39 -- forward demodulation 39,15
  have eq56 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) = X2 := superpose eq15 eq55 -- forward demodulation 55,15
  have eq101 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq14 eq22 -- superposition 22,14
  have eq124 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))))) := superpose eq15 eq101 -- forward demodulation 101,15
  have eq125 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq13 eq124 -- forward demodulation 124,13
  have eq126 (X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq13 eq125 -- forward demodulation 125,13
  have eq152 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq126 eq15 -- superposition 15,126
  have eq159 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq152 -- forward demodulation 152,15
  have eq464 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := superpose eq13 eq159 -- superposition 159,13
  have eq827 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq42 eq464 -- superposition 464,42
  have eq881 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq14 eq827 -- forward demodulation 827,14
  have eq882 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq15 eq881 -- forward demodulation 881,15
  have eq883 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq13 eq882 -- forward demodulation 882,13
  have eq1424 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2))) = (((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X1)) ◇ X2) := superpose eq22 eq52 -- superposition 52,22
  have eq1527 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2))) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq15 eq1424 -- forward demodulation 1424,15
  have eq1528 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2))) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X2))) := superpose eq15 eq1527 -- forward demodulation 1527,15
  have eq1529 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)))) := superpose eq15 eq1528 -- forward demodulation 1528,15
  have eq1530 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))))) := superpose eq15 eq1529 -- forward demodulation 1529,15
  have eq1531 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))))) := superpose eq15 eq1530 -- forward demodulation 1530,15
  have eq1532 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2))) := superpose eq13 eq1531 -- forward demodulation 1531,13
  have eq1533 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)))) := superpose eq15 eq1532 -- forward demodulation 1532,15
  have eq1534 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2))))) := superpose eq15 eq1533 -- forward demodulation 1533,15
  have eq1535 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)))))) := superpose eq15 eq1534 -- forward demodulation 1534,15
  have eq1536 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))))))) := superpose eq15 eq1535 -- forward demodulation 1535,15
  have eq1537 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))))))) := superpose eq15 eq1536 -- forward demodulation 1536,15
  have eq1538 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq56 eq1537 -- forward demodulation 1537,56
  have eq1539 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq15 eq1538 -- forward demodulation 1538,15
  have eq2575 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2) = (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X2))) := superpose eq883 eq51 -- superposition 51,883
  have eq2682 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2))) := superpose eq1539 eq2575 -- forward demodulation 2575,1539
  have eq2683 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2)))) := superpose eq15 eq2682 -- forward demodulation 2682,15
  have eq2684 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq15 eq2683 -- forward demodulation 2683,15
  have eq2685 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2) := superpose eq13 eq2684 -- forward demodulation 2684,13
  have eq2686 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X2) := superpose eq14 eq2685 -- forward demodulation 2685,14
  have eq2687 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) := superpose eq15 eq2686 -- forward demodulation 2686,15
  have eq2688 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X0) ◇ X2) := superpose eq13 eq2687 -- forward demodulation 2687,13
  have eq3232 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq15 eq2688 -- superposition 2688,15
  have eq4330 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq3232 eq16 -- superposition 16,3232
  subsumption eq4330 rfl

theorem Equation307_3256_4512_implies_Equation308 (G : Type*) [Magma G]
    (h307 : Equation307 G) (h3256 : Equation3256 G) (h4512 : Equation4512 G) : Equation308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h307 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h3256 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq18 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq12 eq14 -- superposition 14,12
  have eq19 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq14 -- superposition 14,13
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq14 eq13 -- superposition 13,14
  have eq28 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq14 eq18 -- forward demodulation 18,14
  have eq29 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq14 eq19 -- forward demodulation 19,14
  have eq30 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := superpose eq14 eq29 -- forward demodulation 29,14
  have eq31 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq14 eq30 -- forward demodulation 30,14
  have eq64 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq28 eq23 -- superposition 23,28
  have eq90 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))))))) := superpose eq14 eq64 -- forward demodulation 64,14
  have eq91 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))))))) := superpose eq14 eq90 -- forward demodulation 90,14
  have eq92 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))))) := superpose eq28 eq91 -- forward demodulation 91,28
  have eq171 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq28 eq31 -- superposition 31,28
  have eq209 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq31 eq171 -- forward demodulation 171,31
  have eq210 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq31 eq209 -- forward demodulation 209,31
  have eq211 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq210 eq92 -- backward demodulation 92,210
  have eq212 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq31 eq211 -- forward demodulation 211,31
  have eq213 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq212 eq31 -- backward demodulation 31,212
  have eq260 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq213 eq15 -- superposition 15,213
  subsumption eq260 rfl

theorem Equation307_3261_4512_implies_Equation3258 (G : Type*) [Magma G]
    (h307 : Equation307 G) (h3261 : Equation3261 G) (h4512 : Equation4512 G) : Equation3258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h307 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h3261 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq21 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq14 -- superposition 14,13
  have eq23 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq12 eq14 -- superposition 14,12
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq13 eq14 -- superposition 14,13
  have eq27 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq14 eq13 -- superposition 13,14
  have eq31 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq14 eq21 -- forward demodulation 21,14
  have eq32 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq14 eq31 -- forward demodulation 31,14
  have eq33 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq14 eq32 -- forward demodulation 32,14
  have eq36 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq14 eq23 -- forward demodulation 23,14
  have eq37 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq14 eq24 -- forward demodulation 24,14
  have eq39 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq14 eq27 -- forward demodulation 27,14
  have eq74 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq33 -- superposition 33,13
  have eq89 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq12 eq74 -- forward demodulation 74,12
  have eq193 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq89 eq39 -- superposition 39,89
  have eq241 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq37 eq193 -- forward demodulation 193,37
  have eq242 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ X1)) := superpose eq241 eq36 -- backward demodulation 36,241
  have eq251 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq242 eq241 -- backward demodulation 241,242
  have eq683 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq251 eq15 -- superposition 15,251
  subsumption eq683 rfl

theorem Equation307_3261_4512_implies_Equation4284 (G : Type*) [Magma G]
    (h307 : Equation307 G) (h3261 : Equation3261 G) (h4512 : Equation4512 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h307 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h3261 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq15 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq20 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq12 eq14 -- superposition 14,12
  have eq21 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq14 -- superposition 14,13
  have eq30 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq14 eq20 -- forward demodulation 20,14
  have eq31 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq14 eq21 -- forward demodulation 21,14
  have eq32 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq14 eq31 -- forward demodulation 31,14
  have eq33 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq14 eq32 -- forward demodulation 32,14
  have eq74 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq33 -- superposition 33,13
  have eq89 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq12 eq74 -- forward demodulation 74,12
  have eq115 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq30 eq89 -- superposition 89,30
  have eq318 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq115 eq15 -- superposition 15,115
  subsumption eq318 rfl

theorem Equation307_3278_4512_implies_Equation312 (G : Type*) [Magma G]
    (h307 : Equation307 G) (h3278 : Equation3278 G) (h4512 : Equation4512 G) : Equation312 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h307 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3278 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq15 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq19 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq12 eq14 -- superposition 14,12
  have eq29 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq14 eq19 -- forward demodulation 19,14
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq13 eq29 -- superposition 29,13
  have eq62 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq13 eq49 -- forward demodulation 49,13
  have eq87 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq62 eq15 -- superposition 15,62
  subsumption eq87 rfl

theorem Equation307_3306_4512_implies_Equation323 (G : Type*) [Magma G]
    (h307 : Equation307 G) (h3306 : Equation3306 G) (h4512 : Equation4512 G) : Equation323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h307 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := mod_symm (h3306 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq19 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq12 eq14 -- superposition 14,12
  have eq29 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq14 eq19 -- forward demodulation 19,14
  have eq30 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq13 eq29 -- forward demodulation 29,13
  have eq51 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq30 eq15 -- superposition 15,30
  subsumption eq51 rfl

theorem Equation307_3315_4512_implies_Equation325 (G : Type*) [Magma G]
    (h307 : Equation307 G) (h3315 : Equation3315 G) (h4512 : Equation4512 G) : Equation325 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h307 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3315 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq29 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq14 eq13 -- superposition 13,14
  have eq77 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ X0)) := superpose eq12 eq29 -- superposition 29,12
  have eq95 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq13 eq77 -- forward demodulation 77,13
  have eq221 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq95 eq15 -- superposition 15,95
  subsumption eq221 rfl

theorem Equation307_3319_4512_implies_Equation326 (G : Type*) [Magma G]
    (h307 : Equation307 G) (h3319 : Equation3319 G) (_ : Equation4512 G) : Equation326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h307 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := mod_symm (h3319 ..)
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq15 eq16

theorem Equation307_3353_4512_implies_Equation333 (G : Type*) [Magma G]
    (h307 : Equation307 G) (h3353 : Equation3353 G) (h4512 : Equation4512 G) : Equation333 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h307 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3353 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq15 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq23 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq12 eq14 -- superposition 14,12
  have eq33 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq14 eq23 -- forward demodulation 23,14
  have eq54 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq13 eq33 -- superposition 33,13
  have eq68 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq13 eq54 -- forward demodulation 54,13
  have eq95 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq68 eq15 -- superposition 15,68
  subsumption eq95 rfl

theorem Equation307_4268_4512_implies_Equation308 (G : Type*) [Magma G]
    (h307 : Equation307 G) (h4268 : Equation4268 G) (_ : Equation4512 G) : Equation308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h307 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4268 ..)
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq15 eq16

theorem Equation307_4269_4512_implies_Equation309 (G : Type*) [Magma G]
    (h307 : Equation307 G) (h4269 : Equation4269 G) (_ : Equation4512 G) : Equation309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h307 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4269 ..)
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq15 eq16

theorem Equation307_4272_4512_implies_Equation312 (G : Type*) [Magma G]
    (h307 : Equation307 G) (h4272 : Equation4272 G) (_ : Equation4512 G) : Equation312 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h307 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4272 ..)
  have eq15 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq15 eq16

theorem Equation307_4283_4343_4512_implies_Equation4284 (G : Type*) [Magma G]
    (h307 : Equation307 G) (h4283 : Equation4283 G) (h4343 : Equation4343 G) (h4512 : Equation4512 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq14 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h307 ..)
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq16 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4343 ..)
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq18 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq20 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq16 eq15 -- superposition 15,16
  have eq24 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq17 eq20 -- forward demodulation 20,17
  have eq27 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq14 eq17 -- superposition 17,14
  have eq36 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq16 eq17 -- superposition 17,16
  have eq46 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq17 eq15 -- superposition 15,17
  have eq48 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq17 eq27 -- forward demodulation 27,17
  have eq60 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq17 eq36 -- forward demodulation 36,17
  have eq135 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq15 eq24 -- superposition 24,15
  have eq187 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq46 -- superposition 46,15
  have eq212 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq15 eq46 -- superposition 46,15
  have eq269 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq48 eq187 -- forward demodulation 187,48
  have eq272 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq269 eq135 -- backward demodulation 135,269
  have eq294 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq272 eq60 -- backward demodulation 60,272
  have eq367 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ X0)) := superpose eq272 eq212 -- forward demodulation 212,272
  have eq3196 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq367 eq294 -- superposition 294,367
  have eq3364 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := superpose eq14 eq3196 -- forward demodulation 3196,14
  have eq3783 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq16 eq3364 -- superposition 3364,16
  have eq5669 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq3783 eq18 -- superposition 18,3783
  subsumption eq5669 rfl

theorem Equation307_4284_4321_4512_implies_Equation4293 (G : Type*) [Magma G]
    (h307 : Equation307 G) (h4284 : Equation4284 G) (h4321 : Equation4321 G) (h4512 : Equation4512 G) : Equation4293 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq14 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h307 ..)
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq16 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4321 ..)
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq18 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq19 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq15 eq15 -- superposition 15,15
  have eq20 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq15 eq18 -- superposition 18,15
  have eq21 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq17 eq19 -- forward demodulation 19,17
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq14 eq21 -- forward demodulation 21,14
  have eq23 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq14 eq22 -- forward demodulation 22,14
  have eq25 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq15 eq16 -- superposition 16,15
  have eq35 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq17 eq25 -- forward demodulation 25,17
  have eq44 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq14 eq17 -- superposition 17,14
  have eq47 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq16 eq17 -- superposition 17,16
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq17 eq14 -- superposition 14,17
  have eq65 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq17 eq44 -- forward demodulation 44,17
  have eq68 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq17 eq47 -- forward demodulation 47,17
  have eq88 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq15 eq23 -- superposition 23,15
  have eq91 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq16 eq23 -- superposition 23,16
  have eq95 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq15 eq23 -- superposition 23,15
  have eq111 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq65 eq88 -- forward demodulation 88,65
  have eq112 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq17 eq111 -- forward demodulation 111,17
  have eq122 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq112 eq91 -- forward demodulation 91,112
  have eq123 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq17 eq122 -- forward demodulation 122,17
  have eq127 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq95 eq123 -- backward demodulation 123,95
  have eq128 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq95 eq112 -- backward demodulation 112,95
  have eq166 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq16 eq65 -- superposition 65,16
  have eq182 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq128 eq166 -- forward demodulation 166,128
  have eq184 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq182 eq127 -- backward demodulation 127,182
  have eq186 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq182 eq56 -- backward demodulation 56,182
  have eq217 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2)))) := superpose eq17 eq95 -- superposition 95,17
  have eq231 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := superpose eq17 eq217 -- forward demodulation 217,17
  have eq590 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq182 eq182 -- superposition 182,182
  have eq655 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq17 eq590 -- forward demodulation 590,17
  have eq656 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq17 eq655 -- forward demodulation 655,17
  have eq657 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) := superpose eq15 eq656 -- forward demodulation 656,15
  have eq658 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq231 eq657 -- forward demodulation 657,231
  have eq659 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq182 eq658 -- forward demodulation 658,182
  have eq660 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq95 eq659 -- forward demodulation 659,95
  have eq1129 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq23 eq184 -- superposition 184,23
  have eq1198 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq65 eq1129 -- forward demodulation 1129,65
  have eq1202 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq1198 eq660 -- backward demodulation 660,1198
  have eq1420 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq15 eq68 -- superposition 68,15
  have eq1421 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq16 eq68 -- superposition 68,16
  have eq1762 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq1202 eq1420 -- forward demodulation 1420,1202
  have eq1763 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq1762 eq1421 -- forward demodulation 1421,1762
  have eq1764 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq1763 eq35 -- backward demodulation 35,1763
  have eq4459 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := superpose eq186 eq1764 -- superposition 1764,186
  have eq4947 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq4459 eq20 -- superposition 20,4459
  subsumption eq4947 eq15

theorem Equation307_4290_4291_4512_implies_Equation4283 (G : Type*) [Magma G]
    (h307 : Equation307 G) (h4290 : Equation4290 G) (h4291 : Equation4291 G) (h4512 : Equation4512 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq14 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h307 ..)
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq16 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq18 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq20 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq15 eq15 -- superposition 15,15
  have eq22 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq14 eq20 -- forward demodulation 20,14
  have eq23 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq14 eq22 -- forward demodulation 22,14
  have eq24 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq17 eq23 -- forward demodulation 23,17
  have eq26 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose eq15 eq16 -- superposition 16,15
  have eq29 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq16 -- superposition 16,15
  have eq30 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq15 eq16 -- superposition 16,15
  have eq34 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq24 eq30 -- forward demodulation 30,24
  have eq37 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq14 eq17 -- superposition 17,14
  have eq43 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq14 eq17 -- superposition 17,14
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq17 eq14 -- superposition 14,17
  have eq57 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq17 eq37 -- forward demodulation 37,17
  have eq64 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq26 eq43 -- forward demodulation 43,26
  have eq65 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq17 eq64 -- forward demodulation 64,17
  have eq66 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq17 eq65 -- forward demodulation 65,17
  have eq98 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq26 eq16 -- superposition 16,26
  have eq131 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq16 eq34 -- superposition 34,16
  have eq142 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq34 -- superposition 34,15
  have eq150 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq131 -- forward demodulation 131,15
  have eq151 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq57 eq150 -- forward demodulation 150,57
  have eq152 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq151 eq49 -- backward demodulation 49,151
  have eq154 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq152 eq66 -- backward demodulation 66,152
  have eq176 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq142 eq98 -- backward demodulation 98,142
  have eq178 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq176 eq29 -- backward demodulation 29,176
  have eq180 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq178 eq154 -- backward demodulation 154,178
  have eq1022 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq180 eq142 -- superposition 142,180
  have eq1551 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose eq26 eq1022 -- superposition 1022,26
  have eq4855 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq1551 eq18 -- superposition 18,1551
  subsumption eq4855 rfl

theorem Equation307_4290_4321_4512_implies_Equation4284 (G : Type*) [Magma G]
    (h307 : Equation307 G) (h4290 : Equation4290 G) (h4321 : Equation4321 G) (h4512 : Equation4512 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq14 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h307 ..)
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq16 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4321 ..)
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq18 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq20 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq15 eq15 -- superposition 15,15
  have eq22 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq14 eq20 -- forward demodulation 20,14
  have eq23 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq14 eq22 -- forward demodulation 22,14
  have eq24 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq17 eq23 -- forward demodulation 23,17
  have eq27 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq16 -- superposition 16,15
  have eq28 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq15 eq16 -- superposition 16,15
  have eq29 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq16 eq16 -- superposition 16,16
  have eq37 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq17 eq27 -- forward demodulation 27,17
  have eq38 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq17 eq28 -- forward demodulation 28,17
  have eq39 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq24 eq38 -- forward demodulation 38,24
  have eq41 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq17 eq29 -- forward demodulation 29,17
  have eq49 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq14 eq17 -- superposition 17,14
  have eq55 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq14 eq17 -- superposition 17,14
  have eq70 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq17 eq49 -- forward demodulation 49,17
  have eq77 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq17 eq55 -- forward demodulation 55,17
  have eq90 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq15 eq39 -- superposition 39,15
  have eq94 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq39 eq39 -- superposition 39,39
  have eq97 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq39 -- superposition 39,15
  have eq102 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq39 eq16 -- superposition 16,39
  have eq107 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq15 eq90 -- forward demodulation 90,15
  have eq108 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq70 eq107 -- forward demodulation 107,70
  have eq113 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq15 eq94 -- forward demodulation 94,15
  have eq114 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq39 eq113 -- forward demodulation 113,39
  have eq117 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq97 eq114 -- backward demodulation 114,97
  have eq127 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq117 eq102 -- forward demodulation 102,117
  have eq128 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq17 eq127 -- forward demodulation 127,17
  have eq129 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq17 eq128 -- forward demodulation 128,17
  have eq130 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq97 eq129 -- forward demodulation 129,97
  have eq189 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq16 eq70 -- superposition 70,16
  have eq195 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq70 -- superposition 70,15
  have eq204 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq70 eq16 -- superposition 16,70
  have eq214 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq195 eq108 -- backward demodulation 108,195
  have eq215 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq195 eq41 -- backward demodulation 41,195
  have eq216 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq214 eq37 -- backward demodulation 37,214
  have eq229 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq17 eq204 -- forward demodulation 204,17
  have eq230 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq216 eq229 -- forward demodulation 229,216
  have eq231 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq70 eq230 -- forward demodulation 230,70
  have eq240 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq70 eq216 -- superposition 216,70
  have eq268 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq14 eq240 -- forward demodulation 240,14
  have eq269 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq17 eq268 -- forward demodulation 268,17
  have eq270 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq215 eq269 -- forward demodulation 269,215
  have eq271 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq17 eq270 -- forward demodulation 270,17
  have eq272 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq231 eq271 -- forward demodulation 271,231
  have eq273 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq272 eq189 -- backward demodulation 189,272
  have eq275 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq273 eq77 -- backward demodulation 77,273
  have eq284 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq39 eq275 -- forward demodulation 275,39
  have eq1030 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq284 eq130 -- superposition 130,284
  have eq1730 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq1030 eq18 -- superposition 18,1030
  subsumption eq1730 rfl

theorem Equation307_4291_4343_4512_implies_Equation4283 (G : Type*) [Magma G]
    (h307 : Equation307 G) (h4291 : Equation4291 G) (h4343 : Equation4343 G) (h4512 : Equation4512 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq14 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h307 ..)
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq16 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4343 ..)
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq18 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq23 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq16 eq15 -- superposition 15,16
  have eq25 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq14 eq17 -- superposition 17,14
  have eq26 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq15 eq17 -- superposition 17,15
  have eq27 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq15 eq17 -- superposition 17,15
  have eq31 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq14 eq17 -- superposition 17,14
  have eq32 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq15 eq17 -- superposition 17,15
  have eq34 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq16 eq17 -- superposition 17,16
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq17 eq16 -- superposition 16,17
  have eq45 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq17 eq25 -- forward demodulation 25,17
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq17 eq26 -- forward demodulation 26,17
  have eq47 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq17 eq27 -- forward demodulation 27,17
  have eq52 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq16 eq31 -- forward demodulation 31,16
  have eq53 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq17 eq52 -- forward demodulation 52,17
  have eq54 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq14 eq53 -- forward demodulation 53,14
  have eq55 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq17 eq32 -- forward demodulation 32,17
  have eq56 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq17 eq34 -- forward demodulation 34,17
  have eq86 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq15 eq45 -- superposition 45,15
  have eq91 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq45 eq15 -- superposition 15,45
  have eq97 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq86 eq36 -- backward demodulation 36,86
  have eq98 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq86 eq56 -- backward demodulation 56,86
  have eq109 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq45 eq91 -- forward demodulation 91,45
  have eq156 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := superpose eq14 eq46 -- superposition 46,14
  have eq175 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := superpose eq46 eq14 -- superposition 14,46
  have eq263 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) := superpose eq17 eq156 -- forward demodulation 156,17
  have eq264 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) := superpose eq17 eq263 -- forward demodulation 263,17
  have eq265 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) := superpose eq86 eq264 -- forward demodulation 264,86
  have eq318 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) := superpose eq17 eq175 -- forward demodulation 175,17
  have eq319 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq265 eq318 -- forward demodulation 318,265
  have eq320 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq319 eq54 -- backward demodulation 54,319
  have eq430 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq14 eq47 -- superposition 47,14
  have eq532 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq98 eq430 -- forward demodulation 430,98
  have eq533 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq17 eq532 -- forward demodulation 532,17
  have eq534 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) := superpose eq97 eq533 -- forward demodulation 533,97
  have eq535 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) := superpose eq17 eq534 -- forward demodulation 534,17
  have eq536 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq17 eq535 -- forward demodulation 535,17
  have eq537 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq55 eq536 -- forward demodulation 536,55
  have eq538 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq55 eq537 -- forward demodulation 537,55
  have eq539 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq109 eq538 -- forward demodulation 538,109
  have eq543 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq539 eq23 -- backward demodulation 23,539
  have eq2615 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq320 eq98 -- superposition 98,320
  have eq2797 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := superpose eq14 eq2615 -- forward demodulation 2615,14
  have eq3552 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq98 eq543 -- superposition 543,98
  have eq3753 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq17 eq3552 -- forward demodulation 3552,17
  have eq3754 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq45 eq3753 -- forward demodulation 3753,45
  have eq3755 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq14 eq3754 -- forward demodulation 3754,14
  have eq4697 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose eq2797 eq3755 -- superposition 3755,2797
  have eq8138 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq4697 eq18 -- superposition 18,4697
  subsumption eq8138 rfl

theorem Equation307_4293_4314_4512_implies_Equation4283 (G : Type*) [Magma G]
    (h307 : Equation307 G) (h4293 : Equation4293 G) (h4314 : Equation4314 G) (h4512 : Equation4512 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq14 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h307 ..)
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4293 ..)
  have eq16 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4314 ..)
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq18 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq28 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq14 eq17 -- superposition 17,14
  have eq29 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq15 eq17 -- superposition 17,15
  have eq31 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq16 eq17 -- superposition 17,16
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq16 eq17 -- superposition 17,16
  have eq38 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq16 eq17 -- superposition 17,16
  have eq39 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq17 eq16 -- superposition 16,17
  have eq49 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq17 eq28 -- forward demodulation 28,17
  have eq50 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq17 eq29 -- forward demodulation 29,17
  have eq52 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq17 eq31 -- forward demodulation 31,17
  have eq53 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq17 eq32 -- forward demodulation 32,17
  have eq61 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq17 eq39 -- forward demodulation 39,17
  have eq76 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq15 eq49 -- superposition 49,15
  have eq103 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq14 eq76 -- superposition 76,14
  have eq106 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq49 eq76 -- superposition 76,49
  have eq120 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq76 eq17 -- superposition 17,76
  have eq123 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq14 eq103 -- forward demodulation 103,14
  have eq126 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq49 eq106 -- forward demodulation 106,49
  have eq132 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq17 eq120 -- forward demodulation 120,17
  have eq133 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq17 eq132 -- forward demodulation 132,17
  have eq144 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq14 eq50 -- superposition 50,14
  have eq145 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq15 eq50 -- superposition 50,15
  have eq149 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) = (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq16 eq50 -- superposition 50,16
  have eq186 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq50 eq15 -- superposition 15,50
  have eq190 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq50 eq49 -- superposition 49,50
  have eq228 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)))) := superpose eq38 eq144 -- forward demodulation 144,38
  have eq229 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))))) := superpose eq17 eq228 -- forward demodulation 228,17
  have eq230 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))))) := superpose eq17 eq229 -- forward demodulation 229,17
  have eq231 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))))) := superpose eq17 eq230 -- forward demodulation 230,17
  have eq232 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) := superpose eq49 eq231 -- forward demodulation 231,49
  have eq233 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq133 eq232 -- forward demodulation 232,133
  have eq234 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq133 eq233 -- forward demodulation 233,133
  have eq235 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq126 eq234 -- forward demodulation 234,126
  have eq236 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq76 eq235 -- forward demodulation 235,76
  have eq237 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) := superpose eq17 eq145 -- forward demodulation 145,17
  have eq238 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))))) := superpose eq17 eq237 -- forward demodulation 237,17
  have eq239 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq49 eq238 -- forward demodulation 238,49
  have eq240 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq133 eq239 -- forward demodulation 239,133
  have eq241 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq133 eq240 -- forward demodulation 240,133
  have eq365 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq241 eq186 -- forward demodulation 186,241
  have eq371 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq241 eq190 -- forward demodulation 190,241
  have eq372 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq17 eq371 -- forward demodulation 371,17
  have eq373 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq365 eq372 -- forward demodulation 372,365
  have eq374 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq373 eq149 -- backward demodulation 149,373
  have eq473 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq16 eq52 -- superposition 52,16
  have eq480 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := superpose eq16 eq52 -- superposition 52,16
  have eq638 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) := superpose eq17 eq480 -- forward demodulation 480,17
  have eq898 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq123 eq53 -- superposition 53,123
  have eq1120 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) := superpose eq17 eq898 -- forward demodulation 898,17
  have eq1121 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq76 eq1120 -- forward demodulation 1120,76
  have eq1122 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq374 eq1121 -- forward demodulation 1121,374
  have eq1123 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq17 eq1122 -- forward demodulation 1122,17
  have eq1124 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq49 eq1123 -- forward demodulation 1123,49
  have eq1125 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ X0)) := superpose eq14 eq1124 -- forward demodulation 1124,14
  have eq1129 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq1125 eq638 -- backward demodulation 638,1125
  have eq1133 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq1129 eq473 -- backward demodulation 473,1129
  have eq1136 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq1133 eq61 -- backward demodulation 61,1133
  have eq2190 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq236 eq1136 -- superposition 1136,236
  have eq2360 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq14 eq2190 -- forward demodulation 2190,14
  have eq2565 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose eq16 eq2360 -- superposition 2360,16
  have eq4196 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq2565 eq18 -- superposition 18,2565
  subsumption eq4196 rfl

theorem Equation307_4293_4320_4512_implies_Equation4283 (G : Type*) [Magma G]
    (h307 : Equation307 G) (h4293 : Equation4293 G) (h4320 : Equation4320 G) (h4512 : Equation4512 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq14 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h307 ..)
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4293 ..)
  have eq16 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq18 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq23 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq16 eq16 -- superposition 16,16
  have eq26 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq16 eq15 -- superposition 15,16
  have eq35 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) := superpose eq16 eq23 -- forward demodulation 23,16
  have eq36 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq17 eq35 -- forward demodulation 35,17
  have eq37 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq14 eq36 -- forward demodulation 36,14
  have eq38 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq14 eq37 -- forward demodulation 37,14
  have eq44 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq17 eq26 -- forward demodulation 26,17
  have eq46 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq14 eq17 -- superposition 17,14
  have eq52 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq14 eq17 -- superposition 17,14
  have eq53 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq15 eq17 -- superposition 17,15
  have eq55 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq16 eq17 -- superposition 17,16
  have eq56 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq16 eq17 -- superposition 17,16
  have eq64 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq17 eq16 -- superposition 16,17
  have eq67 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq17 eq46 -- forward demodulation 46,17
  have eq74 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq17 eq52 -- forward demodulation 52,17
  have eq75 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq17 eq53 -- forward demodulation 53,17
  have eq76 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq75 eq74 -- backward demodulation 74,75
  have eq78 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq67 eq76 -- forward demodulation 76,67
  have eq81 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq17 eq55 -- forward demodulation 55,17
  have eq82 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq17 eq56 -- forward demodulation 56,17
  have eq94 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq16 eq67 -- superposition 67,16
  have eq98 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq15 eq67 -- superposition 67,15
  have eq109 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq98 eq78 -- backward demodulation 78,98
  have eq110 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq109 eq44 -- backward demodulation 44,109
  have eq113 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = (X2 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq109 eq81 -- backward demodulation 81,109
  have eq134 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq16 eq109 -- superposition 109,16
  have eq135 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq17 eq109 -- superposition 109,17
  have eq136 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq17 eq109 -- superposition 109,17
  have eq176 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq113 eq135 -- forward demodulation 135,113
  have eq177 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq17 eq176 -- forward demodulation 176,17
  have eq178 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq17 eq136 -- forward demodulation 136,17
  have eq179 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1)))) := superpose eq113 eq178 -- forward demodulation 178,113
  have eq180 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq179 eq177 -- backward demodulation 177,179
  have eq218 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq38 eq16 -- superposition 16,38
  have eq290 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq82 eq218 -- forward demodulation 218,82
  have eq291 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) = ((X0 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq17 eq290 -- forward demodulation 290,17
  have eq292 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) = ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq17 eq291 -- forward demodulation 291,17
  have eq293 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq109 eq292 -- forward demodulation 292,109
  have eq294 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq15 eq293 -- forward demodulation 293,15
  have eq295 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq180 eq294 -- forward demodulation 294,180
  have eq296 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq17 eq295 -- forward demodulation 295,17
  have eq297 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq17 eq296 -- forward demodulation 296,17
  have eq298 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq75 eq297 -- forward demodulation 297,75
  have eq299 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq179 eq298 -- forward demodulation 298,179
  have eq300 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq67 eq299 -- forward demodulation 299,67
  have eq301 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq300 eq94 -- backward demodulation 94,300
  have eq480 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq16 eq64 -- superposition 64,16
  have eq607 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) = ((X2 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq17 eq480 -- forward demodulation 480,17
  have eq608 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) = ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq109 eq607 -- forward demodulation 607,109
  have eq609 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq17 eq608 -- forward demodulation 608,17
  have eq610 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq67 eq609 -- forward demodulation 609,67
  have eq1356 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq64 eq301 -- superposition 301,64
  have eq1393 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq134 eq1356 -- forward demodulation 1356,134
  have eq1394 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq610 eq1393 -- forward demodulation 1393,610
  have eq1395 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq17 eq1394 -- forward demodulation 1394,17
  have eq1396 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq110 eq1395 -- forward demodulation 1395,110
  have eq1397 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := superpose eq14 eq1396 -- forward demodulation 1396,14
  have eq2020 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose eq16 eq1397 -- superposition 1397,16
  have eq3614 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq2020 eq18 -- superposition 18,2020
  subsumption eq3614 rfl

theorem Equation307_4293_4343_4512_implies_Equation4284 (G : Type*) [Magma G]
    (h307 : Equation307 G) (h4293 : Equation4293 G) (h4343 : Equation4343 G) (h4512 : Equation4512 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq14 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h307 ..)
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4293 ..)
  have eq16 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4343 ..)
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq18 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq27 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq14 eq17 -- superposition 17,14
  have eq28 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq15 eq17 -- superposition 17,15
  have eq30 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq16 eq17 -- superposition 17,16
  have eq33 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq14 eq17 -- superposition 17,14
  have eq34 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq15 eq17 -- superposition 17,15
  have eq36 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq16 eq17 -- superposition 17,16
  have eq48 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq17 eq27 -- forward demodulation 27,17
  have eq49 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq17 eq28 -- forward demodulation 28,17
  have eq51 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq17 eq30 -- forward demodulation 30,17
  have eq55 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq16 eq33 -- forward demodulation 33,16
  have eq56 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq17 eq55 -- forward demodulation 55,17
  have eq57 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq14 eq56 -- forward demodulation 56,14
  have eq58 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq17 eq34 -- forward demodulation 34,17
  have eq60 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq17 eq36 -- forward demodulation 36,17
  have eq77 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq15 eq48 -- superposition 48,15
  have eq104 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq48 eq77 -- superposition 77,48
  have eq108 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq17 eq77 -- superposition 77,17
  have eq118 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq77 eq17 -- superposition 17,77
  have eq123 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq48 eq104 -- forward demodulation 104,48
  have eq125 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq17 eq108 -- forward demodulation 108,17
  have eq128 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq17 eq118 -- forward demodulation 118,17
  have eq129 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq17 eq128 -- forward demodulation 128,17
  have eq133 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X3) := superpose eq49 eq49 -- superposition 49,49
  have eq140 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq14 eq49 -- superposition 49,14
  have eq173 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq49 eq14 -- superposition 14,49
  have eq201 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) = ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) ◇ X3) := superpose eq17 eq133 -- forward demodulation 133,17
  have eq202 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) = ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))))) ◇ X3) := superpose eq17 eq201 -- forward demodulation 201,17
  have eq203 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) = ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) ◇ X3) := superpose eq48 eq202 -- forward demodulation 202,48
  have eq204 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) = ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X3) := superpose eq129 eq203 -- forward demodulation 203,129
  have eq205 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) = ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3) := superpose eq129 eq204 -- forward demodulation 204,129
  have eq206 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3) = (X2 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X3)))) := superpose eq17 eq205 -- forward demodulation 205,17
  have eq207 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X3))))) := superpose eq17 eq206 -- forward demodulation 206,17
  have eq224 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq60 eq140 -- forward demodulation 140,60
  have eq225 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq17 eq224 -- forward demodulation 224,17
  have eq226 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) := superpose eq60 eq225 -- forward demodulation 225,60
  have eq227 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))))) := superpose eq16 eq226 -- forward demodulation 226,16
  have eq228 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) := superpose eq17 eq227 -- forward demodulation 227,17
  have eq229 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq125 eq228 -- forward demodulation 228,125
  have eq230 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq58 eq229 -- forward demodulation 229,58
  have eq231 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq129 eq230 -- forward demodulation 230,129
  have eq232 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq123 eq231 -- forward demodulation 231,123
  have eq323 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) := superpose eq207 eq173 -- forward demodulation 173,207
  have eq324 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) := superpose eq17 eq323 -- forward demodulation 323,17
  have eq325 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq17 eq324 -- forward demodulation 324,17
  have eq326 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq17 eq325 -- forward demodulation 325,17
  have eq327 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq48 eq326 -- forward demodulation 326,48
  have eq511 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2))) := superpose eq51 eq48 -- superposition 48,51
  have eq816 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2)))) := superpose eq17 eq511 -- forward demodulation 511,17
  have eq817 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2))))) := superpose eq17 eq816 -- forward demodulation 816,17
  have eq841 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq77 eq232 -- superposition 232,77
  have eq930 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq14 eq841 -- forward demodulation 841,14
  have eq931 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq17 eq930 -- forward demodulation 930,17
  have eq932 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq17 eq931 -- forward demodulation 931,17
  have eq933 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq817 eq932 -- forward demodulation 932,817
  have eq934 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq77 eq933 -- forward demodulation 933,77
  have eq935 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq17 eq934 -- forward demodulation 934,17
  have eq936 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq17 eq935 -- forward demodulation 935,17
  have eq937 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq48 eq936 -- forward demodulation 936,48
  have eq938 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq937 eq327 -- backward demodulation 327,937
  have eq939 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq938 eq57 -- backward demodulation 57,938
  have eq1057 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq17 eq939 -- superposition 939,17
  have eq1100 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq1057 eq60 -- backward demodulation 60,1057
  have eq1666 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq77 eq1100 -- superposition 1100,77
  have eq1903 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := superpose eq14 eq1666 -- forward demodulation 1666,14
  have eq2100 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq1903 eq18 -- superposition 18,1903
  subsumption eq2100 rfl

theorem Equation307_4321_4369_4512_implies_Equation4293 (G : Type*) [Magma G]
    (h307 : Equation307 G) (h4321 : Equation4321 G) (h4369 : Equation4369 G) (h4512 : Equation4512 G) : Equation4293 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq14 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h307 ..)
  have eq15 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4321 ..)
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := mod_symm (h4369 ..)
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq18 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq37 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq14 eq16 -- superposition 16,14
  have eq48 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq16 eq15 -- superposition 15,16
  have eq50 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq16 eq18 -- superposition 18,16
  have eq55 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq17 eq48 -- forward demodulation 48,17
  have eq59 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq14 eq17 -- superposition 17,14
  have eq65 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq14 eq17 -- superposition 17,14
  have eq68 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq16 eq17 -- superposition 17,16
  have eq71 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq17 eq14 -- superposition 14,17
  have eq80 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq17 eq59 -- forward demodulation 59,17
  have eq87 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq16 eq65 -- forward demodulation 65,16
  have eq90 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq68 eq71 -- forward demodulation 71,68
  have eq91 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq16 eq90 -- forward demodulation 90,16
  have eq96 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq37 eq37 -- superposition 37,37
  have eq110 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq17 eq37 -- superposition 37,17
  have eq120 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq37 eq15 -- superposition 15,37
  have eq122 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq17 eq96 -- forward demodulation 96,17
  have eq123 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq14 eq122 -- forward demodulation 122,14
  have eq155 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq55 eq120 -- forward demodulation 120,55
  have eq156 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq16 eq155 -- forward demodulation 155,16
  have eq157 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq80 eq156 -- forward demodulation 156,80
  have eq158 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq123 eq157 -- forward demodulation 157,123
  have eq166 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq80 -- superposition 80,15
  have eq168 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) := superpose eq16 eq80 -- superposition 80,16
  have eq179 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq80 eq15 -- superposition 15,80
  have eq180 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq80 eq15 -- superposition 15,80
  have eq186 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq168 eq87 -- backward demodulation 87,168
  have eq196 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq17 eq179 -- forward demodulation 179,17
  have eq197 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq158 eq196 -- forward demodulation 196,158
  have eq198 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq16 eq197 -- forward demodulation 197,16
  have eq199 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq80 eq198 -- forward demodulation 198,80
  have eq200 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq199 eq180 -- forward demodulation 180,199
  have eq201 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq17 eq200 -- forward demodulation 200,17
  have eq202 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq17 eq201 -- forward demodulation 201,17
  have eq203 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq158 eq202 -- forward demodulation 202,158
  have eq210 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq110 -- superposition 110,15
  have eq236 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq16 eq210 -- forward demodulation 210,16
  have eq237 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq158 eq236 -- forward demodulation 236,158
  have eq238 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ X0)) := superpose eq237 eq166 -- backward demodulation 166,237
  have eq241 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq238 eq91 -- backward demodulation 91,238
  have eq2554 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq68 eq238 -- superposition 238,68
  have eq2732 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq2554 eq186 -- backward demodulation 186,2554
  have eq2733 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq2554 eq241 -- backward demodulation 241,2554
  have eq2755 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ X1)) := superpose eq2732 eq2733 -- forward demodulation 2733,2732
  have eq3059 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq203 eq2755 -- superposition 2755,203
  have eq4126 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq3059 eq50 -- superposition 50,3059
  subsumption eq4126 rfl

theorem Equation308_309_4512_implies_Equation3260 (G : Type*) [Magma G]
    (h308 : Equation308 G) (h309 : Equation309 G) (h4512 : Equation4512 G) : Equation3260 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h308 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h309 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq14 eq15 -- superposition 15,14
  have eq33 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = ((X0 ◇ X0) ◇ X2) := superpose eq15 eq22 -- forward demodulation 22,15
  have eq34 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ X2)) := superpose eq15 eq33 -- forward demodulation 33,15
  have eq35 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq13 eq34 -- forward demodulation 34,13
  have eq112 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq35 eq16 -- superposition 16,35
  subsumption eq112 rfl

theorem Equation308_309_4512_implies_Equation3265 (G : Type*) [Magma G]
    (h308 : Equation308 G) (h309 : Equation309 G) (h4512 : Equation4512 G) : Equation3265 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h308 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h309 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq14 eq16 -- forward demodulation 16,14
  have eq23 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq14 eq15 -- superposition 15,14
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq14 eq15 -- superposition 15,14
  have eq27 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq14 -- superposition 14,15
  have eq34 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq15 eq23 -- forward demodulation 23,15
  have eq35 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq15 eq34 -- forward demodulation 34,15
  have eq36 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq13 eq35 -- forward demodulation 35,13
  have eq42 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq15 eq26 -- forward demodulation 26,15
  have eq43 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq36 eq42 -- forward demodulation 42,36
  have eq44 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq27 eq43 -- backward demodulation 43,27
  have eq64 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq44 eq17 -- superposition 17,44
  subsumption eq64 rfl

theorem Equation308_325_4512_implies_Equation327 (G : Type*) [Magma G]
    (h308 : Equation308 G) (h325 : Equation325 G) (h4512 : Equation4512 G) : Equation327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h308 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h325 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq18 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq21 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq15 eq18 -- forward demodulation 18,15
  have eq22 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq14 eq21 -- forward demodulation 21,14
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq22 eq15 -- superposition 15,22
  have eq65 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq15 eq57 -- forward demodulation 57,15
  have eq66 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq13 eq65 -- forward demodulation 65,13
  have eq67 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq22 eq66 -- forward demodulation 66,22
  have eq68 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := superpose eq67 eq15 -- backward demodulation 15,67
  have eq85 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq68 eq16 -- superposition 16,68
  subsumption eq85 rfl

theorem Equation308_4284_4512_implies_Equation310 (G : Type*) [Magma G]
    (h308 : Equation308 G) (h4284 : Equation4284 G) (_ : Equation4512 G) : Equation310 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h308 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq22 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq22 eq13

theorem Equation308_4369_4512_implies_Equation3260 (G : Type*) [Magma G]
    (h308 : Equation308 G) (h4369 : Equation4369 G) (h4512 : Equation4512 G) : Equation3260 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h308 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := mod_symm (h4369 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq21 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq21 eq18 -- backward demodulation 18,21
  have eq195 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq15 eq30 -- superposition 30,15
  have eq3514 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq195 eq16 -- superposition 16,195
  subsumption eq3514 rfl

theorem Equation308_4369_4512_implies_Equation3264 (G : Type*) [Magma G]
    (h308 : Equation308 G) (h4369 : Equation4369 G) (_ : Equation4512 G) : Equation3264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h308 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := mod_symm (h4369 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq17 eq13

theorem Equation308_4369_4512_implies_Equation3265 (G : Type*) [Magma G]
    (h308 : Equation308 G) (h4369 : Equation4369 G) (h4512 : Equation4512 G) : Equation3265 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h308 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := mod_symm (h4369 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq21 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq37 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq14 eq15 -- superposition 15,14
  have eq72 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq21 eq13 -- superposition 13,21
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq21 eq72 -- superposition 72,21
  have eq811 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq13 eq37 -- superposition 37,13
  have eq996 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq21 eq811 -- forward demodulation 811,21
  have eq3732 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq996 eq16 -- superposition 16,996
  subsumption eq3732 eq130

theorem Equation309_312_4512_implies_Equation3274 (G : Type*) [Magma G]
    (h309 : Equation309 G) (h312 : Equation312 G) (_ : Equation4512 G) : Equation3274 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h309 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h312 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq17 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq13 eq16 -- forward demodulation 16,13
  subsumption eq17 eq14

theorem Equation309_312_4512_implies_Equation3292 (G : Type*) [Magma G]
    (h309 : Equation309 G) (h312 : Equation312 G) (h4512 : Equation4512 G) : Equation3292 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h309 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h312 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq23 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq13 eq15 -- superposition 15,13
  have eq25 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq13 -- superposition 13,15
  have eq29 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq15 eq20 -- forward demodulation 20,15
  have eq30 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq15 eq29 -- forward demodulation 29,15
  have eq34 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq15 eq23 -- forward demodulation 23,15
  have eq35 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = (X0 ◇ (X0 ◇ X1)) := superpose eq30 eq34 -- forward demodulation 34,30
  have eq37 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose eq25 eq35 -- backward demodulation 35,25
  have eq90 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq14 eq37 -- superposition 37,14
  have eq162 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq30 eq16 -- superposition 16,30
  subsumption eq162 eq90

theorem Equation309_323_4512_implies_Equation329 (G : Type*) [Magma G]
    (h309 : Equation309 G) (h323 : Equation323 G) (h4512 : Equation4512 G) : Equation329 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h309 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h323 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq23 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq13 eq15 -- superposition 15,13
  have eq26 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq13 -- superposition 13,15
  have eq29 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq15 eq20 -- forward demodulation 20,15
  have eq30 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ X2) := superpose eq14 eq29 -- forward demodulation 29,14
  have eq31 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq15 eq30 -- forward demodulation 30,15
  have eq35 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq15 eq23 -- forward demodulation 23,15
  have eq36 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq31 eq35 -- forward demodulation 35,31
  have eq38 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq26 eq36 -- backward demodulation 36,26
  have eq111 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := superpose eq26 eq31 -- superposition 31,26
  have eq124 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ (X2 ◇ X0)) := superpose eq38 eq111 -- forward demodulation 111,38
  have eq177 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq124 eq16 -- superposition 16,124
  subsumption eq177 rfl

theorem Equation309_4315_4512_implies_Equation311 (G : Type*) [Magma G]
    (h309 : Equation309 G) (h4315 : Equation4315 G) (_ : Equation4512 G) : Equation311 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h309 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h4315 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq28 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq28 eq13

theorem Equation312_323_4512_implies_Equation343 (G : Type*) [Magma G]
    (h312 : Equation312 G) (h323 : Equation323 G) (h4512 : Equation4512 G) : Equation343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h312 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h323 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq13 eq15 -- superposition 15,13
  have eq29 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq20 -- forward demodulation 20,15
  have eq30 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := superpose eq14 eq29 -- forward demodulation 29,14
  have eq53 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq30 eq16 -- superposition 16,30
  subsumption eq53 rfl

theorem Equation312_4284_4512_implies_Equation315 (G : Type*) [Magma G]
    (h312 : Equation312 G) (h4284 : Equation4284 G) (_ : Equation4512 G) : Equation315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h312 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq22 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq22 eq13

theorem Equation312_4287_4512_implies_Equation318 (G : Type*) [Magma G]
    (h312 : Equation312 G) (h4287 : Equation4287 G) (_ : Equation4512 G) : Equation318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h312 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X1)) := mod_symm (h4287 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq26 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ X1) := superpose eq13 eq14 -- superposition 14,13
  have eq28 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq28 eq26

theorem Equation315_323_4512_implies_Equation39 (G : Type*) [Magma G]
    (h315 : Equation315 G) (h323 : Equation323 G) (_ : Equation4512 G) : Equation39 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h315 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h323 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq24 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq13 eq14 -- superposition 14,13
  have eq62 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq24 eq16 -- superposition 16,24
  subsumption eq62 rfl

theorem Equation323_326_4512_implies_Equation3309 (G : Type*) [Magma G]
    (h323 : Equation323 G) (h326 : Equation326 G) (_ : Equation4512 G) : Equation3309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h323 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h326 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq17 eq13

theorem Equation323_3255_4512_implies_Equation309 (G : Type*) [Magma G]
    (h323 : Equation323 G) (h3255 : Equation3255 G) (_ : Equation4512 G) : Equation309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h323 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h3255 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq21 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq46 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq21 eq16 -- superposition 16,21
  subsumption eq46 rfl

theorem Equation323_3258_4512_implies_Equation3326 (G : Type*) [Magma G]
    (h323 : Equation323 G) (h3258 : Equation3258 G) (h4512 : Equation4512 G) : Equation3326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h323 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3258 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq33 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq15 eq23 -- forward demodulation 23,15
  have eq34 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ X2) := superpose eq13 eq33 -- forward demodulation 33,13
  have eq35 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq15 eq34 -- forward demodulation 34,15
  have eq36 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq15 eq35 -- forward demodulation 35,15
  have eq37 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq13 eq36 -- forward demodulation 36,13
  have eq59 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq37 eq16 -- superposition 16,37
  subsumption eq59 rfl

theorem Equation323_4284_4512_implies_Equation326 (G : Type*) [Magma G]
    (h323 : Equation323 G) (h4284 : Equation4284 G) (_ : Equation4512 G) : Equation326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h323 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq13 eq14 -- forward demodulation 14,13
  subsumption eq16 eq17

theorem Equation323_4291_4512_implies_Equation333 (G : Type*) [Magma G]
    (h323 : Equation323 G) (h4291 : Equation4291 G) (_ : Equation4512 G) : Equation333 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h323 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq13 eq14 -- forward demodulation 14,13
  subsumption eq16 eq17

theorem Equation323_4293_4512_implies_Equation43 (G : Type*) [Magma G]
    (h323 : Equation323 G) (h4293 : Equation4293 G) (_ : Equation4512 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h323 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4293 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq17 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ X0) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq21 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq13 eq17 -- superposition 17,13
  have eq50 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq21 eq16 -- superposition 16,21
  subsumption eq50 rfl

theorem Equation323_4321_4512_implies_Equation4362 (G : Type*) [Magma G]
    (h323 : Equation323 G) (h4321 : Equation4321 G) (h4512 : Equation4512 G) : Equation4362 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h323 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4321 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq19 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq14 eq14 -- superposition 14,14
  have eq24 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq14 eq13 -- superposition 13,14
  have eq28 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq19 -- forward demodulation 19,15
  have eq35 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq38 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq13 eq15 -- superposition 15,13
  have eq43 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq13 -- superposition 13,15
  have eq48 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq15 eq35 -- forward demodulation 35,15
  have eq52 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq38 -- forward demodulation 38,15
  have eq61 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq24 eq24 -- superposition 24,24
  have eq68 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq24 eq15 -- superposition 15,24
  have eq80 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq15 eq61 -- forward demodulation 61,15
  have eq81 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq24 eq80 -- forward demodulation 80,24
  have eq82 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq14 eq81 -- forward demodulation 81,14
  have eq83 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq15 eq82 -- forward demodulation 82,15
  have eq84 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq52 eq83 -- forward demodulation 83,52
  have eq85 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ X0)) := superpose eq84 eq28 -- backward demodulation 28,84
  have eq89 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq15 eq68 -- forward demodulation 68,15
  have eq90 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq89 -- forward demodulation 89,15
  have eq91 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq52 eq90 -- forward demodulation 90,52
  have eq93 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq91 eq48 -- backward demodulation 48,91
  have eq437 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := superpose eq43 eq85 -- superposition 85,43
  have eq657 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq14 eq437 -- superposition 437,14
  have eq671 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq437 eq93 -- superposition 93,437
  have eq1188 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := superpose eq437 eq657 -- superposition 657,437
  have eq2080 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq1188 eq15 -- superposition 15,1188
  have eq2161 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq671 eq2080 -- forward demodulation 2080,671
  have eq2162 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq2161 -- forward demodulation 2161,15
  have eq2163 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq13 eq2162 -- forward demodulation 2162,13
  have eq2599 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq2163 eq16 -- superposition 16,2163
  subsumption eq2599 rfl

theorem Equation323_4343_4512_implies_Equation4321 (G : Type*) [Magma G]
    (h323 : Equation323 G) (h4343 : Equation4343 G) (h4512 : Equation4512 G) : Equation4321 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h323 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4343 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq21 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq34 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq21 -- forward demodulation 21,15
  have eq35 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq13 eq34 -- forward demodulation 34,13
  have eq81 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq15 eq35 -- superposition 35,15
  have eq132 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ X2)) := superpose eq15 eq81 -- forward demodulation 81,15
  have eq133 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq13 eq132 -- forward demodulation 132,13
  have eq182 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose eq14 eq133 -- superposition 133,14
  have eq213 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq133 eq16 -- superposition 16,133
  subsumption eq213 eq182

theorem Equation325_3258_4512_implies_Equation38 (G : Type*) [Magma G]
    (h325 : Equation325 G) (h3258 : Equation3258 G) (h4512 : Equation4512 G) : Equation38 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h325 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3258 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq29 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq13 -- superposition 13,15
  have eq105 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq14 eq29 -- superposition 29,14
  have eq161 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq13 eq105 -- superposition 105,13
  have eq256 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq161 eq16 -- superposition 16,161
  subsumption eq256 rfl

theorem Equation326_3255_4512_implies_Equation3322 (G : Type*) [Magma G]
    (h326 : Equation326 G) (h3255 : Equation3255 G) (h4512 : Equation4512 G) : Equation3322 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h326 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h3255 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq13 eq15 -- superposition 15,13
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq26 -- forward demodulation 26,15
  have eq37 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq36 -- forward demodulation 36,15
  have eq104 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq14 eq37 -- superposition 37,14
  have eq121 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq13 eq104 -- forward demodulation 104,13
  have eq291 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq121 eq16 -- superposition 16,121
  subsumption eq291 rfl

theorem Equation326_3258_4512_implies_Equation309 (G : Type*) [Magma G]
    (h326 : Equation326 G) (h3258 : Equation3258 G) (_ : Equation4512 G) : Equation309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h326 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3258 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq13 eq14 -- forward demodulation 14,13
  subsumption eq16 eq17

theorem Equation326_4284_4512_implies_Equation323 (G : Type*) [Magma G]
    (h326 : Equation326 G) (h4284 : Equation4284 G) (_ : Equation4512 G) : Equation323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h326 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4284 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq13 eq14 -- forward demodulation 14,13
  subsumption eq16 eq17

theorem Equation326_4293_4512_implies_Equation4358 (G : Type*) [Magma G]
    (h326 : Equation326 G) (h4293 : Equation4293 G) (h4512 : Equation4512 G) : Equation4358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h326 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4293 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq23 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq13 eq15 -- superposition 15,13
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq23 -- forward demodulation 23,15
  have eq37 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq36 -- forward demodulation 36,15
  have eq53 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq14 eq37 -- superposition 37,14
  have eq916 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq37 eq53 -- superposition 53,37
  have eq1683 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq916 eq16 -- superposition 16,916
  subsumption eq1683 rfl

theorem Equation326_4314_4512_implies_Equation325 (G : Type*) [Magma G]
    (h326 : Equation326 G) (h4314 : Equation4314 G) (_ : Equation4512 G) : Equation325 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h326 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4314 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq13 eq14 -- forward demodulation 14,13
  subsumption eq16 eq17

theorem Equation326_4321_4512_implies_Equation4293 (G : Type*) [Magma G]
    (h326 : Equation326 G) (h4321 : Equation4321 G) (h4512 : Equation4512 G) : Equation4293 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h326 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4321 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq19 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq25 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq15 eq19 -- forward demodulation 19,15
  have eq35 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq13 eq15 -- superposition 15,13
  have eq40 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq14 eq15 -- superposition 15,14
  have eq42 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq13 -- superposition 13,15
  have eq48 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq35 -- forward demodulation 35,15
  have eq49 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq48 -- forward demodulation 48,15
  have eq55 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq40 -- forward demodulation 40,15
  have eq61 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq14 eq49 -- superposition 49,14
  have eq76 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq42 eq61 -- forward demodulation 61,42
  have eq129 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq25 eq49 -- superposition 49,25
  have eq292 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq15 eq129 -- forward demodulation 129,15
  have eq293 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq55 eq292 -- forward demodulation 292,55
  have eq294 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq49 eq293 -- forward demodulation 293,49
  have eq295 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq49 eq294 -- forward demodulation 294,49
  have eq296 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq76 eq295 -- forward demodulation 295,76
  have eq297 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq76 eq296 -- forward demodulation 296,76
  have eq2918 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq76 eq297 -- superposition 297,76
  have eq3280 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose eq14 eq2918 -- superposition 2918,14
  have eq3358 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq2918 eq16 -- superposition 16,2918
  subsumption eq3358 eq3280

theorem Equation326_4343_4512_implies_Equation43 (G : Type*) [Magma G]
    (h326 : Equation326 G) (h4343 : Equation4343 G) (_ : Equation4512 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h326 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4343 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ X0) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq22 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq13 eq17 -- superposition 17,13
  have eq64 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq22 eq16 -- superposition 16,22
  subsumption eq64 rfl

theorem Equation411_3253_4512_implies_Equation8 (G : Type*) [Magma G]
    (h411 : Equation411 G) (h3253 : Equation3253 G) (_ : Equation4512 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h411 ..)
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h3253 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 eq14

theorem Equation411_4268_4512_implies_Equation3 (G : Type*) [Magma G]
    (h411 : Equation411 G) (h4268 : Equation4268 G) (_ : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h411 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4268 ..)
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq15 eq12 -- superposition 12,15
  have eq23 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq17 eq15 -- backward demodulation 15,17
  have eq25 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq23 eq17 -- backward demodulation 17,23
  have eq32 : sK0 ≠ sK0 := superpose eq25 eq14 -- superposition 14,25
  subsumption eq32 rfl

theorem Equation411_4269_4512_implies_Equation3 (G : Type*) [Magma G]
    (h411 : Equation411 G) (h4269 : Equation4269 G) (h4512 : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h411 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4269 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  have eq31 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq12 -- superposition 12,13
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq33 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq13 eq32 -- forward demodulation 32,13
  have eq34 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq13 eq33 -- forward demodulation 33,13
  have eq55 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq31 eq11 -- backward demodulation 11,31
  have eq61 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq55 eq13 -- superposition 13,55
  have eq67 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq13 eq61 -- forward demodulation 61,13
  have eq68 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq13 eq67 -- forward demodulation 67,13
  have eq69 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq68 eq34 -- backward demodulation 34,68
  have eq74 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq69 eq55 -- backward demodulation 55,69
  have eq77 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq69 eq12 -- backward demodulation 12,69
  have eq116 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq74 eq77 -- superposition 77,74
  have eq138 : sK0 ≠ sK0 := superpose eq116 eq14 -- superposition 14,116
  subsumption eq138 rfl

theorem Equation411_4270_4512_implies_Equation8 (G : Type*) [Magma G]
    (h411 : Equation411 G) (h4270 : Equation4270 G) (h4512 : Equation4512 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h411 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4270 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq16 (X0 : G) : sK0 ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq12 eq14 -- superposition 14,12
  have eq25 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq13 eq12 -- superposition 12,13
  have eq170 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq25 -- superposition 25,11
  have eq211 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq170 eq12 -- backward demodulation 12,170
  have eq266 : sK0 ≠ sK0 := superpose eq211 eq16 -- superposition 16,211
  subsumption eq266 rfl

theorem Equation411_4272_4512_implies_Equation3 (G : Type*) [Magma G]
    (h411 : Equation411 G) (h4272 : Equation4272 G) (h4512 : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h411 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4272 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq16 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq12 eq12 -- superposition 12,12
  have eq18 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq12 eq11 -- superposition 11,12
  have eq19 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq13 eq18 -- forward demodulation 18,13
  have eq20 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) := superpose eq13 eq19 -- forward demodulation 19,13
  have eq21 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq20 -- forward demodulation 20,11
  have eq22 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq21 eq16 -- backward demodulation 16,21
  have eq23 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq22 eq11 -- backward demodulation 11,22
  have eq26 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq23 eq12 -- backward demodulation 12,23
  have eq35 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X2 := superpose eq26 eq13 -- superposition 13,26
  have eq48 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq26 eq35 -- forward demodulation 35,26
  have eq63 : sK0 ≠ sK0 := superpose eq48 eq14 -- superposition 14,48
  subsumption eq63 rfl

theorem Equation411_4273_4512_implies_Equation8 (G : Type*) [Magma G]
    (h411 : Equation411 G) (h4273 : Equation4273 G) (h4512 : Equation4512 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h411 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4273 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq12 eq12 -- superposition 12,12
  have eq19 (X0 : G) : sK0 ≠ (X0 ◇ (sK0 ◇ X0)) := superpose eq12 eq14 -- superposition 14,12
  have eq20 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq12 eq11 -- superposition 11,12
  have eq21 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  have eq36 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) := superpose eq13 eq21 -- forward demodulation 21,13
  have eq37 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq13 eq36 -- forward demodulation 36,13
  have eq38 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq13 eq37 -- forward demodulation 37,13
  have eq69 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq15 eq15 -- superposition 15,15
  have eq90 (X0 X1 : G) : sK0 ≠ ((X0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq15 eq19 -- superposition 19,15
  have eq111 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) = X0 := superpose eq11 eq20 -- superposition 20,11
  have eq131 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = X0 := superpose eq13 eq111 -- forward demodulation 111,13
  have eq132 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) = X0 := superpose eq13 eq131 -- forward demodulation 131,13
  have eq133 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq13 eq132 -- forward demodulation 132,13
  have eq134 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq38 eq133 -- forward demodulation 133,38
  have eq136 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq134 eq12 -- backward demodulation 12,134
  have eq154 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ X1) := superpose eq136 eq69 -- backward demodulation 69,136
  have eq156 (X0 : G) : sK0 ≠ ((X0 ◇ sK0) ◇ X0) := superpose eq136 eq90 -- backward demodulation 90,136
  have eq161 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq136 eq154 -- forward demodulation 154,136
  subsumption eq156 eq161

theorem Equation411_4275_4512_implies_Equation8 (G : Type*) [Magma G]
    (h411 : Equation411 G) (h4275 : Equation4275 G) (h4512 : Equation4512 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h411 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4275 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12
  have eq16 (X0 : G) : sK0 ≠ (X0 ◇ (X0 ◇ sK0)) := superpose eq12 eq14 -- superposition 14,12
  have eq17 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := superpose eq12 eq11 -- superposition 11,12
  have eq32 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq12 -- superposition 12,13
  have eq133 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := superpose eq15 eq17 -- superposition 17,15
  have eq178 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) = ((X0 ◇ X0) ◇ X0) := superpose eq17 eq32 -- superposition 32,17
  have eq234 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq13 eq178 -- forward demodulation 178,13
  have eq235 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq133 eq234 -- forward demodulation 234,133
  have eq237 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq235 eq12 -- backward demodulation 12,235
  have eq338 : sK0 ≠ sK0 := superpose eq237 eq16 -- superposition 16,237
  subsumption eq338 rfl

theorem Equation411_4276_4512_implies_Equation2 (G : Type*) [Magma G]
    (h411 : Equation411 G) (h4276 : Equation4276 G) (h4512 : Equation4512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h411 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := mod_symm (h4276 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq15 : sK0 ≠ sK1 := mod_symm nh
  have eq20 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := superpose eq13 eq12 -- superposition 12,13
  have eq22 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) := superpose eq12 eq14 -- superposition 14,12
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = ((X1 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq13 eq14 -- superposition 14,13
  have eq37 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) := superpose eq14 eq22 -- forward demodulation 22,14
  have eq38 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq14 eq37 -- forward demodulation 37,14
  have eq39 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq14 eq38 -- forward demodulation 38,14
  have eq40 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq14 eq23 -- forward demodulation 23,14
  have eq72 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2)) := superpose eq20 eq14 -- superposition 14,20
  have eq77 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2))) := superpose eq14 eq72 -- forward demodulation 72,14
  have eq78 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) := superpose eq14 eq77 -- forward demodulation 77,14
  have eq79 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2))))) := superpose eq14 eq78 -- forward demodulation 78,14
  have eq138 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X2 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq39 eq40 -- superposition 40,39
  have eq160 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))))) = X2 := superpose eq40 eq20 -- superposition 20,40
  have eq233 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))))))) = X2 := superpose eq14 eq160 -- forward demodulation 160,14
  have eq234 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))))))) = X2 := superpose eq14 eq233 -- forward demodulation 233,14
  have eq235 (X0 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X2 := superpose eq79 eq234 -- forward demodulation 234,79
  have eq236 (X0 X2 : G) : (X2 ◇ (X2 ◇ X0)) = X2 := superpose eq12 eq235 -- forward demodulation 235,12
  have eq237 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq236 eq39 -- backward demodulation 39,236
  have eq238 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X2 ◇ (X2 ◇ X2)) ◇ X0) := superpose eq236 eq138 -- backward demodulation 138,236
  have eq279 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ X0) := superpose eq237 eq238 -- forward demodulation 238,237
  have eq280 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq237 eq279 -- forward demodulation 279,237
  have eq303 (X0 X1 : G) : X0 = X1 := superpose eq237 eq280 -- superposition 280,237
  have eq317 (X0 : G) : sK0 ≠ X0 := superpose eq303 eq15 -- superposition 15,303
  subsumption eq317 eq303

theorem Equation411_4283_4290_4512_implies_Equation43 (G : Type*) [Magma G]
    (h411 : Equation411 G) (h4283 : Equation4283 G) (h4290 : Equation4290 G) (h4512 : Equation4512 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq14 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h411 ..)
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq16 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq18 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq21 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq16 eq16 -- superposition 16,16
  have eq26 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq17 eq21 -- forward demodulation 21,17
  have eq34 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq15 eq17 -- superposition 17,15
  have eq35 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq15 eq17 -- superposition 17,15
  have eq36 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq16 eq17 -- superposition 17,16
  have eq42 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq16 eq17 -- superposition 17,16
  have eq59 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq17 eq34 -- forward demodulation 34,17
  have eq60 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq17 eq35 -- forward demodulation 35,17
  have eq61 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq17 eq36 -- forward demodulation 36,17
  have eq2498 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq60 eq61 -- superposition 61,60
  have eq3210 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq26 eq59 -- superposition 59,26
  have eq3936 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq42 eq3210 -- forward demodulation 3210,42
  have eq3937 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq16 eq3936 -- forward demodulation 3936,16
  have eq3938 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq14 eq3937 -- forward demodulation 3937,14
  have eq17991 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq2498 eq3938 -- superposition 3938,2498
  have eq18035 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq14 eq17991 -- forward demodulation 17991,14
  have eq18552 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18035 eq18 -- superposition 18,18035
  subsumption eq18552 rfl

theorem Equation411_4284_4512_implies_Equation3 (G : Type*) [Magma G]
    (h411 : Equation411 G) (h4284 : Equation4284 G) (h4512 : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h411 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq12 eq12 -- superposition 12,12
  have eq16 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq12 eq13 -- superposition 13,12
  have eq21 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) := superpose eq11 eq13 -- superposition 13,11
  have eq27 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) := superpose eq13 eq11 -- superposition 11,13
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq13 eq19 -- forward demodulation 19,13
  have eq39 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq16 eq21 -- forward demodulation 21,16
  have eq49 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)))) := superpose eq36 eq27 -- forward demodulation 27,36
  have eq50 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))))) := superpose eq13 eq49 -- forward demodulation 49,13
  have eq51 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) := superpose eq13 eq50 -- forward demodulation 50,13
  have eq52 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))))) := superpose eq12 eq51 -- forward demodulation 51,12
  have eq53 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq39 eq52 -- forward demodulation 52,39
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq53 -- superposition 53,11
  have eq109 : sK0 ≠ sK0 := superpose eq57 eq14 -- superposition 14,57
  subsumption eq109 rfl

theorem Equation411_4291_4512_implies_Equation3 (G : Type*) [Magma G]
    (h411 : Equation411 G) (h4291 : Equation4291 G) (h4512 : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h411 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq15 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq12 -- superposition 12,11
  have eq69 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq13 eq15 -- superposition 15,13
  have eq88 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq13 eq69 -- forward demodulation 69,13
  have eq89 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq13 eq88 -- forward demodulation 88,13
  have eq90 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq89 -- forward demodulation 89,11
  have eq153 : sK0 ≠ sK0 := superpose eq90 eq14 -- superposition 14,90
  subsumption eq153 rfl

theorem Equation411_4293_4512_implies_Equation3 (G : Type*) [Magma G]
    (h411 : Equation411 G) (h4293 : Equation4293 G) (h4512 : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h411 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4293 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq12 eq13 -- superposition 13,12
  have eq22 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := superpose eq13 eq11 -- superposition 11,13
  have eq30 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq13 eq30 -- forward demodulation 30,13
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq13 eq31 -- forward demodulation 31,13
  have eq33 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq44 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq33 eq22 -- forward demodulation 22,33
  have eq45 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq13 eq44 -- forward demodulation 44,13
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))))) := superpose eq13 eq45 -- forward demodulation 45,13
  have eq47 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))))) := superpose eq13 eq46 -- forward demodulation 46,13
  have eq146 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)))) := superpose eq33 eq32 -- superposition 32,33
  have eq330 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))))) := superpose eq13 eq146 -- forward demodulation 146,13
  have eq331 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))))) := superpose eq13 eq330 -- forward demodulation 330,13
  have eq332 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq331 eq47 -- backward demodulation 47,331
  have eq346 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq11 eq332 -- superposition 332,11
  have eq368 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) = X0 := superpose eq13 eq346 -- forward demodulation 346,13
  have eq369 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))))) = X0 := superpose eq13 eq368 -- forward demodulation 368,13
  have eq370 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))))) = X0 := superpose eq13 eq369 -- forward demodulation 369,13
  have eq371 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq32 eq370 -- forward demodulation 370,32
  have eq372 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq371 -- forward demodulation 371,11
  have eq815 : sK0 ≠ sK0 := superpose eq372 eq14 -- superposition 14,372
  subsumption eq815 rfl

theorem Equation411_4314_4512_implies_Equation3 (G : Type*) [Magma G]
    (h411 : Equation411 G) (h4314 : Equation4314 G) (h4512 : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h411 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4314 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq15 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq12 -- superposition 12,11
  have eq18 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq19 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq13 eq18 -- forward demodulation 18,13
  have eq20 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq13 eq19 -- forward demodulation 19,13
  have eq21 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq20 -- forward demodulation 20,11
  have eq24 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq12 eq13 -- superposition 13,12
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq12 eq13 -- superposition 13,12
  have eq28 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq12 eq13 -- superposition 13,12
  have eq30 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq13 eq12 -- superposition 12,13
  have eq33 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) := superpose eq13 eq11 -- superposition 11,13
  have eq41 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq13 eq24 -- forward demodulation 24,13
  have eq42 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq52 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq30 -- forward demodulation 30,13
  have eq60 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)))) := superpose eq42 eq33 -- forward demodulation 33,42
  have eq61 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))))) := superpose eq13 eq60 -- forward demodulation 60,13
  have eq62 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))))) := superpose eq13 eq61 -- forward demodulation 61,13
  have eq63 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))) := superpose eq52 eq62 -- forward demodulation 62,52
  have eq64 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq13 eq63 -- forward demodulation 63,13
  have eq65 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq52 eq64 -- forward demodulation 64,52
  have eq208 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X3))) = ((X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) ◇ X3) := superpose eq41 eq41 -- superposition 41,41
  have eq222 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2))) := superpose eq41 eq41 -- superposition 41,41
  have eq233 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) := superpose eq13 eq41 -- superposition 41,13
  have eq238 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) := superpose eq41 eq12 -- superposition 12,41
  have eq261 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) ◇ X3) = (X2 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq13 eq208 -- forward demodulation 208,13
  have eq262 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq13 eq261 -- forward demodulation 261,13
  have eq303 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2)))) := superpose eq13 eq222 -- forward demodulation 222,13
  have eq304 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) := superpose eq13 eq303 -- forward demodulation 303,13
  have eq326 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3))))) := superpose eq13 eq233 -- forward demodulation 233,13
  have eq327 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3))))) := superpose eq13 eq326 -- forward demodulation 326,13
  have eq329 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) = ((X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1)) ◇ X3) := superpose eq327 eq262 -- backward demodulation 262,327
  have eq334 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) = ((X2 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1))) ◇ X3) := superpose eq13 eq329 -- forward demodulation 329,13
  have eq335 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) = ((X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1)))) ◇ X3) := superpose eq13 eq334 -- forward demodulation 334,13
  have eq336 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) = ((X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ X3) := superpose eq13 eq335 -- forward demodulation 335,13
  have eq337 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) = ((X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ X3) := superpose eq28 eq336 -- forward demodulation 336,28
  have eq338 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) = ((X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X3) := superpose eq13 eq337 -- forward demodulation 337,13
  have eq375 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = (X2 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := superpose eq13 eq238 -- forward demodulation 238,13
  have eq376 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq13 eq375 -- forward demodulation 375,13
  have eq377 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq327 eq376 -- forward demodulation 376,327
  have eq378 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq13 eq377 -- forward demodulation 377,13
  have eq379 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1)))) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq13 eq378 -- forward demodulation 378,13
  have eq380 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq13 eq379 -- forward demodulation 379,13
  have eq381 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq28 eq380 -- forward demodulation 380,28
  have eq382 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq13 eq381 -- forward demodulation 381,13
  have eq1108 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) = X0 := superpose eq21 eq65 -- superposition 65,21
  have eq1164 (X0 : G) : (X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq41 eq1108 -- forward demodulation 1108,41
  have eq1165 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq13 eq1164 -- forward demodulation 1164,13
  have eq1166 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) = X0 := superpose eq13 eq1165 -- forward demodulation 1165,13
  have eq1167 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))))) = X0 := superpose eq13 eq1166 -- forward demodulation 1166,13
  have eq1168 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))))) = X0 := superpose eq13 eq1167 -- forward demodulation 1167,13
  have eq1169 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))))))) = X0 := superpose eq13 eq1168 -- forward demodulation 1168,13
  have eq1170 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))))) = X0 := superpose eq304 eq1169 -- forward demodulation 1169,304
  have eq1171 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))))) = X0 := superpose eq13 eq1170 -- forward demodulation 1170,13
  have eq1172 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq338 eq1171 -- forward demodulation 1171,338
  have eq1173 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq13 eq1172 -- forward demodulation 1172,13
  have eq1174 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) = X0 := superpose eq13 eq1173 -- forward demodulation 1173,13
  have eq1175 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))))) = X0 := superpose eq13 eq1174 -- forward demodulation 1174,13
  have eq1176 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq338 eq1175 -- forward demodulation 1175,338
  have eq1177 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq13 eq1176 -- forward demodulation 1176,13
  have eq1178 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq13 eq1177 -- forward demodulation 1177,13
  have eq1179 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))))) = X0 := superpose eq13 eq1178 -- forward demodulation 1178,13
  have eq1180 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0))) = X0 := superpose eq338 eq1179 -- forward demodulation 1179,338
  have eq1181 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)))) = X0 := superpose eq13 eq1180 -- forward demodulation 1180,13
  have eq1182 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))) = X0 := superpose eq13 eq1181 -- forward demodulation 1181,13
  have eq1183 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))))) = X0 := superpose eq13 eq1182 -- forward demodulation 1182,13
  have eq1184 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X0)) = X0 := superpose eq338 eq1183 -- forward demodulation 1183,338
  have eq1185 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0))) = X0 := superpose eq13 eq1184 -- forward demodulation 1184,13
  have eq1186 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)))) = X0 := superpose eq13 eq1185 -- forward demodulation 1185,13
  have eq1187 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))))) = X0 := superpose eq13 eq1186 -- forward demodulation 1186,13
  have eq1188 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = X0 := superpose eq382 eq1187 -- forward demodulation 1187,382
  have eq1189 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose eq12 eq1188 -- forward demodulation 1188,12
  have eq1190 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq13 eq1189 -- forward demodulation 1189,13
  have eq1191 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq1190 -- forward demodulation 1190,11
  have eq1916 : sK0 ≠ sK0 := superpose eq1191 eq14 -- superposition 14,1191
  subsumption eq1916 rfl

theorem Equation411_4321_4512_implies_Equation3 (G : Type*) [Magma G]
    (h411 : Equation411 G) (h4321 : Equation4321 G) (h4512 : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h411 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4321 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq15 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose eq11 eq12 -- superposition 12,11
  have eq21 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq22 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq13 eq21 -- forward demodulation 21,13
  have eq23 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq13 eq22 -- forward demodulation 22,13
  have eq24 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq23 -- forward demodulation 23,11
  have eq61 : sK0 ≠ sK0 := superpose eq24 eq14 -- superposition 14,24
  subsumption eq61 rfl

theorem Equation411_4343_4512_implies_Equation3 (G : Type*) [Magma G]
    (h411 : Equation411 G) (h4343 : Equation4343 G) (h4512 : Equation4512 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h411 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4343 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq13 eq12 -- superposition 12,13
  have eq30 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq13 eq30 -- forward demodulation 30,13
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq13 eq31 -- forward demodulation 31,13
  have eq596 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq22 eq32 -- superposition 32,22
  have eq692 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq13 eq596 -- forward demodulation 596,13
  have eq693 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq692 -- forward demodulation 692,11
  have eq1174 : sK0 ≠ sK0 := superpose eq693 eq14 -- superposition 14,693
  subsumption eq1174 rfl

theorem Equation411_4364_4512_implies_Equation43 (G : Type*) [Magma G]
    (h411 : Equation411 G) (h4364 : Equation4364 G) (h4512 : Equation4512 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h411 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h4364 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq15 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) := superpose eq12 eq13 -- superposition 13,12
  have eq26 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) := superpose eq14 eq16 -- forward demodulation 16,14
  have eq27 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq14 eq26 -- forward demodulation 26,14
  have eq28 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq14 eq27 -- forward demodulation 27,14
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) := superpose eq12 eq14 -- superposition 14,12
  have eq61 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) := superpose eq14 eq46 -- forward demodulation 46,14
  have eq62 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq14 eq61 -- forward demodulation 61,14
  have eq63 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq14 eq62 -- forward demodulation 62,14
  have eq4636 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq28 eq63 -- superposition 63,28
  have eq5064 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq4636 eq15 -- superposition 15,4636
  subsumption eq5064 rfl

theorem Equation411_4369_4512_implies_Equation43 (G : Type*) [Magma G]
    (h411 : Equation411 G) (h4369 : Equation4369 G) (h4512 : Equation4512 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h411 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := mod_symm (h4369 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq15 : (sK1 ◇ sK0) ≠ (sK0 ◇ sK1) := mod_symm nh
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq12 eq13 -- superposition 13,12
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) := superpose eq12 eq14 -- superposition 14,12
  have eq43 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) := superpose eq14 eq28 -- forward demodulation 28,14
  have eq44 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq14 eq43 -- forward demodulation 43,14
  have eq45 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq14 eq44 -- forward demodulation 44,14
  have eq84 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1))) := superpose eq14 eq16 -- superposition 16,14
  have eq156 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq14 eq84 -- forward demodulation 84,14
  have eq157 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq14 eq156 -- forward demodulation 156,14
  have eq3652 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq45 eq157 -- superposition 157,45
  have eq5502 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq3652 eq15 -- superposition 15,3652
  subsumption eq5502 rfl

theorem Equation429_3315_4512_implies_Equation11 (G : Type*) [Magma G]
    (h429 : Equation429 G) (h3315 : Equation3315 G) (h4512 : Equation4512 G) : Equation11 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h429 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3315 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq29 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) = (X0 ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq41 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) := superpose eq15 eq29 -- forward demodulation 29,15
  have eq42 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq15 eq41 -- forward demodulation 41,15
  have eq43 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq15 eq42 -- forward demodulation 42,15
  have eq222 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq14 eq43 -- superposition 43,14
  have eq253 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq13 eq222 -- forward demodulation 222,13
  have eq324 : sK0 ≠ sK0 := superpose eq253 eq16 -- superposition 16,253
  subsumption eq324 rfl

theorem Equation429_3353_4512_implies_Equation16 (G : Type*) [Magma G]
    (h429 : Equation429 G) (h3353 : Equation3353 G) (h4512 : Equation4512 G) : Equation16 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h429 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3353 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq22 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq14 eq14 -- superposition 14,14
  have eq24 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)))) := superpose eq14 eq13 -- superposition 13,14
  have eq28 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq15 eq22 -- forward demodulation 22,15
  have eq29 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq15 eq28 -- forward demodulation 28,15
  have eq30 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq13 eq29 -- forward demodulation 29,13
  have eq31 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))) := superpose eq15 eq24 -- forward demodulation 24,15
  have eq32 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq15 eq31 -- forward demodulation 31,15
  have eq33 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq13 eq32 -- forward demodulation 32,13
  have eq34 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) = (X0 ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq46 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) := superpose eq15 eq34 -- forward demodulation 34,15
  have eq47 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq15 eq46 -- forward demodulation 46,15
  have eq48 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq15 eq47 -- forward demodulation 47,15
  have eq74 (X0 X1 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq13 eq30 -- superposition 30,13
  have eq80 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq15 eq30 -- superposition 30,15
  have eq85 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq15 eq74 -- forward demodulation 74,15
  have eq86 (X0 X1 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq15 eq85 -- forward demodulation 85,15
  have eq87 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq15 eq86 -- forward demodulation 86,15
  have eq93 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq80 -- forward demodulation 80,15
  have eq94 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq93 eq87 -- backward demodulation 87,93
  have eq108 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = (((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq13 eq33 -- superposition 33,13
  have eq124 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = (((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq15 eq108 -- forward demodulation 108,15
  have eq125 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = (((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))))) := superpose eq15 eq124 -- forward demodulation 124,15
  have eq126 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = (((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))))) := superpose eq15 eq125 -- forward demodulation 125,15
  have eq127 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = (((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq48 eq126 -- forward demodulation 126,48
  have eq128 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq15 eq127 -- forward demodulation 127,15
  have eq129 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq15 eq128 -- forward demodulation 128,15
  have eq130 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq15 eq129 -- forward demodulation 129,15
  have eq131 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq93 eq130 -- forward demodulation 130,93
  have eq132 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq94 eq131 -- forward demodulation 131,94
  have eq171 : sK0 ≠ sK0 := superpose eq132 eq16 -- superposition 16,132
  subsumption eq171 rfl

theorem Equation440_4283_4512_implies_Equation4358 (G : Type*) [Magma G]
    (h440 : Equation440 G) (h4283 : Equation4283 G) (h4512 : Equation4512 G) : Equation4358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h440 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq31 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2)) = (X0 ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq46 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2))) := superpose eq15 eq31 -- forward demodulation 31,15
  have eq47 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) := superpose eq15 eq46 -- forward demodulation 46,15
  have eq48 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2))))) := superpose eq15 eq47 -- forward demodulation 47,15
  have eq222 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq14 eq48 -- superposition 48,14
  have eq248 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq48 eq222 -- forward demodulation 222,48
  have eq626 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq248 eq16 -- superposition 16,248
  subsumption eq626 rfl

theorem Equation440_4290_4512_implies_Equation504 (G : Type*) [Magma G]
    (h440 : Equation440 G) (h4290 : Equation4290 G) (h4512 : Equation4512 G) : Equation504 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h440 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq26 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq14 eq14 -- superposition 14,14
  have eq32 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq26 -- forward demodulation 26,15
  have eq33 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := superpose eq13 eq32 -- forward demodulation 32,13
  have eq82 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq14 eq33 -- superposition 33,14
  have eq219 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose eq15 eq82 -- superposition 82,15
  have eq597 : sK0 ≠ sK0 := superpose eq219 eq16 -- superposition 16,219
  subsumption eq597 rfl

theorem Equation440_4320_4512_implies_Equation43 (G : Type*) [Magma G]
    (h440 : Equation440 G) (h4320 : Equation4320 G) (h4512 : Equation4512 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h440 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK1 ◇ sK0) ≠ (sK0 ◇ sK1) := mod_symm nh
  have eq23 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) = ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0) := superpose eq13 eq14 -- superposition 14,13
  have eq28 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq14 eq14 -- superposition 14,14
  have eq31 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) = (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) := superpose eq15 eq23 -- forward demodulation 23,15
  have eq32 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) = (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) := superpose eq15 eq31 -- forward demodulation 31,15
  have eq33 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) = (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq15 eq32 -- forward demodulation 32,15
  have eq34 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq13 eq33 -- forward demodulation 33,13
  have eq35 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := superpose eq13 eq34 -- forward demodulation 34,13
  have eq45 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq28 -- forward demodulation 28,15
  have eq46 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq13 eq45 -- forward demodulation 45,13
  have eq89 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq14 eq35 -- superposition 35,14
  have eq337 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose eq15 eq46 -- superposition 46,15
  have eq355 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq337 eq89 -- backward demodulation 89,337
  have eq392 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq355 eq16 -- superposition 16,355
  subsumption eq392 rfl

theorem Equation513_4283_4512_implies_Equation43 (G : Type*) [Magma G]
    (h513 : Equation513 G) (h4283 : Equation4283 G) (_ : Equation4512 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h513 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq16 : (sK1 ◇ sK0) ≠ (sK0 ◇ sK1) := mod_symm nh
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq14 eq13 -- superposition 13,14
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq13 eq19 -- forward demodulation 19,13
  have eq67 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq20 eq16 -- superposition 16,20
  subsumption eq67 rfl

theorem Equation513_4290_4512_implies_Equation440 (G : Type*) [Magma G]
    (h513 : Equation513 G) (h4290 : Equation4290 G) (h4512 : Equation4512 G) : Equation440 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h513 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq19 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose eq14 eq13 -- superposition 13,14
  have eq29 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq14 eq15 -- superposition 15,14
  have eq311 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq19 eq29 -- superposition 29,19
  have eq387 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := superpose eq14 eq311 -- forward demodulation 311,14
  have eq890 : sK0 ≠ sK0 := superpose eq387 eq16 -- superposition 16,387
  subsumption eq890 rfl

theorem Equation513_4320_4512_implies_Equation4362 (G : Type*) [Magma G]
    (h513 : Equation513 G) (h4320 : Equation4320 G) (h4512 : Equation4512 G) : Equation4362 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h513 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq20 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq14 eq14 -- superposition 14,14
  have eq21 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq14 eq13 -- superposition 13,14
  have eq35 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq15 eq20 -- forward demodulation 20,15
  have eq37 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq38 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq43 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq14 -- superposition 14,15
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq15 eq37 -- forward demodulation 37,15
  have eq55 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq38 -- forward demodulation 38,15
  have eq83 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X2)) := superpose eq21 eq15 -- superposition 15,21
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2))) := superpose eq15 eq83 -- forward demodulation 83,15
  have eq102 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)))) := superpose eq15 eq101 -- forward demodulation 101,15
  have eq103 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))))) := superpose eq15 eq102 -- forward demodulation 102,15
  have eq104 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))))) := superpose eq15 eq103 -- forward demodulation 103,15
  have eq105 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))))) := superpose eq15 eq104 -- forward demodulation 104,15
  have eq343 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) = ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) := superpose eq43 eq54 -- superposition 54,43
  have eq385 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2)))) = ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) := superpose eq15 eq343 -- forward demodulation 343,15
  have eq386 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2))))) = ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) := superpose eq15 eq385 -- forward demodulation 385,15
  have eq4137 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq35 eq55 -- superposition 55,35
  have eq4458 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2)))) := superpose eq15 eq4137 -- forward demodulation 4137,15
  have eq4459 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2))))) := superpose eq15 eq4458 -- forward demodulation 4458,15
  have eq4460 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) := superpose eq13 eq4459 -- forward demodulation 4459,13
  have eq4462 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2))))) := superpose eq4460 eq386 -- backward demodulation 386,4460
  have eq4499 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq4462 eq105 -- backward demodulation 105,4462
  have eq5217 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq4499 eq16 -- superposition 16,4499
  subsumption eq5217 rfl

theorem Equation3253_4268_4512_implies_Equation307 (G : Type*) [Magma G]
    (h3253 : Equation3253 G) (h4268 : Equation4268 G) (_ : Equation4512 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h3253 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4268 ..)
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq18 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq12 -- superposition 12,11
  have eq19 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq12 eq14 -- superposition 14,12
  have eq22 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq18 eq12 -- backward demodulation 12,18
  subsumption eq19 eq22

theorem Equation3253_4269_4512_implies_Equation307 (G : Type*) [Magma G]
    (h3253 : Equation3253 G) (h4269 : Equation4269 G) (h4512 : Equation4512 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h3253 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4269 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq16 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq12 eq14 -- superposition 14,12
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12
  have eq31 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq12 -- superposition 12,13
  have eq104 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq13 eq17 -- superposition 17,13
  have eq164 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) := superpose eq31 eq31 -- superposition 31,31
  have eq216 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq104 eq164 -- forward demodulation 164,104
  have eq217 (X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ X2)) := superpose eq216 eq31 -- backward demodulation 31,216
  have eq230 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq217 eq12 -- backward demodulation 12,217
  have eq302 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq230 eq16 -- superposition 16,230
  subsumption eq302 rfl

theorem Equation3253_4270_4512_implies_Equation3259 (G : Type*) [Magma G]
    (h3253 : Equation3253 G) (h4270 : Equation4270 G) (h4512 : Equation4512 G) : Equation3259 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h3253 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4270 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq19 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq13 eq14 -- superposition 14,13
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq13 eq14 -- superposition 14,13
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := superpose eq12 eq14 -- superposition 14,12
  have eq25 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq14 eq13 -- superposition 13,14
  have eq35 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq14 eq19 -- forward demodulation 19,14
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq14 eq20 -- forward demodulation 20,14
  have eq39 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq36 eq22 -- forward demodulation 22,36
  have eq40 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq14 eq39 -- forward demodulation 39,14
  have eq41 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq14 eq40 -- forward demodulation 40,14
  have eq42 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq14 eq41 -- forward demodulation 41,14
  have eq315 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq25 eq35 -- superposition 35,25
  have eq424 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq315 -- forward demodulation 315,12
  have eq1696 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq36 eq42 -- superposition 42,36
  have eq1898 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq424 eq1696 -- forward demodulation 1696,424
  have eq2015 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq1898 eq15 -- superposition 15,1898
  subsumption eq2015 rfl

theorem Equation3253_4272_4512_implies_Equation307 (G : Type*) [Magma G]
    (h3253 : Equation3253 G) (h4272 : Equation4272 G) (h4512 : Equation4512 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h3253 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4272 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12
  have eq16 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq12 eq12 -- superposition 12,12
  have eq17 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq14 -- superposition 14,12
  have eq18 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12
  have eq19 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq12 eq11 -- superposition 11,12
  have eq20 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq13 eq19 -- forward demodulation 19,13
  have eq21 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq20 -- forward demodulation 20,11
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq21 eq16 -- backward demodulation 16,21
  have eq101 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq15 eq18 -- superposition 18,15
  have eq108 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq109 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq108 eq22 -- backward demodulation 22,108
  have eq147 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq109 eq17 -- superposition 17,109
  subsumption eq147 rfl

theorem Equation3253_4273_4512_implies_Equation40 (G : Type*) [Magma G]
    (h3253 : Equation3253 G) (h4273 : Equation4273 G) (h4512 : Equation4512 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h3253 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4273 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq15 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq13 eq13 -- superposition 13,13
  have eq18 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq13 eq13 -- superposition 13,13
  have eq20 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq13 eq12 -- superposition 12,13
  have eq25 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := superpose eq12 eq14 -- superposition 14,12
  have eq42 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) := superpose eq14 eq25 -- forward demodulation 25,14
  have eq43 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) := superpose eq14 eq42 -- forward demodulation 42,14
  have eq44 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq20 eq43 -- forward demodulation 43,20
  have eq111 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq14 eq20 -- superposition 20,14
  have eq112 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq14 eq20 -- superposition 20,14
  have eq115 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq20 eq14 -- superposition 14,20
  have eq129 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq14 eq112 -- forward demodulation 112,14
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq111 eq129 -- forward demodulation 129,111
  have eq131 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq14 eq115 -- forward demodulation 115,14
  have eq132 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq14 eq131 -- forward demodulation 131,14
  have eq133 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq14 eq132 -- forward demodulation 132,14
  have eq134 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq133 eq44 -- backward demodulation 44,133
  have eq202 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq13 eq130 -- superposition 130,13
  have eq259 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq18 eq16 -- superposition 16,18
  have eq293 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq14 eq259 -- forward demodulation 259,14
  have eq294 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq202 eq293 -- forward demodulation 293,202
  have eq560 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq134 eq294 -- superposition 294,134
  have eq780 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq560 eq15 -- superposition 15,560
  subsumption eq780 eq560

theorem Equation3253_4275_4512_implies_Equation3271 (G : Type*) [Magma G]
    (h3253 : Equation3253 G) (h4275 : Equation4275 G) (h4512 : Equation4512 G) : Equation3271 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h3253 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4275 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq15 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq13 eq13 -- superposition 13,13
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq12 -- superposition 12,13
  have eq24 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq13 eq14 -- superposition 14,13
  have eq26 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq14 eq12 -- superposition 12,14
  have eq44 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq14 eq24 -- forward demodulation 24,14
  have eq46 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := superpose eq14 eq26 -- forward demodulation 26,14
  have eq47 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq44 eq46 -- forward demodulation 46,44
  have eq58 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X2 ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq13 eq16 -- superposition 16,13
  have eq93 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq17 eq58 -- forward demodulation 58,17
  have eq134 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq14 eq93 -- superposition 93,14
  have eq148 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq134 eq47 -- backward demodulation 47,134
  have eq181 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq148 eq15 -- superposition 15,148
  subsumption eq181 rfl

theorem Equation3253_4276_4512_implies_Equation40 (G : Type*) [Magma G]
    (h3253 : Equation3253 G) (h4276 : Equation4276 G) (h4512 : Equation4512 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h3253 ..)
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := mod_symm (h4276 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq15 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq20 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq13 eq12 -- superposition 12,13
  have eq26 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := superpose eq12 eq14 -- superposition 14,12
  have eq43 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq20 eq26 -- forward demodulation 26,20
  have eq53 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq14 eq20 -- superposition 20,14
  have eq54 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq20 eq20 -- superposition 20,20
  have eq66 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := superpose eq14 eq53 -- forward demodulation 53,14
  have eq74 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq43 eq43 -- superposition 43,43
  have eq75 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq14 eq43 -- superposition 43,14
  have eq77 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ X1)) := superpose eq14 eq43 -- superposition 43,14
  have eq98 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq14 eq74 -- forward demodulation 74,14
  have eq99 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq14 eq75 -- forward demodulation 75,14
  have eq100 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq99 eq98 -- backward demodulation 98,99
  have eq101 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq77 eq66 -- backward demodulation 66,77
  have eq105 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq100 eq101 -- forward demodulation 101,100
  have eq108 (X0 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ X0)) := superpose eq105 eq54 -- backward demodulation 54,105
  have eq139 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose eq13 eq108 -- superposition 108,13
  have eq217 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq139 eq139 -- superposition 139,139
  have eq391 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq217 eq15 -- superposition 15,217
  subsumption eq391 eq217

theorem Equation3253_4284_4512_implies_Equation307 (G : Type*) [Magma G]
    (h3253 : Equation3253 G) (h4284 : Equation4284 G) (h4512 : Equation4512 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h3253 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq12 eq12 -- superposition 12,12
  have eq16 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq11 eq16 -- forward demodulation 16,11
  have eq70 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq17 -- superposition 17,11
  have eq334 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq70 eq14 -- superposition 14,70
  subsumption eq334 rfl

theorem Equation3253_4291_4512_implies_Equation307 (G : Type*) [Magma G]
    (h3253 : Equation3253 G) (h4291 : Equation4291 G) (h4512 : Equation4512 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h3253 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq18 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = ((X0 ◇ X0) ◇ X1) := superpose eq11 eq13 -- superposition 13,11
  have eq19 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq12 eq13 -- superposition 13,12
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq12 eq13 -- superposition 13,12
  have eq31 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq13 eq18 -- forward demodulation 18,13
  have eq32 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq13 eq31 -- forward demodulation 31,13
  have eq33 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq13 eq32 -- forward demodulation 32,13
  have eq34 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq19 -- forward demodulation 19,13
  have eq35 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq13 eq20 -- forward demodulation 20,13
  have eq80 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq33 -- superposition 33,12
  have eq83 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))))) := superpose eq13 eq33 -- superposition 33,13
  have eq96 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)))))) := superpose eq13 eq83 -- forward demodulation 83,13
  have eq97 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))))) := superpose eq13 eq96 -- forward demodulation 96,13
  have eq98 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))))) := superpose eq13 eq97 -- forward demodulation 97,13
  have eq120 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)))) := superpose eq12 eq34 -- superposition 34,12
  have eq136 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq13 eq34 -- superposition 34,13
  have eq155 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq34 eq33 -- superposition 33,34
  have eq211 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))))) := superpose eq13 eq120 -- forward demodulation 120,13
  have eq212 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))))) := superpose eq13 eq211 -- forward demodulation 211,13
  have eq230 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq13 eq136 -- forward demodulation 136,13
  have eq231 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq13 eq230 -- forward demodulation 230,13
  have eq232 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X2)))) := superpose eq231 eq98 -- backward demodulation 98,231
  have eq234 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2))))) := superpose eq13 eq232 -- forward demodulation 232,13
  have eq235 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2)))))) := superpose eq13 eq234 -- forward demodulation 234,13
  have eq236 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))))) := superpose eq13 eq235 -- forward demodulation 235,13
  have eq323 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq13 eq155 -- forward demodulation 155,13
  have eq324 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq13 eq323 -- forward demodulation 323,13
  have eq325 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq324 eq236 -- backward demodulation 236,324
  have eq332 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq325 eq212 -- backward demodulation 212,325
  have eq357 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq324 eq332 -- forward demodulation 332,324
  have eq379 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3))) = ((X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)))) ◇ X3) := superpose eq34 eq35 -- superposition 35,34
  have eq382 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))))))) := superpose eq11 eq35 -- superposition 35,11
  have eq469 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3))) = ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))))) ◇ X3) := superpose eq13 eq379 -- forward demodulation 379,13
  have eq470 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3))) = ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))))) ◇ X3) := superpose eq13 eq469 -- forward demodulation 469,13
  have eq471 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3))) = ((X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) ◇ X3) := superpose eq325 eq470 -- forward demodulation 470,325
  have eq472 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3) = (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3))) := superpose eq324 eq471 -- forward demodulation 471,324
  have eq473 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3) = (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3)))) := superpose eq13 eq472 -- forward demodulation 472,13
  have eq474 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) := superpose eq13 eq473 -- forward demodulation 473,13
  have eq475 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) := superpose eq13 eq474 -- forward demodulation 474,13
  have eq476 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) = (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) := superpose eq13 eq475 -- forward demodulation 475,13
  have eq477 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) := superpose eq13 eq476 -- forward demodulation 476,13
  have eq494 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ X1))))) := superpose eq34 eq382 -- forward demodulation 382,34
  have eq495 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)))))) := superpose eq13 eq494 -- forward demodulation 494,13
  have eq496 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1))))) := superpose eq357 eq495 -- forward demodulation 495,357
  have eq497 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq13 eq496 -- forward demodulation 496,13
  have eq498 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq477 eq497 -- forward demodulation 497,477
  have eq499 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) = (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq13 eq498 -- forward demodulation 498,13
  have eq500 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq80 eq499 -- forward demodulation 499,80
  have eq501 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq12 eq500 -- forward demodulation 500,12
  have eq502 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq357 eq501 -- forward demodulation 501,357
  have eq503 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq33 eq502 -- forward demodulation 502,33
  have eq757 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq503 -- superposition 503,11
  have eq930 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq757 eq14 -- superposition 14,757
  subsumption eq930 rfl

theorem Equation3253_4293_4512_implies_Equation307 (G : Type*) [Magma G]
    (h3253 : Equation3253 G) (h4293 : Equation4293 G) (h4512 : Equation4512 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h3253 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4293 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq20 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq12 eq13 -- superposition 13,12
  have eq41 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq13 eq20 -- forward demodulation 20,13
  have eq581 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq41 -- superposition 41,11
  have eq958 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq581 eq14 -- superposition 14,581
  subsumption eq958 rfl

theorem Equation3253_4314_4512_implies_Equation307 (G : Type*) [Magma G]
    (h3253 : Equation3253 G) (h4314 : Equation4314 G) (h4512 : Equation4512 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h3253 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4314 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq15 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq12 eq12 -- superposition 12,12
  have eq16 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq12 eq12 -- superposition 12,12
  have eq17 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq18 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  have eq19 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq12 eq13 -- superposition 13,12
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq12 eq13 -- superposition 13,12
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := superpose eq11 eq13 -- superposition 13,11
  have eq23 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq12 eq13 -- superposition 13,12
  have eq32 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq13 eq18 -- forward demodulation 18,13
  have eq33 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq13 eq32 -- forward demodulation 32,13
  have eq34 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq13 eq19 -- forward demodulation 19,13
  have eq35 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq13 eq20 -- forward demodulation 20,13
  have eq38 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq35 eq22 -- forward demodulation 22,35
  have eq39 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq13 eq38 -- forward demodulation 38,13
  have eq40 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq13 eq39 -- forward demodulation 39,13
  have eq41 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq12 eq40 -- forward demodulation 40,12
  have eq42 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq13 eq41 -- forward demodulation 41,13
  have eq43 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq13 eq42 -- forward demodulation 42,13
  have eq108 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq12 eq34 -- superposition 34,12
  have eq119 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X0)) := superpose eq12 eq34 -- superposition 34,12
  have eq128 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) := superpose eq34 eq34 -- superposition 34,34
  have eq130 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) := superpose eq13 eq34 -- superposition 34,13
  have eq186 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) = ((X2 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) ◇ X3) := superpose eq13 eq128 -- forward demodulation 128,13
  have eq187 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) = ((X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) ◇ X3) := superpose eq13 eq186 -- forward demodulation 186,13
  have eq189 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3))))) := superpose eq13 eq130 -- forward demodulation 130,13
  have eq190 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3))))) := superpose eq13 eq189 -- forward demodulation 189,13
  have eq192 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) = ((X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1)) ◇ X3) := superpose eq190 eq187 -- backward demodulation 187,190
  have eq199 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) = ((X2 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1))) ◇ X3) := superpose eq13 eq192 -- forward demodulation 192,13
  have eq200 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) = ((X2 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1)))) ◇ X3) := superpose eq13 eq199 -- forward demodulation 199,13
  have eq201 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) = ((X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) ◇ X3) := superpose eq13 eq200 -- forward demodulation 200,13
  have eq202 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) = ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X3) := superpose eq11 eq201 -- forward demodulation 201,11
  have eq368 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq11 eq35 -- superposition 35,11
  have eq686 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq34 eq15 -- superposition 15,34
  have eq691 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq12 eq15 -- superposition 15,12
  have eq711 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq15 eq34 -- superposition 34,15
  have eq743 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq13 eq686 -- forward demodulation 686,13
  have eq744 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq119 eq743 -- forward demodulation 743,119
  have eq745 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = (X0 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0))) := superpose eq13 eq744 -- forward demodulation 744,13
  have eq746 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0)))) := superpose eq13 eq745 -- forward demodulation 745,13
  have eq747 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq13 eq746 -- forward demodulation 746,13
  have eq748 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq33 eq747 -- forward demodulation 747,33
  have eq769 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq13 eq691 -- forward demodulation 691,13
  have eq770 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq13 eq769 -- forward demodulation 769,13
  have eq771 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq11 eq770 -- forward demodulation 770,11
  have eq772 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq13 eq771 -- forward demodulation 771,13
  have eq773 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq13 eq772 -- forward demodulation 772,13
  have eq868 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq13 eq711 -- forward demodulation 711,13
  have eq869 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) := superpose eq748 eq868 -- forward demodulation 868,748
  have eq870 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq13 eq869 -- forward demodulation 869,13
  have eq871 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq11 eq870 -- forward demodulation 870,11
  have eq872 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq871 eq773 -- backward demodulation 773,871
  have eq975 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))) := superpose eq15 eq108 -- superposition 108,15
  have eq987 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))) := superpose eq108 eq15 -- superposition 15,108
  have eq1091 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq12 eq975 -- forward demodulation 975,12
  have eq1092 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq13 eq1091 -- forward demodulation 1091,13
  have eq1093 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq13 eq1092 -- forward demodulation 1092,13
  have eq1094 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq202 eq1093 -- forward demodulation 1093,202
  have eq1095 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq13 eq1094 -- forward demodulation 1094,13
  have eq1096 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq13 eq1095 -- forward demodulation 1095,13
  have eq1097 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq13 eq1096 -- forward demodulation 1096,13
  have eq1139 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq12 eq987 -- forward demodulation 987,12
  have eq1140 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq13 eq1139 -- forward demodulation 1139,13
  have eq1141 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq13 eq1140 -- forward demodulation 1140,13
  have eq1142 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq1097 eq1141 -- forward demodulation 1141,1097
  have eq1143 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq871 eq1142 -- forward demodulation 1142,871
  have eq1144 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq23 eq1143 -- forward demodulation 1143,23
  have eq1145 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq13 eq1144 -- forward demodulation 1144,13
  have eq1146 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq1145 eq43 -- backward demodulation 43,1145
  have eq1391 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq17 eq12 -- superposition 12,17
  have eq1640 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq13 eq1391 -- forward demodulation 1391,13
  have eq1641 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq11 eq1640 -- forward demodulation 1640,11
  have eq1642 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq872 eq1641 -- forward demodulation 1641,872
  have eq1643 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq368 eq1642 -- forward demodulation 1642,368
  have eq1646 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq1643 eq871 -- backward demodulation 871,1643
  have eq1652 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq1646 eq1146 -- backward demodulation 1146,1646
  have eq1954 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq1652 -- superposition 1652,11
  have eq2146 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq1954 eq14 -- superposition 14,1954
  subsumption eq2146 rfl

theorem Equation3253_4321_4512_implies_Equation307 (G : Type*) [Magma G]
    (h3253 : Equation3253 G) (h4321 : Equation4321 G) (h4512 : Equation4512 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h3253 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4321 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq35 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = ((X0 ◇ X0) ◇ X1) := superpose eq11 eq13 -- superposition 13,11
  have eq36 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq12 eq13 -- superposition 13,12
  have eq49 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose eq13 eq35 -- forward demodulation 35,13
  have eq50 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq13 eq49 -- forward demodulation 49,13
  have eq51 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq13 eq50 -- forward demodulation 50,13
  have eq52 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq13 eq36 -- forward demodulation 36,13
  have eq108 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = (((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq12 eq52 -- superposition 52,12
  have eq113 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq12 eq52 -- superposition 52,12
  have eq172 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X2) := superpose eq13 eq108 -- forward demodulation 108,13
  have eq173 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq13 eq172 -- forward demodulation 172,13
  have eq334 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) := superpose eq11 eq113 -- superposition 113,11
  have eq373 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1) = ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose eq52 eq334 -- forward demodulation 334,52
  have eq374 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1)) := superpose eq13 eq373 -- forward demodulation 373,13
  have eq375 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1) := superpose eq13 eq374 -- forward demodulation 374,13
  have eq376 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) := superpose eq13 eq375 -- forward demodulation 375,13
  have eq377 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1) := superpose eq13 eq376 -- forward demodulation 376,13
  have eq378 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1))) := superpose eq173 eq377 -- forward demodulation 377,173
  have eq379 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq13 eq378 -- forward demodulation 378,13
  have eq380 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq13 eq379 -- forward demodulation 379,13
  have eq381 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq51 eq380 -- forward demodulation 380,51
  have eq382 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq51 eq381 -- forward demodulation 381,51
  have eq1296 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq382 -- superposition 382,11
  have eq1886 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq1296 eq14 -- superposition 14,1296
  subsumption eq1886 rfl

theorem Equation3253_4343_4512_implies_Equation307 (G : Type*) [Magma G]
    (h3253 : Equation3253 G) (h4343 : Equation4343 G) (h4512 : Equation4512 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h3253 ..)
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4343 ..)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq20 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq12 eq13 -- superposition 13,12
  have eq41 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq13 eq20 -- forward demodulation 20,13
  have eq867 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq41 -- superposition 41,11
  have eq1203 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq867 eq14 -- superposition 14,867
  subsumption eq1203 rfl

theorem Equation3255_3258_4512_implies_Equation3261 (G : Type*) [Magma G]
    (h3255 : Equation3255 G) (h3258 : Equation3258 G) (h4512 : Equation4512 G) : Equation3261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h3255 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3258 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq17 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq13 eq13 -- superposition 13,13
  have eq18 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq15 eq17 -- forward demodulation 17,15
  have eq19 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq14 eq18 -- forward demodulation 18,14
  have eq20 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq15 eq19 -- forward demodulation 19,15
  have eq21 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq14 eq20 -- forward demodulation 20,14
  have eq25 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq14 eq15 -- superposition 15,14
  have eq28 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq13 eq15 -- superposition 15,13
  have eq30 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq13 -- superposition 13,15
  have eq36 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq15 eq25 -- forward demodulation 25,15
  have eq37 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq15 eq36 -- forward demodulation 36,15
  have eq38 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq15 eq37 -- forward demodulation 37,15
  have eq39 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq15 eq26 -- forward demodulation 26,15
  have eq40 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq15 eq39 -- forward demodulation 39,15
  have eq43 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) := superpose eq15 eq28 -- forward demodulation 28,15
  have eq44 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) := superpose eq15 eq43 -- forward demodulation 43,15
  have eq58 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq13 eq30 -- superposition 30,13
  have eq159 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq58 eq21 -- superposition 21,58
  have eq204 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq159 -- superposition 159,15
  have eq249 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X0 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq38 eq21 -- superposition 21,38
  have eq270 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X2)))) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X2))))) := superpose eq15 eq249 -- forward demodulation 249,15
  have eq271 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = ((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq40 eq270 -- forward demodulation 270,40
  have eq272 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = (X0 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq15 eq271 -- forward demodulation 271,15
  have eq273 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq40 eq272 -- forward demodulation 272,40
  have eq274 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ X1)) := superpose eq273 eq204 -- backward demodulation 204,273
  have eq276 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) := superpose eq274 eq44 -- backward demodulation 44,274
  have eq679 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq13 eq276 -- superposition 276,13
  have eq817 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq14 eq679 -- forward demodulation 679,14
  have eq818 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq817 eq16 -- backward demodulation 16,817
  subsumption eq818 eq14

theorem Equation3255_3316_4512_implies_Equation326 (G : Type*) [Magma G]
    (h3255 : Equation3255 G) (h3316 : Equation3316 G) (h4512 : Equation4512 G) : Equation326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h3255 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3316 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq33 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq14 eq15 -- superposition 15,14
  have eq35 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq13 eq15 -- superposition 15,13
  have eq38 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq13 -- superposition 13,15
  have eq46 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq15 eq33 -- forward demodulation 33,15
  have eq47 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq46 -- forward demodulation 46,15
  have eq50 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) := superpose eq15 eq35 -- forward demodulation 35,15
  have eq51 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) := superpose eq15 eq50 -- forward demodulation 50,15
  have eq52 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) := superpose eq14 eq51 -- forward demodulation 51,14
  have eq78 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq13 eq38 -- superposition 38,13
  have eq83 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq13 eq38 -- superposition 38,13
  have eq106 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq15 eq78 -- forward demodulation 78,15
  have eq107 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq15 eq106 -- forward demodulation 106,15
  have eq108 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq14 eq107 -- forward demodulation 107,14
  have eq115 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq83 eq108 -- backward demodulation 108,83
  have eq697 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq47 eq52 -- superposition 52,47
  have eq1084 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq115 eq697 -- superposition 697,115
  have eq1162 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq1084 -- forward demodulation 1084,15
  have eq1163 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq697 eq1162 -- forward demodulation 1162,697
  have eq1337 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq1163 eq16 -- superposition 16,1163
  subsumption eq1337 rfl

theorem Equation3255_4283_4512_implies_Equation308 (G : Type*) [Magma G]
    (h3255 : Equation3255 G) (h4283 : Equation4283 G) (h4512 : Equation4512 G) : Equation308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h3255 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4283 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq23 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq14 eq13 -- superposition 13,14
  have eq67 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq13 eq23 -- superposition 23,13
  have eq167 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq67 eq15 -- superposition 15,67
  have eq173 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq167 -- forward demodulation 167,15
  have eq174 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq23 eq173 -- forward demodulation 173,23
  have eq280 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq174 eq16 -- superposition 16,174
  subsumption eq280 rfl

theorem Equation3255_4284_4512_implies_Equation3258 (G : Type*) [Magma G]
    (h3255 : Equation3255 G) (h4284 : Equation4284 G) (h4512 : Equation4512 G) : Equation3258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h3255 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq25 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq14 eq13 -- superposition 13,14
  have eq30 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq15 eq25 -- forward demodulation 25,15
  have eq31 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq15 eq30 -- forward demodulation 30,15
  have eq32 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq13 eq31 -- forward demodulation 31,13
  have eq34 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq41 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq13 -- superposition 13,15
  have eq42 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq15 eq13 -- superposition 13,15
  have eq46 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq14 -- superposition 14,15
  have eq50 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq34 -- forward demodulation 34,15
  have eq60 (X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq41 eq32 -- backward demodulation 32,41
  have eq61 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq15 eq42 -- forward demodulation 42,15
  have eq72 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq60 eq14 -- superposition 14,60
  have eq468 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := superpose eq13 eq50 -- superposition 50,13
  have eq509 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq50 eq72 -- superposition 72,50
  have eq779 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq15 eq509 -- forward demodulation 509,15
  have eq780 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq15 eq779 -- forward demodulation 779,15
  have eq781 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq15 eq780 -- forward demodulation 780,15
  have eq782 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq61 eq781 -- forward demodulation 781,61
  have eq846 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq15 eq468 -- superposition 468,15
  have eq870 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq15 eq846 -- forward demodulation 846,15
  have eq871 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq870 eq782 -- backward demodulation 782,870
  have eq872 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq871 eq46 -- backward demodulation 46,871
  have eq1502 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := superpose eq872 eq16 -- superposition 16,872
  subsumption eq1502 eq13

theorem Equation3255_4290_4512_implies_Equation40 (G : Type*) [Magma G]
    (h3255 : Equation3255 G) (h4290 : Equation4290 G) (h4512 : Equation4512 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h3255 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq20 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq14 eq14 -- superposition 14,14
  have eq21 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq14 eq14 -- superposition 14,14
  have eq23 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq14 eq13 -- superposition 13,14
  have eq24 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq13 eq21 -- forward demodulation 21,13
  have eq25 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq24 -- forward demodulation 24,15
  have eq28 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq15 eq23 -- forward demodulation 23,15
  have eq29 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq14 eq28 -- forward demodulation 28,14
  have eq30 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq13 eq29 -- forward demodulation 29,13
  have eq31 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq45 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq15 eq31 -- forward demodulation 31,15
  have eq46 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq15 eq45 -- forward demodulation 45,15
  have eq47 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq15 eq46 -- forward demodulation 46,15
  have eq48 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq47 eq30 -- backward demodulation 30,47
  have eq49 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq48 eq25 -- backward demodulation 25,48
  have eq52 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq49 eq14 -- backward demodulation 14,49
  have eq53 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq49 eq20 -- backward demodulation 20,49
  have eq60 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq52 eq53 -- forward demodulation 53,52
  have eq127 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq49 eq60 -- superposition 60,49
  have eq186 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq127 eq16 -- superposition 16,127
  subsumption eq186 eq127

theorem Equation3255_4291_4512_implies_Equation309 (G : Type*) [Magma G]
    (h3255 : Equation3255 G) (h4291 : Equation4291 G) (h4512 : Equation4512 G) : Equation309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h3255 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq24 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq14 eq14 -- superposition 14,14
  have eq25 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq14 eq14 -- superposition 14,14
  have eq27 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq14 eq13 -- superposition 13,14
  have eq29 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq27 eq25 -- backward demodulation 25,27
  have eq30 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq43 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq15 eq30 -- forward demodulation 30,15
  have eq44 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq15 eq43 -- forward demodulation 43,15
  have eq45 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq15 eq44 -- forward demodulation 44,15
  have eq91 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq14 eq29 -- superposition 29,14
  have eq95 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq15 eq29 -- superposition 29,15
  have eq114 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq91 eq24 -- backward demodulation 24,91
  have eq132 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq27 eq95 -- forward demodulation 95,27
  have eq475 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq14 eq45 -- superposition 45,14
  have eq526 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq114 eq475 -- forward demodulation 475,114
  have eq527 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ X1) := superpose eq132 eq526 -- forward demodulation 526,132
  have eq614 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq527 eq16 -- superposition 16,527
  subsumption eq614 rfl

theorem Equation3255_4293_4512_implies_Equation40 (G : Type*) [Magma G]
    (h3255 : Equation3255 G) (h4293 : Equation4293 G) (h4512 : Equation4512 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h3255 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4293 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq29 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq30 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq38 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq13 -- superposition 13,15
  have eq43 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq15 eq29 -- forward demodulation 29,15
  have eq44 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq15 eq43 -- forward demodulation 43,15
  have eq45 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq15 eq44 -- forward demodulation 44,15
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq30 -- forward demodulation 30,15
  have eq63 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq15 eq38 -- superposition 38,15
  have eq66 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq14 eq38 -- superposition 38,14
  have eq69 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq13 eq38 -- superposition 38,13
  have eq120 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq14 eq45 -- superposition 45,14
  have eq139 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq63 eq120 -- forward demodulation 120,63
  have eq183 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq69 eq15 -- superposition 15,69
  have eq189 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq183 -- forward demodulation 183,15
  have eq191 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq189 eq66 -- backward demodulation 66,189
  have eq200 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq191 eq189 -- backward demodulation 189,191
  have eq203 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = ((X1 ◇ X1) ◇ X2) := superpose eq200 eq46 -- backward demodulation 46,200
  have eq204 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq200 eq139 -- backward demodulation 139,200
  have eq223 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X2)) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq203 eq203 -- superposition 203,203
  have eq272 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq203 eq69 -- superposition 69,203
  have eq286 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = ((X0 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq15 eq223 -- forward demodulation 223,15
  have eq287 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq200 eq286 -- forward demodulation 286,200
  have eq353 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq287 eq272 -- forward demodulation 272,287
  have eq354 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq200 eq353 -- forward demodulation 353,200
  have eq1422 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq204 eq354 -- superposition 354,204
  have eq1644 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq1422 eq16 -- superposition 16,1422
  subsumption eq1644 eq1422

theorem Equation3255_4314_4512_implies_Equation308 (G : Type*) [Magma G]
    (h3255 : Equation3255 G) (h4314 : Equation4314 G) (h4512 : Equation4512 G) : Equation308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h3255 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4314 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq24 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq14 eq14 -- superposition 14,14
  have eq25 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq14 eq13 -- superposition 13,14
  have eq27 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq14 eq13 -- superposition 13,14
  have eq28 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq24 -- forward demodulation 24,15
  have eq29 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq25 eq28 -- backward demodulation 28,25
  have eq33 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq15 eq27 -- forward demodulation 27,15
  have eq34 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq15 eq33 -- forward demodulation 33,15
  have eq35 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq13 eq34 -- forward demodulation 34,13
  have eq36 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq50 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq15 eq36 -- forward demodulation 36,15
  have eq51 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq15 eq50 -- forward demodulation 50,15
  have eq52 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq15 eq51 -- forward demodulation 51,15
  have eq53 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq52 eq35 -- backward demodulation 35,52
  have eq91 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq29 eq29 -- superposition 29,29
  have eq127 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq91 eq15 -- superposition 15,91
  have eq132 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq127 -- forward demodulation 127,15
  have eq133 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq53 eq132 -- forward demodulation 132,53
  have eq190 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq133 eq16 -- superposition 16,133
  subsumption eq190 rfl

theorem Equation3255_4320_4512_implies_Equation309 (G : Type*) [Magma G]
    (h3255 : Equation3255 G) (h4320 : Equation4320 G) (h4512 : Equation4512 G) : Equation309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h3255 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq24 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq13 eq14 -- superposition 14,13
  have eq25 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq14 eq14 -- superposition 14,14
  have eq28 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq14 eq13 -- superposition 13,14
  have eq29 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq14 eq13 -- superposition 13,14
  have eq31 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq15 eq24 -- forward demodulation 24,15
  have eq32 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))) := superpose eq14 eq31 -- forward demodulation 31,14
  have eq33 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq15 eq32 -- forward demodulation 32,15
  have eq34 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq14 eq33 -- forward demodulation 33,14
  have eq35 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq15 eq34 -- forward demodulation 34,15
  have eq36 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq13 eq35 -- forward demodulation 35,13
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq15 eq25 -- forward demodulation 25,15
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq15 eq29 -- forward demodulation 29,15
  have eq44 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq28 eq43 -- forward demodulation 43,28
  have eq45 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq15 eq44 -- forward demodulation 44,15
  have eq46 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq45 eq37 -- backward demodulation 37,45
  have eq47 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq46 eq36 -- backward demodulation 36,46
  have eq48 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq46 eq47 -- forward demodulation 47,46
  have eq49 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq48 eq46 -- backward demodulation 46,48
  have eq59 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq13 eq15 -- superposition 15,13
  have eq60 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq14 eq15 -- superposition 15,14
  have eq76 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) := superpose eq15 eq59 -- forward demodulation 59,15
  have eq77 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) := superpose eq15 eq76 -- forward demodulation 76,15
  have eq78 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) := superpose eq49 eq77 -- forward demodulation 77,49
  have eq79 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq60 -- forward demodulation 60,15
  have eq80 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = (X2 ◇ (X1 ◇ X1)) := superpose eq49 eq79 -- forward demodulation 79,49
  have eq81 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) := superpose eq80 eq78 -- backward demodulation 78,80
  have eq82 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq28 eq81 -- forward demodulation 81,28
  have eq83 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq82 eq14 -- backward demodulation 14,82
  have eq122 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq83 eq16 -- superposition 16,83
  subsumption eq122 rfl

theorem Equation3255_4321_4512_implies_Equation40 (G : Type*) [Magma G]
    (h3255 : Equation3255 G) (h4321 : Equation4321 G) (h4512 : Equation4512 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h3255 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4321 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq24 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq14 eq14 -- superposition 14,14
  have eq29 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq14 eq13 -- superposition 13,14
  have eq30 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq14 eq13 -- superposition 13,14
  have eq32 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq14 eq13 -- superposition 13,14
  have eq35 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq24 -- forward demodulation 24,15
  have eq41 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq15 eq30 -- forward demodulation 30,15
  have eq42 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq29 eq41 -- forward demodulation 41,29
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq15 eq42 -- forward demodulation 42,15
  have eq44 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq29 eq43 -- forward demodulation 43,29
  have eq45 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq15 eq32 -- forward demodulation 32,15
  have eq46 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq29 eq45 -- forward demodulation 45,29
  have eq47 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq44 eq46 -- forward demodulation 46,44
  have eq81 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq14 eq29 -- superposition 29,14
  have eq95 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq15 eq81 -- forward demodulation 81,15
  have eq96 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq29 eq95 -- forward demodulation 95,29
  have eq97 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq96 eq35 -- backward demodulation 35,96
  have eq146 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq96 eq15 -- superposition 15,96
  have eq157 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq15 eq146 -- forward demodulation 146,15
  have eq158 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq15 eq157 -- forward demodulation 157,15
  have eq245 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq15 eq44 -- superposition 44,15
  have eq292 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq96 eq245 -- forward demodulation 245,96
  have eq321 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq292 eq47 -- superposition 47,292
  have eq507 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq96 eq97 -- superposition 97,96
  have eq573 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq15 eq507 -- forward demodulation 507,15
  have eq574 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq15 eq573 -- forward demodulation 573,15
  have eq575 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq158 eq574 -- forward demodulation 574,158
  have eq576 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq14 eq575 -- forward demodulation 575,14
  have eq577 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq576 -- forward demodulation 576,15
  have eq578 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq13 eq577 -- forward demodulation 577,13
  have eq579 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq578 eq321 -- backward demodulation 321,578
  have eq1082 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq292 eq579 -- superposition 579,292
  have eq1539 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq1082 eq16 -- superposition 16,1082
  subsumption eq1539 eq1082

theorem Equation3255_4343_4512_implies_Equation40 (G : Type*) [Magma G]
    (h3255 : Equation3255 G) (h4343 : Equation4343 G) (h4512 : Equation4512 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h3255 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4343 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq23 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq14 eq13 -- superposition 13,14
  have eq24 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq14 eq13 -- superposition 13,14
  have eq25 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq15 eq23 -- forward demodulation 23,15
  have eq26 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq15 eq25 -- forward demodulation 25,15
  have eq27 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq13 eq26 -- forward demodulation 26,13
  have eq28 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq15 eq24 -- forward demodulation 24,15
  have eq29 (X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq27 eq28 -- forward demodulation 28,27
  have eq30 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq31 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq37 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq13 -- superposition 13,15
  have eq44 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq15 eq30 -- forward demodulation 30,15
  have eq45 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq15 eq44 -- forward demodulation 44,15
  have eq46 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq15 eq45 -- forward demodulation 45,15
  have eq47 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq31 -- forward demodulation 31,15
  have eq64 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq29 eq14 -- superposition 14,29
  have eq68 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq29 eq14 -- superposition 14,29
  have eq87 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq14 eq37 -- superposition 37,14
  have eq125 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq15 eq87 -- forward demodulation 87,15
  have eq126 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq64 eq125 -- forward demodulation 125,64
  have eq178 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq14 eq46 -- superposition 46,14
  have eq196 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq126 eq178 -- forward demodulation 178,126
  have eq204 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq196 eq47 -- backward demodulation 47,196
  have eq240 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq196 eq15 -- superposition 15,196
  have eq249 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq240 -- forward demodulation 240,15
  have eq250 (X0 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X2) := superpose eq196 eq249 -- forward demodulation 249,196
  have eq251 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq250 eq68 -- backward demodulation 68,250
  have eq255 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ X2) := superpose eq251 eq204 -- backward demodulation 204,251
  have eq278 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq29 eq255 -- superposition 255,29
  have eq531 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq251 eq278 -- superposition 278,251
  have eq705 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq531 eq16 -- superposition 16,531
  subsumption eq705 eq531

theorem Equation3256_3261_4512_implies_Equation3259 (G : Type*) [Magma G]
    (h3256 : Equation3256 G) (h3261 : Equation3261 G) (h4512 : Equation4512 G) : Equation3259 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h3256 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h3261 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2)))) := superpose eq13 eq15 -- superposition 15,13
  have eq30 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq15 eq14 -- superposition 14,15
  have eq40 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := superpose eq15 eq24 -- forward demodulation 24,15
  have eq41 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := superpose eq15 eq40 -- forward demodulation 40,15
  have eq47 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq15 eq30 -- forward demodulation 30,15
  have eq445 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq47 eq41 -- superposition 41,47
  have eq590 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq445 eq16 -- superposition 16,445
  subsumption eq590 rfl

theorem Equation3256_3278_4512_implies_Equation40 (G : Type*) [Magma G]
    (h3256 : Equation3256 G) (h3278 : Equation3278 G) (_ : Equation4512 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h3256 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3278 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq19 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq13 eq14 -- superposition 14,13
  have eq53 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq19 eq16 -- superposition 16,19
  subsumption eq53 eq19

theorem Equation3256_3306_4512_implies_Equation3331 (G : Type*) [Magma G]
    (h3256 : Equation3256 G) (h3306 : Equation3306 G) (h4512 : Equation4512 G) : Equation3331 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h3256 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := mod_symm (h3306 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq20 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq26 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq15 eq13 -- superposition 13,15
  have eq51 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq15 eq20 -- superposition 20,15
  have eq52 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq20 -- superposition 20,15
  have eq55 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq15 eq20 -- superposition 20,15
  have eq57 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq20 eq15 -- superposition 15,20
  have eq63 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq20 eq15 -- superposition 15,20
  have eq66 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq51 -- forward demodulation 51,15
  have eq67 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq20 eq55 -- forward demodulation 55,20
  have eq68 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq15 eq57 -- forward demodulation 57,15
  have eq70 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq15 eq63 -- forward demodulation 63,15
  have eq71 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ X2) := superpose eq14 eq70 -- forward demodulation 70,14
  have eq72 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq71 eq68 -- backward demodulation 68,71
  have eq73 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ X2)) := superpose eq72 eq67 -- backward demodulation 67,72
  have eq74 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq73 eq52 -- backward demodulation 52,73
  have eq76 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq74 eq66 -- backward demodulation 66,74
  have eq94 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq14 eq26 -- superposition 26,14
  have eq798 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X0))) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq94 eq72 -- superposition 72,94
  have eq849 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq76 eq798 -- forward demodulation 798,76
  have eq1048 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq849 eq16 -- superposition 16,849
  subsumption eq1048 rfl

theorem Equation3256_3315_4512_implies_Equation3323 (G : Type*) [Magma G]
    (h3256 : Equation3256 G) (h3315 : Equation3315 G) (h4512 : Equation4512 G) : Equation3323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h3256 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3315 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq23 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq14 eq15 -- superposition 15,14
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq15 eq23 -- forward demodulation 23,15
  have eq37 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq15 eq36 -- forward demodulation 36,15
  have eq38 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq15 eq37 -- forward demodulation 37,15
  have eq265 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ X1))) = (X0 ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq13 eq38 -- superposition 38,13
  have eq296 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq14 eq265 -- forward demodulation 265,14
  have eq365 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq296 eq16 -- superposition 16,296
  subsumption eq365 rfl

theorem Equation3256_3319_4512_implies_Equation3315 (G : Type*) [Magma G]
    (h3256 : Equation3256 G) (h3319 : Equation3319 G) (h4512 : Equation4512 G) : Equation3315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h3256 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := mod_symm (h3319 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) := superpose eq14 eq15 -- superposition 15,14
  have eq44 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) := superpose eq15 eq31 -- forward demodulation 31,15
  have eq45 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq15 eq44 -- forward demodulation 44,15
  have eq46 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq15 eq45 -- forward demodulation 45,15
  have eq174 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq13 eq46 -- superposition 46,13
  have eq193 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq14 eq174 -- forward demodulation 174,14
  have eq245 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq193 eq16 -- superposition 16,193
  subsumption eq245 rfl

theorem Equation3256_4283_4512_implies_Equation3259 (G : Type*) [Magma G]
    (h3256 : Equation3256 G) (h4283 : Equation4283 G) (h4512 : Equation4512 G) : Equation3259 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h3256 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq18 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq20 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq15 eq18 -- forward demodulation 18,15
  have eq59 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq14 eq20 -- superposition 20,14
  have eq213 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq59 eq16 -- superposition 16,59
  subsumption eq213 rfl

theorem Equation3256_4290_4512_implies_Equation40 (G : Type*) [Magma G]
    (h3256 : Equation3256 G) (h4290 : Equation4290 G) (h4512 : Equation4512 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h3256 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq19 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq67 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq15 eq19 -- superposition 19,15
  have eq113 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq13 eq67 -- superposition 67,13
  have eq194 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq113 eq16 -- superposition 16,113
  subsumption eq194 eq113

theorem Equation3256_4320_4512_implies_Equation40 (G : Type*) [Magma G]
    (h3256 : Equation3256 G) (h4320 : Equation4320 G) (h4512 : Equation4512 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h3256 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq19 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq14 eq14 -- superposition 14,14
  have eq22 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq14 eq13 -- superposition 13,14
  have eq29 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq15 eq19 -- forward demodulation 19,15
  have eq35 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq22 eq29 -- backward demodulation 29,22
  have eq42 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2)))) := superpose eq13 eq15 -- superposition 15,13
  have eq50 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2)))) := superpose eq15 eq13 -- superposition 13,15
  have eq60 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := superpose eq15 eq42 -- forward demodulation 42,15
  have eq61 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := superpose eq15 eq60 -- forward demodulation 60,15
  have eq62 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := superpose eq22 eq61 -- forward demodulation 61,22
  have eq74 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := superpose eq15 eq50 -- forward demodulation 50,15
  have eq75 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq62 eq74 -- forward demodulation 74,62
  have eq288 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq35 eq75 -- superposition 75,35
  have eq365 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq75 eq288 -- forward demodulation 288,75
  have eq917 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq75 eq365 -- superposition 365,75
  have eq1306 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq917 eq16 -- superposition 16,917
  subsumption eq1306 eq917

theorem Equation3258_3316_4512_implies_Equation323 (G : Type*) [Magma G]
    (h3258 : Equation3258 G) (h3316 : Equation3316 G) (h4512 : Equation4512 G) : Equation323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3258 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3316 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq22 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := superpose eq13 eq15 -- superposition 15,13
  have eq33 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq15 eq22 -- forward demodulation 22,15
  have eq34 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq15 eq33 -- forward demodulation 33,15
  have eq35 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq15 eq34 -- forward demodulation 34,15
  have eq40 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := superpose eq15 eq25 -- forward demodulation 25,15
  have eq41 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq14 eq40 -- forward demodulation 40,14
  have eq188 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq41 eq35 -- superposition 35,41
  have eq232 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq188 eq16 -- superposition 16,188
  subsumption eq232 rfl

theorem Equation3258_4283_4512_implies_Equation308 (G : Type*) [Magma G]
    (h3258 : Equation3258 G) (h4283 : Equation4283 G) (h4512 : Equation4512 G) : Equation308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3258 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq25 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq15 eq13 -- superposition 13,15
  have eq31 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq15 eq17 -- forward demodulation 17,15
  have eq32 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq15 eq31 -- forward demodulation 31,15
  have eq33 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq15 eq32 -- forward demodulation 32,15
  have eq49 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq13 eq25 -- superposition 25,13
  have eq50 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq14 eq25 -- superposition 25,14
  have eq59 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq15 eq50 -- forward demodulation 50,15
  have eq60 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq15 eq59 -- forward demodulation 59,15
  have eq61 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq33 eq60 -- forward demodulation 60,33
  have eq196 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq49 eq15 -- superposition 15,49
  have eq222 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq196 -- forward demodulation 196,15
  have eq223 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq61 eq222 -- forward demodulation 222,61
  have eq424 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq223 eq16 -- superposition 16,223
  subsumption eq424 rfl

theorem Equation3258_4284_4512_implies_Equation3255 (G : Type*) [Magma G]
    (h3258 : Equation3258 G) (h4284 : Equation4284 G) (h4512 : Equation4512 G) : Equation3255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3258 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq14 eq13 -- superposition 13,14
  have eq24 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq40 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq24 -- forward demodulation 24,15
  have eq405 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq40 -- superposition 40,19
  have eq733 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq15 eq405 -- superposition 405,15
  have eq769 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq15 eq733 -- forward demodulation 733,15
  have eq4067 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq769 eq16 -- superposition 16,769
  subsumption eq4067 rfl

theorem Equation3258_4290_4512_implies_Equation40 (G : Type*) [Magma G]
    (h3258 : Equation3258 G) (h4290 : Equation4290 G) (h4512 : Equation4512 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3258 ..)
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4290 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq17 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq14 eq14 -- superposition 14,14
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq14 eq13 -- superposition 13,14
  have eq21 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq22 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq21 -- forward demodulation 21,15
  have eq63 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq19 eq15 -- superposition 15,19
  have eq72 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq15 eq63 -- forward demodulation 63,15
  have eq73 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq72 -- forward demodulation 72,15
  have eq74 (X0 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X2) := superpose eq19 eq73 -- forward demodulation 73,19
  have eq75 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq74 eq22 -- backward demodulation 22,74
  have eq259 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq75 eq74 -- superposition 74,75
  have eq321 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq259 eq16 -- superposition 16,259
  subsumption eq321 eq259

theorem Equation3258_4291_4512_implies_Equation312 (G : Type*) [Magma G]
    (h3258 : Equation3258 G) (h4291 : Equation4291 G) (h4512 : Equation4512 G) : Equation312 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3258 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq28 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq15 eq13 -- superposition 13,15
  have eq45 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq13 eq28 -- superposition 28,13
  have eq48 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq13 eq28 -- superposition 28,13
  have eq57 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq45 -- forward demodulation 45,15
  have eq58 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq13 eq57 -- forward demodulation 57,13
  have eq59 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq48 eq17 -- backward demodulation 17,48
  have eq72 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq28 eq59 -- superposition 59,28
  have eq83 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq15 eq72 -- forward demodulation 72,15
  have eq84 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) := superpose eq15 eq83 -- forward demodulation 83,15
  have eq85 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq28 eq84 -- forward demodulation 84,28
  have eq86 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq58 eq85 -- forward demodulation 85,58
  have eq154 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq86 eq16 -- superposition 16,86
  subsumption eq154 rfl

theorem Equation3258_4293_4512_implies_Equation40 (G : Type*) [Magma G]
    (h3258 : Equation3258 G) (h4293 : Equation4293 G) (h4512 : Equation4512 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3258 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4293 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq25 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq15 eq13 -- superposition 13,15
  have eq31 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq15 eq17 -- forward demodulation 17,15
  have eq32 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq15 eq31 -- forward demodulation 31,15
  have eq33 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq15 eq32 -- forward demodulation 32,15
  have eq48 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq13 eq25 -- superposition 25,13
  have eq49 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0))) := superpose eq14 eq25 -- superposition 25,14
  have eq58 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0)))) := superpose eq15 eq49 -- forward demodulation 49,15
  have eq59 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq15 eq58 -- forward demodulation 58,15
  have eq60 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq33 eq59 -- forward demodulation 59,33
  have eq112 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq48 eq15 -- superposition 15,48
  have eq125 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq112 -- forward demodulation 112,15
  have eq126 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq60 eq125 -- forward demodulation 125,60
  have eq512 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose eq14 eq126 -- superposition 126,14
  have eq943 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq126 eq512 -- superposition 512,126
  have eq1318 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq943 eq16 -- superposition 16,943
  subsumption eq1318 eq943

theorem Equation3258_4314_4512_implies_Equation308 (G : Type*) [Magma G]
    (h3258 : Equation3258 G) (h4314 : Equation4314 G) (h4512 : Equation4512 G) : Equation308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3258 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4314 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq18 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq14 eq14 -- superposition 14,14
  have eq20 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq14 eq13 -- superposition 13,14
  have eq22 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq18 -- forward demodulation 18,15
  have eq29 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := superpose eq13 eq15 -- superposition 15,13
  have eq46 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := superpose eq15 eq29 -- forward demodulation 29,15
  have eq47 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) := superpose eq20 eq46 -- forward demodulation 46,20
  have eq57 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq14 eq20 -- superposition 20,14
  have eq59 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq20 -- superposition 20,15
  have eq65 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq15 eq57 -- forward demodulation 57,15
  have eq66 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq47 eq65 -- forward demodulation 65,47
  have eq70 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq59 -- forward demodulation 59,15
  have eq71 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq20 eq70 -- forward demodulation 70,20
  have eq116 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq66 eq66 -- superposition 66,66
  have eq117 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq14 eq66 -- superposition 66,14
  have eq138 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq116 eq22 -- backward demodulation 22,116
  have eq139 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq117 eq138 -- backward demodulation 138,117
  have eq174 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq139 eq15 -- superposition 15,139
  have eq179 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq174 -- forward demodulation 174,15
  have eq180 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq179 -- forward demodulation 179,15
  have eq188 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq117 -- superposition 117,15
  have eq197 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq117 eq15 -- superposition 15,117
  have eq204 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X2)) := superpose eq188 eq71 -- backward demodulation 71,188
  have eq210 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq15 eq197 -- forward demodulation 197,15
  have eq211 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq15 eq210 -- forward demodulation 210,15
  have eq436 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq204 -- superposition 204,15
  have eq505 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((X2 ◇ X3) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq211 eq436 -- forward demodulation 436,211
  have eq506 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq505 eq180 -- backward demodulation 180,505
  have eq731 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq506 eq16 -- superposition 16,506
  subsumption eq731 rfl

theorem Equation3258_4320_4512_implies_Equation309 (G : Type*) [Magma G]
    (h3258 : Equation3258 G) (h4320 : Equation4320 G) (h4512 : Equation4512 G) : Equation309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3258 ..)
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4320 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq14 eq14 -- superposition 14,14
  have eq22 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq14 eq13 -- superposition 13,14
  have eq23 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq15 eq17 -- forward demodulation 17,15
  have eq24 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq13 eq23 -- forward demodulation 23,13
  have eq34 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq15 eq22 -- forward demodulation 22,15
  have eq35 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq13 eq34 -- forward demodulation 34,13
  have eq36 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq35 eq24 -- backward demodulation 24,35
  have eq40 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq36 eq14 -- backward demodulation 14,36
  have eq48 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq40 eq16 -- superposition 16,40
  subsumption eq48 rfl

theorem Equation3258_4321_4512_implies_Equation40 (G : Type*) [Magma G]
    (h3258 : Equation3258 G) (h4321 : Equation4321 G) (h4512 : Equation4512 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3258 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4321 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq17 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq18 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq14 eq14 -- superposition 14,14
  have eq23 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq15 eq17 -- forward demodulation 17,15
  have eq24 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq15 eq23 -- forward demodulation 23,15
  have eq25 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq15 eq18 -- forward demodulation 18,15
  have eq26 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq35 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq36 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq47 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq14 -- superposition 14,15
  have eq49 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq15 eq35 -- forward demodulation 35,15
  have eq50 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq15 eq49 -- forward demodulation 49,15
  have eq51 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq15 eq50 -- forward demodulation 50,15
  have eq52 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq51 eq24 -- backward demodulation 24,51
  have eq53 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq15 eq36 -- forward demodulation 36,15
  have eq69 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq14 eq26 -- superposition 26,14
  have eq79 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq15 eq26 -- superposition 26,15
  have eq109 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq15 eq69 -- forward demodulation 69,15
  have eq110 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq15 eq109 -- forward demodulation 109,15
  have eq125 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq79 eq110 -- backward demodulation 110,79
  have eq126 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq125 eq52 -- backward demodulation 52,125
  have eq147 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq15 eq126 -- superposition 126,15
  have eq156 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq15 eq147 -- forward demodulation 147,15
  have eq157 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq79 eq156 -- forward demodulation 156,79
  have eq158 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq126 eq157 -- forward demodulation 157,126
  have eq161 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq158 eq79 -- backward demodulation 79,158
  have eq186 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq161 eq15 -- superposition 15,161
  have eq194 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq186 -- forward demodulation 186,15
  have eq427 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq126 eq47 -- superposition 47,126
  have eq428 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) = (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) := superpose eq26 eq47 -- superposition 47,26
  have eq508 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq15 eq427 -- forward demodulation 427,15
  have eq509 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq194 eq508 -- forward demodulation 508,194
  have eq510 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq194 eq509 -- forward demodulation 509,194
  have eq511 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := superpose eq161 eq510 -- forward demodulation 510,161
  have eq512 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq161 eq511 -- forward demodulation 511,161
  have eq526 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)))) := superpose eq15 eq428 -- forward demodulation 428,15
  have eq527 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))))) := superpose eq15 eq526 -- forward demodulation 526,15
  have eq528 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))))) := superpose eq15 eq527 -- forward demodulation 527,15
  have eq529 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))))) := superpose eq161 eq528 -- forward demodulation 528,161
  have eq530 (X0 X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))))) := superpose eq161 eq529 -- forward demodulation 529,161
  have eq691 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq53 eq512 -- superposition 512,53
  have eq719 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq15 eq691 -- forward demodulation 691,15
  have eq720 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq719 -- forward demodulation 719,15
  have eq721 (X0 X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := superpose eq720 eq530 -- backward demodulation 530,720
  have eq1208 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq721 eq721 -- superposition 721,721
  have eq1536 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq1208 eq16 -- superposition 16,1208
  subsumption eq1536 eq1208

theorem Equation3258_4343_4512_implies_Equation40 (G : Type*) [Magma G]
    (h3258 : Equation3258 G) (h4343 : Equation4343 G) (h4512 : Equation4512 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3258 ..)
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4343 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq14 eq13 -- superposition 13,14
  have eq35 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq15 eq13 -- superposition 13,15
  have eq109 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ X1) := superpose eq19 eq35 -- superposition 35,19
  have eq147 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq14 eq109 -- superposition 109,14
  have eq310 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq109 eq147 -- superposition 147,109
  have eq524 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq310 eq16 -- superposition 16,310
  subsumption eq524 eq310

theorem Equation3261_3278_4512_implies_Equation3271 (G : Type*) [Magma G]
    (h3261 : Equation3261 G) (h3278 : Equation3278 G) (h4512 : Equation4512 G) : Equation3271 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h3261 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3278 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq17 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq13 eq13 -- superposition 13,13
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq19 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = ((X1 ◇ X1) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq27 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq15 eq14 -- superposition 14,15
  have eq29 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq15 eq18 -- forward demodulation 18,15
  have eq30 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq15 eq29 -- forward demodulation 29,15
  have eq31 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq15 eq30 -- forward demodulation 30,15
  have eq32 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X1 ◇ (X1 ◇ X2)) := superpose eq15 eq19 -- forward demodulation 19,15
  have eq33 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := superpose eq15 eq32 -- forward demodulation 32,15
  have eq34 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq15 eq33 -- forward demodulation 33,15
  have eq107 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq31 eq27 -- superposition 27,31
  have eq120 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq15 eq107 -- forward demodulation 107,15
  have eq121 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq120 eq17 -- backward demodulation 17,120
  have eq168 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq14 eq34 -- superposition 34,14
  have eq179 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq13 eq34 -- superposition 34,13
  have eq241 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2)))) := superpose eq179 eq27 -- superposition 27,179
  have eq259 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2))))) := superpose eq15 eq241 -- forward demodulation 241,15
  have eq260 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq168 eq259 -- forward demodulation 259,168
  have eq261 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq260 eq121 -- backward demodulation 121,260
  have eq297 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq261 eq16 -- superposition 16,261
  subsumption eq297 rfl

theorem Equation3261_3306_4512_implies_Equation3334 (G : Type*) [Magma G]
    (h3261 : Equation3261 G) (h3306 : Equation3306 G) (h4512 : Equation4512 G) : Equation3334 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h3261 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := mod_symm (h3306 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq26 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq13 -- superposition 13,15
  have eq31 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq15 eq20 -- forward demodulation 20,15
  have eq32 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq15 eq31 -- forward demodulation 31,15
  have eq33 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq15 eq32 -- forward demodulation 32,15
  have eq42 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq15 eq26 -- forward demodulation 26,15
  have eq52 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq13 eq33 -- superposition 33,13
  have eq63 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq14 eq52 -- forward demodulation 52,14
  have eq103 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq42 eq33 -- superposition 33,42
  have eq107 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq42 eq33 -- superposition 33,42
  have eq131 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq63 eq107 -- forward demodulation 107,63
  have eq359 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq103 eq15 -- superposition 15,103
  have eq455 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq15 eq359 -- forward demodulation 359,15
  have eq456 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) := superpose eq15 eq455 -- forward demodulation 455,15
  have eq457 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq15 eq456 -- forward demodulation 456,15
  have eq458 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq15 eq457 -- forward demodulation 457,15
  have eq459 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq15 eq458 -- forward demodulation 458,15
  have eq460 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq131 eq459 -- forward demodulation 459,131
  have eq609 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq460 eq16 -- superposition 16,460
  subsumption eq609 rfl

theorem Equation3261_3315_4512_implies_Equation3256 (G : Type*) [Magma G]
    (h3261 : Equation3261 G) (h3315 : Equation3315 G) (h4512 : Equation4512 G) : Equation3256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h3261 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3315 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq32 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq15 eq14 -- superposition 14,15
  have eq34 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq15 eq23 -- forward demodulation 23,15
  have eq35 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq15 eq34 -- forward demodulation 34,15
  have eq36 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq15 eq35 -- forward demodulation 35,15
  have eq121 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose eq32 eq36 -- superposition 36,32
  have eq137 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq121 eq16 -- backward demodulation 16,121
  subsumption eq137 eq13

theorem Equation3261_3319_4512_implies_Equation3306 (G : Type*) [Magma G]
    (h3261 : Equation3261 G) (h3319 : Equation3319 G) (h4512 : Equation4512 G) : Equation3306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h3261 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := mod_symm (h3319 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq32 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq43 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq15 eq32 -- forward demodulation 32,15
  have eq44 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq15 eq43 -- forward demodulation 43,15
  have eq45 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq15 eq44 -- forward demodulation 44,15
  have eq165 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq45 -- superposition 45,13
  have eq180 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq14 eq165 -- forward demodulation 165,14
  have eq560 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq180 eq16 -- superposition 16,180
  subsumption eq560 rfl

theorem Equation3261_3346_4512_implies_Equation3388 (G : Type*) [Magma G]
    (h3261 : Equation3261 G) (h3346 : Equation3346 G) (h4512 : Equation4512 G) : Equation3388 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h3261 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h3346 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq24 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X1 ◇ X0) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq27 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := superpose eq14 eq15 -- superposition 15,14
  have eq28 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq13 -- superposition 13,15
  have eq34 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq15 eq23 -- forward demodulation 23,15
  have eq35 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq15 eq34 -- forward demodulation 34,15
  have eq36 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq15 eq35 -- forward demodulation 35,15
  have eq37 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq15 eq24 -- forward demodulation 24,15
  have eq38 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq15 eq37 -- forward demodulation 37,15
  have eq39 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq15 eq38 -- forward demodulation 38,15
  have eq44 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := superpose eq15 eq27 -- forward demodulation 27,15
  have eq45 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq15 eq28 -- forward demodulation 28,15
  have eq90 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq14 eq39 -- superposition 39,14
  have eq102 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq36 eq39 -- superposition 39,36
  have eq172 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq45 eq39 -- superposition 39,45
  have eq207 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X0))) = (X2 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq90 eq172 -- forward demodulation 172,90
  have eq208 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq14 eq207 -- forward demodulation 207,14
  have eq213 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq208 eq102 -- backward demodulation 102,208
  have eq228 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) := superpose eq213 eq44 -- backward demodulation 44,213
  have eq238 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq14 eq228 -- forward demodulation 228,14
  have eq315 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := superpose eq238 eq16 -- superposition 16,238
  subsumption eq315 eq208

theorem Equation3261_3353_4512_implies_Equation3346 (G : Type*) [Magma G]
    (h3261 : Equation3261 G) (h3353 : Equation3353 G) (h4512 : Equation4512 G) : Equation3346 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h3261 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3353 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq14 eq14 -- superposition 14,14
  have eq22 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq15 eq19 -- forward demodulation 19,15
  have eq23 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq15 eq22 -- forward demodulation 22,15
  have eq24 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq29 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq14 -- superposition 14,15
  have eq35 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq15 eq24 -- forward demodulation 24,15
  have eq36 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq15 eq35 -- forward demodulation 35,15
  have eq37 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq15 eq36 -- forward demodulation 36,15
  have eq54 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq14 eq29 -- superposition 29,14
  have eq57 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq13 eq29 -- superposition 29,13
  have eq71 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq15 eq54 -- forward demodulation 54,15
  have eq88 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq37 -- superposition 37,13
  have eq124 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (X2 ◇ (X2 ◇ X2)) := superpose eq15 eq57 -- superposition 57,15
  have eq125 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq57 -- superposition 57,15
  have eq149 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X2 ◇ (X2 ◇ X2)) := superpose eq15 eq124 -- forward demodulation 124,15
  have eq150 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq149 eq23 -- backward demodulation 23,149
  have eq151 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq71 eq125 -- forward demodulation 125,71
  have eq159 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq151 eq88 -- backward demodulation 88,151
  have eq396 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq15 eq150 -- superposition 150,15
  have eq473 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq159 eq396 -- forward demodulation 396,159
  have eq474 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq473 -- forward demodulation 473,15
  have eq919 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq474 eq16 -- superposition 16,474
  subsumption eq919 rfl

theorem Equation3261_4283_4512_implies_Equation3256 (G : Type*) [Magma G]
    (h3261 : Equation3261 G) (h4283 : Equation4283 G) (h4512 : Equation4512 G) : Equation3256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h3261 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq18 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq14 eq13 -- superposition 13,14
  have eq29 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq13 eq15 -- superposition 15,13
  have eq32 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq14 -- superposition 14,15
  have eq37 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq15 eq13 -- superposition 13,15
  have eq46 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq15 eq29 -- forward demodulation 29,15
  have eq47 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq18 eq46 -- forward demodulation 46,18
  have eq54 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq47 eq37 -- forward demodulation 37,47
  have eq486 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq54 eq32 -- superposition 32,54
  have eq619 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq15 eq486 -- forward demodulation 486,15
  have eq620 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := superpose eq18 eq619 -- forward demodulation 619,18
  have eq621 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq620 eq16 -- backward demodulation 16,620
  subsumption eq621 eq13

theorem Equation3261_4290_4512_implies_Equation40 (G : Type*) [Magma G]
    (h3261 : Equation3261 G) (h4290 : Equation4290 G) (_ : Equation4512 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h3261 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq18 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq14 eq14 -- superposition 14,14
  have eq22 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq14 eq13 -- superposition 13,14
  have eq23 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq13 eq18 -- forward demodulation 18,13
  have eq27 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq13 eq22 -- forward demodulation 22,13
  have eq28 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq23 eq27 -- forward demodulation 27,23
  have eq114 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq23 eq28 -- superposition 28,23
  have eq206 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq114 eq16 -- superposition 16,114
  subsumption eq206 eq114

theorem Equation3261_4320_4512_implies_Equation3271 (G : Type*) [Magma G]
    (h3261 : Equation3261 G) (h4320 : Equation4320 G) (h4512 : Equation4512 G) : Equation3271 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h3261 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq23 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq14 eq13 -- superposition 13,14
  have eq37 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X1 ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq14 eq23 -- forward demodulation 23,14
  have eq38 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq15 eq37 -- forward demodulation 37,15
  have eq39 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq13 eq38 -- forward demodulation 38,13
  have eq45 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq14 eq15 -- superposition 15,14
  have eq46 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq14 eq15 -- superposition 15,14
  have eq48 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq13 -- superposition 13,15
  have eq63 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq45 -- forward demodulation 45,15
  have eq64 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq46 -- forward demodulation 46,15
  have eq65 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq15 eq48 -- forward demodulation 48,15
  have eq197 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq14 eq39 -- superposition 39,14
  have eq217 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) := superpose eq39 eq15 -- superposition 15,39
  have eq218 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq39 eq14 -- superposition 14,39
  have eq237 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))) := superpose eq64 eq197 -- forward demodulation 197,64
  have eq238 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq15 eq237 -- forward demodulation 237,15
  have eq239 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq65 eq238 -- forward demodulation 238,65
  have eq300 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) := superpose eq15 eq217 -- forward demodulation 217,15
  have eq301 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq15 eq300 -- forward demodulation 300,15
  have eq302 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq15 eq301 -- forward demodulation 301,15
  have eq303 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq15 eq302 -- forward demodulation 302,15
  have eq304 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))))) := superpose eq63 eq218 -- forward demodulation 218,63
  have eq305 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)))))) := superpose eq15 eq304 -- forward demodulation 304,15
  have eq306 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))))) := superpose eq15 eq305 -- forward demodulation 305,15
  have eq307 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) = ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq303 eq306 -- forward demodulation 306,303
  have eq308 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq239 eq307 -- forward demodulation 307,239
  have eq309 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq15 eq308 -- forward demodulation 308,15
  have eq310 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq65 eq309 -- forward demodulation 309,65
  have eq359 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq310 eq16 -- superposition 16,310
  subsumption eq359 rfl

theorem Equation3278_3306_4512_implies_Equation3414 (G : Type*) [Magma G]
    (h3278 : Equation3278 G) (h3306 : Equation3306 G) (h4512 : Equation4512 G) : Equation3414 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3278 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := mod_symm (h3306 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq19 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = ((X1 ◇ X1) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq30 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X1 ◇ (X1 ◇ X2)) := superpose eq15 eq19 -- forward demodulation 19,15
  have eq31 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := superpose eq15 eq30 -- forward demodulation 30,15
  have eq32 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq15 eq31 -- forward demodulation 31,15
  have eq96 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq14 eq32 -- superposition 32,14
  have eq244 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq96 eq16 -- superposition 16,96
  subsumption eq244 rfl

theorem Equation3278_3319_4512_implies_Equation3261 (G : Type*) [Magma G]
    (h3278 : Equation3278 G) (h3319 : Equation3319 G) (h4512 : Equation4512 G) : Equation3261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3278 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := mod_symm (h3319 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq27 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = ((X1 ◇ X1) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq38 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X1 ◇ (X1 ◇ X2)) := superpose eq15 eq27 -- forward demodulation 27,15
  have eq39 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := superpose eq15 eq38 -- forward demodulation 38,15
  have eq40 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq15 eq39 -- forward demodulation 39,15
  have eq112 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose eq14 eq40 -- superposition 40,14
  have eq124 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq112 eq16 -- backward demodulation 16,112
  subsumption eq124 eq13

theorem Equation3278_4283_4512_implies_Equation40 (G : Type*) [Magma G]
    (h3278 : Equation3278 G) (h4283 : Equation4283 G) (h4512 : Equation4512 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3278 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq17 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq15 eq17 -- forward demodulation 17,15
  have eq54 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq13 eq19 -- superposition 19,13
  have eq130 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq54 eq54 -- superposition 54,54
  have eq355 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq130 eq16 -- superposition 16,130
  subsumption eq355 eq130

theorem Equation3278_4290_4512_implies_Equation40 (G : Type*) [Magma G]
    (h3278 : Equation3278 G) (h4290 : Equation4290 G) (h4512 : Equation4512 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3278 ..)
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4290 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq63 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq15 eq19 -- superposition 19,15
  have eq105 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq13 eq63 -- superposition 63,13
  have eq191 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq105 eq16 -- superposition 16,105
  subsumption eq191 eq105

theorem Equation3278_4320_4512_implies_Equation3261 (G : Type*) [Magma G]
    (h3278 : Equation3278 G) (h4320 : Equation4320 G) (h4512 : Equation4512 G) : Equation3261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3278 ..)
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4320 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq19 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq14 eq14 -- superposition 14,14
  have eq21 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq14 eq13 -- superposition 13,14
  have eq30 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) := superpose eq14 eq19 -- forward demodulation 19,14
  have eq31 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq15 eq30 -- forward demodulation 30,15
  have eq32 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq13 eq31 -- forward demodulation 31,13
  have eq43 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq14 eq15 -- superposition 15,14
  have eq60 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq43 -- forward demodulation 43,15
  have eq61 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = (X2 ◇ (X1 ◇ X1)) := superpose eq21 eq60 -- forward demodulation 60,21
  have eq76 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq15 eq21 -- superposition 21,15
  have eq78 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq21 eq15 -- superposition 15,21
  have eq95 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq61 eq76 -- forward demodulation 76,61
  have eq96 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq13 eq95 -- forward demodulation 95,13
  have eq99 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq15 eq78 -- forward demodulation 78,15
  have eq100 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq99 -- forward demodulation 99,15
  have eq101 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq100 -- forward demodulation 100,15
  have eq185 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq32 eq96 -- superposition 96,32
  have eq258 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq185 -- forward demodulation 185,15
  have eq259 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq96 eq258 -- forward demodulation 258,96
  have eq260 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq14 eq259 -- forward demodulation 259,14
  have eq261 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq15 eq260 -- forward demodulation 260,15
  have eq262 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq101 eq261 -- forward demodulation 261,101
  have eq263 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq96 eq262 -- forward demodulation 262,96
  have eq292 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq263 eq16 -- superposition 16,263
  subsumption eq292 rfl

theorem Equation3306_4283_4512_implies_Equation3308 (G : Type*) [Magma G]
    (h3306 : Equation3306 G) (h4283 : Equation4283 G) (_ : Equation4512 G) : Equation3308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := mod_symm (h3306 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq17 eq13

theorem Equation3306_4290_4512_implies_Equation43 (G : Type*) [Magma G]
    (h3306 : Equation3306 G) (h4290 : Equation4290 G) (h4512 : Equation4512 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := mod_symm (h3306 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq18 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq14 eq14 -- superposition 14,14
  have eq20 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq14 eq13 -- superposition 13,14
  have eq22 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq14 eq13 -- superposition 13,14
  have eq28 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq13 eq15 -- superposition 15,13
  have eq31 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq14 eq15 -- superposition 15,14
  have eq32 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq14 eq15 -- superposition 15,14
  have eq33 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq14 -- superposition 14,15
  have eq43 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq28 -- forward demodulation 28,15
  have eq46 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))) := superpose eq15 eq30 -- forward demodulation 30,15
  have eq47 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) := superpose eq15 eq46 -- forward demodulation 46,15
  have eq48 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq31 -- forward demodulation 31,15
  have eq49 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq48 -- forward demodulation 48,15
  have eq50 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq33 -- forward demodulation 33,15
  have eq64 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq20 eq15 -- superposition 15,20
  have eq73 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq15 eq64 -- forward demodulation 64,15
  have eq74 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq15 eq73 -- forward demodulation 73,15
  have eq75 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq15 eq74 -- forward demodulation 74,15
  have eq194 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2)) := superpose eq22 eq15 -- superposition 15,22
  have eq232 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2))) := superpose eq15 eq194 -- forward demodulation 194,15
  have eq233 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq15 eq232 -- forward demodulation 232,15
  have eq234 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq15 eq233 -- forward demodulation 233,15
  have eq351 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = (X2 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq14 eq32 -- superposition 32,14
  have eq812 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq13 eq43 -- superposition 43,13
  have eq928 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq15 eq812 -- forward demodulation 812,15
  have eq1149 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))))) := superpose eq14 eq47 -- superposition 47,14
  have eq1238 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq75 eq1149 -- forward demodulation 1149,75
  have eq1607 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq32 eq49 -- superposition 49,32
  have eq1893 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq14 eq1607 -- forward demodulation 1607,14
  have eq1894 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq1238 eq1893 -- forward demodulation 1893,1238
  have eq1895 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose eq13 eq1894 -- forward demodulation 1894,13
  have eq2200 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq1895 eq13 -- superposition 13,1895
  have eq2217 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) := superpose eq1895 eq43 -- superposition 43,1895
  have eq2231 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq1895 eq22 -- superposition 22,1895
  have eq2311 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq15 eq2217 -- forward demodulation 2217,15
  have eq2312 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq15 eq2311 -- forward demodulation 2311,15
  have eq2313 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq15 eq2312 -- forward demodulation 2312,15
  have eq2314 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq928 eq2313 -- forward demodulation 2313,928
  have eq2342 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))))) := superpose eq351 eq2231 -- forward demodulation 2231,351
  have eq2343 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq2314 eq2342 -- forward demodulation 2342,2314
  have eq2344 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq2343 -- forward demodulation 2343,15
  have eq2345 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq13 eq2344 -- forward demodulation 2344,13
  have eq2394 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq18 eq50 -- superposition 50,18
  have eq2555 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq32 eq2394 -- forward demodulation 2394,32
  have eq2556 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq14 eq2555 -- forward demodulation 2555,14
  have eq2557 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq234 eq2556 -- forward demodulation 2556,234
  have eq2558 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq2345 eq2557 -- forward demodulation 2557,2345
  have eq4876 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq2558 eq2200 -- superposition 2200,2558
  have eq5634 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq4876 eq16 -- superposition 16,4876
  subsumption eq5634 rfl

theorem Equation3315_3353_4512_implies_Equation43 (G : Type*) [Magma G]
    (h3315 : Equation3315 G) (h3353 : Equation3353 G) (h4512 : Equation4512 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3315 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3353 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq14 eq14 -- superposition 14,14
  have eq23 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq15 eq20 -- forward demodulation 20,15
  have eq24 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq15 eq23 -- forward demodulation 23,15
  have eq28 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := superpose eq13 eq15 -- superposition 15,13
  have eq44 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := superpose eq15 eq28 -- forward demodulation 28,15
  have eq45 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := superpose eq15 eq44 -- forward demodulation 44,15
  have eq660 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq15 eq24 -- superposition 24,15
  have eq812 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))))) := superpose eq15 eq660 -- forward demodulation 660,15
  have eq813 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ X0) := superpose eq45 eq812 -- forward demodulation 812,45
  have eq1549 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq13 eq813 -- superposition 813,13
  have eq2042 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq1549 eq16 -- superposition 16,1549
  subsumption eq2042 rfl

theorem Equation3315_4283_4512_implies_Equation3306 (G : Type*) [Magma G]
    (h3315 : Equation3315 G) (h4283 : Equation4283 G) (h4512 : Equation4512 G) : Equation3306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3315 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq31 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq14 -- superposition 14,15
  have eq110 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq14 eq31 -- superposition 31,14
  have eq169 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq13 eq110 -- forward demodulation 110,13
  have eq697 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq169 eq16 -- superposition 16,169
  subsumption eq697 rfl

theorem Equation3316_4283_4512_implies_Equation323 (G : Type*) [Magma G]
    (h3316 : Equation3316 G) (h4283 : Equation4283 G) (h4512 : Equation4512 G) : Equation323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3316 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq22 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq14 eq13 -- superposition 13,14
  have eq27 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq13 eq15 -- superposition 15,13
  have eq34 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq14 -- superposition 14,15
  have eq41 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq15 eq27 -- forward demodulation 27,15
  have eq42 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq41 -- forward demodulation 41,15
  have eq61 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq22 -- superposition 22,15
  have eq77 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq15 eq61 -- forward demodulation 61,15
  have eq78 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq42 eq77 -- forward demodulation 77,42
  have eq80 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq78 eq34 -- backward demodulation 34,78
  have eq164 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq13 eq80 -- superposition 80,13
  have eq245 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq164 eq16 -- superposition 16,164
  subsumption eq245 rfl

theorem Equation3316_4284_4512_implies_Equation323 (G : Type*) [Magma G]
    (h3316 : Equation3316 G) (h4284 : Equation4284 G) (h4512 : Equation4512 G) : Equation323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3316 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq20 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq14 eq14 -- superposition 14,14
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq15 eq20 -- forward demodulation 20,15
  have eq24 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq13 eq23 -- forward demodulation 23,13
  have eq40 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq14 -- superposition 14,15
  have eq59 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq13 eq40 -- forward demodulation 40,13
  have eq66 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq13 eq24 -- superposition 24,13
  have eq91 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq59 eq66 -- forward demodulation 66,59
  have eq92 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq15 eq91 -- forward demodulation 91,15
  have eq93 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ X1)) := superpose eq13 eq92 -- forward demodulation 92,13
  have eq94 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq13 eq93 -- forward demodulation 93,13
  have eq176 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq94 eq16 -- superposition 16,94
  subsumption eq176 rfl

theorem Equation3316_4290_4512_implies_Equation43 (G : Type*) [Magma G]
    (h3316 : Equation3316 G) (h4290 : Equation4290 G) (h4512 : Equation4512 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3316 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq24 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq14 eq13 -- superposition 13,14
  have eq28 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq15 eq24 -- forward demodulation 24,15
  have eq29 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq13 eq15 -- superposition 15,13
  have eq35 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq14 eq15 -- superposition 15,14
  have eq43 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq15 eq29 -- forward demodulation 29,15
  have eq44 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq43 -- forward demodulation 43,15
  have eq45 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq44 eq28 -- backward demodulation 28,44
  have eq52 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq35 -- forward demodulation 35,15
  have eq53 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq44 eq52 -- forward demodulation 52,44
  have eq54 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq53 -- forward demodulation 53,15
  have eq55 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := superpose eq13 eq54 -- forward demodulation 54,13
  have eq86 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq55 eq13 -- superposition 13,55
  have eq109 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq86 eq45 -- backward demodulation 45,86
  have eq115 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose eq109 eq86 -- backward demodulation 86,109
  have eq271 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq109 eq115 -- superposition 115,109
  have eq413 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq271 eq16 -- superposition 16,271
  subsumption eq413 rfl

theorem Equation3316_4291_4512_implies_Equation323 (G : Type*) [Magma G]
    (h3316 : Equation3316 G) (h4291 : Equation4291 G) (h4512 : Equation4512 G) : Equation323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3316 ..)
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq21 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq23 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq14 eq14 -- superposition 14,14
  have eq26 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq14 eq13 -- superposition 13,14
  have eq27 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq13 eq23 -- forward demodulation 23,13
  have eq30 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq14 eq26 -- forward demodulation 26,14
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq13 eq15 -- superposition 15,13
  have eq37 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq14 eq15 -- superposition 15,14
  have eq44 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq15 eq31 -- forward demodulation 31,15
  have eq45 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq44 -- forward demodulation 44,15
  have eq51 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq37 -- forward demodulation 37,15
  have eq52 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq45 eq51 -- forward demodulation 51,45
  have eq56 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq52 eq30 -- backward demodulation 30,52
  have eq57 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq13 eq56 -- forward demodulation 56,13
  have eq59 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq57 eq27 -- backward demodulation 27,57
  have eq60 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq57 eq21 -- backward demodulation 21,57
  have eq67 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq59 eq60 -- forward demodulation 60,59
  have eq95 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq67 eq16 -- superposition 16,67
  subsumption eq95 rfl

theorem Equation3316_4293_4512_implies_Equation43 (G : Type*) [Magma G]
    (h3316 : Equation3316 G) (h4293 : Equation4293 G) (h4512 : Equation4512 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3316 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4293 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq13 eq15 -- superposition 15,13
  have eq30 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq14 eq15 -- superposition 15,14
  have eq39 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq15 eq25 -- forward demodulation 25,15
  have eq40 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq39 -- forward demodulation 39,15
  have eq46 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq30 -- forward demodulation 30,15
  have eq47 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq40 eq46 -- forward demodulation 46,40
  have eq65 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq13 eq47 -- superposition 47,13
  have eq94 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq15 eq65 -- forward demodulation 65,15
  have eq95 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ X0) := superpose eq13 eq94 -- forward demodulation 94,13
  have eq98 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose eq95 eq14 -- backward demodulation 14,95
  have eq143 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq98 eq95 -- superposition 95,98
  have eq219 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq143 eq16 -- superposition 16,143
  subsumption eq219 rfl

theorem Equation3316_4314_4512_implies_Equation325 (G : Type*) [Magma G]
    (h3316 : Equation3316 G) (h4314 : Equation4314 G) (h4512 : Equation4512 G) : Equation325 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3316 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4314 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq13 eq13 -- superposition 13,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq15 eq17 -- forward demodulation 17,15
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq14 eq18 -- forward demodulation 18,14
  have eq20 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq15 eq19 -- forward demodulation 19,15
  have eq24 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq14 eq13 -- superposition 13,14
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq24 eq20 -- backward demodulation 20,24
  have eq52 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq28 eq16 -- superposition 16,28
  subsumption eq52 rfl

theorem Equation3316_4320_4512_implies_Equation326 (G : Type*) [Magma G]
    (h3316 : Equation3316 G) (h4320 : Equation4320 G) (h4512 : Equation4512 G) : Equation326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3316 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq21 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq13 eq14 -- superposition 14,13
  have eq28 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq15 eq21 -- forward demodulation 21,15
  have eq29 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq13 eq28 -- forward demodulation 28,13
  have eq30 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq13 eq29 -- forward demodulation 29,13
  have eq118 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq15 eq30 -- superposition 30,15
  have eq144 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq15 eq118 -- forward demodulation 118,15
  have eq145 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq13 eq144 -- forward demodulation 144,13
  have eq147 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq145 eq14 -- backward demodulation 14,145
  have eq201 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq147 eq16 -- superposition 16,147
  subsumption eq201 rfl

theorem Equation3316_4321_4512_implies_Equation43 (G : Type*) [Magma G]
    (h3316 : Equation3316 G) (h4321 : Equation4321 G) (h4512 : Equation4512 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3316 ..)
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4321 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq28 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq14 eq13 -- superposition 13,14
  have eq41 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq15 eq28 -- forward demodulation 28,15
  have eq42 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq13 eq41 -- forward demodulation 41,13
  have eq43 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq13 eq42 -- forward demodulation 42,13
  have eq45 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq43 eq14 -- backward demodulation 14,43
  have eq89 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq45 eq43 -- superposition 43,45
  have eq130 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq89 eq16 -- superposition 16,89
  subsumption eq130 rfl

theorem Equation3316_4343_4512_implies_Equation43 (G : Type*) [Magma G]
    (h3316 : Equation3316 G) (h4343 : Equation4343 G) (h4512 : Equation4512 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3316 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4343 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq21 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq14 eq13 -- superposition 13,14
  have eq23 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq15 eq21 -- forward demodulation 21,15
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq13 eq15 -- superposition 15,13
  have eq30 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq14 eq15 -- superposition 15,14
  have eq37 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq14 -- superposition 14,15
  have eq39 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq15 eq25 -- forward demodulation 25,15
  have eq40 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq39 -- forward demodulation 39,15
  have eq46 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq30 -- forward demodulation 30,15
  have eq47 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ (X0 ◇ X1)) := superpose eq13 eq46 -- forward demodulation 46,13
  have eq49 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq47 eq23 -- backward demodulation 23,47
  have eq50 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq47 eq49 -- forward demodulation 49,47
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := superpose eq13 eq37 -- forward demodulation 37,13
  have eq60 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X3)) = (X2 ◇ (X3 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)))) := superpose eq47 eq47 -- superposition 47,47
  have eq62 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq47 eq47 -- superposition 47,47
  have eq65 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq15 eq47 -- superposition 47,15
  have eq74 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq47 eq15 -- superposition 15,47
  have eq79 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X3)) = (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))))) := superpose eq15 eq60 -- forward demodulation 60,15
  have eq80 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X3)) = (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) := superpose eq15 eq79 -- forward demodulation 79,15
  have eq81 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X3)) = (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq50 eq80 -- forward demodulation 80,50
  have eq82 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X3)) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq47 eq81 -- forward demodulation 81,47
  have eq83 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X3)) = (X2 ◇ (X1 ◇ (X3 ◇ X0))) := superpose eq47 eq82 -- forward demodulation 82,47
  have eq85 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = (X2 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq47 eq62 -- forward demodulation 62,47
  have eq86 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq47 eq65 -- forward demodulation 65,47
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq15 eq74 -- forward demodulation 74,15
  have eq95 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := superpose eq15 eq94 -- forward demodulation 94,15
  have eq96 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X3))) = (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) := superpose eq15 eq95 -- forward demodulation 95,15
  have eq97 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X3))) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := superpose eq15 eq96 -- forward demodulation 96,15
  have eq115 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq14 eq50 -- superposition 50,14
  have eq116 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq14 eq50 -- superposition 50,14
  have eq117 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq50 -- superposition 50,15
  have eq121 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq15 eq50 -- superposition 50,15
  have eq156 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq47 eq115 -- forward demodulation 115,47
  have eq157 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq47 eq156 -- forward demodulation 156,47
  have eq158 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq47 eq157 -- forward demodulation 157,47
  have eq159 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq47 eq116 -- forward demodulation 116,47
  have eq160 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq158 eq159 -- forward demodulation 159,158
  have eq161 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq15 eq160 -- forward demodulation 160,15
  have eq162 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := superpose eq13 eq161 -- forward demodulation 161,13
  have eq163 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) := superpose eq86 eq117 -- forward demodulation 117,86
  have eq164 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) := superpose eq15 eq163 -- forward demodulation 163,15
  have eq165 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq97 eq164 -- forward demodulation 164,97
  have eq166 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq97 eq165 -- forward demodulation 165,97
  have eq167 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq58 eq166 -- forward demodulation 166,58
  have eq171 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq15 eq121 -- forward demodulation 121,15
  have eq172 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq40 eq171 -- forward demodulation 171,40
  have eq173 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ X1)) := superpose eq58 eq172 -- forward demodulation 172,58
  have eq218 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq58 eq58 -- superposition 58,58
  have eq239 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X2)) = (X0 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq47 eq218 -- forward demodulation 218,47
  have eq240 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = ((X0 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq15 eq239 -- forward demodulation 239,15
  have eq241 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq173 eq240 -- forward demodulation 240,173
  have eq242 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X2 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq241 eq85 -- backward demodulation 85,241
  have eq275 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) := superpose eq47 eq162 -- superposition 162,47
  have eq298 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq162 eq13 -- superposition 13,162
  have eq315 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := superpose eq15 eq275 -- forward demodulation 275,15
  have eq316 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq15 eq315 -- forward demodulation 315,15
  have eq317 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq242 eq316 -- forward demodulation 316,242
  have eq318 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) = (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))) := superpose eq83 eq317 -- forward demodulation 317,83
  have eq319 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) := superpose eq15 eq318 -- forward demodulation 318,15
  have eq320 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) := superpose eq167 eq319 -- forward demodulation 319,167
  have eq321 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) := superpose eq15 eq320 -- forward demodulation 320,15
  have eq322 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq167 eq321 -- forward demodulation 321,167
  have eq323 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq242 eq322 -- forward demodulation 322,242
  have eq324 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ X0)) := superpose eq167 eq323 -- forward demodulation 323,167
  have eq359 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) := superpose eq242 eq298 -- forward demodulation 298,242
  have eq360 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq15 eq359 -- forward demodulation 359,15
  have eq361 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ X0)) := superpose eq324 eq360 -- forward demodulation 360,324
  have eq362 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq13 eq361 -- forward demodulation 361,13
  have eq365 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq362 eq162 -- backward demodulation 162,362
  have eq373 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq365 eq14 -- backward demodulation 14,365
  have eq524 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq373 eq365 -- superposition 365,373
  have eq628 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq524 eq16 -- superposition 16,524
  subsumption eq628 rfl

theorem Equation3319_4290_4512_implies_Equation43 (G : Type*) [Magma G]
    (h3319 : Equation3319 G) (h4290 : Equation4290 G) (h4512 : Equation4512 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := mod_symm (h3319 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq24 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq25 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq14 eq14 -- superposition 14,14
  have eq27 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq15 eq24 -- forward demodulation 24,15
  have eq28 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq15 eq27 -- forward demodulation 27,15
  have eq29 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq13 eq28 -- forward demodulation 28,13
  have eq30 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq15 eq29 -- forward demodulation 29,15
  have eq31 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq15 eq30 -- forward demodulation 30,15
  have eq32 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq13 eq25 -- forward demodulation 25,13
  have eq33 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq32 -- forward demodulation 32,15
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) := superpose eq13 eq15 -- superposition 15,13
  have eq37 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq38 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq41 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq14 eq15 -- superposition 15,14
  have eq42 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq14 eq15 -- superposition 15,14
  have eq50 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) := superpose eq15 eq36 -- forward demodulation 36,15
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq15 eq50 -- forward demodulation 50,15
  have eq52 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq15 eq51 -- forward demodulation 51,15
  have eq53 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq37 -- forward demodulation 37,15
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq38 -- forward demodulation 38,15
  have eq58 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq42 -- forward demodulation 42,15
  have eq59 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq58 -- forward demodulation 58,15
  have eq72 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq13 eq22 -- superposition 22,13
  have eq76 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq15 eq22 -- superposition 22,15
  have eq97 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq15 eq72 -- forward demodulation 72,15
  have eq98 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq15 eq97 -- forward demodulation 97,15
  have eq99 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq13 eq98 -- forward demodulation 98,13
  have eq100 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq15 eq99 -- forward demodulation 99,15
  have eq101 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq15 eq100 -- forward demodulation 100,15
  have eq102 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq31 eq101 -- forward demodulation 101,31
  have eq108 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq15 eq76 -- forward demodulation 76,15
  have eq257 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq14 eq33 -- superposition 33,14
  have eq295 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq14 eq257 -- forward demodulation 257,14
  have eq331 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) := superpose eq13 eq41 -- superposition 41,13
  have eq364 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq15 eq41 -- superposition 41,15
  have eq365 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq13 eq41 -- superposition 41,13
  have eq405 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2)))) := superpose eq15 eq331 -- forward demodulation 331,15
  have eq406 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2))))) := superpose eq15 eq405 -- forward demodulation 405,15
  have eq407 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X2 ◇ (X2 ◇ X1))) := superpose eq108 eq406 -- forward demodulation 406,108
  have eq562 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq13 eq365 -- superposition 365,13
  have eq572 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq365 -- superposition 365,15
  have eq581 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq15 eq365 -- superposition 365,15
  have eq585 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X2))) = (X2 ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq365 eq41 -- superposition 41,365
  have eq588 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq365 eq15 -- superposition 15,365
  have eq590 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq15 eq562 -- forward demodulation 562,15
  have eq591 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq15 eq590 -- forward demodulation 590,15
  have eq592 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq365 eq591 -- forward demodulation 591,365
  have eq633 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) := superpose eq15 eq581 -- forward demodulation 581,15
  have eq636 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2)))) := superpose eq15 eq585 -- forward demodulation 585,15
  have eq637 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2))))) := superpose eq15 eq636 -- forward demodulation 636,15
  have eq642 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq15 eq588 -- forward demodulation 588,15
  have eq643 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq15 eq642 -- forward demodulation 642,15
  have eq654 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))))) := superpose eq41 eq52 -- superposition 52,41
  have eq658 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq33 eq52 -- superposition 52,33
  have eq662 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) := superpose eq41 eq52 -- superposition 52,41
  have eq701 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))))) := superpose eq364 eq658 -- forward demodulation 658,364
  have eq702 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))))) := superpose eq15 eq701 -- forward demodulation 701,15
  have eq703 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq52 eq702 -- forward demodulation 702,52
  have eq704 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq15 eq703 -- forward demodulation 703,15
  have eq705 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq52 eq704 -- forward demodulation 704,52
  have eq711 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = (X3 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) := superpose eq662 eq654 -- backward demodulation 654,662
  have eq1160 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2))) = ((X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X2) := superpose eq41 eq54 -- superposition 54,41
  have eq1195 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)))))) := superpose eq54 eq52 -- superposition 52,54
  have eq1266 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2))) = (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2)) := superpose eq15 eq1160 -- forward demodulation 1160,15
  have eq1267 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2))) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2))) := superpose eq15 eq1266 -- forward demodulation 1266,15
  have eq1268 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2))) = (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2)))) := superpose eq15 eq1267 -- forward demodulation 1267,15
  have eq1269 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2))) = (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq15 eq1268 -- forward demodulation 1268,15
  have eq1270 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2))) := superpose eq52 eq1269 -- forward demodulation 1269,52
  have eq1271 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2)))) := superpose eq15 eq1270 -- forward demodulation 1270,15
  have eq1272 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) := superpose eq15 eq1271 -- forward demodulation 1271,15
  have eq1392 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X3 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)))))) := superpose eq407 eq1195 -- forward demodulation 1195,407
  have eq1393 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X3 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2))))))) := superpose eq15 eq1392 -- forward demodulation 1392,15
  have eq1394 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X3 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)))))))) := superpose eq15 eq1393 -- forward demodulation 1393,15
  have eq1395 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X3 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)))))) := superpose eq1272 eq1394 -- forward demodulation 1394,1272
  have eq1396 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) = (X3 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))))))) := superpose eq15 eq1395 -- forward demodulation 1395,15
  have eq1397 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) = (X3 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))))) := superpose eq52 eq1396 -- forward demodulation 1396,52
  have eq1398 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = (X3 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) := superpose eq15 eq1397 -- forward demodulation 1397,15
  have eq1399 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq1272 eq1398 -- forward demodulation 1398,1272
  have eq1762 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq365 eq31 -- superposition 31,365
  have eq2126 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq592 eq1762 -- forward demodulation 1762,592
  have eq2354 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := superpose eq53 eq2126 -- superposition 2126,53
  have eq2386 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq2126 eq365 -- superposition 365,2126
  have eq2443 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq643 eq2354 -- forward demodulation 2354,643
  have eq2444 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq2443 -- forward demodulation 2443,15
  have eq2498 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq2386 -- forward demodulation 2386,15
  have eq2499 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq365 eq2498 -- forward demodulation 2498,365
  have eq2582 (X0 X1 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))))) = (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)))) := superpose eq102 eq59 -- superposition 59,102
  have eq3005 (X0 X1 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))))) := superpose eq15 eq2582 -- forward demodulation 2582,15
  have eq3006 (X0 X1 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))))) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)))))) := superpose eq15 eq3005 -- forward demodulation 3005,15
  have eq3007 (X0 X1 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))))))) := superpose eq15 eq3006 -- forward demodulation 3006,15
  have eq3008 (X0 X1 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))))) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X1 ◇ X0)))) := superpose eq637 eq3007 -- forward demodulation 3007,637
  have eq3009 (X0 X1 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))))) = (X0 ◇ (X1 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))))) := superpose eq711 eq3008 -- forward demodulation 3008,711
  have eq3010 (X0 X1 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))))) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)))))) := superpose eq15 eq3009 -- forward demodulation 3009,15
  have eq3011 (X0 X1 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))))))) := superpose eq15 eq3010 -- forward demodulation 3010,15
  have eq3012 (X0 X1 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)))))))) := superpose eq15 eq3011 -- forward demodulation 3011,15
  have eq3013 (X0 X1 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)))))) := superpose eq52 eq3012 -- forward demodulation 3012,52
  have eq3014 (X0 X1 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0)))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))))))) := superpose eq15 eq3013 -- forward demodulation 3013,15
  have eq3015 (X0 X1 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0)))))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))))) := superpose eq643 eq3014 -- forward demodulation 3014,643
  have eq3016 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq572 eq3015 -- forward demodulation 3015,572
  have eq3017 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = (X1 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))))))) := superpose eq15 eq3016 -- forward demodulation 3016,15
  have eq3018 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0)))))))) := superpose eq15 eq3017 -- forward demodulation 3017,15
  have eq3019 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))))))))) := superpose eq15 eq3018 -- forward demodulation 3018,15
  have eq3020 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0))))))))) := superpose eq1399 eq3019 -- forward demodulation 3019,1399
  have eq3021 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0))))))))) := superpose eq1399 eq3020 -- forward demodulation 3020,1399
  have eq3022 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0))))))) := superpose eq1272 eq3021 -- forward demodulation 3021,1272
  have eq3023 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0)))))))) := superpose eq15 eq3022 -- forward demodulation 3022,15
  have eq3024 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0)))))) := superpose eq643 eq3023 -- forward demodulation 3023,643
  have eq3025 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0))))))) := superpose eq15 eq3024 -- forward demodulation 3024,15
  have eq3026 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0))))) := superpose eq52 eq3025 -- forward demodulation 3025,52
  have eq3027 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)))))) := superpose eq15 eq3026 -- forward demodulation 3026,15
  have eq3028 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)))) := superpose eq365 eq3027 -- forward demodulation 3027,365
  have eq3029 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))))) := superpose eq15 eq3028 -- forward demodulation 3028,15
  have eq3030 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq15 eq3029 -- forward demodulation 3029,15
  have eq3031 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = (X0 ◇ (X1 ◇ X0)) := superpose eq633 eq3030 -- forward demodulation 3030,633
  have eq3032 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ X0)) := superpose eq15 eq3031 -- forward demodulation 3031,15
  have eq3293 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq2499 eq2499 -- superposition 2499,2499
  have eq3306 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := superpose eq41 eq2499 -- superposition 2499,41
  have eq3404 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) := superpose eq15 eq3293 -- forward demodulation 3293,15
  have eq3430 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) := superpose eq705 eq3306 -- forward demodulation 3306,705
  have eq3431 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq52 eq3430 -- forward demodulation 3430,52
  have eq3432 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq15 eq3431 -- forward demodulation 3431,15
  have eq3433 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq3404 eq3432 -- forward demodulation 3432,3404
  have eq3434 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq2444 eq3433 -- forward demodulation 3433,2444
  have eq3437 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq3434 eq295 -- backward demodulation 295,3434
  have eq3452 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose eq3434 eq3032 -- backward demodulation 3032,3434
  have eq4316 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq14 eq3452 -- superposition 3452,14
  have eq4829 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq2126 eq4316 -- superposition 4316,2126
  have eq4969 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq15 eq4829 -- forward demodulation 4829,15
  have eq4970 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq4969 eq3437 -- backward demodulation 3437,4969
  have eq5268 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq2499 eq4970 -- superposition 4970,2499
  have eq5666 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq5268 eq16 -- superposition 16,5268
  subsumption eq5666 rfl

theorem Equation3319_4320_4512_implies_Equation3346 (G : Type*) [Magma G]
    (h3319 : Equation3319 G) (h4320 : Equation4320 G) (h4512 : Equation4512 G) : Equation3346 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := mod_symm (h3319 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq61 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq14 eq15 -- superposition 15,14
  have eq78 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq61 -- forward demodulation 61,15
  have eq1686 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := superpose eq78 eq16 -- superposition 16,78
  subsumption eq1686 eq13

theorem Equation3353_4320_4512_implies_Equation3319 (G : Type*) [Magma G]
    (h3353 : Equation3353 G) (h4320 : Equation4320 G) (h4512 : Equation4512 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3353 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq48 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq14 eq15 -- superposition 15,14
  have eq65 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq48 -- forward demodulation 48,15
  have eq1809 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq65 eq65 -- superposition 65,65
  have eq1960 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq13 eq1809 -- forward demodulation 1809,13
  have eq2356 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq1960 eq16 -- superposition 16,1960
  subsumption eq2356 rfl

theorem Equation4268_4269_4512_implies_Equation4286 (G : Type*) [Magma G]
    (h4268 : Equation4268 G) (h4269 : Equation4269 G) (_ : Equation4512 G) : Equation4286 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4268 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4269 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq17 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq17 eq13

theorem Equation4268_4270_4512_implies_Equation4288 (G : Type*) [Magma G]
    (h4268 : Equation4268 G) (h4270 : Equation4270 G) (_ : Equation4512 G) : Equation4288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4268 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4270 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq17 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq17 eq13

theorem Equation4268_4272_4512_implies_Equation4299 (G : Type*) [Magma G]
    (h4268 : Equation4268 G) (h4272 : Equation4272 G) (_ : Equation4512 G) : Equation4299 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4268 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4272 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq17 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq17 eq13

theorem Equation4268_4273_4512_implies_Equation4301 (G : Type*) [Magma G]
    (h4268 : Equation4268 G) (h4273 : Equation4273 G) (_ : Equation4512 G) : Equation4301 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4268 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4273 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq17 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq17 eq13

theorem Equation4268_4275_4512_implies_Equation4277 (G : Type*) [Magma G]
    (h4268 : Equation4268 G) (h4275 : Equation4275 G) (_ : Equation4512 G) : Equation4277 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4268 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4275 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := superpose eq13 eq13 -- superposition 13,13
  have eq21 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq14 eq14 -- superposition 14,14
  have eq82 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := superpose eq14 eq17 -- superposition 17,14
  have eq165 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (X0 ◇ sK2)) := superpose eq21 eq16 -- superposition 16,21
  subsumption eq165 eq82

theorem Equation4268_4276_4512_implies_Equation4275 (G : Type*) [Magma G]
    (h4268 : Equation4268 G) (h4276 : Equation4276 G) (_ : Equation4512 G) : Equation4275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4268 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := mod_symm (h4276 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := superpose eq13 eq13 -- superposition 13,13
  have eq22 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X2)) := superpose eq13 eq14 -- superposition 14,13
  have eq95 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ X0)) := superpose eq17 eq16 -- superposition 16,17
  subsumption eq95 eq22

theorem Equation4268_4283_4512_implies_Equation4269 (G : Type*) [Magma G]
    (h4268 : Equation4268 G) (h4283 : Equation4283 G) (_ : Equation4512 G) : Equation4269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4268 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq23 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq23 eq13

theorem Equation4268_4284_4512_implies_Equation4270 (G : Type*) [Magma G]
    (h4268 : Equation4268 G) (h4284 : Equation4284 G) (_ : Equation4512 G) : Equation4270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4268 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq24 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq24 eq13

theorem Equation4268_4287_4512_implies_Equation4271 (G : Type*) [Magma G]
    (h4268 : Equation4268 G) (h4287 : Equation4287 G) (_ : Equation4512 G) : Equation4271 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4268 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X1)) := mod_symm (h4287 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq34 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK2)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq34 eq13

theorem Equation4268_4290_4512_implies_Equation4272 (G : Type*) [Magma G]
    (h4268 : Equation4268 G) (h4290 : Equation4290 G) (_ : Equation4512 G) : Equation4272 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4268 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq25 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq25 eq13

theorem Equation4268_4291_4512_implies_Equation4273 (G : Type*) [Magma G]
    (h4268 : Equation4268 G) (h4291 : Equation4291 G) (_ : Equation4512 G) : Equation4273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4268 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq27 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq27 eq13

theorem Equation4268_4293_4512_implies_Equation4275 (G : Type*) [Magma G]
    (h4268 : Equation4268 G) (h4293 : Equation4293 G) (_ : Equation4512 G) : Equation4275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4268 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4293 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq22 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq22 eq13

theorem Equation4268_4320_4512_implies_Equation4275 (G : Type*) [Magma G]
    (h4268 : Equation4268 G) (h4320 : Equation4320 G) (h4512 : Equation4512 G) : Equation4275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4268 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := superpose eq13 eq13 -- superposition 13,13
  have eq20 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq13 eq14 -- superposition 14,13
  have eq21 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq13 eq14 -- superposition 14,13
  have eq27 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq14 eq13 -- superposition 13,14
  have eq28 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq14 eq20 -- forward demodulation 20,14
  have eq29 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq13 eq28 -- forward demodulation 28,13
  have eq30 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq21 -- forward demodulation 21,15
  have eq31 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq13 eq30 -- forward demodulation 30,13
  have eq102 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ X0)) := superpose eq17 eq16 -- superposition 16,17
  have eq106 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq17 eq14 -- superposition 14,17
  have eq123 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq15 eq106 -- forward demodulation 106,15
  have eq124 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq13 eq123 -- forward demodulation 123,13
  have eq194 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq14 eq27 -- superposition 27,14
  have eq235 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq15 eq194 -- forward demodulation 194,15
  have eq236 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq13 eq235 -- forward demodulation 235,13
  have eq378 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X2) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq29 eq15 -- superposition 15,29
  have eq408 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X2) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq15 eq378 -- forward demodulation 378,15
  have eq409 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X2) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq408 -- forward demodulation 408,15
  have eq410 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq124 eq409 -- forward demodulation 409,124
  have eq589 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq31 eq14 -- superposition 14,31
  have eq649 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq410 eq589 -- forward demodulation 589,410
  have eq1704 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := superpose eq236 eq649 -- superposition 649,236
  have eq2266 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq1704 eq102 -- superposition 102,1704
  subsumption eq2266 eq1704

theorem Equation4268_4321_4512_implies_Equation4275 (G : Type*) [Magma G]
    (h4268 : Equation4268 G) (h4321 : Equation4321 G) (h4512 : Equation4512 G) : Equation4275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4268 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4321 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := superpose eq13 eq13 -- superposition 13,13
  have eq20 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq13 eq14 -- superposition 14,13
  have eq30 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq20 -- forward demodulation 20,15
  have eq31 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq13 eq30 -- forward demodulation 30,13
  have eq42 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq49 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq14 eq15 -- superposition 15,14
  have eq59 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq15 eq42 -- forward demodulation 42,15
  have eq69 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq49 -- forward demodulation 49,15
  have eq103 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ X0)) := superpose eq17 eq16 -- superposition 16,17
  have eq107 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq17 eq14 -- superposition 14,17
  have eq126 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq15 eq107 -- forward demodulation 107,15
  have eq127 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq13 eq126 -- forward demodulation 126,13
  have eq253 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X2) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq31 eq15 -- superposition 15,31
  have eq290 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X2) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq15 eq253 -- forward demodulation 253,15
  have eq291 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X2) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq290 -- forward demodulation 290,15
  have eq292 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq127 eq291 -- forward demodulation 291,127
  have eq531 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq13 eq292 -- superposition 292,13
  have eq666 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2))))) := superpose eq59 eq59 -- superposition 59,59
  have eq682 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ (X0 ◇ X3)) ◇ X1) := superpose eq17 eq59 -- superposition 59,17
  have eq829 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X2) := superpose eq531 eq666 -- forward demodulation 666,531
  have eq830 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) ◇ X2) := superpose eq15 eq829 -- forward demodulation 829,15
  have eq831 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)))) ◇ X2) := superpose eq15 eq830 -- forward demodulation 830,15
  have eq832 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq13 eq831 -- forward demodulation 831,13
  have eq1001 (X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ (sK1 ◇ X1)) ◇ X2) := superpose eq682 eq103 -- superposition 103,682
  have eq4264 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq17 eq69 -- superposition 69,17
  have eq5199 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq832 eq4264 -- superposition 4264,832
  have eq5342 (X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X1 ◇ (X1 ◇ X2)) := superpose eq4264 eq1001 -- superposition 1001,4264
  subsumption eq5342 eq5199

theorem Equation4268_4343_4512_implies_Equation4275 (G : Type*) [Magma G]
    (h4268 : Equation4268 G) (h4343 : Equation4343 G) (h4512 : Equation4512 G) : Equation4275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4268 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4343 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := superpose eq13 eq13 -- superposition 13,13
  have eq20 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq14 eq13 -- superposition 13,14
  have eq22 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq39 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq15 eq22 -- forward demodulation 22,15
  have eq128 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq20 eq15 -- superposition 15,20
  have eq142 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq15 eq128 -- forward demodulation 128,15
  have eq143 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq15 eq142 -- forward demodulation 142,15
  have eq144 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq15 eq143 -- forward demodulation 143,15
  have eq145 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq15 eq144 -- forward demodulation 144,15
  have eq146 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq13 eq145 -- forward demodulation 145,13
  have eq184 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2)))) := superpose eq14 eq39 -- superposition 39,14
  have eq207 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ (X0 ◇ X3)) ◇ X1) := superpose eq17 eq39 -- superposition 39,17
  have eq280 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq13 eq184 -- forward demodulation 184,13
  have eq281 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq15 eq280 -- forward demodulation 280,15
  have eq282 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq146 eq281 -- forward demodulation 281,146
  have eq2439 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ X3)) = (X2 ◇ (X2 ◇ X2)) := superpose eq207 eq282 -- superposition 282,207
  have eq3191 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq2439 eq16 -- superposition 16,2439
  subsumption eq3191 eq2439

theorem Equation4269_4270_4512_implies_Equation4318 (G : Type*) [Magma G]
    (h4269 : Equation4269 G) (h4270 : Equation4270 G) (_ : Equation4512 G) : Equation4318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4269 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4270 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq17 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq17 eq13

theorem Equation4269_4272_4512_implies_Equation4327 (G : Type*) [Magma G]
    (h4269 : Equation4269 G) (h4272 : Equation4272 G) (_ : Equation4512 G) : Equation4327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4269 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4272 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq17 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq17 eq13

theorem Equation4269_4273_4512_implies_Equation4279 (G : Type*) [Magma G]
    (h4269 : Equation4269 G) (h4273 : Equation4273 G) (_ : Equation4512 G) : Equation4279 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4269 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4273 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := superpose eq13 eq13 -- superposition 13,13
  have eq19 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq14 eq14 -- superposition 14,14
  have eq74 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X0)) := superpose eq14 eq17 -- superposition 17,14
  have eq159 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq19 eq16 -- superposition 16,19
  subsumption eq159 eq74

theorem Equation4269_4275_4512_implies_Equation4296 (G : Type*) [Magma G]
    (h4269 : Equation4269 G) (h4275 : Equation4275 G) (_ : Equation4512 G) : Equation4296 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4269 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4275 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq18 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq13 eq16 -- superposition 16,13
  subsumption eq18 eq14

theorem Equation4269_4276_4512_implies_Equation4273 (G : Type*) [Magma G]
    (h4269 : Equation4269 G) (h4276 : Equation4276 G) (_ : Equation4512 G) : Equation4273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4269 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := mod_symm (h4276 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := superpose eq13 eq13 -- superposition 13,13
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X2)) := superpose eq13 eq14 -- superposition 14,13
  have eq91 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq17 eq16 -- superposition 16,17
  subsumption eq91 eq20

theorem Equation4269_4280_4512_implies_Equation4331 (G : Type*) [Magma G]
    (h4269 : Equation4269 G) (h4280 : Equation4280 G) (_ : Equation4512 G) : Equation4331 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4269 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X2)) := mod_symm (h4280 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq17 : (sK2 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq13 eq16 -- forward demodulation 16,13
  subsumption eq17 eq14

theorem Equation4269_4283_4512_implies_Equation4268 (G : Type*) [Magma G]
    (h4269 : Equation4269 G) (h4283 : Equation4283 G) (_ : Equation4512 G) : Equation4268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4269 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4283 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq18 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq114 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq18 eq16 -- superposition 16,18
  subsumption eq114 rfl

theorem Equation4269_4290_4512_implies_Equation4273 (G : Type*) [Magma G]
    (h4269 : Equation4269 G) (h4290 : Equation4290 G) (h4512 : Equation4512 G) : Equation4273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4269 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := superpose eq13 eq13 -- superposition 13,13
  have eq19 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq14 eq14 -- superposition 14,14
  have eq21 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq14 eq13 -- superposition 13,14
  have eq22 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq19 -- forward demodulation 19,15
  have eq23 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq14 eq21 -- forward demodulation 21,14
  have eq24 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq13 eq15 -- superposition 15,13
  have eq29 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq13 eq15 -- superposition 15,13
  have eq40 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq13 -- superposition 13,15
  have eq41 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq15 eq24 -- forward demodulation 24,15
  have eq42 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq15 eq25 -- forward demodulation 25,15
  have eq47 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq15 eq29 -- forward demodulation 29,15
  have eq57 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq40 eq23 -- backward demodulation 23,40
  have eq59 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq40 eq22 -- backward demodulation 22,40
  have eq60 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq59 eq57 -- backward demodulation 57,59
  have eq61 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (X1 ◇ X1)) := superpose eq40 eq60 -- forward demodulation 60,40
  have eq62 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq61 eq59 -- backward demodulation 59,61
  have eq69 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X3 ◇ X2)) := superpose eq15 eq17 -- superposition 17,15
  have eq117 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq40 -- superposition 40,15
  have eq124 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq14 eq40 -- superposition 40,14
  have eq127 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) := superpose eq15 eq40 -- superposition 40,15
  have eq158 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq117 eq47 -- backward demodulation 47,117
  have eq160 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) := superpose eq15 eq127 -- forward demodulation 127,15
  have eq178 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq13 eq62 -- superposition 62,13
  have eq211 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq178 eq160 -- backward demodulation 160,178
  have eq219 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) := superpose eq178 eq211 -- forward demodulation 211,178
  have eq264 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) = ((X0 ◇ X1) ◇ (X4 ◇ (X0 ◇ X1))) := superpose eq15 eq69 -- superposition 69,15
  have eq321 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X4 ◇ (X0 ◇ X1))) := superpose eq219 eq264 -- forward demodulation 264,219
  have eq324 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq321 eq158 -- backward demodulation 158,321
  have eq380 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq324 eq15 -- superposition 15,324
  have eq423 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) := superpose eq15 eq380 -- forward demodulation 380,15
  have eq424 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) := superpose eq15 eq423 -- forward demodulation 423,15
  have eq425 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq15 eq424 -- forward demodulation 424,15
  have eq426 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq124 eq425 -- forward demodulation 425,124
  have eq427 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq324 eq426 -- forward demodulation 426,324
  have eq428 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq427 -- forward demodulation 427,15
  have eq1611 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ (X2 ◇ X0)) ◇ X1) := superpose eq14 eq41 -- superposition 41,14
  have eq1864 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X2 ◇ X0)) ◇ X1) := superpose eq428 eq1611 -- forward demodulation 1611,428
  have eq1867 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq1864 eq42 -- backward demodulation 42,1864
  have eq2257 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose eq178 eq1867 -- superposition 1867,178
  have eq2423 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq2257 eq16 -- superposition 16,2257
  subsumption eq2423 eq13

theorem Equation4269_4291_4512_implies_Equation4275 (G : Type*) [Magma G]
    (h4269 : Equation4269 G) (h4291 : Equation4291 G) (_ : Equation4512 G) : Equation4275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4269 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq23 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq23 eq13

theorem Equation4269_4293_4512_implies_Equation4273 (G : Type*) [Magma G]
    (h4269 : Equation4269 G) (h4293 : Equation4293 G) (h4512 : Equation4512 G) : Equation4273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4269 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4293 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := superpose eq13 eq13 -- superposition 13,13
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq13 eq15 -- superposition 15,13
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq25 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq14 eq15 -- superposition 15,14
  have eq27 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq13 -- superposition 13,15
  have eq32 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq14 -- superposition 14,15
  have eq34 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq13 -- superposition 13,15
  have eq35 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq15 eq18 -- forward demodulation 18,15
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq15 eq19 -- forward demodulation 19,15
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq20 -- forward demodulation 20,15
  have eq43 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq25 -- forward demodulation 25,15
  have eq57 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X3 ◇ X2)) := superpose eq15 eq17 -- superposition 17,15
  have eq79 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq17 eq16 -- superposition 16,17
  have eq87 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq15 eq34 -- superposition 34,15
  have eq92 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq15 eq34 -- superposition 34,15
  have eq107 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (X1 ◇ X1)) := superpose eq14 eq34 -- superposition 34,14
  have eq119 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X3) = (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) := superpose eq34 eq15 -- superposition 15,34
  have eq123 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq34 eq92 -- forward demodulation 92,34
  have eq150 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) := superpose eq15 eq119 -- forward demodulation 119,15
  have eq151 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := superpose eq15 eq150 -- forward demodulation 150,15
  have eq175 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))))) := superpose eq35 eq35 -- superposition 35,35
  have eq206 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq35 eq14 -- superposition 14,35
  have eq208 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3)) = ((X0 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3) := superpose eq35 eq15 -- superposition 15,35
  have eq209 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq35 eq17 -- superposition 17,35
  have eq250 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X2) := superpose eq107 eq175 -- forward demodulation 175,107
  have eq251 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0))))) ◇ X2) := superpose eq15 eq250 -- forward demodulation 250,15
  have eq252 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X2) := superpose eq151 eq251 -- forward demodulation 251,151
  have eq253 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) ◇ X2) := superpose eq15 eq252 -- forward demodulation 252,15
  have eq254 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq34 eq253 -- forward demodulation 253,34
  have eq301 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq107 eq206 -- forward demodulation 206,107
  have eq303 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X3) = ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3)) := superpose eq107 eq208 -- forward demodulation 208,107
  have eq304 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = (X2 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq107 eq209 -- forward demodulation 209,107
  have eq398 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X4)) = ((X0 ◇ (X3 ◇ X0)) ◇ X4) := superpose eq57 eq15 -- superposition 15,57
  have eq440 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ X4) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X4))) := superpose eq15 eq398 -- forward demodulation 398,15
  have eq441 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ X4) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X4)))) := superpose eq15 eq440 -- forward demodulation 440,15
  have eq503 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X3) := superpose eq15 eq36 -- superposition 36,15
  have eq664 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) ◇ X3) := superpose eq37 eq503 -- forward demodulation 503,37
  have eq665 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) = ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X3) := superpose eq15 eq664 -- forward demodulation 664,15
  have eq666 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) = ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X3) := superpose eq15 eq665 -- forward demodulation 665,15
  have eq667 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) = ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) := superpose eq15 eq666 -- forward demodulation 666,15
  have eq668 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) := superpose eq107 eq667 -- forward demodulation 667,107
  have eq669 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3))))) := superpose eq15 eq668 -- forward demodulation 668,15
  have eq941 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq14 eq37 -- superposition 37,14
  have eq996 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X2)) := superpose eq37 eq35 -- superposition 35,37
  have eq1232 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq15 eq941 -- forward demodulation 941,15
  have eq1233 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq15 eq1232 -- forward demodulation 1232,15
  have eq1234 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq15 eq1233 -- forward demodulation 1233,15
  have eq1407 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq15 eq996 -- forward demodulation 996,15
  have eq1408 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq15 eq1407 -- forward demodulation 1407,15
  have eq1476 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq13 eq254 -- superposition 254,13
  have eq1503 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq36 eq254 -- superposition 254,36
  have eq1580 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq1476 eq301 -- backward demodulation 301,1476
  have eq1779 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq32 eq37 -- superposition 37,32
  have eq1780 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq32 eq36 -- superposition 36,32
  have eq2004 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq1503 eq1779 -- forward demodulation 1779,1503
  have eq2228 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3))))) = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq35 eq43 -- superposition 43,35
  have eq2291 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq57 eq43 -- superposition 43,57
  have eq2302 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq57 eq43 -- superposition 43,57
  have eq2468 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq1476 eq2228 -- forward demodulation 2228,1476
  have eq2669 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq15 eq2302 -- forward demodulation 2302,15
  have eq2670 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq1580 eq2669 -- forward demodulation 2669,1580
  have eq2671 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq2670 eq27 -- backward demodulation 27,2670
  have eq2684 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq2671 eq87 -- backward demodulation 87,2671
  have eq2688 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) := superpose eq2684 eq2004 -- backward demodulation 2004,2684
  have eq2694 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq2688 eq1780 -- backward demodulation 1780,2688
  have eq2699 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((X0 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X2)) := superpose eq2694 eq1408 -- backward demodulation 1408,2694
  have eq2702 (X0 X3 : G) : (X0 ◇ (X3 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X3) := superpose eq2699 eq303 -- backward demodulation 303,2699
  have eq2705 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq2702 eq36 -- backward demodulation 36,2702
  have eq2709 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3))))) := superpose eq2702 eq669 -- backward demodulation 669,2702
  have eq2715 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq2705 eq35 -- backward demodulation 35,2705
  have eq2723 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq2705 eq43 -- backward demodulation 43,2705
  have eq2747 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3))) := superpose eq2705 eq2468 -- backward demodulation 2468,2705
  have eq2758 (X0 X1 X2 X4 : G) : (X0 ◇ (X4 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X4)))) := superpose eq2715 eq441 -- backward demodulation 441,2715
  have eq2785 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3)))) := superpose eq15 eq2747 -- forward demodulation 2747,15
  have eq2786 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X3))))) := superpose eq15 eq2785 -- forward demodulation 2785,15
  have eq2787 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0)))) := superpose eq2705 eq2786 -- forward demodulation 2786,2705
  have eq2788 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq2705 eq2787 -- forward demodulation 2787,2705
  have eq2802 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X0)) = (X0 ◇ (X1 ◇ (X3 ◇ X1))) := superpose eq2758 eq2709 -- forward demodulation 2709,2758
  have eq2804 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq2802 eq2291 -- backward demodulation 2291,2802
  have eq2828 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq2804 eq123 -- backward demodulation 123,2804
  have eq3926 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))) = ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq2723 eq32 -- superposition 32,2723
  have eq4349 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))) = ((X2 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq3926 -- forward demodulation 3926,15
  have eq4350 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))) = (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq1234 eq4349 -- forward demodulation 4349,1234
  have eq4351 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq15 eq4350 -- forward demodulation 4350,15
  have eq4352 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq2828 eq4351 -- forward demodulation 4351,2828
  have eq4687 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X0)) = (X4 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2))))) := superpose eq304 eq2788 -- superposition 2788,304
  have eq4794 (X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X1 ◇ (X2 ◇ (sK1 ◇ X2))) := superpose eq2788 eq79 -- superposition 79,2788
  have eq4918 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X0)) = (X4 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))))) := superpose eq15 eq4687 -- forward demodulation 4687,15
  have eq4919 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X0)) = (X4 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq4352 eq4918 -- forward demodulation 4918,4352
  have eq4920 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X0)) = (X4 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq2804 eq4919 -- forward demodulation 4919,2804
  subsumption eq4794 eq4920

theorem Equation4269_4300_4512_implies_Equation4278 (G : Type*) [Magma G]
    (h4269 : Equation4269 G) (h4300 : Equation4300 G) (_ : Equation4512 G) : Equation4278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4269 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := mod_symm (h4300 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := superpose eq13 eq13 -- superposition 13,13
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ X1)) := superpose eq14 eq14 -- superposition 14,14
  have eq184 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq17 eq19 -- superposition 19,17
  have eq232 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ sK0)) := superpose eq19 eq16 -- superposition 16,19
  subsumption eq232 eq184

theorem Equation4269_4314_4512_implies_Equation4270 (G : Type*) [Magma G]
    (h4269 : Equation4269 G) (h4314 : Equation4314 G) (_ : Equation4512 G) : Equation4270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4269 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4314 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq24 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq24 eq13

theorem Equation4269_4315_4512_implies_Equation4271 (G : Type*) [Magma G]
    (h4269 : Equation4269 G) (h4315 : Equation4315 G) (_ : Equation4512 G) : Equation4271 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4269 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h4315 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq31 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq31 eq13

theorem Equation4269_4320_4512_implies_Equation4272 (G : Type*) [Magma G]
    (h4269 : Equation4269 G) (h4320 : Equation4320 G) (_ : Equation4512 G) : Equation4272 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4269 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq25 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq25 eq13

theorem Equation4269_4321_4512_implies_Equation4273 (G : Type*) [Magma G]
    (h4269 : Equation4269 G) (h4321 : Equation4321 G) (_ : Equation4512 G) : Equation4273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4269 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4321 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq28 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq28 eq13

theorem Equation4269_4343_4512_implies_Equation4273 (G : Type*) [Magma G]
    (h4269 : Equation4269 G) (h4343 : Equation4343 G) (h4512 : Equation4512 G) : Equation4273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4269 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4343 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := superpose eq13 eq13 -- superposition 13,13
  have eq22 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq23 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq13 eq15 -- superposition 15,13
  have eq24 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq38 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq13 -- superposition 13,15
  have eq39 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq15 eq22 -- forward demodulation 22,15
  have eq40 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq15 eq23 -- forward demodulation 23,15
  have eq41 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq24 -- forward demodulation 24,15
  have eq130 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X3) = (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) := superpose eq38 eq15 -- superposition 15,38
  have eq151 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) := superpose eq15 eq130 -- forward demodulation 130,15
  have eq152 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := superpose eq15 eq151 -- forward demodulation 151,15
  have eq175 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2)))) := superpose eq14 eq39 -- superposition 39,14
  have eq210 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq39 eq17 -- superposition 17,39
  have eq280 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2)))) = (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq15 eq175 -- forward demodulation 175,15
  have eq281 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2)))) = (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq40 eq280 -- forward demodulation 280,40
  have eq282 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2)))) = (X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq15 eq281 -- forward demodulation 281,15
  have eq283 (X0 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2)))) := superpose eq38 eq282 -- forward demodulation 282,38
  have eq596 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq40 eq40 -- superposition 40,40
  have eq613 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq14 eq40 -- superposition 40,14
  have eq784 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1))))) = ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X1) := superpose eq15 eq596 -- forward demodulation 596,15
  have eq785 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1))))) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1) := superpose eq152 eq784 -- forward demodulation 784,152
  have eq786 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1))))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq15 eq785 -- forward demodulation 785,15
  have eq787 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1))))) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq15 eq786 -- forward demodulation 786,15
  have eq788 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1))))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) := superpose eq41 eq787 -- forward demodulation 787,41
  have eq789 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1))))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq15 eq788 -- forward demodulation 788,15
  have eq790 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq15 eq789 -- forward demodulation 789,15
  have eq791 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq15 eq790 -- forward demodulation 790,15
  have eq792 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq152 eq791 -- forward demodulation 791,152
  have eq793 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq15 eq792 -- forward demodulation 792,15
  have eq794 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq15 eq793 -- forward demodulation 793,15
  have eq799 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq613 -- forward demodulation 613,15
  have eq800 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq38 eq799 -- forward demodulation 799,38
  have eq801 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq800 eq794 -- backward demodulation 794,800
  have eq805 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = (X2 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq801 eq210 -- backward demodulation 210,801
  have eq822 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq801 eq283 -- backward demodulation 283,801
  have eq4435 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := superpose eq805 eq822 -- superposition 822,805
  have eq4972 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq4435 eq16 -- superposition 16,4435
  subsumption eq4972 eq4435

theorem Equation4270_4272_4512_implies_Equation4280 (G : Type*) [Magma G]
    (h4270 : Equation4270 G) (h4272 : Equation4272 G) (_ : Equation4512 G) : Equation4280 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4270 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4272 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq13 eq13 -- superposition 13,13
  have eq19 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := superpose eq14 eq14 -- superposition 14,14
  have eq68 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq14 eq17 -- superposition 17,14
  have eq153 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq19 eq16 -- superposition 16,19
  subsumption eq153 eq68

theorem Equation4270_4273_4512_implies_Equation4325 (G : Type*) [Magma G]
    (h4270 : Equation4270 G) (h4273 : Equation4273 G) (_ : Equation4512 G) : Equation4325 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4270 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4273 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq18 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq13 eq16 -- superposition 16,13
  subsumption eq18 eq14

theorem Equation4270_4275_4512_implies_Equation4297 (G : Type*) [Magma G]
    (h4270 : Equation4270 G) (h4275 : Equation4275 G) (_ : Equation4512 G) : Equation4297 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4270 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4275 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq18 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq13 eq16 -- superposition 16,13
  subsumption eq18 eq14

theorem Equation4270_4276_4512_implies_Equation4272 (G : Type*) [Magma G]
    (h4270 : Equation4270 G) (h4276 : Equation4276 G) (_ : Equation4512 G) : Equation4272 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4270 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := mod_symm (h4276 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq13 eq13 -- superposition 13,13
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X2 ◇ X2)) := superpose eq13 eq14 -- superposition 14,13
  have eq87 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq17 eq16 -- superposition 16,17
  subsumption eq87 eq20

theorem Equation4270_4284_4512_implies_Equation4268 (G : Type*) [Magma G]
    (h4270 : Equation4270 G) (h4284 : Equation4284 G) (_ : Equation4512 G) : Equation4268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4270 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4284 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq18 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq127 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq18 eq16 -- superposition 16,18
  subsumption eq127 rfl

theorem Equation4270_4290_4512_implies_Equation4275 (G : Type*) [Magma G]
    (h4270 : Equation4270 G) (h4290 : Equation4290 G) (_ : Equation4512 G) : Equation4275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4270 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq22 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq22 eq13

theorem Equation4270_4291_4512_implies_Equation4272 (G : Type*) [Magma G]
    (h4270 : Equation4270 G) (h4291 : Equation4291 G) (h4512 : Equation4512 G) : Equation4272 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4270 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq13 eq13 -- superposition 13,13
  have eq22 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq31 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq13 -- superposition 13,15
  have eq38 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq15 eq22 -- forward demodulation 22,15
  have eq39 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq23 -- forward demodulation 23,15
  have eq113 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq14 eq31 -- superposition 31,14
  have eq162 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X2 ◇ X3))) = ((X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ X3) := superpose eq17 eq38 -- superposition 38,17
  have eq186 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1))) := superpose eq38 eq38 -- superposition 38,38
  have eq210 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) := superpose eq38 eq17 -- superposition 17,38
  have eq226 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq38 eq14 -- superposition 14,38
  have eq233 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X2 ◇ X3))) = ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) := superpose eq15 eq162 -- forward demodulation 162,15
  have eq260 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1)))) := superpose eq15 eq186 -- forward demodulation 186,15
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1))))) := superpose eq15 eq260 -- forward demodulation 260,15
  have eq289 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = (X2 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq113 eq210 -- forward demodulation 210,113
  have eq399 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) = (((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2) := superpose eq13 eq39 -- superposition 39,13
  have eq525 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) = ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X2) := superpose eq15 eq399 -- forward demodulation 399,15
  have eq526 (X0 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq233 eq525 -- forward demodulation 525,233
  have eq527 (X0 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq15 eq526 -- forward demodulation 526,15
  have eq528 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq113 eq527 -- forward demodulation 527,113
  have eq532 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq528 eq226 -- backward demodulation 226,528
  have eq538 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq528 eq261 -- backward demodulation 261,528
  have eq542 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq538 eq532 -- backward demodulation 532,538
  have eq2289 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X2)) = (X1 ◇ (X1 ◇ X1)) := superpose eq289 eq542 -- superposition 542,289
  have eq3096 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq2289 eq16 -- superposition 16,2289
  subsumption eq3096 eq2289

theorem Equation4270_4293_4512_implies_Equation4272 (G : Type*) [Magma G]
    (h4270 : Equation4270 G) (h4293 : Equation4293 G) (h4512 : Equation4512 G) : Equation4272 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4270 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4293 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq13 eq13 -- superposition 13,13
  have eq22 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq13 eq15 -- superposition 15,13
  have eq28 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq14 eq15 -- superposition 15,14
  have eq31 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq13 -- superposition 13,15
  have eq37 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq14 -- superposition 14,15
  have eq39 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq15 eq22 -- forward demodulation 22,15
  have eq40 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq23 -- forward demodulation 23,15
  have eq42 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq25 -- forward demodulation 25,15
  have eq46 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq28 -- forward demodulation 28,15
  have eq77 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq17 eq16 -- superposition 16,17
  have eq118 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X3)) = (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))))) := superpose eq31 eq31 -- superposition 31,31
  have eq172 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X2 ◇ X3))) = ((X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ X3) := superpose eq17 eq39 -- superposition 39,17
  have eq197 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1))) := superpose eq39 eq39 -- superposition 39,39
  have eq237 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq39 eq14 -- superposition 14,39
  have eq244 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X2 ◇ X3))) = ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) := superpose eq15 eq172 -- forward demodulation 172,15
  have eq269 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1)))) := superpose eq15 eq197 -- forward demodulation 197,15
  have eq270 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1))))) := superpose eq15 eq269 -- forward demodulation 269,15
  have eq368 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq15 eq40 -- superposition 40,15
  have eq370 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X3) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) := superpose eq40 eq40 -- superposition 40,40
  have eq373 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq14 eq40 -- superposition 40,14
  have eq378 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq15 eq40 -- superposition 40,15
  have eq384 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq40 eq17 -- superposition 17,40
  have eq388 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq40 eq77 -- superposition 77,40
  have eq402 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq40 eq14 -- superposition 14,40
  have eq413 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1))) := superpose eq40 eq31 -- superposition 31,40
  have eq491 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq15 eq373 -- forward demodulation 373,15
  have eq492 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq15 eq491 -- forward demodulation 491,15
  have eq493 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq15 eq492 -- forward demodulation 492,15
  have eq496 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq15 eq378 -- forward demodulation 378,15
  have eq542 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)))) := superpose eq15 eq413 -- forward demodulation 413,15
  have eq543 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))))) := superpose eq15 eq542 -- forward demodulation 542,15
  have eq544 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))))) := superpose eq15 eq543 -- forward demodulation 543,15
  have eq545 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))))) := superpose eq15 eq544 -- forward demodulation 544,15
  have eq582 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)))) := superpose eq14 eq42 -- superposition 42,14
  have eq584 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))))) := superpose eq39 eq42 -- superposition 42,39
  have eq585 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) = (X0 ◇ (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2))))) := superpose eq40 eq42 -- superposition 42,40
  have eq612 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X1 ◇ X0))) = ((X2 ◇ (X2 ◇ X2)) ◇ X1) := superpose eq14 eq42 -- superposition 42,14
  have eq641 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3)) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))))) := superpose eq42 eq39 -- superposition 39,42
  have eq651 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X3 ◇ (X3 ◇ (X1 ◇ X2))))) := superpose eq42 eq40 -- superposition 40,42
  have eq709 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))))) := superpose eq15 eq582 -- forward demodulation 582,15
  have eq710 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq15 eq709 -- forward demodulation 709,15
  have eq713 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)))))) := superpose eq15 eq584 -- forward demodulation 584,15
  have eq714 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))))))) := superpose eq15 eq713 -- forward demodulation 713,15
  have eq715 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))))))) := superpose eq15 eq714 -- forward demodulation 714,15
  have eq716 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))))))) := superpose eq15 eq715 -- forward demodulation 715,15
  have eq717 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X1))))) := superpose eq496 eq716 -- forward demodulation 716,496
  have eq718 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)))))) := superpose eq15 eq717 -- forward demodulation 717,15
  have eq719 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))))))) := superpose eq15 eq718 -- forward demodulation 718,15
  have eq720 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))))) := superpose eq15 eq719 -- forward demodulation 719,15
  have eq721 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)))) := superpose eq496 eq720 -- forward demodulation 720,496
  have eq722 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))))) := superpose eq15 eq721 -- forward demodulation 721,15
  have eq723 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))))) := superpose eq15 eq722 -- forward demodulation 722,15
  have eq724 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))))) := superpose eq15 eq723 -- forward demodulation 723,15
  have eq725 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))))) = ((X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) ◇ X1) := superpose eq15 eq724 -- forward demodulation 724,15
  have eq726 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))))) = ((X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ X1) := superpose eq15 eq725 -- forward demodulation 725,15
  have eq727 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))))) := superpose eq244 eq726 -- forward demodulation 726,244
  have eq728 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) = (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2)))))) := superpose eq15 eq585 -- forward demodulation 585,15
  have eq729 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) = (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))))) := superpose eq15 eq728 -- forward demodulation 728,15
  have eq758 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0))) := superpose eq612 eq545 -- backward demodulation 545,612
  have eq765 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose eq612 eq727 -- backward demodulation 727,612
  have eq781 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0)))) := superpose eq15 eq758 -- forward demodulation 758,15
  have eq782 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq15 eq781 -- forward demodulation 781,15
  have eq783 (X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq782 eq388 -- backward demodulation 388,782
  have eq786 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = (X2 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq782 eq384 -- backward demodulation 384,782
  have eq809 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose eq15 eq765 -- forward demodulation 765,15
  have eq810 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq15 eq809 -- forward demodulation 809,15
  have eq811 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq118 eq810 -- forward demodulation 810,118
  have eq825 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq811 eq237 -- backward demodulation 237,811
  have eq835 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq811 eq710 -- backward demodulation 710,811
  have eq849 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) = (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq811 eq729 -- backward demodulation 729,811
  have eq852 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq811 eq270 -- backward demodulation 270,811
  have eq1006 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3)) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq612 eq641 -- forward demodulation 641,612
  have eq1007 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3)) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq15 eq1006 -- forward demodulation 1006,15
  have eq1008 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3)) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq15 eq1007 -- forward demodulation 1007,15
  have eq1009 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3)) ◇ X1) := superpose eq852 eq1008 -- forward demodulation 1008,852
  have eq1010 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ (X3 ◇ X3))) ◇ X1) := superpose eq15 eq1009 -- forward demodulation 1009,15
  have eq1011 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X3)))) ◇ X1) := superpose eq15 eq1010 -- forward demodulation 1010,15
  have eq1012 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq811 eq1011 -- forward demodulation 1011,811
  have eq1042 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) := superpose eq1012 eq651 -- forward demodulation 651,1012
  have eq1043 (X0 X3 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq1042 eq849 -- backward demodulation 849,1042
  have eq1044 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq1043 eq835 -- backward demodulation 835,1043
  have eq1175 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq13 eq786 -- superposition 786,13
  have eq1872 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq786 eq811 -- superposition 811,786
  have eq1939 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq1044 eq1872 -- forward demodulation 1872,1044
  have eq2639 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq13 eq1012 -- superposition 1012,13
  have eq2670 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X2 ◇ (X2 ◇ X1))) := superpose eq42 eq1012 -- superposition 1012,42
  have eq2783 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq2639 eq825 -- backward demodulation 825,2639
  have eq2914 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0))) := superpose eq811 eq37 -- superposition 37,811
  have eq2915 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0))) = ((X3 ◇ X0) ◇ (X3 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1))) := superpose eq39 eq37 -- superposition 37,39
  have eq3022 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq37 eq39 -- superposition 39,37
  have eq3124 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))) := superpose eq15 eq2914 -- forward demodulation 2914,15
  have eq3125 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq15 eq3124 -- forward demodulation 3124,15
  have eq3126 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) = ((X0 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X0) := superpose eq368 eq3125 -- forward demodulation 3125,368
  have eq3127 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) = (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq15 eq3126 -- forward demodulation 3126,15
  have eq3128 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq15 eq3127 -- forward demodulation 3127,15
  have eq3129 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq15 eq3128 -- forward demodulation 3128,15
  have eq3130 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq2783 eq3129 -- forward demodulation 3129,2783
  have eq3131 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0))) = ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1)))) := superpose eq15 eq2915 -- forward demodulation 2915,15
  have eq3132 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0))) = ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1))))) := superpose eq15 eq3131 -- forward demodulation 3131,15
  have eq3133 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1))))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X0)))) := superpose eq15 eq3132 -- forward demodulation 3132,15
  have eq3134 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1))))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X0))))) := superpose eq15 eq3133 -- forward demodulation 3133,15
  have eq3135 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1))))) := superpose eq3130 eq3134 -- forward demodulation 3134,3130
  have eq3307 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))))) := superpose eq15 eq3022 -- forward demodulation 3022,15
  have eq3308 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq3135 eq3307 -- forward demodulation 3307,3135
  have eq3309 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ (X3 ◇ X3))) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq3308 -- forward demodulation 3308,15
  have eq3410 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) = (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)))) := superpose eq42 eq46 -- superposition 46,42
  have eq3440 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) := superpose eq40 eq46 -- superposition 46,40
  have eq3453 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3))))) = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq40 eq46 -- superposition 46,40
  have eq3489 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))))) := superpose eq46 eq46 -- superposition 46,46
  have eq3583 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq46 eq39 -- superposition 39,46
  have eq3703 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) = (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))))) := superpose eq15 eq3410 -- forward demodulation 3410,15
  have eq3704 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)))))) := superpose eq15 eq3703 -- forward demodulation 3703,15
  have eq3705 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))))))) := superpose eq15 eq3704 -- forward demodulation 3704,15
  have eq3706 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))))))) := superpose eq15 eq3705 -- forward demodulation 3705,15
  have eq3707 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))))))) := superpose eq15 eq3706 -- forward demodulation 3706,15
  have eq3708 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2))))) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))))))) := superpose eq15 eq3707 -- forward demodulation 3707,15
  have eq3709 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))))))) := superpose eq2670 eq3708 -- forward demodulation 3708,2670
  have eq3710 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))))))) := superpose eq1939 eq3709 -- forward demodulation 3709,1939
  have eq3811 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X2)) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) := superpose eq15 eq3440 -- forward demodulation 3440,15
  have eq3812 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) := superpose eq15 eq3811 -- forward demodulation 3811,15
  have eq3870 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))))) = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq15 eq3453 -- forward demodulation 3453,15
  have eq3871 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))))) = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq15 eq3870 -- forward demodulation 3870,15
  have eq3872 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq2670 eq3871 -- forward demodulation 3871,2670
  have eq3873 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq1939 eq3872 -- forward demodulation 3872,1939
  have eq4007 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) = ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) := superpose eq3812 eq3489 -- forward demodulation 3489,3812
  have eq4008 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) = ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) := superpose eq15 eq4007 -- forward demodulation 4007,15
  have eq4009 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) = (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq493 eq4008 -- forward demodulation 4008,493
  have eq4010 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq15 eq4009 -- forward demodulation 4009,15
  have eq4353 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq1175 eq811 -- superposition 811,1175
  have eq4539 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq2783 eq4353 -- forward demodulation 4353,2783
  have eq4555 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq4539 eq3309 -- backward demodulation 3309,4539
  have eq4610 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq4555 eq3583 -- backward demodulation 3583,4555
  have eq4611 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq4610 eq4010 -- backward demodulation 4010,4610
  have eq4613 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) = ((X1 ◇ (X0 ◇ X0)) ◇ X3) := superpose eq4611 eq370 -- backward demodulation 370,4611
  have eq4614 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq4611 eq402 -- backward demodulation 402,4611
  have eq4628 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) = (X1 ◇ ((X0 ◇ X0) ◇ X3)) := superpose eq15 eq4613 -- forward demodulation 4613,15
  have eq4629 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) = (X1 ◇ (X0 ◇ (X0 ◇ X3))) := superpose eq15 eq4628 -- forward demodulation 4628,15
  have eq4632 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X3))) := superpose eq4614 eq4629 -- backward demodulation 4629,4614
  have eq4639 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))))))) := superpose eq4632 eq3710 -- backward demodulation 3710,4632
  have eq4642 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq4632 eq3873 -- backward demodulation 3873,4632
  have eq4694 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))))) := superpose eq4632 eq4639 -- forward demodulation 4639,4632
  have eq4695 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) = (X3 ◇ (X0 ◇ X0)) := superpose eq4539 eq4694 -- forward demodulation 4694,4539
  have eq4696 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq4539 eq4695 -- forward demodulation 4695,4539
  have eq4697 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X3 ◇ (X0 ◇ X0)) := superpose eq4539 eq4696 -- forward demodulation 4696,4539
  have eq4704 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0))))) := superpose eq4632 eq4642 -- forward demodulation 4642,4632
  have eq4705 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X0)))) := superpose eq4539 eq4704 -- forward demodulation 4704,4539
  have eq4706 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X3 ◇ (X0 ◇ X0))) := superpose eq4539 eq4705 -- forward demodulation 4705,4539
  have eq7197 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X0)) := superpose eq4697 eq4706 -- superposition 4706,4697
  have eq7413 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq4706 eq783 -- superposition 783,4706
  subsumption eq7413 eq7197

theorem Equation4270_4300_4512_implies_Equation4268 (G : Type*) [Magma G]
    (h4270 : Equation4270 G) (h4300 : Equation4300 G) (h4512 : Equation4512 G) : Equation4268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4270 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := mod_symm (h4300 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq18 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq25 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq14 eq16 -- superposition 16,14
  have eq30 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq38 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq14 eq15 -- superposition 15,14
  have eq46 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq15 eq30 -- forward demodulation 30,15
  have eq62 (X0 X1 : G) : (X1 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK0 ◇ sK0)) := superpose eq14 eq25 -- superposition 25,14
  have eq495 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X3 ◇ (X0 ◇ X0)) := superpose eq18 eq38 -- superposition 38,18
  have eq693 (X0 X2 : G) : (X2 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK1)))) := superpose eq46 eq62 -- superposition 62,46
  subsumption eq693 eq495

theorem Equation4270_4314_4512_implies_Equation4269 (G : Type*) [Magma G]
    (h4270 : Equation4270 G) (h4314 : Equation4314 G) (_ : Equation4512 G) : Equation4269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4270 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4314 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq18 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq130 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq18 eq16 -- superposition 16,18
  subsumption eq130 rfl

theorem Equation4270_4320_4512_implies_Equation4273 (G : Type*) [Magma G]
    (h4270 : Equation4270 G) (h4320 : Equation4320 G) (_ : Equation4512 G) : Equation4273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4270 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq24 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq24 eq13

theorem Equation4270_4321_4512_implies_Equation4272 (G : Type*) [Magma G]
    (h4270 : Equation4270 G) (h4321 : Equation4321 G) (h4512 : Equation4512 G) : Equation4272 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4270 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4321 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq13 eq13 -- superposition 13,13
  have eq20 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq14 eq14 -- superposition 14,14
  have eq28 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq15 eq20 -- forward demodulation 20,15
  have eq34 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq35 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq13 eq15 -- superposition 15,13
  have eq36 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq43 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq13 -- superposition 13,15
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq15 eq34 -- forward demodulation 34,15
  have eq52 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq35 -- forward demodulation 35,15
  have eq53 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq15 eq36 -- forward demodulation 36,15
  have eq65 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq17 eq17 -- superposition 17,17
  have eq99 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq15 eq65 -- forward demodulation 65,15
  have eq126 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq14 eq43 -- superposition 43,14
  have eq128 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X3)) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq43 eq43 -- superposition 43,43
  have eq158 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := superpose eq15 eq126 -- forward demodulation 126,15
  have eq159 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq43 eq158 -- forward demodulation 158,43
  have eq162 (X0 X3 : G) : (X3 ◇ (X3 ◇ X3)) = (X3 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq159 eq128 -- forward demodulation 128,159
  have eq193 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X2 ◇ X3))) = ((X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ X3) := superpose eq17 eq51 -- superposition 51,17
  have eq265 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X2 ◇ X3))) = ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) := superpose eq15 eq193 -- forward demodulation 193,15
  have eq486 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X3 ◇ X2))) = ((X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) ◇ X2) := superpose eq52 eq52 -- superposition 52,52
  have eq529 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq162 eq52 -- superposition 52,162
  have eq605 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X2))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X3 ◇ X2))) := superpose eq265 eq486 -- forward demodulation 486,265
  have eq678 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq529 eq605 -- backward demodulation 605,529
  have eq841 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq13 eq678 -- superposition 678,13
  have eq889 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq841 eq99 -- backward demodulation 99,841
  have eq1582 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq889 eq678 -- superposition 678,889
  have eq1591 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X3)))) := superpose eq889 eq53 -- superposition 53,889
  have eq2957 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq28 -- superposition 28,15
  have eq2997 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)))) := superpose eq889 eq28 -- superposition 28,889
  have eq3019 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq53 eq28 -- superposition 28,53
  have eq3020 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := superpose eq15 eq28 -- superposition 28,15
  have eq3329 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq15 eq2957 -- forward demodulation 2957,15
  have eq3422 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))))) := superpose eq15 eq2997 -- forward demodulation 2997,15
  have eq3423 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))))) := superpose eq15 eq3422 -- forward demodulation 3422,15
  have eq3424 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := superpose eq841 eq3423 -- forward demodulation 3423,841
  have eq3425 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) = ((X3 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X3)))) := superpose eq15 eq3424 -- forward demodulation 3424,15
  have eq3426 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) = ((X3 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X3))))) := superpose eq15 eq3425 -- forward demodulation 3425,15
  have eq3477 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq15 eq3019 -- forward demodulation 3019,15
  have eq3478 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq15 eq3477 -- forward demodulation 3477,15
  have eq3479 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq1591 eq3020 -- forward demodulation 3020,1591
  have eq3480 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq3479 -- forward demodulation 3479,15
  have eq3481 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq3480 -- forward demodulation 3480,15
  have eq3482 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq3481 -- forward demodulation 3481,15
  have eq3483 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq3482 eq3329 -- backward demodulation 3329,3482
  have eq5830 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2)))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X3) := superpose eq889 eq529 -- superposition 529,889
  have eq5840 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq13 eq529 -- superposition 529,13
  have eq6006 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) = (((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) ◇ X3) := superpose eq1582 eq5830 -- forward demodulation 5830,1582
  have eq6007 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X3) := superpose eq15 eq6006 -- forward demodulation 6006,15
  have eq6008 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X3) := superpose eq1582 eq6007 -- forward demodulation 6007,1582
  have eq6009 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X1))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := superpose eq6008 eq3426 -- backward demodulation 3426,6008
  have eq6013 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X1)) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq5840 eq6009 -- backward demodulation 6009,5840
  have eq6023 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq6013 eq28 -- backward demodulation 28,6013
  have eq6116 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq6023 eq3478 -- backward demodulation 3478,6023
  have eq6162 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq6116 eq3483 -- backward demodulation 3483,6116
  have eq6200 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq6013 eq6162 -- forward demodulation 6162,6013
  have eq6201 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq6013 eq6200 -- forward demodulation 6200,6013
  have eq7748 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := superpose eq6116 eq6201 -- superposition 6201,6116
  have eq8366 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq7748 eq16 -- superposition 16,7748
  subsumption eq8366 eq13

theorem Equation4270_4343_4512_implies_Equation4272 (G : Type*) [Magma G]
    (h4270 : Equation4270 G) (h4343 : Equation4343 G) (_ : Equation4512 G) : Equation4272 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4270 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4343 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq20 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq20 eq13

theorem Equation4271_4272_4512_implies_Equation4274 (G : Type*) [Magma G]
    (h4271 : Equation4271 G) (h4272 : Equation4272 G) (_ : Equation4512 G) : Equation4274 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h4271 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4272 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq17 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X4)) := superpose eq13 eq13 -- superposition 13,13
  have eq72 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X3)) := superpose eq14 eq17 -- superposition 17,14
  have eq97 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (X0 ◇ X1)) := superpose eq17 eq16 -- superposition 16,17
  subsumption eq97 eq72

theorem Equation4272_4273_4512_implies_Equation4270 (G : Type*) [Magma G]
    (h4272 : Equation4272 G) (h4273 : Equation4273 G) (_ : Equation4512 G) : Equation4270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4272 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4273 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq21 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq14 eq14 -- superposition 14,14
  have eq22 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ X2)) := superpose eq13 eq14 -- superposition 14,13
  have eq197 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq22 eq21 -- superposition 21,22
  have eq202 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq22 eq16 -- superposition 16,22
  have eq420 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ X0))) := superpose eq14 eq202 -- superposition 202,14
  subsumption eq420 eq197

theorem Equation4272_4275_4512_implies_Equation4304 (G : Type*) [Magma G]
    (h4272 : Equation4272 G) (h4275 : Equation4275 G) (_ : Equation4512 G) : Equation4304 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4272 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4275 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq19 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq13 eq16 -- superposition 16,13
  subsumption eq19 eq14

theorem Equation4272_4276_4512_implies_Equation4270 (G : Type*) [Magma G]
    (h4272 : Equation4272 G) (h4276 : Equation4276 G) (_ : Equation4512 G) : Equation4270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4272 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := mod_symm (h4276 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := superpose eq13 eq13 -- superposition 13,13
  have eq22 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X2 ◇ X2)) := superpose eq13 eq14 -- superposition 14,13
  have eq85 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq17 eq16 -- superposition 16,17
  subsumption eq85 eq22

theorem Equation4272_4283_4512_implies_Equation4270 (G : Type*) [Magma G]
    (h4272 : Equation4272 G) (h4283 : Equation4283 G) (h4512 : Equation4512 G) : Equation4270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4272 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := superpose eq13 eq13 -- superposition 13,13
  have eq19 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq21 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq15 eq19 -- forward demodulation 19,15
  have eq30 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq13 eq15 -- superposition 15,13
  have eq78 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq17 eq16 -- superposition 16,17
  have eq134 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) = ((X2 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq30 eq15 -- superposition 15,30
  have eq145 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) := superpose eq15 eq134 -- forward demodulation 134,15
  have eq146 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := superpose eq15 eq145 -- forward demodulation 145,15
  have eq155 (X0 X1 : G) : (X0 ◇ (sK0 ◇ sK0)) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq13 eq78 -- superposition 78,13
  have eq182 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq14 eq21 -- superposition 21,14
  have eq243 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq146 eq182 -- forward demodulation 182,146
  have eq244 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq30 eq243 -- forward demodulation 243,30
  have eq1701 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X1)) := superpose eq17 eq244 -- superposition 244,17
  have eq1744 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq244 eq155 -- superposition 155,244
  subsumption eq1744 eq1701

theorem Equation4272_4284_4512_implies_Equation4275 (G : Type*) [Magma G]
    (h4272 : Equation4272 G) (h4284 : Equation4284 G) (_ : Equation4512 G) : Equation4275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4272 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq23 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq23 eq13

theorem Equation4272_4287_4512_implies_Equation4278 (G : Type*) [Magma G]
    (h4272 : Equation4272 G) (h4287 : Equation4287 G) (_ : Equation4512 G) : Equation4278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4272 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X1)) := mod_symm (h4287 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq29 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq31 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq31 eq29

theorem Equation4272_4290_4512_implies_Equation4268 (G : Type*) [Magma G]
    (h4272 : Equation4272 G) (h4290 : Equation4290 G) (_ : Equation4512 G) : Equation4268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4272 ..)
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4290 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq21 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq126 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq21 eq16 -- superposition 16,21
  subsumption eq126 rfl

theorem Equation4272_4293_4512_implies_Equation4270 (G : Type*) [Magma G]
    (h4272 : Equation4272 G) (h4293 : Equation4293 G) (h4512 : Equation4512 G) : Equation4270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4272 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4293 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := superpose eq13 eq13 -- superposition 13,13
  have eq19 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq21 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq15 eq19 -- forward demodulation 19,15
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq31 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq13 eq15 -- superposition 15,13
  have eq39 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq15 eq23 -- forward demodulation 23,15
  have eq49 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq31 eq21 -- backward demodulation 21,31
  have eq76 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq17 eq16 -- superposition 16,17
  have eq149 (X0 X1 : G) : (X0 ◇ (sK0 ◇ sK0)) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq13 eq76 -- superposition 76,13
  have eq168 (X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X2) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2))) := superpose eq31 eq39 -- superposition 39,31
  have eq254 (X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X2) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) := superpose eq15 eq168 -- forward demodulation 168,15
  have eq255 (X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = ((X1 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq49 eq254 -- forward demodulation 254,49
  have eq1826 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X1)) := superpose eq17 eq255 -- superposition 255,17
  have eq1864 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq255 eq149 -- superposition 149,255
  subsumption eq1864 eq1826

theorem Equation4272_4314_4512_implies_Equation4269 (G : Type*) [Magma G]
    (h4272 : Equation4272 G) (h4314 : Equation4314 G) (_ : Equation4512 G) : Equation4269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4272 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4314 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := superpose eq13 eq13 -- superposition 13,13
  have eq24 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq65 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X1)) := superpose eq14 eq17 -- superposition 17,14
  have eq113 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq24 eq24 -- superposition 24,24
  have eq147 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq65 eq65 -- superposition 65,65
  have eq344 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq113 eq16 -- superposition 16,113
  have eq598 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ X0))) := superpose eq24 eq344 -- superposition 344,24
  subsumption eq598 eq147

theorem Equation4272_4320_4512_implies_Equation4269 (G : Type*) [Magma G]
    (h4272 : Equation4272 G) (h4320 : Equation4320 G) (_ : Equation4512 G) : Equation4269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4272 ..)
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4320 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq21 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq136 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq21 eq16 -- superposition 16,21
  subsumption eq136 rfl

theorem Equation4272_4321_4512_implies_Equation4270 (G : Type*) [Magma G]
    (h4272 : Equation4272 G) (h4321 : Equation4321 G) (h4512 : Equation4512 G) : Equation4270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4272 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4321 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := superpose eq13 eq13 -- superposition 13,13
  have eq35 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq41 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq13 eq15 -- superposition 15,13
  have eq51 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq15 eq35 -- forward demodulation 35,15
  have eq86 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq17 eq16 -- superposition 16,17
  have eq118 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq15 eq41 -- superposition 41,15
  have eq142 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) = ((X2 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq41 eq15 -- superposition 15,41
  have eq157 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) := superpose eq15 eq142 -- forward demodulation 142,15
  have eq158 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := superpose eq15 eq157 -- forward demodulation 157,15
  have eq163 (X0 X1 : G) : (X0 ◇ (sK0 ◇ sK0)) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq13 eq86 -- superposition 86,13
  have eq233 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq51 eq14 -- superposition 14,51
  have eq423 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq158 eq233 -- forward demodulation 233,158
  have eq424 (X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = ((X1 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq118 eq423 -- forward demodulation 423,118
  have eq2967 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X1)) := superpose eq17 eq424 -- superposition 424,17
  have eq3019 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) ≠ (X1 ◇ (sK1 ◇ sK1)) := superpose eq424 eq163 -- superposition 163,424
  subsumption eq3019 eq2967

theorem Equation4272_4343_4512_implies_Equation4270 (G : Type*) [Magma G]
    (h4272 : Equation4272 G) (h4343 : Equation4343 G) (_ : Equation4512 G) : Equation4270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4272 ..)
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4343 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq20 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq124 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq20 eq16 -- superposition 16,20
  subsumption eq124 rfl

theorem Equation4273_4275_4512_implies_Equation4305 (G : Type*) [Magma G]
    (h4273 : Equation4273 G) (h4275 : Equation4275 G) (_ : Equation4512 G) : Equation4305 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4273 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4275 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq20 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq13 eq16 -- superposition 16,13
  subsumption eq20 eq14

theorem Equation4273_4276_4512_implies_Equation4269 (G : Type*) [Magma G]
    (h4273 : Equation4273 G) (h4276 : Equation4276 G) (_ : Equation4512 G) : Equation4269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4273 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := mod_symm (h4276 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq13 eq13 -- superposition 13,13
  have eq22 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X2)) := superpose eq13 eq14 -- superposition 14,13
  have eq98 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq17 eq16 -- superposition 16,17
  subsumption eq98 eq22

theorem Equation4273_4283_4512_implies_Equation4275 (G : Type*) [Magma G]
    (h4273 : Equation4273 G) (h4283 : Equation4283 G) (_ : Equation4512 G) : Equation4275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4273 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq21 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq21 eq13

theorem Equation4273_4284_4512_implies_Equation4269 (G : Type*) [Magma G]
    (h4273 : Equation4273 G) (h4284 : Equation4284 G) (h4512 : Equation4512 G) : Equation4269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4273 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq13 eq13 -- superposition 13,13
  have eq18 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq13 eq13 -- superposition 13,13
  have eq19 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq13 eq13 -- superposition 13,13
  have eq21 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq14 eq13 -- superposition 13,14
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq14 eq13 -- superposition 13,14
  have eq26 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq30 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq13 eq15 -- superposition 15,13
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq14 eq15 -- superposition 15,14
  have eq43 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq26 -- forward demodulation 26,15
  have eq49 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq31 -- forward demodulation 31,15
  have eq86 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq17 eq16 -- superposition 16,17
  have eq121 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq18 eq14 -- superposition 14,18
  have eq141 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq15 eq121 -- forward demodulation 121,15
  have eq142 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq13 eq141 -- forward demodulation 141,13
  have eq143 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq18 eq142 -- forward demodulation 142,18
  have eq145 (X0 X1 : G) : (X0 ◇ (sK0 ◇ X0)) ≠ (X1 ◇ (sK1 ◇ X1)) := superpose eq13 eq86 -- superposition 86,13
  have eq160 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X1))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq19 eq19 -- superposition 19,19
  have eq171 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq13 eq19 -- superposition 19,13
  have eq211 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X1))) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq43 eq160 -- forward demodulation 160,43
  have eq212 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X1))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq15 eq211 -- forward demodulation 211,15
  have eq213 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X1))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq14 eq212 -- forward demodulation 212,14
  have eq214 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X1))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq15 eq213 -- forward demodulation 213,15
  have eq215 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq13 eq214 -- forward demodulation 214,13
  have eq222 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq15 eq171 -- forward demodulation 171,15
  have eq223 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq15 eq222 -- forward demodulation 222,15
  have eq224 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq43 eq223 -- forward demodulation 223,43
  have eq225 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq15 eq224 -- forward demodulation 224,15
  have eq226 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) := superpose eq15 eq225 -- forward demodulation 225,15
  have eq227 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq15 eq226 -- forward demodulation 226,15
  have eq228 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq30 eq227 -- forward demodulation 227,30
  have eq341 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq21 eq21 -- superposition 21,21
  have eq406 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq14 eq341 -- forward demodulation 341,14
  have eq407 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq15 eq406 -- forward demodulation 406,15
  have eq408 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq49 eq407 -- forward demodulation 407,49
  have eq409 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq15 eq408 -- forward demodulation 408,15
  have eq566 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = ((X0 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq22 eq14 -- superposition 14,22
  have eq661 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = ((X0 ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq15 eq566 -- forward demodulation 566,15
  have eq662 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq13 eq661 -- forward demodulation 661,13
  have eq663 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq15 eq662 -- forward demodulation 662,15
  have eq664 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq143 eq663 -- forward demodulation 663,143
  have eq670 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq664 eq228 -- backward demodulation 228,664
  have eq683 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq670 eq409 -- backward demodulation 409,670
  have eq701 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq215 eq683 -- forward demodulation 683,215
  have eq1670 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq701 eq17 -- superposition 17,701
  have eq1683 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ≠ (X1 ◇ (sK1 ◇ X1)) := superpose eq701 eq145 -- superposition 145,701
  subsumption eq1683 eq1670

theorem Equation4273_4287_4512_implies_Equation4268 (G : Type*) [Magma G]
    (h4273 : Equation4273 G) (h4287 : Equation4287 G) (h4512 : Equation4512 G) : Equation4268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4273 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X1)) := mod_symm (h4287 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq13 eq13 -- superposition 13,13
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq31 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq14 eq16 -- superposition 16,14
  have eq50 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X3 ◇ X2)) := superpose eq15 eq14 -- superposition 14,15
  have eq74 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ (X1 ◇ sK1))) := superpose eq15 eq31 -- superposition 31,15
  have eq89 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := superpose eq14 eq17 -- superposition 17,14
  have eq400 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X0)) = (X3 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq24 eq50 -- superposition 50,24
  have eq2506 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq89 eq74 -- superposition 74,89
  subsumption eq2506 eq400

theorem Equation4273_4291_4512_implies_Equation4268 (G : Type*) [Magma G]
    (h4273 : Equation4273 G) (h4291 : Equation4291 G) (_ : Equation4512 G) : Equation4268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4273 ..)
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq136 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq20 eq16 -- superposition 16,20
  subsumption eq136 rfl

theorem Equation4273_4293_4512_implies_Equation4269 (G : Type*) [Magma G]
    (h4273 : Equation4273 G) (h4293 : Equation4293 G) (h4512 : Equation4512 G) : Equation4269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4273 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4293 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq13 eq13 -- superposition 13,13
  have eq19 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq13 eq13 -- superposition 13,13
  have eq20 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq14 eq13 -- superposition 13,14
  have eq24 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq27 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq13 eq15 -- superposition 15,13
  have eq29 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq14 eq15 -- superposition 15,14
  have eq41 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq24 -- forward demodulation 24,15
  have eq45 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq15 eq27 -- forward demodulation 27,15
  have eq46 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq15 eq45 -- forward demodulation 45,15
  have eq47 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq29 -- forward demodulation 29,15
  have eq48 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq47 eq46 -- backward demodulation 46,47
  have eq86 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq17 eq16 -- superposition 16,17
  have eq150 (X0 X1 : G) : (X0 ◇ (sK0 ◇ X0)) ≠ (X1 ◇ (sK1 ◇ X1)) := superpose eq13 eq86 -- superposition 86,13
  have eq181 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq15 eq19 -- superposition 19,15
  have eq191 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq15 eq19 -- superposition 19,15
  have eq208 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq19 eq13 -- superposition 13,19
  have eq255 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) := superpose eq41 eq181 -- forward demodulation 181,41
  have eq256 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) := superpose eq15 eq255 -- forward demodulation 255,15
  have eq257 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq15 eq256 -- forward demodulation 256,15
  have eq258 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq15 eq257 -- forward demodulation 257,15
  have eq291 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq15 eq208 -- forward demodulation 208,15
  have eq292 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq15 eq291 -- forward demodulation 291,15
  have eq293 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq41 eq292 -- forward demodulation 292,41
  have eq294 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq15 eq293 -- forward demodulation 293,15
  have eq295 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq15 eq294 -- forward demodulation 294,15
  have eq296 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq15 eq295 -- forward demodulation 295,15
  have eq297 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq258 eq296 -- forward demodulation 296,258
  have eq365 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq13 eq20 -- superposition 20,13
  have eq366 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq17 eq20 -- superposition 20,17
  have eq480 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq365 -- forward demodulation 365,15
  have eq481 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq41 eq480 -- forward demodulation 480,41
  have eq482 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq481 -- forward demodulation 481,15
  have eq483 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq482 -- forward demodulation 482,15
  have eq484 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq483 -- forward demodulation 483,15
  have eq485 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq47 eq484 -- forward demodulation 484,47
  have eq486 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq15 eq366 -- forward demodulation 366,15
  have eq487 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq15 eq486 -- forward demodulation 486,15
  have eq488 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq48 eq487 -- forward demodulation 487,48
  have eq489 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq297 eq488 -- forward demodulation 488,297
  have eq490 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq489 eq485 -- backward demodulation 485,489
  have eq585 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq20 eq490 -- superposition 490,20
  have eq613 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq15 eq585 -- forward demodulation 585,15
  have eq614 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq297 eq613 -- forward demodulation 613,297
  have eq615 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq614 eq191 -- backward demodulation 191,614
  have eq848 (X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = (X2 ◇ (X2 ◇ X2)) := superpose eq615 eq615 -- superposition 615,615
  have eq1416 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X2)) := superpose eq13 eq848 -- superposition 848,13
  have eq1453 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) ≠ (X1 ◇ (sK1 ◇ X1)) := superpose eq848 eq150 -- superposition 150,848
  subsumption eq1453 eq1416

theorem Equation4273_4314_4512_implies_Equation4269 (G : Type*) [Magma G]
    (h4273 : Equation4273 G) (h4314 : Equation4314 G) (_ : Equation4512 G) : Equation4269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4273 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4314 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq13 eq13 -- superposition 13,13
  have eq24 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq97 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq17 eq16 -- superposition 16,17
  have eq122 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq24 eq17 -- superposition 17,24
  have eq160 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq24 eq97 -- superposition 97,24
  subsumption eq160 eq122

theorem Equation4273_4320_4512_implies_Equation4270 (G : Type*) [Magma G]
    (h4273 : Equation4273 G) (h4320 : Equation4320 G) (_ : Equation4512 G) : Equation4270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4273 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq24 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq138 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq24 eq16 -- superposition 16,24
  subsumption eq138 rfl

theorem Equation4273_4321_4512_implies_Equation4269 (G : Type*) [Magma G]
    (h4273 : Equation4273 G) (h4321 : Equation4321 G) (_ : Equation4512 G) : Equation4269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4273 ..)
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4321 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq24 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq157 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq24 eq16 -- superposition 16,24
  subsumption eq157 rfl

theorem Equation4273_4343_4512_implies_Equation4269 (G : Type*) [Magma G]
    (h4273 : Equation4273 G) (h4343 : Equation4343 G) (h4512 : Equation4512 G) : Equation4269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4273 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4343 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq13 eq13 -- superposition 13,13
  have eq18 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq13 eq13 -- superposition 13,13
  have eq19 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq13 eq13 -- superposition 13,13
  have eq20 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq14 eq13 -- superposition 13,14
  have eq27 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq13 eq15 -- superposition 15,13
  have eq28 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq13 eq15 -- superposition 15,13
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq14 -- superposition 14,15
  have eq45 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq14 eq27 -- forward demodulation 27,14
  have eq46 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq15 eq45 -- forward demodulation 45,15
  have eq47 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq15 eq46 -- forward demodulation 46,15
  have eq86 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq17 eq16 -- superposition 16,17
  have eq102 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq14 eq18 -- superposition 18,14
  have eq128 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq15 eq102 -- forward demodulation 102,15
  have eq139 (X0 X1 : G) : (X0 ◇ (sK0 ◇ X0)) ≠ (X1 ◇ (sK1 ◇ X1)) := superpose eq13 eq86 -- superposition 86,13
  have eq165 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq13 eq19 -- superposition 19,13
  have eq199 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq19 eq13 -- superposition 13,19
  have eq200 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq19 eq18 -- superposition 18,19
  have eq217 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq15 eq165 -- forward demodulation 165,15
  have eq218 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq15 eq217 -- forward demodulation 217,15
  have eq219 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq15 eq218 -- forward demodulation 218,15
  have eq220 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq47 eq219 -- forward demodulation 219,47
  have eq281 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq15 eq199 -- forward demodulation 199,15
  have eq282 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq15 eq281 -- forward demodulation 281,15
  have eq283 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq15 eq282 -- forward demodulation 282,15
  have eq284 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq14 eq283 -- forward demodulation 283,14
  have eq285 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq14 eq284 -- forward demodulation 284,14
  have eq286 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq15 eq285 -- forward demodulation 285,15
  have eq287 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq13 eq286 -- forward demodulation 286,13
  have eq289 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq287 eq128 -- backward demodulation 128,287
  have eq290 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)))) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq15 eq200 -- forward demodulation 200,15
  have eq291 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq15 eq290 -- forward demodulation 290,15
  have eq292 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq220 eq291 -- forward demodulation 291,220
  have eq293 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq15 eq292 -- forward demodulation 292,15
  have eq336 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) := superpose eq15 eq20 -- superposition 20,15
  have eq399 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq15 eq336 -- forward demodulation 336,15
  have eq467 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)))) := superpose eq19 eq28 -- superposition 28,19
  have eq534 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))))) := superpose eq15 eq467 -- forward demodulation 467,15
  have eq535 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))))) := superpose eq15 eq534 -- forward demodulation 534,15
  have eq536 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))))) := superpose eq15 eq535 -- forward demodulation 535,15
  have eq537 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))))) := superpose eq14 eq536 -- forward demodulation 536,14
  have eq538 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))))) := superpose eq14 eq537 -- forward demodulation 537,14
  have eq539 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))))) := superpose eq15 eq538 -- forward demodulation 538,15
  have eq540 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))))) := superpose eq13 eq539 -- forward demodulation 539,13
  have eq2204 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0)))))) := superpose eq20 eq31 -- superposition 31,20
  have eq2210 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq13 eq31 -- superposition 31,13
  have eq2350 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))))))) := superpose eq15 eq2204 -- forward demodulation 2204,15
  have eq2351 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))))))) := superpose eq15 eq2350 -- forward demodulation 2350,15
  have eq2352 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X2 ◇ X2)) := superpose eq540 eq2351 -- forward demodulation 2351,540
  have eq2353 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq289 eq2352 -- forward demodulation 2352,289
  have eq2368 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) = (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0))) := superpose eq2353 eq2210 -- forward demodulation 2210,2353
  have eq2369 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) = (X2 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) := superpose eq15 eq2368 -- forward demodulation 2368,15
  have eq2370 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) = ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq15 eq2369 -- forward demodulation 2369,15
  have eq2371 (X1 X2 : G) : (X2 ◇ (X1 ◇ (X1 ◇ X1))) = ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq289 eq2370 -- forward demodulation 2370,289
  have eq2373 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X1 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq2371 eq2353 -- backward demodulation 2353,2371
  have eq2413 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq2373 eq293 -- backward demodulation 293,2373
  have eq2444 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq399 eq2413 -- forward demodulation 2413,399
  have eq3837 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := superpose eq19 eq2444 -- superposition 2444,19
  have eq4788 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X2)) := superpose eq13 eq3837 -- superposition 3837,13
  have eq4833 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) ≠ (X1 ◇ (sK1 ◇ X1)) := superpose eq3837 eq139 -- superposition 139,3837
  subsumption eq4833 eq4788

theorem Equation4275_4276_4512_implies_Equation4268 (G : Type*) [Magma G]
    (h4275 : Equation4275 G) (h4276 : Equation4276 G) (_ : Equation4512 G) : Equation4268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4275 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := mod_symm (h4276 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq13 eq13 -- superposition 13,13
  have eq20 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X2)) := superpose eq13 eq14 -- superposition 14,13
  have eq90 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (X0 ◇ sK1)) := superpose eq17 eq16 -- superposition 16,17
  subsumption eq90 eq20

theorem Equation4275_4283_4512_implies_Equation4273 (G : Type*) [Magma G]
    (h4275 : Equation4275 G) (h4283 : Equation4283 G) (_ : Equation4512 G) : Equation4273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4275 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq18 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq118 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq18 eq16 -- superposition 16,18
  subsumption eq118 rfl

theorem Equation4275_4284_4512_implies_Equation4272 (G : Type*) [Magma G]
    (h4275 : Equation4275 G) (h4284 : Equation4284 G) (_ : Equation4512 G) : Equation4272 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4275 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq19 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq115 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq19 eq16 -- superposition 16,19
  subsumption eq115 rfl

theorem Equation4275_4290_4512_implies_Equation4270 (G : Type*) [Magma G]
    (h4275 : Equation4275 G) (h4290 : Equation4290 G) (_ : Equation4512 G) : Equation4270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4275 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq19 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq119 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq19 eq16 -- superposition 16,19
  subsumption eq119 rfl

theorem Equation4275_4291_4512_implies_Equation4269 (G : Type*) [Magma G]
    (h4275 : Equation4275 G) (h4291 : Equation4291 G) (_ : Equation4512 G) : Equation4269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4275 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq18 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq113 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq18 eq16 -- superposition 16,18
  subsumption eq113 rfl

theorem Equation4275_4293_4512_implies_Equation4268 (G : Type*) [Magma G]
    (h4275 : Equation4275 G) (h4293 : Equation4293 G) (_ : Equation4512 G) : Equation4268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4275 ..)
  have eq14 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4293 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq18 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq126 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq18 eq16 -- superposition 16,18
  subsumption eq126 rfl

theorem Equation4275_4314_4512_implies_Equation4268 (G : Type*) [Magma G]
    (h4275 : Equation4275 G) (h4314 : Equation4314 G) (h4512 : Equation4512 G) : Equation4268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4275 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4314 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq13 eq13 -- superposition 13,13
  have eq18 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- superposition 14,13
  have eq25 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq26 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = ((X1 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq27 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq28 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq14 eq15 -- superposition 15,14
  have eq31 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq13 eq15 -- superposition 15,13
  have eq41 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq13 -- superposition 13,15
  have eq42 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq15 eq25 -- forward demodulation 25,15
  have eq43 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq26 -- forward demodulation 26,15
  have eq44 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq15 eq27 -- forward demodulation 27,15
  have eq45 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq28 -- forward demodulation 28,15
  have eq50 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq31 -- forward demodulation 31,15
  have eq80 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (X0 ◇ sK1)) := superpose eq17 eq16 -- superposition 16,17
  have eq124 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X2 ◇ (X2 ◇ X1))) := superpose eq17 eq41 -- superposition 41,17
  have eq172 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq124 eq18 -- backward demodulation 18,124
  have eq199 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq15 eq172 -- superposition 172,15
  have eq203 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq172 eq14 -- superposition 14,172
  have eq205 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq172 eq15 -- superposition 15,172
  have eq220 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq203 -- forward demodulation 203,15
  have eq221 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq205 -- forward demodulation 205,15
  have eq222 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq15 eq221 -- forward demodulation 221,15
  have eq223 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq222 -- forward demodulation 222,15
  have eq244 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X2 ◇ X3))) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3) := superpose eq42 eq42 -- superposition 42,42
  have eq334 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X2 ◇ X3))) = ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2))))) ◇ X3) := superpose eq15 eq244 -- forward demodulation 244,15
  have eq335 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X2 ◇ X3))) = ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))))) ◇ X3) := superpose eq15 eq334 -- forward demodulation 334,15
  have eq445 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X0))) = (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X0)))) := superpose eq41 eq199 -- superposition 199,41
  have eq446 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq199 -- superposition 199,13
  have eq452 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq17 eq199 -- superposition 199,17
  have eq461 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq199 eq15 -- superposition 15,199
  have eq476 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq15 eq445 -- forward demodulation 445,15
  have eq478 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq446 eq220 -- backward demodulation 220,446
  have eq529 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq15 eq461 -- forward demodulation 461,15
  have eq530 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq15 eq529 -- forward demodulation 529,15
  have eq532 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X2 ◇ X3))) = ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2))))) ◇ X3) := superpose eq530 eq335 -- backward demodulation 335,530
  have eq557 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = (X2 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq172 eq43 -- superposition 43,172
  have eq558 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X2) := superpose eq15 eq43 -- superposition 43,15
  have eq568 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) = ((X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) ◇ X2) := superpose eq43 eq43 -- superposition 43,43
  have eq569 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))))) := superpose eq41 eq43 -- superposition 43,41
  have eq571 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X2 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq13 eq43 -- superposition 43,13
  have eq595 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X2) := superpose eq15 eq43 -- superposition 43,15
  have eq597 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1) = (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq43 eq43 -- superposition 43,43
  have eq612 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq15 eq43 -- superposition 43,15
  have eq631 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq43 eq42 -- superposition 42,43
  have eq669 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq15 eq557 -- forward demodulation 557,15
  have eq670 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq14 eq669 -- forward demodulation 669,14
  have eq671 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq15 eq670 -- forward demodulation 670,15
  have eq672 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq452 eq671 -- forward demodulation 671,452
  have eq673 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X2) := superpose eq15 eq558 -- forward demodulation 558,15
  have eq674 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2) := superpose eq50 eq673 -- forward demodulation 673,50
  have eq675 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq478 eq674 -- forward demodulation 674,478
  have eq676 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq675 -- forward demodulation 675,15
  have eq701 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) = ((X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ X2) := superpose eq14 eq568 -- forward demodulation 568,14
  have eq702 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) = ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) ◇ X2) := superpose eq15 eq701 -- forward demodulation 701,15
  have eq703 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) = ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) ◇ X2) := superpose eq15 eq702 -- forward demodulation 702,15
  have eq704 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) = ((X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ X2) := superpose eq676 eq703 -- forward demodulation 703,676
  have eq705 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) = ((X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X2) := superpose eq15 eq704 -- forward demodulation 704,15
  have eq706 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) = ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X2) := superpose eq15 eq705 -- forward demodulation 705,15
  have eq707 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) := superpose eq532 eq706 -- forward demodulation 706,532
  have eq708 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X3 ◇ (X3 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2)))) := superpose eq15 eq707 -- forward demodulation 707,15
  have eq709 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2))))) := superpose eq15 eq708 -- forward demodulation 708,15
  have eq712 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq15 eq569 -- forward demodulation 569,15
  have eq713 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = (X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) := superpose eq676 eq712 -- forward demodulation 712,676
  have eq714 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = (X2 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq15 eq713 -- forward demodulation 713,15
  have eq715 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq15 eq714 -- forward demodulation 714,15
  have eq724 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X2 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose eq14 eq571 -- forward demodulation 571,14
  have eq725 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose eq15 eq724 -- forward demodulation 724,15
  have eq726 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq15 eq725 -- forward demodulation 725,15
  have eq727 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq676 eq726 -- forward demodulation 726,676
  have eq728 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X2 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq15 eq727 -- forward demodulation 727,15
  have eq729 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq15 eq728 -- forward demodulation 728,15
  have eq730 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq715 eq729 -- forward demodulation 729,715
  have eq731 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq478 eq730 -- forward demodulation 730,478
  have eq782 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X2) := superpose eq43 eq595 -- forward demodulation 595,43
  have eq783 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) := superpose eq15 eq782 -- forward demodulation 782,15
  have eq784 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq15 eq783 -- forward demodulation 783,15
  have eq789 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1) = (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq43 eq597 -- forward demodulation 597,43
  have eq790 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) := superpose eq15 eq789 -- forward demodulation 789,15
  have eq791 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) := superpose eq14 eq790 -- forward demodulation 790,14
  have eq792 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq15 eq791 -- forward demodulation 791,15
  have eq793 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq452 eq792 -- forward demodulation 792,452
  have eq825 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq15 eq612 -- forward demodulation 612,15
  have eq869 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = ((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1) := superpose eq793 eq631 -- forward demodulation 631,793
  have eq870 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = ((X3 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X1) := superpose eq478 eq869 -- forward demodulation 869,478
  have eq871 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = ((X0 ◇ (X0 ◇ X3)) ◇ X1) := superpose eq446 eq870 -- forward demodulation 870,446
  have eq990 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq172 eq478 -- superposition 478,172
  have eq992 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq15 eq478 -- superposition 478,15
  have eq996 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X2 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq478 -- superposition 478,13
  have eq1038 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq14 eq990 -- forward demodulation 990,14
  have eq1039 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq1038 -- forward demodulation 1038,15
  have eq1040 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq223 eq1039 -- forward demodulation 1039,223
  have eq1041 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq15 eq1040 -- forward demodulation 1040,15
  have eq1042 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq452 eq1041 -- forward demodulation 1041,452
  have eq1043 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq478 eq1042 -- forward demodulation 1042,478
  have eq1055 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq1043 eq709 -- backward demodulation 709,1043
  have eq1063 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq1043 eq784 -- backward demodulation 784,1043
  have eq1075 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq1055 eq672 -- backward demodulation 672,1055
  have eq1078 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X3)) ◇ X1) := superpose eq1075 eq871 -- backward demodulation 871,1075
  have eq1096 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := superpose eq15 eq992 -- forward demodulation 992,15
  have eq1097 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq825 eq1096 -- forward demodulation 1096,825
  have eq1098 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq15 eq1097 -- forward demodulation 1097,15
  have eq1099 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq15 eq1098 -- forward demodulation 1098,15
  have eq1100 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq1043 eq1099 -- forward demodulation 1099,1043
  have eq1101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq1100 -- forward demodulation 1100,15
  have eq1180 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) := superpose eq172 eq44 -- superposition 44,172
  have eq1185 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3))) = ((X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) ◇ X3) := superpose eq43 eq44 -- superposition 44,43
  have eq1242 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X3) = (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))))) := superpose eq42 eq44 -- superposition 44,42
  have eq1251 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2))) = (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) ◇ X2) := superpose eq44 eq43 -- superposition 43,44
  have eq1302 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) := superpose eq996 eq1180 -- forward demodulation 1180,996
  have eq1303 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq1302 -- forward demodulation 1302,15
  have eq1304 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq1303 -- forward demodulation 1303,15
  have eq1305 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq1304 -- forward demodulation 1304,15
  have eq1327 (X0 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3))) = ((X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X3) := superpose eq793 eq1185 -- forward demodulation 1185,793
  have eq1328 (X0 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3))) = ((X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X3) := superpose eq15 eq1327 -- forward demodulation 1327,15
  have eq1329 (X0 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3))) = ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X3) := superpose eq15 eq1328 -- forward demodulation 1328,15
  have eq1330 (X0 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3))) = ((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X3) := superpose eq452 eq1329 -- forward demodulation 1329,452
  have eq1331 (X0 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3))) = (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X3)) := superpose eq15 eq1330 -- forward demodulation 1330,15
  have eq1332 (X0 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X3))) := superpose eq15 eq1331 -- forward demodulation 1331,15
  have eq1333 (X0 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X3)))) := superpose eq15 eq1332 -- forward demodulation 1332,15
  have eq1334 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X3))) = (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3))) := superpose eq1043 eq1333 -- forward demodulation 1333,1043
  have eq1335 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X3))) = (X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3)))) := superpose eq15 eq1334 -- forward demodulation 1334,15
  have eq1336 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X3))) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3))))) := superpose eq15 eq1335 -- forward demodulation 1335,15
  have eq1337 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X3))) = (X2 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3)) := superpose eq1063 eq1336 -- forward demodulation 1336,1063
  have eq1338 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X3))) = (X2 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3))) := superpose eq15 eq1337 -- forward demodulation 1337,15
  have eq1339 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X3))) = (X2 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3)))) := superpose eq15 eq1338 -- forward demodulation 1338,15
  have eq1478 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X3) = (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X3)))))) := superpose eq15 eq1242 -- forward demodulation 1242,15
  have eq1479 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X3) = (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X3))))))) := superpose eq15 eq1478 -- forward demodulation 1478,15
  have eq1480 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X3))))))) = ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) ◇ X3) := superpose eq15 eq1479 -- forward demodulation 1479,15
  have eq1481 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X3) = (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X3))))))) := superpose eq15 eq1480 -- forward demodulation 1480,15
  have eq1482 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X3))))))) := superpose eq1078 eq1481 -- forward demodulation 1481,1078
  have eq1518 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2))) = ((X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))))) ◇ X2) := superpose eq15 eq1251 -- forward demodulation 1251,15
  have eq1519 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2))) = ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))))) ◇ X2) := superpose eq15 eq1518 -- forward demodulation 1518,15
  have eq1520 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2))) = ((X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))))) ◇ X2) := superpose eq1305 eq1519 -- forward demodulation 1519,1305
  have eq1521 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X3 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2))) := superpose eq1078 eq1520 -- forward demodulation 1520,1078
  have eq1522 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2)))) := superpose eq15 eq1521 -- forward demodulation 1521,15
  have eq1523 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) := superpose eq15 eq1522 -- forward demodulation 1522,15
  have eq1524 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X3)))) := superpose eq1523 eq1482 -- backward demodulation 1482,1523
  have eq1525 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ X3)) = (X2 ◇ (X0 ◇ (X0 ◇ X3))) := superpose eq1524 eq1339 -- backward demodulation 1339,1524
  have eq1546 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq1525 eq1101 -- backward demodulation 1101,1525
  have eq1817 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq15 eq731 -- superposition 731,15
  have eq1922 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq15 eq1817 -- forward demodulation 1817,15
  have eq1923 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq15 eq1922 -- forward demodulation 1922,15
  have eq1924 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq1546 eq1923 -- forward demodulation 1923,1546
  have eq1925 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) := superpose eq1924 eq476 -- backward demodulation 476,1924
  have eq3195 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X2)) = (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) := superpose eq45 eq50 -- superposition 50,45
  have eq3464 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X2)) = (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))))) := superpose eq15 eq3195 -- forward demodulation 3195,15
  have eq3465 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))))) := superpose eq15 eq3464 -- forward demodulation 3464,15
  have eq3466 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2))))))) := superpose eq1525 eq3465 -- forward demodulation 3465,1525
  have eq3467 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) := superpose eq1525 eq3466 -- forward demodulation 3466,1525
  have eq3468 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X2)) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq1925 eq3467 -- forward demodulation 3467,1925
  have eq4221 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ sK1))) := superpose eq1078 eq80 -- superposition 80,1078
  have eq4468 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ sK1)))) := superpose eq15 eq4221 -- forward demodulation 4221,15
  subsumption eq4468 eq3468

theorem Equation4275_4315_4512_implies_Equation4269 (G : Type*) [Magma G]
    (h4275 : Equation4275 G) (h4315 : Equation4315 G) (_ : Equation4512 G) : Equation4269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4275 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h4315 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq25 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = (X2 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq13 eq14 -- superposition 14,13
  have eq29 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq14 eq16 -- superposition 16,14
  have eq74 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq13 eq29 -- superposition 29,13
  subsumption eq74 eq25

theorem Equation4275_4321_4512_implies_Equation4268 (G : Type*) [Magma G]
    (h4275 : Equation4275 G) (h4321 : Equation4321 G) (h4512 : Equation4512 G) : Equation4268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4275 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4321 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq13 eq13 -- superposition 13,13
  have eq18 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq14 -- superposition 14,13
  have eq26 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq15 eq18 -- forward demodulation 18,15
  have eq34 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq50 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq13 -- superposition 13,15
  have eq51 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq15 eq34 -- forward demodulation 34,15
  have eq91 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (X0 ◇ sK1)) := superpose eq17 eq16 -- superposition 16,17
  have eq141 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X2 ◇ (X2 ◇ X1))) := superpose eq17 eq50 -- superposition 50,17
  have eq195 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq141 eq26 -- backward demodulation 26,141
  have eq223 (X0 X1 : G) : (X0 ◇ (X0 ◇ sK0)) ≠ (X1 ◇ (X1 ◇ sK1)) := superpose eq13 eq91 -- superposition 91,13
  have eq235 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq195 -- superposition 195,13
  have eq246 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq195 eq15 -- superposition 15,195
  have eq266 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq15 eq246 -- forward demodulation 246,15
  have eq267 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq15 eq266 -- forward demodulation 266,15
  have eq304 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X2)) = (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)))) := superpose eq17 eq51 -- superposition 51,17
  have eq309 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq14 eq51 -- superposition 51,14
  have eq343 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq51 eq13 -- superposition 13,51
  have eq359 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ sK1)) ≠ (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ sK0)))) := superpose eq51 eq223 -- superposition 223,51
  have eq395 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X2)) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) := superpose eq15 eq304 -- forward demodulation 304,15
  have eq396 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X2)) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))))) := superpose eq15 eq395 -- forward demodulation 395,15
  have eq409 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))))) = (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq15 eq309 -- forward demodulation 309,15
  have eq410 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))))) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq409 -- forward demodulation 409,15
  have eq448 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq235 eq343 -- forward demodulation 343,235
  have eq449 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq235 eq448 -- forward demodulation 448,235
  have eq450 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq235 eq449 -- forward demodulation 449,235
  have eq472 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ sK1)) ≠ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ sK0))))) := superpose eq15 eq359 -- forward demodulation 359,15
  have eq473 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ sK1)) ≠ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ sK0)))))) := superpose eq15 eq472 -- forward demodulation 472,15
  have eq510 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1)))) := superpose eq17 eq235 -- superposition 235,17
  have eq517 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq235 eq235 -- superposition 235,235
  have eq530 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)))) = (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))))) := superpose eq51 eq235 -- superposition 235,51
  have eq547 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq235 eq50 -- superposition 50,235
  have eq557 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq235 eq517 -- forward demodulation 517,235
  have eq558 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq557 eq450 -- backward demodulation 450,557
  have eq563 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq558 eq396 -- backward demodulation 396,558
  have eq570 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ sK1)) ≠ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ sK0)))) := superpose eq558 eq473 -- backward demodulation 473,558
  have eq572 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq558 eq267 -- backward demodulation 267,558
  have eq620 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) = (X2 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)))) := superpose eq572 eq530 -- forward demodulation 530,572
  have eq621 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) = (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) := superpose eq15 eq620 -- forward demodulation 620,15
  have eq622 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) = (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))))) := superpose eq15 eq621 -- forward demodulation 621,15
  have eq623 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq558 eq622 -- forward demodulation 622,558
  have eq624 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq623 eq410 -- backward demodulation 410,623
  have eq649 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq558 eq547 -- forward demodulation 547,558
  have eq650 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = (X0 ◇ (X2 ◇ (X2 ◇ X1))) := superpose eq649 eq510 -- backward demodulation 510,649
  have eq660 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq650 eq624 -- backward demodulation 624,650
  have eq664 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq235 eq660 -- forward demodulation 660,235
  have eq665 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq235 eq664 -- forward demodulation 664,235
  have eq666 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq235 eq665 -- forward demodulation 665,235
  have eq670 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq666 eq563 -- backward demodulation 563,666
  have eq681 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ sK1)) ≠ (X1 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq666 eq570 -- backward demodulation 570,666
  subsumption eq681 eq670

theorem Equation4275_4343_4512_implies_Equation4268 (G : Type*) [Magma G]
    (h4275 : Equation4275 G) (h4343 : Equation4343 G) (h4512 : Equation4512 G) : Equation4268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4275 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4343 ..)
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq13 eq13 -- superposition 13,13
  have eq18 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq14 eq13 -- superposition 13,14
  have eq20 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq15 eq18 -- forward demodulation 18,15
  have eq22 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = ((X1 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq13 eq15 -- superposition 15,13
  have eq24 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq14 eq15 -- superposition 15,14
  have eq28 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq13 eq15 -- superposition 15,13
  have eq29 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq14 eq15 -- superposition 15,14
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq14 -- superposition 14,15
  have eq38 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq13 -- superposition 13,15
  have eq39 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq15 eq22 -- forward demodulation 22,15
  have eq40 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq23 -- forward demodulation 23,15
  have eq41 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq24 -- forward demodulation 24,15
  have eq47 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq15 eq28 -- forward demodulation 28,15
  have eq48 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq29 -- forward demodulation 29,15
  have eq55 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq17 -- superposition 17,13
  have eq79 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (X0 ◇ sK1)) := superpose eq17 eq16 -- superposition 16,17
  have eq100 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = ((X2 ◇ X3) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq15 eq38 -- superposition 38,15
  have eq119 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X0))) = ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X0)))) := superpose eq38 eq38 -- superposition 38,38
  have eq120 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq38 -- superposition 38,13
  have eq140 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) = ((X2 ◇ X3) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq14 eq100 -- forward demodulation 100,14
  have eq141 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = ((X2 ◇ X3) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq15 eq140 -- forward demodulation 140,15
  have eq164 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) = ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq15 eq119 -- forward demodulation 119,15
  have eq176 (X0 X1 : G) : (X0 ◇ (X0 ◇ sK0)) ≠ (X1 ◇ (X1 ◇ sK1)) := superpose eq13 eq79 -- superposition 79,13
  have eq239 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq39 eq17 -- superposition 17,39
  have eq363 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ sK1)) ≠ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ sK0)))) := superpose eq39 eq176 -- superposition 176,39
  have eq384 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X2) := superpose eq15 eq40 -- superposition 40,15
  have eq420 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1) = (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq40 eq40 -- superposition 40,40
  have eq443 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq40 eq13 -- superposition 13,40
  have eq463 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq40 eq14 -- superposition 14,40
  have eq485 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) ◇ X2) := superpose eq48 eq384 -- forward demodulation 384,48
  have eq486 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) ◇ X2) := superpose eq14 eq485 -- forward demodulation 485,14
  have eq487 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X2) := superpose eq15 eq486 -- forward demodulation 486,15
  have eq488 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X2) := superpose eq15 eq487 -- forward demodulation 487,15
  have eq562 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1) := superpose eq40 eq420 -- forward demodulation 420,40
  have eq563 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) := superpose eq15 eq562 -- forward demodulation 562,15
  have eq564 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) := superpose eq14 eq563 -- forward demodulation 563,14
  have eq565 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq15 eq564 -- forward demodulation 564,15
  have eq618 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq15 eq463 -- forward demodulation 463,15
  have eq619 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq15 eq618 -- forward demodulation 618,15
  have eq620 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose eq565 eq619 -- forward demodulation 619,565
  have eq621 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq15 eq620 -- forward demodulation 620,15
  have eq622 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq15 eq621 -- forward demodulation 621,15
  have eq623 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq15 eq622 -- forward demodulation 622,15
  have eq624 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq47 eq623 -- forward demodulation 623,47
  have eq665 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X3))) = ((X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) ◇ X3) := superpose eq41 eq41 -- superposition 41,41
  have eq666 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X3))) = ((X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) ◇ X3) := superpose eq40 eq41 -- superposition 41,40
  have eq691 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ (X0 ◇ X0)) = (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq38 eq41 -- superposition 41,38
  have eq772 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X3))) = ((X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X3) := superpose eq624 eq665 -- forward demodulation 665,624
  have eq827 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ (X0 ◇ X0)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))))) := superpose eq15 eq691 -- forward demodulation 691,15
  have eq1041 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq40 eq47 -- superposition 47,40
  have eq1051 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq40 eq47 -- superposition 47,40
  have eq1069 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))))) := superpose eq47 eq47 -- superposition 47,47
  have eq1072 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1)))) := superpose eq17 eq47 -- superposition 47,17
  have eq1156 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq14 eq1051 -- forward demodulation 1051,14
  have eq1157 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq15 eq1156 -- forward demodulation 1156,15
  have eq1158 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq14 eq1157 -- forward demodulation 1157,14
  have eq1159 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq15 eq1158 -- forward demodulation 1158,15
  have eq1204 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq1072 eq443 -- backward demodulation 443,1072
  have eq1205 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X2) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq1072 eq488 -- backward demodulation 488,1072
  have eq1210 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X3))) = ((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X3) := superpose eq1072 eq772 -- backward demodulation 772,1072
  have eq1219 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq1204 eq1041 -- backward demodulation 1041,1204
  have eq1221 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq1219 eq1159 -- backward demodulation 1159,1219
  have eq1225 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X3))) = ((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X3) := superpose eq1221 eq666 -- backward demodulation 666,1221
  have eq1237 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X3))) = (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X3)) := superpose eq15 eq1225 -- forward demodulation 1225,15
  have eq1238 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X3))) := superpose eq15 eq1237 -- forward demodulation 1237,15
  have eq1239 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X3)))) := superpose eq15 eq1238 -- forward demodulation 1238,15
  have eq1412 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq55 eq55 -- superposition 55,55
  have eq1436 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq13 eq55 -- superposition 55,13
  have eq1515 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) := superpose eq55 eq38 -- superposition 38,55
  have eq1524 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) = (X3 ◇ (X0 ◇ (X3 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))))) := superpose eq55 eq47 -- superposition 47,55
  have eq1558 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq1205 eq1436 -- forward demodulation 1436,1205
  have eq1559 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq15 eq1558 -- forward demodulation 1558,15
  have eq1560 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq15 eq1559 -- forward demodulation 1559,15
  have eq1561 (X0 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) := superpose eq1560 eq1412 -- backward demodulation 1412,1560
  have eq1715 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq15 eq1515 -- forward demodulation 1515,15
  have eq1723 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ X0)) = (X3 ◇ (X0 ◇ (X3 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))))) := superpose eq1072 eq1524 -- forward demodulation 1524,1072
  have eq1814 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq47 eq31 -- superposition 31,47
  have eq1836 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3))) := superpose eq31 eq41 -- superposition 41,31
  have eq2058 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3)))) := superpose eq15 eq1836 -- forward demodulation 1836,15
  have eq2059 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3))))) := superpose eq15 eq2058 -- forward demodulation 2058,15
  have eq2184 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((X2 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq17 eq1814 -- superposition 1814,17
  have eq2185 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((X2 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq17 eq1814 -- superposition 1814,17
  have eq2208 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq15 eq1814 -- superposition 1814,15
  have eq2248 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq2184 -- forward demodulation 2184,15
  have eq2249 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq141 eq2248 -- forward demodulation 2248,141
  have eq2250 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq1072 eq2249 -- forward demodulation 2249,1072
  have eq2251 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq2185 -- forward demodulation 2185,15
  have eq2252 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq2250 eq2251 -- forward demodulation 2251,2250
  have eq2254 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) := superpose eq2252 eq1715 -- backward demodulation 1715,2252
  have eq2255 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq2254 eq1561 -- backward demodulation 1561,2254
  have eq2256 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq2255 eq20 -- backward demodulation 20,2255
  have eq2481 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X3))) := superpose eq2208 eq1210 -- backward demodulation 1210,2208
  have eq2523 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X3) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X3)))) := superpose eq2481 eq1239 -- backward demodulation 1239,2481
  have eq2524 (X0 X2 X3 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X3)) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X3)))) := superpose eq15 eq2523 -- forward demodulation 2523,15
  have eq2525 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X3))) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X3)))) := superpose eq15 eq2524 -- forward demodulation 2524,15
  have eq2652 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) := superpose eq14 eq48 -- superposition 48,14
  have eq2659 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq39 eq48 -- superposition 48,39
  have eq2681 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))))) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X3 ◇ X3))) := superpose eq55 eq48 -- superposition 48,55
  have eq2685 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))))) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X3 ◇ X3))) := superpose eq55 eq48 -- superposition 48,55
  have eq2707 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))))))) = (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3))) := superpose eq39 eq48 -- superposition 48,39
  have eq2814 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3))))) = ((X0 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X3) := superpose eq2652 eq2059 -- backward demodulation 2059,2652
  have eq2830 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3))))) = (X0 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X3)) := superpose eq15 eq2814 -- forward demodulation 2814,15
  have eq2831 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3))))) = (X0 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3))) := superpose eq15 eq2830 -- forward demodulation 2830,15
  have eq2832 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3))))) = (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3)))) := superpose eq15 eq2831 -- forward demodulation 2831,15
  have eq2838 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ (X0 ◇ X0)) = (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0))))) := superpose eq2832 eq827 -- backward demodulation 827,2832
  have eq2839 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0))))) := superpose eq2832 eq1069 -- backward demodulation 1069,2832
  have eq2861 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq15 eq2659 -- forward demodulation 2659,15
  have eq2862 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq15 eq2861 -- forward demodulation 2861,15
  have eq2955 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))))) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X3 ◇ X3)))) := superpose eq15 eq2681 -- forward demodulation 2681,15
  have eq2956 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X3))))) := superpose eq15 eq2955 -- forward demodulation 2955,15
  have eq2957 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X3))))) = (X3 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) := superpose eq2838 eq2956 -- forward demodulation 2956,2838
  have eq2958 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X3))))) = (X3 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) := superpose eq15 eq2957 -- forward demodulation 2957,15
  have eq2959 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X3))))) = (X3 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq15 eq2958 -- forward demodulation 2958,15
  have eq2960 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X3))))) := superpose eq2862 eq2959 -- forward demodulation 2959,2862
  have eq2982 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))))) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X3 ◇ X3)))) := superpose eq15 eq2685 -- forward demodulation 2685,15
  have eq2983 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X3 ◇ X3))))) := superpose eq15 eq2982 -- forward demodulation 2982,15
  have eq2984 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0))))))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X3 ◇ X3))))) := superpose eq15 eq2983 -- forward demodulation 2983,15
  have eq2985 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))))))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X3 ◇ X3))))) := superpose eq15 eq2984 -- forward demodulation 2984,15
  have eq2986 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X3 ◇ X3))))) = (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0))))))) := superpose eq2862 eq2985 -- forward demodulation 2985,2862
  have eq2987 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X3 ◇ X3))))) = (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))))) := superpose eq2960 eq2986 -- forward demodulation 2986,2960
  have eq2988 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X3 ◇ X3))))) = (X3 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq2960 eq2987 -- forward demodulation 2987,2960
  have eq3102 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))))))) = (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X3)))) := superpose eq15 eq2707 -- forward demodulation 2707,15
  have eq3103 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))))))) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X3))))) := superpose eq15 eq3102 -- forward demodulation 3102,15
  have eq3104 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))))) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X3))))) := superpose eq2525 eq3103 -- forward demodulation 3103,2525
  have eq3449 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq47 eq2256 -- superposition 2256,47
  have eq3451 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq13 eq2256 -- superposition 2256,13
  have eq3546 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0))))) = (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) := superpose eq2832 eq3449 -- forward demodulation 3449,2832
  have eq3549 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq120 eq3451 -- forward demodulation 3451,120
  have eq3576 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) := superpose eq3549 eq2839 -- backward demodulation 2839,3549
  have eq3582 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq3549 eq3546 -- backward demodulation 3546,3549
  have eq3588 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) = (X1 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq3582 eq164 -- backward demodulation 164,3582
  have eq3601 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) := superpose eq3588 eq3576 -- backward demodulation 3576,3588
  have eq3612 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X3))))) = (X3 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq3601 eq3104 -- backward demodulation 3104,3601
  have eq3627 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X3))))) = (X3 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq3601 eq3612 -- forward demodulation 3612,3601
  have eq3628 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X3))))) = (X3 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq3601 eq3627 -- forward demodulation 3627,3601
  have eq3629 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = (X3 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq3628 eq2988 -- backward demodulation 2988,3628
  have eq3631 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X0))) = (X3 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq3549 eq3629 -- forward demodulation 3629,3549
  have eq3632 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ X0)) = (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq3631 eq1723 -- backward demodulation 1723,3631
  have eq3633 (X0 X3 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X3))) := superpose eq3632 eq2525 -- backward demodulation 2525,3632
  have eq3637 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq3633 eq239 -- backward demodulation 239,3633
  have eq3696 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ sK1)) ≠ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq3633 eq363 -- backward demodulation 363,3633
  subsumption eq3696 eq3637

theorem Equation4283_4284_4512_implies_Equation4314 (G : Type*) [Magma G]
    (h4283 : Equation4283 G) (h4284 : Equation4284 G) (_ : Equation4512 G) : Equation4314 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq17 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq17 eq13

theorem Equation4283_4290_4512_implies_Equation4320 (G : Type*) [Magma G]
    (h4283 : Equation4283 G) (h4290 : Equation4290 G) (_ : Equation4512 G) : Equation4320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq17 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq17 eq13

theorem Equation4283_4291_4512_implies_Equation4293 (G : Type*) [Magma G]
    (h4283 : Equation4283 G) (h4291 : Equation4291 G) (_ : Equation4512 G) : Equation4293 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq17 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq13 eq16 -- superposition 16,13
  subsumption eq17 eq14

theorem Equation4283_4291_4512_implies_Equation4321 (G : Type*) [Magma G]
    (h4283 : Equation4283 G) (h4291 : Equation4291 G) (_ : Equation4512 G) : Equation4321 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq17 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq17 eq13

theorem Equation4283_4293_4512_implies_Equation4291 (G : Type*) [Magma G]
    (h4283 : Equation4283 G) (h4293 : Equation4293 G) (_ : Equation4512 G) : Equation4291 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4293 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq69 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq17 eq16 -- superposition 16,17
  subsumption eq69 rfl

theorem Equation4283_4314_4512_implies_Equation4284 (G : Type*) [Magma G]
    (h4283 : Equation4283 G) (h4314 : Equation4314 G) (_ : Equation4512 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4314 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq23 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq23 eq13

theorem Equation4283_4320_4512_implies_Equation4290 (G : Type*) [Magma G]
    (h4283 : Equation4283 G) (h4320 : Equation4320 G) (_ : Equation4512 G) : Equation4290 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq24 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq24 eq13

theorem Equation4283_4321_4512_implies_Equation4291 (G : Type*) [Magma G]
    (h4283 : Equation4283 G) (h4321 : Equation4321 G) (_ : Equation4512 G) : Equation4291 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4321 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq27 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq27 eq13

theorem Equation4284_4290_4512_implies_Equation4293 (G : Type*) [Magma G]
    (h4284 : Equation4284 G) (h4290 : Equation4290 G) (_ : Equation4512 G) : Equation4293 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq18 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq13 eq16 -- superposition 16,13
  subsumption eq18 eq14

theorem Equation4284_4290_4512_implies_Equation4343 (G : Type*) [Magma G]
    (h4284 : Equation4284 G) (h4290 : Equation4290 G) (_ : Equation4512 G) : Equation4343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq17 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq17 eq13

theorem Equation4284_4291_4512_implies_Equation4320 (G : Type*) [Magma G]
    (h4284 : Equation4284 G) (h4291 : Equation4291 G) (_ : Equation4512 G) : Equation4320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq19 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq72 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq19 eq16 -- superposition 16,19
  subsumption eq72 rfl

theorem Equation4284_4293_4512_implies_Equation4290 (G : Type*) [Magma G]
    (h4284 : Equation4284 G) (h4293 : Equation4293 G) (_ : Equation4512 G) : Equation4290 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4293 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq20 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq76 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq20 eq16 -- superposition 16,20
  subsumption eq76 rfl

theorem Equation4284_4314_4512_implies_Equation4283 (G : Type*) [Magma G]
    (h4284 : Equation4284 G) (h4314 : Equation4314 G) (_ : Equation4512 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4314 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq19 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq76 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq19 eq16 -- superposition 16,19
  subsumption eq76 rfl

theorem Equation4284_4320_4512_implies_Equation4291 (G : Type*) [Magma G]
    (h4284 : Equation4284 G) (h4320 : Equation4320 G) (_ : Equation4512 G) : Equation4291 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq26 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq26 eq13

theorem Equation4284_4343_4512_implies_Equation4290 (G : Type*) [Magma G]
    (h4284 : Equation4284 G) (h4343 : Equation4343 G) (_ : Equation4512 G) : Equation4290 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4343 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq21 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq21 eq13

theorem Equation4290_4291_4512_implies_Equation4314 (G : Type*) [Magma G]
    (h4290 : Equation4290 G) (h4291 : Equation4291 G) (_ : Equation4512 G) : Equation4314 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq20 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq74 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq20 eq16 -- superposition 16,20
  subsumption eq74 rfl

theorem Equation4290_4293_4512_implies_Equation4284 (G : Type*) [Magma G]
    (h4290 : Equation4290 G) (h4293 : Equation4293 G) (_ : Equation4512 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4293 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq21 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq78 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq21 eq16 -- superposition 16,21
  subsumption eq78 rfl

theorem Equation4290_4314_4512_implies_Equation4291 (G : Type*) [Magma G]
    (h4290 : Equation4290 G) (h4314 : Equation4314 G) (_ : Equation4512 G) : Equation4291 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4314 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq26 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq26 eq13

theorem Equation4290_4320_4512_implies_Equation4283 (G : Type*) [Magma G]
    (h4290 : Equation4290 G) (h4320 : Equation4320 G) (_ : Equation4512 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4320 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq22 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq89 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq22 eq16 -- superposition 16,22
  subsumption eq89 rfl

theorem Equation4290_4343_4512_implies_Equation4284 (G : Type*) [Magma G]
    (h4290 : Equation4290 G) (h4343 : Equation4343 G) (_ : Equation4512 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4343 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq21 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq80 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq21 eq16 -- superposition 16,21
  subsumption eq80 rfl

theorem Equation4291_4293_4512_implies_Equation4283 (G : Type*) [Magma G]
    (h4291 : Equation4291 G) (h4293 : Equation4293 G) (_ : Equation4512 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4293 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq19 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq65 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq19 eq16 -- superposition 16,19
  subsumption eq65 rfl

theorem Equation4291_4314_4512_implies_Equation4290 (G : Type*) [Magma G]
    (h4291 : Equation4291 G) (h4314 : Equation4314 G) (_ : Equation4512 G) : Equation4290 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4314 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq23 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq69 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq23 eq16 -- superposition 16,23
  subsumption eq69 rfl

theorem Equation4291_4320_4512_implies_Equation4284 (G : Type*) [Magma G]
    (h4291 : Equation4291 G) (h4320 : Equation4320 G) (_ : Equation4512 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq23 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq79 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq23 eq16 -- superposition 16,23
  subsumption eq79 rfl

theorem Equation4291_4321_4512_implies_Equation4283 (G : Type*) [Magma G]
    (h4291 : Equation4291 G) (h4321 : Equation4321 G) (_ : Equation4512 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4321 ..)
  have eq16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq23 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq85 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq23 eq16 -- superposition 16,23
  subsumption eq85 rfl

theorem Equation4314_4320_4512_implies_Equation4321 (G : Type*) [Magma G]
    (h4314 : Equation4314 G) (h4320 : Equation4320 G) (_ : Equation4512 G) : Equation4321 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4314 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq19 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq13 eq16 -- superposition 16,13
  subsumption eq19 eq14

theorem Equation4314_4320_4512_implies_Equation4343 (G : Type*) [Magma G]
    (h4314 : Equation4314 G) (h4320 : Equation4320 G) (_ : Equation4512 G) : Equation4343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4314 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq17 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq14 eq16 -- forward demodulation 16,14
  subsumption eq17 eq13

theorem Equation4314_4321_4512_implies_Equation4320 (G : Type*) [Magma G]
    (h4314 : Equation4314 G) (h4321 : Equation4321 G) (_ : Equation4512 G) : Equation4320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4314 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4321 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq24 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq93 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq24 eq16 -- superposition 16,24
  subsumption eq93 rfl

theorem Equation4314_4343_4512_implies_Equation4320 (G : Type*) [Magma G]
    (h4314 : Equation4314 G) (h4343 : Equation4343 G) (_ : Equation4512 G) : Equation4320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4314 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4343 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq22 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq22 eq13

theorem Equation4320_4321_4512_implies_Equation4314 (G : Type*) [Magma G]
    (h4320 : Equation4320 G) (h4321 : Equation4321 G) (_ : Equation4512 G) : Equation4314 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4321 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq28 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq101 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq28 eq16 -- superposition 16,28
  subsumption eq101 rfl

theorem Equation4320_4343_4512_implies_Equation4314 (G : Type*) [Magma G]
    (h4320 : Equation4320 G) (h4343 : Equation4343 G) (_ : Equation4512 G) : Equation4314 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4343 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq27 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq92 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq27 eq16 -- superposition 16,27
  subsumption eq92 rfl

theorem Equation4358_4362_4512_implies_Equation4364 (G : Type*) [Magma G]
    (h4358 : Equation4358 G) (h4362 : Equation4362 G) (_ : Equation4512 G) : Equation4364 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := mod_symm (h4358 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h4362 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq21 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq13 eq16 -- superposition 16,13
  subsumption eq21 eq14

theorem Equation4358_4362_4512_implies_Equation4369 (G : Type*) [Magma G]
    (h4358 : Equation4358 G) (h4362 : Equation4362 G) (_ : Equation4512 G) : Equation4369 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := mod_symm (h4358 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h4362 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq31 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X1 ◇ (X0 ◇ X2)) := superpose eq13 eq14 -- superposition 14,13
  have eq39 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq39 eq31

theorem Equation4358_4364_4512_implies_Equation4362 (G : Type*) [Magma G]
    (h4358 : Equation4358 G) (h4364 : Equation4364 G) (_ : Equation4512 G) : Equation4362 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := mod_symm (h4358 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h4364 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq39 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := superpose eq14 eq16 -- superposition 16,14
  subsumption eq39 eq13

theorem Equation4358_4369_4512_implies_Equation4362 (G : Type*) [Magma G]
    (h4358 : Equation4358 G) (h4369 : Equation4369 G) (_ : Equation4512 G) : Equation4362 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := mod_symm (h4358 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := mod_symm (h4369 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq29 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq110 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := superpose eq29 eq16 -- superposition 16,29
  subsumption eq110 eq13

theorem Equation4362_4364_4512_implies_Equation4358 (G : Type*) [Magma G]
    (h4362 : Equation4362 G) (h4364 : Equation4364 G) (_ : Equation4512 G) : Equation4358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h4362 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h4364 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq26 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X2 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq123 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq26 eq16 -- superposition 16,26
  subsumption eq123 rfl

theorem Equation4362_4369_4512_implies_Equation4358 (G : Type*) [Magma G]
    (h4362 : Equation4362 G) (h4369 : Equation4369 G) (_ : Equation4512 G) : Equation4358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h4362 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := mod_symm (h4369 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13
  have eq78 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ X1)) := superpose eq14 eq25 -- superposition 25,14
  have eq309 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq78 eq16 -- superposition 16,78
  subsumption eq309 rfl

theorem Equation4364_4369_4512_implies_Equation4358 (G : Type*) [Magma G]
    (h4364 : Equation4364 G) (h4369 : Equation4369 G) (_ : Equation4512 G) : Equation4358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h4364 ..)
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := mod_symm (h4369 ..)
  have eq16 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq29 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ X1)) := superpose eq13 eq14 -- superposition 14,13
  have eq120 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq29 eq16 -- superposition 16,29
  subsumption eq120 rfl


end Conjectures

