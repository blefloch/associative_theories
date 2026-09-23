import equational_theories.Superposition
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
import equational_theories.Equations.All

/- Generated file collecting conjectures about single equations -/

namespace Conjectures


/- Equivalence of [2, 6, 7, 15, 17, 18, 20, 21, 22, 63, 64, 67, 69, 70, 71, 74, 76, 77, 79, 80, 81, 83, 84, 85, 87, 88, 89, 91, 92, 93, 95, 96, 97, 98, 465, 467, 468, 470, 471, 472, 474, 475, 478, 480, 482, 484, 485, 486, 488, 490, 493, 494, 496, 497, 498, 499, 501, 502, 505, 507, 509, 512, 514, 515, 517, 518, 519, 521, 523, 525, 526, 527, 529, 530, 531, 533, 534, 535, 536, 538, 539, 540, 542, 544, 547, 548, 550, 551, 552, 553, 555, 557, 559, 560, 561, 563, 564, 565, 567, 568, 569, 570, 573, 574, 576, 577, 578, 580, 581, 582, 584, 585, 586, 587, 589, 590, 591, 592, 594, 595, 596, 597, 599, 600, 601, 602, 604, 605, 606, 607, 609, 610, 611, 612, 613] -/
theorem Equation613_4512_implies_Equation2 (G : Type*) [Magma G]
    (h613 : Equation613 G) (_ : Equation4512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) = X0 := mod_symm (h613 ..)
  have eq13 : sK0 ≠ sK1 := mod_symm nh
  have eq20 (X5 X6 : G) : X5 = X6 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq13 -- superposition 13,20
  subsumption eq22 eq20

theorem Equation2_4512_implies_Equation6 (G : Type*) [Magma G]
    (h2 : Equation2 G) (_ : Equation4512 G) : Equation6 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : X0 = X1 := mod_symm (h2 ..)
  have eq13 : sK0 ≠ (sK1 ◇ sK1) := mod_symm nh
  subsumption eq13 eq11

theorem Equation6_4512_implies_Equation7 (G : Type*) [Magma G]
    (h6 : Equation6 G) (_ : Equation4512 G) : Equation7 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ X1) = X0 := mod_symm (h6 ..)
  have eq13 : sK0 ≠ (sK1 ◇ sK2) := mod_symm nh
  have eq14 (X1 X2 : G) : X1 = X2 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq16 eq14

theorem Equation7_4512_implies_Equation15 (G : Type*) [Magma G]
    (h7 : Equation7 G) (_ : Equation4512 G) : Equation15 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := mod_symm (h7 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation15_4512_implies_Equation17 (G : Type*) [Magma G]
    (h15 : Equation15 G) (h4512 : Equation4512 G) : Equation17 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := mod_symm (h15 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq11 eq12 -- forward demodulation 12,11
  have eq16 : sK0 ≠ sK1 := superpose eq11 eq13 -- superposition 13,11
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq11 eq14 -- superposition 14,11
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq16 -- superposition 16,19
  subsumption eq22 eq19

theorem Equation17_4512_implies_Equation18 (G : Type*) [Magma G]
    (h17 : Equation17 G) (_ : Equation4512 G) : Equation18 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := mod_symm (h17 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq15 (X1 X2 : G) : X1 = X2 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 : G) : sK0 ≠ (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq17 eq15

theorem Equation18_4512_implies_Equation20 (G : Type*) [Magma G]
    (h18 : Equation18 G) (_ : Equation4512 G) : Equation20 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X0 := mod_symm (h18 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq16 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq18 eq16

theorem Equation20_4512_implies_Equation21 (G : Type*) [Magma G]
    (h20 : Equation20 G) (_ : Equation4512 G) : Equation21 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := mod_symm (h20 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq16 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq18 eq16

theorem Equation21_4512_implies_Equation22 (G : Type*) [Magma G]
    (h21 : Equation21 G) (_ : Equation4512 G) : Equation22 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X0 := mod_symm (h21 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq16 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq18 eq16

theorem Equation22_4512_implies_Equation63 (G : Type*) [Magma G]
    (h22 : Equation22 G) (_ : Equation4512 G) : Equation63 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = X0 := mod_symm (h22 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation63_4512_implies_Equation64 (G : Type*) [Magma G]
    (h63 : Equation63 G) (h4512 : Equation4512 G) : Equation64 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h63 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq15 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq15 eq11 -- superposition 11,15
  have eq17 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq18 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq17 -- forward demodulation 17,11
  have eq22 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) = X2 := superpose eq11 eq12 -- superposition 12,11
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq18 -- superposition 18,12
  have eq33 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq18 eq12 -- superposition 12,18
  have eq37 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq33 eq11 -- backward demodulation 11,33
  have eq38 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X2 := superpose eq33 eq22 -- backward demodulation 22,33
  have eq40 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq33 eq13 -- backward demodulation 13,33
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq37 eq32 -- backward demodulation 32,37
  have eq42 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq18 eq41 -- forward demodulation 41,18
  have eq50 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq42 eq38 -- forward demodulation 38,42
  subsumption eq40 eq50

theorem Equation64_4512_implies_Equation67 (G : Type*) [Magma G]
    (h64 : Equation64 G) (_ : Equation4512 G) : Equation67 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X2))) = X0 := mod_symm (h64 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq14 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq18 : sK0 ≠ (sK1 ◇ sK1) := superpose eq14 eq13 -- backward demodulation 13,14
  have eq20 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq17 eq14 -- backward demodulation 14,17
  subsumption eq18 eq20

theorem Equation67_4512_implies_Equation69 (G : Type*) [Magma G]
    (h67 : Equation67 G) (_ : Equation4512 G) : Equation69 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h67 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq14 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X1)) = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq18 : sK0 ≠ (sK1 ◇ sK2) := superpose eq14 eq13 -- backward demodulation 13,14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq17 eq17 -- superposition 17,17
  have eq21 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq17 eq18 -- superposition 18,17
  subsumption eq21 eq19

theorem Equation69_4512_implies_Equation70 (G : Type*) [Magma G]
    (h69 : Equation69 G) (h4512 : Equation4512 G) : Equation70 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h69 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq15 eq12 -- backward demodulation 12,15
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq16 eq11 -- backward demodulation 11,16
  have eq19 : sK0 ≠ (sK1 ◇ sK2) := superpose eq16 eq13 -- backward demodulation 13,16
  subsumption eq19 eq18

theorem Equation70_4512_implies_Equation71 (G : Type*) [Magma G]
    (h70 : Equation70 G) (_ : Equation4512 G) : Equation71 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X2))) = X0 := mod_symm (h70 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq14 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq18 : sK0 ≠ (sK1 ◇ sK2) := superpose eq14 eq13 -- backward demodulation 13,14
  subsumption eq18 eq16

theorem Equation71_4512_implies_Equation74 (G : Type*) [Magma G]
    (h71 : Equation71 G) (_ : Equation4512 G) : Equation74 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h71 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq14 (X1 X4 X5 : G) : (X4 ◇ (X5 ◇ X1)) = X5 := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq19 : sK0 ≠ (sK1 ◇ sK0) := superpose eq14 eq13 -- backward demodulation 13,14
  subsumption eq19 eq18

theorem Equation74_4512_implies_Equation76 (G : Type*) [Magma G]
    (h74 : Equation74 G) (_ : Equation4512 G) : Equation76 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h74 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq15 eq11 -- backward demodulation 11,15
  have eq20 : sK0 ≠ (sK1 ◇ sK1) := superpose eq15 eq13 -- backward demodulation 13,15
  subsumption eq20 eq18

theorem Equation76_4512_implies_Equation77 (G : Type*) [Magma G]
    (h76 : Equation76 G) (_ : Equation4512 G) : Equation77 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h76 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq16 (X1 X2 : G) : X1 = X2 := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 : G) : sK0 ≠ (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq18 eq16

theorem Equation77_4512_implies_Equation79 (G : Type*) [Magma G]
    (h77 : Equation77 G) (_ : Equation4512 G) : Equation79 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h77 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq18 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq18

theorem Equation79_4512_implies_Equation80 (G : Type*) [Magma G]
    (h79 : Equation79 G) (_ : Equation4512 G) : Equation80 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h79 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq19 eq17

theorem Equation80_4512_implies_Equation81 (G : Type*) [Magma G]
    (h80 : Equation80 G) (_ : Equation4512 G) : Equation81 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h80 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq19 eq17

theorem Equation81_4512_implies_Equation83 (G : Type*) [Magma G]
    (h81 : Equation81 G) (_ : Equation4512 G) : Equation83 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h81 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq18 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq18

theorem Equation83_4512_implies_Equation84 (G : Type*) [Magma G]
    (h83 : Equation83 G) (_ : Equation4512 G) : Equation84 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X0 := mod_symm (h83 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = X1 := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X2 X3 : G) : X2 = X3 := superpose eq15 eq15 -- superposition 15,15
  have eq26 (X0 X1 : G) : sK0 ≠ ((X0 ◇ X1) ◇ X0) := superpose eq15 eq13 -- superposition 13,15
  subsumption eq26 eq19

theorem Equation84_4512_implies_Equation85 (G : Type*) [Magma G]
    (h84 : Equation84 G) (h4512 : Equation4512 G) : Equation85 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = X0 := mod_symm (h84 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK3))) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := superpose eq12 eq14 -- forward demodulation 14,12
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))) = X0 := superpose eq12 eq16 -- forward demodulation 16,12
  have eq18 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq11 eq17 -- forward demodulation 17,11
  have eq19 (X2 X3 : G) : X2 = X3 := superpose eq11 eq18 -- superposition 18,11
  have eq25 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ X0)) := superpose eq18 eq13 -- superposition 13,18
  subsumption eq25 eq19

theorem Equation85_4512_implies_Equation87 (G : Type*) [Magma G]
    (h85 : Equation85 G) (_ : Equation4512 G) : Equation87 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X3))) = X0 := mod_symm (h85 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq15 (X1 X2 X4 : G) : (X4 ◇ X2) = X1 := superpose eq11 eq11 -- superposition 11,11
  have eq23 (X2 X4 : G) : X2 = X4 := superpose eq11 eq15 -- superposition 15,11
  have eq32 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ X0)) := superpose eq15 eq13 -- superposition 13,15
  subsumption eq32 eq23

theorem Equation87_4512_implies_Equation88 (G : Type*) [Magma G]
    (h87 : Equation87 G) (_ : Equation4512 G) : Equation88 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X1))) = X0 := mod_symm (h87 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq19 eq17

theorem Equation88_4512_implies_Equation89 (G : Type*) [Magma G]
    (h88 : Equation88 G) (_ : Equation4512 G) : Equation89 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h88 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) := mod_symm nh
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq19 eq17

theorem Equation89_4512_implies_Equation91 (G : Type*) [Magma G]
    (h89 : Equation89 G) (_ : Equation4512 G) : Equation91 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h89 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq18 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq18

theorem Equation91_4512_implies_Equation92 (G : Type*) [Magma G]
    (h91 : Equation91 G) (_ : Equation4512 G) : Equation92 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h91 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq18 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq18

theorem Equation92_4512_implies_Equation93 (G : Type*) [Magma G]
    (h92 : Equation92 G) (_ : Equation4512 G) : Equation93 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X2))) = X0 := mod_symm (h92 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq19 eq17

theorem Equation93_4512_implies_Equation95 (G : Type*) [Magma G]
    (h93 : Equation93 G) (_ : Equation4512 G) : Equation95 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X3))) = X0 := mod_symm (h93 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1))) := mod_symm nh
  have eq18 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq18

theorem Equation95_4512_implies_Equation96 (G : Type*) [Magma G]
    (h95 : Equation95 G) (_ : Equation4512 G) : Equation96 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X1))) = X0 := mod_symm (h95 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2))) := mod_symm nh
  have eq18 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq18

theorem Equation96_4512_implies_Equation97 (G : Type*) [Magma G]
    (h96 : Equation96 G) (_ : Equation4512 G) : Equation97 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X2))) = X0 := mod_symm (h96 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3))) := mod_symm nh
  have eq18 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq18

theorem Equation97_4512_implies_Equation98 (G : Type*) [Magma G]
    (h97 : Equation97 G) (_ : Equation4512 G) : Equation98 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X3))) = X0 := mod_symm (h97 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK4))) := mod_symm nh
  have eq18 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq18

theorem Equation98_4512_implies_Equation465 (G : Type*) [Magma G]
    (h98 : Equation98 G) (_ : Equation4512 G) : Equation465 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X4))) = X0 := mod_symm (h98 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation465_4512_implies_Equation467 (G : Type*) [Magma G]
    (h465 : Equation465 G) (_ : Equation4512 G) : Equation467 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h465 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq14 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq19 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq14 -- backward demodulation 14,17
  have eq20 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := superpose eq17 eq13 -- backward demodulation 13,17
  have eq22 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq17 eq19 -- forward demodulation 19,17
  subsumption eq20 eq22

theorem Equation467_4512_implies_Equation468 (G : Type*) [Magma G]
    (h467 : Equation467 G) (h4512 : Equation4512 G) : Equation468 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h467 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2)))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2))))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq33 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq11 eq23 -- superposition 23,11
  have eq100 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq17 -- superposition 17,11
  have eq151 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq12 eq100 -- superposition 100,12
  have eq153 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq100 eq11 -- superposition 11,100
  have eq160 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq12 eq153 -- forward demodulation 153,12
  have eq161 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq151 eq160 -- forward demodulation 160,151
  have eq162 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq161 eq11 -- backward demodulation 11,161
  have eq165 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq161 eq33 -- backward demodulation 33,161
  have eq185 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq162 eq165 -- forward demodulation 165,162
  have eq186 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq161 eq185 -- forward demodulation 185,161
  have eq187 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))) = X2 := superpose eq186 eq17 -- backward demodulation 17,186
  have eq214 : sK0 ≠ (sK1 ◇ sK0) := superpose eq186 eq13 -- backward demodulation 13,186
  have eq215 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X2 := superpose eq186 eq187 -- forward demodulation 187,186
  have eq216 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq186 eq215 -- forward demodulation 215,186
  subsumption eq214 eq216

theorem Equation468_4512_implies_Equation470 (G : Type*) [Magma G]
    (h468 : Equation468 G) (h4512 : Equation4512 G) : Equation470 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h468 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq14 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X3 ◇ X1))) = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq16 eq11 -- superposition 11,16
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq16 eq18 -- forward demodulation 18,16
  have eq20 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X1)) = X3 := superpose eq19 eq14 -- backward demodulation 14,19
  have eq22 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := superpose eq19 eq13 -- backward demodulation 13,19
  have eq23 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq20 eq19 -- backward demodulation 19,20
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq20 eq12 -- backward demodulation 12,20
  have eq27 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq23 eq24 -- forward demodulation 24,23
  subsumption eq22 eq27

theorem Equation470_4512_implies_Equation471 (G : Type*) [Magma G]
    (h470 : Equation470 G) (h4512 : Equation4512 G) : Equation471 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h470 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq16 eq16 -- superposition 16,16
  have eq19 (X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X1))) = X2 := superpose eq16 eq11 -- superposition 11,16
  have eq21 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) := superpose eq18 eq13 -- backward demodulation 13,18
  have eq26 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq18 eq11 -- superposition 11,18
  have eq27 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq18 eq26 -- forward demodulation 26,18
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq18 eq12 -- superposition 12,18
  have eq45 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq29 eq19 -- backward demodulation 19,29
  have eq50 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq29 eq21 -- backward demodulation 21,29
  have eq51 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq45 eq27 -- backward demodulation 27,45
  have eq54 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq51 eq15 -- backward demodulation 15,51
  have eq59 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq51 eq54 -- forward demodulation 54,51
  have eq64 : sK0 ≠ (sK1 ◇ sK0) := superpose eq51 eq50 -- forward demodulation 50,51
  subsumption eq64 eq59

theorem Equation471_4512_implies_Equation472 (G : Type*) [Magma G]
    (h471 : Equation471 G) (_ : Equation4512 G) : Equation472 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h471 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X2))) = X0 := superpose eq15 eq11 -- backward demodulation 11,15
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X0 := superpose eq15 eq16 -- forward demodulation 16,15
  have eq20 (X2 X3 : G) : X2 = X3 := superpose eq17 eq17 -- superposition 17,17
  have eq22 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq17 eq13 -- superposition 13,17
  subsumption eq22 eq20

theorem Equation472_4512_implies_Equation474 (G : Type*) [Magma G]
    (h472 : Equation472 G) (_ : Equation4512 G) : Equation474 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h472 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq15 (X0 X1 X4 : G) : (X4 ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq15 eq11 -- backward demodulation 11,15
  have eq20 : sK0 ≠ (sK1 ◇ sK1) := superpose eq15 eq13 -- backward demodulation 13,15
  have eq21 (X0 X1 X4 : G) : (X4 ◇ X1) = X0 := superpose eq17 eq15 -- backward demodulation 15,17
  subsumption eq20 eq21

theorem Equation474_4512_implies_Equation475 (G : Type*) [Magma G]
    (h474 : Equation474 G) (h4512 : Equation4512 G) : Equation475 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h474 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq21 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))))) = X2 := superpose eq11 eq12 -- superposition 12,11
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq12 eq11 -- superposition 11,12
  have eq23 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))))) := superpose eq12 eq11 -- superposition 11,12
  have eq31 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))))) = X2 := superpose eq12 eq21 -- forward demodulation 21,12
  have eq32 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq33 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq32 eq31 -- backward demodulation 31,32
  have eq35 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq33 eq11 -- backward demodulation 11,33
  have eq36 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq33 eq24 -- forward demodulation 24,33
  have eq37 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := superpose eq33 eq36 -- forward demodulation 36,33
  have eq38 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq35 eq37 -- forward demodulation 37,35
  have eq39 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := superpose eq38 eq23 -- backward demodulation 23,38
  have eq46 : sK0 ≠ (sK1 ◇ sK0) := superpose eq38 eq13 -- backward demodulation 13,38
  have eq47 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X2 := superpose eq38 eq39 -- forward demodulation 39,38
  have eq48 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq38 eq47 -- forward demodulation 47,38
  subsumption eq46 eq48

theorem Equation475_4512_implies_Equation478 (G : Type*) [Magma G]
    (h475 : Equation475 G) (_ : Equation4512 G) : Equation478 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h475 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq14 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ X1))) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq18 (X1 X2 : G) : X1 = X2 := superpose eq17 eq17 -- superposition 17,17
  have eq20 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (X0 ◇ X0)))) := superpose eq17 eq13 -- superposition 13,17
  subsumption eq20 eq18

theorem Equation478_4512_implies_Equation480 (G : Type*) [Magma G]
    (h478 : Equation478 G) (h4512 : Equation4512 G) : Equation480 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h478 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq14 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq17 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq15 eq13 -- backward demodulation 13,15
  have eq19 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq16 eq11 -- superposition 11,16
  have eq20 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq19 -- forward demodulation 19,14
  have eq24 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq16 eq12 -- superposition 12,16
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq20 eq24 -- forward demodulation 24,20
  have eq33 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq32 eq14 -- backward demodulation 14,32
  have eq38 : sK0 ≠ (sK1 ◇ sK0) := superpose eq32 eq17 -- backward demodulation 17,32
  subsumption eq38 eq33

theorem Equation480_4512_implies_Equation482 (G : Type*) [Magma G]
    (h480 : Equation480 G) (h4512 : Equation4512 G) : Equation482 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h480 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq15 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq15 eq15 -- superposition 15,15
  have eq26 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq15 eq12 -- superposition 12,15
  have eq27 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1)))))) = X2 := superpose eq11 eq12 -- superposition 12,11
  have eq29 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq12 eq15 -- superposition 15,12
  have eq40 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X1))))))) = X2 := superpose eq12 eq27 -- forward demodulation 27,12
  have eq42 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ X2) := superpose eq12 eq20 -- superposition 20,12
  have eq44 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq20 -- superposition 20,12
  have eq58 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq42 eq26 -- backward demodulation 26,42
  have eq63 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK3 ◇ sK3))) := superpose eq42 eq13 -- backward demodulation 13,42
  have eq68 : sK0 ≠ (sK1 ◇ (sK3 ◇ sK3)) := superpose eq42 eq63 -- forward demodulation 63,42
  have eq69 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq42 eq44 -- forward demodulation 44,42
  have eq70 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq58 eq69 -- forward demodulation 69,58
  have eq72 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq70 eq29 -- backward demodulation 29,70
  have eq77 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1))))) = X2 := superpose eq70 eq40 -- backward demodulation 40,70
  have eq80 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq72 eq20 -- backward demodulation 20,72
  have eq86 : sK0 ≠ (sK1 ◇ sK3) := superpose eq72 eq68 -- backward demodulation 68,72
  have eq103 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = X2 := superpose eq80 eq77 -- forward demodulation 77,80
  have eq104 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X2 := superpose eq80 eq103 -- forward demodulation 103,80
  have eq105 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = X2 := superpose eq80 eq104 -- forward demodulation 104,80
  have eq106 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq72 eq105 -- forward demodulation 105,72
  have eq107 (X2 X3 : G) : X2 = X3 := superpose eq106 eq106 -- superposition 106,106
  have eq109 (X0 : G) : sK0 ≠ X0 := superpose eq106 eq86 -- superposition 86,106
  subsumption eq109 eq107

theorem Equation482_4512_implies_Equation484 (G : Type*) [Magma G]
    (h482 : Equation482 G) (_ : Equation4512 G) : Equation484 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h482 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq14 (X1 X4 X5 : G) : (X4 ◇ (X5 ◇ (X4 ◇ X1))) = X5 := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 X4 : G) : (X0 ◇ (X4 ◇ X1)) = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq17 : sK0 ≠ (sK1 ◇ sK2) := superpose eq14 eq13 -- backward demodulation 13,14
  have eq18 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq15 eq11 -- backward demodulation 11,15
  have eq21 (X1 X2 : G) : X1 = X2 := superpose eq18 eq18 -- superposition 18,18
  have eq23 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq18 eq17 -- superposition 17,18
  subsumption eq23 eq21

theorem Equation484_4512_implies_Equation485 (G : Type*) [Magma G]
    (h484 : Equation484 G) (_ : Equation4512 G) : Equation485 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h484 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq16 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq11 eq16 -- superposition 16,11
  have eq20 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq16 eq11 -- superposition 11,16
  have eq23 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq17 eq13 -- backward demodulation 13,17
  have eq27 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ X1) := superpose eq20 eq17 -- backward demodulation 17,20
  have eq31 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq27 eq23 -- backward demodulation 23,27
  subsumption eq31 eq20

theorem Equation485_4512_implies_Equation486 (G : Type*) [Magma G]
    (h485 : Equation485 G) (h4512 : Equation4512 G) : Equation486 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h485 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK3)))) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X1))) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X1)))) = X0 := superpose eq12 eq14 -- forward demodulation 14,12
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X1))))) = X0 := superpose eq12 eq16 -- forward demodulation 16,12
  have eq18 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))))) = X0 := superpose eq12 eq17 -- forward demodulation 17,12
  have eq19 (X0 X2 X3 : G) : (X3 ◇ (X0 ◇ X2)) = X0 := superpose eq11 eq18 -- forward demodulation 18,11
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq19 eq11 -- backward demodulation 11,19
  have eq22 : sK0 ≠ (sK1 ◇ sK2) := superpose eq19 eq13 -- backward demodulation 13,19
  subsumption eq22 eq20

theorem Equation486_4512_implies_Equation488 (G : Type*) [Magma G]
    (h486 : Equation486 G) (_ : Equation4512 G) : Equation488 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h486 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq14 (X0 X1 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X1))) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq18 : sK0 ≠ (sK1 ◇ sK2) := superpose eq14 eq13 -- backward demodulation 13,14
  subsumption eq18 eq17

theorem Equation488_4512_implies_Equation490 (G : Type*) [Magma G]
    (h488 : Equation488 G) (_ : Equation4512 G) : Equation490 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h488 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK3)))) := mod_symm nh
  have eq15 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq15 eq15 -- superposition 15,15
  have eq17 (X0 X1 : G) : X0 = X1 := superpose eq11 eq15 -- superposition 15,11
  have eq22 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq16 eq13 -- backward demodulation 13,16
  have eq29 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq17 eq22 -- superposition 22,17
  subsumption eq29 eq17

theorem Equation490_4512_implies_Equation493 (G : Type*) [Magma G]
    (h490 : Equation490 G) (_ : Equation4512 G) : Equation493 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h490 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq14 (X0 X1 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ X1))) = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq18 : sK0 ≠ (sK1 ◇ sK2) := superpose eq14 eq13 -- backward demodulation 13,14
  subsumption eq18 eq17

theorem Equation493_4512_implies_Equation494 (G : Type*) [Magma G]
    (h493 : Equation493 G) (h4512 : Equation4512 G) : Equation494 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h493 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) = X2 := superpose eq11 eq12 -- superposition 12,11
  have eq32 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq11 eq21 -- forward demodulation 21,11
  have eq33 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X2))) = X0 := superpose eq32 eq11 -- backward demodulation 11,32
  have eq37 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := superpose eq32 eq13 -- backward demodulation 13,32
  have eq38 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X0 := superpose eq32 eq33 -- forward demodulation 33,32
  have eq39 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq32 eq38 -- forward demodulation 38,32
  subsumption eq37 eq39

theorem Equation494_4512_implies_Equation496 (G : Type*) [Magma G]
    (h494 : Equation494 G) (_ : Equation4512 G) : Equation496 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h494 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK1)))) := mod_symm nh
  have eq14 (X0 X1 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X1))) = X5 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq18 : sK0 ≠ (sK1 ◇ sK2) := superpose eq14 eq13 -- backward demodulation 13,14
  subsumption eq18 eq17

theorem Equation496_4512_implies_Equation497 (G : Type*) [Magma G]
    (h496 : Equation496 G) (h4512 : Equation4512 G) : Equation497 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h496 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := mod_symm nh
  have eq16 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X1) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq16 eq12 -- backward demodulation 12,16
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq17 eq11 -- backward demodulation 11,17
  have eq21 : sK0 ≠ (sK1 ◇ sK2) := superpose eq17 eq13 -- backward demodulation 13,17
  subsumption eq21 eq19

theorem Equation497_4512_implies_Equation498 (G : Type*) [Magma G]
    (h497 : Equation497 G) (_ : Equation4512 G) : Equation498 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h497 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := mod_symm nh
  have eq15 (X2 X3 X4 : G) : (X3 ◇ (X4 ◇ X2)) = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq15 eq11 -- backward demodulation 11,15
  have eq20 : sK0 ≠ (sK1 ◇ sK2) := superpose eq15 eq13 -- backward demodulation 13,15
  subsumption eq20 eq18

theorem Equation498_4512_implies_Equation499 (G : Type*) [Magma G]
    (h498 : Equation498 G) (_ : Equation4512 G) : Equation499 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h498 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := mod_symm nh
  have eq14 (X0 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X5 ◇ X0))) = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq18 : sK0 ≠ (sK1 ◇ sK2) := superpose eq14 eq13 -- backward demodulation 13,14
  subsumption eq18 eq17

theorem Equation499_4512_implies_Equation501 (G : Type*) [Magma G]
    (h499 : Equation499 G) (_ : Equation4512 G) : Equation501 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h499 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq14 (X1 X5 X6 X7 : G) : (X5 ◇ (X6 ◇ (X7 ◇ X1))) = X6 := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq19 : sK0 ≠ (sK1 ◇ sK0) := superpose eq14 eq13 -- backward demodulation 13,14
  subsumption eq19 eq18

theorem Equation501_4512_implies_Equation502 (G : Type*) [Magma G]
    (h501 : Equation501 G) (h4512 : Equation4512 G) : Equation502 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h501 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq14 (X0 X1 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1))) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)))) = X0 := superpose eq12 eq14 -- forward demodulation 14,12
  have eq17 (X0 X1 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))))) = X0 := superpose eq12 eq16 -- forward demodulation 16,12
  have eq18 (X0 X1 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))))) = X0 := superpose eq12 eq17 -- forward demodulation 17,12
  have eq19 (X0 X1 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq18 -- forward demodulation 18,11
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq30 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq12 eq29 -- forward demodulation 29,12
  have eq31 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq12 eq30 -- forward demodulation 30,12
  have eq41 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq11 eq19 -- superposition 19,11
  have eq45 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose eq12 eq19 -- superposition 19,12
  have eq47 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq19 eq12 -- superposition 12,19
  have eq48 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0))) := superpose eq19 eq11 -- superposition 11,19
  have eq64 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq12 eq41 -- forward demodulation 41,12
  have eq65 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) := superpose eq12 eq64 -- forward demodulation 64,12
  have eq66 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) := superpose eq12 eq65 -- forward demodulation 65,12
  have eq67 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) := superpose eq12 eq66 -- forward demodulation 66,12
  have eq71 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq12 eq45 -- forward demodulation 45,12
  have eq72 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq12 eq71 -- forward demodulation 71,12
  have eq75 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq12 eq47 -- forward demodulation 47,12
  have eq76 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)))) := superpose eq12 eq48 -- forward demodulation 48,12
  have eq77 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))))) := superpose eq12 eq76 -- forward demodulation 76,12
  have eq78 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))))) := superpose eq12 eq77 -- forward demodulation 77,12
  have eq79 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))))) := superpose eq12 eq78 -- forward demodulation 78,12
  have eq80 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq31 eq79 -- forward demodulation 79,31
  have eq85 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq72 -- superposition 72,11
  have eq101 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose eq85 eq72 -- backward demodulation 72,85
  have eq102 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq85 eq80 -- backward demodulation 80,85
  have eq107 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq85 eq101 -- forward demodulation 101,85
  have eq110 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq107 eq75 -- backward demodulation 75,107
  have eq111 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq107 eq67 -- backward demodulation 67,107
  have eq112 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq107 eq11 -- backward demodulation 11,107
  have eq113 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq107 eq102 -- forward demodulation 102,107
  have eq114 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq113 eq111 -- backward demodulation 111,113
  have eq117 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose eq110 eq114 -- forward demodulation 114,110
  have eq125 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := superpose eq117 eq13 -- backward demodulation 13,117
  have eq146 (X1 X2 : G) : X1 = X2 := superpose eq112 eq112 -- superposition 112,112
  have eq158 (X0 : G) : sK0 ≠ (X0 ◇ (X0 ◇ (sK0 ◇ sK2))) := superpose eq146 eq125 -- superposition 125,146
  subsumption eq158 eq146

theorem Equation502_4512_implies_Equation505 (G : Type*) [Magma G]
    (h502 : Equation502 G) (_ : Equation4512 G) : Equation505 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h502 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq15 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ X1)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq39 (X1 X3 : G) : X1 = X3 := superpose eq11 eq15 -- superposition 15,11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq13 -- superposition 13,15
  subsumption eq49 eq39

theorem Equation505_4512_implies_Equation507 (G : Type*) [Magma G]
    (h505 : Equation505 G) (_ : Equation4512 G) : Equation507 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h505 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq14 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ X1))) = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq16 eq11 -- superposition 11,16
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq14 eq18 -- forward demodulation 18,14
  have eq20 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq19 eq11 -- backward demodulation 11,19
  have eq24 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq19 eq13 -- backward demodulation 13,19
  have eq26 : sK0 ≠ (sK1 ◇ sK1) := superpose eq19 eq24 -- forward demodulation 24,19
  subsumption eq26 eq20

theorem Equation507_4512_implies_Equation509 (G : Type*) [Magma G]
    (h507 : Equation507 G) (h4512 : Equation4512 G) : Equation509 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h507 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq23 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))))) = X2 := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) = X3 := superpose eq12 eq11 -- superposition 11,12
  have eq25 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq12 eq11 -- superposition 11,12
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))))) = X2 := superpose eq12 eq23 -- forward demodulation 23,12
  have eq34 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq24 eq25 -- forward demodulation 25,24
  have eq40 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X2 := superpose eq34 eq33 -- backward demodulation 33,34
  have eq42 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq34 eq13 -- backward demodulation 13,34
  have eq45 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq34 eq40 -- forward demodulation 40,34
  subsumption eq42 eq45

theorem Equation509_4512_implies_Equation512 (G : Type*) [Magma G]
    (h509 : Equation509 G) (_ : Equation4512 G) : Equation512 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h509 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq14 (X1 X4 X5 : G) : (X4 ◇ (X4 ◇ (X5 ◇ X1))) = X5 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq18 : sK0 ≠ (sK1 ◇ sK0) := superpose eq14 eq13 -- backward demodulation 13,14
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq16 eq11 -- backward demodulation 11,16
  have eq24 (X1 X2 : G) : X1 = X2 := superpose eq19 eq19 -- superposition 19,19
  have eq26 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq19 eq18 -- superposition 18,19
  subsumption eq26 eq24

theorem Equation512_4512_implies_Equation514 (G : Type*) [Magma G]
    (h512 : Equation512 G) (_ : Equation4512 G) : Equation514 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq15 eq11 -- backward demodulation 11,15
  have eq20 : sK0 ≠ (sK1 ◇ sK1) := superpose eq15 eq13 -- backward demodulation 13,15
  subsumption eq20 eq18

theorem Equation514_4512_implies_Equation515 (G : Type*) [Magma G]
    (h514 : Equation514 G) (_ : Equation4512 G) : Equation515 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h514 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq17 (X1 X2 : G) : X1 = X2 := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 : G) : sK0 ≠ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq19 eq17

theorem Equation515_4512_implies_Equation517 (G : Type*) [Magma G]
    (h515 : Equation515 G) (_ : Equation4512 G) : Equation517 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h515 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq20 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation517_4512_implies_Equation518 (G : Type*) [Magma G]
    (h517 : Equation517 G) (_ : Equation4512 G) : Equation518 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h517 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq18 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq18

theorem Equation518_4512_implies_Equation519 (G : Type*) [Magma G]
    (h518 : Equation518 G) (_ : Equation4512 G) : Equation519 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h518 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq18 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq18

theorem Equation519_4512_implies_Equation521 (G : Type*) [Magma G]
    (h519 : Equation519 G) (_ : Equation4512 G) : Equation521 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h519 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq20 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation521_4512_implies_Equation523 (G : Type*) [Magma G]
    (h521 : Equation521 G) (h4512 : Equation4512 G) : Equation523 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h521 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK3)))) := mod_symm nh
  have eq23 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))))) = X3 := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq12 eq11 -- superposition 11,12
  have eq25 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))))) = X3 := superpose eq12 eq23 -- forward demodulation 23,12
  have eq34 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq25 eq24 -- backward demodulation 24,25
  have eq39 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X1)))))) = X3 := superpose eq34 eq33 -- backward demodulation 33,34
  have eq42 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := superpose eq34 eq13 -- backward demodulation 13,34
  have eq59 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X1))))) = X3 := superpose eq34 eq39 -- forward demodulation 39,34
  have eq60 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X1)))) = X3 := superpose eq34 eq59 -- forward demodulation 59,34
  have eq61 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq34 eq60 -- forward demodulation 60,34
  have eq62 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = X3 := superpose eq34 eq61 -- forward demodulation 61,34
  have eq63 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq34 eq62 -- forward demodulation 62,34
  subsumption eq42 eq63

theorem Equation523_4512_implies_Equation525 (G : Type*) [Magma G]
    (h523 : Equation523 G) (_ : Equation4512 G) : Equation525 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h523 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq11 eq11 -- superposition 11,11
  have eq25 (X2 X4 : G) : X2 = X4 := superpose eq11 eq16 -- superposition 16,11
  have eq35 (X0 : G) : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ X0))) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq35 eq25

theorem Equation525_4512_implies_Equation526 (G : Type*) [Magma G]
    (h525 : Equation525 G) (_ : Equation4512 G) : Equation526 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h525 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq19 eq17

theorem Equation526_4512_implies_Equation527 (G : Type*) [Magma G]
    (h526 : Equation526 G) (_ : Equation4512 G) : Equation527 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h526 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))) := mod_symm nh
  have eq18 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq18

theorem Equation527_4512_implies_Equation529 (G : Type*) [Magma G]
    (h527 : Equation527 G) (_ : Equation4512 G) : Equation529 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h527 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq20 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation529_4512_implies_Equation530 (G : Type*) [Magma G]
    (h529 : Equation529 G) (_ : Equation4512 G) : Equation530 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h529 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq19 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq19

theorem Equation530_4512_implies_Equation531 (G : Type*) [Magma G]
    (h530 : Equation530 G) (_ : Equation4512 G) : Equation531 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h530 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq18 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq18

theorem Equation531_4512_implies_Equation533 (G : Type*) [Magma G]
    (h531 : Equation531 G) (_ : Equation4512 G) : Equation533 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h531 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1)))) := mod_symm nh
  have eq20 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation533_4512_implies_Equation534 (G : Type*) [Magma G]
    (h533 : Equation533 G) (_ : Equation4512 G) : Equation534 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h533 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := mod_symm nh
  have eq19 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq19

theorem Equation534_4512_implies_Equation535 (G : Type*) [Magma G]
    (h534 : Equation534 G) (_ : Equation4512 G) : Equation535 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h534 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := mod_symm nh
  have eq20 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation535_4512_implies_Equation536 (G : Type*) [Magma G]
    (h535 : Equation535 G) (_ : Equation4512 G) : Equation536 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h535 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := mod_symm nh
  have eq19 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq19

theorem Equation536_4512_implies_Equation538 (G : Type*) [Magma G]
    (h536 : Equation536 G) (_ : Equation4512 G) : Equation538 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h536 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq20 (X4 X5 : G) : X4 = X5 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 X3 : G) : sK0 ≠ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation538_4512_implies_Equation539 (G : Type*) [Magma G]
    (h538 : Equation538 G) (_ : Equation4512 G) : Equation539 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h538 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq16 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq11 eq16 -- superposition 16,11
  have eq22 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq17 eq11 -- backward demodulation 11,17
  have eq26 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := superpose eq17 eq13 -- backward demodulation 13,17
  have eq31 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq22 -- forward demodulation 22,17
  have eq32 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq17 eq31 -- forward demodulation 31,17
  have eq36 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq17 eq26 -- forward demodulation 26,17
  have eq37 : sK0 ≠ (sK1 ◇ sK2) := superpose eq17 eq36 -- forward demodulation 36,17
  have eq41 (X1 X2 : G) : X1 = X2 := superpose eq32 eq32 -- superposition 32,32
  have eq43 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq32 eq37 -- superposition 37,32
  subsumption eq43 eq41

theorem Equation539_4512_implies_Equation540 (G : Type*) [Magma G]
    (h539 : Equation539 G) (h4512 : Equation4512 G) : Equation540 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h539 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK3)))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose eq12 eq15 -- forward demodulation 15,12
  have eq21 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq12 eq20 -- forward demodulation 20,12
  have eq22 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq16 eq21 -- backward demodulation 21,16
  have eq26 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK3))) := superpose eq16 eq13 -- backward demodulation 13,16
  have eq27 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq16 eq22 -- forward demodulation 22,16
  have eq28 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq16 eq27 -- forward demodulation 27,16
  subsumption eq26 eq28

theorem Equation540_4512_implies_Equation542 (G : Type*) [Magma G]
    (h540 : Equation540 G) (_ : Equation4512 G) : Equation542 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h540 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq14 (X0 X2 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X2))) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq18 : sK0 ≠ (sK1 ◇ sK1) := superpose eq14 eq13 -- backward demodulation 13,14
  have eq19 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ X2)) = X0 := superpose eq17 eq14 -- backward demodulation 14,17
  have eq21 (X0 X2 X4 : G) : (X4 ◇ X2) = X0 := superpose eq17 eq19 -- forward demodulation 19,17
  subsumption eq18 eq21

theorem Equation542_4512_implies_Equation544 (G : Type*) [Magma G]
    (h542 : Equation542 G) (_ : Equation4512 G) : Equation544 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h542 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK3)))) := mod_symm nh
  have eq15 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X1 := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X1 X2 : G) : X1 = X2 := superpose eq15 eq15 -- superposition 15,15
  have eq27 (X0 : G) : sK0 ≠ ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq15 eq13 -- superposition 13,15
  subsumption eq27 eq18

theorem Equation544_4512_implies_Equation547 (G : Type*) [Magma G]
    (h544 : Equation544 G) (_ : Equation4512 G) : Equation547 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h544 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq14 (X0 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ X2))) = X5 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq18 : sK0 ≠ (sK1 ◇ sK2) := superpose eq14 eq13 -- backward demodulation 13,14
  have eq19 (X1 X2 : G) : X1 = X2 := superpose eq17 eq17 -- superposition 17,17
  have eq21 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq17 eq18 -- superposition 18,17
  subsumption eq21 eq19

theorem Equation547_4512_implies_Equation548 (G : Type*) [Magma G]
    (h547 : Equation547 G) (_ : Equation4512 G) : Equation548 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h547 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X0 := superpose eq15 eq11 -- backward demodulation 11,15
  have eq22 (X2 X3 : G) : X2 = X3 := superpose eq19 eq19 -- superposition 19,19
  have eq24 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq19 eq13 -- superposition 13,19
  subsumption eq24 eq22

theorem Equation548_4512_implies_Equation550 (G : Type*) [Magma G]
    (h548 : Equation548 G) (_ : Equation4512 G) : Equation550 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h548 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := mod_symm nh
  have eq14 (X0 X2 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X2))) = X5 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq18 : sK0 ≠ (sK1 ◇ sK3) := superpose eq14 eq13 -- backward demodulation 13,14
  subsumption eq18 eq17

theorem Equation550_4512_implies_Equation551 (G : Type*) [Magma G]
    (h550 : Equation550 G) (_ : Equation4512 G) : Equation551 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h550 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK3 ◇ sK2)))) := mod_symm nh
  have eq16 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X1 := superpose eq11 eq11 -- superposition 11,11
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) ≠ sK0 := superpose eq16 eq13 -- superposition 13,16
  subsumption eq31 eq16

theorem Equation551_4512_implies_Equation552 (G : Type*) [Magma G]
    (h551 : Equation551 G) (_ : Equation4512 G) : Equation552 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h551 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK3 ◇ sK3)))) := mod_symm nh
  have eq16 (X1 X2 X3 : G) : (X3 ◇ X2) = X1 := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X2 X4 : G) : X2 = X4 := superpose eq11 eq16 -- superposition 16,11
  have eq27 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ X0)) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq27 eq20

theorem Equation552_4512_implies_Equation553 (G : Type*) [Magma G]
    (h552 : Equation552 G) (_ : Equation4512 G) : Equation553 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h552 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK3 ◇ sK4)))) := mod_symm nh
  have eq14 (X1 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X5 ◇ X1))) = X5 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq18 : sK0 ≠ (sK1 ◇ sK3) := superpose eq14 eq13 -- backward demodulation 13,14
  subsumption eq18 eq17

theorem Equation553_4512_implies_Equation555 (G : Type*) [Magma G]
    (h553 : Equation553 G) (_ : Equation4512 G) : Equation555 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h553 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq14 (X2 X5 X6 X7 : G) : (X5 ◇ (X6 ◇ (X7 ◇ X2))) = X7 := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq19 : sK0 ≠ (sK1 ◇ sK0) := superpose eq14 eq13 -- backward demodulation 13,14
  subsumption eq19 eq18

theorem Equation555_4512_implies_Equation557 (G : Type*) [Magma G]
    (h555 : Equation555 G) (_ : Equation4512 G) : Equation557 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h555 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := mod_symm nh
  have eq15 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq15 eq11 -- superposition 11,15
  have eq28 (X1 X2 : G) : X1 = X2 := superpose eq15 eq22 -- superposition 22,15
  have eq36 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ X0))) := superpose eq22 eq13 -- superposition 13,22
  subsumption eq36 eq28

theorem Equation557_4512_implies_Equation559 (G : Type*) [Magma G]
    (h557 : Equation557 G) (_ : Equation4512 G) : Equation559 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h557 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq25 (X2 X4 : G) : X2 = X4 := superpose eq11 eq16 -- superposition 16,11
  have eq35 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ X0))) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq35 eq25

theorem Equation559_4512_implies_Equation560 (G : Type*) [Magma G]
    (h559 : Equation559 G) (_ : Equation4512 G) : Equation560 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h559 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq19 eq17

theorem Equation560_4512_implies_Equation561 (G : Type*) [Magma G]
    (h560 : Equation560 G) (_ : Equation4512 G) : Equation561 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h560 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK3)))) := mod_symm nh
  have eq19 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq19

theorem Equation561_4512_implies_Equation563 (G : Type*) [Magma G]
    (h561 : Equation561 G) (_ : Equation4512 G) : Equation563 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h561 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq20 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation563_4512_implies_Equation564 (G : Type*) [Magma G]
    (h563 : Equation563 G) (_ : Equation4512 G) : Equation564 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h563 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq18 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq18

theorem Equation564_4512_implies_Equation565 (G : Type*) [Magma G]
    (h564 : Equation564 G) (_ : Equation4512 G) : Equation565 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h564 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq18 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq18

theorem Equation565_4512_implies_Equation567 (G : Type*) [Magma G]
    (h565 : Equation565 G) (_ : Equation4512 G) : Equation567 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h565 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK1)))) := mod_symm nh
  have eq20 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation567_4512_implies_Equation568 (G : Type*) [Magma G]
    (h567 : Equation567 G) (_ : Equation4512 G) : Equation568 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h567 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK2)))) := mod_symm nh
  have eq19 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq19

theorem Equation568_4512_implies_Equation569 (G : Type*) [Magma G]
    (h568 : Equation568 G) (_ : Equation4512 G) : Equation569 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h568 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK3)))) := mod_symm nh
  have eq20 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation569_4512_implies_Equation570 (G : Type*) [Magma G]
    (h569 : Equation569 G) (_ : Equation4512 G) : Equation570 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h569 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK4)))) := mod_symm nh
  have eq19 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq19

theorem Equation570_4512_implies_Equation573 (G : Type*) [Magma G]
    (h570 : Equation570 G) (_ : Equation4512 G) : Equation573 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h570 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq20 (X4 X5 : G) : X4 = X5 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 X3 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation573_4512_implies_Equation574 (G : Type*) [Magma G]
    (h573 : Equation573 G) (h4512 : Equation4512 G) : Equation574 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h573 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK3)))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose eq12 eq15 -- forward demodulation 15,12
  have eq23 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq12 eq22 -- forward demodulation 22,12
  have eq27 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2))))) = X3 := superpose eq11 eq12 -- superposition 12,11
  have eq37 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq11 eq27 -- forward demodulation 27,11
  have eq38 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq37 eq23 -- backward demodulation 23,37
  have eq43 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := superpose eq37 eq13 -- backward demodulation 13,37
  have eq44 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq37 eq38 -- forward demodulation 38,37
  have eq45 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq37 eq44 -- forward demodulation 44,37
  subsumption eq43 eq45

theorem Equation574_4512_implies_Equation576 (G : Type*) [Magma G]
    (h574 : Equation574 G) (_ : Equation4512 G) : Equation576 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h574 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq16 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq25 (X2 X4 : G) : X2 = X4 := superpose eq11 eq16 -- superposition 16,11
  have eq35 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ X0))) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq35 eq25

theorem Equation576_4512_implies_Equation577 (G : Type*) [Magma G]
    (h576 : Equation576 G) (_ : Equation4512 G) : Equation577 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h576 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq19 eq17

theorem Equation577_4512_implies_Equation578 (G : Type*) [Magma G]
    (h577 : Equation577 G) (_ : Equation4512 G) : Equation578 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h577 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK3)))) := mod_symm nh
  have eq18 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq18

theorem Equation578_4512_implies_Equation580 (G : Type*) [Magma G]
    (h578 : Equation578 G) (_ : Equation4512 G) : Equation580 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h578 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq20 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation580_4512_implies_Equation581 (G : Type*) [Magma G]
    (h580 : Equation580 G) (_ : Equation4512 G) : Equation581 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h580 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq20 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation581_4512_implies_Equation582 (G : Type*) [Magma G]
    (h581 : Equation581 G) (_ : Equation4512 G) : Equation582 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h581 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq18 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq18

theorem Equation582_4512_implies_Equation584 (G : Type*) [Magma G]
    (h582 : Equation582 G) (_ : Equation4512 G) : Equation584 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h582 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK1)))) := mod_symm nh
  have eq20 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation584_4512_implies_Equation585 (G : Type*) [Magma G]
    (h584 : Equation584 G) (_ : Equation4512 G) : Equation585 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h584 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := mod_symm nh
  have eq20 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation585_4512_implies_Equation586 (G : Type*) [Magma G]
    (h585 : Equation585 G) (_ : Equation4512 G) : Equation586 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h585 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := mod_symm nh
  have eq19 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq19

theorem Equation586_4512_implies_Equation587 (G : Type*) [Magma G]
    (h586 : Equation586 G) (_ : Equation4512 G) : Equation587 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h586 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := mod_symm nh
  have eq19 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq19

theorem Equation587_4512_implies_Equation589 (G : Type*) [Magma G]
    (h587 : Equation587 G) (_ : Equation4512 G) : Equation589 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h587 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq20 (X4 X5 : G) : X4 = X5 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 X3 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation589_4512_implies_Equation590 (G : Type*) [Magma G]
    (h589 : Equation589 G) (_ : Equation4512 G) : Equation590 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h589 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq16 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = X2 := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X2 X3 : G) : X2 = X3 := superpose eq16 eq16 -- superposition 16,16
  have eq29 (X0 X1 : G) : sK0 ≠ ((X0 ◇ X1) ◇ X0) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq29 eq20

theorem Equation590_4512_implies_Equation591 (G : Type*) [Magma G]
    (h590 : Equation590 G) (_ : Equation4512 G) : Equation591 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h590 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := mod_symm nh
  have eq16 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X3 X4 : G) : X3 = X4 := superpose eq11 eq16 -- superposition 16,11
  have eq28 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ X0))) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq28 eq21

theorem Equation591_4512_implies_Equation592 (G : Type*) [Magma G]
    (h591 : Equation591 G) (_ : Equation4512 G) : Equation592 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h591 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK4)))) := mod_symm nh
  have eq16 (X1 X2 X3 : G) : (X3 ◇ X1) = X2 := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X3 X4 : G) : X3 = X4 := superpose eq11 eq16 -- superposition 16,11
  have eq28 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ X0))) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq28 eq21

theorem Equation592_4512_implies_Equation594 (G : Type*) [Magma G]
    (h592 : Equation592 G) (_ : Equation4512 G) : Equation594 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X4)))) = X0 := mod_symm (h592 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq16 (X2 X3 X5 : G) : (X5 ◇ X3) = X2 := superpose eq11 eq11 -- superposition 11,11
  have eq25 (X3 X5 : G) : X3 = X5 := superpose eq11 eq16 -- superposition 16,11
  have eq35 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ X0))) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq35 eq25

theorem Equation594_4512_implies_Equation595 (G : Type*) [Magma G]
    (h594 : Equation594 G) (_ : Equation4512 G) : Equation595 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h594 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq19 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq19

theorem Equation595_4512_implies_Equation596 (G : Type*) [Magma G]
    (h595 : Equation595 G) (_ : Equation4512 G) : Equation596 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h595 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK3)))) := mod_symm nh
  have eq19 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq19

theorem Equation596_4512_implies_Equation597 (G : Type*) [Magma G]
    (h596 : Equation596 G) (_ : Equation4512 G) : Equation597 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h596 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK4)))) := mod_symm nh
  have eq19 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq19

theorem Equation597_4512_implies_Equation599 (G : Type*) [Magma G]
    (h597 : Equation597 G) (_ : Equation4512 G) : Equation599 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X4)))) = X0 := mod_symm (h597 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq20 (X4 X5 : G) : X4 = X5 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 X3 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation599_4512_implies_Equation600 (G : Type*) [Magma G]
    (h599 : Equation599 G) (_ : Equation4512 G) : Equation600 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h599 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq20 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation600_4512_implies_Equation601 (G : Type*) [Magma G]
    (h600 : Equation600 G) (_ : Equation4512 G) : Equation601 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h600 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq19 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq19

theorem Equation601_4512_implies_Equation602 (G : Type*) [Magma G]
    (h601 : Equation601 G) (_ : Equation4512 G) : Equation602 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h601 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ sK4)))) := mod_symm nh
  have eq19 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq19

theorem Equation602_4512_implies_Equation604 (G : Type*) [Magma G]
    (h602 : Equation602 G) (_ : Equation4512 G) : Equation604 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X4)))) = X0 := mod_symm (h602 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK1)))) := mod_symm nh
  have eq20 (X4 X5 : G) : X4 = X5 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 X3 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation604_4512_implies_Equation605 (G : Type*) [Magma G]
    (h604 : Equation604 G) (_ : Equation4512 G) : Equation605 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h604 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK2)))) := mod_symm nh
  have eq20 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation605_4512_implies_Equation606 (G : Type*) [Magma G]
    (h605 : Equation605 G) (_ : Equation4512 G) : Equation606 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h605 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK3)))) := mod_symm nh
  have eq20 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation606_4512_implies_Equation607 (G : Type*) [Magma G]
    (h606 : Equation606 G) (_ : Equation4512 G) : Equation607 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h606 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK4)))) := mod_symm nh
  have eq19 (X3 X4 : G) : X3 = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 X1 X2 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq19

theorem Equation607_4512_implies_Equation609 (G : Type*) [Magma G]
    (h607 : Equation607 G) (_ : Equation4512 G) : Equation609 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h607 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))) := mod_symm nh
  have eq20 (X4 X5 : G) : X4 = X5 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 X3 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation609_4512_implies_Equation610 (G : Type*) [Magma G]
    (h609 : Equation609 G) (_ : Equation4512 G) : Equation610 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X1)))) = X0 := mod_symm (h609 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK2)))) := mod_symm nh
  have eq20 (X4 X5 : G) : X4 = X5 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 X3 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation610_4512_implies_Equation611 (G : Type*) [Magma G]
    (h610 : Equation610 G) (_ : Equation4512 G) : Equation611 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X2)))) = X0 := mod_symm (h610 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK3)))) := mod_symm nh
  have eq20 (X4 X5 : G) : X4 = X5 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 X3 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation611_4512_implies_Equation612 (G : Type*) [Magma G]
    (h611 : Equation611 G) (_ : Equation4512 G) : Equation612 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X3)))) = X0 := mod_symm (h611 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK4)))) := mod_symm nh
  have eq20 (X4 X5 : G) : X4 = X5 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 X3 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20

theorem Equation612_4512_implies_Equation613 (G : Type*) [Magma G]
    (h612 : Equation612 G) (_ : Equation4512 G) : Equation613 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, sK5, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4)))) = X0 := mod_symm (h612 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK5)))) := mod_symm nh
  have eq20 (X4 X5 : G) : X4 = X5 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 X3 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq20


/- Equivalence of [4, 9, 12, 48, 50, 51, 53, 54, 57, 59, 60, 61, 412, 415, 418, 420, 421, 423, 424, 425, 428, 430, 431, 433, 434, 435, 437, 438, 441, 443, 445, 447, 448, 449, 451, 453, 456, 457, 459, 460, 461, 462] -/
theorem Equation462_4512_implies_Equation4 (G : Type*) [Magma G]
    (h462 : Equation462 G) (_ : Equation4512 G) : Equation4 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h462 ..)
  have eq13 : sK0 ≠ (sK0 ◇ sK1) := mod_symm nh
  have eq14 (X0 X5 X6 X7 : G) : (X5 ◇ (X6 ◇ (X7 ◇ X0))) = X5 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq21 : sK0 ≠ sK0 := superpose eq17 eq13 -- superposition 13,17
  subsumption eq21 rfl

theorem Equation4_4512_implies_Equation9 (G : Type*) [Magma G]
    (h4 : Equation4 G) (_ : Equation4512 G) : Equation9 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = X0 := mod_symm (h4 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation9_4512_implies_Equation12 (G : Type*) [Magma G]
    (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation12 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := mod_symm (h9 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq16 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq25 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq11 eq24 -- forward demodulation 24,11
  have eq28 : sK0 ≠ (sK0 ◇ sK1) := superpose eq25 eq13 -- backward demodulation 13,25
  subsumption eq28 eq25

theorem Equation12_4512_implies_Equation48 (G : Type*) [Magma G]
    (h12 : Equation12 G) (_ : Equation4512 G) : Equation48 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := mod_symm (h12 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation48_4512_implies_Equation50 (G : Type*) [Magma G]
    (h48 : Equation48 G) (h4512 : Equation4512 G) : Equation50 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h48 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq17 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq15 eq13 -- backward demodulation 13,15
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq29 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq12 eq20 -- forward demodulation 20,12
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq29 -- forward demodulation 29,12
  have eq31 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq11 eq30 -- forward demodulation 30,11
  have eq34 : sK0 ≠ (sK0 ◇ sK0) := superpose eq31 eq17 -- backward demodulation 17,31
  subsumption eq34 eq15

theorem Equation50_4512_implies_Equation51 (G : Type*) [Magma G]
    (h50 : Equation50 G) (h4512 : Equation4512 G) : Equation51 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h50 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq14 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq21 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq29 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq12 eq14 -- superposition 14,12
  have eq34 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq29 -- forward demodulation 29,11
  have eq38 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq34 eq11 -- backward demodulation 11,34
  have eq39 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq38 eq22 -- backward demodulation 22,38
  have eq46 : sK0 ≠ (sK0 ◇ sK0) := superpose eq39 eq13 -- backward demodulation 13,39
  subsumption eq46 eq34

theorem Equation51_4512_implies_Equation53 (G : Type*) [Magma G]
    (h51 : Equation51 G) (h4512 : Equation4512 G) : Equation53 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h51 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = (X0 ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq27 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq28 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq11 eq27 -- forward demodulation 27,11
  have eq32 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq28 eq13 -- backward demodulation 13,28
  subsumption eq32 eq28

theorem Equation53_4512_implies_Equation54 (G : Type*) [Magma G]
    (h53 : Equation53 G) (h4512 : Equation4512 G) : Equation54 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h53 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := superpose eq12 eq14 -- forward demodulation 14,12
  have eq16 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq12 eq15 -- forward demodulation 15,12
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq11 eq16 -- forward demodulation 16,11
  have eq20 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq17 eq13 -- backward demodulation 13,17
  subsumption eq20 eq17

theorem Equation54_4512_implies_Equation57 (G : Type*) [Magma G]
    (h54 : Equation54 G) (_ : Equation4512 G) : Equation57 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h54 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq11 eq11 -- superposition 11,11
  have eq19 : sK0 ≠ (sK0 ◇ sK1) := superpose eq15 eq13 -- backward demodulation 13,15
  subsumption eq19 eq15

theorem Equation57_4512_implies_Equation59 (G : Type*) [Magma G]
    (h57 : Equation57 G) (_ : Equation4512 G) : Equation59 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h57 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq15 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq11 eq11 -- superposition 11,11
  have eq19 : sK0 ≠ (sK0 ◇ sK1) := superpose eq15 eq13 -- backward demodulation 13,15
  subsumption eq19 eq15

theorem Equation59_4512_implies_Equation60 (G : Type*) [Magma G]
    (h59 : Equation59 G) (h4512 : Equation4512 G) : Equation60 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h59 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) = X3 := superpose eq12 eq14 -- forward demodulation 14,12
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X3 := superpose eq12 eq16 -- forward demodulation 16,12
  have eq18 (X1 X3 : G) : (X3 ◇ X1) = X3 := superpose eq15 eq17 -- backward demodulation 17,15
  have eq21 : sK0 ≠ (sK0 ◇ sK1) := superpose eq15 eq13 -- backward demodulation 13,15
  subsumption eq21 eq18

theorem Equation60_4512_implies_Equation61 (G : Type*) [Magma G]
    (h60 : Equation60 G) (_ : Equation4512 G) : Equation61 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h60 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X1)))) = X2 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X2 X3 : G) : (X2 ◇ X3) = X2 := superpose eq11 eq14 -- forward demodulation 14,11
  have eq19 : sK0 ≠ (sK0 ◇ sK1) := superpose eq16 eq13 -- backward demodulation 13,16
  subsumption eq19 eq16

theorem Equation61_4512_implies_Equation412 (G : Type*) [Magma G]
    (h61 : Equation61 G) (_ : Equation4512 G) : Equation412 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h61 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation412_4512_implies_Equation415 (G : Type*) [Magma G]
    (h412 : Equation412 G) (h4512 : Equation4512 G) : Equation415 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h412 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq14 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq15 eq14 -- backward demodulation 14,15
  have eq22 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) = (X0 ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq32 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq33 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq12 eq32 -- forward demodulation 32,12
  have eq34 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq12 eq33 -- forward demodulation 33,12
  have eq35 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq11 eq34 -- forward demodulation 34,11
  have eq38 : sK0 ≠ (sK0 ◇ sK0) := superpose eq35 eq13 -- backward demodulation 13,35
  subsumption eq38 eq17

theorem Equation415_4512_implies_Equation418 (G : Type*) [Magma G]
    (h415 : Equation415 G) (h4512 : Equation4512 G) : Equation418 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h415 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq16 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq31 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq32 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := superpose eq12 eq31 -- forward demodulation 31,12
  have eq33 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq11 eq32 -- forward demodulation 32,11
  have eq37 : sK0 ≠ (sK0 ◇ sK0) := superpose eq33 eq13 -- backward demodulation 13,33
  subsumption eq37 eq16

theorem Equation418_4512_implies_Equation420 (G : Type*) [Magma G]
    (h418 : Equation418 G) (h4512 : Equation4512 G) : Equation420 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h418 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq17 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq15 eq13 -- backward demodulation 13,15
  have eq35 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = (X0 ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq50 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3))) := superpose eq12 eq35 -- forward demodulation 35,12
  have eq51 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3)))) := superpose eq12 eq50 -- forward demodulation 50,12
  have eq52 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) := superpose eq12 eq51 -- forward demodulation 51,12
  have eq53 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq11 eq52 -- forward demodulation 52,11
  have eq59 : sK0 ≠ (sK0 ◇ sK0) := superpose eq53 eq17 -- backward demodulation 17,53
  subsumption eq59 eq16

theorem Equation420_4512_implies_Equation421 (G : Type*) [Magma G]
    (h420 : Equation420 G) (h4512 : Equation4512 G) : Equation421 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h420 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2)) = (X0 ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X2))))) := superpose eq11 eq12 -- superposition 12,11
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq23 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2))))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq27 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))))) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq28 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) = X2 := superpose eq12 eq18 -- forward demodulation 18,12
  have eq31 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq24 -- superposition 24,11
  have eq45 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = X2 := superpose eq11 eq31 -- forward demodulation 31,11
  have eq47 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq45 eq27 -- backward demodulation 27,45
  have eq50 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) = X2 := superpose eq47 eq28 -- backward demodulation 28,47
  have eq51 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = X2 := superpose eq47 eq50 -- forward demodulation 50,47
  have eq52 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = X2 := superpose eq47 eq51 -- forward demodulation 51,47
  have eq53 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq47 eq52 -- forward demodulation 52,47
  have eq54 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq53 eq24 -- backward demodulation 24,53
  have eq60 : sK0 ≠ (sK0 ◇ sK0) := superpose eq54 eq13 -- backward demodulation 13,54
  subsumption eq60 eq54

theorem Equation421_4512_implies_Equation423 (G : Type*) [Magma G]
    (h421 : Equation421 G) (h4512 : Equation4512 G) : Equation423 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h421 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq15 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq16 eq12 -- superposition 12,16
  have eq23 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq15 eq19 -- forward demodulation 19,15
  have eq26 : sK0 ≠ (sK0 ◇ sK0) := superpose eq23 eq13 -- backward demodulation 13,23
  subsumption eq26 eq16

theorem Equation423_4512_implies_Equation424 (G : Type*) [Magma G]
    (h423 : Equation423 G) (h4512 : Equation4512 G) : Equation424 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h423 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3)) = (X0 ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq25 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3))) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq26 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3)))) := superpose eq12 eq25 -- forward demodulation 25,12
  have eq27 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3))))) := superpose eq12 eq26 -- forward demodulation 26,12
  have eq32 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq16 -- superposition 16,11
  have eq39 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X2 := superpose eq16 eq11 -- superposition 11,16
  have eq40 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := superpose eq32 eq13 -- backward demodulation 13,32
  have eq42 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq32 eq39 -- forward demodulation 39,32
  have eq43 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq42 eq27 -- backward demodulation 27,42
  have eq54 : sK0 ≠ (sK0 ◇ sK0) := superpose eq43 eq40 -- backward demodulation 40,43
  subsumption eq54 eq32

theorem Equation424_4512_implies_Equation425 (G : Type*) [Magma G]
    (h424 : Equation424 G) (_ : Equation4512 G) : Equation425 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h424 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq15 eq11 -- backward demodulation 11,15
  have eq21 : sK0 ≠ sK0 := superpose eq16 eq13 -- superposition 13,16
  subsumption eq21 rfl

theorem Equation425_4512_implies_Equation428 (G : Type*) [Magma G]
    (h425 : Equation425 G) (h4512 : Equation4512 G) : Equation428 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h425 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq14 (X0 X4 X5 : G) : (X4 ◇ (X4 ◇ (X5 ◇ X0))) = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X4 : G) : (X4 ◇ (X4 ◇ X0)) = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq15 eq13 -- backward demodulation 13,15
  have eq27 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4)) = (X0 ◇ X4) := superpose eq11 eq12 -- superposition 12,11
  have eq41 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X4) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4))) := superpose eq12 eq27 -- forward demodulation 27,12
  have eq42 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq14 eq41 -- forward demodulation 41,14
  have eq47 : sK0 ≠ (sK0 ◇ sK1) := superpose eq42 eq17 -- backward demodulation 17,42
  subsumption eq47 eq42

theorem Equation428_4512_implies_Equation430 (G : Type*) [Magma G]
    (h428 : Equation428 G) (h4512 : Equation4512 G) : Equation430 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h428 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq14 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq17 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq13 -- backward demodulation 13,14
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3)) = (X0 ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq26 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3))) := superpose eq12 eq19 -- forward demodulation 19,12
  have eq27 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3)))) := superpose eq12 eq26 -- forward demodulation 26,12
  have eq28 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3))))) := superpose eq12 eq27 -- forward demodulation 27,12
  have eq29 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq11 eq28 -- forward demodulation 28,11
  have eq39 : sK0 ≠ sK0 := superpose eq29 eq17 -- superposition 17,29
  subsumption eq39 rfl

theorem Equation430_4512_implies_Equation431 (G : Type*) [Magma G]
    (h430 : Equation430 G) (h4512 : Equation4512 G) : Equation431 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h430 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq14 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2)) = (X0 ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq20 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq14 eq12 -- superposition 12,14
  have eq27 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq28 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2)))) := superpose eq12 eq27 -- forward demodulation 27,12
  have eq29 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) := superpose eq12 eq28 -- forward demodulation 28,12
  have eq34 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq12 eq20 -- forward demodulation 20,12
  have eq59 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0)))) := superpose eq11 eq29 -- superposition 29,11
  have eq61 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq14 eq29 -- superposition 29,14
  have eq81 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X2 := superpose eq11 eq59 -- forward demodulation 59,11
  have eq83 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq11 eq61 -- forward demodulation 61,11
  have eq84 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = X2 := superpose eq83 eq81 -- backward demodulation 81,83
  have eq90 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq84 eq34 -- backward demodulation 34,84
  have eq97 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq84 eq13 -- backward demodulation 13,84
  have eq98 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq84 eq90 -- forward demodulation 90,84
  subsumption eq97 eq98

theorem Equation431_4512_implies_Equation433 (G : Type*) [Magma G]
    (h431 : Equation431 G) (_ : Equation4512 G) : Equation433 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h431 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq14 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ X0))) = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq15 eq14 -- backward demodulation 14,15
  have eq21 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq17 eq13 -- backward demodulation 13,17
  subsumption eq21 eq17

theorem Equation433_4512_implies_Equation434 (G : Type*) [Magma G]
    (h433 : Equation433 G) (h4512 : Equation4512 G) : Equation434 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h433 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq16 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0) := superpose eq11 eq16 -- superposition 16,11
  have eq25 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) = X2 := superpose eq16 eq11 -- superposition 11,16
  have eq26 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) = X2 := superpose eq12 eq25 -- forward demodulation 25,12
  have eq27 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = X2 := superpose eq16 eq26 -- forward demodulation 26,16
  have eq28 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq27 eq22 -- backward demodulation 22,27
  have eq33 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq27 eq13 -- backward demodulation 13,27
  subsumption eq33 eq28

theorem Equation434_4512_implies_Equation435 (G : Type*) [Magma G]
    (h434 : Equation434 G) (h4512 : Equation4512 G) : Equation435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h434 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq14 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ X2) := superpose eq14 eq12 -- superposition 12,14
  have eq21 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq12 eq14 -- superposition 14,12
  have eq23 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq27 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := superpose eq12 eq15 -- superposition 15,12
  have eq32 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq23 eq27 -- forward demodulation 27,23
  have eq33 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq32 eq21 -- backward demodulation 21,32
  have eq36 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq32 eq13 -- backward demodulation 13,32
  subsumption eq36 eq33

theorem Equation435_4512_implies_Equation437 (G : Type*) [Magma G]
    (h435 : Equation435 G) (_ : Equation4512 G) : Equation437 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h435 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq15 (X0 X4 : G) : (X0 ◇ (X4 ◇ X0)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq11 eq11 -- superposition 11,11
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq15 eq13 -- backward demodulation 13,15
  have eq22 : sK0 ≠ (sK0 ◇ sK1) := superpose eq16 eq17 -- backward demodulation 17,16
  subsumption eq22 eq16

theorem Equation437_4512_implies_Equation438 (G : Type*) [Magma G]
    (h437 : Equation437 G) (h4512 : Equation4512 G) : Equation438 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h437 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq21 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq28 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq29 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq12 eq28 -- forward demodulation 28,12
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq12 eq29 -- forward demodulation 29,12
  have eq37 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) := superpose eq11 eq30 -- superposition 30,11
  have eq38 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) = (X3 ◇ (X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X2))))) := superpose eq30 eq30 -- superposition 30,30
  have eq49 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := superpose eq11 eq37 -- forward demodulation 37,11
  have eq50 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) = (X3 ◇ X2) := superpose eq30 eq38 -- forward demodulation 38,30
  have eq78 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0))) = X3 := superpose eq49 eq49 -- superposition 49,49
  have eq108 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0)))) = X3 := superpose eq12 eq78 -- forward demodulation 78,12
  have eq109 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0))))) = X3 := superpose eq12 eq108 -- forward demodulation 108,12
  have eq110 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0)))))) = X3 := superpose eq12 eq109 -- forward demodulation 109,12
  have eq111 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0))))))) = X3 := superpose eq12 eq110 -- forward demodulation 110,12
  have eq112 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0)))))))) = X3 := superpose eq12 eq111 -- forward demodulation 111,12
  have eq113 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0))))))))) = X3 := superpose eq12 eq112 -- forward demodulation 112,12
  have eq114 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0))))) = X3 := superpose eq50 eq113 -- forward demodulation 113,50
  have eq115 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq114 eq30 -- backward demodulation 30,114
  have eq130 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := superpose eq115 eq13 -- backward demodulation 13,115
  subsumption eq130 eq115

theorem Equation438_4512_implies_Equation441 (G : Type*) [Magma G]
    (h438 : Equation438 G) (_ : Equation4512 G) : Equation441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h438 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq16 eq15 -- backward demodulation 15,16
  have eq21 : sK0 ≠ (sK0 ◇ sK1) := superpose eq17 eq13 -- backward demodulation 13,17
  subsumption eq21 eq17

theorem Equation441_4512_implies_Equation443 (G : Type*) [Magma G]
    (h441 : Equation441 G) (_ : Equation4512 G) : Equation443 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h441 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq14 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq15 eq14 -- backward demodulation 14,15
  have eq21 : sK0 ≠ (sK0 ◇ sK1) := superpose eq17 eq13 -- backward demodulation 13,17
  subsumption eq21 eq17

theorem Equation443_4512_implies_Equation445 (G : Type*) [Magma G]
    (h443 : Equation443 G) (h4512 : Equation4512 G) : Equation445 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h443 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = X2 := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := superpose eq12 eq15 -- forward demodulation 15,12
  have eq23 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) = X2 := superpose eq12 eq22 -- forward demodulation 22,12
  have eq24 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq11 eq23 -- forward demodulation 23,11
  have eq26 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq24 eq11 -- backward demodulation 11,24
  have eq28 : sK0 ≠ (sK0 ◇ sK1) := superpose eq24 eq13 -- backward demodulation 13,24
  subsumption eq28 eq26

theorem Equation445_4512_implies_Equation447 (G : Type*) [Magma G]
    (h445 : Equation445 G) (_ : Equation4512 G) : Equation447 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h445 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq16 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq21 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := superpose eq16 eq13 -- backward demodulation 13,16
  subsumption eq21 eq16

theorem Equation447_4512_implies_Equation448 (G : Type*) [Magma G]
    (h447 : Equation447 G) (h4512 : Equation4512 G) : Equation448 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h447 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq25 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq26 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))))) = X3 := superpose eq12 eq11 -- superposition 11,12
  have eq34 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq25 eq26 -- forward demodulation 26,25
  have eq42 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := superpose eq34 eq13 -- backward demodulation 13,34
  subsumption eq42 eq34

theorem Equation448_4512_implies_Equation449 (G : Type*) [Magma G]
    (h448 : Equation448 G) (_ : Equation4512 G) : Equation449 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h448 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK3)))) := mod_symm nh
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq11 eq11 -- superposition 11,11
  have eq22 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := superpose eq15 eq13 -- backward demodulation 13,15
  subsumption eq22 eq15

theorem Equation449_4512_implies_Equation451 (G : Type*) [Magma G]
    (h449 : Equation449 G) (_ : Equation4512 G) : Equation451 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h449 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq14 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ X0))) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 X4 : G) : (X1 ◇ (X4 ◇ X0)) = X1 := superpose eq11 eq11 -- superposition 11,11
  have eq17 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq13 -- backward demodulation 13,14
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq15 eq11 -- backward demodulation 11,15
  have eq23 : sK0 ≠ sK0 := superpose eq18 eq17 -- superposition 17,18
  subsumption eq23 rfl

theorem Equation451_4512_implies_Equation453 (G : Type*) [Magma G]
    (h451 : Equation451 G) (h4512 : Equation4512 G) : Equation453 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h451 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) = X2 := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) = X2 := superpose eq12 eq14 -- forward demodulation 14,12
  have eq17 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))))) = X2 := superpose eq12 eq16 -- forward demodulation 16,12
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))))) = X2 := superpose eq12 eq17 -- forward demodulation 17,12
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X3))))) = X2 := superpose eq11 eq18 -- forward demodulation 18,11
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq15 eq11 -- backward demodulation 11,15
  have eq21 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq20 eq19 -- backward demodulation 19,20
  have eq23 : sK0 ≠ (sK0 ◇ sK1) := superpose eq20 eq13 -- backward demodulation 13,20
  subsumption eq23 eq21

theorem Equation453_4512_implies_Equation456 (G : Type*) [Magma G]
    (h453 : Equation453 G) (_ : Equation4512 G) : Equation456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h453 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq14 (X0 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X0))) = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq17 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq13 -- backward demodulation 13,14
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq15 eq11 -- backward demodulation 11,15
  have eq23 : sK0 ≠ sK0 := superpose eq18 eq17 -- superposition 17,18
  subsumption eq23 rfl

theorem Equation456_4512_implies_Equation457 (G : Type*) [Magma G]
    (h456 : Equation456 G) (_ : Equation4512 G) : Equation457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h456 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))))) = X2 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = X2 := superpose eq11 eq14 -- forward demodulation 14,11
  have eq17 (X2 X3 : G) : (X2 ◇ X3) = X2 := superpose eq11 eq16 -- forward demodulation 16,11
  have eq20 : sK0 ≠ (sK0 ◇ sK1) := superpose eq17 eq13 -- backward demodulation 13,17
  subsumption eq20 eq17

theorem Equation457_4512_implies_Equation459 (G : Type*) [Magma G]
    (h457 : Equation457 G) (_ : Equation4512 G) : Equation459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h457 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1)))) := mod_symm nh
  have eq15 (X0 X3 X4 : G) : (X3 ◇ (X4 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq15 eq11 -- backward demodulation 11,15
  have eq20 : sK0 ≠ (sK0 ◇ sK1) := superpose eq15 eq13 -- backward demodulation 13,15
  subsumption eq20 eq17

theorem Equation459_4512_implies_Equation460 (G : Type*) [Magma G]
    (h459 : Equation459 G) (h4512 : Equation4512 G) : Equation460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h459 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := mod_symm nh
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X5 ◇ X0))) = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) = X4 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X5 ◇ X0)))) = X4 := superpose eq12 eq14 -- forward demodulation 14,12
  have eq18 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X5 ◇ X0))))) = X4 := superpose eq12 eq17 -- forward demodulation 17,12
  have eq19 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X5 ◇ X0)))))) = X4 := superpose eq12 eq18 -- forward demodulation 18,12
  have eq20 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X0))) = X4 := superpose eq12 eq15 -- forward demodulation 15,12
  have eq21 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X0)))) = X4 := superpose eq12 eq20 -- forward demodulation 20,12
  have eq22 (X1 X2 X4 : G) : (X4 ◇ (X1 ◇ X2)) = X4 := superpose eq21 eq19 -- backward demodulation 19,21
  have eq23 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq22 eq11 -- backward demodulation 11,22
  have eq26 : sK0 ≠ (sK0 ◇ sK1) := superpose eq22 eq13 -- backward demodulation 13,22
  subsumption eq26 eq23

theorem Equation460_4512_implies_Equation461 (G : Type*) [Magma G]
    (h460 : Equation460 G) (_ : Equation4512 G) : Equation461 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h460 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := mod_symm nh
  have eq16 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq23 : sK0 ≠ (sK0 ◇ sK1) := superpose eq16 eq13 -- backward demodulation 13,16
  subsumption eq23 eq16

theorem Equation461_4512_implies_Equation462 (G : Type*) [Magma G]
    (h461 : Equation461 G) (_ : Equation4512 G) : Equation462 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h461 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := mod_symm nh
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X5)) = X3 := superpose eq11 eq14 -- forward demodulation 14,11
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq17 eq11 -- backward demodulation 11,17
  have eq20 : sK0 ≠ (sK0 ◇ sK1) := superpose eq17 eq13 -- backward demodulation 13,17
  subsumption eq20 eq18


/- Equivalence of [5, 13, 19, 62, 65, 68, 72, 78, 82, 86, 90, 94, 463, 469, 476, 479, 483, 487, 491, 495, 503, 506, 510, 516, 520, 524, 532, 537, 541, 545, 549, 554, 558, 566, 571, 579, 583, 588, 593, 598, 603, 608] -/
theorem Equation608_4512_implies_Equation5 (G : Type*) [Magma G]
    (h608 : Equation608 G) (h4512 : Equation4512 G) : Equation5 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X0 := mod_symm (h608 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq33 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5)) = (X4 ◇ X5) := superpose eq11 eq12 -- superposition 12,11
  have eq46 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ X5) = (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X5))) := superpose eq12 eq33 -- forward demodulation 33,12
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ X5) = (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X5)))) := superpose eq12 eq46 -- forward demodulation 46,12
  have eq48 (X4 X5 : G) : (X4 ◇ X5) = X5 := superpose eq11 eq47 -- forward demodulation 47,11
  have eq97 : sK0 ≠ sK0 := superpose eq48 eq13 -- superposition 13,48
  subsumption eq97 rfl

theorem Equation5_4512_implies_Equation13 (G : Type*) [Magma G]
    (h5 : Equation5 G) (_ : Equation4512 G) : Equation13 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = X0 := mod_symm (h5 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq16 : sK0 ≠ (sK1 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq16 eq11

theorem Equation13_4512_implies_Equation19 (G : Type*) [Magma G]
    (h13 : Equation13 G) (_ : Equation4512 G) : Equation19 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := mod_symm (h13 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq15 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq14 eq13 -- backward demodulation 13,14
  subsumption eq15 eq11

theorem Equation19_4512_implies_Equation62 (G : Type*) [Magma G]
    (h19 : Equation19 G) (h4512 : Equation4512 G) : Equation62 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := mod_symm (h19 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X2 := superpose eq11 eq12 -- forward demodulation 12,11
  have eq15 : sK0 ≠ (sK1 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq17 (X2 X3 : G) : (X2 ◇ X3) = X3 := superpose eq11 eq14 -- superposition 14,11
  have eq25 : sK0 ≠ sK0 := superpose eq17 eq15 -- superposition 15,17
  subsumption eq25 rfl

theorem Equation62_4512_implies_Equation65 (G : Type*) [Magma G]
    (h62 : Equation62 G) (h4512 : Equation4512 G) : Equation65 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h62 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq16 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq17 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := superpose eq11 eq16 -- forward demodulation 16,11
  have eq18 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq11 eq17 -- superposition 17,11
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq17 eq18 -- forward demodulation 18,17
  have eq24 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq23 -- forward demodulation 23,11
  have eq25 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq24 eq17 -- backward demodulation 17,24
  have eq29 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq25 eq13 -- backward demodulation 13,25
  have eq31 : sK0 ≠ (sK1 ◇ sK0) := superpose eq25 eq29 -- forward demodulation 29,25
  subsumption eq31 eq25

theorem Equation65_4512_implies_Equation68 (G : Type*) [Magma G]
    (h65 : Equation65 G) (h4512 : Equation4512 G) : Equation68 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := mod_symm (h65 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq16 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq24 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq25 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ X1) := superpose eq24 eq16 -- backward demodulation 16,24
  have eq26 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq25 eq11 -- backward demodulation 11,25
  have eq27 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq25 eq13 -- backward demodulation 13,25
  subsumption eq27 eq26

theorem Equation68_4512_implies_Equation72 (G : Type*) [Magma G]
    (h68 : Equation68 G) (h4512 : Equation4512 G) : Equation72 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h68 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq17 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X1 := superpose eq11 eq16 -- forward demodulation 16,11
  have eq18 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq17 eq11 -- backward demodulation 11,17
  have eq21 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq18 eq13 -- backward demodulation 13,18
  have eq23 : sK0 ≠ (sK1 ◇ sK0) := superpose eq18 eq21 -- forward demodulation 21,18
  subsumption eq23 eq18

theorem Equation72_4512_implies_Equation78 (G : Type*) [Magma G]
    (h72 : Equation72 G) (h4512 : Equation4512 G) : Equation78 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := mod_symm (h72 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq14 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq14 eq11 -- superposition 11,14
  have eq16 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq12 eq15 -- forward demodulation 15,12
  have eq17 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq16 -- forward demodulation 16,11
  have eq19 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq17 eq11 -- backward demodulation 11,17
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq17 eq12 -- superposition 12,17
  have eq35 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq19 eq32 -- forward demodulation 32,19
  have eq41 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq35 eq13 -- backward demodulation 13,35
  have eq46 : sK0 ≠ (sK1 ◇ sK0) := superpose eq35 eq41 -- forward demodulation 41,35
  subsumption eq46 eq35

theorem Equation78_4512_implies_Equation82 (G : Type*) [Magma G]
    (h78 : Equation78 G) (_ : Equation4512 G) : Equation82 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := mod_symm (h78 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq11 eq15 -- superposition 15,11
  have eq25 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (X0 ◇ sK0))) := superpose eq15 eq13 -- superposition 13,15
  subsumption eq25 eq16

theorem Equation82_4512_implies_Equation86 (G : Type*) [Magma G]
    (h82 : Equation82 G) (_ : Equation4512 G) : Equation86 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X0 := mod_symm (h82 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq15 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11
  have eq16 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := superpose eq15 eq13 -- backward demodulation 13,15
  subsumption eq16 eq11

theorem Equation86_4512_implies_Equation90 (G : Type*) [Magma G]
    (h86 : Equation86 G) (_ : Equation4512 G) : Equation90 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := mod_symm (h86 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq11 eq15 -- superposition 15,11
  have eq22 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (X0 ◇ sK0))) := superpose eq15 eq13 -- superposition 13,15
  subsumption eq22 eq16

theorem Equation90_4512_implies_Equation94 (G : Type*) [Magma G]
    (h90 : Equation90 G) (_ : Equation4512 G) : Equation94 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X0 := mod_symm (h90 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := superpose eq15 eq11 -- superposition 11,15
  have eq25 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) := superpose eq15 eq13 -- superposition 13,15
  subsumption eq25 eq22

theorem Equation94_4512_implies_Equation463 (G : Type*) [Magma G]
    (h94 : Equation94 G) (h4512 : Equation4512 G) : Equation463 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X0 := mod_symm (h94 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq14 : sK0 ≠ (sK1 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq31 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)) = (X3 ◇ X4) := superpose eq11 eq12 -- superposition 12,11
  have eq43 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) := superpose eq12 eq31 -- forward demodulation 31,12
  have eq44 (X3 X4 : G) : (X3 ◇ X4) = X4 := superpose eq11 eq43 -- forward demodulation 43,11
  have eq79 : sK0 ≠ sK0 := superpose eq44 eq14 -- superposition 14,44
  subsumption eq79 rfl

theorem Equation463_4512_implies_Equation469 (G : Type*) [Magma G]
    (h463 : Equation463 G) (h4512 : Equation4512 G) : Equation469 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h463 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq25 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))) = X2 := superpose eq11 eq12 -- superposition 12,11
  have eq35 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq11 eq25 -- forward demodulation 25,11
  have eq40 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := superpose eq35 eq13 -- backward demodulation 13,35
  have eq48 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq35 eq40 -- forward demodulation 40,35
  have eq49 : sK0 ≠ (sK1 ◇ sK0) := superpose eq35 eq48 -- forward demodulation 48,35
  subsumption eq49 eq35

theorem Equation469_4512_implies_Equation476 (G : Type*) [Magma G]
    (h469 : Equation469 G) (h4512 : Equation4512 G) : Equation476 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h469 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq25 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2))))) = X2 := superpose eq11 eq12 -- superposition 12,11
  have eq35 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq11 eq25 -- forward demodulation 25,11
  have eq41 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := superpose eq35 eq13 -- backward demodulation 13,35
  have eq55 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq35 eq41 -- forward demodulation 41,35
  have eq56 : sK0 ≠ (sK1 ◇ sK0) := superpose eq35 eq55 -- forward demodulation 55,35
  subsumption eq56 eq35

theorem Equation476_4512_implies_Equation479 (G : Type*) [Magma G]
    (h476 : Equation476 G) (h4512 : Equation4512 G) : Equation479 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h476 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq17 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq18 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq19 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq20 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq12 eq19 -- forward demodulation 19,12
  have eq21 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq20 -- forward demodulation 20,11
  have eq23 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq21 eq11 -- superposition 11,21
  have eq24 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq25 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq24 -- forward demodulation 24,11
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq34 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq12 eq27 -- forward demodulation 27,12
  have eq35 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq12 eq34 -- forward demodulation 34,12
  have eq36 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq12 eq35 -- forward demodulation 35,12
  have eq37 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ X1)) := superpose eq36 eq18 -- backward demodulation 18,36
  have eq38 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq37 eq11 -- backward demodulation 11,37
  have eq47 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq25 -- superposition 25,12
  have eq50 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq38 eq47 -- forward demodulation 47,38
  have eq58 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := superpose eq50 eq13 -- backward demodulation 13,50
  have eq74 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq50 eq58 -- forward demodulation 58,50
  have eq75 : sK0 ≠ (sK1 ◇ sK0) := superpose eq50 eq74 -- forward demodulation 74,50
  subsumption eq75 eq50

theorem Equation479_4512_implies_Equation483 (G : Type*) [Magma G]
    (h479 : Equation479 G) (h4512 : Equation4512 G) : Equation483 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h479 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X1))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq21 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))) := superpose eq12 eq20 -- forward demodulation 20,12
  have eq24 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) = X2 := superpose eq16 eq11 -- superposition 11,16
  have eq28 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2))))) = X2 := superpose eq12 eq24 -- forward demodulation 24,12
  have eq34 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ X2) := superpose eq16 eq12 -- superposition 12,16
  have eq48 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X2)))) = X2 := superpose eq34 eq28 -- backward demodulation 28,34
  have eq50 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq34 eq21 -- backward demodulation 21,34
  have eq51 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq34 eq13 -- backward demodulation 13,34
  have eq53 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X2))) = X2 := superpose eq34 eq48 -- forward demodulation 48,34
  have eq54 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X2 := superpose eq34 eq53 -- forward demodulation 53,34
  have eq61 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq34 eq50 -- forward demodulation 50,34
  have eq62 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = X1 := superpose eq54 eq61 -- forward demodulation 61,54
  have eq65 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq62 eq34 -- backward demodulation 34,62
  have eq69 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq65 eq54 -- backward demodulation 54,65
  have eq80 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq69 eq51 -- forward demodulation 51,69
  have eq81 : sK0 ≠ (sK1 ◇ sK0) := superpose eq65 eq80 -- forward demodulation 80,65
  subsumption eq81 eq69

theorem Equation483_4512_implies_Equation487 (G : Type*) [Magma G]
    (h483 : Equation483 G) (_ : Equation4512 G) : Equation487 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h483 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq19 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := superpose eq15 eq13 -- backward demodulation 13,15
  subsumption eq19 eq11

theorem Equation487_4512_implies_Equation491 (G : Type*) [Magma G]
    (h487 : Equation487 G) (h4512 : Equation4512 G) : Equation491 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h487 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq23 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))))) = X2 := superpose eq11 eq12 -- superposition 12,11
  have eq25 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = X3 := superpose eq12 eq11 -- superposition 11,12
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))))) = X2 := superpose eq12 eq23 -- forward demodulation 23,12
  have eq34 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq25 eq33 -- backward demodulation 33,25
  have eq42 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := superpose eq34 eq13 -- backward demodulation 13,34
  have eq63 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq34 eq42 -- forward demodulation 42,34
  have eq64 : sK0 ≠ (sK1 ◇ sK0) := superpose eq34 eq63 -- forward demodulation 63,34
  subsumption eq64 eq34

theorem Equation491_4512_implies_Equation495 (G : Type*) [Magma G]
    (h491 : Equation491 G) (_ : Equation4512 G) : Equation495 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h491 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := mod_symm nh
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq22 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := superpose eq16 eq13 -- backward demodulation 13,16
  have eq25 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq16 eq16 -- superposition 16,16
  have eq26 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X1 := superpose eq16 eq11 -- superposition 11,16
  have eq49 (X0 : G) : sK0 ≠ (X0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := superpose eq25 eq22 -- superposition 22,25
  subsumption eq49 eq26

theorem Equation495_4512_implies_Equation503 (G : Type*) [Magma G]
    (h495 : Equation495 G) (h4512 : Equation4512 G) : Equation503 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0)))) = X0 := mod_symm (h495 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq14 (X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X1))) = (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X5 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X1))) = (X4 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X5 ◇ X1)))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq18 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X1))) = X1 := superpose eq11 eq17 -- forward demodulation 17,11
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq18 eq11 -- backward demodulation 11,18
  have eq22 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := superpose eq19 eq13 -- backward demodulation 13,19
  have eq25 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq19 eq22 -- forward demodulation 22,19
  have eq26 : sK0 ≠ (sK1 ◇ sK0) := superpose eq19 eq25 -- forward demodulation 25,19
  subsumption eq26 eq19

theorem Equation503_4512_implies_Equation506 (G : Type*) [Magma G]
    (h503 : Equation503 G) (h4512 : Equation4512 G) : Equation506 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h503 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq16 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq12 eq25 -- forward demodulation 25,12
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq12 eq26 -- forward demodulation 26,12
  have eq28 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ X1)) := superpose eq27 eq17 -- backward demodulation 17,27
  have eq29 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq28 eq11 -- backward demodulation 11,28
  have eq40 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq29 eq29 -- superposition 29,29
  have eq42 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) := superpose eq29 eq12 -- superposition 12,29
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := superpose eq12 eq42 -- forward demodulation 42,12
  have eq47 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq12 eq46 -- forward demodulation 46,12
  have eq53 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq40 eq29 -- superposition 29,40
  have eq56 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq12 eq53 -- forward demodulation 53,12
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq29 eq56 -- forward demodulation 56,29
  have eq59 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq57 eq29 -- backward demodulation 29,57
  have eq66 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ X2)) := superpose eq59 eq47 -- backward demodulation 47,59
  have eq67 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq59 eq66 -- forward demodulation 66,59
  have eq74 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := superpose eq67 eq13 -- backward demodulation 13,67
  have eq85 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq67 eq74 -- forward demodulation 74,67
  have eq86 : sK0 ≠ (sK1 ◇ sK0) := superpose eq67 eq85 -- forward demodulation 85,67
  subsumption eq86 eq67

theorem Equation506_4512_implies_Equation510 (G : Type*) [Magma G]
    (h506 : Equation506 G) (h4512 : Equation4512 G) : Equation510 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h506 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X1 := superpose eq11 eq16 -- superposition 16,11
  have eq27 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq16 eq12 -- superposition 12,16
  have eq31 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq42 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := superpose eq27 eq13 -- backward demodulation 13,27
  have eq62 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq12 eq15 -- superposition 15,12
  have eq66 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X3)) = ((X2 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq15 eq12 -- superposition 12,15
  have eq77 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (X0 ◇ sK0))) := superpose eq15 eq42 -- superposition 42,15
  have eq79 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq62 -- forward demodulation 62,12
  have eq80 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ X3))) := superpose eq12 eq66 -- forward demodulation 66,12
  have eq90 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = (X3 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X4 ◇ X1)))) := superpose eq11 eq31 -- superposition 31,11
  have eq92 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X4 ◇ (X1 ◇ (X2 ◇ X1)))))) := superpose eq15 eq31 -- superposition 31,15
  have eq125 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X4 ◇ X1))))) := superpose eq12 eq90 -- forward demodulation 90,12
  have eq126 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X4 ◇ X1)))))) := superpose eq12 eq125 -- forward demodulation 125,12
  have eq127 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X4 ◇ X1))))))) := superpose eq12 eq126 -- forward demodulation 126,12
  have eq128 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = (X3 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq20 eq127 -- forward demodulation 127,20
  have eq133 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X4 ◇ (X1 ◇ (X2 ◇ X1))))))) := superpose eq12 eq92 -- forward demodulation 92,12
  have eq134 (X0 X1 X3 : G) : (X0 ◇ X1) = (X3 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq20 eq133 -- forward demodulation 133,20
  have eq135 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq134 eq128 -- backward demodulation 128,134
  have eq142 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq135 eq11 -- backward demodulation 11,135
  have eq153 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq142 eq15 -- backward demodulation 15,142
  have eq159 (X0 X1 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ X3))) := superpose eq142 eq80 -- backward demodulation 80,142
  have eq167 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := superpose eq153 eq79 -- backward demodulation 79,153
  have eq168 : sK0 ≠ (sK1 ◇ sK0) := superpose eq153 eq77 -- backward demodulation 77,153
  have eq173 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X2 := superpose eq159 eq167 -- backward demodulation 167,159
  have eq175 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq173 eq27 -- backward demodulation 27,173
  have eq352 : sK0 ≠ sK0 := superpose eq175 eq168 -- superposition 168,175
  subsumption eq352 rfl

theorem Equation510_4512_implies_Equation516 (G : Type*) [Magma G]
    (h510 : Equation510 G) (h4512 : Equation4512 G) : Equation516 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h510 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq14 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq14 eq11 -- superposition 11,14
  have eq16 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = X0 := superpose eq12 eq15 -- forward demodulation 15,12
  have eq17 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq11 eq16 -- forward demodulation 16,11
  have eq18 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose eq12 eq17 -- forward demodulation 17,12
  have eq22 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq14 eq12 -- superposition 12,14
  have eq36 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq22 eq18 -- backward demodulation 18,22
  have eq37 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq22 eq36 -- forward demodulation 36,22
  have eq38 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq37 eq14 -- backward demodulation 14,37
  have eq41 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq38 eq11 -- backward demodulation 11,38
  have eq54 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq38 eq12 -- superposition 12,38
  have eq58 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq54 eq41 -- backward demodulation 41,54
  have eq60 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := superpose eq54 eq13 -- backward demodulation 13,54
  have eq61 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq58 eq54 -- backward demodulation 54,58
  have eq77 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq61 eq60 -- forward demodulation 60,61
  have eq78 : sK0 ≠ (sK1 ◇ sK0) := superpose eq61 eq77 -- forward demodulation 77,61
  subsumption eq78 eq61

theorem Equation516_4512_implies_Equation520 (G : Type*) [Magma G]
    (h516 : Equation516 G) (_ : Equation4512 G) : Equation520 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h516 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := superpose eq15 eq13 -- backward demodulation 13,15
  subsumption eq17 eq11

theorem Equation520_4512_implies_Equation524 (G : Type*) [Magma G]
    (h520 : Equation520 G) (_ : Equation4512 G) : Equation524 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h520 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq11 eq11 -- superposition 11,11
  have eq16 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := superpose eq15 eq13 -- backward demodulation 13,15
  subsumption eq16 eq11

theorem Equation524_4512_implies_Equation532 (G : Type*) [Magma G]
    (h524 : Equation524 G) (h4512 : Equation4512 G) : Equation532 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h524 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))))) = X3 := superpose eq11 eq12 -- superposition 12,11
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = X3 := superpose eq12 eq11 -- superposition 11,12
  have eq28 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))))) = X3 := superpose eq12 eq18 -- forward demodulation 18,12
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3))))))) = X3 := superpose eq12 eq28 -- forward demodulation 28,12
  have eq34 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X2 ◇ X3)) := superpose eq12 eq15 -- superposition 15,12
  have eq56 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))))) = X3 := superpose eq34 eq29 -- backward demodulation 29,34
  have eq57 : sK0 ≠ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) := superpose eq34 eq13 -- backward demodulation 13,34
  have eq58 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq20 eq56 -- forward demodulation 56,20
  have eq77 : sK0 ≠ (sK1 ◇ (sK3 ◇ sK0)) := superpose eq58 eq57 -- forward demodulation 57,58
  have eq78 : sK0 ≠ (sK1 ◇ sK0) := superpose eq58 eq77 -- forward demodulation 77,58
  subsumption eq78 eq58

theorem Equation532_4512_implies_Equation537 (G : Type*) [Magma G]
    (h532 : Equation532 G) (_ : Equation4512 G) : Equation537 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) = X0 := mod_symm (h532 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq16 (X0 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X3 := superpose eq11 eq16 -- superposition 16,11
  have eq27 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (X0 ◇ sK0)))) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq27 eq17

theorem Equation537_4512_implies_Equation541 (G : Type*) [Magma G]
    (h537 : Equation537 G) (_ : Equation4512 G) : Equation541 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h537 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq15 eq13 -- backward demodulation 13,15
  subsumption eq20 eq11

theorem Equation541_4512_implies_Equation545 (G : Type*) [Magma G]
    (h541 : Equation541 G) (_ : Equation4512 G) : Equation545 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h541 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq11 eq11 -- superposition 11,11
  have eq19 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq15 eq13 -- backward demodulation 13,15
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq15 eq15 -- superposition 15,15
  have eq21 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) = X1 := superpose eq15 eq11 -- superposition 11,15
  have eq44 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq20 eq19 -- superposition 19,20
  subsumption eq44 eq21

theorem Equation545_4512_implies_Equation549 (G : Type*) [Magma G]
    (h545 : Equation545 G) (h4512 : Equation4512 G) : Equation549 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h545 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := mod_symm nh
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = X3 := superpose eq11 eq12 -- superposition 12,11
  have eq32 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq11 eq21 -- forward demodulation 21,11
  have eq38 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := superpose eq32 eq13 -- backward demodulation 13,32
  have eq47 : sK0 ≠ (sK1 ◇ (sK3 ◇ sK0)) := superpose eq32 eq38 -- forward demodulation 38,32
  have eq48 : sK0 ≠ (sK1 ◇ sK0) := superpose eq32 eq47 -- forward demodulation 47,32
  subsumption eq48 eq32

theorem Equation549_4512_implies_Equation554 (G : Type*) [Magma G]
    (h549 : Equation549 G) (_ : Equation4512 G) : Equation554 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) = X0 := mod_symm (h549 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq27 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := superpose eq16 eq11 -- superposition 11,16
  have eq30 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (X0 ◇ sK0)))) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq30 eq27

theorem Equation554_4512_implies_Equation558 (G : Type*) [Magma G]
    (h554 : Equation554 G) (_ : Equation4512 G) : Equation558 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h554 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq16 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := superpose eq14 eq13 -- backward demodulation 13,14
  subsumption eq16 eq11

theorem Equation558_4512_implies_Equation566 (G : Type*) [Magma G]
    (h558 : Equation558 G) (_ : Equation4512 G) : Equation566 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h558 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq16 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := superpose eq15 eq13 -- backward demodulation 13,15
  subsumption eq16 eq11

theorem Equation566_4512_implies_Equation571 (G : Type*) [Magma G]
    (h566 : Equation566 G) (_ : Equation4512 G) : Equation571 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X0)))) = X0 := mod_symm (h566 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq16 (X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = X3 := superpose eq11 eq16 -- superposition 16,11
  have eq27 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (X0 ◇ sK0)))) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq27 eq17

theorem Equation571_4512_implies_Equation579 (G : Type*) [Magma G]
    (h571 : Equation571 G) (_ : Equation4512 G) : Equation579 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h571 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq16 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := superpose eq15 eq13 -- backward demodulation 13,15
  subsumption eq16 eq11

theorem Equation579_4512_implies_Equation583 (G : Type*) [Magma G]
    (h579 : Equation579 G) (_ : Equation4512 G) : Equation583 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h579 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := mod_symm nh
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X1)))) = X1 := superpose eq16 eq11 -- superposition 11,16
  have eq27 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq27 eq23

theorem Equation583_4512_implies_Equation588 (G : Type*) [Magma G]
    (h583 : Equation583 G) (_ : Equation4512 G) : Equation588 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X0)))) = X0 := mod_symm (h583 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq24 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X2)))) = X2 := superpose eq16 eq11 -- superposition 11,16
  have eq27 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (X0 ◇ sK0)))) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq27 eq24

theorem Equation588_4512_implies_Equation593 (G : Type*) [Magma G]
    (h588 : Equation588 G) (_ : Equation4512 G) : Equation593 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h588 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq16 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq17 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := superpose eq16 eq13 -- backward demodulation 13,16
  subsumption eq17 eq11

theorem Equation593_4512_implies_Equation598 (G : Type*) [Magma G]
    (h593 : Equation593 G) (_ : Equation4512 G) : Equation598 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h593 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = (X2 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = X3 := superpose eq11 eq16 -- superposition 16,11
  have eq27 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ sK0)))) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq27 eq17

theorem Equation598_4512_implies_Equation603 (G : Type*) [Magma G]
    (h598 : Equation598 G) (_ : Equation4512 G) : Equation603 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h598 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := mod_symm nh
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq23 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X4 ◇ (X2 ◇ X1)))) = X1 := superpose eq16 eq11 -- superposition 11,16
  have eq27 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq27 eq23

theorem Equation603_4512_implies_Equation608 (G : Type*) [Magma G]
    (h603 : Equation603 G) (_ : Equation4512 G) : Equation608 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) = X0 := mod_symm (h603 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK0)))) := mod_symm nh
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq23 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ (X2 ◇ X1)))) = X1 := superpose eq16 eq11 -- superposition 11,16
  have eq27 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK0)))) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq27 eq23


/- Equivalence of [10, 49, 52, 55, 58, 413, 416, 422, 426, 432, 439, 442, 446, 450, 454, 458] -/
theorem Equation458_4512_implies_Equation10 (G : Type*) [Magma G]
    (h458 : Equation458 G) (h4512 : Equation4512 G) : Equation10 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) = X0 := mod_symm (h458 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq16 (X0 X3 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq25 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq16 eq12 -- superposition 12,16
  have eq29 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq41 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := superpose eq11 eq25 -- superposition 25,11
  have eq72 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq29 -- superposition 29,11
  have eq141 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq72 eq41 -- superposition 41,72
  have eq367 : sK0 ≠ sK0 := superpose eq141 eq13 -- superposition 13,141
  subsumption eq367 rfl

theorem Equation10_4512_implies_Equation49 (G : Type*) [Magma G]
    (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation49 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h10 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq26 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq36 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq26 -- superposition 26,11
  have eq86 : sK0 ≠ sK0 := superpose eq36 eq14 -- superposition 14,36
  subsumption eq86 rfl

theorem Equation49_4512_implies_Equation52 (G : Type*) [Magma G]
    (h49 : Equation49 G) (h4512 : Equation4512 G) : Equation52 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := mod_symm (h49 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq20 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq35 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq20 -- superposition 20,11
  have eq52 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq35 eq13 -- backward demodulation 13,35
  have eq64 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq35 eq12 -- superposition 12,35
  have eq74 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq11 eq64 -- superposition 64,11
  have eq138 : sK0 ≠ sK0 := superpose eq74 eq52 -- superposition 52,74
  subsumption eq138 rfl

theorem Equation52_4512_implies_Equation55 (G : Type*) [Magma G]
    (h52 : Equation52 G) (h4512 : Equation4512 G) : Equation55 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := mod_symm (h52 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq14 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq14 eq12 -- superposition 12,14
  have eq35 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq19 eq11 -- superposition 11,19
  have eq36 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq19 eq12 -- superposition 12,19
  have eq39 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq35 eq19 -- backward demodulation 19,35
  have eq43 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq39 eq11 -- backward demodulation 11,39
  have eq49 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq36 -- forward demodulation 36,12
  have eq54 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq43 eq12 -- superposition 12,43
  have eq56 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq12 eq54 -- forward demodulation 54,12
  have eq57 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq56 eq49 -- backward demodulation 49,56
  have eq59 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq57 eq13 -- backward demodulation 13,57
  subsumption eq59 eq43

theorem Equation55_4512_implies_Equation58 (G : Type*) [Magma G]
    (h55 : Equation55 G) (h4512 : Equation4512 G) : Equation58 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h55 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq15 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq15 eq11 -- superposition 11,15
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq12 eq16 -- forward demodulation 16,12
  have eq18 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq17 -- forward demodulation 17,11
  have eq21 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq27 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq28 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq12 eq27 -- forward demodulation 27,12
  have eq31 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) = X2 := superpose eq12 eq24 -- forward demodulation 24,12
  have eq34 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq18 eq12 -- superposition 12,18
  have eq40 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq34 eq28 -- backward demodulation 28,34
  have eq41 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq40 eq31 -- backward demodulation 31,40
  have eq73 : sK0 ≠ sK0 := superpose eq41 eq13 -- superposition 13,41
  subsumption eq73 rfl

theorem Equation58_4512_implies_Equation413 (G : Type*) [Magma G]
    (h58 : Equation58 G) (h4512 : Equation4512 G) : Equation413 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := mod_symm (h58 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq28 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq63 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq28 -- superposition 28,11
  have eq83 : sK0 ≠ sK0 := superpose eq63 eq14 -- superposition 14,63
  subsumption eq83 rfl

theorem Equation413_4512_implies_Equation416 (G : Type*) [Magma G]
    (h413 : Equation413 G) (h4512 : Equation4512 G) : Equation416 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h413 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq24 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq46 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq24 -- superposition 24,11
  have eq78 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := superpose eq46 eq13 -- backward demodulation 13,46
  have eq97 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq46 eq12 -- superposition 12,46
  have eq103 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq97 eq11 -- backward demodulation 11,97
  have eq118 : sK0 ≠ sK0 := superpose eq103 eq78 -- superposition 78,103
  subsumption eq118 rfl

theorem Equation416_4512_implies_Equation422 (G : Type*) [Magma G]
    (h416 : Equation416 G) (h4512 : Equation4512 G) : Equation422 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h416 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq37 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq18 -- superposition 18,11
  have eq49 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := superpose eq37 eq18 -- backward demodulation 18,37
  have eq117 : sK0 ≠ sK0 := superpose eq49 eq13 -- superposition 13,49
  subsumption eq117 rfl

theorem Equation422_4512_implies_Equation426 (G : Type*) [Magma G]
    (h422 : Equation422 G) (h4512 : Equation4512 G) : Equation426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h422 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq24 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq44 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq24 -- superposition 24,11
  have eq68 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq44 eq13 -- backward demodulation 13,44
  have eq69 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq44 eq68 -- forward demodulation 68,44
  have eq86 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq44 eq12 -- superposition 12,44
  have eq87 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq44 eq11 -- superposition 11,44
  have eq212 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq86 eq87 -- superposition 87,86
  have eq264 : sK0 ≠ sK0 := superpose eq212 eq69 -- superposition 69,212
  subsumption eq264 rfl

theorem Equation426_4512_implies_Equation432 (G : Type*) [Magma G]
    (h426 : Equation426 G) (h4512 : Equation4512 G) : Equation432 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h426 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq19 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq34 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq19 eq19 -- superposition 19,19
  have eq36 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq19 -- superposition 19,11
  have eq45 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq36 eq34 -- backward demodulation 34,36
  have eq52 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq36 eq45 -- forward demodulation 45,36
  have eq53 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq52 eq13 -- backward demodulation 13,52
  subsumption eq53 eq52

theorem Equation432_4512_implies_Equation439 (G : Type*) [Magma G]
    (h432 : Equation432 G) (h4512 : Equation4512 G) : Equation439 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h432 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq26 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq15 eq12 -- superposition 12,15
  have eq32 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq48 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq26 eq11 -- superposition 11,26
  have eq50 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq26 eq12 -- superposition 12,26
  have eq57 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq26 eq48 -- forward demodulation 48,26
  have eq59 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq57 eq32 -- backward demodulation 32,57
  have eq65 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq12 eq50 -- forward demodulation 50,12
  have eq66 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq12 eq65 -- forward demodulation 65,12
  have eq67 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := superpose eq66 eq13 -- backward demodulation 13,66
  subsumption eq67 eq59

theorem Equation439_4512_implies_Equation442 (G : Type*) [Magma G]
    (h439 : Equation439 G) (h4512 : Equation4512 G) : Equation442 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h439 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq16 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq16 eq11 -- superposition 11,16
  have eq18 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = X0 := superpose eq12 eq17 -- forward demodulation 17,12
  have eq19 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq12 eq18 -- forward demodulation 18,12
  have eq20 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq19 -- forward demodulation 19,11
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2)) = (X0 ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq26 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq16 eq12 -- superposition 12,16
  have eq29 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq34 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq35 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq12 eq34 -- forward demodulation 34,12
  have eq36 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq12 eq35 -- forward demodulation 35,12
  have eq40 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq20 eq26 -- forward demodulation 26,20
  have eq44 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))))) = X2 := superpose eq12 eq29 -- forward demodulation 29,12
  have eq45 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))))) = X2 := superpose eq12 eq44 -- forward demodulation 44,12
  have eq51 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq40 eq12 -- superposition 12,40
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq51 eq36 -- backward demodulation 36,51
  have eq59 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := superpose eq51 eq13 -- backward demodulation 13,51
  have eq63 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq51 eq58 -- forward demodulation 58,51
  have eq64 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) = X2 := superpose eq63 eq45 -- backward demodulation 45,63
  have eq65 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq63 eq64 -- forward demodulation 64,63
  subsumption eq59 eq65

theorem Equation442_4512_implies_Equation446 (G : Type*) [Magma G]
    (h442 : Equation442 G) (h4512 : Equation4512 G) : Equation446 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h442 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq26 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq16 eq12 -- superposition 12,16
  have eq30 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq40 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := superpose eq26 eq13 -- backward demodulation 13,26
  have eq55 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq30 -- superposition 30,11
  have eq79 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq55 eq12 -- superposition 12,55
  have eq92 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := superpose eq79 eq11 -- backward demodulation 11,79
  have eq114 : sK0 ≠ sK0 := superpose eq92 eq40 -- superposition 40,92
  subsumption eq114 rfl

theorem Equation446_4512_implies_Equation450 (G : Type*) [Magma G]
    (h446 : Equation446 G) (h4512 : Equation4512 G) : Equation450 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h446 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq15 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq15 eq12 -- superposition 12,15
  have eq26 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq39 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq21 eq11 -- superposition 11,21
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq26 -- superposition 26,11
  have eq72 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq57 eq39 -- backward demodulation 39,57
  have eq117 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ X2) := superpose eq72 eq12 -- superposition 12,72
  have eq119 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq12 eq117 -- forward demodulation 117,12
  have eq120 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq119 eq13 -- backward demodulation 13,119
  subsumption eq120 eq72

theorem Equation450_4512_implies_Equation454 (G : Type*) [Magma G]
    (h450 : Equation450 G) (h4512 : Equation4512 G) : Equation454 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h450 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq25 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq16 eq12 -- superposition 12,16
  have eq30 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = X3 := superpose eq12 eq11 -- superposition 11,12
  have eq45 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq25 eq11 -- superposition 11,25
  have eq47 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq25 eq12 -- superposition 12,25
  have eq54 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq12 eq47 -- forward demodulation 47,12
  have eq55 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq12 eq54 -- forward demodulation 54,12
  have eq56 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := superpose eq55 eq13 -- backward demodulation 13,55
  have eq101 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq45 eq30 -- superposition 30,45
  have eq176 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq12 eq101 -- superposition 101,12
  have eq383 : sK0 ≠ sK0 := superpose eq176 eq56 -- superposition 56,176
  subsumption eq383 rfl

theorem Equation454_4512_implies_Equation458 (G : Type*) [Magma G]
    (h454 : Equation454 G) (h4512 : Equation4512 G) : Equation458 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h454 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := mod_symm nh
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq25 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq16 eq12 -- superposition 12,16
  have eq31 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3))))) = X3 := superpose eq12 eq11 -- superposition 11,12
  have eq49 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq25 eq12 -- superposition 12,25
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq12 eq49 -- forward demodulation 49,12
  have eq58 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq12 eq57 -- forward demodulation 57,12
  have eq59 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X3 := superpose eq58 eq31 -- backward demodulation 31,58
  have eq84 : sK0 ≠ sK0 := superpose eq59 eq13 -- superposition 13,59
  subsumption eq84 rfl


/- Equivalence of [11, 414, 417, 427, 444, 452, 455] -/
theorem Equation455_4512_implies_Equation11 (G : Type*) [Magma G]
    (h455 : Equation455 G) (_ : Equation4512 G) : Equation11 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h455 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq16 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq11 eq11 -- superposition 11,11
  have eq26 : sK0 ≠ sK0 := superpose eq16 eq13 -- superposition 13,16
  subsumption eq26 rfl

theorem Equation11_4512_implies_Equation414 (G : Type*) [Magma G]
    (h11 : Equation11 G) (_ : Equation4512 G) : Equation414 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := mod_symm (h11 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation414_4512_implies_Equation417 (G : Type*) [Magma G]
    (h414 : Equation414 G) (h4512 : Equation4512 G) : Equation417 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h414 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq14 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2)) = (X0 ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq23 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2)))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq35 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq12 eq14 -- superposition 14,12
  have eq48 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq35 eq11 -- superposition 11,35
  have eq130 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ X0) := superpose eq18 eq24 -- superposition 24,18
  have eq170 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq130 eq13 -- backward demodulation 13,130
  subsumption eq170 eq48

theorem Equation417_4512_implies_Equation427 (G : Type*) [Magma G]
    (h417 : Equation417 G) (h4512 : Equation4512 G) : Equation427 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h417 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)))) = X0 := superpose eq12 eq14 -- forward demodulation 14,12
  have eq16 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))))) = X0 := superpose eq12 eq15 -- forward demodulation 15,12
  have eq17 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) = X0 := superpose eq12 eq16 -- forward demodulation 16,12
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) = (X0 ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq22 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq25 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq26 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq12 eq25 -- forward demodulation 25,12
  have eq27 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq12 eq26 -- forward demodulation 26,12
  have eq28 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq27 eq17 -- backward demodulation 17,27
  have eq40 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq28 eq12 -- superposition 12,28
  have eq44 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq40 -- forward demodulation 40,12
  have eq89 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq44 eq22 -- superposition 22,44
  have eq157 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq44 eq27 -- superposition 27,44
  have eq180 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq27 eq157 -- forward demodulation 157,27
  have eq181 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq180 eq89 -- backward demodulation 89,180
  have eq182 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq180 eq13 -- backward demodulation 13,180
  subsumption eq182 eq181

theorem Equation427_4512_implies_Equation444 (G : Type*) [Magma G]
    (h427 : Equation427 G) (h4512 : Equation4512 G) : Equation444 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h427 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)))) = X0 := superpose eq12 eq14 -- forward demodulation 14,12
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))))) = X0 := superpose eq12 eq16 -- forward demodulation 16,12
  have eq18 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) = X0 := superpose eq12 eq17 -- forward demodulation 17,12
  have eq26 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq42 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq18 -- superposition 18,11
  have eq83 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq42 eq12 -- superposition 12,42
  have eq87 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq83 -- forward demodulation 83,12
  have eq181 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq26 eq87 -- superposition 87,26
  have eq192 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq87 eq26 -- superposition 26,87
  have eq204 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq87 eq181 -- forward demodulation 181,87
  have eq216 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq204 eq192 -- forward demodulation 192,204
  have eq220 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq216 eq13 -- backward demodulation 13,216
  subsumption eq220 eq216

theorem Equation444_4512_implies_Equation452 (G : Type*) [Magma G]
    (h444 : Equation444 G) (h4512 : Equation4512 G) : Equation452 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h444 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X2 := superpose eq11 eq14 -- forward demodulation 14,11
  have eq22 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := superpose eq12 eq16 -- superposition 16,12
  have eq38 : sK0 ≠ sK0 := superpose eq22 eq13 -- superposition 13,22
  subsumption eq38 rfl

theorem Equation452_4512_implies_Equation455 (G : Type*) [Magma G]
    (h452 : Equation452 G) (h4512 : Equation4512 G) : Equation455 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h452 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X0))) = X3 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X0)))) = X3 := superpose eq12 eq14 -- forward demodulation 14,12
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))))) = X3 := superpose eq12 eq16 -- forward demodulation 16,12
  have eq18 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))))) = X3 := superpose eq12 eq17 -- forward demodulation 17,12
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq26 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3))) := superpose eq12 eq19 -- forward demodulation 19,12
  have eq27 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X3)))) := superpose eq12 eq26 -- forward demodulation 26,12
  have eq28 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq12 eq27 -- forward demodulation 27,12
  have eq29 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq28 eq18 -- backward demodulation 18,28
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq29 eq12 -- superposition 12,29
  have eq42 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq12 eq39 -- forward demodulation 39,12
  have eq43 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq42 eq13 -- backward demodulation 13,42
  subsumption eq43 eq29


/- Equivalence of [14, 464, 481, 489, 492, 508, 522, 543, 546, 556, 572] -/
theorem Equation572_4512_implies_Equation14 (G : Type*) [Magma G]
    (h572 : Equation572 G) (_ : Equation4512 G) : Equation14 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h572 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq16 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq11 eq16 -- superposition 16,11
  have eq22 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq11 -- backward demodulation 11,17
  have eq26 : sK0 ≠ sK0 := superpose eq22 eq13 -- superposition 13,22
  subsumption eq26 rfl

theorem Equation14_4512_implies_Equation464 (G : Type*) [Magma G]
    (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation464 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := mod_symm (h14 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq26 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq25 eq13 -- backward demodulation 13,25
  subsumption eq26 eq11

theorem Equation464_4512_implies_Equation481 (G : Type*) [Magma G]
    (h464 : Equation464 G) (h4512 : Equation4512 G) : Equation481 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h464 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq23 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq16 eq12 -- superposition 12,16
  have eq24 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))))) = X2 := superpose eq11 eq12 -- superposition 12,11
  have eq26 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq12 eq11 -- superposition 11,12
  have eq31 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2))) := superpose eq12 eq20 -- forward demodulation 20,12
  have eq32 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq12 eq31 -- forward demodulation 31,12
  have eq33 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq12 eq32 -- forward demodulation 32,12
  have eq37 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))))) := superpose eq12 eq26 -- forward demodulation 26,12
  have eq38 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))))) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq23 eq12 -- superposition 12,23
  have eq50 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq46 -- forward demodulation 46,12
  have eq52 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq11 -- backward demodulation 11,50
  have eq53 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X2 := superpose eq50 eq24 -- backward demodulation 24,50
  have eq54 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq50 eq33 -- backward demodulation 33,50
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq54 eq38 -- backward demodulation 38,54
  have eq59 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq54 eq58 -- forward demodulation 58,54
  have eq60 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq59 eq53 -- backward demodulation 53,59
  have eq76 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq60 eq52 -- superposition 52,60
  have eq197 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq12 eq76 -- superposition 76,12
  have eq211 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq197 eq13 -- backward demodulation 13,197
  subsumption eq211 eq52

theorem Equation481_4512_implies_Equation489 (G : Type*) [Magma G]
    (h481 : Equation481 G) (h4512 : Equation4512 G) : Equation489 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h481 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq30 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X3))))) = X2 := superpose eq11 eq12 -- superposition 12,11
  have eq37 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) := superpose eq12 eq11 -- superposition 11,12
  have eq44 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X3)))))) = X2 := superpose eq12 eq30 -- forward demodulation 30,12
  have eq45 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq37 eq44 -- backward demodulation 44,37
  have eq48 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq45 eq13 -- backward demodulation 13,45
  subsumption eq48 eq45

theorem Equation489_4512_implies_Equation492 (G : Type*) [Magma G]
    (h489 : Equation489 G) (h4512 : Equation4512 G) : Equation492 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h489 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq15 eq12 -- superposition 12,15
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq15 eq26 -- superposition 26,15
  have eq74 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := superpose eq57 eq13 -- backward demodulation 13,57
  have eq75 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq15 eq74 -- forward demodulation 74,15
  subsumption eq75 eq15

theorem Equation492_4512_implies_Equation508 (G : Type*) [Magma G]
    (h492 : Equation492 G) (h4512 : Equation4512 G) : Equation508 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h492 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) = X2 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = (X1 ◇ X0) := superpose eq11 eq16 -- superposition 16,11
  have eq22 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq11 -- backward demodulation 11,17
  have eq48 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X3 ◇ (X3 ◇ (X2 ◇ X1))) ◇ X2) := superpose eq15 eq15 -- superposition 15,15
  have eq49 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X1) = X0 := superpose eq22 eq15 -- superposition 15,22
  have eq50 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq16 eq15 -- superposition 15,16
  have eq64 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq49 eq48 -- backward demodulation 48,49
  have eq79 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq12 eq50 -- superposition 50,12
  have eq86 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq79 eq13 -- backward demodulation 13,79
  subsumption eq86 eq64

theorem Equation508_4512_implies_Equation522 (G : Type*) [Magma G]
    (h508 : Equation508 G) (h4512 : Equation4512 G) : Equation522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h508 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X2 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X2 : G) : (X2 ◇ (X2 ◇ X0)) = X0 := superpose eq15 eq14 -- backward demodulation 14,15
  have eq22 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := superpose eq12 eq15 -- superposition 15,12
  have eq68 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq16 eq22 -- superposition 22,16
  have eq93 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq68 eq13 -- backward demodulation 13,68
  subsumption eq93 eq16

theorem Equation522_4512_implies_Equation543 (G : Type*) [Magma G]
    (h522 : Equation522 G) (h4512 : Equation4512 G) : Equation543 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h522 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq16 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = (X2 ◇ X0) := superpose eq11 eq16 -- superposition 16,11
  have eq24 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq44 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq12 eq24 -- superposition 24,12
  have eq56 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq44 eq13 -- backward demodulation 13,44
  subsumption eq56 eq24

theorem Equation543_4512_implies_Equation546 (G : Type*) [Magma G]
    (h543 : Equation543 G) (h4512 : Equation4512 G) : Equation546 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h543 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq23 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))))) = X3 := superpose eq11 eq12 -- superposition 12,11
  have eq25 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq12 eq11 -- superposition 11,12
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))))) = X3 := superpose eq12 eq23 -- forward demodulation 23,12
  have eq34 (X0 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X3 := superpose eq25 eq33 -- backward demodulation 33,25
  have eq43 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq34 eq12 -- superposition 12,34
  have eq49 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq12 eq43 -- forward demodulation 43,12
  have eq50 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq49 eq13 -- backward demodulation 13,49
  subsumption eq50 eq34

theorem Equation546_4512_implies_Equation556 (G : Type*) [Magma G]
    (h546 : Equation546 G) (h4512 : Equation4512 G) : Equation556 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h546 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq16 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq11 eq11 -- superposition 11,11
  have eq24 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq16 eq12 -- superposition 12,16
  have eq43 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq24 eq11 -- superposition 11,24
  have eq44 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq24 eq11 -- superposition 11,24
  have eq95 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq11 eq43 -- superposition 43,11
  have eq182 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := superpose eq12 eq44 -- superposition 44,12
  have eq214 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := superpose eq182 eq13 -- backward demodulation 13,182
  have eq215 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq95 eq214 -- forward demodulation 214,95
  subsumption eq215 eq43

theorem Equation556_4512_implies_Equation572 (G : Type*) [Magma G]
    (h556 : Equation556 G) (h4512 : Equation4512 G) : Equation572 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h556 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := superpose eq16 eq11 -- superposition 11,16
  have eq33 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := superpose eq16 eq12 -- superposition 12,16
  have eq47 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := superpose eq33 eq13 -- backward demodulation 13,33
  subsumption eq47 eq22


/- Equivalence of [16, 466, 473, 500, 528, 562, 575] -/
theorem Equation575_4512_implies_Equation16 (G : Type*) [Magma G]
    (h575 : Equation575 G) (h4512 : Equation4512 G) : Equation16 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h575 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X3 ◇ (X3 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq34 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = ((X0 ◇ X1) ◇ (X4 ◇ (X4 ◇ X2))) := superpose eq12 eq14 -- superposition 14,12
  have eq49 (X1 X2 X3 X4 X5 : G) : (X4 ◇ (X4 ◇ (X5 ◇ (X1 ◇ X2)))) = (X5 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X2)))) := superpose eq14 eq14 -- superposition 14,14
  have eq51 (X0 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X2)))) = X2 := superpose eq11 eq14 -- superposition 14,11
  have eq127 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = ((X3 ◇ X0) ◇ (X4 ◇ (X4 ◇ (X3 ◇ X2)))) := superpose eq51 eq18 -- superposition 18,51
  have eq130 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X3 ◇ (X3 ◇ X2))) := superpose eq11 eq18 -- superposition 18,11
  have eq131 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ (X4 ◇ (X4 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X2)))))) := superpose eq14 eq18 -- superposition 18,14
  have eq188 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq130 eq34 -- backward demodulation 34,130
  have eq191 (X1 X2 X3 X5 : G) : (X5 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X2)))) = (X1 ◇ (X5 ◇ X2)) := superpose eq188 eq49 -- backward demodulation 49,188
  have eq207 (X0 X1 X2 X4 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ (X4 ◇ (X4 ◇ (X0 ◇ X2)))) := superpose eq191 eq131 -- forward demodulation 131,191
  have eq208 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq207 eq127 -- backward demodulation 127,207
  have eq210 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq208 eq14 -- backward demodulation 14,208
  have eq217 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq210 eq11 -- backward demodulation 11,210
  have eq285 : sK0 ≠ sK0 := superpose eq217 eq13 -- superposition 13,217
  subsumption eq285 rfl

theorem Equation16_4512_implies_Equation466 (G : Type*) [Magma G]
    (h16 : Equation16 G) (_ : Equation4512 G) : Equation466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h16 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq14 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation466_4512_implies_Equation473 (G : Type*) [Magma G]
    (h466 : Equation466 G) (h4512 : Equation4512 G) : Equation473 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h466 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq16 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1))))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq17 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)))))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq18 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))))))) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq19 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))))))) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))))))) := superpose eq12 eq19 -- forward demodulation 19,12
  have eq23 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))))) = X2 := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq33 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))))) = X2 := superpose eq12 eq23 -- forward demodulation 23,12
  have eq34 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq33 eq20 -- backward demodulation 20,33
  have eq48 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq11 eq24 -- superposition 24,11
  have eq106 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq48 -- superposition 48,12
  have eq114 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq106 eq34 -- backward demodulation 34,106
  have eq116 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq114 eq11 -- backward demodulation 11,114
  have eq121 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := superpose eq116 eq33 -- backward demodulation 33,116
  have eq241 : sK0 ≠ sK0 := superpose eq121 eq13 -- superposition 13,121
  subsumption eq241 rfl

theorem Equation473_4512_implies_Equation500 (G : Type*) [Magma G]
    (h473 : Equation473 G) (h4512 : Equation4512 G) : Equation500 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h473 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2)))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq38 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq11 eq18 -- superposition 18,11
  have eq67 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq38 -- superposition 38,12
  have eq75 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq67 eq13 -- backward demodulation 13,67
  have eq103 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) = X1 := superpose eq11 eq23 -- superposition 23,11
  have eq113 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = (X3 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))))) := superpose eq12 eq23 -- superposition 23,12
  have eq119 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq23 eq18 -- superposition 18,23
  have eq132 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))))) := superpose eq12 eq113 -- forward demodulation 113,12
  have eq133 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))))) := superpose eq12 eq132 -- forward demodulation 132,12
  have eq134 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X2)))) := superpose eq103 eq133 -- forward demodulation 133,103
  have eq142 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq134 eq18 -- backward demodulation 18,134
  have eq154 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq142 eq119 -- forward demodulation 119,142
  have eq175 : sK0 ≠ sK0 := superpose eq154 eq75 -- superposition 75,154
  subsumption eq175 rfl

theorem Equation500_4512_implies_Equation528 (G : Type*) [Magma G]
    (h500 : Equation500 G) (_ : Equation4512 G) : Equation528 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h500 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq15 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq14 eq13 -- backward demodulation 13,14
  subsumption eq15 eq11

theorem Equation528_4512_implies_Equation562 (G : Type*) [Magma G]
    (h528 : Equation528 G) (h4512 : Equation4512 G) : Equation562 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h528 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X3 ◇ (X3 ◇ (X0 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X3))))) = X3 := superpose eq11 eq12 -- superposition 12,11
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3))))) = X3 := superpose eq12 eq11 -- superposition 11,12
  have eq28 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))))) = X3 := superpose eq12 eq18 -- forward demodulation 18,12
  have eq229 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))))) = X2 := superpose eq14 eq22 -- superposition 22,14
  have eq277 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) = X2 := superpose eq12 eq229 -- forward demodulation 229,12
  have eq278 (X2 X3 : G) : (X3 ◇ (X3 ◇ X2)) = X2 := superpose eq11 eq277 -- forward demodulation 277,11
  have eq283 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3)))) = X3 := superpose eq278 eq28 -- backward demodulation 28,278
  have eq393 : sK0 ≠ sK0 := superpose eq283 eq13 -- superposition 13,283
  subsumption eq393 rfl

theorem Equation562_4512_implies_Equation575 (G : Type*) [Magma G]
    (h562 : Equation562 G) (h4512 : Equation4512 G) : Equation575 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := mod_symm (h562 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))))) = X3 := superpose eq11 eq12 -- superposition 12,11
  have eq27 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) = X3 := superpose eq12 eq17 -- forward demodulation 17,12
  have eq155 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq11 eq27 -- superposition 27,11
  have eq220 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq155 eq11 -- backward demodulation 11,155
  have eq229 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq220 eq13 -- backward demodulation 13,220
  subsumption eq229 eq220


/- Equivalence of [38, 42, 322, 324, 328, 330, 331, 3305, 3307, 3310, 3311, 3313, 3314, 3325, 3327, 3328, 3329, 3332, 3333, 3335, 3336, 3337, 3339, 3340, 3341] -/
theorem Equation3341_4512_implies_Equation38 (G : Type*) [Magma G]
    (h3341 : Equation3341 G) (_ : Equation4512 G) : Equation38 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X3 ◇ X4))) := mod_symm (h3341 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq20 (X0 X4 X5 : G) : (X0 ◇ X4) = (X0 ◇ X5) := superpose eq11 eq11 -- superposition 11,11
  have eq30 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq20 eq13 -- superposition 13,20
  subsumption eq30 eq20

theorem Equation38_4512_implies_Equation42 (G : Type*) [Magma G]
    (h38 : Equation38 G) (_ : Equation4512 G) : Equation42 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := mod_symm (h38 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK2) := mod_symm nh
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation42_4512_implies_Equation322 (G : Type*) [Magma G]
    (h42 : Equation42 G) (_ : Equation4512 G) : Equation322 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := mod_symm (h42 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation322_4512_implies_Equation324 (G : Type*) [Magma G]
    (h322 : Equation322 G) (_ : Equation4512 G) : Equation324 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h322 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq15 eq11

theorem Equation324_4512_implies_Equation328 (G : Type*) [Magma G]
    (h324 : Equation324 G) (_ : Equation4512 G) : Equation328 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X2)) := mod_symm (h324 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq11

theorem Equation328_4512_implies_Equation330 (G : Type*) [Magma G]
    (h328 : Equation328 G) (_ : Equation4512 G) : Equation330 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X0)) := mod_symm (h328 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq11

theorem Equation330_4512_implies_Equation331 (G : Type*) [Magma G]
    (h330 : Equation330 G) (_ : Equation4512 G) : Equation331 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X2)) := mod_symm (h330 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq11

theorem Equation331_4512_implies_Equation3305 (G : Type*) [Magma G]
    (h331 : Equation331 G) (_ : Equation4512 G) : Equation3305 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X3)) := mod_symm (h331 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3305_4512_implies_Equation3307 (G : Type*) [Magma G]
    (h3305 : Equation3305 G) (_ : Equation4512 G) : Equation3307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h3305 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq15 eq11

theorem Equation3307_4512_implies_Equation3310 (G : Type*) [Magma G]
    (h3307 : Equation3307 G) (_ : Equation4512 G) : Equation3310 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := mod_symm (h3307 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq22 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq11

theorem Equation3310_4512_implies_Equation3311 (G : Type*) [Magma G]
    (h3310 : Equation3310 G) (h4512 : Equation4512 G) : Equation3311 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := mod_symm (h3310 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK2) := superpose eq11 eq13 -- superposition 13,11
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = ((X0 ◇ X1) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq25 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq26 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq25 -- forward demodulation 25,12
  have eq27 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X3)) := superpose eq11 eq26 -- forward demodulation 26,11
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq27 eq11 -- backward demodulation 11,27
  have eq47 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq29 eq15 -- superposition 15,29
  have eq52 : (sK0 ◇ sK2) ≠ (sK0 ◇ sK0) := superpose eq47 eq16 -- backward demodulation 16,47
  subsumption eq52 eq47

theorem Equation3311_4512_implies_Equation3313 (G : Type*) [Magma G]
    (h3311 : Equation3311 G) (_ : Equation4512 G) : Equation3313 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h3311 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq21 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (X0 ◇ sK0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq11

theorem Equation3313_4512_implies_Equation3314 (G : Type*) [Magma G]
    (h3313 : Equation3313 G) (_ : Equation4512 G) : Equation3314 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X2 ◇ X2))) := mod_symm (h3313 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (X0 ◇ X0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq11

theorem Equation3314_4512_implies_Equation3325 (G : Type*) [Magma G]
    (h3314 : Equation3314 G) (_ : Equation4512 G) : Equation3325 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X2 ◇ X3))) := mod_symm (h3314 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq22 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (X0 ◇ X1))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq11

theorem Equation3325_4512_implies_Equation3327 (G : Type*) [Magma G]
    (h3325 : Equation3325 G) (_ : Equation4512 G) : Equation3327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X0))) := mod_symm (h3325 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq11

theorem Equation3327_4512_implies_Equation3328 (G : Type*) [Magma G]
    (h3327 : Equation3327 G) (_ : Equation4512 G) : Equation3328 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X2))) := mod_symm (h3327 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK3))) := mod_symm nh
  have eq21 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ (sK0 ◇ X0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq11

theorem Equation3328_4512_implies_Equation3329 (G : Type*) [Magma G]
    (h3328 : Equation3328 G) (_ : Equation4512 G) : Equation3329 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X3))) := mod_symm (h3328 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq22 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ (sK0 ◇ X1))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq11

theorem Equation3329_4512_implies_Equation3332 (G : Type*) [Magma G]
    (h3329 : Equation3329 G) (h4512 : Equation4512 G) : Equation3332 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X0))) := mod_symm (h3329 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK3))) := mod_symm nh
  have eq20 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) := superpose eq11 eq12 -- superposition 12,11
  have eq21 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ X3)) := superpose eq12 eq20 -- forward demodulation 20,12
  have eq30 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ (X3 ◇ X0))) := superpose eq21 eq29 -- backward demodulation 29,21
  have eq31 (X0 X1 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X1 ◇ X3)) := superpose eq11 eq30 -- forward demodulation 30,11
  have eq35 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X0)) := superpose eq31 eq11 -- backward demodulation 11,31
  have eq37 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK3)) := superpose eq31 eq13 -- backward demodulation 13,31
  have eq57 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq35 eq37 -- superposition 37,35
  subsumption eq57 eq35

theorem Equation3332_4512_implies_Equation3333 (G : Type*) [Magma G]
    (h3332 : Equation3332 G) (_ : Equation4512 G) : Equation3333 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := mod_symm (h3332 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq15 (X0 X1 X2 X4 : G) : (X4 ◇ X1) = (X4 ◇ (X0 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11
  have eq45 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ X1)) := superpose eq15 eq13 -- superposition 13,15
  subsumption eq45 eq15

theorem Equation3333_4512_implies_Equation3335 (G : Type*) [Magma G]
    (h3333 : Equation3333 G) (_ : Equation4512 G) : Equation3335 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X2 ◇ X0))) := mod_symm (h3333 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq22 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ (X0 ◇ sK0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq11

theorem Equation3335_4512_implies_Equation3336 (G : Type*) [Magma G]
    (h3335 : Equation3335 G) (_ : Equation4512 G) : Equation3336 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X2 ◇ X2))) := mod_symm (h3335 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq21 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq11

theorem Equation3336_4512_implies_Equation3337 (G : Type*) [Magma G]
    (h3336 : Equation3336 G) (_ : Equation4512 G) : Equation3337 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X2 ◇ X3))) := mod_symm (h3336 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq22 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq11

theorem Equation3337_4512_implies_Equation3339 (G : Type*) [Magma G]
    (h3337 : Equation3337 G) (_ : Equation4512 G) : Equation3339 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X3 ◇ X0))) := mod_symm (h3337 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK2))) := mod_symm nh
  have eq22 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq11

theorem Equation3339_4512_implies_Equation3340 (G : Type*) [Magma G]
    (h3339 : Equation3339 G) (_ : Equation4512 G) : Equation3340 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X3 ◇ X2))) := mod_symm (h3339 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK3))) := mod_symm nh
  have eq22 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq11

theorem Equation3340_4512_implies_Equation3341 (G : Type*) [Magma G]
    (h3340 : Equation3340 G) (_ : Equation4512 G) : Equation3341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X3 ◇ X3))) := mod_symm (h3340 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := mod_symm nh
  have eq22 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq11


/- Equivalence of [39, 45, 336, 339, 347, 351, 355, 3349, 3356, 3359, 3367, 3371, 3375, 3384, 3392, 3401, 3405, 3409, 3418, 3422, 3426, 3436, 3441, 3446, 3451] -/
theorem Equation3451_4512_implies_Equation39 (G : Type*) [Magma G]
    (h3451 : Equation3451 G) (_ : Equation4512 G) : Equation39 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ X1))) := mod_symm (h3451 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq20 (X3 X4 X5 : G) : (X4 ◇ X3) = (X5 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq30 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq20 eq13 -- superposition 13,20
  subsumption eq30 eq20

theorem Equation39_4512_implies_Equation45 (G : Type*) [Magma G]
    (h39 : Equation39 G) (_ : Equation4512 G) : Equation45 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := mod_symm (h39 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK1) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq15 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq15 eq14

theorem Equation45_4512_implies_Equation336 (G : Type*) [Magma G]
    (h45 : Equation45 G) (h4512 : Equation4512 G) : Equation336 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := mod_symm (h45 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- superposition 13,11
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq56 (X1 : G) : (sK0 ◇ sK1) ≠ (X1 ◇ sK1) := superpose eq29 eq20 -- superposition 20,29
  subsumption eq56 eq11

theorem Equation336_4512_implies_Equation339 (G : Type*) [Magma G]
    (h336 : Equation336 G) (_ : Equation4512 G) : Equation339 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X1)) := mod_symm (h336 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq23 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq14 eq13 -- superposition 13,14
  have eq56 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq11 eq23 -- superposition 23,11
  subsumption eq56 eq14

theorem Equation339_4512_implies_Equation347 (G : Type*) [Magma G]
    (h339 : Equation339 G) (_ : Equation4512 G) : Equation347 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X1)) := mod_symm (h339 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X1 ◇ X0)) := superpose eq11 eq17 -- superposition 17,11
  have eq26 (X0 : G) : (sK0 ◇ sK1) ≠ (sK2 ◇ (X0 ◇ sK1)) := superpose eq17 eq13 -- superposition 13,17
  subsumption eq26 eq21

theorem Equation347_4512_implies_Equation351 (G : Type*) [Magma G]
    (h347 : Equation347 G) (h4512 : Equation4512 G) : Equation351 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ X1)) := mod_symm (h347 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq17 (X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ X1) := superpose eq11 eq11 -- superposition 11,11
  have eq29 (X0 : G) : (sK0 ◇ sK1) ≠ (sK2 ◇ (X0 ◇ sK1)) := superpose eq17 eq13 -- superposition 13,17
  have eq47 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq11 eq12 -- superposition 12,11
  have eq55 (X1 : G) : (sK0 ◇ sK1) ≠ (sK2 ◇ (X1 ◇ (sK1 ◇ sK1))) := superpose eq11 eq29 -- superposition 29,11
  subsumption eq55 eq47

theorem Equation351_4512_implies_Equation355 (G : Type*) [Magma G]
    (h351 : Equation351 G) (_ : Equation4512 G) : Equation355 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ X1)) := mod_symm (h351 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ sK1)) := mod_symm nh
  have eq18 (X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ X1) := superpose eq11 eq11 -- superposition 11,11
  have eq23 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X0 ◇ X1)) := superpose eq11 eq18 -- superposition 18,11
  have eq28 (X0 : G) : (sK0 ◇ sK1) ≠ (sK2 ◇ (X0 ◇ sK1)) := superpose eq18 eq13 -- superposition 13,18
  subsumption eq28 eq23

theorem Equation355_4512_implies_Equation3349 (G : Type*) [Magma G]
    (h355 : Equation355 G) (_ : Equation4512 G) : Equation3349 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ X1)) := mod_symm (h355 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq11

theorem Equation3349_4512_implies_Equation3356 (G : Type*) [Magma G]
    (h3349 : Equation3349 G) (h4512 : Equation4512 G) : Equation3356 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h3349 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq16 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq11 eq13 -- superposition 13,11
  have eq20 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq11 -- superposition 11,12
  have eq29 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = (X0 ◇ X3) := superpose eq20 eq21 -- forward demodulation 21,20
  have eq30 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X2) := superpose eq29 eq12 -- backward demodulation 12,29
  have eq31 (X1 X2 X3 : G) : (X3 ◇ X2) = (X2 ◇ (X3 ◇ (X1 ◇ X2))) := superpose eq30 eq20 -- backward demodulation 20,30
  have eq38 (X2 X3 : G) : (X3 ◇ X2) = (X2 ◇ (X3 ◇ X2)) := superpose eq30 eq31 -- forward demodulation 31,30
  have eq60 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq30 eq38 -- superposition 38,30
  have eq69 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq60 eq60 -- superposition 60,60
  have eq77 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq60 eq16 -- superposition 16,60
  subsumption eq77 eq69

theorem Equation3356_4512_implies_Equation3359 (G : Type*) [Magma G]
    (h3356 : Equation3356 G) (h4512 : Equation4512 G) : Equation3359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := mod_symm (h3356 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq42 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ X2) := superpose eq14 eq12 -- superposition 12,14
  have eq91 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq42 eq13 -- superposition 13,42
  subsumption eq91 eq42

theorem Equation3359_4512_implies_Equation3367 (G : Type*) [Magma G]
    (h3359 : Equation3359 G) (h4512 : Equation4512 G) : Equation3367 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := mod_symm (h3359 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq17 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq47 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ X2) := superpose eq17 eq12 -- superposition 12,17
  have eq92 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq47 eq13 -- superposition 13,47
  subsumption eq92 eq47

theorem Equation3367_4512_implies_Equation3371 (G : Type*) [Magma G]
    (h3367 : Equation3367 G) (h4512 : Equation4512 G) : Equation3371 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X1 ◇ X1))) := mod_symm (h3367 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq17 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq47 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ X2) := superpose eq17 eq12 -- superposition 12,17
  have eq92 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK2 ◇ sK1)) := superpose eq47 eq13 -- superposition 13,47
  subsumption eq92 eq47

theorem Equation3371_4512_implies_Equation3375 (G : Type*) [Magma G]
    (h3371 : Equation3371 G) (_ : Equation4512 G) : Equation3375 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X2 ◇ X1))) := mod_symm (h3371 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1))) := mod_symm nh
  have eq18 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq27 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq18 eq11 -- superposition 11,18
  have eq32 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (X0 ◇ (sK3 ◇ sK1))) := superpose eq18 eq13 -- superposition 13,18
  subsumption eq32 eq27

theorem Equation3375_4512_implies_Equation3384 (G : Type*) [Magma G]
    (h3375 : Equation3375 G) (_ : Equation4512 G) : Equation3384 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := mod_symm (h3375 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq19 (X0 X3 X4 : G) : (X3 ◇ X0) = (X4 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq24 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X0) = (X4 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq11 eq19 -- superposition 19,11
  have eq33 (X0 : G) : (sK0 ◇ sK1) ≠ (sK2 ◇ (X0 ◇ (sK1 ◇ sK1))) := superpose eq19 eq13 -- superposition 13,19
  subsumption eq33 eq24

theorem Equation3384_4512_implies_Equation3392 (G : Type*) [Magma G]
    (h3384 : Equation3384 G) (h4512 : Equation4512 G) : Equation3392 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h3384 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK3 ◇ sK1))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq18 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq17 -- forward demodulation 17,11
  have eq19 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ X1)) := superpose eq18 eq11 -- backward demodulation 11,18
  have eq23 (X1 X2 X3 : G) : (X3 ◇ X1) = (X2 ◇ X1) := superpose eq19 eq19 -- superposition 19,19
  have eq48 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ X2) := superpose eq12 eq23 -- superposition 23,12
  have eq120 (X0 : G) : (sK0 ◇ sK1) ≠ (sK2 ◇ (X0 ◇ sK1)) := superpose eq48 eq13 -- superposition 13,48
  subsumption eq120 eq48

theorem Equation3392_4512_implies_Equation3401 (G : Type*) [Magma G]
    (h3392 : Equation3392 G) (h4512 : Equation4512 G) : Equation3401 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X3 ◇ X1))) := mod_symm (h3392 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq20 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X4) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) := superpose eq11 eq12 -- superposition 12,11
  have eq26 (X0 X2 X4 : G) : (X2 ◇ X4) = (X0 ◇ (X2 ◇ X4)) := superpose eq11 eq20 -- forward demodulation 20,11
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ X1)) := superpose eq26 eq11 -- backward demodulation 11,26
  have eq30 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ sK1)) := superpose eq26 eq13 -- backward demodulation 13,26
  subsumption eq30 eq29

theorem Equation3401_4512_implies_Equation3405 (G : Type*) [Magma G]
    (h3401 : Equation3401 G) (h4512 : Equation4512 G) : Equation3405 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ (X1 ◇ X1))) := mod_symm (h3401 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq17 (X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ X1) := superpose eq11 eq11 -- superposition 11,11
  have eq56 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ X2) := superpose eq17 eq12 -- superposition 12,17
  have eq101 (X0 : G) : (sK0 ◇ sK1) ≠ (sK2 ◇ (X0 ◇ sK1)) := superpose eq56 eq13 -- superposition 13,56
  subsumption eq101 eq56

theorem Equation3405_4512_implies_Equation3409 (G : Type*) [Magma G]
    (h3405 : Equation3405 G) (_ : Equation4512 G) : Equation3409 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ (X2 ◇ X1))) := mod_symm (h3405 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK1))) := mod_symm nh
  have eq17 (X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ X1) := superpose eq11 eq11 -- superposition 11,11
  have eq23 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq11 eq17 -- superposition 17,11
  have eq33 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK1 ◇ (sK3 ◇ sK1))) := superpose eq17 eq13 -- superposition 13,17
  subsumption eq33 eq23

theorem Equation3409_4512_implies_Equation3418 (G : Type*) [Magma G]
    (h3409 : Equation3409 G) (h4512 : Equation4512 G) : Equation3418 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ (X3 ◇ X1))) := mod_symm (h3409 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq19 (X1 X3 X4 : G) : (X3 ◇ X1) = (X4 ◇ X1) := superpose eq11 eq11 -- superposition 11,11
  have eq54 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ X2) := superpose eq19 eq12 -- superposition 12,19
  have eq95 (X0 : G) : (sK0 ◇ sK1) ≠ (sK2 ◇ (X0 ◇ sK1)) := superpose eq54 eq13 -- superposition 13,54
  subsumption eq95 eq54

theorem Equation3418_4512_implies_Equation3422 (G : Type*) [Magma G]
    (h3418 : Equation3418 G) (h4512 : Equation4512 G) : Equation3422 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X1 ◇ X1))) := mod_symm (h3418 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq17 (X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ X1) := superpose eq11 eq11 -- superposition 11,11
  have eq46 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ X2) := superpose eq17 eq12 -- superposition 12,17
  have eq82 (X0 : G) : (sK0 ◇ sK1) ≠ (sK2 ◇ (X0 ◇ sK1)) := superpose eq46 eq13 -- superposition 13,46
  subsumption eq82 eq46

theorem Equation3422_4512_implies_Equation3426 (G : Type*) [Magma G]
    (h3422 : Equation3422 G) (h4512 : Equation4512 G) : Equation3426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X2 ◇ X1))) := mod_symm (h3422 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK1))) := mod_symm nh
  have eq20 (X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ X1) := superpose eq11 eq11 -- superposition 11,11
  have eq49 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ X2) := superpose eq20 eq12 -- superposition 12,20
  have eq97 (X0 : G) : (sK0 ◇ sK1) ≠ (sK2 ◇ (X0 ◇ sK1)) := superpose eq49 eq13 -- superposition 13,49
  subsumption eq97 eq49

theorem Equation3426_4512_implies_Equation3436 (G : Type*) [Magma G]
    (h3426 : Equation3426 G) (_ : Equation4512 G) : Equation3436 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X3 ◇ X1))) := mod_symm (h3426 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq20 (X2 X3 X4 : G) : (X3 ◇ X2) = (X4 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq25 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq11 eq20 -- superposition 20,11
  have eq34 (X0 : G) : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (X0 ◇ sK1))) := superpose eq20 eq13 -- superposition 13,20
  subsumption eq34 eq25

theorem Equation3436_4512_implies_Equation3441 (G : Type*) [Magma G]
    (h3436 : Equation3436 G) (h4512 : Equation4512 G) : Equation3441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ X1))) := mod_symm (h3436 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq19 (X2 X3 X4 : G) : (X3 ◇ X2) = (X4 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq53 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ X2) := superpose eq19 eq12 -- superposition 12,19
  have eq95 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK2 ◇ sK1)) := superpose eq53 eq13 -- superposition 13,53
  subsumption eq95 eq53

theorem Equation3441_4512_implies_Equation3446 (G : Type*) [Magma G]
    (h3441 : Equation3441 G) (_ : Equation4512 G) : Equation3446 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X2 ◇ X1))) := mod_symm (h3441 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK1))) := mod_symm nh
  have eq20 (X2 X3 X4 : G) : (X3 ◇ X2) = (X4 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq25 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X2) = (X4 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq11 eq20 -- superposition 20,11
  have eq30 (X0 : G) : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (X0 ◇ sK1))) := superpose eq20 eq13 -- superposition 13,20
  subsumption eq30 eq25

theorem Equation3446_4512_implies_Equation3451 (G : Type*) [Magma G]
    (h3446 : Equation3446 G) (_ : Equation4512 G) : Equation3451 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X3 ◇ X1))) := mod_symm (h3446 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1))) := mod_symm nh
  have eq20 (X2 X3 X4 : G) : (X3 ◇ X2) = (X4 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq30 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = (X4 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq20 eq11 -- superposition 11,20
  have eq34 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK3 ◇ (sK4 ◇ sK1))) := superpose eq20 eq13 -- superposition 13,20
  subsumption eq34 eq30


/- Equivalence of [40, 3269, 3282, 3286, 3294, 3297] -/
theorem Equation3297_4512_implies_Equation40 (G : Type*) [Magma G]
    (h3297 : Equation3297 G) (_ : Equation4512 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X2 ◇ X1))) := mod_symm (h3297 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq18 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq25 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq18 eq13 -- superposition 13,18
  subsumption eq25 eq18

theorem Equation40_4512_implies_Equation3269 (G : Type*) [Magma G]
    (h40 : Equation40 G) (h4512 : Equation4512 G) : Equation3269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := mod_symm (h40 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq18 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq21 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq11 eq12 -- superposition 12,11
  have eq39 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := superpose eq12 eq18 -- superposition 18,12
  have eq69 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq18 eq21 -- superposition 21,18
  have eq92 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq12 eq69 -- forward demodulation 69,12
  have eq331 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ (X0 ◇ sK1))) := superpose eq39 eq13 -- superposition 13,39
  subsumption eq331 eq92

theorem Equation3269_4512_implies_Equation3282 (G : Type*) [Magma G]
    (h3269 : Equation3269 G) (h4512 : Equation4512 G) : Equation3282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := mod_symm (h3269 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq11 eq13 -- superposition 13,11
  have eq17 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = ((X1 ◇ X1) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq19 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq11 eq12 -- superposition 12,11
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = (X1 ◇ (X1 ◇ X2)) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq40 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq11 eq14 -- superposition 14,11
  have eq55 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1))) := superpose eq14 eq11 -- superposition 11,14
  have eq57 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq12 eq40 -- forward demodulation 40,12
  have eq58 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq12 eq57 -- forward demodulation 57,12
  have eq59 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq12 eq58 -- forward demodulation 58,12
  have eq60 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq12 eq59 -- forward demodulation 59,12
  have eq61 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X1))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq11 eq60 -- forward demodulation 60,11
  have eq62 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq11 eq61 -- forward demodulation 61,11
  have eq107 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq12 eq55 -- forward demodulation 55,12
  have eq108 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq12 eq107 -- forward demodulation 107,12
  have eq109 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq62 eq108 -- forward demodulation 108,62
  have eq118 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)))) := superpose eq14 eq19 -- superposition 19,14
  have eq126 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X1)) := superpose eq19 eq11 -- superposition 11,19
  have eq145 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1))))) := superpose eq12 eq118 -- forward demodulation 118,12
  have eq146 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1)))))) := superpose eq12 eq145 -- forward demodulation 145,12
  have eq147 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))) := superpose eq12 eq146 -- forward demodulation 146,12
  have eq148 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq25 eq147 -- forward demodulation 147,25
  have eq149 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq25 eq148 -- forward demodulation 148,25
  have eq150 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq109 eq149 -- forward demodulation 149,109
  have eq167 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq150 eq126 -- forward demodulation 126,150
  have eq622 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq167 eq167 -- superposition 167,167
  have eq760 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq622 eq16 -- superposition 16,622
  subsumption eq760 eq622

theorem Equation3282_4512_implies_Equation3286 (G : Type*) [Magma G]
    (h3282 : Equation3282 G) (_ : Equation4512 G) : Equation3286 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := mod_symm (h3282 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq23 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (X0 ◇ X0))) := superpose eq16 eq13 -- superposition 13,16
  have eq56 (X1 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq11 eq23 -- superposition 23,11
  subsumption eq56 eq15

theorem Equation3286_4512_implies_Equation3294 (G : Type*) [Magma G]
    (h3286 : Equation3286 G) (h4512 : Equation4512 G) : Equation3294 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X2))) := mod_symm (h3286 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq18 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq36 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq18 eq12 -- superposition 12,18
  have eq420 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq36 eq13 -- superposition 13,36
  subsumption eq420 eq18

theorem Equation3294_4512_implies_Equation3297 (G : Type*) [Magma G]
    (h3294 : Equation3294 G) (h4512 : Equation4512 G) : Equation3297 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := mod_symm (h3294 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq17 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq30 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ X2) := superpose eq17 eq12 -- superposition 12,17
  have eq181 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq30 -- superposition 30,12
  have eq194 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq30 eq11 -- superposition 11,30
  have eq233 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq12 eq194 -- forward demodulation 194,12
  have eq1906 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ (X0 ◇ sK1))) := superpose eq181 eq13 -- superposition 13,181
  subsumption eq1906 eq233


/- Equivalence of [41, 44, 46, 334, 337, 338, 340, 341, 342, 344, 345, 346, 348, 349, 350, 352, 353, 354, 356, 357, 358, 3344, 3347, 3348, 3351, 3354, 3357, 3358, 3360, 3361, 3362, 3365, 3366, 3368, 3369, 3372, 3373, 3374, 3376, 3377, 3378, 3379, 3381, 3382, 3383, 3386, 3387, 3389, 3390, 3391, 3393, 3394, 3395, 3396, 3399, 3400, 3402, 3403, 3406, 3407, 3408, 3410, 3411, 3412, 3413, 3415, 3416, 3419, 3420, 3421, 3423, 3424, 3425, 3427, 3428, 3429, 3430, 3432, 3433, 3434, 3435, 3437, 3438, 3439, 3440, 3442, 3443, 3444, 3445, 3447, 3448, 3449, 3450, 3452, 3453, 3454, 3455] -/
theorem Equation3455_4512_implies_Equation41 (G : Type*) [Magma G]
    (h3455 : Equation3455 G) (_ : Equation4512 G) : Equation41 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ X5))) := mod_symm (h3455 ..)
  have eq13 : (sK1 ◇ sK2) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq20 (X4 X5 X6 X7 : G) : (X4 ◇ X5) = (X6 ◇ X7) := superpose eq11 eq11 -- superposition 11,11
  have eq30 (X0 X1 : G) : (X0 ◇ X1) ≠ (sK0 ◇ sK0) := superpose eq20 eq13 -- superposition 13,20
  subsumption eq30 eq20

theorem Equation41_4512_implies_Equation44 (G : Type*) [Magma G]
    (h41 : Equation41 G) (_ : Equation4512 G) : Equation44 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ X2) := mod_symm (h41 ..)
  have eq13 : (sK1 ◇ sK2) ≠ (sK0 ◇ sK1) := mod_symm nh
  have eq18 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK1) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq18 eq11

theorem Equation44_4512_implies_Equation46 (G : Type*) [Magma G]
    (h44 : Equation44 G) (_ : Equation4512 G) : Equation46 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ X2) := mod_symm (h44 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK3) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK2) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq18 eq14

theorem Equation46_4512_implies_Equation334 (G : Type*) [Magma G]
    (h46 : Equation46 G) (_ : Equation4512 G) : Equation334 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ X3) := mod_symm (h46 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation334_4512_implies_Equation337 (G : Type*) [Magma G]
    (h334 : Equation334 G) (_ : Equation4512 G) : Equation337 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h334 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq15 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq28 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq11 eq15 -- superposition 15,11
  have eq30 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK1) := superpose eq15 eq13 -- superposition 13,15
  subsumption eq30 eq28

theorem Equation337_4512_implies_Equation338 (G : Type*) [Magma G]
    (h337 : Equation337 G) (_ : Equation4512 G) : Equation338 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X2)) := mod_symm (h337 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq16 (X0 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq26 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (X0 ◇ sK0)) := superpose eq17 eq13 -- superposition 13,17
  have eq28 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq17 eq11 -- superposition 11,17
  have eq140 (X1 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (X1 ◇ sK0))) := superpose eq16 eq26 -- superposition 26,16
  subsumption eq140 eq28

theorem Equation338_4512_implies_Equation340 (G : Type*) [Magma G]
    (h338 : Equation338 G) (h4512 : Equation4512 G) : Equation340 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h338 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq11 eq14 -- superposition 14,11
  have eq22 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X3 ◇ X2) := superpose eq17 eq15 -- backward demodulation 15,17
  have eq43 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X0) := superpose eq11 eq22 -- superposition 22,11
  have eq52 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK2) := superpose eq22 eq13 -- superposition 13,22
  subsumption eq52 eq43

theorem Equation340_4512_implies_Equation341 (G : Type*) [Magma G]
    (h340 : Equation340 G) (_ : Equation4512 G) : Equation341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X2)) := mod_symm (h340 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq28 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (X0 ◇ sK3)) := superpose eq18 eq13 -- superposition 13,18
  have eq57 (X1 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK3 ◇ (X1 ◇ X1))) := superpose eq11 eq28 -- superposition 28,11
  subsumption eq57 eq16

theorem Equation341_4512_implies_Equation342 (G : Type*) [Magma G]
    (h341 : Equation341 G) (_ : Equation4512 G) : Equation342 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X3)) := mod_symm (h341 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq18 (X0 X3 X4 : G) : (X3 ◇ X0) = (X4 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq35 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X0) = (X4 ◇ (X1 ◇ X2)) := superpose eq11 eq18 -- superposition 18,11
  have eq50 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK0 ◇ sK0)) := superpose eq18 eq13 -- superposition 13,18
  subsumption eq50 eq35

theorem Equation342_4512_implies_Equation344 (G : Type*) [Magma G]
    (h342 : Equation342 G) (_ : Equation4512 G) : Equation344 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h342 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq19 eq15

theorem Equation344_4512_implies_Equation345 (G : Type*) [Magma G]
    (h344 : Equation344 G) (_ : Equation4512 G) : Equation345 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X2)) := mod_symm (h344 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK3)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X0 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq15

theorem Equation345_4512_implies_Equation346 (G : Type*) [Magma G]
    (h345 : Equation345 G) (_ : Equation4512 G) : Equation346 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X3)) := mod_symm (h345 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq15 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = (X1 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK2 ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq15

theorem Equation346_4512_implies_Equation348 (G : Type*) [Magma G]
    (h346 : Equation346 G) (h4512 : Equation4512 G) : Equation348 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ X0)) := mod_symm (h346 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ X1) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = (X3 ◇ (X2 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X0) := superpose eq11 eq15 -- forward demodulation 15,11
  have eq28 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq14 eq17 -- superposition 17,14
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X3 ◇ X2) := superpose eq11 eq17 -- superposition 17,11
  have eq67 (X0 : G) : (sK0 ◇ sK1) ≠ (sK2 ◇ (X0 ◇ sK2)) := superpose eq28 eq13 -- superposition 13,28
  subsumption eq67 eq29

theorem Equation348_4512_implies_Equation349 (G : Type*) [Magma G]
    (h348 : Equation348 G) (_ : Equation4512 G) : Equation349 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ X2)) := mod_symm (h348 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq18 (X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ X1) := superpose eq11 eq11 -- superposition 11,11
  have eq25 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X1 ◇ X0)) := superpose eq11 eq18 -- superposition 18,11
  have eq31 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK1 ◇ sK3)) := superpose eq18 eq13 -- superposition 13,18
  subsumption eq31 eq25

theorem Equation349_4512_implies_Equation350 (G : Type*) [Magma G]
    (h349 : Equation349 G) (_ : Equation4512 G) : Equation350 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ X3)) := mod_symm (h349 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 X3 X4 X5 : G) : (X4 ◇ X0) = (X5 ◇ (X3 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK2) := superpose eq11 eq13 -- superposition 13,11
  have eq22 (X1 X2 : G) : (sK0 ◇ sK1) ≠ (X1 ◇ (sK2 ◇ X2)) := superpose eq11 eq20 -- superposition 20,11
  subsumption eq22 eq17

theorem Equation350_4512_implies_Equation352 (G : Type*) [Magma G]
    (h350 : Equation350 G) (_ : Equation4512 G) : Equation352 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ X0)) := mod_symm (h350 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X3 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X0 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq15

theorem Equation352_4512_implies_Equation353 (G : Type*) [Magma G]
    (h352 : Equation352 G) (_ : Equation4512 G) : Equation353 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ X2)) := mod_symm (h352 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq19 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq19 eq11

theorem Equation353_4512_implies_Equation354 (G : Type*) [Magma G]
    (h353 : Equation353 G) (_ : Equation4512 G) : Equation354 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ X3)) := mod_symm (h353 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ sK0)) := mod_symm nh
  have eq20 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq11

theorem Equation354_4512_implies_Equation356 (G : Type*) [Magma G]
    (h354 : Equation354 G) (_ : Equation4512 G) : Equation356 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ X0)) := mod_symm (h354 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ sK2)) := mod_symm nh
  have eq15 (X0 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X0)) = (X2 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X1 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq15

theorem Equation356_4512_implies_Equation357 (G : Type*) [Magma G]
    (h356 : Equation356 G) (_ : Equation4512 G) : Equation357 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ X2)) := mod_symm (h356 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq20 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X1 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq11

theorem Equation357_4512_implies_Equation358 (G : Type*) [Magma G]
    (h357 : Equation357 G) (_ : Equation4512 G) : Equation358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ X3)) := mod_symm (h357 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ sK4)) := mod_symm nh
  have eq20 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq11

theorem Equation358_4512_implies_Equation3344 (G : Type*) [Magma G]
    (h358 : Equation358 G) (_ : Equation4512 G) : Equation3344 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ X4)) := mod_symm (h358 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3344_4512_implies_Equation3347 (G : Type*) [Magma G]
    (h3344 : Equation3344 G) (h4512 : Equation4512 G) : Equation3347 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := mod_symm (h3344 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq14 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = ((X1 ◇ X0) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq34 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = (X1 ◇ (X0 ◇ X3)) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq35 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq12 eq34 -- forward demodulation 34,12
  have eq36 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq35 -- forward demodulation 35,12
  have eq37 (X0 X1 X3 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X3)) := superpose eq11 eq36 -- forward demodulation 36,11
  have eq38 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq37 eq14 -- backward demodulation 14,37
  have eq42 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq37 eq13 -- backward demodulation 13,37
  subsumption eq42 eq38

theorem Equation3347_4512_implies_Equation3348 (G : Type*) [Magma G]
    (h3347 : Equation3347 G) (h4512 : Equation4512 G) : Equation3348 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := mod_symm (h3347 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ X0) := superpose eq11 eq15 -- superposition 15,11
  have eq19 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq15 eq11 -- superposition 11,15
  have eq23 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq19 eq13 -- backward demodulation 13,19
  have eq34 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = ((X1 ◇ X0) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq38 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) := superpose eq11 eq12 -- superposition 12,11
  have eq48 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = (X1 ◇ (X0 ◇ X3)) := superpose eq12 eq34 -- forward demodulation 34,12
  have eq49 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) := superpose eq12 eq48 -- forward demodulation 48,12
  have eq50 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) := superpose eq12 eq49 -- forward demodulation 49,12
  have eq51 (X0 X1 X3 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X3)) := superpose eq11 eq50 -- forward demodulation 50,11
  have eq55 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq51 eq12 -- backward demodulation 12,51
  have eq65 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq51 eq38 -- forward demodulation 38,51
  have eq66 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq65 eq23 -- backward demodulation 23,65
  have eq77 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq18 eq55 -- superposition 55,18
  have eq91 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq77 eq66 -- superposition 66,77
  subsumption eq91 rfl

theorem Equation3348_4512_implies_Equation3351 (G : Type*) [Magma G]
    (h3348 : Equation3348 G) (h4512 : Equation4512 G) : Equation3351 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h3348 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq11 eq15 -- forward demodulation 15,11
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := superpose eq20 eq12 -- backward demodulation 12,20
  have eq23 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq21 eq11 -- backward demodulation 11,21
  have eq24 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK3)) := superpose eq21 eq13 -- backward demodulation 13,21
  have eq33 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X2) := superpose eq21 eq23 -- superposition 23,21
  have eq39 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq23 eq33 -- superposition 33,23
  have eq51 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq33 eq24 -- superposition 24,33
  subsumption eq51 eq39

theorem Equation3351_4512_implies_Equation3354 (G : Type*) [Magma G]
    (h3351 : Equation3351 G) (h4512 : Equation4512 G) : Equation3354 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := mod_symm (h3351 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = (X0 ◇ X4) := superpose eq11 eq11 -- superposition 11,11
  have eq16 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq11 eq13 -- superposition 13,11
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ X0) := superpose eq15 eq12 -- backward demodulation 12,15
  have eq20 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X3) := superpose eq17 eq17 -- superposition 17,17
  have eq21 (X0 X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq17 eq15 -- superposition 15,17
  have eq27 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = (X0 ◇ X3) := superpose eq21 eq20 -- backward demodulation 20,21
  have eq34 (X0 X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ X0) := superpose eq17 eq27 -- superposition 27,17
  have eq59 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ X0) := superpose eq34 eq16 -- superposition 16,34
  subsumption eq59 eq34

theorem Equation3354_4512_implies_Equation3357 (G : Type*) [Magma G]
    (h3354 : Equation3354 G) (h4512 : Equation4512 G) : Equation3357 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h3354 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq14 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = ((X1 ◇ X0) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq23 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = (X1 ◇ (X0 ◇ X3)) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq24 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq25 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X3 ◇ X0) := superpose eq14 eq24 -- forward demodulation 24,14
  have eq26 (X0 X1 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq25 eq14 -- backward demodulation 14,25
  have eq28 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq25 eq11 -- backward demodulation 11,25
  have eq29 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK1)) := superpose eq25 eq13 -- backward demodulation 13,25
  have eq93 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq28 eq26 -- superposition 26,28
  have eq95 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK1) := superpose eq26 eq29 -- superposition 29,26
  subsumption eq95 eq93

theorem Equation3357_4512_implies_Equation3358 (G : Type*) [Magma G]
    (h3357 : Equation3357 G) (h4512 : Equation4512 G) : Equation3358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := mod_symm (h3357 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq18 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq46 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ X2) := superpose eq18 eq12 -- superposition 12,18
  have eq168 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq46 eq11 -- superposition 11,46
  have eq183 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (X0 ◇ sK0)) := superpose eq46 eq13 -- superposition 13,46
  subsumption eq183 eq168

theorem Equation3358_4512_implies_Equation3360 (G : Type*) [Magma G]
    (h3358 : Equation3358 G) (h4512 : Equation4512 G) : Equation3360 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h3358 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X3 ◇ (X3 ◇ (X2 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ X3) := superpose eq11 eq14 -- forward demodulation 14,11
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = ((X2 ◇ X0) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = (X2 ◇ (X0 ◇ X3)) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq25 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq26 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = (X3 ◇ X0) := superpose eq11 eq25 -- forward demodulation 25,11
  have eq27 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X2 ◇ X1) ◇ X3) := superpose eq26 eq17 -- backward demodulation 17,26
  have eq29 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X2)) := superpose eq26 eq11 -- backward demodulation 11,26
  have eq31 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK2)) := superpose eq26 eq13 -- backward demodulation 13,26
  have eq55 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X1) := superpose eq29 eq26 -- superposition 26,29
  have eq74 (X2 X3 X4 : G) : (X3 ◇ X2) = (X4 ◇ X2) := superpose eq27 eq27 -- superposition 27,27
  have eq115 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq55 eq31 -- superposition 31,55
  subsumption eq115 eq74

theorem Equation3360_4512_implies_Equation3361 (G : Type*) [Magma G]
    (h3360 : Equation3360 G) (h4512 : Equation4512 G) : Equation3361 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ X2))) := mod_symm (h3360 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq17 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq47 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ X2) := superpose eq17 eq12 -- superposition 12,17
  have eq84 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq47 eq11 -- superposition 11,47
  have eq92 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (X0 ◇ sK3)) := superpose eq47 eq13 -- superposition 13,47
  subsumption eq92 eq84

theorem Equation3361_4512_implies_Equation3362 (G : Type*) [Magma G]
    (h3361 : Equation3361 G) (_ : Equation4512 G) : Equation3362 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h3361 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq19 (X0 X3 X4 : G) : (X3 ◇ X0) = (X4 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq32 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X0) = (X0 ◇ (X3 ◇ (X1 ◇ X2))) := superpose eq19 eq11 -- superposition 11,19
  have eq34 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ (X0 ◇ sK0))) := superpose eq19 eq13 -- superposition 13,19
  subsumption eq34 eq32

theorem Equation3362_4512_implies_Equation3365 (G : Type*) [Magma G]
    (h3362 : Equation3362 G) (h4512 : Equation4512 G) : Equation3365 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X0 ◇ X0))) := mod_symm (h3362 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK3))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) := superpose eq11 eq12 -- superposition 12,11
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq12 eq11 -- superposition 11,12
  have eq22 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq31 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq11 eq20 -- forward demodulation 20,11
  have eq32 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) := superpose eq31 eq13 -- backward demodulation 13,31
  have eq33 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ ((X0 ◇ X0) ◇ X3)) := superpose eq15 eq21 -- forward demodulation 21,15
  have eq34 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X0 ◇ (X0 ◇ X3))) := superpose eq12 eq33 -- forward demodulation 33,12
  have eq35 (X0 X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X2 ◇ X0)) := superpose eq11 eq22 -- forward demodulation 22,11
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ X2) := superpose eq35 eq34 -- backward demodulation 34,35
  have eq42 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X0) := superpose eq35 eq12 -- backward demodulation 12,35
  have eq43 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq35 eq32 -- backward demodulation 32,35
  have eq58 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq42 eq36 -- superposition 36,42
  have eq85 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ X0)) := superpose eq58 eq43 -- superposition 43,58
  subsumption eq85 eq35

theorem Equation3365_4512_implies_Equation3366 (G : Type*) [Magma G]
    (h3365 : Equation3365 G) (h4512 : Equation4512 G) : Equation3366 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X0 ◇ X3))) := mod_symm (h3365 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X2 X4 X5 : G) : (X0 ◇ X4) = (X4 ◇ (X5 ◇ (X2 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 X2 X4 : G) : (X1 ◇ X4) = (X4 ◇ (X2 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)) = ((X2 ◇ X0) ◇ X4) := superpose eq11 eq12 -- superposition 12,11
  have eq23 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)) = (X2 ◇ (X0 ◇ X4)) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq24 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq25 (X0 X2 X4 : G) : (X2 ◇ (X0 ◇ X4)) = (X4 ◇ X0) := superpose eq14 eq24 -- forward demodulation 24,14
  have eq29 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq25 eq13 -- backward demodulation 13,25
  subsumption eq29 eq15

theorem Equation3366_4512_implies_Equation3368 (G : Type*) [Magma G]
    (h3366 : Equation3366 G) (h4512 : Equation4512 G) : Equation3368 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X1 ◇ X0))) := mod_symm (h3366 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = (X1 ◇ (X2 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) := superpose eq11 eq12 -- superposition 12,11
  have eq21 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq11 -- superposition 11,12
  have eq28 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3))))) := superpose eq12 eq19 -- forward demodulation 19,12
  have eq29 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq21 eq28 -- backward demodulation 28,21
  have eq30 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := superpose eq29 eq13 -- backward demodulation 13,29
  have eq48 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X2 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0))) := superpose eq15 eq11 -- superposition 11,15
  have eq65 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X2 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X0)))) := superpose eq12 eq48 -- forward demodulation 48,12
  have eq71 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X0 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq11 eq29 -- superposition 29,11
  have eq109 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ X0)) := superpose eq21 eq71 -- forward demodulation 71,21
  have eq123 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X2 ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq109 eq65 -- backward demodulation 65,109
  have eq132 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK2)) := superpose eq109 eq30 -- backward demodulation 30,109
  have eq154 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ X2) := superpose eq109 eq123 -- forward demodulation 123,109
  subsumption eq132 eq154

theorem Equation3368_4512_implies_Equation3369 (G : Type*) [Magma G]
    (h3368 : Equation3368 G) (h4512 : Equation4512 G) : Equation3369 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := mod_symm (h3368 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) := mod_symm nh
  have eq17 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq47 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ X2) := superpose eq17 eq12 -- superposition 12,17
  have eq70 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X0 ◇ X1)) := superpose eq11 eq47 -- superposition 47,11
  have eq92 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK1 ◇ sK3)) := superpose eq47 eq13 -- superposition 13,47
  subsumption eq92 eq70

theorem Equation3369_4512_implies_Equation3372 (G : Type*) [Magma G]
    (h3369 : Equation3369 G) (_ : Equation4512 G) : Equation3372 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := mod_symm (h3369 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq17 (X0 X1 X3 X4 : G) : (X4 ◇ X1) = (X1 ◇ (X3 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 X3 X4 : G) : (X3 ◇ X0) = (X4 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq28 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ (X0 ◇ sK2))) := superpose eq19 eq13 -- superposition 13,19
  subsumption eq28 eq17

theorem Equation3372_4512_implies_Equation3373 (G : Type*) [Magma G]
    (h3372 : Equation3372 G) (h4512 : Equation4512 G) : Equation3373 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X2 ◇ X2))) := mod_symm (h3372 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq19 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq51 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ X2) := superpose eq19 eq12 -- superposition 12,19
  have eq88 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X1 ◇ X0)) := superpose eq51 eq11 -- superposition 11,51
  have eq97 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (X0 ◇ sK3)) := superpose eq51 eq13 -- superposition 13,51
  subsumption eq97 eq88

theorem Equation3373_4512_implies_Equation3374 (G : Type*) [Magma G]
    (h3373 : Equation3373 G) (_ : Equation4512 G) : Equation3374 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X2 ◇ X3))) := mod_symm (h3373 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq18 (X0 X2 X3 X4 : G) : (X3 ◇ X4) = (X4 ◇ (X2 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X3 X4 : G) : (X3 ◇ X0) = (X4 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq35 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (X0 ◇ (sK3 ◇ sK0))) := superpose eq20 eq13 -- superposition 13,20
  subsumption eq35 eq18

theorem Equation3374_4512_implies_Equation3376 (G : Type*) [Magma G]
    (h3374 : Equation3374 G) (h4512 : Equation4512 G) : Equation3376 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X3 ◇ X0))) := mod_symm (h3374 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X4 ◇ (X3 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)) = ((X3 ◇ X0) ◇ X4) := superpose eq11 eq12 -- superposition 12,11
  have eq23 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)) = (X3 ◇ (X0 ◇ X4)) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq24 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq25 (X0 X3 X4 : G) : (X3 ◇ (X0 ◇ X4)) = (X4 ◇ X0) := superpose eq11 eq24 -- forward demodulation 24,11
  have eq27 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ X1) := superpose eq25 eq12 -- backward demodulation 12,25
  have eq28 (X0 X1 X3 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X3)) := superpose eq25 eq11 -- backward demodulation 11,25
  have eq29 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK3)) := superpose eq25 eq13 -- backward demodulation 13,25
  have eq31 (X0 X3 X4 : G) : (X4 ◇ (X3 ◇ X0)) = (X4 ◇ X3) := superpose eq27 eq15 -- backward demodulation 15,27
  have eq56 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ X0) := superpose eq28 eq25 -- superposition 25,28
  have eq78 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK2) := superpose eq31 eq29 -- superposition 29,31
  subsumption eq78 eq56

theorem Equation3376_4512_implies_Equation3377 (G : Type*) [Magma G]
    (h3376 : Equation3376 G) (_ : Equation4512 G) : Equation3377 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := mod_symm (h3376 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3))) := mod_symm nh
  have eq18 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = (X4 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X3 X4 : G) : (X3 ◇ X0) = (X4 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq37 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (X0 ◇ (sK3 ◇ sK3))) := superpose eq20 eq13 -- superposition 13,20
  subsumption eq37 eq18

theorem Equation3377_4512_implies_Equation3378 (G : Type*) [Magma G]
    (h3377 : Equation3377 G) (_ : Equation4512 G) : Equation3378 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X3 ◇ X3))) := mod_symm (h3377 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK4))) := mod_symm nh
  have eq18 (X0 X2 X3 X4 : G) : (X3 ◇ X4) = (X4 ◇ (X2 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X3 X4 : G) : (X3 ◇ X0) = (X4 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq35 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (X0 ◇ (sK3 ◇ sK4))) := superpose eq20 eq13 -- superposition 13,20
  subsumption eq35 eq18

theorem Equation3378_4512_implies_Equation3379 (G : Type*) [Magma G]
    (h3378 : Equation3378 G) (_ : Equation4512 G) : Equation3379 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X3 ◇ X4))) := mod_symm (h3378 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq20 (X0 X4 X5 : G) : (X4 ◇ X0) = (X5 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq41 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ X0) = (X5 ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq11 eq20 -- superposition 20,11
  have eq58 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq20 eq13 -- superposition 13,20
  subsumption eq58 eq41

theorem Equation3379_4512_implies_Equation3381 (G : Type*) [Magma G]
    (h3379 : Equation3379 G) (_ : Equation4512 G) : Equation3381 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h3379 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq19 eq15

theorem Equation3381_4512_implies_Equation3382 (G : Type*) [Magma G]
    (h3381 : Equation3381 G) (_ : Equation4512 G) : Equation3382 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X2))) := mod_symm (h3381 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK3))) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X0 ◇ (X0 ◇ X3))) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK2 ◇ (sK2 ◇ X0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq15

theorem Equation3382_4512_implies_Equation3383 (G : Type*) [Magma G]
    (h3382 : Equation3382 G) (_ : Equation4512 G) : Equation3383 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X3))) := mod_symm (h3382 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq15 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X0 ◇ X5))) = (X1 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK2 ◇ (sK2 ◇ X1))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq15

theorem Equation3383_4512_implies_Equation3386 (G : Type*) [Magma G]
    (h3383 : Equation3383 G) (h4512 : Equation4512 G) : Equation3386 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h3383 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK3))) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = (X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X2)))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2))))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) = ((X1 ◇ X2) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) = (X1 ◇ (X2 ◇ X3)) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq25 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq26 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := superpose eq12 eq25 -- forward demodulation 25,12
  have eq29 (X0 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ (X2 ◇ X3)) := superpose eq11 eq20 -- forward demodulation 20,11
  have eq30 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = (X3 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq29 eq17 -- backward demodulation 17,29
  have eq31 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := superpose eq29 eq26 -- backward demodulation 26,29
  have eq35 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ sK3)) := superpose eq29 eq13 -- backward demodulation 13,29
  have eq36 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = (X3 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq29 eq30 -- forward demodulation 30,29
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = (X1 ◇ (X1 ◇ X2)) := superpose eq29 eq36 -- forward demodulation 36,29
  have eq38 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ (X2 ◇ X1)) ◇ X0) := superpose eq29 eq37 -- forward demodulation 37,29
  have eq39 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ X1) ◇ X0) := superpose eq29 eq38 -- forward demodulation 38,29
  have eq40 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X3)) = (X1 ◇ (X2 ◇ X3)) := superpose eq29 eq31 -- forward demodulation 31,29
  have eq41 (X1 X2 X3 : G) : (X1 ◇ X3) = (X1 ◇ (X2 ◇ X3)) := superpose eq29 eq40 -- forward demodulation 40,29
  have eq74 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X2 ◇ X3) := superpose eq29 eq39 -- superposition 39,29
  have eq134 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK3) := superpose eq41 eq35 -- superposition 35,41
  subsumption eq134 eq74

theorem Equation3386_4512_implies_Equation3387 (G : Type*) [Magma G]
    (h3386 : Equation3386 G) (h4512 : Equation4512 G) : Equation3387 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := mod_symm (h3386 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X1 X2 X4 X5 : G) : (X4 ◇ X0) = (X5 ◇ (X4 ◇ (X1 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) := superpose eq11 eq12 -- superposition 12,11
  have eq27 (X0 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ (X2 ◇ X3)) := superpose eq11 eq19 -- forward demodulation 19,11
  have eq28 (X0 X1 X2 X4 X5 : G) : (X4 ◇ X0) = (X5 ◇ (X1 ◇ X2)) := superpose eq27 eq14 -- backward demodulation 14,27
  have eq31 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ sK0)) := superpose eq27 eq13 -- backward demodulation 13,27
  subsumption eq31 eq28

theorem Equation3387_4512_implies_Equation3389 (G : Type*) [Magma G]
    (h3387 : Equation3387 G) (_ : Equation4512 G) : Equation3389 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X2 ◇ X0))) := mod_symm (h3387 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X0 ◇ (X3 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK2 ◇ (X0 ◇ sK2))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq15

theorem Equation3389_4512_implies_Equation3390 (G : Type*) [Magma G]
    (h3389 : Equation3389 G) (_ : Equation4512 G) : Equation3390 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X2 ◇ X2))) := mod_symm (h3389 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X0 ◇ (X3 ◇ X3))) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK2 ◇ (X0 ◇ X0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq15

theorem Equation3390_4512_implies_Equation3391 (G : Type*) [Magma G]
    (h3390 : Equation3390 G) (_ : Equation4512 G) : Equation3391 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X2 ◇ X3))) := mod_symm (h3390 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq15 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X5))) = (X1 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK2 ◇ (X0 ◇ X1))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq15

theorem Equation3391_4512_implies_Equation3393 (G : Type*) [Magma G]
    (h3391 : Equation3391 G) (_ : Equation4512 G) : Equation3393 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X3 ◇ X0))) := mod_symm (h3391 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK3 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X0))) = (X1 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK2 ◇ (X1 ◇ sK2))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq15

theorem Equation3393_4512_implies_Equation3394 (G : Type*) [Magma G]
    (h3393 : Equation3393 G) (_ : Equation4512 G) : Equation3394 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X3 ◇ X2))) := mod_symm (h3393 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK3 ◇ sK3))) := mod_symm nh
  have eq15 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X4))) = (X1 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK2 ◇ (X1 ◇ X0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq15

theorem Equation3394_4512_implies_Equation3395 (G : Type*) [Magma G]
    (h3394 : Equation3394 G) (_ : Equation4512 G) : Equation3395 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X3 ◇ X3))) := mod_symm (h3394 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK3 ◇ sK4))) := mod_symm nh
  have eq15 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X5))) = (X1 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK2 ◇ (X1 ◇ X1))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq15

theorem Equation3395_4512_implies_Equation3396 (G : Type*) [Magma G]
    (h3395 : Equation3395 G) (_ : Equation4512 G) : Equation3396 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X3 ◇ X4))) := mod_symm (h3395 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq18 (X0 X1 X4 X5 X6 : G) : (X0 ◇ X5) = (X6 ◇ (X1 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK2 ◇ (X1 ◇ X2))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq18

theorem Equation3396_4512_implies_Equation3399 (G : Type*) [Magma G]
    (h3396 : Equation3396 G) (h4512 : Equation4512 G) : Equation3399 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3396 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK3))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = (X2 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq11 eq15 -- forward demodulation 15,11
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X2) := superpose eq11 eq16 -- superposition 16,11
  have eq23 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := superpose eq17 eq12 -- backward demodulation 12,17
  have eq25 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ X0)) := superpose eq23 eq11 -- backward demodulation 11,23
  have eq26 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ sK0)) := superpose eq23 eq13 -- backward demodulation 13,23
  subsumption eq26 eq25

theorem Equation3399_4512_implies_Equation3400 (G : Type*) [Magma G]
    (h3399 : Equation3399 G) (h4512 : Equation4512 G) : Equation3400 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ (X0 ◇ X3))) := mod_symm (h3399 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X1 X2 X4 X5 : G) : (X0 ◇ X4) = (X5 ◇ (X4 ◇ (X2 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)) = ((X2 ◇ X1) ◇ X4) := superpose eq11 eq12 -- superposition 12,11
  have eq23 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)) = (X2 ◇ (X1 ◇ X4)) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq24 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ X4)) = (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq25 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = (X2 ◇ (X1 ◇ X4)) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq26 (X1 X2 X4 : G) : (X2 ◇ X1) = (X2 ◇ (X1 ◇ X4)) := superpose eq11 eq25 -- forward demodulation 25,11
  have eq27 (X0 X2 X4 X5 : G) : (X0 ◇ X4) = (X5 ◇ (X4 ◇ X2)) := superpose eq26 eq14 -- backward demodulation 14,26
  have eq30 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ sK1)) := superpose eq26 eq13 -- backward demodulation 13,26
  subsumption eq30 eq27

theorem Equation3400_4512_implies_Equation3402 (G : Type*) [Magma G]
    (h3400 : Equation3400 G) (h4512 : Equation4512 G) : Equation3402 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h3400 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = (X3 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = ((X2 ◇ X1) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := superpose eq11 eq12 -- superposition 12,11
  have eq23 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = (X2 ◇ (X1 ◇ X3)) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq24 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq25 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq28 (X0 X2 X3 : G) : (X3 ◇ X2) = (X0 ◇ (X3 ◇ X2)) := superpose eq11 eq19 -- forward demodulation 19,11
  have eq29 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq28 eq14 -- backward demodulation 14,28
  have eq30 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq28 eq25 -- backward demodulation 25,28
  have eq34 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ sK2)) := superpose eq28 eq13 -- backward demodulation 13,28
  have eq35 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ (X1 ◇ X2)) ◇ X0) := superpose eq28 eq29 -- forward demodulation 29,28
  have eq36 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X2) ◇ X0) := superpose eq28 eq35 -- forward demodulation 35,28
  have eq37 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X1 ◇ X3) := superpose eq28 eq30 -- forward demodulation 30,28
  have eq38 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = (X0 ◇ (X2 ◇ X3)) := superpose eq28 eq37 -- forward demodulation 37,28
  have eq71 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X2 ◇ X3) := superpose eq28 eq36 -- superposition 36,28
  have eq153 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK2) := superpose eq38 eq34 -- superposition 34,38
  subsumption eq153 eq71

theorem Equation3402_4512_implies_Equation3403 (G : Type*) [Magma G]
    (h3402 : Equation3402 G) (_ : Equation4512 G) : Equation3403 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ (X1 ◇ X2))) := mod_symm (h3402 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK3))) := mod_symm nh
  have eq18 (X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ X1) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq11 eq18 -- superposition 18,11
  have eq29 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK1 ◇ (sK1 ◇ sK3))) := superpose eq18 eq13 -- superposition 13,18
  subsumption eq29 eq22

theorem Equation3403_4512_implies_Equation3406 (G : Type*) [Magma G]
    (h3403 : Equation3403 G) (_ : Equation4512 G) : Equation3406 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := mod_symm (h3403 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq17 (X0 X1 X3 X4 X5 : G) : (X4 ◇ X0) = (X5 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X1 X3 X4 : G) : (X3 ◇ X1) = (X4 ◇ X1) := superpose eq11 eq11 -- superposition 11,11
  have eq32 (X0 : G) : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (X0 ◇ sK2))) := superpose eq19 eq13 -- superposition 13,19
  subsumption eq32 eq17

theorem Equation3406_4512_implies_Equation3407 (G : Type*) [Magma G]
    (h3406 : Equation3406 G) (h4512 : Equation4512 G) : Equation3407 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ (X2 ◇ X2))) := mod_symm (h3406 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ X1) := superpose eq11 eq11 -- superposition 11,11
  have eq53 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ X2) := superpose eq19 eq12 -- superposition 12,19
  have eq90 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (X1 ◇ (X2 ◇ X1)) := superpose eq53 eq11 -- superposition 11,53
  have eq98 (X0 : G) : (sK0 ◇ sK1) ≠ (sK2 ◇ (X0 ◇ sK3)) := superpose eq53 eq13 -- superposition 13,53
  have eq166 (X1 : G) : (sK0 ◇ sK1) ≠ (X1 ◇ sK3) := superpose eq53 eq98 -- superposition 98,53
  have eq248 (X1 : G) : (sK0 ◇ sK1) ≠ ((sK3 ◇ sK3) ◇ (X1 ◇ (sK3 ◇ sK3))) := superpose eq17 eq166 -- superposition 166,17
  subsumption eq248 eq90

theorem Equation3407_4512_implies_Equation3408 (G : Type*) [Magma G]
    (h3407 : Equation3407 G) (_ : Equation4512 G) : Equation3408 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h3407 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq17 (X0 X1 X3 X4 X5 : G) : (X4 ◇ X5) = (X0 ◇ (X5 ◇ (X3 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X1 X3 X4 : G) : (X3 ◇ X1) = (X4 ◇ X1) := superpose eq11 eq11 -- superposition 11,11
  have eq39 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0))) := superpose eq20 eq13 -- superposition 13,20
  subsumption eq39 eq17

theorem Equation3408_4512_implies_Equation3410 (G : Type*) [Magma G]
    (h3408 : Equation3408 G) (h4512 : Equation4512 G) : Equation3410 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ (X3 ◇ X0))) := mod_symm (h3408 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK2))) := mod_symm nh
  have eq20 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) := superpose eq11 eq12 -- superposition 12,11
  have eq22 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (X3 ◇ (X0 ◇ X1)) := superpose eq12 eq11 -- superposition 11,12
  have eq27 (X0 X2 X4 : G) : (X4 ◇ X2) = (X0 ◇ (X4 ◇ X2)) := superpose eq11 eq20 -- forward demodulation 20,11
  have eq31 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ X0)) := superpose eq27 eq11 -- backward demodulation 11,27
  have eq32 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ sK2)) := superpose eq27 eq13 -- backward demodulation 13,27
  have eq35 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq27 eq22 -- forward demodulation 22,27
  have eq36 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X4 ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq27 eq35 -- forward demodulation 35,27
  have eq37 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X4 ◇ (X2 ◇ X3)) := superpose eq27 eq36 -- forward demodulation 36,27
  have eq44 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X1 ◇ sK2)) := superpose eq31 eq32 -- superposition 32,31
  subsumption eq44 eq37

theorem Equation3410_4512_implies_Equation3411 (G : Type*) [Magma G]
    (h3410 : Equation3410 G) (_ : Equation4512 G) : Equation3411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ (X3 ◇ X2))) := mod_symm (h3410 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK3))) := mod_symm nh
  have eq20 (X1 X3 X4 : G) : (X3 ◇ X1) = (X4 ◇ X1) := superpose eq11 eq11 -- superposition 11,11
  have eq30 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = (X4 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq11 eq20 -- superposition 20,11
  have eq40 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK1 ◇ (sK3 ◇ sK3))) := superpose eq20 eq13 -- superposition 13,20
  subsumption eq40 eq30

theorem Equation3411_4512_implies_Equation3412 (G : Type*) [Magma G]
    (h3411 : Equation3411 G) (_ : Equation4512 G) : Equation3412 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ (X3 ◇ X3))) := mod_symm (h3411 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK4))) := mod_symm nh
  have eq17 (X0 X2 X3 X4 X5 : G) : (X3 ◇ X4) = (X5 ◇ (X4 ◇ (X2 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X1 X3 X4 : G) : (X3 ◇ X1) = (X4 ◇ X1) := superpose eq11 eq11 -- superposition 11,11
  have eq38 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK1 ◇ (sK3 ◇ sK4))) := superpose eq20 eq13 -- superposition 13,20
  subsumption eq38 eq17

theorem Equation3412_4512_implies_Equation3413 (G : Type*) [Magma G]
    (h3412 : Equation3412 G) (_ : Equation4512 G) : Equation3413 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ (X3 ◇ X4))) := mod_symm (h3412 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq18 (X0 X1 X4 X5 X6 : G) : (X6 ◇ (X4 ◇ X1)) = (X5 ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK2) := superpose eq11 eq13 -- superposition 13,11
  have eq24 (X1 X2 X3 : G) : (sK0 ◇ sK1) ≠ (X1 ◇ (sK2 ◇ (X2 ◇ X3))) := superpose eq11 eq22 -- superposition 22,11
  subsumption eq24 eq18

theorem Equation3413_4512_implies_Equation3415 (G : Type*) [Magma G]
    (h3413 : Equation3413 G) (_ : Equation4512 G) : Equation3415 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ X0))) := mod_symm (h3413 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X3 ◇ (X0 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X0 ◇ (sK2 ◇ sK2))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq15

theorem Equation3415_4512_implies_Equation3416 (G : Type*) [Magma G]
    (h3415 : Equation3415 G) (_ : Equation4512 G) : Equation3416 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ X2))) := mod_symm (h3415 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK3))) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X0 ◇ (sK2 ◇ X0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq15

theorem Equation3416_4512_implies_Equation3419 (G : Type*) [Magma G]
    (h3416 : Equation3416 G) (_ : Equation4512 G) : Equation3419 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ X3))) := mod_symm (h3416 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X4 ◇ (X0 ◇ X5))) = (X1 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X0 ◇ (sK2 ◇ X1))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq15

theorem Equation3419_4512_implies_Equation3420 (G : Type*) [Magma G]
    (h3419 : Equation3419 G) (h4512 : Equation4512 G) : Equation3420 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X1 ◇ X2))) := mod_symm (h3419 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK3))) := mod_symm nh
  have eq19 (X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ X1) := superpose eq11 eq11 -- superposition 11,11
  have eq55 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ X2) := superpose eq19 eq12 -- superposition 12,19
  have eq78 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X1 ◇ X0)) := superpose eq11 eq55 -- superposition 55,11
  have eq101 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK1 ◇ sK3)) := superpose eq55 eq13 -- superposition 13,55
  subsumption eq101 eq78

theorem Equation3420_4512_implies_Equation3421 (G : Type*) [Magma G]
    (h3420 : Equation3420 G) (_ : Equation4512 G) : Equation3421 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X1 ◇ X3))) := mod_symm (h3420 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq17 (X0 X1 X3 X4 X5 : G) : (X4 ◇ X0) = (X5 ◇ (X5 ◇ (X3 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK2) := superpose eq11 eq13 -- superposition 13,11
  have eq26 (X1 X2 : G) : (sK0 ◇ sK1) ≠ (X1 ◇ (X1 ◇ (sK2 ◇ X2))) := superpose eq11 eq22 -- superposition 22,11
  subsumption eq26 eq17

theorem Equation3421_4512_implies_Equation3423 (G : Type*) [Magma G]
    (h3421 : Equation3421 G) (_ : Equation4512 G) : Equation3423 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X2 ◇ X0))) := mod_symm (h3421 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X3 ◇ (X3 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X0 ◇ (X0 ◇ sK2))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq15

theorem Equation3423_4512_implies_Equation3424 (G : Type*) [Magma G]
    (h3423 : Equation3423 G) (_ : Equation4512 G) : Equation3424 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X2 ◇ X2))) := mod_symm (h3423 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq11

theorem Equation3424_4512_implies_Equation3425 (G : Type*) [Magma G]
    (h3424 : Equation3424 G) (_ : Equation4512 G) : Equation3425 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X2 ◇ X3))) := mod_symm (h3424 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq22 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq11

theorem Equation3425_4512_implies_Equation3427 (G : Type*) [Magma G]
    (h3425 : Equation3425 G) (_ : Equation4512 G) : Equation3427 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X3 ◇ X0))) := mod_symm (h3425 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X2 X3 X4 X5 : G) : (X4 ◇ (X4 ◇ (X5 ◇ X0))) = (X2 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X0 ◇ (X1 ◇ sK2))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq15

theorem Equation3427_4512_implies_Equation3428 (G : Type*) [Magma G]
    (h3427 : Equation3427 G) (_ : Equation4512 G) : Equation3428 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X3 ◇ X2))) := mod_symm (h3427 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK3))) := mod_symm nh
  have eq21 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq11

theorem Equation3428_4512_implies_Equation3429 (G : Type*) [Magma G]
    (h3428 : Equation3428 G) (_ : Equation4512 G) : Equation3429 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X3 ◇ X3))) := mod_symm (h3428 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) := mod_symm nh
  have eq21 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq11

theorem Equation3429_4512_implies_Equation3430 (G : Type*) [Magma G]
    (h3429 : Equation3429 G) (_ : Equation4512 G) : Equation3430 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X3 ◇ X4))) := mod_symm (h3429 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq22 (X0 X1 X2 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq11

theorem Equation3430_4512_implies_Equation3432 (G : Type*) [Magma G]
    (h3430 : Equation3430 G) (_ : Equation4512 G) : Equation3432 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ X0))) := mod_symm (h3430 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X0))) = (X2 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq15

theorem Equation3432_4512_implies_Equation3433 (G : Type*) [Magma G]
    (h3432 : Equation3432 G) (_ : Equation4512 G) : Equation3433 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ X2))) := mod_symm (h3432 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) := mod_symm nh
  have eq15 (X0 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X4))) = (X2 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X1 ◇ (sK2 ◇ X0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq15

theorem Equation3433_4512_implies_Equation3434 (G : Type*) [Magma G]
    (h3433 : Equation3433 G) (_ : Equation4512 G) : Equation3434 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ X3))) := mod_symm (h3433 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK4))) := mod_symm nh
  have eq18 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = (X4 ◇ (X0 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X1 ◇ (sK2 ◇ X1))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq18

theorem Equation3434_4512_implies_Equation3435 (G : Type*) [Magma G]
    (h3434 : Equation3434 G) (_ : Equation4512 G) : Equation3435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ X4))) := mod_symm (h3434 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq18 (X1 X2 X4 X5 X6 : G) : (X1 ◇ X5) = (X6 ◇ (X2 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X1 ◇ (sK2 ◇ X2))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq18

theorem Equation3435_4512_implies_Equation3437 (G : Type*) [Magma G]
    (h3435 : Equation3435 G) (h4512 : Equation4512 G) : Equation3437 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ X0))) := mod_symm (h3435 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = (X4 ◇ (X5 ◇ (X3 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := superpose eq11 eq14 -- forward demodulation 14,11
  have eq19 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X1) ◇ (X2 ◇ X3)) := superpose eq12 eq12 -- superposition 12,12
  have eq20 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) := superpose eq11 eq12 -- superposition 12,11
  have eq28 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) = ((X0 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq12 eq19 -- forward demodulation 19,12
  have eq29 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq17 eq28 -- forward demodulation 28,17
  have eq30 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ (X4 ◇ X3)) := superpose eq11 eq20 -- forward demodulation 20,11
  have eq36 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ (X2 ◇ X3)) := superpose eq30 eq29 -- backward demodulation 29,30
  have eq37 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ sK2)) := superpose eq30 eq13 -- backward demodulation 13,30
  subsumption eq37 eq36

theorem Equation3437_4512_implies_Equation3438 (G : Type*) [Magma G]
    (h3437 : Equation3437 G) (_ : Equation4512 G) : Equation3438 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ X2))) := mod_symm (h3437 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK3))) := mod_symm nh
  have eq20 (X2 X3 X4 : G) : (X3 ◇ X2) = (X4 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq30 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X2) = (X4 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq11 eq20 -- superposition 20,11
  have eq40 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (sK3 ◇ (sK1 ◇ sK3))) := superpose eq20 eq13 -- superposition 13,20
  subsumption eq40 eq30

theorem Equation3438_4512_implies_Equation3439 (G : Type*) [Magma G]
    (h3438 : Equation3438 G) (_ : Equation4512 G) : Equation3439 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ X3))) := mod_symm (h3438 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK4))) := mod_symm nh
  have eq18 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = (X4 ◇ (X2 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X2 X3 X4 : G) : (X3 ◇ X2) = (X4 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq38 (X0 : G) : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (X0 ◇ sK4))) := superpose eq20 eq13 -- superposition 13,20
  subsumption eq38 eq18

theorem Equation3439_4512_implies_Equation3440 (G : Type*) [Magma G]
    (h3439 : Equation3439 G) (_ : Equation4512 G) : Equation3440 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ X4))) := mod_symm (h3439 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq17 (X0 X2 X4 X5 X6 X7 : G) : (X5 ◇ X0) = (X6 ◇ (X7 ◇ (X4 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK2) := superpose eq11 eq13 -- superposition 13,11
  have eq25 (X1 X2 X3 : G) : (sK0 ◇ sK1) ≠ (X1 ◇ (X2 ◇ (sK2 ◇ X3))) := superpose eq11 eq22 -- superposition 22,11
  subsumption eq25 eq17

theorem Equation3440_4512_implies_Equation3442 (G : Type*) [Magma G]
    (h3440 : Equation3440 G) (_ : Equation4512 G) : Equation3442 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X2 ◇ X0))) := mod_symm (h3440 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ (X4 ◇ X0))) = (X2 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X1 ◇ (X0 ◇ sK2))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq15

theorem Equation3442_4512_implies_Equation3443 (G : Type*) [Magma G]
    (h3442 : Equation3442 G) (_ : Equation4512 G) : Equation3443 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X2 ◇ X2))) := mod_symm (h3442 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq21 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq11

theorem Equation3443_4512_implies_Equation3444 (G : Type*) [Magma G]
    (h3443 : Equation3443 G) (_ : Equation4512 G) : Equation3444 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X2 ◇ X3))) := mod_symm (h3443 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK2 ◇ sK4))) := mod_symm nh
  have eq21 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq11

theorem Equation3444_4512_implies_Equation3445 (G : Type*) [Magma G]
    (h3444 : Equation3444 G) (_ : Equation4512 G) : Equation3445 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X2 ◇ X4))) := mod_symm (h3444 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq22 (X0 X1 X2 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq11

theorem Equation3445_4512_implies_Equation3447 (G : Type*) [Magma G]
    (h3445 : Equation3445 G) (_ : Equation4512 G) : Equation3447 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X3 ◇ X0))) := mod_symm (h3445 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ (X5 ◇ X0))) = (X2 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X1 ◇ (X1 ◇ sK2))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq15

theorem Equation3447_4512_implies_Equation3448 (G : Type*) [Magma G]
    (h3447 : Equation3447 G) (_ : Equation4512 G) : Equation3448 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X3 ◇ X2))) := mod_symm (h3447 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK3))) := mod_symm nh
  have eq22 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq11

theorem Equation3448_4512_implies_Equation3449 (G : Type*) [Magma G]
    (h3448 : Equation3448 G) (_ : Equation4512 G) : Equation3449 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X3 ◇ X3))) := mod_symm (h3448 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK4))) := mod_symm nh
  have eq21 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq11

theorem Equation3449_4512_implies_Equation3450 (G : Type*) [Magma G]
    (h3449 : Equation3449 G) (_ : Equation4512 G) : Equation3450 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X3 ◇ X4))) := mod_symm (h3449 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK0))) := mod_symm nh
  have eq22 (X0 X1 X2 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq11

theorem Equation3450_4512_implies_Equation3452 (G : Type*) [Magma G]
    (h3450 : Equation3450 G) (_ : Equation4512 G) : Equation3452 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ X0))) := mod_symm (h3450 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X6 ◇ (X7 ◇ X0))) = (X3 ◇ X4) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X1 ◇ (X2 ◇ sK2))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq15

theorem Equation3452_4512_implies_Equation3453 (G : Type*) [Magma G]
    (h3452 : Equation3452 G) (_ : Equation4512 G) : Equation3453 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ X2))) := mod_symm (h3452 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK3))) := mod_symm nh
  have eq22 (X0 X1 X2 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq11

theorem Equation3453_4512_implies_Equation3454 (G : Type*) [Magma G]
    (h3453 : Equation3453 G) (_ : Equation4512 G) : Equation3454 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ X3))) := mod_symm (h3453 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK4))) := mod_symm nh
  have eq22 (X0 X1 X2 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq11

theorem Equation3454_4512_implies_Equation3455 (G : Type*) [Magma G]
    (h3454 : Equation3454 G) (_ : Equation4512 G) : Equation3455 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, sK5, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ X4))) := mod_symm (h3454 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK5))) := mod_symm nh
  have eq22 (X0 X1 X2 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq11


/- Equivalence of [66, 73] -/
theorem Equation73_4512_implies_Equation66 (G : Type*) [Magma G]
    (h73 : Equation73 G) (h4512 : Equation4512 G) : Equation66 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h73 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq14 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose eq12 eq14 -- forward demodulation 14,12
  have eq16 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq12 eq15 -- forward demodulation 15,12
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq24 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq37 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3)) := superpose eq20 eq12 -- superposition 12,20
  have eq50 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3))) := superpose eq12 eq37 -- forward demodulation 37,12
  have eq51 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3)))) := superpose eq12 eq50 -- forward demodulation 50,12
  have eq52 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3))))) := superpose eq12 eq51 -- forward demodulation 51,12
  have eq53 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3))))) := superpose eq12 eq52 -- forward demodulation 52,12
  have eq58 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq11 eq24 -- superposition 24,11
  have eq62 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq24 -- superposition 24,11
  have eq100 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) = X0 := superpose eq11 eq16 -- superposition 16,11
  have eq165 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := superpose eq12 eq100 -- forward demodulation 100,12
  have eq166 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = X0 := superpose eq12 eq165 -- forward demodulation 165,12
  have eq167 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X1 ◇ X1)) = X0 := superpose eq24 eq166 -- forward demodulation 166,24
  have eq168 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ X1)) = X0 := superpose eq62 eq167 -- forward demodulation 167,62
  have eq169 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X0 := superpose eq20 eq168 -- forward demodulation 168,20
  have eq373 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq11 eq169 -- superposition 169,11
  have eq395 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)))) = X0 := superpose eq58 eq373 -- forward demodulation 373,58
  have eq396 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))))) = X0 := superpose eq12 eq395 -- forward demodulation 395,12
  have eq397 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) = X0 := superpose eq12 eq396 -- forward demodulation 396,12
  have eq398 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq53 eq397 -- forward demodulation 397,53
  have eq1363 : sK0 ≠ sK0 := superpose eq398 eq13 -- superposition 13,398
  subsumption eq1363 rfl

theorem Equation66_4512_implies_Equation73 (G : Type*) [Magma G]
    (h66 : Equation66 G) (h4512 : Equation4512 G) : Equation73 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h66 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq14 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq53 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq14 eq24 -- superposition 24,14
  have eq67 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := superpose eq53 eq13 -- backward demodulation 13,53
  subsumption eq67 eq11


/- Equivalence of [308, 3254, 3257] -/
theorem Equation3257_4512_implies_Equation308 (G : Type*) [Magma G]
    (h3257 : Equation3257 G) (h4512 : Equation4512 G) : Equation308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := mod_symm (h3257 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq28 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq12 eq28 -- forward demodulation 28,12
  have eq30 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X3)) := superpose eq11 eq29 -- forward demodulation 29,11
  have eq46 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq30 eq13 -- superposition 13,30
  subsumption eq46 rfl

theorem Equation308_4512_implies_Equation3254 (G : Type*) [Magma G]
    (h308 : Equation308 G) (_ : Equation4512 G) : Equation3254 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h308 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3254_4512_implies_Equation3257 (G : Type*) [Magma G]
    (h3254 : Equation3254 G) (h4512 : Equation4512 G) : Equation3257 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := mod_symm (h3254 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq28 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq29 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq12 eq28 -- forward demodulation 28,12
  have eq30 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq29 -- forward demodulation 29,12
  have eq31 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq11 eq30 -- forward demodulation 30,11
  have eq51 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq31 eq13 -- superposition 13,31
  subsumption eq51 rfl


/- Equivalence of [310, 3262, 3263, 3266] -/
theorem Equation3266_4512_implies_Equation310 (G : Type*) [Magma G]
    (h3266 : Equation3266 G) (_ : Equation4512 G) : Equation310 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := mod_symm (h3266 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq16 (X0 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq26 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq26 rfl

theorem Equation310_4512_implies_Equation3262 (G : Type*) [Magma G]
    (h310 : Equation310 G) (_ : Equation4512 G) : Equation3262 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h310 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation3262_4512_implies_Equation3263 (G : Type*) [Magma G]
    (h3262 : Equation3262 G) (h4512 : Equation4512 G) : Equation3263 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := mod_symm (h3262 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq11 eq12 -- superposition 12,11
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq11 eq12 -- superposition 12,11
  have eq111 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))))) = ((X0 ◇ (X3 ◇ (X3 ◇ X3))) ◇ X0) := superpose eq15 eq16 -- superposition 16,15
  have eq123 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq15 eq16 -- superposition 16,15
  have eq126 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X3 ◇ X3))) ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2))) := superpose eq16 eq16 -- superposition 16,16
  have eq144 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X3)) = ((X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ X3) := superpose eq16 eq16 -- superposition 16,16
  have eq150 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))) = ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq11 eq16 -- superposition 16,11
  have eq152 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X3 ◇ X3))) ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2))) := superpose eq16 eq16 -- superposition 16,16
  have eq157 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (X3 ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq16 eq15 -- superposition 15,16
  have eq195 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X3 ◇ X3))) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)))) := superpose eq12 eq126 -- forward demodulation 126,12
  have eq196 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X3 ◇ X3))) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))))) := superpose eq12 eq195 -- forward demodulation 195,12
  have eq197 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X3 ◇ X3))) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))))) := superpose eq12 eq196 -- forward demodulation 196,12
  have eq198 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X3 ◇ X3)))) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))))) := superpose eq12 eq197 -- forward demodulation 197,12
  have eq199 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X3 ◇ (X3 ◇ X3))))) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))))) := superpose eq12 eq198 -- forward demodulation 198,12
  have eq200 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X3)))))) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))))) := superpose eq12 eq199 -- forward demodulation 199,12
  have eq201 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))))) := superpose eq15 eq200 -- forward demodulation 200,15
  have eq202 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))))) := superpose eq12 eq201 -- forward demodulation 201,12
  have eq203 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))))) := superpose eq12 eq202 -- forward demodulation 202,12
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ X3) = ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X3))) := superpose eq12 eq144 -- forward demodulation 144,12
  have eq227 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ X3) = ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X3)))) := superpose eq12 eq226 -- forward demodulation 226,12
  have eq228 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ X3) = ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X3))))) := superpose eq12 eq227 -- forward demodulation 227,12
  have eq231 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq123 eq150 -- forward demodulation 150,123
  have eq232 (X0 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ X0)) := superpose eq231 eq15 -- backward demodulation 15,231
  have eq241 (X0 X1 X3 : G) : ((X0 ◇ (X3 ◇ (X3 ◇ X3))) ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq231 eq111 -- backward demodulation 111,231
  have eq247 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X3) = ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X3))))) := superpose eq231 eq228 -- backward demodulation 228,231
  have eq251 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X2 ◇ X2)) := superpose eq232 eq19 -- backward demodulation 19,232
  have eq252 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq232 eq20 -- backward demodulation 20,232
  have eq261 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq232 eq123 -- backward demodulation 123,232
  have eq267 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq232 eq231 -- backward demodulation 231,232
  have eq274 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq232 eq261 -- forward demodulation 261,232
  have eq286 (X0 X3 : G) : (X0 ◇ X0) = ((X0 ◇ (X3 ◇ (X3 ◇ X3))) ◇ X0) := superpose eq267 eq241 -- forward demodulation 241,267
  have eq287 (X0 X3 : G) : (X0 ◇ X0) = ((X0 ◇ (X3 ◇ X3)) ◇ X0) := superpose eq232 eq286 -- forward demodulation 286,232
  have eq296 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X3) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X3))))) := superpose eq232 eq247 -- forward demodulation 247,232
  have eq297 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X3)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X3))))) := superpose eq12 eq296 -- forward demodulation 296,12
  have eq302 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X3 ◇ X3))) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)))) := superpose eq12 eq152 -- forward demodulation 152,12
  have eq303 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X3 ◇ X3))) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))))) := superpose eq12 eq302 -- forward demodulation 302,12
  have eq304 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X3 ◇ X3))) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))))) := superpose eq12 eq303 -- forward demodulation 303,12
  have eq305 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X3 ◇ X3))) ◇ X2) := superpose eq203 eq304 -- forward demodulation 304,203
  have eq306 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = ((X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X3 ◇ X3)))) ◇ X2) := superpose eq12 eq305 -- forward demodulation 305,12
  have eq307 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X3 ◇ (X3 ◇ X3))))) ◇ X2) := superpose eq12 eq306 -- forward demodulation 306,12
  have eq308 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X3)))))) ◇ X2) := superpose eq12 eq307 -- forward demodulation 307,12
  have eq309 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X3))))) ◇ X2) := superpose eq232 eq308 -- forward demodulation 308,232
  have eq310 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2) := superpose eq267 eq309 -- forward demodulation 309,267
  have eq311 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq232 eq310 -- forward demodulation 310,232
  have eq327 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (X3 ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq12 eq157 -- forward demodulation 157,12
  have eq328 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (X3 ◇ (X0 ◇ (X2 ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq12 eq327 -- forward demodulation 327,12
  have eq329 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (X3 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1))))))) := superpose eq12 eq328 -- forward demodulation 328,12
  have eq330 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (X3 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1)))))) := superpose eq232 eq329 -- forward demodulation 329,232
  have eq331 (X0 X2 X3 : G) : (X3 ◇ X3) = (X3 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq267 eq330 -- forward demodulation 330,267
  have eq332 (X0 X2 X3 : G) : (X3 ◇ X3) = (X3 ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq232 eq331 -- forward demodulation 331,232
  have eq414 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq232 eq12 -- superposition 12,232
  have eq420 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = ((X0 ◇ X0) ◇ X2) := superpose eq12 eq414 -- forward demodulation 414,12
  have eq428 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X3)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X3))) := superpose eq420 eq297 -- backward demodulation 297,420
  have eq440 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X3)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X3)))) := superpose eq12 eq428 -- forward demodulation 428,12
  have eq578 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq251 eq287 -- superposition 287,251
  have eq583 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq232 eq287 -- superposition 287,232
  have eq598 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq12 eq578 -- forward demodulation 578,12
  have eq611 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X3 ◇ X3))) = ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq252 eq252 -- superposition 252,252
  have eq617 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3))) = (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) := superpose eq251 eq252 -- superposition 252,251
  have eq661 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq332 eq611 -- forward demodulation 611,332
  have eq662 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq12 eq661 -- forward demodulation 661,12
  have eq671 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3))) := superpose eq274 eq617 -- forward demodulation 617,274
  have eq672 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq332 eq671 -- forward demodulation 671,332
  have eq673 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq672 eq662 -- backward demodulation 662,672
  have eq682 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq673 eq598 -- backward demodulation 598,673
  have eq724 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq583 eq12 -- superposition 12,583
  have eq728 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq682 eq724 -- forward demodulation 724,682
  have eq808 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq232 eq728 -- superposition 728,232
  have eq854 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ X1)) := superpose eq808 eq311 -- backward demodulation 311,808
  have eq856 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X3)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq854 eq440 -- backward demodulation 440,854
  have eq860 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X3)) := superpose eq672 eq856 -- forward demodulation 856,672
  have eq869 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq860 eq13 -- backward demodulation 13,860
  subsumption eq869 eq232

theorem Equation3263_4512_implies_Equation3266 (G : Type*) [Magma G]
    (h3263 : Equation3263 G) (_ : Equation4512 G) : Equation3266 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := mod_symm (h3263 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq17 (X0 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq17 eq13 -- backward demodulation 13,17
  subsumption eq18 eq17


/- Equivalence of [312, 3268, 3288] -/
theorem Equation3288_4512_implies_Equation312 (G : Type*) [Magma G]
    (h3288 : Equation3288 G) (h4512 : Equation4512 G) : Equation312 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ X0))) := mod_symm (h3288 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq18 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) := superpose eq11 eq12 -- superposition 12,11
  have eq27 (X0 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X3 ◇ X3)) := superpose eq11 eq18 -- forward demodulation 18,11
  have eq39 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq27 eq13 -- superposition 13,27
  subsumption eq39 rfl

theorem Equation312_4512_implies_Equation3268 (G : Type*) [Magma G]
    (h312 : Equation312 G) (_ : Equation4512 G) : Equation3268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h312 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq14 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation3268_4512_implies_Equation3288 (G : Type*) [Magma G]
    (h3268 : Equation3268 G) (h4512 : Equation4512 G) : Equation3288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h3268 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq20 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq11 eq12 -- superposition 12,11
  have eq29 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X2 ◇ X2)) := superpose eq11 eq20 -- forward demodulation 20,11
  have eq31 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq29 eq13 -- backward demodulation 13,29
  subsumption eq31 eq29


/- Equivalence of [313, 319] -/
theorem Equation319_4512_implies_Equation313 (G : Type*) [Magma G]
    (h319 : Equation319 G) (_ : Equation4512 G) : Equation313 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ X1)) := mod_symm (h319 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation313_4512_implies_Equation319 (G : Type*) [Magma G]
    (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h313 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq53 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq14 eq13 -- superposition 13,14
  have eq125 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq15 -- superposition 15,15
  have eq146 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq12 eq125 -- forward demodulation 125,12
  have eq147 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq146 -- forward demodulation 146,15
  have eq148 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq147 -- forward demodulation 147,11
  have eq182 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq16 eq148 -- superposition 148,16
  have eq199 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq148 eq53 -- superposition 53,148
  subsumption eq199 eq182


/- Equivalence of [314, 321] -/
theorem Equation321_4512_implies_Equation314 (G : Type*) [Magma G]
    (h321 : Equation321 G) (_ : Equation4512 G) : Equation314 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ X3)) := mod_symm (h321 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  subsumption eq13 eq11

theorem Equation314_4512_implies_Equation321 (G : Type*) [Magma G]
    (h314 : Equation314 G) (_ : Equation4512 G) : Equation321 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h314 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq76 (X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ X4)) = (X2 ◇ X2) := superpose eq17 eq14 -- superposition 14,17
  have eq102 (X0 X1 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (sK2 ◇ X1)) := superpose eq14 eq13 -- superposition 13,14
  subsumption eq102 eq76


/- Equivalence of [315, 3281, 3284, 3296] -/
theorem Equation3296_4512_implies_Equation315 (G : Type*) [Magma G]
    (h3296 : Equation3296 G) (h4512 : Equation4512 G) : Equation315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X2 ◇ X0))) := mod_symm (h3296 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0))))) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq11 eq17 -- forward demodulation 17,11
  have eq25 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := superpose eq11 eq12 -- superposition 12,11
  have eq34 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = (X3 ◇ (X0 ◇ X0)) := superpose eq25 eq16 -- backward demodulation 16,25
  have eq43 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq12 eq20 -- superposition 20,12
  have eq48 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) := superpose eq20 eq12 -- superposition 12,20
  have eq52 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X2 ◇ X2)) := superpose eq20 eq43 -- forward demodulation 43,20
  have eq64 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) := superpose eq12 eq48 -- forward demodulation 48,12
  have eq65 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := superpose eq12 eq64 -- forward demodulation 64,12
  have eq73 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = (X3 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) := superpose eq11 eq52 -- superposition 52,11
  have eq84 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X1 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq65 eq73 -- forward demodulation 73,65
  have eq150 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0))))) = (X4 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) := superpose eq11 eq34 -- superposition 34,11
  have eq205 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = (X4 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq84 eq150 -- forward demodulation 150,84
  have eq206 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X3 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) := superpose eq84 eq205 -- forward demodulation 205,84
  have eq207 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X3 ◇ (X0 ◇ X0)) := superpose eq11 eq206 -- forward demodulation 206,11
  have eq329 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (sK0 ◇ sK0)) := superpose eq207 eq13 -- superposition 13,207
  subsumption eq329 eq52

theorem Equation315_4512_implies_Equation3281 (G : Type*) [Magma G]
    (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation3281 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h315 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq14 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq16 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq24 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12
  have eq66 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq11 eq16 -- superposition 16,11
  have eq85 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq24 eq66 -- forward demodulation 66,24
  have eq136 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq85 eq14 -- superposition 14,85
  subsumption eq136 rfl

theorem Equation3281_4512_implies_Equation3284 (G : Type*) [Magma G]
    (h3281 : Equation3281 G) (h4512 : Equation4512 G) : Equation3284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h3281 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = (X2 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq33 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq46 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq17 eq11 -- superposition 11,17
  have eq54 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq12 eq46 -- forward demodulation 46,12
  have eq55 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq33 eq54 -- forward demodulation 54,33
  have eq76 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq55 eq12 -- superposition 12,55
  have eq85 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq12 eq76 -- forward demodulation 76,12
  have eq86 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq85 eq18 -- backward demodulation 18,85
  have eq340 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq86 -- superposition 86,12
  have eq447 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq12 eq340 -- forward demodulation 340,12
  have eq863 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq11 eq14 -- superposition 14,11
  have eq991 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq85 eq863 -- forward demodulation 863,85
  have eq992 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq85 eq991 -- forward demodulation 991,85
  have eq993 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq85 eq992 -- forward demodulation 992,85
  have eq994 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq55 eq993 -- forward demodulation 993,55
  have eq1896 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ X1) := superpose eq55 eq994 -- superposition 994,55
  have eq5709 : (sK0 ◇ sK0) ≠ (sK2 ◇ (sK2 ◇ sK0)) := superpose eq447 eq13 -- superposition 13,447
  subsumption eq5709 eq1896

theorem Equation3284_4512_implies_Equation3296 (G : Type*) [Magma G]
    (h3284 : Equation3284 G) (h4512 : Equation4512 G) : Equation3296 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h3284 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq11 eq16 -- forward demodulation 16,11
  have eq36 (X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = (((X2 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) := superpose eq17 eq17 -- superposition 17,17
  have eq40 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq17 -- superposition 17,12
  have eq60 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X3)) = (((X2 ◇ X1) ◇ (X2 ◇ X1)) ◇ X3) := superpose eq17 eq12 -- superposition 12,17
  have eq65 (X1 X3 : G) : (X1 ◇ X1) = (X3 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq19 eq36 -- forward demodulation 36,19
  have eq66 (X1 X3 : G) : (X1 ◇ X1) = (X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq12 eq65 -- forward demodulation 65,12
  have eq67 (X1 X3 : G) : (X1 ◇ X1) = (X3 ◇ (X1 ◇ X1)) := superpose eq11 eq66 -- forward demodulation 66,11
  have eq74 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq67 eq40 -- forward demodulation 40,67
  have eq96 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X3)) = ((X2 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3) := superpose eq12 eq60 -- forward demodulation 60,12
  have eq97 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X3) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := superpose eq74 eq96 -- forward demodulation 96,74
  have eq98 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := superpose eq12 eq97 -- forward demodulation 97,12
  have eq266 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq98 -- superposition 98,11
  have eq302 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq266 eq13 -- backward demodulation 13,266
  subsumption eq302 eq67


/- Equivalence of [316, 317, 320, 3270, 3272, 3276, 3279, 3280, 3283, 3285, 3287, 3293, 3298, 3299, 3303] -/
theorem Equation3303_4512_implies_Equation316 (G : Type*) [Magma G]
    (h3303 : Equation3303 G) (_ : Equation4512 G) : Equation316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ X3))) := mod_symm (h3303 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq18 (X2 X3 X4 : G) : (X3 ◇ X3) = (X4 ◇ (X2 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X3 X4 : G) : (X3 ◇ X3) = (X4 ◇ X4) := superpose eq11 eq11 -- superposition 11,11
  have eq30 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq20 eq13 -- superposition 13,20
  subsumption eq30 eq18

theorem Equation316_4512_implies_Equation317 (G : Type*) [Magma G]
    (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation317 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := mod_symm (h316 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq16 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq27 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ X2) := superpose eq16 eq12 -- superposition 12,16
  have eq278 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X0) := superpose eq11 eq27 -- superposition 27,11
  have eq486 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq278 -- superposition 278,12
  have eq805 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq486 eq13 -- superposition 13,486
  subsumption eq805 eq16

theorem Equation317_4512_implies_Equation320 (G : Type*) [Magma G]
    (h317 : Equation317 G) (_ : Equation4512 G) : Equation320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X2)) := mod_symm (h317 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq16 (X0 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq24 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq17 eq13 -- superposition 13,17
  subsumption eq24 eq16

theorem Equation320_4512_implies_Equation3270 (G : Type*) [Magma G]
    (h320 : Equation320 G) (h4512 : Equation4512 G) : Equation3270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ X2)) := mod_symm (h320 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq18 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq34 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ X2) := superpose eq18 eq12 -- superposition 12,18
  have eq168 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X0) := superpose eq11 eq34 -- superposition 34,11
  have eq365 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq168 -- superposition 168,12
  have eq657 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq365 eq13 -- superposition 13,365
  subsumption eq657 eq11

theorem Equation3270_4512_implies_Equation3272 (G : Type*) [Magma G]
    (h3270 : Equation3270 G) (_ : Equation4512 G) : Equation3272 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := mod_symm (h3270 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq14 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq15 eq14 -- backward demodulation 14,15
  have eq17 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq15 eq13 -- backward demodulation 13,15
  subsumption eq17 eq16

theorem Equation3272_4512_implies_Equation3276 (G : Type*) [Magma G]
    (h3272 : Equation3272 G) (h4512 : Equation4512 G) : Equation3276 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h3272 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq19 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq18 -- forward demodulation 18,11
  have eq20 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq42 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq11 eq19 -- superposition 19,11
  have eq45 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq19 eq11 -- superposition 11,19
  have eq48 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq12 eq42 -- forward demodulation 42,12
  have eq49 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq48 eq20 -- backward demodulation 20,48
  have eq148 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) := superpose eq45 eq45 -- superposition 45,45
  have eq155 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq45 eq11 -- superposition 11,45
  have eq159 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq45 eq49 -- superposition 49,45
  have eq184 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))))) := superpose eq12 eq148 -- forward demodulation 148,12
  have eq185 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) := superpose eq15 eq184 -- forward demodulation 184,15
  have eq186 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq12 eq185 -- forward demodulation 185,12
  have eq187 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq48 eq186 -- forward demodulation 186,48
  have eq188 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq187 eq13 -- backward demodulation 13,187
  have eq189 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) := superpose eq12 eq155 -- forward demodulation 155,12
  have eq193 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq12 eq159 -- forward demodulation 159,12
  have eq194 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq15 eq193 -- forward demodulation 193,15
  have eq197 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq194 eq189 -- backward demodulation 189,194
  have eq200 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq197 eq48 -- backward demodulation 48,197
  have eq201 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose eq200 eq11 -- backward demodulation 11,200
  have eq282 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq201 eq201 -- superposition 201,201
  have eq316 (X0 : G) : (X0 ◇ X0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq282 eq188 -- superposition 188,282
  subsumption eq316 eq200

theorem Equation3276_4512_implies_Equation3279 (G : Type*) [Magma G]
    (h3276 : Equation3276 G) (h4512 : Equation4512 G) : Equation3279 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X2))) := mod_symm (h3276 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq25 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X1 ◇ X1)) := superpose eq11 eq24 -- forward demodulation 24,11
  have eq39 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq25 eq25 -- superposition 25,25
  have eq102 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ X2) := superpose eq39 eq12 -- superposition 12,39
  have eq687 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X0) := superpose eq25 eq102 -- superposition 102,25
  have eq1123 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq687 -- superposition 687,12
  have eq1674 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq1123 eq13 -- superposition 13,1123
  subsumption eq1674 eq39

theorem Equation3279_4512_implies_Equation3280 (G : Type*) [Magma G]
    (h3279 : Equation3279 G) (h4512 : Equation4512 G) : Equation3280 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3279 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = ((X1 ◇ X1) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq28 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq12 eq20 -- forward demodulation 20,12
  have eq29 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq12 eq28 -- forward demodulation 28,12
  have eq116 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X3)) = (((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X1 ◇ X0)) ◇ X3) := superpose eq19 eq19 -- superposition 19,19
  have eq192 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X3)) = ((X2 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0))) ◇ X3) := superpose eq12 eq116 -- forward demodulation 116,12
  have eq193 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X3)) = ((X2 ◇ (X2 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X0)))) ◇ X3) := superpose eq12 eq192 -- forward demodulation 192,12
  have eq194 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X3)) = ((X2 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0))))) ◇ X3) := superpose eq12 eq193 -- forward demodulation 193,12
  have eq283 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ X0) ◇ (X3 ◇ X2)))) = ((X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) ◇ X2) := superpose eq29 eq29 -- superposition 29,29
  have eq306 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X1) = (X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))))) := superpose eq11 eq29 -- superposition 29,11
  have eq356 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = (X3 ◇ (X3 ◇ ((X0 ◇ X0) ◇ (X3 ◇ X2)))) := superpose eq194 eq283 -- forward demodulation 283,194
  have eq357 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X2))))) := superpose eq12 eq356 -- forward demodulation 356,12
  have eq358 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ X1)) := superpose eq357 eq15 -- backward demodulation 15,357
  have eq459 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X1) = (X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq358 eq306 -- forward demodulation 306,358
  have eq652 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq358 -- superposition 358,11
  have eq750 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq652 eq652 -- superposition 652,652
  have eq759 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq652 eq11 -- superposition 11,652
  have eq768 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq652 eq358 -- superposition 358,652
  have eq788 (X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = ((X2 ◇ (X2 ◇ X2)) ◇ X1) := superpose eq759 eq459 -- backward demodulation 459,759
  have eq854 (X1 X2 : G) : (X2 ◇ X2) = ((X2 ◇ X2) ◇ X1) := superpose eq768 eq788 -- backward demodulation 788,768
  have eq1332 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq854 -- superposition 854,12
  have eq3410 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq1332 eq13 -- superposition 13,1332
  subsumption eq3410 eq750

theorem Equation3280_4512_implies_Equation3283 (G : Type*) [Magma G]
    (h3280 : Equation3280 G) (_ : Equation4512 G) : Equation3283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h3280 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq16 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X3 ◇ (X1 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq19 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq11 eq13 -- superposition 13,11
  have eq74 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq11 eq16 -- superposition 16,11
  have eq114 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq74 eq19 -- superposition 19,74
  subsumption eq114 eq74

theorem Equation3283_4512_implies_Equation3285 (G : Type*) [Magma G]
    (h3283 : Equation3283 G) (h4512 : Equation4512 G) : Equation3285 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := mod_symm (h3283 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq17 (X0 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq29 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ X2) := superpose eq18 eq12 -- superposition 12,18
  have eq145 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X0) := superpose eq17 eq29 -- superposition 29,17
  have eq316 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ X2) := superpose eq12 eq145 -- superposition 145,12
  have eq560 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq316 eq13 -- superposition 13,316
  subsumption eq560 eq18

theorem Equation3285_4512_implies_Equation3287 (G : Type*) [Magma G]
    (h3285 : Equation3285 G) (h4512 : Equation4512 G) : Equation3287 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := mod_symm (h3285 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq17 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq30 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ X2) := superpose eq17 eq12 -- superposition 12,17
  have eq42 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq109 (X0 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq11 eq42 -- superposition 42,11
  have eq272 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X0) := superpose eq109 eq30 -- superposition 30,109
  have eq510 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq272 -- superposition 272,12
  have eq940 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq510 eq13 -- superposition 13,510
  subsumption eq940 eq17

theorem Equation3287_4512_implies_Equation3293 (G : Type*) [Magma G]
    (h3287 : Equation3287 G) (_ : Equation4512 G) : Equation3293 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h3287 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq17 (X0 X3 X4 : G) : (X4 ◇ X4) = (X0 ◇ (X3 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq89 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq17 eq13 -- superposition 13,17
  subsumption eq89 eq17

theorem Equation3293_4512_implies_Equation3298 (G : Type*) [Magma G]
    (h3293 : Equation3293 G) (_ : Equation4512 G) : Equation3298 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X1 ◇ X1))) := mod_symm (h3293 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq18 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq28 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ X1)) := superpose eq18 eq11 -- superposition 11,18
  have eq88 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq28 eq13 -- superposition 13,28
  subsumption eq88 eq28

theorem Equation3298_4512_implies_Equation3299 (G : Type*) [Magma G]
    (h3298 : Equation3298 G) (h4512 : Equation4512 G) : Equation3299 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X2 ◇ X2))) := mod_symm (h3298 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq18 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq30 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq18 eq11 -- superposition 11,18
  have eq36 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ X2) := superpose eq18 eq12 -- superposition 12,18
  have eq71 (X2 X3 X4 : G) : (X3 ◇ X3) = (X4 ◇ (X2 ◇ X2)) := superpose eq30 eq30 -- superposition 30,30
  have eq337 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X0) := superpose eq71 eq36 -- superposition 36,71
  have eq600 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq337 -- superposition 337,12
  have eq976 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq600 eq13 -- superposition 13,600
  subsumption eq976 eq71

theorem Equation3299_4512_implies_Equation3303 (G : Type*) [Magma G]
    (h3299 : Equation3299 G) (_ : Equation4512 G) : Equation3303 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X2 ◇ X3))) := mod_symm (h3299 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3))) := mod_symm nh
  have eq17 (X0 X3 X4 X5 : G) : (X4 ◇ X4) = (X5 ◇ (X0 ◇ (X3 ◇ X3))) := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X3 X4 : G) : (X3 ◇ X3) = (X4 ◇ X4) := superpose eq11 eq11 -- superposition 11,11
  have eq32 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (X0 ◇ X0))) := superpose eq19 eq13 -- superposition 13,19
  subsumption eq32 eq17


/- Equivalence of [325, 3318] -/
theorem Equation3318_4512_implies_Equation325 (G : Type*) [Magma G]
    (h3318 : Equation3318 G) (h4512 : Equation4512 G) : Equation325 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h3318 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq22 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq12 eq19 -- forward demodulation 19,12
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq12 eq25 -- forward demodulation 25,12
  have eq27 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq12 eq26 -- forward demodulation 26,12
  have eq31 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq69 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq27 eq27 -- superposition 27,27
  have eq87 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq27 eq69 -- forward demodulation 69,27
  have eq88 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq87 eq31 -- backward demodulation 31,87
  have eq133 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq88 -- superposition 88,11
  have eq186 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq133 eq27 -- superposition 27,133
  have eq202 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose eq11 eq186 -- forward demodulation 186,11
  have eq451 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq202 eq13 -- superposition 13,202
  subsumption eq451 rfl

theorem Equation325_4512_implies_Equation3318 (G : Type*) [Magma G]
    (h325 : Equation325 G) (h4512 : Equation4512 G) : Equation3318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h325 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq19 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12
  have eq21 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq79 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq19 eq13 -- superposition 13,19
  have eq118 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose eq11 eq22 -- superposition 22,11
  have eq137 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq11 eq118 -- forward demodulation 118,11
  have eq246 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq137 eq79 -- superposition 79,137
  subsumption eq246 rfl


/- Equivalence of [327, 3317, 3320, 3321, 3324] -/
theorem Equation3324_4512_implies_Equation327 (G : Type*) [Magma G]
    (h3324 : Equation3324 G) (_ : Equation4512 G) : Equation327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := mod_symm (h3324 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq15 (X0 X1 X4 : G) : (X4 ◇ X0) = (X4 ◇ (X0 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq23 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq13 -- superposition 13,15
  subsumption eq23 rfl

theorem Equation327_4512_implies_Equation3317 (G : Type*) [Magma G]
    (h327 : Equation327 G) (_ : Equation4512 G) : Equation3317 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h327 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3317_4512_implies_Equation3320 (G : Type*) [Magma G]
    (h3317 : Equation3317 G) (h4512 : Equation4512 G) : Equation3320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h3317 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = ((X0 ◇ X1) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq34 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq35 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) := superpose eq12 eq34 -- forward demodulation 34,12
  have eq36 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) := superpose eq12 eq35 -- forward demodulation 35,12
  have eq37 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X3)) := superpose eq11 eq36 -- forward demodulation 36,11
  have eq42 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq37 eq13 -- backward demodulation 13,37
  subsumption eq42 eq37

theorem Equation3320_4512_implies_Equation3321 (G : Type*) [Magma G]
    (h3320 : Equation3320 G) (h4512 : Equation4512 G) : Equation3321 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := mod_symm (h3320 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq25 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = ((X0 ◇ X1) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq35 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := superpose eq12 eq25 -- forward demodulation 25,12
  have eq36 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq12 eq35 -- forward demodulation 35,12
  have eq37 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq36 -- forward demodulation 36,12
  have eq38 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X3)) := superpose eq11 eq37 -- forward demodulation 37,11
  have eq41 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq38 eq13 -- backward demodulation 13,38
  subsumption eq41 eq38

theorem Equation3321_4512_implies_Equation3324 (G : Type*) [Magma G]
    (h3321 : Equation3321 G) (h4512 : Equation4512 G) : Equation3324 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h3321 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq22 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq11 -- superposition 11,12
  have eq31 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ X0) := superpose eq22 eq23 -- forward demodulation 23,22
  have eq38 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq31 eq13 -- backward demodulation 13,31
  subsumption eq38 eq31


/- Equivalence of [329, 3312, 3330, 3338] -/
theorem Equation3338_4512_implies_Equation329 (G : Type*) [Magma G]
    (h3338 : Equation3338 G) (h4512 : Equation4512 G) : Equation329 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X3 ◇ X1))) := mod_symm (h3338 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq20 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X2) = (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq27 (X2 X3 X4 : G) : (X3 ◇ X2) = (X3 ◇ (X4 ◇ X2)) := superpose eq11 eq20 -- forward demodulation 20,11
  have eq43 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq27 eq13 -- superposition 13,27
  subsumption eq43 rfl

theorem Equation329_4512_implies_Equation3312 (G : Type*) [Magma G]
    (h329 : Equation329 G) (_ : Equation4512 G) : Equation3312 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X1)) := mod_symm (h329 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq15 eq11

theorem Equation3312_4512_implies_Equation3330 (G : Type*) [Magma G]
    (h3312 : Equation3312 G) (h4512 : Equation4512 G) : Equation3330 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h3312 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = ((X0 ◇ X2) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq23 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = (X0 ◇ (X2 ◇ X3)) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq25 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X2 ◇ X3)) := superpose eq11 eq24 -- forward demodulation 24,11
  have eq30 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK1)) := superpose eq25 eq13 -- backward demodulation 13,25
  subsumption eq30 eq25

theorem Equation3330_4512_implies_Equation3338 (G : Type*) [Magma G]
    (h3330 : Equation3330 G) (_ : Equation4512 G) : Equation3338 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X1))) := mod_symm (h3330 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK1))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := superpose eq15 eq13 -- backward demodulation 13,15
  subsumption eq20 eq11


/- Equivalence of [332, 335, 3345, 3352] -/
theorem Equation3352_4512_implies_Equation332 (G : Type*) [Magma G]
    (h3352 : Equation3352 G) (h4512 : Equation4512 G) : Equation332 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h3352 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq16 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq15 -- forward demodulation 15,11
  have eq34 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq12 eq16 -- superposition 16,12
  have eq41 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq34 -- forward demodulation 34,11
  have eq42 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq41 eq16 -- backward demodulation 16,41
  have eq67 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ X1) := superpose eq42 eq11 -- superposition 11,42
  have eq70 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq67 -- forward demodulation 67,12
  have eq71 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq70 -- forward demodulation 70,11
  have eq80 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ X0) := superpose eq11 eq71 -- superposition 71,11
  have eq234 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq80 eq13 -- superposition 13,80
  subsumption eq234 rfl

theorem Equation332_4512_implies_Equation335 (G : Type*) [Magma G]
    (h332 : Equation332 G) (h4512 : Equation4512 G) : Equation335 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h332 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
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
  have eq59 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq49 eq13 -- backward demodulation 13,49
  have eq125 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq40 eq59 -- superposition 59,40
  subsumption eq125 eq22

theorem Equation335_4512_implies_Equation3345 (G : Type*) [Magma G]
    (h335 : Equation335 G) (h4512 : Equation4512 G) : Equation3345 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h335 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = ((X1 ◇ X0) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq21 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq12 eq20 -- forward demodulation 20,12
  have eq29 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq11 eq21 -- superposition 21,11
  have eq45 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq29 eq13 -- backward demodulation 13,29
  subsumption eq45 eq11

theorem Equation3345_4512_implies_Equation3352 (G : Type*) [Magma G]
    (h3345 : Equation3345 G) (h4512 : Equation4512 G) : Equation3352 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h3345 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq16 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq18 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq12 eq17 -- forward demodulation 17,12
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq11 eq18 -- forward demodulation 18,11
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = ((X1 ◇ X0) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq22 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq12 eq11 -- superposition 11,12
  have eq26 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq12 eq20 -- forward demodulation 20,12
  have eq27 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq12 eq26 -- forward demodulation 26,12
  have eq28 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq27 -- forward demodulation 27,12
  have eq31 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X2 ◇ X0)) := superpose eq31 eq24 -- forward demodulation 24,31
  have eq37 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X0)) := superpose eq12 eq32 -- superposition 32,12
  have eq38 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)) := superpose eq11 eq32 -- superposition 32,11
  have eq45 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := superpose eq37 eq13 -- backward demodulation 13,37
  have eq46 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) := superpose eq12 eq38 -- forward demodulation 38,12
  have eq47 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))) := superpose eq12 eq46 -- forward demodulation 46,12
  have eq48 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq37 eq47 -- forward demodulation 47,37
  have eq49 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq12 eq48 -- forward demodulation 48,12
  have eq59 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq11 eq19 -- superposition 19,11
  have eq62 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))))) := superpose eq12 eq19 -- superposition 19,12
  have eq70 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0))) := superpose eq32 eq19 -- superposition 19,32
  have eq71 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)))))) := superpose eq12 eq19 -- superposition 19,12
  have eq79 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))))) := superpose eq37 eq59 -- forward demodulation 59,37
  have eq80 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))))) := superpose eq37 eq79 -- forward demodulation 79,37
  have eq81 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))))) := superpose eq37 eq80 -- forward demodulation 80,37
  have eq82 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))))) := superpose eq12 eq81 -- forward demodulation 81,12
  have eq83 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))))) := superpose eq12 eq82 -- forward demodulation 82,12
  have eq84 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))))) := superpose eq11 eq83 -- forward demodulation 83,11
  have eq95 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))))))) := superpose eq12 eq62 -- forward demodulation 62,12
  have eq96 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))))))) := superpose eq37 eq95 -- forward demodulation 95,37
  have eq97 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))))))) := superpose eq37 eq96 -- forward demodulation 96,37
  have eq98 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))))))) := superpose eq12 eq97 -- forward demodulation 97,12
  have eq99 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq49 eq98 -- forward demodulation 98,49
  have eq100 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq28 eq99 -- forward demodulation 99,28
  have eq102 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))))) := superpose eq100 eq84 -- backward demodulation 84,100
  have eq106 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) := superpose eq100 eq31 -- backward demodulation 31,100
  have eq108 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq49 eq102 -- forward demodulation 102,49
  have eq130 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X2 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)))) := superpose eq12 eq70 -- forward demodulation 70,12
  have eq131 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))))) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq132 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)))))) := superpose eq37 eq131 -- forward demodulation 131,37
  have eq133 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))))) := superpose eq12 eq132 -- forward demodulation 132,12
  have eq134 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))))) := superpose eq12 eq133 -- forward demodulation 133,12
  have eq135 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))))) := superpose eq28 eq134 -- forward demodulation 134,28
  have eq136 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) := superpose eq106 eq135 -- forward demodulation 135,106
  have eq142 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) := superpose eq100 eq71 -- forward demodulation 71,100
  have eq143 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) := superpose eq37 eq142 -- forward demodulation 142,37
  have eq144 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0))))) := superpose eq11 eq143 -- forward demodulation 143,11
  have eq145 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq106 eq144 -- forward demodulation 144,106
  have eq146 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq145 eq136 -- backward demodulation 136,145
  have eq151 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq146 eq106 -- backward demodulation 106,146
  have eq268 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq11 eq151 -- superposition 151,11
  have eq273 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose eq11 eq151 -- superposition 151,11
  have eq295 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq273 eq11 -- backward demodulation 11,273
  have eq297 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq273 eq108 -- backward demodulation 108,273
  have eq305 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq273 eq297 -- forward demodulation 297,273
  have eq306 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose eq305 eq268 -- backward demodulation 268,305
  have eq314 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq306 eq45 -- backward demodulation 45,306
  subsumption eq314 eq295


/- Equivalence of [333, 3343] -/
theorem Equation3343_4512_implies_Equation333 (G : Type*) [Magma G]
    (h3343 : Equation3343 G) (h4512 : Equation4512 G) : Equation333 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := mod_symm (h3343 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = ((X1 ◇ X0) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq11 eq12 -- superposition 12,11
  have eq22 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq67 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq14 -- superposition 14,12
  have eq85 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq12 eq67 -- forward demodulation 67,12
  have eq86 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq24 eq85 -- forward demodulation 85,24
  have eq114 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X0)))) := superpose eq11 eq24 -- superposition 24,11
  have eq123 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq14 eq24 -- superposition 24,14
  have eq135 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq114 eq18 -- backward demodulation 18,114
  have eq151 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq12 eq123 -- forward demodulation 123,12
  have eq152 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq135 eq151 -- forward demodulation 151,135
  have eq153 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq152 -- forward demodulation 152,12
  have eq154 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq86 eq153 -- forward demodulation 153,86
  have eq203 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq154 eq13 -- superposition 13,154
  subsumption eq203 rfl

theorem Equation333_4512_implies_Equation3343 (G : Type*) [Magma G]
    (h333 : Equation333 G) (h4512 : Equation4512 G) : Equation3343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h333 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq14 -- superposition 14,12
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq28 -- forward demodulation 28,11
  have eq33 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq32 eq13 -- backward demodulation 13,32
  subsumption eq33 eq11


/- Equivalence of [343, 3363, 3380, 3397, 3431] -/
theorem Equation3431_4512_implies_Equation343 (G : Type*) [Magma G]
    (h3431 : Equation3431 G) (h4512 : Equation4512 G) : Equation343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := mod_symm (h3431 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq18 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) := superpose eq11 eq12 -- superposition 12,11
  have eq27 (X0 X3 X4 : G) : (X3 ◇ X4) = (X0 ◇ (X3 ◇ X4)) := superpose eq11 eq18 -- forward demodulation 18,11
  have eq41 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq27 eq13 -- superposition 13,27
  subsumption eq41 rfl

theorem Equation343_4512_implies_Equation3363 (G : Type*) [Magma G]
    (h343 : Equation343 G) (_ : Equation4512 G) : Equation3363 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := mod_symm (h343 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq15 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq15 eq11

theorem Equation3363_4512_implies_Equation3380 (G : Type*) [Magma G]
    (h3363 : Equation3363 G) (h4512 : Equation4512 G) : Equation3380 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X0 ◇ X1))) := mod_symm (h3363 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq11 -- superposition 11,12
  have eq28 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := superpose eq20 eq19 -- backward demodulation 19,20
  have eq36 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK1)) := superpose eq28 eq13 -- backward demodulation 13,28
  subsumption eq36 eq28

theorem Equation3380_4512_implies_Equation3397 (G : Type*) [Magma G]
    (h3380 : Equation3380 G) (_ : Equation4512 G) : Equation3397 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := mod_symm (h3380 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq16 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := superpose eq15 eq13 -- backward demodulation 13,15
  subsumption eq16 eq11

theorem Equation3397_4512_implies_Equation3431 (G : Type*) [Magma G]
    (h3397 : Equation3397 G) (_ : Equation4512 G) : Equation3431 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h3397 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq19 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) := superpose eq15 eq13 -- backward demodulation 13,15
  subsumption eq19 eq11


/- Equivalence of [419, 436] -/
theorem Equation436_4512_implies_Equation419 (G : Type*) [Magma G]
    (h436 : Equation436 G) (h4512 : Equation4512 G) : Equation419 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h436 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2)) = (X0 ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq21 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2)))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq23 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2))))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq33 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq23 -- superposition 23,11
  have eq42 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq33 eq13 -- backward demodulation 13,33
  subsumption eq42 eq11

theorem Equation419_4512_implies_Equation436 (G : Type*) [Magma G]
    (h419 : Equation419 G) (h4512 : Equation4512 G) : Equation436 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h419 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq21 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2)) = (X0 ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))))) = X2 := superpose eq12 eq11 -- superposition 11,12
  have eq28 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq29 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq12 eq28 -- forward demodulation 28,12
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq12 eq29 -- forward demodulation 29,12
  have eq34 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) = X2 := superpose eq12 eq24 -- forward demodulation 24,12
  have eq81 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq34 -- superposition 34,11
  have eq90 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) := superpose eq34 eq30 -- superposition 30,34
  have eq461 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq81 eq90 -- superposition 90,81
  have eq489 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := superpose eq461 eq13 -- backward demodulation 13,461
  have eq539 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq90 eq489 -- superposition 489,90
  subsumption eq539 eq81


/- Equivalence of [477, 511] -/
theorem Equation511_4512_implies_Equation477 (G : Type*) [Magma G]
    (h511 : Equation511 G) (h4512 : Equation4512 G) : Equation477 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h511 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq14 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1))) = X0 := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)))) = X0 := superpose eq12 eq14 -- forward demodulation 14,12
  have eq16 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1))))) = X0 := superpose eq12 eq15 -- forward demodulation 15,12
  have eq17 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)))))) = X0 := superpose eq12 eq16 -- forward demodulation 16,12
  have eq18 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))))))) = X0 := superpose eq12 eq17 -- forward demodulation 17,12
  have eq19 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))))))) = X0 := superpose eq12 eq18 -- forward demodulation 18,12
  have eq20 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))))) = X0 := superpose eq12 eq19 -- forward demodulation 19,12
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq23 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))))) = X2 := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq12 eq11 -- superposition 11,12
  have eq28 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq12 eq28 -- forward demodulation 28,12
  have eq30 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq12 eq29 -- forward demodulation 29,12
  have eq31 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = X0 := superpose eq30 eq20 -- backward demodulation 20,30
  have eq34 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))))) = X2 := superpose eq12 eq23 -- forward demodulation 23,12
  have eq35 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))))) = X2 := superpose eq12 eq34 -- forward demodulation 34,12
  have eq107 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq30 -- superposition 30,11
  have eq108 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq24 eq30 -- superposition 30,24
  have eq363 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := superpose eq107 eq11 -- superposition 11,107
  have eq446 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))))) = X0 := superpose eq107 eq35 -- superposition 35,107
  have eq1496 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq107 eq363 -- superposition 363,107
  have eq1545 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq363 eq1496 -- forward demodulation 1496,363
  have eq1967 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X2))) := superpose eq31 eq108 -- superposition 108,31
  have eq2018 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0)))) := superpose eq108 eq30 -- superposition 30,108
  have eq2171 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X2)))) := superpose eq12 eq1967 -- forward demodulation 1967,12
  have eq2172 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X2))))) := superpose eq12 eq2171 -- forward demodulation 2171,12
  have eq2173 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X2)))))) := superpose eq12 eq2172 -- forward demodulation 2172,12
  have eq2174 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2))))))) := superpose eq12 eq2173 -- forward demodulation 2173,12
  have eq2175 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)))))))) := superpose eq12 eq2174 -- forward demodulation 2174,12
  have eq2176 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))))))))) := superpose eq12 eq2175 -- forward demodulation 2175,12
  have eq2177 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))))))))) := superpose eq12 eq2176 -- forward demodulation 2176,12
  have eq2273 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2))))) := superpose eq1545 eq2018 -- forward demodulation 2018,1545
  have eq2280 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))))) := superpose eq2273 eq2177 -- backward demodulation 2177,2273
  have eq2284 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := superpose eq2280 eq446 -- backward demodulation 446,2280
  have eq8299 : sK0 ≠ sK0 := superpose eq2284 eq13 -- superposition 13,2284
  subsumption eq8299 rfl

theorem Equation477_4512_implies_Equation511 (G : Type*) [Magma G]
    (h477 : Equation477 G) (h4512 : Equation4512 G) : Equation511 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h477 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2)))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2))))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq76 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq11 eq23 -- superposition 23,11
  have eq80 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := superpose eq11 eq23 -- superposition 23,11
  have eq97 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := superpose eq80 eq13 -- backward demodulation 13,80
  have eq98 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := superpose eq76 eq97 -- forward demodulation 97,76
  subsumption eq98 eq11


/- Equivalence of [3273, 3295] -/
theorem Equation3295_4512_implies_Equation3273 (G : Type*) [Magma G]
    (h3295 : Equation3295 G) (_ : Equation4512 G) : Equation3273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := mod_symm (h3295 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3273_4512_implies_Equation3295 (G : Type*) [Magma G]
    (h3273 : Equation3273 G) (_ : Equation4512 G) : Equation3295 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := mod_symm (h3273 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) := mod_symm nh
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq19 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq11 eq13 -- superposition 13,11
  have eq47 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq17 eq17 -- superposition 17,17
  have eq125 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq47 eq19 -- superposition 19,47
  subsumption eq125 eq47


/- Equivalence of [3275, 3289, 3301] -/
theorem Equation3301_4512_implies_Equation3275 (G : Type*) [Magma G]
    (h3301 : Equation3301 G) (_ : Equation4512 G) : Equation3275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := mod_symm (h3301 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3275_4512_implies_Equation3289 (G : Type*) [Magma G]
    (h3275 : Equation3275 G) (h4512 : Equation4512 G) : Equation3289 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h3275 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq19 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq11 eq13 -- superposition 13,11
  have eq27 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq59 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := superpose eq17 eq11 -- superposition 11,17
  have eq93 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq27 -- superposition 27,11
  have eq150 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq11 eq93 -- superposition 93,11
  have eq178 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ (X1 ◇ X1)) := superpose eq150 eq59 -- backward demodulation 59,150
  have eq179 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq178 eq16 -- backward demodulation 16,178
  have eq262 (X3 X4 : G) : (X3 ◇ X3) = (X4 ◇ X4) := superpose eq179 eq179 -- superposition 179,179
  have eq382 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq262 eq19 -- superposition 19,262
  subsumption eq382 eq262

theorem Equation3289_4512_implies_Equation3301 (G : Type*) [Magma G]
    (h3289 : Equation3289 G) (_ : Equation4512 G) : Equation3301 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ X1))) := mod_symm (h3289 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1))) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11
  have eq19 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq11 eq13 -- superposition 13,11
  have eq49 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq17 eq17 -- superposition 17,17
  have eq168 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq49 eq19 -- superposition 19,49
  subsumption eq168 eq49


/- Equivalence of [3277, 3291, 3304] -/
theorem Equation3304_4512_implies_Equation3277 (G : Type*) [Magma G]
    (h3304 : Equation3304 G) (_ : Equation4512 G) : Equation3277 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ X4))) := mod_symm (h3304 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3277_4512_implies_Equation3291 (G : Type*) [Magma G]
    (h3277 : Equation3277 G) (_ : Equation4512 G) : Equation3291 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := mod_symm (h3277 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK3))) := mod_symm nh
  have eq18 (X0 X1 X4 : G) : (X0 ◇ X0) = (X4 ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq21 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq11 eq13 -- superposition 13,11
  have eq51 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq18 eq18 -- superposition 18,18
  have eq164 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq51 eq21 -- superposition 21,51
  subsumption eq164 eq51

theorem Equation3291_4512_implies_Equation3304 (G : Type*) [Magma G]
    (h3291 : Equation3291 G) (_ : Equation4512 G) : Equation3304 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ X3))) := mod_symm (h3291 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK4))) := mod_symm nh
  have eq18 (X1 X2 X4 : G) : (X1 ◇ X1) = (X4 ◇ (X2 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11
  have eq21 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq11 eq13 -- superposition 13,11
  have eq52 (X1 X3 : G) : (X1 ◇ X1) = (X3 ◇ X3) := superpose eq11 eq18 -- superposition 18,11
  have eq155 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq52 eq21 -- superposition 21,52
  subsumption eq155 eq52


/- Equivalence of [3290, 3302] -/
theorem Equation3302_4512_implies_Equation3290 (G : Type*) [Magma G]
    (h3302 : Equation3302 G) (_ : Equation4512 G) : Equation3290 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ X2))) := mod_symm (h3302 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := mod_symm nh
  subsumption eq13 eq11

theorem Equation3290_4512_implies_Equation3302 (G : Type*) [Magma G]
    (h3290 : Equation3290 G) (_ : Equation4512 G) : Equation3302 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ X2))) := mod_symm (h3290 ..)
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2))) := mod_symm nh
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq11 eq13 -- superposition 13,11
  have eq55 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq18 eq18 -- superposition 18,18
  have eq154 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq55 eq20 -- superposition 20,55
  subsumption eq154 eq55


/- Equivalence of [3342, 3355] -/
theorem Equation3355_4512_implies_Equation3342 (G : Type*) [Magma G]
    (h3355 : Equation3355 G) (h4512 : Equation4512 G) : Equation3342 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h3355 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X1 ◇ X0) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq22 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq40 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) := superpose eq14 eq12 -- superposition 12,14
  have eq41 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq14 eq11 -- superposition 11,14
  have eq68 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq12 eq40 -- forward demodulation 40,12
  have eq69 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq12 eq68 -- forward demodulation 68,12
  have eq70 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq12 eq69 -- forward demodulation 69,12
  have eq71 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq12 eq41 -- forward demodulation 41,12
  have eq72 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))))) := superpose eq12 eq71 -- forward demodulation 71,12
  have eq73 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))))) := superpose eq11 eq72 -- forward demodulation 72,11
  have eq74 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = (X2 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X0)))) := superpose eq11 eq24 -- superposition 24,11
  have eq75 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) = (X3 ◇ (X3 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq24 eq24 -- superposition 24,24
  have eq77 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) = (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq14 eq24 -- superposition 24,14
  have eq78 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq24 -- superposition 24,11
  have eq79 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq24 eq24 -- superposition 24,24
  have eq82 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose eq11 eq24 -- superposition 24,11
  have eq85 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ X2) ◇ X0) := superpose eq11 eq24 -- superposition 24,11
  have eq94 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq11 eq74 -- forward demodulation 74,11
  have eq95 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq12 eq94 -- forward demodulation 94,12
  have eq97 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq95 eq73 -- backward demodulation 73,95
  have eq100 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq12 eq97 -- forward demodulation 97,12
  have eq101 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq95 eq100 -- forward demodulation 100,95
  have eq102 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) = ((X1 ◇ (X0 ◇ X2)) ◇ X3) := superpose eq11 eq75 -- forward demodulation 75,11
  have eq103 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) = (X1 ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq12 eq102 -- forward demodulation 102,12
  have eq104 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := superpose eq12 eq103 -- forward demodulation 103,12
  have eq106 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) = (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq24 eq77 -- forward demodulation 77,24
  have eq107 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq78 eq14 -- backward demodulation 14,78
  have eq108 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq79 eq70 -- backward demodulation 70,79
  have eq151 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq11 eq107 -- superposition 107,11
  have eq156 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X0)))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) := superpose eq107 eq24 -- superposition 24,107
  have eq171 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq12 eq151 -- forward demodulation 151,12
  have eq177 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) := superpose eq11 eq156 -- forward demodulation 156,11
  have eq178 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) := superpose eq12 eq177 -- forward demodulation 177,12
  have eq179 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq178 eq106 -- backward demodulation 106,178
  have eq200 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq78 eq78 -- superposition 78,78
  have eq219 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq12 eq200 -- forward demodulation 200,12
  have eq220 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq12 eq219 -- forward demodulation 219,12
  have eq221 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq179 eq220 -- forward demodulation 220,179
  have eq360 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq12 eq82 -- superposition 82,12
  have eq641 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq12 eq85 -- superposition 85,12
  have eq799 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := superpose eq85 eq171 -- superposition 171,85
  have eq2186 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X3) = (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3)) := superpose eq95 eq12 -- superposition 12,95
  have eq2346 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X3) = (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3))) := superpose eq12 eq2186 -- forward demodulation 2186,12
  have eq2347 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3)))) := superpose eq12 eq2346 -- forward demodulation 2346,12
  have eq2348 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3))))) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq12 eq2347 -- forward demodulation 2347,12
  have eq2349 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3))))) := superpose eq12 eq2348 -- forward demodulation 2348,12
  have eq2350 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X3)) = (X2 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq104 eq2349 -- forward demodulation 2349,104
  have eq2351 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X3 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := superpose eq12 eq2350 -- forward demodulation 2350,12
  have eq2417 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq85 eq641 -- superposition 641,85
  have eq2680 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq107 eq101 -- superposition 101,107
  have eq2827 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq12 eq2680 -- forward demodulation 2680,12
  have eq2828 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq360 eq2827 -- forward demodulation 2827,360
  have eq2829 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq2351 eq2828 -- forward demodulation 2828,2351
  have eq2830 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq79 eq2829 -- forward demodulation 2829,79
  have eq2831 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq221 eq2830 -- forward demodulation 2830,221
  have eq5142 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq799 eq2831 -- superposition 2831,799
  have eq5153 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq11 eq2831 -- superposition 2831,11
  have eq5154 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq24 eq2831 -- superposition 2831,24
  have eq5327 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq108 eq178 -- superposition 178,108
  have eq5328 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X2 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq178 eq178 -- superposition 178,178
  have eq5399 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq178 eq108 -- superposition 108,178
  have eq5407 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq178 eq24 -- superposition 24,178
  have eq5554 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) = ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq5154 eq5327 -- forward demodulation 5327,5154
  have eq5555 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) = ((X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq2417 eq5554 -- forward demodulation 5554,2417
  have eq5556 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) = ((X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq12 eq5555 -- forward demodulation 5555,12
  have eq5557 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) = ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq12 eq5556 -- forward demodulation 5556,12
  have eq5558 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) = ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq11 eq5557 -- forward demodulation 5557,11
  have eq5559 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) = ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq12 eq5558 -- forward demodulation 5558,12
  have eq5560 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) = ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq12 eq5559 -- forward demodulation 5559,12
  have eq5561 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X3)))) = ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq12 eq5560 -- forward demodulation 5560,12
  have eq5562 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X3))))) = ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq12 eq5561 -- forward demodulation 5561,12
  have eq5563 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (X0 ◇ X2)) = ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq95 eq5562 -- forward demodulation 5562,95
  have eq5564 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X0 ◇ X2))) = ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq12 eq5563 -- forward demodulation 5563,12
  have eq5565 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq12 eq5328 -- forward demodulation 5328,12
  have eq5566 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) = ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq5154 eq5565 -- forward demodulation 5565,5154
  have eq5567 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) = ((X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq2417 eq5566 -- forward demodulation 5566,2417
  have eq5568 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) = ((X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq12 eq5567 -- forward demodulation 5567,12
  have eq5569 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) = ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq12 eq5568 -- forward demodulation 5568,12
  have eq5570 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) = ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq11 eq5569 -- forward demodulation 5569,11
  have eq5571 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) = ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq12 eq5570 -- forward demodulation 5570,12
  have eq5572 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X0 ◇ X2))) = (X2 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) := superpose eq5564 eq5571 -- forward demodulation 5571,5564
  have eq5573 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X0 ◇ X2))) = (X2 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X3)))) := superpose eq12 eq5572 -- forward demodulation 5572,12
  have eq5574 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X0 ◇ X2))) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X3))))) := superpose eq12 eq5573 -- forward demodulation 5573,12
  have eq5575 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X0 ◇ X2))) = (X2 ◇ ((X1 ◇ X3) ◇ X0)) := superpose eq11 eq5574 -- forward demodulation 5574,11
  have eq5576 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X0))) = (X1 ◇ (X3 ◇ (X0 ◇ X2))) := superpose eq12 eq5575 -- forward demodulation 5575,12
  have eq5771 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq12 eq5399 -- forward demodulation 5399,12
  have eq5772 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq5771 -- forward demodulation 5771,12
  have eq5773 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq11 eq5772 -- forward demodulation 5772,11
  have eq5774 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq11 eq5773 -- forward demodulation 5773,11
  have eq5775 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq5774 -- forward demodulation 5774,12
  have eq5797 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq5576 eq5407 -- forward demodulation 5407,5576
  have eq5798 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq95 eq5797 -- forward demodulation 5797,95
  have eq5799 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (X0 ◇ (X2 ◇ X1)) := superpose eq5775 eq5798 -- forward demodulation 5798,5775
  have eq5800 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ (X2 ◇ X1)) := superpose eq5153 eq5799 -- forward demodulation 5799,5153
  have eq5801 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X1)) := superpose eq11 eq5800 -- forward demodulation 5800,11
  have eq8103 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := superpose eq5801 eq13 -- superposition 13,5801
  have eq8377 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq5153 eq8103 -- forward demodulation 8103,5153
  subsumption eq8377 eq5142

theorem Equation3342_4512_implies_Equation3355 (G : Type*) [Magma G]
    (h3342 : Equation3342 G) (h4512 : Equation4512 G) : Equation3355 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h3342 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
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
  have eq81 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq31 -- superposition 31,11
  have eq109 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq81 -- forward demodulation 81,11
  have eq110 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := superpose eq109 eq13 -- backward demodulation 13,109
  have eq150 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := superpose eq31 eq110 -- superposition 110,31
  subsumption eq150 eq70


/- Equivalence of [3350, 3364, 3370, 3385, 3398, 3404, 3417] -/
theorem Equation3417_4512_implies_Equation3350 (G : Type*) [Magma G]
    (h3417 : Equation3417 G) (h4512 : Equation4512 G) : Equation3350 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X1 ◇ X0))) := mod_symm (h3417 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = (X3 ◇ (X3 ◇ (X2 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ X0) := superpose eq11 eq14 -- forward demodulation 14,11
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X1) ◇ (X2 ◇ X3)) := superpose eq12 eq12 -- superposition 12,12
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq11 eq12 -- superposition 12,11
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq26 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq27 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq12 eq19 -- forward demodulation 19,12
  have eq75 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X2 ◇ X1) ◇ X0) ◇ X0) := superpose eq15 eq16 -- superposition 16,15
  have eq90 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq12 eq75 -- forward demodulation 75,12
  have eq110 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = (X4 ◇ (X4 ◇ (X3 ◇ (X1 ◇ X2)))) := superpose eq16 eq20 -- superposition 20,16
  have eq111 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X2 ◇ X1))) = ((X1 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq11 eq20 -- superposition 20,11
  have eq141 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq11 eq110 -- forward demodulation 110,11
  have eq142 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq141 -- forward demodulation 141,12
  have eq143 (X0 X2 X3 : G) : (X3 ◇ X2) = (X0 ◇ (X2 ◇ (X3 ◇ X0))) := superpose eq142 eq27 -- backward demodulation 27,142
  have eq144 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq11 eq111 -- forward demodulation 111,11
  have eq186 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X2 ◇ X1)) := superpose eq11 eq143 -- superposition 143,11
  have eq1031 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq26 eq90 -- superposition 90,26
  have eq1728 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq144 eq186 -- superposition 186,144
  have eq2067 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (X0 ◇ X0))) := superpose eq1728 eq13 -- superposition 13,1728
  subsumption eq2067 eq1031

theorem Equation3350_4512_implies_Equation3364 (G : Type*) [Magma G]
    (h3350 : Equation3350 G) (h4512 : Equation4512 G) : Equation3364 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X2))) := mod_symm (h3350 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) = ((X1 ◇ X0) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) = (X1 ◇ (X0 ◇ X3)) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq25 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq26 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := superpose eq12 eq25 -- forward demodulation 25,12
  have eq27 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ (X3 ◇ X1)) := superpose eq17 eq26 -- forward demodulation 26,17
  have eq28 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := superpose eq27 eq13 -- backward demodulation 13,27
  subsumption eq28 eq11

theorem Equation3364_4512_implies_Equation3370 (G : Type*) [Magma G]
    (h3364 : Equation3364 G) (_ : Equation4512 G) : Equation3370 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X0 ◇ X2))) := mod_symm (h3364 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq45 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq13 -- superposition 13,15
  subsumption eq45 rfl

theorem Equation3370_4512_implies_Equation3385 (G : Type*) [Magma G]
    (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation3385 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X2 ◇ X0))) := mod_symm (h3370 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq18 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := superpose eq11 eq12 -- superposition 12,11
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq27 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq11 eq18 -- forward demodulation 18,11
  have eq28 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) := superpose eq27 eq19 -- forward demodulation 19,27
  have eq29 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq27 eq28 -- forward demodulation 28,27
  have eq30 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq12 eq29 -- forward demodulation 29,12
  have eq79 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq11 eq27 -- superposition 27,11
  have eq101 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := superpose eq27 eq13 -- superposition 13,27
  have eq113 (X1 X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq79 eq30 -- backward demodulation 30,79
  have eq115 (X1 X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq12 eq113 -- forward demodulation 113,12
  have eq129 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := superpose eq27 eq101 -- forward demodulation 101,27
  have eq579 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq115 eq79 -- superposition 79,115
  have eq816 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq579 eq79 -- superposition 79,579
  have eq833 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (X0 ◇ X0))) := superpose eq579 eq129 -- superposition 129,579
  subsumption eq833 eq816

theorem Equation3385_4512_implies_Equation3398 (G : Type*) [Magma G]
    (h3385 : Equation3385 G) (h4512 : Equation4512 G) : Equation3398 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := mod_symm (h3385 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq65 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq12 eq14 -- superposition 14,12
  have eq93 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) := superpose eq12 eq65 -- forward demodulation 65,12
  have eq94 (X0 X2 X3 : G) : (X3 ◇ X2) = (X0 ◇ (X2 ◇ (X3 ◇ X0))) := superpose eq20 eq93 -- forward demodulation 93,20
  have eq128 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq94 eq13 -- superposition 13,94
  subsumption eq128 rfl

theorem Equation3398_4512_implies_Equation3404 (G : Type*) [Magma G]
    (h3398 : Equation3398 G) (h4512 : Equation4512 G) : Equation3404 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h3398 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq18 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) := superpose eq11 eq12 -- superposition 12,11
  have eq19 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq11 -- superposition 11,12
  have eq27 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ X3)) := superpose eq12 eq19 -- forward demodulation 19,12
  have eq28 (X0 X2 X3 : G) : (X3 ◇ X2) = (X0 ◇ (X3 ◇ (X0 ◇ X2))) := superpose eq27 eq18 -- backward demodulation 18,27
  have eq60 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq11 eq28 -- superposition 28,11
  have eq73 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := superpose eq60 eq13 -- backward demodulation 13,60
  subsumption eq73 eq11

theorem Equation3404_4512_implies_Equation3417 (G : Type*) [Magma G]
    (h3404 : Equation3404 G) (h4512 : Equation4512 G) : Equation3417 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h3404 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X0) = (X1 ◇ (X2 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) := superpose eq11 eq12 -- superposition 12,11
  have eq20 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq12 eq11 -- superposition 11,12
  have eq26 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3))))) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq27 (X0 X2 X3 : G) : (X3 ◇ X2) = (X0 ◇ (X3 ◇ (X2 ◇ X0))) := superpose eq20 eq26 -- backward demodulation 26,20
  have eq38 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq12 eq15 -- superposition 15,12
  have eq39 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq15 eq15 -- superposition 15,15
  have eq57 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq27 eq38 -- forward demodulation 38,27
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq57 eq39 -- forward demodulation 39,57
  have eq75 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X0 ◇ (X3 ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq15 eq27 -- superposition 27,15
  have eq92 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq58 eq75 -- forward demodulation 75,58
  have eq93 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := superpose eq92 eq13 -- backward demodulation 13,92
  subsumption eq93 eq11


/- Equivalence of [4268, 4282, 4395] -/
theorem Equation4395_4512_implies_Equation4268 (G : Type*) [Magma G]
    (h4395 : Equation4395 G) (_ : Equation4512 G) : Equation4268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := mod_symm (h4395 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11
  have eq54 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq15 eq13 -- superposition 13,15
  subsumption eq54 eq15

theorem Equation4268_4512_implies_Equation4282 (G : Type*) [Magma G]
    (h4268 : Equation4268 G) (_ : Equation4512 G) : Equation4282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h4268 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation4282_4512_implies_Equation4395 (G : Type*) [Magma G]
    (h4282 : Equation4282 G) (h4512 : Equation4512 G) : Equation4395 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := mod_symm (h4282 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq14 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq14 eq11


/- Equivalence of [4269, 4316, 4432] -/
theorem Equation4432_4512_implies_Equation4269 (G : Type*) [Magma G]
    (h4432 : Equation4432 G) (_ : Equation4512 G) : Equation4269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := mod_symm (h4432 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq52 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq15 eq13 -- superposition 13,15
  subsumption eq52 eq15

theorem Equation4269_4512_implies_Equation4316 (G : Type*) [Magma G]
    (h4269 : Equation4269 G) (_ : Equation4512 G) : Equation4316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4269 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation4316_4512_implies_Equation4432 (G : Type*) [Magma G]
    (h4316 : Equation4316 G) (h4512 : Equation4512 G) : Equation4432 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := mod_symm (h4316 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq14 eq11


/- Equivalence of [4270, 4341, 4469] -/
theorem Equation4469_4512_implies_Equation4270 (G : Type*) [Magma G]
    (h4469 : Equation4469 G) (_ : Equation4512 G) : Equation4270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := mod_symm (h4469 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11
  have eq52 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq14 eq13 -- superposition 13,14
  subsumption eq52 eq14

theorem Equation4270_4512_implies_Equation4341 (G : Type*) [Magma G]
    (h4270 : Equation4270 G) (_ : Equation4512 G) : Equation4341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4270 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation4341_4512_implies_Equation4469 (G : Type*) [Magma G]
    (h4341 : Equation4341 G) (h4512 : Equation4512 G) : Equation4469 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := mod_symm (h4341 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq14 eq11


/- Equivalence of [4271, 4285, 4289, 4317, 4319, 4342, 4359, 4361, 4506, 4507, 4509, 4514, 4518, 4519, 4521] -/
theorem Equation4521_4512_implies_Equation4271 (G : Type*) [Magma G]
    (h4521 : Equation4521 G) (_ : Equation4512 G) : Equation4271 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X3) ◇ X3) := mod_symm (h4521 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq20 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X2 ◇ X3)) = (X0 ◇ (X4 ◇ X5)) := superpose eq11 eq11 -- superposition 11,11
  have eq137 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ X1)) := superpose eq20 eq13 -- superposition 13,20
  subsumption eq137 eq20

theorem Equation4271_4512_implies_Equation4285 (G : Type*) [Magma G]
    (h4271 : Equation4271 G) (_ : Equation4512 G) : Equation4285 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h4271 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation4285_4512_implies_Equation4289 (G : Type*) [Magma G]
    (h4285 : Equation4285 G) (_ : Equation4512 G) : Equation4289 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h4285 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK2 ◇ sK3)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 : (sK0 ◇ (sK0 ◇ sK2)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq14 -- superposition 14,11
  subsumption eq22 eq17

theorem Equation4289_4512_implies_Equation4317 (G : Type*) [Magma G]
    (h4289 : Equation4289 G) (_ : Equation4512 G) : Equation4317 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X3)) := mod_symm (h4289 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq16 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X2 ◇ X3)) = (X0 ◇ (X4 ◇ X5)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq16

theorem Equation4317_4512_implies_Equation4319 (G : Type*) [Magma G]
    (h4317 : Equation4317 G) (_ : Equation4512 G) : Equation4319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X1)) := mod_symm (h4317 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK2 ◇ sK3)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq42 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X3 ◇ X0)) := superpose eq11 eq17 -- superposition 17,11
  have eq63 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK3)) := superpose eq17 eq14 -- superposition 14,17
  subsumption eq63 eq42

theorem Equation4319_4512_implies_Equation4342 (G : Type*) [Magma G]
    (h4319 : Equation4319 G) (_ : Equation4512 G) : Equation4342 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X3)) := mod_symm (h4319 ..)
  have eq13 : (sK0 ◇ (sK2 ◇ sK3)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq16 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X2 ◇ X3)) = (X0 ◇ (X4 ◇ X5)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq16

theorem Equation4342_4512_implies_Equation4359 (G : Type*) [Magma G]
    (h4342 : Equation4342 G) (_ : Equation4512 G) : Equation4359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X3)) := mod_symm (h4342 ..)
  have eq13 : (sK0 ◇ (sK2 ◇ sK3)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq16 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X2 ◇ X3)) = (X0 ◇ (X4 ◇ X5)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq16

theorem Equation4359_4512_implies_Equation4361 (G : Type*) [Magma G]
    (h4359 : Equation4359 G) (_ : Equation4512 G) : Equation4361 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X3)) := mod_symm (h4359 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ sK4)) := mod_symm nh
  have eq16 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ (X2 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK3)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq16

theorem Equation4361_4512_implies_Equation4506 (G : Type*) [Magma G]
    (h4361 : Equation4361 G) (h4512 : Equation4512 G) : Equation4506 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X4)) := mod_symm (h4361 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq14 eq11

theorem Equation4506_4512_implies_Equation4507 (G : Type*) [Magma G]
    (h4506 : Equation4506 G) (h4512 : Equation4512 G) : Equation4507 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X0) ◇ X0) := mod_symm (h4506 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq17 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq59 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ X1)) := superpose eq17 eq14 -- superposition 14,17
  subsumption eq59 eq17

theorem Equation4507_4512_implies_Equation4509 (G : Type*) [Magma G]
    (h4507 : Equation4507 G) (h4512 : Equation4512 G) : Equation4509 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X0) ◇ X1) := mod_symm (h4507 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK0) ◇ sK3) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK0 ◇ sK3)) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq36 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11
  have eq46 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq36 eq14 -- backward demodulation 14,36
  have eq143 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq36 eq46 -- superposition 46,36
  subsumption eq143 eq19

theorem Equation4509_4512_implies_Equation4514 (G : Type*) [Magma G]
    (h4509 : Equation4509 G) (h4512 : Equation4512 G) : Equation4514 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X0) ◇ X3) := mod_symm (h4509 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq19 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X2 ◇ X3)) = (X0 ◇ (X4 ◇ X5)) := superpose eq11 eq11 -- superposition 11,11
  have eq28 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq28 eq19

theorem Equation4514_4512_implies_Equation4518 (G : Type*) [Magma G]
    (h4514 : Equation4514 G) (h4512 : Equation4512 G) : Equation4518 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X0) := mod_symm (h4514 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK3) ◇ sK0) := mod_symm nh
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK3)) := superpose eq11 eq13 -- superposition 13,11
  have eq25 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose eq11 eq12 -- superposition 12,11
  have eq38 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ (X1 ◇ X0))) := superpose eq11 eq19 -- superposition 19,11
  have eq97 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose eq25 eq25 -- superposition 25,25
  have eq138 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK3 ◇ (X1 ◇ X0))) := superpose eq97 eq38 -- backward demodulation 38,97
  subsumption eq138 eq97

theorem Equation4518_4512_implies_Equation4519 (G : Type*) [Magma G]
    (h4518 : Equation4518 G) (h4512 : Equation4512 G) : Equation4519 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X3) ◇ X0) := mod_symm (h4518 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK3) ◇ sK1) := mod_symm nh
  have eq19 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X2 ◇ X3)) = (X0 ◇ (X4 ◇ X5)) := superpose eq11 eq11 -- superposition 11,11
  have eq26 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ sK1)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq26 eq19

theorem Equation4519_4512_implies_Equation4521 (G : Type*) [Magma G]
    (h4519 : Equation4519 G) (h4512 : Equation4512 G) : Equation4521 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X3) ◇ X1) := mod_symm (h4519 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  have eq32 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X3)) := superpose eq11 eq12 -- superposition 12,11
  have eq185 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ (X2 ◇ X4)) := superpose eq32 eq32 -- superposition 32,32
  have eq215 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ X1)) := superpose eq32 eq22 -- superposition 22,32
  subsumption eq215 eq185


/- Equivalence of [4272, 4351, 4483] -/
theorem Equation4483_4512_implies_Equation4272 (G : Type*) [Magma G]
    (h4483 : Equation4483 G) (_ : Equation4512 G) : Equation4272 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ X1) := mod_symm (h4483 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq56 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ sK0)) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq56 eq16

theorem Equation4272_4512_implies_Equation4351 (G : Type*) [Magma G]
    (h4272 : Equation4272 G) (_ : Equation4512 G) : Equation4351 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4272 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq16 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq16 eq14

theorem Equation4351_4512_implies_Equation4483 (G : Type*) [Magma G]
    (h4351 : Equation4351 G) (h4512 : Equation4512 G) : Equation4483 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := mod_symm (h4351 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq28 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq28 eq11


/- Equivalence of [4273, 4332, 4446] -/
theorem Equation4446_4512_implies_Equation4273 (G : Type*) [Magma G]
    (h4446 : Equation4446 G) (_ : Equation4512 G) : Equation4273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ X1) := mod_symm (h4446 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11
  have eq54 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ X0)) := superpose eq15 eq13 -- superposition 13,15
  subsumption eq54 eq15

theorem Equation4273_4512_implies_Equation4332 (G : Type*) [Magma G]
    (h4273 : Equation4273 G) (_ : Equation4512 G) : Equation4332 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4273 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq17 eq14

theorem Equation4332_4512_implies_Equation4446 (G : Type*) [Magma G]
    (h4332 : Equation4332 G) (h4512 : Equation4512 G) : Equation4446 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := mod_symm (h4332 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq31 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq31 eq11


/- Equivalence of [4274, 4281, 4292, 4295, 4298, 4302, 4303, 4306, 4309, 4313, 4322, 4326, 4328, 4329, 4333, 4335, 4338, 4344, 4345, 4347, 4349, 4350, 4352, 4353, 4356, 4363, 4365, 4366, 4368, 4370, 4371, 4372, 4373, 4375, 4376, 4377, 4379, 4523, 4524, 4527, 4528, 4530, 4532, 4536, 4538, 4540, 4543, 4545, 4548, 4549, 4551, 4555, 4557, 4558, 4560, 4561, 4562, 4563, 4565, 4567, 4570, 4572, 4573, 4575, 4576, 4577, 4578, 4580, 4581] -/
theorem Equation4581_4512_implies_Equation4274 (G : Type*) [Magma G]
    (h4581 : Equation4581 G) (_ : Equation4512 G) : Equation4274 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X4) ◇ X4) := mod_symm (h4581 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq20 (X2 X3 X4 X5 X6 X7 : G) : (X2 ◇ (X3 ◇ X4)) = (X5 ◇ (X6 ◇ X7)) := superpose eq11 eq11 -- superposition 11,11
  have eq111 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq20 eq13 -- superposition 13,20
  subsumption eq111 eq20

theorem Equation4274_4512_implies_Equation4281 (G : Type*) [Magma G]
    (h4274 : Equation4274 G) (_ : Equation4512 G) : Equation4281 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h4274 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq38 (X0 X1 X3 X4 X5 X6 X7 : G) : (X6 ◇ (X0 ◇ X7)) = (X5 ◇ (X3 ◇ (X1 ◇ X4))) := superpose eq15 eq15 -- superposition 15,15
  have eq63 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ X1)) := superpose eq15 eq13 -- superposition 13,15
  have eq76 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X2 ◇ (X0 ◇ (sK2 ◇ X1))) := superpose eq11 eq63 -- superposition 63,11
  subsumption eq76 eq38

theorem Equation4281_4512_implies_Equation4292 (G : Type*) [Magma G]
    (h4281 : Equation4281 G) (_ : Equation4512 G) : Equation4292 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X3)) := mod_symm (h4281 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq21 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq11

theorem Equation4292_4512_implies_Equation4295 (G : Type*) [Magma G]
    (h4292 : Equation4292 G) (_ : Equation4512 G) : Equation4295 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h4292 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq14 : (sK1 ◇ (sK2 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq67 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ X0)) := superpose eq17 eq14 -- superposition 14,17
  have eq81 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X0)) = (X3 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq18 eq18 -- superposition 18,18
  have eq258 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq18 eq67 -- superposition 67,18
  subsumption eq258 eq81

theorem Equation4295_4512_implies_Equation4298 (G : Type*) [Magma G]
    (h4295 : Equation4295 G) (h4512 : Equation4512 G) : Equation4298 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h4295 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X3)) = ((X1 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq26 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X2 ◇ X3)) := superpose eq12 eq11 -- superposition 11,12
  have eq30 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ X3))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq62 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (X0 ◇ sK3)) := superpose eq16 eq13 -- superposition 13,16
  have eq86 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X3)) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq11 eq26 -- superposition 26,11
  have eq1209 (X0 X2 X3 X4 X5 : G) : (X3 ◇ (X3 ◇ X4)) = (X4 ◇ (X5 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3))))) := superpose eq30 eq26 -- superposition 26,30
  have eq1236 (X0 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ sK3)))) := superpose eq30 eq62 -- superposition 62,30
  have eq1376 (X2 X3 X4 X5 : G) : (X3 ◇ (X3 ◇ X4)) = (X4 ◇ (X2 ◇ (X2 ◇ X5))) := superpose eq86 eq1209 -- forward demodulation 1209,86
  subsumption eq1236 eq1376

theorem Equation4298_4512_implies_Equation4302 (G : Type*) [Magma G]
    (h4298 : Equation4298 G) (_ : Equation4512 G) : Equation4302 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ X3)) := mod_symm (h4298 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK0 ◇ sK3)) := mod_symm nh
  have eq17 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (X0 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq17

theorem Equation4302_4512_implies_Equation4303 (G : Type*) [Magma G]
    (h4302 : Equation4302 G) (_ : Equation4512 G) : Equation4303 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X3)) := mod_symm (h4302 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq19 (X0 X1 X3 X4 X5 : G) : (X0 ◇ (X0 ◇ X4)) = (X5 ◇ (X1 ◇ (X1 ◇ X3))) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  have eq43 (X0 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq11 eq22 -- superposition 22,11
  subsumption eq43 eq19

theorem Equation4303_4512_implies_Equation4306 (G : Type*) [Magma G]
    (h4303 : Equation4303 G) (h4512 : Equation4512 G) : Equation4306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := mod_symm (h4303 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X0)) = (X0 ◇ (X2 ◇ (X2 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X1))) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq25 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X3)) = ((X2 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X3 ◇ (X3 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ X3))) := superpose eq12 eq25 -- forward demodulation 25,12
  have eq61 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK3)) := superpose eq16 eq13 -- superposition 13,16
  have eq305 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X1)) = (X3 ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq29 eq22 -- superposition 22,29
  have eq895 (X1 X2 X3 X4 X5 : G) : (X4 ◇ (X4 ◇ X3)) = (X5 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X4))))) := superpose eq34 eq29 -- superposition 29,34
  have eq907 (X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X2 ◇ (X2 ◇ (X1 ◇ (sK1 ◇ sK3)))) := superpose eq34 eq61 -- superposition 61,34
  have eq1070 (X1 X2 X3 X4 X5 : G) : (X4 ◇ (X4 ◇ X3)) = (X5 ◇ (X2 ◇ (X2 ◇ X1))) := superpose eq305 eq895 -- forward demodulation 895,305
  have eq1078 (X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X2 ◇ (sK3 ◇ (sK3 ◇ sK1))) := superpose eq29 eq907 -- forward demodulation 907,29
  subsumption eq1078 eq1070

theorem Equation4306_4512_implies_Equation4309 (G : Type*) [Magma G]
    (h4306 : Equation4306 G) (_ : Equation4512 G) : Equation4309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X3)) := mod_symm (h4306 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK3 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X2 ◇ X0)) = (X3 ◇ (X1 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (X0 ◇ sK3)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq17

theorem Equation4309_4512_implies_Equation4313 (G : Type*) [Magma G]
    (h4309 : Equation4309 G) (_ : Equation4512 G) : Equation4313 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ X0)) := mod_symm (h4309 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK3 ◇ sK4)) := mod_symm nh
  have eq16 (X0 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ X0)) = (X4 ◇ (X5 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ X2)) = (X3 ◇ (X4 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq62 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (X1 ◇ sK4)) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq62 eq17

theorem Equation4313_4512_implies_Equation4322 (G : Type*) [Magma G]
    (h4313 : Equation4313 G) (_ : Equation4512 G) : Equation4322 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ X4)) := mod_symm (h4313 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq11

theorem Equation4322_4512_implies_Equation4326 (G : Type*) [Magma G]
    (h4322 : Equation4322 G) (_ : Equation4512 G) : Equation4326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h4322 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = (X3 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq65 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ X0)) := superpose eq16 eq13 -- superposition 13,16
  have eq116 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq11 eq18 -- superposition 18,11
  have eq138 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq18 eq65 -- superposition 65,18
  subsumption eq138 eq116

theorem Equation4326_4512_implies_Equation4328 (G : Type*) [Magma G]
    (h4326 : Equation4326 G) (_ : Equation4512 G) : Equation4328 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X2 ◇ X3)) := mod_symm (h4326 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq17 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ X2)) = (X1 ◇ (X3 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq17

theorem Equation4328_4512_implies_Equation4329 (G : Type*) [Magma G]
    (h4328 : Equation4328 G) (h4512 : Equation4512 G) : Equation4329 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ X1)) := mod_symm (h4328 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK0 ◇ sK3)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X0) ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq21 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK3 ◇ sK0)) := superpose eq11 eq13 -- superposition 13,11
  have eq22 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq30 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X3 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq39 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq30 eq22 -- backward demodulation 22,30
  have eq192 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = (X2 ◇ (X2 ◇ X2)) := superpose eq30 eq39 -- superposition 39,30
  have eq221 : (sK0 ◇ (sK3 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq192 eq21 -- backward demodulation 21,192
  subsumption eq221 eq192

theorem Equation4329_4512_implies_Equation4333 (G : Type*) [Magma G]
    (h4329 : Equation4329 G) (_ : Equation4512 G) : Equation4333 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ X3)) := mod_symm (h4329 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq17 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X1)) = (X3 ◇ (X0 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq17

theorem Equation4333_4512_implies_Equation4335 (G : Type*) [Magma G]
    (h4333 : Equation4333 G) (_ : Equation4512 G) : Equation4335 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X3)) := mod_symm (h4333 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK3 ◇ sK1)) := mod_symm nh
  have eq18 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X4)) = (X5 ◇ (X2 ◇ (X1 ◇ X3))) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK3 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  have eq39 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((X0 ◇ sK3) ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq11 eq22 -- superposition 22,11
  subsumption eq39 eq18

theorem Equation4335_4512_implies_Equation4338 (G : Type*) [Magma G]
    (h4335 : Equation4335 G) (_ : Equation4512 G) : Equation4338 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ X1)) := mod_symm (h4335 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK3 ◇ sK4)) := mod_symm nh
  have eq17 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ X2)) = (X3 ◇ (X4 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK4 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq17

theorem Equation4338_4512_implies_Equation4344 (G : Type*) [Magma G]
    (h4338 : Equation4338 G) (_ : Equation4512 G) : Equation4344 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ X4)) := mod_symm (h4338 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq22 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq11

theorem Equation4344_4512_implies_Equation4345 (G : Type*) [Magma G]
    (h4344 : Equation4344 G) (_ : Equation4512 G) : Equation4345 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h4344 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X3)) = (X3 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq68 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK2 ◇ X0)) := superpose eq15 eq13 -- superposition 13,15
  have eq115 (X0 X1 X2 X4 : G) : (X2 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X4)) := superpose eq15 eq17 -- superposition 17,15
  have eq129 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ X2)))) := superpose eq17 eq68 -- superposition 68,17
  subsumption eq129 eq115

theorem Equation4345_4512_implies_Equation4347 (G : Type*) [Magma G]
    (h4345 : Equation4345 G) (h4512 : Equation4512 G) : Equation4347 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h4345 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X3)) = ((X1 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq11 eq12 -- superposition 12,11
  have eq23 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq11 eq12 -- superposition 12,11
  have eq28 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X3 ◇ X3)) := superpose eq12 eq11 -- superposition 11,12
  have eq29 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := superpose eq12 eq20 -- forward demodulation 20,12
  have eq63 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (X0 ◇ sK3)) := superpose eq15 eq13 -- superposition 13,15
  have eq540 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq28 eq23 -- superposition 23,28
  have eq1112 (X0 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X4)) = (X4 ◇ (X5 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3))))) := superpose eq29 eq28 -- superposition 28,29
  have eq1138 (X0 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ sK3)))) := superpose eq29 eq63 -- superposition 63,29
  have eq1323 (X0 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X4)) = (X4 ◇ (X5 ◇ (X0 ◇ X0))) := superpose eq540 eq1112 -- forward demodulation 1112,540
  have eq1364 (X0 X2 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq540 eq1138 -- forward demodulation 1138,540
  subsumption eq1364 eq1323

theorem Equation4347_4512_implies_Equation4349 (G : Type*) [Magma G]
    (h4347 : Equation4347 G) (_ : Equation4512 G) : Equation4349 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X2 ◇ X3)) := mod_symm (h4347 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK0 ◇ sK3)) := mod_symm nh
  have eq16 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X3 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq21 eq16

theorem Equation4349_4512_implies_Equation4350 (G : Type*) [Magma G]
    (h4349 : Equation4349 G) (_ : Equation4512 G) : Equation4350 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X3)) := mod_symm (h4349 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X2)) = (X3 ◇ (X0 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq17

theorem Equation4350_4512_implies_Equation4352 (G : Type*) [Magma G]
    (h4350 : Equation4350 G) (_ : Equation4512 G) : Equation4352 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := mod_symm (h4350 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq39 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X1)) := superpose eq11 eq16 -- superposition 16,11
  have eq60 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK3)) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq60 eq39

theorem Equation4352_4512_implies_Equation4353 (G : Type*) [Magma G]
    (h4352 : Equation4352 G) (h4512 : Equation4512 G) : Equation4353 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X1 ◇ X3)) := mod_symm (h4352 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK3 ◇ sK0)) := mod_symm nh
  have eq18 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X0)) = (X5 ◇ (X2 ◇ (X1 ◇ X3))) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK3 ◇ sK3)) := superpose eq11 eq13 -- superposition 13,11
  have eq43 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (X1 ◇ (sK3 ◇ sK3))) := superpose eq12 eq22 -- superposition 22,12
  subsumption eq43 eq18

theorem Equation4353_4512_implies_Equation4356 (G : Type*) [Magma G]
    (h4353 : Equation4353 G) (_ : Equation4512 G) : Equation4356 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ X0)) := mod_symm (h4353 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK3 ◇ sK4)) := mod_symm nh
  have eq16 (X0 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ X0)) = (X4 ◇ (X5 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X2)) = (X3 ◇ (X4 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq60 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (X1 ◇ sK4)) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq60 eq17

theorem Equation4356_4512_implies_Equation4363 (G : Type*) [Magma G]
    (h4356 : Equation4356 G) (_ : Equation4512 G) : Equation4363 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ X4)) := mod_symm (h4356 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK3)) := mod_symm nh
  have eq22 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq11

theorem Equation4363_4512_implies_Equation4365 (G : Type*) [Magma G]
    (h4363 : Equation4363 G) (_ : Equation4512 G) : Equation4365 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := mod_symm (h4363 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq14 (X0 X1 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = (X4 ◇ (X1 ◇ (X0 ◇ X3))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X3 X4 : G) : (X1 ◇ (X0 ◇ X3)) = (X1 ◇ (X0 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq65 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK2 ◇ X0)) := superpose eq16 eq13 -- superposition 13,16
  have eq97 (X0 X1 X2 X4 X5 X6 : G) : (X2 ◇ (X0 ◇ X4)) = (X1 ◇ (X5 ◇ (X0 ◇ X6))) := superpose eq14 eq14 -- superposition 14,14
  have eq130 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (X1 ◇ (sK1 ◇ X2))) := superpose eq14 eq65 -- superposition 65,14
  subsumption eq130 eq97

theorem Equation4365_4512_implies_Equation4366 (G : Type*) [Magma G]
    (h4365 : Equation4365 G) (_ : Equation4512 G) : Equation4366 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X3)) := mod_symm (h4365 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK3 ◇ sK0)) := mod_symm nh
  have eq16 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK3)) := superpose eq11 eq13 -- superposition 13,11
  have eq49 (X0 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X4 ◇ X0)) = (X2 ◇ (X5 ◇ X6)) := superpose eq16 eq16 -- superposition 16,16
  have eq66 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (X1 ◇ X2)) := superpose eq16 eq22 -- superposition 22,16
  subsumption eq66 eq49

theorem Equation4366_4512_implies_Equation4368 (G : Type*) [Magma G]
    (h4366 : Equation4366 G) (_ : Equation4512 G) : Equation4368 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X3 ◇ X0)) := mod_symm (h4366 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK3 ◇ sK4)) := mod_symm nh
  have eq16 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ X3)) = (X1 ◇ (X4 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq42 (X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X2 ◇ X4)) = (X5 ◇ (X6 ◇ X1)) := superpose eq16 eq16 -- superposition 16,16
  have eq63 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (X1 ◇ sK3)) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq63 eq42

theorem Equation4368_4512_implies_Equation4370 (G : Type*) [Magma G]
    (h4368 : Equation4368 G) (_ : Equation4512 G) : Equation4370 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X3 ◇ X4)) := mod_symm (h4368 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq22 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (X0 ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq11

theorem Equation4370_4512_implies_Equation4371 (G : Type*) [Magma G]
    (h4370 : Equation4370 G) (h4512 : Equation4512 G) : Equation4371 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X3)) := mod_symm (h4370 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK3 ◇ sK0)) := mod_symm nh
  have eq16 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  have eq40 (X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X1 ◇ (sK3 ◇ sK0)) := superpose eq11 eq22 -- superposition 22,11
  have eq46 (X0 X1 X3 X4 X5 X6 X7 : G) : (X6 ◇ (X0 ◇ X7)) = (X5 ◇ (X3 ◇ (X1 ◇ X4))) := superpose eq16 eq16 -- superposition 16,16
  have eq97 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (X1 ◇ (sK3 ◇ sK0))) := superpose eq12 eq40 -- superposition 40,12
  subsumption eq97 eq46

theorem Equation4371_4512_implies_Equation4372 (G : Type*) [Magma G]
    (h4371 : Equation4371 G) (h4512 : Equation4512 G) : Equation4372 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X3 ◇ X0)) := mod_symm (h4371 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK3 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X5 ◇ X4)) = (X4 ◇ (X2 ◇ (X3 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (X0 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  have eq29 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X3 ◇ X4)) := superpose eq12 eq11 -- superposition 11,12
  have eq133 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (X1 ◇ (X2 ◇ sK1))) := superpose eq29 eq22 -- superposition 22,29
  have eq189 (X0 X1 X3 X4 X5 X6 : G) : (X3 ◇ (X4 ◇ X0)) = ((X5 ◇ X1) ◇ (X6 ◇ X0)) := superpose eq29 eq14 -- superposition 14,29
  have eq409 (X0 X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((X2 ◇ X0) ◇ (X3 ◇ sK2)) := superpose eq14 eq133 -- superposition 133,14
  subsumption eq409 eq189

theorem Equation4372_4512_implies_Equation4373 (G : Type*) [Magma G]
    (h4372 : Equation4372 G) (_ : Equation4512 G) : Equation4373 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X3 ◇ X1)) := mod_symm (h4372 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK3 ◇ sK4)) := mod_symm nh
  have eq16 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X0)) = (X2 ◇ (X4 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK4 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  have eq47 (X0 X1 X3 X4 X5 X6 : G) : (X3 ◇ (X0 ◇ X4)) = (X1 ◇ (X5 ◇ X6)) := superpose eq16 eq16 -- superposition 16,16
  have eq64 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK4 ◇ (X1 ◇ X2)) := superpose eq16 eq22 -- superposition 22,16
  subsumption eq64 eq47

theorem Equation4373_4512_implies_Equation4375 (G : Type*) [Magma G]
    (h4373 : Equation4373 G) (_ : Equation4512 G) : Equation4375 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X3 ◇ X4)) := mod_symm (h4373 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK1 ◇ sK4)) := mod_symm nh
  have eq16 (X0 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X4 ◇ X0)) = (X2 ◇ (X5 ◇ X6)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (X1 ◇ sK3)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq16

theorem Equation4375_4512_implies_Equation4376 (G : Type*) [Magma G]
    (h4375 : Equation4375 G) (_ : Equation4512 G) : Equation4376 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X4)) := mod_symm (h4375 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X1 X3 X4 X5 X6 X7 : G) : (X6 ◇ (X0 ◇ X7)) = (X5 ◇ (X3 ◇ (X1 ◇ X4))) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK2 ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  have eq39 (X0 X2 X3 X4 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X4 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq11 eq22 -- superposition 22,11
  subsumption eq39 eq14

theorem Equation4376_4512_implies_Equation4377 (G : Type*) [Magma G]
    (h4376 : Equation4376 G) (h4512 : Equation4512 G) : Equation4377 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X2 ◇ X1)) := mod_symm (h4376 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK2 ◇ sK4)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X1 ◇ X2) ◇ X0)) = (X4 ◇ (X3 ◇ (X2 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X1)) = (X4 ◇ (X2 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK4 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  have eq24 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X3 ◇ (X2 ◇ X1))) = (X5 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq31 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X4 ◇ (X3 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq68 (X0 X1 : G) : (X1 ◇ (sK4 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq16 eq22 -- superposition 22,16
  have eq228 (X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ X2)) = (X5 ◇ (X6 ◇ (X2 ◇ X1))) := superpose eq31 eq24 -- superposition 24,31
  have eq431 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (sK2 ◇ sK4))) ≠ (X3 ◇ (sK1 ◇ sK2)) := superpose eq31 eq68 -- superposition 68,31
  subsumption eq431 eq228

theorem Equation4377_4512_implies_Equation4379 (G : Type*) [Magma G]
    (h4377 : Equation4377 G) (_ : Equation4512 G) : Equation4379 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, sK5, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X2 ◇ X4)) := mod_symm (h4377 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK4 ◇ sK5)) := mod_symm nh
  have eq16 (X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X4 ◇ X1)) = (X5 ◇ (X2 ◇ X6)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK5 ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq16

theorem Equation4379_4512_implies_Equation4523 (G : Type*) [Magma G]
    (h4379 : Equation4379 G) (h4512 : Equation4512 G) : Equation4523 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X4 ◇ X5)) := mod_symm (h4379 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq31 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq31 eq11

theorem Equation4523_4512_implies_Equation4524 (G : Type*) [Magma G]
    (h4523 : Equation4523 G) (h4512 : Equation4512 G) : Equation4524 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X0) ◇ X0) := mod_symm (h4523 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq28 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11
  have eq30 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq12 eq13 -- superposition 13,12
  have eq39 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq28 eq30 -- forward demodulation 30,28
  subsumption eq39 eq18

theorem Equation4524_4512_implies_Equation4527 (G : Type*) [Magma G]
    (h4524 : Equation4524 G) (h4512 : Equation4512 G) : Equation4527 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X0) ◇ X1) := mod_symm (h4524 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X0) = (X3 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X0) = (X3 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq30 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ X0)) := superpose eq11 eq12 -- superposition 12,11
  have eq31 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) = ((X2 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq11 eq12 -- superposition 12,11
  have eq32 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq12 eq13 -- superposition 13,12
  have eq63 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK1 ◇ X0)) := superpose eq18 eq32 -- superposition 32,18
  have eq113 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X3)) := superpose eq18 eq30 -- superposition 30,18
  have eq210 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X2) := superpose eq30 eq20 -- superposition 20,30
  have eq1718 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ X1) ◇ X2)) = (X0 ◇ (X3 ◇ X4)) := superpose eq210 eq113 -- superposition 113,210
  have eq1852 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X2))) = (X0 ◇ (X3 ◇ X4)) := superpose eq12 eq1718 -- forward demodulation 1718,12
  have eq2003 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ ((X1 ◇ (sK1 ◇ X0)) ◇ X1)) := superpose eq31 eq63 -- superposition 63,31
  have eq2320 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (X1 ◇ ((sK1 ◇ X0) ◇ X1))) := superpose eq12 eq2003 -- forward demodulation 2003,12
  subsumption eq2320 eq1852

theorem Equation4527_4512_implies_Equation4528 (G : Type*) [Magma G]
    (h4527 : Equation4527 G) (h4512 : Equation4512 G) : Equation4528 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h4527 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq21 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK1 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  have eq39 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11
  have eq149 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ X1)) := superpose eq39 eq21 -- superposition 21,39
  subsumption eq149 rfl

theorem Equation4528_4512_implies_Equation4530 (G : Type*) [Magma G]
    (h4528 : Equation4528 G) (h4512 : Equation4512 G) : Equation4530 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ X1) := mod_symm (h4528 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK1) ◇ sK3) := mod_symm nh
  have eq18 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq32 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK1 ◇ sK3)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq32 eq18

theorem Equation4530_4512_implies_Equation4532 (G : Type*) [Magma G]
    (h4530 : Equation4530 G) (h4512 : Equation4512 G) : Equation4532 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ X3) := mod_symm (h4530 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq17 (X0 X1 X3 X4 X5 : G) : (X3 ◇ (X0 ◇ X4)) = ((X1 ◇ X1) ◇ X5) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X2 X3 X4 X5 : G) : (X2 ◇ (X0 ◇ X3)) = (X4 ◇ (X0 ◇ X5)) := superpose eq11 eq11 -- superposition 11,11
  have eq32 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK2 ◇ sK1)) := superpose eq12 eq13 -- superposition 13,12
  have eq98 (X2 X3 X4 X5 X6 X7 : G) : (X2 ◇ (X3 ◇ X4)) = (X5 ◇ (X6 ◇ X7)) := superpose eq17 eq17 -- superposition 17,17
  have eq179 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK2 ◇ X1)) := superpose eq20 eq32 -- superposition 32,20
  subsumption eq179 eq98

theorem Equation4532_4512_implies_Equation4536 (G : Type*) [Magma G]
    (h4532 : Equation4532 G) (h4512 : Equation4512 G) : Equation4536 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ X1) := mod_symm (h4532 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK3) ◇ sK1) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (X3 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X1)) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq11 eq11 -- superposition 11,11
  have eq17 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK3)) := superpose eq11 eq13 -- superposition 13,11
  have eq20 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq21 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X1))) = ((X1 ◇ (X2 ◇ X1)) ◇ X0) := superpose eq12 eq15 -- forward demodulation 15,12
  have eq22 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = ((X1 ◇ (X2 ◇ X1)) ◇ X0) := superpose eq20 eq21 -- forward demodulation 21,20
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = ((X1 ◇ (X2 ◇ X1)) ◇ X0) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq62 (X0 X1 : G) : (X1 ◇ (sK1 ◇ sK3)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq17 eq19 -- superposition 19,17
  have eq315 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X0)) = (X4 ◇ (X2 ◇ X3)) := superpose eq17 eq23 -- superposition 23,17
  have eq330 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ≠ (X2 ◇ (sK1 ◇ sK2)) := superpose eq23 eq62 -- superposition 62,23
  subsumption eq330 eq315

theorem Equation4536_4512_implies_Equation4538 (G : Type*) [Magma G]
    (h4536 : Equation4536 G) (h4512 : Equation4512 G) : Equation4538 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X1) := mod_symm (h4536 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq20 (X0 X2 X3 X4 X5 : G) : (X2 ◇ (X0 ◇ X3)) = (X4 ◇ (X0 ◇ X5)) := superpose eq11 eq11 -- superposition 11,11
  have eq31 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ X0)) := superpose eq11 eq12 -- superposition 12,11
  have eq37 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK3 ◇ sK3)) := superpose eq12 eq13 -- superposition 13,12
  have eq112 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ X1)) := superpose eq20 eq37 -- superposition 37,20
  have eq173 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = (X2 ◇ (X1 ◇ X3)) := superpose eq20 eq31 -- superposition 31,20
  have eq300 (X0 X1 X2 X3 : G) : (X0 ◇ (sK1 ◇ X1)) ≠ (X2 ◇ (sK3 ◇ X3)) := superpose eq20 eq112 -- superposition 112,20
  subsumption eq300 eq173

theorem Equation4538_4512_implies_Equation4540 (G : Type*) [Magma G]
    (h4538 : Equation4538 G) (_ : Equation4512 G) : Equation4540 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X3) ◇ X3) := mod_symm (h4538 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq17 (X0 X1 X3 X4 X5 : G) : (X3 ◇ (X0 ◇ X4)) = ((X1 ◇ X5) ◇ X5) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK2 ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  have eq42 (X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ X2) ◇ X2) := superpose eq11 eq22 -- superposition 22,11
  subsumption eq42 eq17

theorem Equation4540_4512_implies_Equation4543 (G : Type*) [Magma G]
    (h4540 : Equation4540 G) (h4512 : Equation4512 G) : Equation4543 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X0) := mod_symm (h4540 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK0) ◇ sK3) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11
  have eq27 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK0 ◇ sK3)) := superpose eq12 eq13 -- superposition 13,12
  have eq30 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X2 ◇ X3) ◇ X3) := superpose eq12 eq11 -- superposition 11,12
  have eq62 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (X0 ◇ sK3)) := superpose eq18 eq27 -- superposition 27,18
  have eq95 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := superpose eq11 eq25 -- superposition 25,11
  have eq138 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK2) ◇ sK2) := superpose eq11 eq62 -- superposition 62,11
  have eq347 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X0) = ((X3 ◇ X0) ◇ X0) := superpose eq15 eq30 -- superposition 30,15
  have eq745 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ X1)) := superpose eq95 eq347 -- superposition 347,95
  have eq3530 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((X0 ◇ sK2) ◇ sK2) := superpose eq347 eq138 -- superposition 138,347
  subsumption eq3530 eq745

theorem Equation4543_4512_implies_Equation4545 (G : Type*) [Magma G]
    (h4543 : Equation4543 G) (h4512 : Equation4512 G) : Equation4545 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X3) := mod_symm (h4543 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (X0 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X3 ◇ X0)) := superpose eq11 eq12 -- superposition 12,11
  have eq148 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ X3)) = (X1 ◇ (X4 ◇ X0)) := superpose eq29 eq29 -- superposition 29,29
  have eq178 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (X1 ◇ sK1)) := superpose eq29 eq22 -- superposition 22,29
  subsumption eq178 eq148

theorem Equation4545_4512_implies_Equation4548 (G : Type*) [Magma G]
    (h4545 : Equation4545 G) (h4512 : Equation4512 G) : Equation4548 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X1) := mod_symm (h4545 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq22 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X1))) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq34 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK2 ◇ sK0)) := superpose eq12 eq13 -- superposition 13,12
  have eq57 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK2 ◇ sK0)) := superpose eq19 eq34 -- superposition 34,19
  have eq980 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X2 ◇ X3)) = (X5 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq19 eq22 -- superposition 22,19
  have eq1049 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X2 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq22 eq57 -- superposition 57,22
  subsumption eq1049 eq980

theorem Equation4548_4512_implies_Equation4549 (G : Type*) [Magma G]
    (h4548 : Equation4548 G) (h4512 : Equation4512 G) : Equation4549 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X0) := mod_symm (h4548 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X3) = (X3 ◇ ((X2 ◇ X2) ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X3) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X2) := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X3) = (X3 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq12 eq22 -- forward demodulation 22,12
  have eq24 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X2 ◇ X0))) = (((X2 ◇ X2) ◇ X1) ◇ X3) := superpose eq15 eq23 -- backward demodulation 23,15
  have eq25 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X2 ◇ X0))) = ((X2 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq12 eq24 -- forward demodulation 24,12
  have eq26 (X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ X3) = ((X2 ◇ X2) ◇ X3) := superpose eq15 eq25 -- forward demodulation 25,15
  have eq27 (X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ X3) = (X2 ◇ (X2 ◇ X3)) := superpose eq12 eq26 -- forward demodulation 26,12
  have eq31 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) := superpose eq12 eq18 -- forward demodulation 18,12
  have eq32 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ X2)) := superpose eq27 eq31 -- forward demodulation 31,27
  have eq36 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11
  have eq38 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK2 ◇ sK1)) := superpose eq12 eq13 -- superposition 13,12
  have eq79 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (X0 ◇ sK1)) := superpose eq19 eq38 -- superposition 38,19
  have eq126 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := superpose eq11 eq36 -- superposition 36,11
  have eq336 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK1) ◇ sK2) := superpose eq11 eq79 -- superposition 79,11
  have eq589 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := superpose eq15 eq32 -- superposition 32,15
  have eq1205 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X3 ◇ (X3 ◇ X1)) := superpose eq126 eq589 -- superposition 589,126
  have eq2511 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (X0 ◇ sK2)) := superpose eq589 eq336 -- superposition 336,589
  subsumption eq2511 eq1205

theorem Equation4549_4512_implies_Equation4551 (G : Type*) [Magma G]
    (h4549 : Equation4549 G) (h4512 : Equation4512 G) : Equation4551 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X1) := mod_symm (h4549 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = (X3 ◇ ((X2 ◇ X2) ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = (X3 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  have eq22 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = (X3 ◇ (X2 ◇ (X2 ◇ X1))) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X2 ◇ X1))) = (((X2 ◇ X2) ◇ X1) ◇ X0) := superpose eq11 eq22 -- forward demodulation 22,11
  have eq24 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X2 ◇ X1))) = ((X2 ◇ (X2 ◇ X1)) ◇ X0) := superpose eq12 eq23 -- forward demodulation 23,12
  have eq25 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq12 eq16 -- forward demodulation 16,12
  have eq34 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11
  have eq72 (X0 X1 : G) : (X1 ◇ (sK3 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ sK2)) := superpose eq19 eq21 -- superposition 21,19
  have eq214 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X0)) = ((X1 ◇ X1) ◇ X0) := superpose eq34 eq25 -- superposition 25,34
  have eq282 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X0) = (X3 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq12 eq214 -- forward demodulation 214,12
  have eq285 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X1) = ((X2 ◇ (X2 ◇ X1)) ◇ X0) := superpose eq282 eq24 -- backward demodulation 24,282
  have eq288 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = ((X2 ◇ (X2 ◇ X1)) ◇ X0) := superpose eq12 eq285 -- forward demodulation 285,12
  have eq604 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X0 ◇ X1)) = (X4 ◇ (X2 ◇ X3)) := superpose eq19 eq288 -- superposition 288,19
  have eq627 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) ≠ (X2 ◇ (sK3 ◇ sK2)) := superpose eq288 eq72 -- superposition 72,288
  subsumption eq627 eq604

theorem Equation4551_4512_implies_Equation4555 (G : Type*) [Magma G]
    (h4551 : Equation4551 G) (h4512 : Equation4512 G) : Equation4555 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X3) := mod_symm (h4551 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq17 (X0 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X0)) = ((X2 ◇ X2) ◇ X5) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ X0)) = (X4 ◇ (X5 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq34 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK3 ◇ sK3)) := superpose eq12 eq13 -- superposition 13,12
  have eq93 (X2 X3 X4 X5 X6 X7 : G) : (X2 ◇ (X3 ◇ X4)) = (X5 ◇ (X6 ◇ X7)) := superpose eq17 eq17 -- superposition 17,17
  have eq163 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (X1 ◇ sK3)) := superpose eq20 eq34 -- superposition 34,20
  subsumption eq163 eq93

theorem Equation4555_4512_implies_Equation4557 (G : Type*) [Magma G]
    (h4555 : Equation4555 G) (_ : Equation4512 G) : Equation4557 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X3) := mod_symm (h4555 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq17 (X0 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X0)) = ((X2 ◇ X5) ◇ X5) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (X1 ◇ sK3)) := superpose eq11 eq13 -- superposition 13,11
  have eq41 (X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ X2) ◇ X2) := superpose eq11 eq22 -- superposition 22,11
  subsumption eq41 eq17

theorem Equation4557_4512_implies_Equation4558 (G : Type*) [Magma G]
    (h4557 : Equation4557 G) (h4512 : Equation4512 G) : Equation4558 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X0) ◇ X0) := mod_symm (h4557 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq24 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11
  have eq26 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK0 ◇ sK1)) := superpose eq12 eq13 -- superposition 13,12
  have eq132 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X3)) = (X4 ◇ (X0 ◇ X0)) := superpose eq24 eq24 -- superposition 24,24
  have eq158 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ sK3)) := superpose eq24 eq26 -- superposition 26,24
  subsumption eq158 eq132

theorem Equation4558_4512_implies_Equation4560 (G : Type*) [Magma G]
    (h4558 : Equation4558 G) (h4512 : Equation4512 G) : Equation4560 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X0) ◇ X1) := mod_symm (h4558 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK0) ◇ sK3) := mod_symm nh
  have eq20 (X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X3)) = (X1 ◇ (X2 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  have eq30 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X3)) := superpose eq11 eq12 -- superposition 12,11
  have eq199 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X1 ◇ (X2 ◇ X3))) = (X4 ◇ (X0 ◇ X5)) := superpose eq30 eq20 -- superposition 20,30
  have eq206 (X0 X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq30 eq22 -- superposition 22,30
  subsumption eq206 eq199

theorem Equation4560_4512_implies_Equation4561 (G : Type*) [Magma G]
    (h4560 : Equation4560 G) (h4512 : Equation4512 G) : Equation4561 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X0) ◇ X3) := mod_symm (h4560 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK0) ◇ sK4) := mod_symm nh
  have eq28 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = (X0 ◇ (X1 ◇ X0)) := superpose eq11 eq12 -- superposition 12,11
  have eq30 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK0 ◇ sK4)) := superpose eq12 eq13 -- superposition 13,12
  have eq162 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X3)) = (X4 ◇ (X0 ◇ X4)) := superpose eq28 eq28 -- superposition 28,28
  have eq196 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ X0)) := superpose eq28 eq30 -- superposition 30,28
  subsumption eq196 eq162

theorem Equation4561_4512_implies_Equation4562 (G : Type*) [Magma G]
    (h4561 : Equation4561 G) (h4512 : Equation4512 G) : Equation4562 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X0) ◇ X4) := mod_symm (h4561 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq22 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (X0 ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  have eq27 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X3 ◇ X4)) := superpose eq11 eq12 -- superposition 12,11
  have eq147 (X0 X1 X3 X4 X5 X6 : G) : (X3 ◇ (X0 ◇ X4)) = (X1 ◇ (X5 ◇ X6)) := superpose eq27 eq27 -- superposition 27,27
  have eq189 (X0 X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (X2 ◇ X3)) := superpose eq27 eq22 -- superposition 22,27
  subsumption eq189 eq147

theorem Equation4562_4512_implies_Equation4563 (G : Type*) [Magma G]
    (h4562 : Equation4562 G) (h4512 : Equation4512 G) : Equation4563 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ X0) := mod_symm (h4562 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK1 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X3)) := superpose eq11 eq12 -- superposition 12,11
  have eq162 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X4)) := superpose eq29 eq29 -- superposition 29,29
  have eq192 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK1 ◇ X1)) := superpose eq29 eq22 -- superposition 22,29
  subsumption eq192 eq162

theorem Equation4563_4512_implies_Equation4565 (G : Type*) [Magma G]
    (h4563 : Equation4563 G) (h4512 : Equation4512 G) : Equation4565 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ X1) := mod_symm (h4563 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK1) ◇ sK3) := mod_symm nh
  have eq20 (X1 X2 X3 X4 X5 : G) : (X2 ◇ (X1 ◇ X3)) = (X4 ◇ (X1 ◇ X5)) := superpose eq11 eq11 -- superposition 11,11
  have eq32 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK1 ◇ sK3)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq32 eq20

theorem Equation4565_4512_implies_Equation4567 (G : Type*) [Magma G]
    (h4565 : Equation4565 G) (h4512 : Equation4512 G) : Equation4567 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ X3) := mod_symm (h4565 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq17 (X0 X2 X3 X4 X5 : G) : ((X5 ◇ X0) ◇ X5) = (X3 ◇ (X2 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X1 X2 X3 X4 X5 : G) : (X2 ◇ (X1 ◇ X3)) = (X4 ◇ (X1 ◇ X5)) := superpose eq11 eq11 -- superposition 11,11
  have eq30 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK2 ◇ sK0)) := superpose eq12 eq13 -- superposition 13,12
  have eq82 (X2 X3 X4 X5 X6 X7 : G) : (X2 ◇ (X3 ◇ X4)) = (X5 ◇ (X6 ◇ X7)) := superpose eq17 eq17 -- superposition 17,17
  have eq182 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK2 ◇ X1)) := superpose eq20 eq30 -- superposition 30,20
  subsumption eq182 eq82

theorem Equation4567_4512_implies_Equation4570 (G : Type*) [Magma G]
    (h4567 : Equation4567 G) (h4512 : Equation4512 G) : Equation4570 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X0) := mod_symm (h4567 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq20 (X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X1)) = (X2 ◇ (X4 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (X0 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  have eq28 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X3 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11
  have eq147 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X4 ◇ X1)) = (X0 ◇ (X3 ◇ X2)) := superpose eq20 eq28 -- superposition 28,20
  have eq186 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (X1 ◇ X0)) := superpose eq28 eq22 -- superposition 22,28
  subsumption eq186 eq147

theorem Equation4570_4512_implies_Equation4572 (G : Type*) [Magma G]
    (h4570 : Equation4570 G) (h4512 : Equation4512 G) : Equation4572 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X3) := mod_symm (h4570 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK3) ◇ sK0) := mod_symm nh
  have eq17 (X1 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X2)) = ((X5 ◇ X1) ◇ X5) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X1 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ X1)) = (X4 ◇ (X5 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq29 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK3 ◇ sK0)) := superpose eq12 eq13 -- superposition 13,12
  have eq96 (X2 X3 X4 X5 X6 X7 : G) : (X2 ◇ (X3 ◇ X4)) = (X5 ◇ (X6 ◇ X7)) := superpose eq17 eq17 -- superposition 17,17
  have eq167 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (X1 ◇ sK0)) := superpose eq20 eq29 -- superposition 29,20
  subsumption eq167 eq96

theorem Equation4572_4512_implies_Equation4573 (G : Type*) [Magma G]
    (h4572 : Equation4572 G) (h4512 : Equation4512 G) : Equation4573 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X3) ◇ X0) := mod_symm (h4572 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK3) ◇ sK1) := mod_symm nh
  have eq22 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (X0 ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  have eq28 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11
  have eq166 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X3)) = (X4 ◇ (X4 ◇ X0)) := superpose eq28 eq28 -- superposition 28,28
  have eq204 (X2 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X2 ◇ (X2 ◇ sK1)) := superpose eq28 eq22 -- superposition 22,28
  subsumption eq204 eq166

theorem Equation4573_4512_implies_Equation4575 (G : Type*) [Magma G]
    (h4573 : Equation4573 G) (_ : Equation4512 G) : Equation4575 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X3) ◇ X1) := mod_symm (h4573 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq20 (X1 X2 X3 X4 X5 : G) : (X2 ◇ (X1 ◇ X3)) = (X4 ◇ (X1 ◇ X5)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  have eq98 (X0 X1 X3 X4 X5 X6 X7 : G) : (X6 ◇ (X0 ◇ X7)) = (X5 ◇ (X3 ◇ (X1 ◇ X4))) := superpose eq20 eq20 -- superposition 20,20
  have eq132 (X0 X2 X3 X4 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X4 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq20 eq22 -- superposition 22,20
  subsumption eq132 eq98

theorem Equation4575_4512_implies_Equation4576 (G : Type*) [Magma G]
    (h4575 : Equation4575 G) (h4512 : Equation4512 G) : Equation4576 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X3) ◇ X3) := mod_symm (h4575 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK3) ◇ sK4) := mod_symm nh
  have eq19 (X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ (X2 ◇ X3)) = (X4 ◇ (X5 ◇ X6)) := superpose eq11 eq11 -- superposition 11,11
  have eq27 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK3 ◇ sK4)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq27 eq19

theorem Equation4576_4512_implies_Equation4577 (G : Type*) [Magma G]
    (h4576 : Equation4576 G) (h4512 : Equation4512 G) : Equation4577 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X3) ◇ X4) := mod_symm (h4576 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK4) ◇ sK0) := mod_symm nh
  have eq20 (X2 X3 X4 X5 X6 X7 : G) : (X2 ◇ (X3 ◇ X4)) = (X5 ◇ (X6 ◇ X7)) := superpose eq11 eq11 -- superposition 11,11
  have eq28 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK4 ◇ sK0)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq28 eq20

theorem Equation4577_4512_implies_Equation4578 (G : Type*) [Magma G]
    (h4577 : Equation4577 G) (h4512 : Equation4512 G) : Equation4578 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X4) ◇ X0) := mod_symm (h4577 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK4) ◇ sK1) := mod_symm nh
  have eq22 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (X0 ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  have eq26 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X3 ◇ X4)) := superpose eq11 eq12 -- superposition 12,11
  have eq140 (X0 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X4 ◇ X0)) = (X2 ◇ (X5 ◇ X6)) := superpose eq26 eq26 -- superposition 26,26
  have eq182 (X1 X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X1 ◇ (X2 ◇ X3)) := superpose eq26 eq22 -- superposition 22,26
  subsumption eq182 eq140

theorem Equation4578_4512_implies_Equation4580 (G : Type*) [Magma G]
    (h4578 : Equation4578 G) (h4512 : Equation4512 G) : Equation4580 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X4) ◇ X1) := mod_symm (h4578 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK4) ◇ sK3) := mod_symm nh
  have eq22 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ X1)) := superpose eq11 eq13 -- superposition 13,11
  have eq29 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X2 ◇ X4)) := superpose eq11 eq12 -- superposition 12,11
  have eq159 (X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X4 ◇ X1)) = (X5 ◇ (X2 ◇ X6)) := superpose eq29 eq29 -- superposition 29,29
  have eq189 (X1 X2 X3 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X2 ◇ (X1 ◇ X3)) := superpose eq29 eq22 -- superposition 22,29
  subsumption eq189 eq159

theorem Equation4580_4512_implies_Equation4581 (G : Type*) [Magma G]
    (h4580 : Equation4580 G) (h4512 : Equation4512 G) : Equation4581 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X4) ◇ X3) := mod_symm (h4580 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK4) ◇ sK4) := mod_symm nh
  have eq20 (X2 X3 X4 X5 X6 X7 : G) : (X2 ◇ (X3 ◇ X4)) = (X5 ◇ (X6 ◇ X7)) := superpose eq11 eq11 -- superposition 11,11
  have eq32 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK4 ◇ sK4)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq32 eq20


/- Equivalence of [4275, 4307, 4409] -/
theorem Equation4409_4512_implies_Equation4275 (G : Type*) [Magma G]
    (h4409 : Equation4409 G) (_ : Equation4512 G) : Equation4275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ X1) := mod_symm (h4409 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq49 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (X0 ◇ sK0)) := superpose eq15 eq13 -- superposition 13,15
  subsumption eq49 eq15

theorem Equation4275_4512_implies_Equation4307 (G : Type*) [Magma G]
    (h4275 : Equation4275 G) (_ : Equation4512 G) : Equation4307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h4275 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq15 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq15 eq14

theorem Equation4307_4512_implies_Equation4409 (G : Type*) [Magma G]
    (h4307 : Equation4307 G) (h4512 : Equation4512 G) : Equation4409 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := mod_symm (h4307 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq31 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq31 eq11


/- Equivalence of [4277, 4294, 4308, 4423, 4425] -/
theorem Equation4425_4512_implies_Equation4277 (G : Type*) [Magma G]
    (h4425 : Equation4425 G) (_ : Equation4512 G) : Equation4277 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X2) ◇ X2) := mod_symm (h4425 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq17 (X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ X2)) = (X3 ◇ (X3 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq78 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq17 eq13 -- superposition 13,17
  subsumption eq78 eq17

theorem Equation4277_4512_implies_Equation4294 (G : Type*) [Magma G]
    (h4277 : Equation4277 G) (_ : Equation4512 G) : Equation4294 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X2)) := mod_symm (h4277 ..)
  have eq13 : (sK1 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq20 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq11

theorem Equation4294_4512_implies_Equation4308 (G : Type*) [Magma G]
    (h4294 : Equation4294 G) (_ : Equation4512 G) : Equation4308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X2)) := mod_symm (h4294 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X1 ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (X0 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq16

theorem Equation4308_4512_implies_Equation4423 (G : Type*) [Magma G]
    (h4308 : Equation4308 G) (h4512 : Equation4512 G) : Equation4423 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X3)) := mod_symm (h4308 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq27 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ sK0)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq27 eq11

theorem Equation4423_4512_implies_Equation4425 (G : Type*) [Magma G]
    (h4423 : Equation4423 G) (h4512 : Equation4512 G) : Equation4425 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X2) ◇ X0) := mod_symm (h4423 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq18 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  have eq23 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq174 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X1 ◇ (X1 ◇ X3)) := superpose eq23 eq23 -- superposition 23,23
  have eq202 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq23 eq18 -- superposition 18,23
  subsumption eq202 eq174


/- Equivalence of [4278, 4310, 4323, 4334, 4348, 4354, 4367, 4378, 4533, 4542, 4550, 4554, 4559, 4569, 4574] -/
theorem Equation4574_4512_implies_Equation4278 (G : Type*) [Magma G]
    (h4574 : Equation4574 G) (_ : Equation4512 G) : Equation4278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X3) ◇ X2) := mod_symm (h4574 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq20 (X1 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ X1)) = (X4 ◇ (X5 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq115 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (X1 ◇ sK0)) := superpose eq20 eq13 -- superposition 13,20
  subsumption eq115 eq20

theorem Equation4278_4512_implies_Equation4310 (G : Type*) [Magma G]
    (h4278 : Equation4278 G) (_ : Equation4512 G) : Equation4310 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h4278 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK3 ◇ sK1)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X0)) = (X3 ◇ (X4 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq18 eq15

theorem Equation4310_4512_implies_Equation4323 (G : Type*) [Magma G]
    (h4310 : Equation4310 G) (_ : Equation4512 G) : Equation4323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ X1)) := mod_symm (h4310 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq16 (X1 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ X1)) = (X4 ◇ (X5 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (X0 ◇ sK0)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq16

theorem Equation4323_4512_implies_Equation4334 (G : Type*) [Magma G]
    (h4323 : Equation4323 G) (_ : Equation4512 G) : Equation4334 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h4323 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK3 ◇ sK0)) := mod_symm nh
  have eq14 : (sK2 ◇ (sK3 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X3 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq21 : (sK0 ◇ (sK2 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq14 -- superposition 14,11
  subsumption eq21 eq17

theorem Equation4334_4512_implies_Equation4348 (G : Type*) [Magma G]
    (h4334 : Equation4334 G) (_ : Equation4512 G) : Equation4348 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ X0)) := mod_symm (h4334 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq16 (X0 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ X0)) = (X4 ◇ (X5 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq16

theorem Equation4348_4512_implies_Equation4354 (G : Type*) [Magma G]
    (h4348 : Equation4348 G) (_ : Equation4512 G) : Equation4354 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := mod_symm (h4348 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK3 ◇ sK1)) := mod_symm nh
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq40 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := superpose eq11 eq16 -- superposition 16,11
  have eq61 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK3 ◇ sK1)) := superpose eq16 eq13 -- superposition 13,16
  subsumption eq61 eq40

theorem Equation4354_4512_implies_Equation4367 (G : Type*) [Magma G]
    (h4354 : Equation4354 G) (_ : Equation4512 G) : Equation4367 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ X1)) := mod_symm (h4354 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK3 ◇ sK2)) := mod_symm nh
  have eq16 (X1 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ X1)) = (X4 ◇ (X5 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq16

theorem Equation4367_4512_implies_Equation4378 (G : Type*) [Magma G]
    (h4367 : Equation4367 G) (_ : Equation4512 G) : Equation4378 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X3 ◇ X2)) := mod_symm (h4367 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK4 ◇ sK2)) := mod_symm nh
  have eq16 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X1 ◇ (X4 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (sK3 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq16

theorem Equation4378_4512_implies_Equation4533 (G : Type*) [Magma G]
    (h4378 : Equation4378 G) (h4512 : Equation4512 G) : Equation4533 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X4 ◇ X2)) := mod_symm (h4378 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq31 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK2 ◇ sK2)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq31 eq11

theorem Equation4533_4512_implies_Equation4542 (G : Type*) [Magma G]
    (h4533 : Equation4533 G) (h4512 : Equation4512 G) : Equation4542 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ X2) := mod_symm (h4533 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq17 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq25 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11
  have eq27 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK0 ◇ sK2)) := superpose eq12 eq13 -- superposition 13,12
  have eq83 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := superpose eq17 eq25 -- superposition 25,17
  have eq97 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq25 eq27 -- superposition 27,25
  subsumption eq97 eq83

theorem Equation4542_4512_implies_Equation4550 (G : Type*) [Magma G]
    (h4542 : Equation4542 G) (h4512 : Equation4512 G) : Equation4550 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h4542 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq21 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (X0 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  have eq31 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq11 eq12 -- superposition 12,11
  have eq127 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (X1 ◇ sK2)) := superpose eq31 eq21 -- superposition 21,31
  subsumption eq127 rfl

theorem Equation4550_4512_implies_Equation4554 (G : Type*) [Magma G]
    (h4550 : Equation4550 G) (h4512 : Equation4512 G) : Equation4554 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ X2) := mod_symm (h4550 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq18 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X0)) = (X3 ◇ (X4 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq27 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK3 ◇ sK2)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq27 eq18

theorem Equation4554_4512_implies_Equation4559 (G : Type*) [Magma G]
    (h4554 : Equation4554 G) (h4512 : Equation4512 G) : Equation4559 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X3) ◇ X2) := mod_symm (h4554 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq20 (X0 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ X0)) = (X4 ◇ (X5 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq30 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK0 ◇ sK2)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq30 eq20

theorem Equation4559_4512_implies_Equation4569 (G : Type*) [Magma G]
    (h4559 : Equation4559 G) (h4512 : Equation4512 G) : Equation4569 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X0) ◇ X2) := mod_symm (h4559 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (X0 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  have eq28 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X3 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq143 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X1 ◇ (X4 ◇ X2)) := superpose eq28 eq28 -- superposition 28,28
  have eq173 (X0 X1 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (X0 ◇ (X1 ◇ sK2)) := superpose eq28 eq22 -- superposition 22,28
  subsumption eq173 eq143

theorem Equation4569_4512_implies_Equation4574 (G : Type*) [Magma G]
    (h4569 : Equation4569 G) (h4512 : Equation4512 G) : Equation4574 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X2) ◇ X2) := mod_symm (h4569 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq20 (X1 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ X1)) = (X4 ◇ (X5 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq29 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK3 ◇ sK2)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq29 eq20


/- Equivalence of [4279, 4324, 4336, 4454, 4462] -/
theorem Equation4462_4512_implies_Equation4279 (G : Type*) [Magma G]
    (h4462 : Equation4462 G) (_ : Equation4512 G) : Equation4279 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X2) ◇ X2) := mod_symm (h4462 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq17 (X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X1)) = (X3 ◇ (X4 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq80 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq17 eq13 -- superposition 13,17
  subsumption eq80 eq17

theorem Equation4279_4512_implies_Equation4324 (G : Type*) [Magma G]
    (h4279 : Equation4279 G) (_ : Equation4512 G) : Equation4324 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X1)) := mod_symm (h4279 ..)
  have eq13 : (sK1 ◇ (sK2 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq20 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq11

theorem Equation4324_4512_implies_Equation4336 (G : Type*) [Magma G]
    (h4324 : Equation4324 G) (_ : Equation4512 G) : Equation4336 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X2 ◇ X1)) := mod_symm (h4324 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK3 ◇ sK2)) := mod_symm nh
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (X1 ◇ (X3 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq22 eq16

theorem Equation4336_4512_implies_Equation4454 (G : Type*) [Magma G]
    (h4336 : Equation4336 G) (h4512 : Equation4512 G) : Equation4454 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ X2)) := mod_symm (h4336 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq27 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK0 ◇ sK2)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq27 eq11

theorem Equation4454_4512_implies_Equation4462 (G : Type*) [Magma G]
    (h4454 : Equation4454 G) (h4512 : Equation4512 G) : Equation4462 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h4454 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq20 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (X0 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  have eq26 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X2 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11
  have eq141 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (X1 ◇ (X3 ◇ X1)) := superpose eq26 eq26 -- superposition 26,26
  have eq165 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq26 eq20 -- superposition 20,26
  subsumption eq165 eq141


/- Equivalence of [4280, 4346, 4355, 4489, 4499] -/
theorem Equation4499_4512_implies_Equation4280 (G : Type*) [Magma G]
    (h4499 : Equation4499 G) (_ : Equation4512 G) : Equation4280 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ X2) ◇ X2) := mod_symm (h4499 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq18 (X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X2)) = (X3 ◇ (X4 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq91 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq18 eq13 -- superposition 13,18
  subsumption eq91 eq18

theorem Equation4280_4512_implies_Equation4346 (G : Type*) [Magma G]
    (h4280 : Equation4280 G) (_ : Equation4512 G) : Equation4346 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X2)) := mod_symm (h4280 ..)
  have eq13 : (sK1 ◇ (sK2 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq20 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq11

theorem Equation4346_4512_implies_Equation4355 (G : Type*) [Magma G]
    (h4346 : Equation4346 G) (_ : Equation4512 G) : Equation4355 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X2 ◇ X2)) := mod_symm (h4346 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X3 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq20 eq15

theorem Equation4355_4512_implies_Equation4489 (G : Type*) [Magma G]
    (h4355 : Equation4355 G) (h4512 : Equation4512 G) : Equation4489 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ X3)) := mod_symm (h4355 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq31 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK0 ◇ sK0)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq31 eq11

theorem Equation4489_4512_implies_Equation4499 (G : Type*) [Magma G]
    (h4489 : Equation4489 G) (h4512 : Equation4512 G) : Equation4499 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ X0) ◇ X0) := mod_symm (h4489 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq18 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (X0 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  have eq23 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X2 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq126 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X3 ◇ X3)) := superpose eq23 eq23 -- superposition 23,23
  have eq148 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq23 eq18 -- superposition 18,23
  subsumption eq148 eq126


/- Equivalence of [4283, 4433] -/
theorem Equation4433_4512_implies_Equation4283 (G : Type*) [Magma G]
    (h4433 : Equation4433 G) (h4512 : Equation4512 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := mod_symm (h4433 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq21 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11
  have eq42 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq21 eq13 -- superposition 13,21
  subsumption eq42 rfl

theorem Equation4283_4512_implies_Equation4433 (G : Type*) [Magma G]
    (h4283 : Equation4283 G) (h4512 : Equation4512 G) : Equation4433 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h4283 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq14 eq11


/- Equivalence of [4284, 4470] -/
theorem Equation4470_4512_implies_Equation4284 (G : Type*) [Magma G]
    (h4470 : Equation4470 G) (h4512 : Equation4512 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := mod_symm (h4470 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq23 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11
  have eq48 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq23 eq13 -- superposition 13,23
  subsumption eq48 rfl

theorem Equation4284_4512_implies_Equation4470 (G : Type*) [Magma G]
    (h4284 : Equation4284 G) (h4512 : Equation4512 G) : Equation4470 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4284 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq14 eq11


/- Equivalence of [4286, 4434] -/
theorem Equation4434_4512_implies_Equation4286 (G : Type*) [Magma G]
    (h4434 : Equation4434 G) (h4512 : Equation4512 G) : Equation4286 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ X2) := mod_symm (h4434 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq19 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = (X0 ◇ (X3 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq28 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X0)) := superpose eq11 eq12 -- superposition 12,11
  have eq113 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq19 eq13 -- superposition 13,19
  subsumption eq113 eq28

theorem Equation4286_4512_implies_Equation4434 (G : Type*) [Magma G]
    (h4286 : Equation4286 G) (h4512 : Equation4512 G) : Equation4434 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X0)) := mod_symm (h4286 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK2)) := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq14 eq11


/- Equivalence of [4287, 4340, 4360, 4508, 4516] -/
theorem Equation4516_4512_implies_Equation4287 (G : Type*) [Magma G]
    (h4516 : Equation4516 G) (_ : Equation4512 G) : Equation4287 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X2) := mod_symm (h4516 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq70 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ sK1)) := superpose eq19 eq13 -- superposition 13,19
  subsumption eq70 eq19

theorem Equation4287_4512_implies_Equation4340 (G : Type*) [Magma G]
    (h4287 : Equation4287 G) (_ : Equation4512 G) : Equation4340 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X1)) := mod_symm (h4287 ..)
  have eq13 : (sK0 ◇ (sK2 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK2 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation4340_4512_implies_Equation4360 (G : Type*) [Magma G]
    (h4340 : Equation4340 G) (_ : Equation4512 G) : Equation4360 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X1)) := mod_symm (h4340 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ sK2)) := mod_symm nh
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq19 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq19 eq16

theorem Equation4360_4512_implies_Equation4508 (G : Type*) [Magma G]
    (h4360 : Equation4360 G) (h4512 : Equation4512 G) : Equation4508 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X2)) := mod_symm (h4360 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK0 ◇ sK2)) := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq14 eq11

theorem Equation4508_4512_implies_Equation4516 (G : Type*) [Magma G]
    (h4508 : Equation4508 G) (h4512 : Equation4512 G) : Equation4516 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X0) ◇ X2) := mod_symm (h4508 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq38 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq38 eq18


/- Equivalence of [4288, 4471] -/
theorem Equation4471_4512_implies_Equation4288 (G : Type*) [Magma G]
    (h4471 : Equation4471 G) (h4512 : Equation4512 G) : Equation4288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ X2) := mod_symm (h4471 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq18 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = (X0 ◇ (X3 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq25 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq110 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq18 eq13 -- superposition 13,18
  subsumption eq110 eq25

theorem Equation4288_4512_implies_Equation4471 (G : Type*) [Magma G]
    (h4288 : Equation4288 G) (h4512 : Equation4512 G) : Equation4471 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := mod_symm (h4288 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK2)) := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq14 eq11


/- Equivalence of [4290, 4482] -/
theorem Equation4482_4512_implies_Equation4290 (G : Type*) [Magma G]
    (h4482 : Equation4482 G) (h4512 : Equation4512 G) : Equation4290 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h4482 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := superpose eq11 eq12 -- superposition 12,11
  have eq44 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq17 eq13 -- superposition 13,17
  subsumption eq44 rfl

theorem Equation4290_4512_implies_Equation4482 (G : Type*) [Magma G]
    (h4290 : Equation4290 G) (h4512 : Equation4512 G) : Equation4482 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4290 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq22 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq22 eq11


/- Equivalence of [4291, 4445] -/
theorem Equation4445_4512_implies_Equation4291 (G : Type*) [Magma G]
    (h4445 : Equation4445 G) (h4512 : Equation4512 G) : Equation4291 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h4445 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq21 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11
  have eq48 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq21 eq13 -- superposition 13,21
  subsumption eq48 rfl

theorem Equation4291_4512_implies_Equation4445 (G : Type*) [Magma G]
    (h4291 : Equation4291 G) (h4512 : Equation4512 G) : Equation4445 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h4291 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq21 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq21 eq11


/- Equivalence of [4296, 4460] -/
theorem Equation4460_4512_implies_Equation4296 (G : Type*) [Magma G]
    (h4460 : Equation4460 G) (h4512 : Equation4512 G) : Equation4296 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X2) ◇ X0) := mod_symm (h4460 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq17 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = (X1 ◇ (X3 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11
  have eq100 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq17 eq13 -- superposition 13,17
  subsumption eq100 eq22

theorem Equation4296_4512_implies_Equation4460 (G : Type*) [Magma G]
    (h4296 : Equation4296 G) (h4512 : Equation4512 G) : Equation4460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ X1)) := mod_symm (h4296 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq27 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK2 ◇ sK0)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq27 eq11


/- Equivalence of [4297, 4497] -/
theorem Equation4497_4512_implies_Equation4297 (G : Type*) [Magma G]
    (h4497 : Equation4497 G) (h4512 : Equation4512 G) : Equation4297 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ X2) ◇ X0) := mod_symm (h4497 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq20 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X2)) = (X1 ◇ (X3 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq29 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq123 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq20 eq13 -- superposition 13,20
  subsumption eq123 eq29

theorem Equation4297_4512_implies_Equation4497 (G : Type*) [Magma G]
    (h4297 : Equation4297 G) (h4512 : Equation4512 G) : Equation4497 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ X2)) := mod_symm (h4297 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq26 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ sK0)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq26 eq11


/- Equivalence of [4299, 4312, 4484, 4500] -/
theorem Equation4500_4512_implies_Equation4299 (G : Type*) [Magma G]
    (h4500 : Equation4500 G) (h4512 : Equation4512 G) : Equation4299 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ X2) ◇ X3) := mod_symm (h4500 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq20 (X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ X3)) = (X4 ◇ (X5 ◇ X5)) := superpose eq11 eq11 -- superposition 11,11
  have eq27 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ X3)) := superpose eq11 eq12 -- superposition 12,11
  have eq119 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq20 eq13 -- superposition 13,20
  subsumption eq119 eq27

theorem Equation4299_4512_implies_Equation4312 (G : Type*) [Magma G]
    (h4299 : Equation4299 G) (h4512 : Equation4512 G) : Equation4312 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h4299 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq16 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = (X3 ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq26 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq11 eq12 -- superposition 12,11
  have eq61 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK3 ◇ sK3)) := superpose eq16 eq13 -- superposition 13,16
  have eq183 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ X0)) ≠ (X1 ◇ (sK3 ◇ sK3)) := superpose eq20 eq61 -- superposition 61,20
  have eq343 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X3)) := superpose eq15 eq26 -- superposition 26,15
  have eq396 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) ≠ (X2 ◇ (sK3 ◇ sK3)) := superpose eq26 eq183 -- superposition 183,26
  subsumption eq396 eq343

theorem Equation4312_4512_implies_Equation4484 (G : Type*) [Magma G]
    (h4312 : Equation4312 G) (h4512 : Equation4512 G) : Equation4484 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ X3)) := mod_symm (h4312 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq26 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK2)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq26 eq11

theorem Equation4484_4512_implies_Equation4500 (G : Type*) [Magma G]
    (h4484 : Equation4484 G) (_ : Equation4512 G) : Equation4500 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ X2) := mod_symm (h4484 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X3) = (X2 ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq20 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK2 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  have eq35 (X1 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ X1) := superpose eq11 eq20 -- superposition 20,11
  subsumption eq35 eq15


/- Equivalence of [4300, 4330, 4374, 4529, 4546] -/
theorem Equation4546_4512_implies_Equation4300 (G : Type*) [Magma G]
    (h4546 : Equation4546 G) (_ : Equation4512 G) : Equation4300 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X2) := mod_symm (h4546 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq59 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK0 ◇ sK1)) := superpose eq19 eq13 -- superposition 13,19
  subsumption eq59 eq19

theorem Equation4300_4512_implies_Equation4330 (G : Type*) [Magma G]
    (h4300 : Equation4300 G) (_ : Equation4512 G) : Equation4330 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := mod_symm (h4300 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq17 eq14

theorem Equation4330_4512_implies_Equation4374 (G : Type*) [Magma G]
    (h4330 : Equation4330 G) (_ : Equation4512 G) : Equation4374 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := mod_symm (h4330 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK3 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq17 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK1 ◇ sK2)) := superpose eq11 eq13 -- superposition 13,11
  subsumption eq17 eq14

theorem Equation4374_4512_implies_Equation4529 (G : Type*) [Magma G]
    (h4374 : Equation4374 G) (h4512 : Equation4512 G) : Equation4529 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := mod_symm (h4374 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq25 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK1 ◇ sK2)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq25 eq11

theorem Equation4529_4512_implies_Equation4546 (G : Type*) [Magma G]
    (h4529 : Equation4529 G) (h4512 : Equation4512 G) : Equation4546 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ X2) := mod_symm (h4529 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq34 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK1 ◇ sK2)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq34 eq19


/- Equivalence of [4301, 4311, 4447, 4463] -/
theorem Equation4463_4512_implies_Equation4301 (G : Type*) [Magma G]
    (h4463 : Equation4463 G) (h4512 : Equation4512 G) : Equation4301 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X2) ◇ X3) := mod_symm (h4463 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq19 (X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ X2)) = (X4 ◇ (X5 ◇ X4)) := superpose eq11 eq11 -- superposition 11,11
  have eq25 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq110 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq19 eq13 -- superposition 13,19
  subsumption eq110 eq25

theorem Equation4301_4512_implies_Equation4311 (G : Type*) [Magma G]
    (h4301 : Equation4301 G) (_ : Equation4512 G) : Equation4311 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := mod_symm (h4301 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK3 ◇ sK2)) := mod_symm nh
  have eq16 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X3)) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq67 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK3 ◇ X0)) := superpose eq16 eq13 -- superposition 13,16
  have eq221 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ X0)) ≠ (X1 ◇ (sK3 ◇ X1)) := superpose eq21 eq67 -- superposition 67,21
  have eq460 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ X3)) := superpose eq11 eq18 -- superposition 18,11
  have eq502 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) ≠ (sK0 ◇ (sK0 ◇ X2)) := superpose eq18 eq221 -- superposition 221,18
  subsumption eq502 eq460

theorem Equation4311_4512_implies_Equation4447 (G : Type*) [Magma G]
    (h4311 : Equation4311 G) (h4512 : Equation4512 G) : Equation4447 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ X2)) := mod_symm (h4311 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq27 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK2)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq27 eq11

theorem Equation4447_4512_implies_Equation4463 (G : Type*) [Magma G]
    (h4447 : Equation4447 G) (_ : Equation4512 G) : Equation4463 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ X2) := mod_symm (h4447 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq17 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK2 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  have eq41 (X1 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK2) ◇ X1) := superpose eq11 eq21 -- superposition 21,11
  subsumption eq41 eq17


/- Equivalence of [4304, 4498] -/
theorem Equation4498_4512_implies_Equation4304 (G : Type*) [Magma G]
    (h4498 : Equation4498 G) (h4512 : Equation4512 G) : Equation4304 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ X2) ◇ X1) := mod_symm (h4498 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq18 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq27 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11
  have eq109 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq18 eq13 -- superposition 13,18
  subsumption eq109 eq27

theorem Equation4304_4512_implies_Equation4498 (G : Type*) [Magma G]
    (h4304 : Equation4304 G) (h4512 : Equation4512 G) : Equation4498 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := mod_symm (h4304 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq28 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ sK1)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq28 eq11


/- Equivalence of [4305, 4461] -/
theorem Equation4461_4512_implies_Equation4305 (G : Type*) [Magma G]
    (h4461 : Equation4461 G) (h4512 : Equation4512 G) : Equation4305 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X2) ◇ X1) := mod_symm (h4461 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq19 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq30 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq117 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq19 eq13 -- superposition 13,19
  subsumption eq117 eq30

theorem Equation4305_4512_implies_Equation4461 (G : Type*) [Magma G]
    (h4305 : Equation4305 G) (h4512 : Equation4512 G) : Equation4461 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X2)) := mod_symm (h4305 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq29 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK2 ◇ sK1)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq29 eq11


/- Equivalence of [4314, 4472] -/
theorem Equation4472_4512_implies_Equation4314 (G : Type*) [Magma G]
    (h4472 : Equation4472 G) (h4512 : Equation4512 G) : Equation4314 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := mod_symm (h4472 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq21 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose eq11 eq12 -- superposition 12,11
  have eq45 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq21 eq13 -- superposition 13,21
  subsumption eq45 rfl

theorem Equation4314_4512_implies_Equation4472 (G : Type*) [Magma G]
    (h4314 : Equation4314 G) (h4512 : Equation4512 G) : Equation4472 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h4314 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq14 eq11


/- Equivalence of [4315, 4339, 4357, 4510, 4511] -/
theorem Equation4511_4512_implies_Equation4315 (G : Type*) [Magma G]
    (h4511 : Equation4511 G) (_ : Equation4512 G) : Equation4315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X1) := mod_symm (h4511 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq73 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq18 eq13 -- superposition 13,18
  subsumption eq73 eq18

theorem Equation4315_4512_implies_Equation4339 (G : Type*) [Magma G]
    (h4315 : Equation4315 G) (_ : Equation4512 G) : Equation4339 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h4315 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation4339_4512_implies_Equation4357 (G : Type*) [Magma G]
    (h4339 : Equation4339 G) (_ : Equation4512 G) : Equation4357 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X2)) := mod_symm (h4339 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11

theorem Equation4357_4512_implies_Equation4510 (G : Type*) [Magma G]
    (h4357 : Equation4357 G) (h4512 : Equation4512 G) : Equation4510 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := mod_symm (h4357 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq14 eq11

theorem Equation4510_4512_implies_Equation4511 (G : Type*) [Magma G]
    (h4510 : Equation4510 G) (h4512 : Equation4512 G) : Equation4511 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X0) := mod_symm (h4510 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq64 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq19 eq14 -- superposition 14,19
  subsumption eq64 eq19


/- Equivalence of [4318, 4475] -/
theorem Equation4475_4512_implies_Equation4318 (G : Type*) [Magma G]
    (h4475 : Equation4475 G) (h4512 : Equation4512 G) : Equation4318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X2) ◇ X0) := mod_symm (h4475 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq17 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = (X0 ◇ (X3 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq22 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq108 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq17 eq13 -- superposition 13,17
  subsumption eq108 eq22

theorem Equation4318_4512_implies_Equation4475 (G : Type*) [Magma G]
    (h4318 : Equation4318 G) (h4512 : Equation4512 G) : Equation4475 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X2)) := mod_symm (h4318 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq25 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq25 eq11


/- Equivalence of [4320, 4480] -/
theorem Equation4480_4512_implies_Equation4320 (G : Type*) [Magma G]
    (h4480 : Equation4480 G) (h4512 : Equation4512 G) : Equation4320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := mod_symm (h4480 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq18 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := superpose eq11 eq12 -- superposition 12,11
  have eq41 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq18 eq13 -- superposition 13,18
  subsumption eq41 rfl

theorem Equation4320_4512_implies_Equation4480 (G : Type*) [Magma G]
    (h4320 : Equation4320 G) (h4512 : Equation4512 G) : Equation4480 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h4320 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq26 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq26 eq11


/- Equivalence of [4325, 4491] -/
theorem Equation4491_4512_implies_Equation4325 (G : Type*) [Magma G]
    (h4491 : Equation4491 G) (h4512 : Equation4512 G) : Equation4325 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h4491 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq19 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X2)) = (X1 ◇ (X3 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11
  have eq29 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X2 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11
  have eq115 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq19 eq13 -- superposition 13,19
  subsumption eq115 eq29

theorem Equation4325_4512_implies_Equation4491 (G : Type*) [Magma G]
    (h4325 : Equation4325 G) (h4512 : Equation4512 G) : Equation4491 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X2 ◇ X2)) := mod_symm (h4325 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq27 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK0 ◇ sK2)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq27 eq11


/- Equivalence of [4327, 4486] -/
theorem Equation4486_4512_implies_Equation4327 (G : Type*) [Magma G]
    (h4486 : Equation4486 G) (h4512 : Equation4512 G) : Equation4327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X2) ◇ X1) := mod_symm (h4486 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq19 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = (X3 ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11
  have eq30 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := superpose eq11 eq12 -- superposition 12,11
  have eq114 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ sK0)) := superpose eq19 eq13 -- superposition 13,19
  subsumption eq114 eq30

theorem Equation4327_4512_implies_Equation4486 (G : Type*) [Magma G]
    (h4327 : Equation4327 G) (h4512 : Equation4512 G) : Equation4486 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := mod_symm (h4327 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK1 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq28 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK2 ◇ sK1)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq28 eq11


/- Equivalence of [4331, 4337, 4495, 4503] -/
theorem Equation4503_4512_implies_Equation4331 (G : Type*) [Magma G]
    (h4503 : Equation4503 G) (h4512 : Equation4512 G) : Equation4331 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ X3) ◇ X2) := mod_symm (h4503 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq19 (X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ X3)) = (X4 ◇ (X5 ◇ X5)) := superpose eq11 eq11 -- superposition 11,11
  have eq26 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ X3)) := superpose eq11 eq12 -- superposition 12,11
  have eq108 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq19 eq13 -- superposition 13,19
  subsumption eq108 eq26

theorem Equation4331_4512_implies_Equation4337 (G : Type*) [Magma G]
    (h4331 : Equation4331 G) (_ : Equation4512 G) : Equation4337 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X1)) := mod_symm (h4331 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq16 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK3 ◇ X0)) := superpose eq11 eq13 -- superposition 13,11
  have eq38 (X0 X1 : G) : (X0 ◇ (sK1 ◇ sK1)) ≠ (X1 ◇ (sK3 ◇ X1)) := superpose eq11 eq21 -- superposition 21,11
  have eq62 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq16 eq11 -- superposition 11,16
  have eq142 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ≠ (X2 ◇ (sK1 ◇ sK1)) := superpose eq16 eq38 -- superposition 38,16
  subsumption eq142 eq62

theorem Equation4337_4512_implies_Equation4495 (G : Type*) [Magma G]
    (h4337 : Equation4337 G) (h4512 : Equation4512 G) : Equation4495 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ X3)) := mod_symm (h4337 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq26 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK2)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq26 eq11

theorem Equation4495_4512_implies_Equation4503 (G : Type*) [Magma G]
    (h4495 : Equation4495 G) (_ : Equation4512 G) : Equation4503 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ X1) ◇ X2) := mod_symm (h4495 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = ((X3 ◇ X0) ◇ X3) := superpose eq11 eq11 -- superposition 11,11
  have eq21 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK3 ◇ sK3)) := superpose eq11 eq13 -- superposition 13,11
  have eq39 (X1 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((X1 ◇ sK3) ◇ X1) := superpose eq11 eq21 -- superposition 21,11
  subsumption eq39 eq16


/- Equivalence of [4364, 4541] -/
theorem Equation4541_4512_implies_Equation4364 (G : Type*) [Magma G]
    (h4541 : Equation4541 G) (h4512 : Equation4512 G) : Equation4364 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X1) := mod_symm (h4541 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X0)) := superpose eq11 eq12 -- superposition 12,11
  have eq46 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq17 eq13 -- superposition 13,17
  subsumption eq46 rfl

theorem Equation4364_4512_implies_Equation4541 (G : Type*) [Magma G]
    (h4364 : Equation4364 G) (h4512 : Equation4512 G) : Equation4541 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h4364 ..)
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := mod_symm (h4512 ..)
  have eq13 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq27 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK0 ◇ sK1)) := superpose eq12 eq13 -- superposition 13,12
  subsumption eq27 eq11


end Conjectures

