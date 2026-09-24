/- Generated file proving equivalence of conjunction representatives -/

import equational_theories.Equations.All
import equational_theories.FactsSyntax
import associative_theories.EquationIndex
import associative_theories.AssociativeTheoriesIndex
import associative_theories.AssociativeTheoriesEarly
import associative_theories.AssociativeTheoriesLong
import associative_theories.VampireProvenOne
import associative_theories.VampireProvenTwo
import associative_theories.OneImpliDeduced
import associative_theories.EarlyLongEquiv
import associative_theories.ImplicationsAT

open EQIndex
open ATIndex
open VampireProven

set_option maxHeartbeats 1000000


def conj16 : EQIndex → ATIndex
| eq1 => at16
| eq2 => at2
| eq3 => at16
| eq4 => at2
| eq5 => at2
| eq8 => at16
| eq10 => at2
| eq11 => at2
| eq14 => at2
| eq16 => at2
| eq38 => at2
| eq39 => at2
| eq40 => at2
| eq41 => at2
| eq43 => at16
| eq47 => at16
| eq56 => at2
| eq66 => at2
| eq75 => at2
| eq307 => at16
| eq308 => at2
| eq309 => at2
| eq310 => at2
| eq311 => at2
| eq312 => at2
| eq313 => at2
| eq314 => at2
| eq315 => at2
| eq316 => at2
| eq318 => at2
| eq323 => at16
| eq325 => at16
| eq326 => at16
| eq327 => at2
| eq329 => at2
| eq332 => at16
| eq333 => at16
| eq343 => at2
| eq411 => at16
| eq419 => at2
| eq429 => at2
| eq440 => at2
| eq477 => at2
| eq504 => at2
| eq513 => at2
| eq3253 => at16
| eq3255 => at2
| eq3256 => at2
| eq3258 => at2
| eq3259 => at2
| eq3260 => at2
| eq3261 => at2
| eq3264 => at2
| eq3265 => at2
| eq3267 => at2
| eq3271 => at2
| eq3273 => at2
| eq3274 => at2
| eq3275 => at2
| eq3277 => at2
| eq3278 => at2
| eq3290 => at2
| eq3292 => at2
| eq3300 => at2
| eq3306 => at16
| eq3308 => at16
| eq3309 => at16
| eq3315 => at16
| eq3316 => at16
| eq3319 => at16
| eq3322 => at2
| eq3323 => at2
| eq3326 => at2
| eq3331 => at2
| eq3334 => at2
| eq3342 => at16
| eq3346 => at16
| eq3350 => at2
| eq3353 => at16
| eq3388 => at2
| eq3414 => at2
| eq4268 => at2
| eq4269 => at2
| eq4270 => at2
| eq4271 => at2
| eq4272 => at2
| eq4273 => at2
| eq4274 => at2
| eq4275 => at2
| eq4276 => at2
| eq4277 => at2
| eq4278 => at2
| eq4279 => at2
| eq4280 => at2
| eq4283 => at16
| eq4284 => at16
| eq4286 => at2
| eq4287 => at2
| eq4288 => at2
| eq4290 => at16
| eq4291 => at16
| eq4293 => at16
| eq4296 => at2
| eq4297 => at2
| eq4299 => at2
| eq4300 => at2
| eq4301 => at2
| eq4304 => at2
| eq4305 => at2
| eq4314 => at16
| eq4315 => at2
| eq4318 => at2
| eq4320 => at16
| eq4321 => at16
| eq4325 => at2
| eq4327 => at2
| eq4331 => at2
| eq4343 => at16
| eq4358 => at16
| eq4362 => at16
| eq4364 => at16
| eq4369 => at16
| eq4512 => at16


private theorem AT16_Equation1_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation1 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h1⟩ := h
  exact hh

private theorem AT16_Equation2_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation2 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h2⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h3⟩ := h
  exact hh

private theorem AT16_Equation4_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4268 := Equation4_4512_implies_Equation4268 G h4 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation5_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation5 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h5⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4269 := Equation5_4512_implies_Equation4269 G h5 h4512
  have h4273 := Equation4269_4290_4512_implies_Equation4273 G h4269 h4290 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation8_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation8 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h8⟩ := h
  exact hh

private theorem AT16_Equation10_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation10 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h10⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4269 := Equation10_4512_implies_Equation4269 G h10 h4512
  have h4273 := Equation4269_4290_4512_implies_Equation4273 G h4269 h4290 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation11_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation11 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h11⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4270 := Equation11_4512_implies_Equation4270 G h11 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation14_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation14 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h14⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4273 := Equation14_4512_implies_Equation4273 G h14 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation16_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation16 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h16⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4275 := Equation16_4512_implies_Equation4275 G h16 h4512
  have h4273 := Equation4275_4283_4512_implies_Equation4273 G h4275 h4283 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation38_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation38 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h38⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4268 := Equation38_4512_implies_Equation4268 G h38 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation39_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation39 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h39⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4269 := Equation39_4512_implies_Equation4269 G h39 h4512
  have h4273 := Equation4269_4290_4512_implies_Equation4273 G h4269 h4290 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation40_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation40 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h40⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4270 := Equation40_4512_implies_Equation4270 G h40 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation41_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation41 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h41⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4273 := Equation41_4512_implies_Equation4273 G h41 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation43_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation43 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h43⟩ := h
  exact hh

private theorem AT16_Equation47_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation47 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h47⟩ := h
  exact hh

private theorem AT16_Equation56_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation56 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h56⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h66 := Equation43_56_4512_implies_Equation66 G h43 h56 h4512
  have h4276 := Equation66_4512_implies_Equation4276 G h66 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation66_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation66 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h66⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4276 := Equation66_4512_implies_Equation4276 G h66 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation75_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation75 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h75⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h56 := Equation43_75_4512_implies_Equation56 G h43 h75 h4512
  have h4276 := Equation56_75_4512_implies_Equation4276 G h56 h75 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation307_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation307 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h307⟩ := h
  exact hh

private theorem AT16_Equation308_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation308 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h308⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4268 := Equation308_4512_implies_Equation4268 G h308 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation309_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation309 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h309⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4269 := Equation309_4512_implies_Equation4269 G h309 h4512
  have h4273 := Equation4269_4290_4512_implies_Equation4273 G h4269 h4290 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation310_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation310 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h310⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4268 := Equation310_4512_implies_Equation4268 G h310 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation311_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation311 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h311⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4268 := Equation311_4512_implies_Equation4268 G h311 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation312_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation312 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h312⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4272 := Equation312_4512_implies_Equation4272 G h312 h4512
  have h4268 := Equation4272_4290_4512_implies_Equation4268 G h4272 h4290 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation313_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation313 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h313⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4273 := Equation313_4512_implies_Equation4273 G h313 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation314_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation314 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h314⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4273 := Equation314_4512_implies_Equation4273 G h314 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation315_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation315 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4275 := Equation315_4512_implies_Equation4275 G h315 h4512
  have h4273 := Equation4275_4283_4512_implies_Equation4273 G h4275 h4283 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation316_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation316 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h316⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4276 := Equation316_4512_implies_Equation4276 G h316 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation318_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation318 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h318⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4269 := Equation318_4512_implies_Equation4269 G h318 h4512
  have h4273 := Equation4269_4290_4512_implies_Equation4273 G h4269 h4290 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation323_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation323 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h323⟩ := h
  exact hh

private theorem AT16_Equation325_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation325 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h325⟩ := h
  exact hh

private theorem AT16_Equation326_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation326 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h326⟩ := h
  exact hh

private theorem AT16_Equation327_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation327 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h327⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4268 := Equation327_4512_implies_Equation4268 G h327 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation329_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation329 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h329⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4269 := Equation329_4512_implies_Equation4269 G h329 h4512
  have h4273 := Equation4269_4290_4512_implies_Equation4273 G h4269 h4290 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation332_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation332 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h332⟩ := h
  exact hh

private theorem AT16_Equation333_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation333 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h333⟩ := h
  exact hh

private theorem AT16_Equation343_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation343 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h343⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4272 := Equation343_4512_implies_Equation4272 G h343 h4512
  have h4268 := Equation4272_4290_4512_implies_Equation4268 G h4272 h4290 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation411_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation411 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h411⟩ := h
  exact hh

private theorem AT16_Equation419_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation419 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h419⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4269 := Equation10_4512_implies_Equation4269 G h10 h4512
  have h4273 := Equation4269_4290_4512_implies_Equation4273 G h4269 h4290 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation429_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation429 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h429⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4269 := Equation10_4512_implies_Equation4269 G h10 h4512
  have h4273 := Equation4269_4290_4512_implies_Equation4273 G h4269 h4290 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation440_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation440 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h440⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  have h4270 := Equation11_4512_implies_Equation4270 G h11 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation477_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation477 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h477⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h440 := Equation477_4512_implies_Equation440 G h477 h4512
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  have h4270 := Equation11_4512_implies_Equation4270 G h11 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation504_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation504 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h504⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h440 := Equation504_4512_implies_Equation440 G h504 h4512
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  have h4270 := Equation11_4512_implies_Equation4270 G h11 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation513_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation513 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h513⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h16 := Equation8_513_4512_implies_Equation16 G h8 h513 h4512
  have h4275 := Equation16_4512_implies_Equation4275 G h16 h4512
  have h4273 := Equation4275_4283_4512_implies_Equation4273 G h4275 h4283 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3253_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3253 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h3253⟩ := h
  exact hh

private theorem AT16_Equation3255_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3255 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3255⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h308 := Equation3255_4283_4512_implies_Equation308 G h3255 h4283 h4512
  have h4268 := Equation308_4512_implies_Equation4268 G h308 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3256_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3256 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3256⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h308 := Equation307_3256_4512_implies_Equation308 G h307 h3256 h4512
  have h4268 := Equation308_4512_implies_Equation4268 G h308 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3258_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3258 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3258⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h4268 := Equation38_4512_implies_Equation4268 G h38 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3259_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3259 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3259⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4270 := Equation3259_4512_implies_Equation4270 G h3259 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3260_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3260 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3260⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4268 := Equation3260_4512_implies_Equation4268 G h3260 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3261_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3261 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3261⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h40 := Equation3261_4290_4512_implies_Equation40 G h3261 h4290 h4512
  have h4275 := Equation40_4512_implies_Equation4275 G h40 h4512
  have h4273 := Equation4275_4283_4512_implies_Equation4273 G h4275 h4283 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3264_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3264 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3264⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h3258 := Equation3264_4512_implies_Equation3258 G h3264 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h4268 := Equation38_4512_implies_Equation4268 G h38 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3265_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3265 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3265⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4268 := Equation3265_4512_implies_Equation4268 G h3265 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3267_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3267 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3267⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4268 := Equation3267_4512_implies_Equation4268 G h3267 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3271_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3271 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3271⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4275 := Equation3271_4512_implies_Equation4275 G h3271 h4512
  have h4273 := Equation4275_4283_4512_implies_Equation4273 G h4275 h4283 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3273_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3273 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3273⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4276 := Equation3273_4512_implies_Equation4276 G h3273 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3274_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3274 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3274⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4275 := Equation3274_4512_implies_Equation4275 G h3274 h4512
  have h4273 := Equation4275_4283_4512_implies_Equation4273 G h4275 h4283 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3275_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3275 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3275⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4276 := Equation3275_4512_implies_Equation4276 G h3275 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3277_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3277 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3277⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4276 := Equation3277_4512_implies_Equation4276 G h3277 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3278_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3278 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3278⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h40 := Equation3278_4283_4512_implies_Equation40 G h3278 h4283 h4512
  have h4270 := Equation40_4512_implies_Equation4270 G h40 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3290_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3290 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3290⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4276 := Equation3290_4512_implies_Equation4276 G h3290 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3292_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3292 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3292⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4275 := Equation3292_4512_implies_Equation4275 G h3292 h4512
  have h4273 := Equation4275_4283_4512_implies_Equation4273 G h4275 h4283 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3300_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3300 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3300⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4275 := Equation3300_4512_implies_Equation4275 G h3300 h4512
  have h4273 := Equation4275_4283_4512_implies_Equation4273 G h4275 h4283 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3306_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3306 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h3306⟩ := h
  exact hh

private theorem AT16_Equation3308_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3308 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h3308⟩ := h
  exact hh

private theorem AT16_Equation3309_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3309 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h3309⟩ := h
  exact hh

private theorem AT16_Equation3315_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3315 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h3315⟩ := h
  exact hh

private theorem AT16_Equation3316_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3316 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h3316⟩ := h
  exact hh

private theorem AT16_Equation3319_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3319 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h3319⟩ := h
  exact hh

private theorem AT16_Equation3322_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3322 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3322⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h3255 := Equation3322_4512_implies_Equation3255 G h3322 h4512
  have h308 := Equation3255_4283_4512_implies_Equation308 G h3255 h4283 h4512
  have h4268 := Equation308_4512_implies_Equation4268 G h308 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3323_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3323 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3323⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h3256 := Equation3323_4512_implies_Equation3256 G h3323 h4512
  have h308 := Equation307_3256_4512_implies_Equation308 G h307 h3256 h4512
  have h4268 := Equation308_4512_implies_Equation4268 G h308 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3326_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3326 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3326⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h3258 := Equation3326_4512_implies_Equation3258 G h3326 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h4268 := Equation38_4512_implies_Equation4268 G h38 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3331_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3331 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3331⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4270 := Equation3331_4512_implies_Equation4270 G h3331 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3334_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3334 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3334⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h3261 := Equation3334_4512_implies_Equation3261 G h3334 h4512
  have h40 := Equation3261_4290_4512_implies_Equation40 G h3261 h4290 h4512
  have h4275 := Equation40_4512_implies_Equation4275 G h40 h4512
  have h4273 := Equation4275_4283_4512_implies_Equation4273 G h4275 h4283 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3342_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3342 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h3342⟩ := h
  exact hh

private theorem AT16_Equation3346_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3346 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h3346⟩ := h
  exact hh

private theorem AT16_Equation3350_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3350 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3350⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4273 := Equation3350_4512_implies_Equation4273 G h3350 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3353_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3353 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h3353⟩ := h
  exact hh

private theorem AT16_Equation3388_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3388 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3388⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4275 := Equation3388_4512_implies_Equation4275 G h3388 h4512
  have h4273 := Equation4275_4283_4512_implies_Equation4273 G h4275 h4283 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation3414_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation3414 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3414⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h3278 := Equation3414_4512_implies_Equation3278 G h3414 h4512
  have h40 := Equation3278_4283_4512_implies_Equation40 G h3278 h4283 h4512
  have h4270 := Equation40_4512_implies_Equation4270 G h40 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4268_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4268 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4268⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4269_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4269 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4269⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4273 := Equation4269_4290_4512_implies_Equation4273 G h4269 h4290 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4270_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4270 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4270⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4271_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4271 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4271⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4268 := Equation4271_4512_implies_Equation4268 G h4271 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4272_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4272 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4272⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4268 := Equation4272_4290_4512_implies_Equation4268 G h4272 h4290 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4273_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4273 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4273⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4274_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4274 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4274⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4273 := Equation4274_4512_implies_Equation4273 G h4274 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4275_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4275 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4275⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4273 := Equation4275_4283_4512_implies_Equation4273 G h4275 h4283 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4276_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4276 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4276⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4277_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4277 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4277⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4276 := Equation4277_4512_implies_Equation4276 G h4277 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4278_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4278 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4278⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4269 := Equation4278_4512_implies_Equation4269 G h4278 h4512
  have h4273 := Equation4269_4290_4512_implies_Equation4273 G h4269 h4290 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4279_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4279 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4279⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4276 := Equation4279_4512_implies_Equation4276 G h4279 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4280_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4280 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4280⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4276 := Equation4280_4512_implies_Equation4276 G h4280 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4283_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4283 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h4283⟩ := h
  exact hh

private theorem AT16_Equation4284_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4284 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h4284⟩ := h
  exact hh

private theorem AT16_Equation4286_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4286 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4286⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4268 := Equation4286_4512_implies_Equation4268 G h4286 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4287_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4287 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4287⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4269 := Equation4287_4512_implies_Equation4269 G h4287 h4512
  have h4273 := Equation4269_4290_4512_implies_Equation4273 G h4269 h4290 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4288_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4288 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4288⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4268 := Equation4288_4512_implies_Equation4268 G h4288 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4290_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4290 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h4290⟩ := h
  exact hh

private theorem AT16_Equation4291_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4291 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h4291⟩ := h
  exact hh

private theorem AT16_Equation4293_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4293 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h4293⟩ := h
  exact hh

private theorem AT16_Equation4296_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4296 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4296⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4269 := Equation4296_4512_implies_Equation4269 G h4296 h4512
  have h4273 := Equation4269_4290_4512_implies_Equation4273 G h4269 h4290 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4297_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4297 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4297⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4270 := Equation4297_4512_implies_Equation4270 G h4297 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4299_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4299 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4299⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4276 := Equation4299_4512_implies_Equation4276 G h4299 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4300_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4300 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4300⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4272 := Equation4300_4512_implies_Equation4272 G h4300 h4512
  have h4268 := Equation4272_4290_4512_implies_Equation4268 G h4272 h4290 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4301_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4301 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4301⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4276 := Equation4301_4512_implies_Equation4276 G h4301 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4304_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4304 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4304⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4275 := Equation4304_4512_implies_Equation4275 G h4304 h4512
  have h4273 := Equation4275_4283_4512_implies_Equation4273 G h4275 h4283 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4305_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4305 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4305⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4273 := Equation4305_4512_implies_Equation4273 G h4305 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4314_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4314 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h4314⟩ := h
  exact hh

private theorem AT16_Equation4315_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4315 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4268 := Equation4315_4512_implies_Equation4268 G h4315 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4318_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4318 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4318⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4269 := Equation4318_4512_implies_Equation4269 G h4318 h4512
  have h4273 := Equation4269_4290_4512_implies_Equation4273 G h4269 h4290 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4320_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4320 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h4320⟩ := h
  exact hh

private theorem AT16_Equation4321_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4321 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h4321⟩ := h
  exact hh

private theorem AT16_Equation4325_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4325 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4325⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4273 := Equation4325_4512_implies_Equation4273 G h4325 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4327_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4327 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4327⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4269 := Equation4327_4512_implies_Equation4269 G h4327 h4512
  have h4273 := Equation4269_4290_4512_implies_Equation4273 G h4269 h4290 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4331_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4331 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4331⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at16
  obtain ⟨h1, h3, h8, h43, h47, h307, h323, h325, h326, h332, h333, h411, h3253, h3306, h3308, h3309, h3315, h3316, h3319, h3342, h3346, h3353, h4283, h4284, h4290, h4291, h4293, h4314, h4320, h4321, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h4276 := Equation4331_4512_implies_Equation4276 G h4331 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT16_Equation4343_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4343 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h4343⟩ := h
  exact hh

private theorem AT16_Equation4358_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4358 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h4358⟩ := h
  exact hh

private theorem AT16_Equation4362_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4362 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h4362⟩ := h
  exact hh

private theorem AT16_Equation4364_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4364 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h4364⟩ := h
  exact hh

private theorem AT16_Equation4369_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4369 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h4369⟩ := h
  exact hh

private theorem AT16_Equation4512_implies (G : Type*) [Magma G] (h : (AssociativeTheory16 G) ∧ (Equation4512 G)) : AssociativeTheory16 G := by
  obtain ⟨hh, h4512⟩ := h
  exact hh

theorem AT16_conj_implied (G: Type*) [Magma G] (eqid : EQIndex) (h : ATearly G (conj16 eqid)) : (AssociativeTheory16 G) ∧ (EQeq G eqid) := by
  have h0 := (AT_equiv G (conj16 eqid)).mp h
  rcases eqid
  all_goals
    constructor
    exact AT_implies G _ h at16 True.intro
    repeat' (obtain ⟨h1, h0⟩ := h0 ; try exact h1) ; try exact h0

theorem AT16_conj (G: Type*) [Magma G] (eqid : EQIndex) : (AssociativeTheory16 G) ∧ (EQeq G eqid) <-> (ATearly G (conj16 eqid)) :=
⟨match eqid with
| eq1 => AT16_Equation1_implies G
| eq2 => AT16_Equation2_implies G
| eq3 => AT16_Equation3_implies G
| eq4 => AT16_Equation4_implies G
| eq5 => AT16_Equation5_implies G
| eq8 => AT16_Equation8_implies G
| eq10 => AT16_Equation10_implies G
| eq11 => AT16_Equation11_implies G
| eq14 => AT16_Equation14_implies G
| eq16 => AT16_Equation16_implies G
| eq38 => AT16_Equation38_implies G
| eq39 => AT16_Equation39_implies G
| eq40 => AT16_Equation40_implies G
| eq41 => AT16_Equation41_implies G
| eq43 => AT16_Equation43_implies G
| eq47 => AT16_Equation47_implies G
| eq56 => AT16_Equation56_implies G
| eq66 => AT16_Equation66_implies G
| eq75 => AT16_Equation75_implies G
| eq307 => AT16_Equation307_implies G
| eq308 => AT16_Equation308_implies G
| eq309 => AT16_Equation309_implies G
| eq310 => AT16_Equation310_implies G
| eq311 => AT16_Equation311_implies G
| eq312 => AT16_Equation312_implies G
| eq313 => AT16_Equation313_implies G
| eq314 => AT16_Equation314_implies G
| eq315 => AT16_Equation315_implies G
| eq316 => AT16_Equation316_implies G
| eq318 => AT16_Equation318_implies G
| eq323 => AT16_Equation323_implies G
| eq325 => AT16_Equation325_implies G
| eq326 => AT16_Equation326_implies G
| eq327 => AT16_Equation327_implies G
| eq329 => AT16_Equation329_implies G
| eq332 => AT16_Equation332_implies G
| eq333 => AT16_Equation333_implies G
| eq343 => AT16_Equation343_implies G
| eq411 => AT16_Equation411_implies G
| eq419 => AT16_Equation419_implies G
| eq429 => AT16_Equation429_implies G
| eq440 => AT16_Equation440_implies G
| eq477 => AT16_Equation477_implies G
| eq504 => AT16_Equation504_implies G
| eq513 => AT16_Equation513_implies G
| eq3253 => AT16_Equation3253_implies G
| eq3255 => AT16_Equation3255_implies G
| eq3256 => AT16_Equation3256_implies G
| eq3258 => AT16_Equation3258_implies G
| eq3259 => AT16_Equation3259_implies G
| eq3260 => AT16_Equation3260_implies G
| eq3261 => AT16_Equation3261_implies G
| eq3264 => AT16_Equation3264_implies G
| eq3265 => AT16_Equation3265_implies G
| eq3267 => AT16_Equation3267_implies G
| eq3271 => AT16_Equation3271_implies G
| eq3273 => AT16_Equation3273_implies G
| eq3274 => AT16_Equation3274_implies G
| eq3275 => AT16_Equation3275_implies G
| eq3277 => AT16_Equation3277_implies G
| eq3278 => AT16_Equation3278_implies G
| eq3290 => AT16_Equation3290_implies G
| eq3292 => AT16_Equation3292_implies G
| eq3300 => AT16_Equation3300_implies G
| eq3306 => AT16_Equation3306_implies G
| eq3308 => AT16_Equation3308_implies G
| eq3309 => AT16_Equation3309_implies G
| eq3315 => AT16_Equation3315_implies G
| eq3316 => AT16_Equation3316_implies G
| eq3319 => AT16_Equation3319_implies G
| eq3322 => AT16_Equation3322_implies G
| eq3323 => AT16_Equation3323_implies G
| eq3326 => AT16_Equation3326_implies G
| eq3331 => AT16_Equation3331_implies G
| eq3334 => AT16_Equation3334_implies G
| eq3342 => AT16_Equation3342_implies G
| eq3346 => AT16_Equation3346_implies G
| eq3350 => AT16_Equation3350_implies G
| eq3353 => AT16_Equation3353_implies G
| eq3388 => AT16_Equation3388_implies G
| eq3414 => AT16_Equation3414_implies G
| eq4268 => AT16_Equation4268_implies G
| eq4269 => AT16_Equation4269_implies G
| eq4270 => AT16_Equation4270_implies G
| eq4271 => AT16_Equation4271_implies G
| eq4272 => AT16_Equation4272_implies G
| eq4273 => AT16_Equation4273_implies G
| eq4274 => AT16_Equation4274_implies G
| eq4275 => AT16_Equation4275_implies G
| eq4276 => AT16_Equation4276_implies G
| eq4277 => AT16_Equation4277_implies G
| eq4278 => AT16_Equation4278_implies G
| eq4279 => AT16_Equation4279_implies G
| eq4280 => AT16_Equation4280_implies G
| eq4283 => AT16_Equation4283_implies G
| eq4284 => AT16_Equation4284_implies G
| eq4286 => AT16_Equation4286_implies G
| eq4287 => AT16_Equation4287_implies G
| eq4288 => AT16_Equation4288_implies G
| eq4290 => AT16_Equation4290_implies G
| eq4291 => AT16_Equation4291_implies G
| eq4293 => AT16_Equation4293_implies G
| eq4296 => AT16_Equation4296_implies G
| eq4297 => AT16_Equation4297_implies G
| eq4299 => AT16_Equation4299_implies G
| eq4300 => AT16_Equation4300_implies G
| eq4301 => AT16_Equation4301_implies G
| eq4304 => AT16_Equation4304_implies G
| eq4305 => AT16_Equation4305_implies G
| eq4314 => AT16_Equation4314_implies G
| eq4315 => AT16_Equation4315_implies G
| eq4318 => AT16_Equation4318_implies G
| eq4320 => AT16_Equation4320_implies G
| eq4321 => AT16_Equation4321_implies G
| eq4325 => AT16_Equation4325_implies G
| eq4327 => AT16_Equation4327_implies G
| eq4331 => AT16_Equation4331_implies G
| eq4343 => AT16_Equation4343_implies G
| eq4358 => AT16_Equation4358_implies G
| eq4362 => AT16_Equation4362_implies G
| eq4364 => AT16_Equation4364_implies G
| eq4369 => AT16_Equation4369_implies G
| eq4512 => AT16_Equation4512_implies G
, AT16_conj_implied G eqid⟩

