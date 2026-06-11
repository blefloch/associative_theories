/- Generated file proving equivalence of conjunction representatives -/

import equational_theories.Equations.All
import equational_theories.FactsSyntax
import associative_theories.EquationIndex
import associative_theories.AssociativeTheoriesIndex
import associative_theories.AssociativeTheoriesEarly
import associative_theories.AssociativeTheoriesLong
import associative_theories.ConjecturesOneImpli
import associative_theories.ConjecturesTwo
import associative_theories.OneImpliDeduced
import associative_theories.EarlyLongEquiv

open EQIndex
open ATIndex
open Conjectures

set_option maxHeartbeats 1000000


def conj13 : EQIndex → ATIndex
| eq1 => at13
| eq2 => at2
| eq3 => at2
| eq4 => at2
| eq5 => at2
| eq8 => at2
| eq10 => at2
| eq11 => at2
| eq14 => at2
| eq16 => at2
| eq38 => at13
| eq39 => at13
| eq40 => at13
| eq41 => at13
| eq43 => at13
| eq47 => at2
| eq56 => at2
| eq66 => at2
| eq75 => at2
| eq307 => at13
| eq308 => at13
| eq309 => at13
| eq310 => at13
| eq311 => at13
| eq312 => at13
| eq313 => at13
| eq314 => at13
| eq315 => at13
| eq316 => at13
| eq318 => at13
| eq323 => at13
| eq325 => at13
| eq326 => at13
| eq327 => at13
| eq329 => at13
| eq332 => at13
| eq333 => at13
| eq343 => at13
| eq411 => at2
| eq419 => at2
| eq429 => at2
| eq440 => at2
| eq477 => at2
| eq504 => at2
| eq513 => at2
| eq3253 => at13
| eq3255 => at13
| eq3256 => at13
| eq3258 => at13
| eq3259 => at13
| eq3260 => at13
| eq3261 => at13
| eq3264 => at13
| eq3265 => at13
| eq3267 => at13
| eq3271 => at13
| eq3273 => at13
| eq3274 => at13
| eq3275 => at13
| eq3277 => at13
| eq3278 => at13
| eq3290 => at13
| eq3292 => at13
| eq3300 => at13
| eq3306 => at13
| eq3308 => at13
| eq3309 => at13
| eq3315 => at13
| eq3316 => at13
| eq3319 => at13
| eq3322 => at13
| eq3323 => at13
| eq3326 => at13
| eq3331 => at13
| eq3334 => at13
| eq3342 => at13
| eq3346 => at13
| eq3350 => at13
| eq3353 => at13
| eq3388 => at13
| eq3414 => at13
| eq4268 => at13
| eq4269 => at13
| eq4270 => at13
| eq4271 => at13
| eq4272 => at13
| eq4273 => at13
| eq4274 => at13
| eq4275 => at13
| eq4276 => at13
| eq4277 => at13
| eq4278 => at13
| eq4279 => at13
| eq4280 => at13
| eq4283 => at13
| eq4284 => at13
| eq4286 => at13
| eq4287 => at13
| eq4288 => at13
| eq4290 => at13
| eq4291 => at13
| eq4293 => at13
| eq4296 => at13
| eq4297 => at13
| eq4299 => at13
| eq4300 => at13
| eq4301 => at13
| eq4304 => at13
| eq4305 => at13
| eq4314 => at13
| eq4315 => at13
| eq4318 => at13
| eq4320 => at13
| eq4321 => at13
| eq4325 => at13
| eq4327 => at13
| eq4331 => at13
| eq4343 => at13
| eq4358 => at13
| eq4362 => at13
| eq4364 => at13
| eq4369 => at13
| eq4512 => at13


private theorem AT13_Equation1_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation1 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h1⟩ := h
  exact hh

private theorem AT13_Equation2_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation2 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h2⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at13
  obtain ⟨h1, h38, h39, h40, h41, h43, h307, h308, h309, h310, h311, h312, h313, h314, h315, h316, h318, h323, h325, h326, h327, h329, h332, h333, h343, h3253, h3255, h3256, h3258, h3259, h3260, h3261, h3264, h3265, h3267, h3271, h3273, h3274, h3275, h3277, h3278, h3290, h3292, h3300, h3306, h3308, h3309, h3315, h3316, h3319, h3322, h3323, h3326, h3331, h3334, h3342, h3346, h3350, h3353, h3388, h3414, h4268, h4269, h4270, h4271, h4272, h4273, h4274, h4275, h4276, h4277, h4278, h4279, h4280, h4283, h4284, h4286, h4287, h4288, h4290, h4291, h4293, h4296, h4297, h4299, h4300, h4301, h4304, h4305, h4314, h4315, h4318, h4320, h4321, h4325, h4327, h4331, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  exact ⟨h2, h4512⟩

private theorem AT13_Equation3_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at13
  obtain ⟨h1, h38, h39, h40, h41, h43, h307, h308, h309, h310, h311, h312, h313, h314, h315, h316, h318, h323, h325, h326, h327, h329, h332, h333, h343, h3253, h3255, h3256, h3258, h3259, h3260, h3261, h3264, h3265, h3267, h3271, h3273, h3274, h3275, h3277, h3278, h3290, h3292, h3300, h3306, h3308, h3309, h3315, h3316, h3319, h3322, h3323, h3326, h3331, h3334, h3342, h3346, h3350, h3353, h3388, h3414, h4268, h4269, h4270, h4271, h4272, h4273, h4274, h4275, h4276, h4277, h4278, h4279, h4280, h4283, h4284, h4286, h4287, h4288, h4290, h4291, h4293, h4296, h4297, h4299, h4300, h4301, h4304, h4305, h4314, h4315, h4318, h4320, h4321, h4325, h4327, h4331, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT13_Equation4_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at13
  obtain ⟨h1, h38, h39, h40, h41, h43, h307, h308, h309, h310, h311, h312, h313, h314, h315, h316, h318, h323, h325, h326, h327, h329, h332, h333, h343, h3253, h3255, h3256, h3258, h3259, h3260, h3261, h3264, h3265, h3267, h3271, h3273, h3274, h3275, h3277, h3278, h3290, h3292, h3300, h3306, h3308, h3309, h3315, h3316, h3319, h3322, h3323, h3326, h3331, h3334, h3342, h3346, h3350, h3353, h3388, h3414, h4268, h4269, h4270, h4271, h4272, h4273, h4274, h4275, h4276, h4277, h4278, h4279, h4280, h4283, h4284, h4286, h4287, h4288, h4290, h4291, h4293, h4296, h4297, h4299, h4300, h4301, h4304, h4305, h4314, h4315, h4318, h4320, h4321, h4325, h4327, h4331, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h47 := Equation4_4512_implies_Equation47 G h4 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT13_Equation5_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation5 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h5⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at13
  obtain ⟨h1, h38, h39, h40, h41, h43, h307, h308, h309, h310, h311, h312, h313, h314, h315, h316, h318, h323, h325, h326, h327, h329, h332, h333, h343, h3253, h3255, h3256, h3258, h3259, h3260, h3261, h3264, h3265, h3267, h3271, h3273, h3274, h3275, h3277, h3278, h3290, h3292, h3300, h3306, h3308, h3309, h3315, h3316, h3319, h3322, h3323, h3326, h3331, h3334, h3342, h3346, h3350, h3353, h3388, h3414, h4268, h4269, h4270, h4271, h4272, h4273, h4274, h4275, h4276, h4277, h4278, h4279, h4280, h4283, h4284, h4286, h4287, h4288, h4290, h4291, h4293, h4296, h4297, h4299, h4300, h4301, h4304, h4305, h4314, h4315, h4318, h4320, h4321, h4325, h4327, h4331, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h47 := Equation5_4512_implies_Equation47 G h5 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT13_Equation8_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation8 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h8⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at13
  obtain ⟨h1, h38, h39, h40, h41, h43, h307, h308, h309, h310, h311, h312, h313, h314, h315, h316, h318, h323, h325, h326, h327, h329, h332, h333, h343, h3253, h3255, h3256, h3258, h3259, h3260, h3261, h3264, h3265, h3267, h3271, h3273, h3274, h3275, h3277, h3278, h3290, h3292, h3300, h3306, h3308, h3309, h3315, h3316, h3319, h3322, h3323, h3326, h3331, h3334, h3342, h3346, h3350, h3353, h3388, h3414, h4268, h4269, h4270, h4271, h4272, h4273, h4274, h4275, h4276, h4277, h4278, h4279, h4280, h4283, h4284, h4286, h4287, h4288, h4290, h4291, h4293, h4296, h4297, h4299, h4300, h4301, h4304, h4305, h4314, h4315, h4318, h4320, h4321, h4325, h4327, h4331, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h411 := Equation8_4512_implies_Equation411 G h8 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT13_Equation10_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation10 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h10⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at13
  obtain ⟨h1, h38, h39, h40, h41, h43, h307, h308, h309, h310, h311, h312, h313, h314, h315, h316, h318, h323, h325, h326, h327, h329, h332, h333, h343, h3253, h3255, h3256, h3258, h3259, h3260, h3261, h3264, h3265, h3267, h3271, h3273, h3274, h3275, h3277, h3278, h3290, h3292, h3300, h3306, h3308, h3309, h3315, h3316, h3319, h3322, h3323, h3326, h3331, h3334, h3342, h3346, h3350, h3353, h3388, h3414, h4268, h4269, h4270, h4271, h4272, h4273, h4274, h4275, h4276, h4277, h4278, h4279, h4280, h4283, h4284, h4286, h4287, h4288, h4290, h4291, h4293, h4296, h4297, h4299, h4300, h4301, h4304, h4305, h4314, h4315, h4318, h4320, h4321, h4325, h4327, h4331, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h47 := Equation10_4512_implies_Equation47 G h10 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT13_Equation11_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation11 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h11⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at13
  obtain ⟨h1, h38, h39, h40, h41, h43, h307, h308, h309, h310, h311, h312, h313, h314, h315, h316, h318, h323, h325, h326, h327, h329, h332, h333, h343, h3253, h3255, h3256, h3258, h3259, h3260, h3261, h3264, h3265, h3267, h3271, h3273, h3274, h3275, h3277, h3278, h3290, h3292, h3300, h3306, h3308, h3309, h3315, h3316, h3319, h3322, h3323, h3326, h3331, h3334, h3342, h3346, h3350, h3353, h3388, h3414, h4268, h4269, h4270, h4271, h4272, h4273, h4274, h4275, h4276, h4277, h4278, h4279, h4280, h4283, h4284, h4286, h4287, h4288, h4290, h4291, h4293, h4296, h4297, h4299, h4300, h4301, h4304, h4305, h4314, h4315, h4318, h4320, h4321, h4325, h4327, h4331, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h411 := Equation11_4512_implies_Equation411 G h11 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT13_Equation14_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation14 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h14⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at13
  obtain ⟨h1, h38, h39, h40, h41, h43, h307, h308, h309, h310, h311, h312, h313, h314, h315, h316, h318, h323, h325, h326, h327, h329, h332, h333, h343, h3253, h3255, h3256, h3258, h3259, h3260, h3261, h3264, h3265, h3267, h3271, h3273, h3274, h3275, h3277, h3278, h3290, h3292, h3300, h3306, h3308, h3309, h3315, h3316, h3319, h3322, h3323, h3326, h3331, h3334, h3342, h3346, h3350, h3353, h3388, h3414, h4268, h4269, h4270, h4271, h4272, h4273, h4274, h4275, h4276, h4277, h4278, h4279, h4280, h4283, h4284, h4286, h4287, h4288, h4290, h4291, h4293, h4296, h4297, h4299, h4300, h4301, h4304, h4305, h4314, h4315, h4318, h4320, h4321, h4325, h4327, h4331, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h411 := Equation14_4512_implies_Equation411 G h14 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT13_Equation16_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation16 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h16⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at13
  obtain ⟨h1, h38, h39, h40, h41, h43, h307, h308, h309, h310, h311, h312, h313, h314, h315, h316, h318, h323, h325, h326, h327, h329, h332, h333, h343, h3253, h3255, h3256, h3258, h3259, h3260, h3261, h3264, h3265, h3267, h3271, h3273, h3274, h3275, h3277, h3278, h3290, h3292, h3300, h3306, h3308, h3309, h3315, h3316, h3319, h3322, h3323, h3326, h3331, h3334, h3342, h3346, h3350, h3353, h3388, h3414, h4268, h4269, h4270, h4271, h4272, h4273, h4274, h4275, h4276, h4277, h4278, h4279, h4280, h4283, h4284, h4286, h4287, h4288, h4290, h4291, h4293, h4296, h4297, h4299, h4300, h4301, h4304, h4305, h4314, h4315, h4318, h4320, h4321, h4325, h4327, h4331, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h411 := Equation16_4512_implies_Equation411 G h16 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT13_Equation38_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation38 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h38⟩ := h
  exact hh

private theorem AT13_Equation39_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation39 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h39⟩ := h
  exact hh

private theorem AT13_Equation40_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation40 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h40⟩ := h
  exact hh

private theorem AT13_Equation41_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation41 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h41⟩ := h
  exact hh

private theorem AT13_Equation43_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation43 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h43⟩ := h
  exact hh

private theorem AT13_Equation47_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation47 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h47⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at13
  obtain ⟨h1, h38, h39, h40, h41, h43, h307, h308, h309, h310, h311, h312, h313, h314, h315, h316, h318, h323, h325, h326, h327, h329, h332, h333, h343, h3253, h3255, h3256, h3258, h3259, h3260, h3261, h3264, h3265, h3267, h3271, h3273, h3274, h3275, h3277, h3278, h3290, h3292, h3300, h3306, h3308, h3309, h3315, h3316, h3319, h3322, h3323, h3326, h3331, h3334, h3342, h3346, h3350, h3353, h3388, h3414, h4268, h4269, h4270, h4271, h4272, h4273, h4274, h4275, h4276, h4277, h4278, h4279, h4280, h4283, h4284, h4286, h4287, h4288, h4290, h4291, h4293, h4296, h4297, h4299, h4300, h4301, h4304, h4305, h4314, h4315, h4318, h4320, h4321, h4325, h4327, h4331, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT13_Equation56_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation56 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h56⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at13
  obtain ⟨h1, h38, h39, h40, h41, h43, h307, h308, h309, h310, h311, h312, h313, h314, h315, h316, h318, h323, h325, h326, h327, h329, h332, h333, h343, h3253, h3255, h3256, h3258, h3259, h3260, h3261, h3264, h3265, h3267, h3271, h3273, h3274, h3275, h3277, h3278, h3290, h3292, h3300, h3306, h3308, h3309, h3315, h3316, h3319, h3322, h3323, h3326, h3331, h3334, h3342, h3346, h3350, h3353, h3388, h3414, h4268, h4269, h4270, h4271, h4272, h4273, h4274, h4275, h4276, h4277, h4278, h4279, h4280, h4283, h4284, h4286, h4287, h4288, h4290, h4291, h4293, h4296, h4297, h4299, h4300, h4301, h4304, h4305, h4314, h4315, h4318, h4320, h4321, h4325, h4327, h4331, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h47 := Equation56_4512_implies_Equation47 G h56 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT13_Equation66_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation66 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h66⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at13
  obtain ⟨h1, h38, h39, h40, h41, h43, h307, h308, h309, h310, h311, h312, h313, h314, h315, h316, h318, h323, h325, h326, h327, h329, h332, h333, h343, h3253, h3255, h3256, h3258, h3259, h3260, h3261, h3264, h3265, h3267, h3271, h3273, h3274, h3275, h3277, h3278, h3290, h3292, h3300, h3306, h3308, h3309, h3315, h3316, h3319, h3322, h3323, h3326, h3331, h3334, h3342, h3346, h3350, h3353, h3388, h3414, h4268, h4269, h4270, h4271, h4272, h4273, h4274, h4275, h4276, h4277, h4278, h4279, h4280, h4283, h4284, h4286, h4287, h4288, h4290, h4291, h4293, h4296, h4297, h4299, h4300, h4301, h4304, h4305, h4314, h4315, h4318, h4320, h4321, h4325, h4327, h4331, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h47 := Equation66_4512_implies_Equation47 G h66 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT13_Equation75_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation75 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h75⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at13
  obtain ⟨h1, h38, h39, h40, h41, h43, h307, h308, h309, h310, h311, h312, h313, h314, h315, h316, h318, h323, h325, h326, h327, h329, h332, h333, h343, h3253, h3255, h3256, h3258, h3259, h3260, h3261, h3264, h3265, h3267, h3271, h3273, h3274, h3275, h3277, h3278, h3290, h3292, h3300, h3306, h3308, h3309, h3315, h3316, h3319, h3322, h3323, h3326, h3331, h3334, h3342, h3346, h3350, h3353, h3388, h3414, h4268, h4269, h4270, h4271, h4272, h4273, h4274, h4275, h4276, h4277, h4278, h4279, h4280, h4283, h4284, h4286, h4287, h4288, h4290, h4291, h4293, h4296, h4297, h4299, h4300, h4301, h4304, h4305, h4314, h4315, h4318, h4320, h4321, h4325, h4327, h4331, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h47 := Equation75_4512_implies_Equation47 G h75 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT13_Equation307_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation307 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h307⟩ := h
  exact hh

private theorem AT13_Equation308_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation308 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h308⟩ := h
  exact hh

private theorem AT13_Equation309_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation309 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h309⟩ := h
  exact hh

private theorem AT13_Equation310_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation310 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h310⟩ := h
  exact hh

private theorem AT13_Equation311_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation311 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h311⟩ := h
  exact hh

private theorem AT13_Equation312_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation312 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h312⟩ := h
  exact hh

private theorem AT13_Equation313_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation313 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h313⟩ := h
  exact hh

private theorem AT13_Equation314_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation314 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h314⟩ := h
  exact hh

private theorem AT13_Equation315_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation315 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h315⟩ := h
  exact hh

private theorem AT13_Equation316_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation316 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h316⟩ := h
  exact hh

private theorem AT13_Equation318_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation318 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h318⟩ := h
  exact hh

private theorem AT13_Equation323_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation323 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h323⟩ := h
  exact hh

private theorem AT13_Equation325_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation325 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h325⟩ := h
  exact hh

private theorem AT13_Equation326_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation326 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h326⟩ := h
  exact hh

private theorem AT13_Equation327_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation327 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h327⟩ := h
  exact hh

private theorem AT13_Equation329_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation329 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h329⟩ := h
  exact hh

private theorem AT13_Equation332_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation332 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h332⟩ := h
  exact hh

private theorem AT13_Equation333_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation333 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h333⟩ := h
  exact hh

private theorem AT13_Equation343_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation343 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h343⟩ := h
  exact hh

private theorem AT13_Equation411_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation411 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h411⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at13
  obtain ⟨h1, h38, h39, h40, h41, h43, h307, h308, h309, h310, h311, h312, h313, h314, h315, h316, h318, h323, h325, h326, h327, h329, h332, h333, h343, h3253, h3255, h3256, h3258, h3259, h3260, h3261, h3264, h3265, h3267, h3271, h3273, h3274, h3275, h3277, h3278, h3290, h3292, h3300, h3306, h3308, h3309, h3315, h3316, h3319, h3322, h3323, h3326, h3331, h3334, h3342, h3346, h3350, h3353, h3388, h3414, h4268, h4269, h4270, h4271, h4272, h4273, h4274, h4275, h4276, h4277, h4278, h4279, h4280, h4283, h4284, h4286, h4287, h4288, h4290, h4291, h4293, h4296, h4297, h4299, h4300, h4301, h4304, h4305, h4314, h4315, h4318, h4320, h4321, h4325, h4327, h4331, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT13_Equation419_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation419 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h419⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at13
  obtain ⟨h1, h38, h39, h40, h41, h43, h307, h308, h309, h310, h311, h312, h313, h314, h315, h316, h318, h323, h325, h326, h327, h329, h332, h333, h343, h3253, h3255, h3256, h3258, h3259, h3260, h3261, h3264, h3265, h3267, h3271, h3273, h3274, h3275, h3277, h3278, h3290, h3292, h3300, h3306, h3308, h3309, h3315, h3316, h3319, h3322, h3323, h3326, h3331, h3334, h3342, h3346, h3350, h3353, h3388, h3414, h4268, h4269, h4270, h4271, h4272, h4273, h4274, h4275, h4276, h4277, h4278, h4279, h4280, h4283, h4284, h4286, h4287, h4288, h4290, h4291, h4293, h4296, h4297, h4299, h4300, h4301, h4304, h4305, h4314, h4315, h4318, h4320, h4321, h4325, h4327, h4331, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h411 := Equation419_4512_implies_Equation411 G h419 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT13_Equation429_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation429 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h429⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at13
  obtain ⟨h1, h38, h39, h40, h41, h43, h307, h308, h309, h310, h311, h312, h313, h314, h315, h316, h318, h323, h325, h326, h327, h329, h332, h333, h343, h3253, h3255, h3256, h3258, h3259, h3260, h3261, h3264, h3265, h3267, h3271, h3273, h3274, h3275, h3277, h3278, h3290, h3292, h3300, h3306, h3308, h3309, h3315, h3316, h3319, h3322, h3323, h3326, h3331, h3334, h3342, h3346, h3350, h3353, h3388, h3414, h4268, h4269, h4270, h4271, h4272, h4273, h4274, h4275, h4276, h4277, h4278, h4279, h4280, h4283, h4284, h4286, h4287, h4288, h4290, h4291, h4293, h4296, h4297, h4299, h4300, h4301, h4304, h4305, h4314, h4315, h4318, h4320, h4321, h4325, h4327, h4331, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h411 := Equation429_4512_implies_Equation411 G h429 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT13_Equation440_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation440 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h440⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at13
  obtain ⟨h1, h38, h39, h40, h41, h43, h307, h308, h309, h310, h311, h312, h313, h314, h315, h316, h318, h323, h325, h326, h327, h329, h332, h333, h343, h3253, h3255, h3256, h3258, h3259, h3260, h3261, h3264, h3265, h3267, h3271, h3273, h3274, h3275, h3277, h3278, h3290, h3292, h3300, h3306, h3308, h3309, h3315, h3316, h3319, h3322, h3323, h3326, h3331, h3334, h3342, h3346, h3350, h3353, h3388, h3414, h4268, h4269, h4270, h4271, h4272, h4273, h4274, h4275, h4276, h4277, h4278, h4279, h4280, h4283, h4284, h4286, h4287, h4288, h4290, h4291, h4293, h4296, h4297, h4299, h4300, h4301, h4304, h4305, h4314, h4315, h4318, h4320, h4321, h4325, h4327, h4331, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h411 := Equation440_4512_implies_Equation411 G h440 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT13_Equation477_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation477 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h477⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at13
  obtain ⟨h1, h38, h39, h40, h41, h43, h307, h308, h309, h310, h311, h312, h313, h314, h315, h316, h318, h323, h325, h326, h327, h329, h332, h333, h343, h3253, h3255, h3256, h3258, h3259, h3260, h3261, h3264, h3265, h3267, h3271, h3273, h3274, h3275, h3277, h3278, h3290, h3292, h3300, h3306, h3308, h3309, h3315, h3316, h3319, h3322, h3323, h3326, h3331, h3334, h3342, h3346, h3350, h3353, h3388, h3414, h4268, h4269, h4270, h4271, h4272, h4273, h4274, h4275, h4276, h4277, h4278, h4279, h4280, h4283, h4284, h4286, h4287, h4288, h4290, h4291, h4293, h4296, h4297, h4299, h4300, h4301, h4304, h4305, h4314, h4315, h4318, h4320, h4321, h4325, h4327, h4331, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h411 := Equation477_4512_implies_Equation411 G h477 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT13_Equation504_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation504 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h504⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at13
  obtain ⟨h1, h38, h39, h40, h41, h43, h307, h308, h309, h310, h311, h312, h313, h314, h315, h316, h318, h323, h325, h326, h327, h329, h332, h333, h343, h3253, h3255, h3256, h3258, h3259, h3260, h3261, h3264, h3265, h3267, h3271, h3273, h3274, h3275, h3277, h3278, h3290, h3292, h3300, h3306, h3308, h3309, h3315, h3316, h3319, h3322, h3323, h3326, h3331, h3334, h3342, h3346, h3350, h3353, h3388, h3414, h4268, h4269, h4270, h4271, h4272, h4273, h4274, h4275, h4276, h4277, h4278, h4279, h4280, h4283, h4284, h4286, h4287, h4288, h4290, h4291, h4293, h4296, h4297, h4299, h4300, h4301, h4304, h4305, h4314, h4315, h4318, h4320, h4321, h4325, h4327, h4331, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h411 := Equation504_4512_implies_Equation411 G h504 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT13_Equation513_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation513 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h513⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at13
  obtain ⟨h1, h38, h39, h40, h41, h43, h307, h308, h309, h310, h311, h312, h313, h314, h315, h316, h318, h323, h325, h326, h327, h329, h332, h333, h343, h3253, h3255, h3256, h3258, h3259, h3260, h3261, h3264, h3265, h3267, h3271, h3273, h3274, h3275, h3277, h3278, h3290, h3292, h3300, h3306, h3308, h3309, h3315, h3316, h3319, h3322, h3323, h3326, h3331, h3334, h3342, h3346, h3350, h3353, h3388, h3414, h4268, h4269, h4270, h4271, h4272, h4273, h4274, h4275, h4276, h4277, h4278, h4279, h4280, h4283, h4284, h4286, h4287, h4288, h4290, h4291, h4293, h4296, h4297, h4299, h4300, h4301, h4304, h4305, h4314, h4315, h4318, h4320, h4321, h4325, h4327, h4331, h4343, h4358, h4362, h4364, h4369, h4512⟩ := g hh
  have h411 := Equation513_4512_implies_Equation411 G h513 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT13_Equation3253_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3253 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3253⟩ := h
  exact hh

private theorem AT13_Equation3255_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3255 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3255⟩ := h
  exact hh

private theorem AT13_Equation3256_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3256 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3256⟩ := h
  exact hh

private theorem AT13_Equation3258_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3258 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3258⟩ := h
  exact hh

private theorem AT13_Equation3259_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3259 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3259⟩ := h
  exact hh

private theorem AT13_Equation3260_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3260 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3260⟩ := h
  exact hh

private theorem AT13_Equation3261_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3261 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3261⟩ := h
  exact hh

private theorem AT13_Equation3264_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3264 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3264⟩ := h
  exact hh

private theorem AT13_Equation3265_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3265 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3265⟩ := h
  exact hh

private theorem AT13_Equation3267_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3267 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3267⟩ := h
  exact hh

private theorem AT13_Equation3271_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3271 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3271⟩ := h
  exact hh

private theorem AT13_Equation3273_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3273 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3273⟩ := h
  exact hh

private theorem AT13_Equation3274_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3274 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3274⟩ := h
  exact hh

private theorem AT13_Equation3275_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3275 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3275⟩ := h
  exact hh

private theorem AT13_Equation3277_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3277 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3277⟩ := h
  exact hh

private theorem AT13_Equation3278_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3278 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3278⟩ := h
  exact hh

private theorem AT13_Equation3290_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3290 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3290⟩ := h
  exact hh

private theorem AT13_Equation3292_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3292 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3292⟩ := h
  exact hh

private theorem AT13_Equation3300_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3300 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3300⟩ := h
  exact hh

private theorem AT13_Equation3306_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3306 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3306⟩ := h
  exact hh

private theorem AT13_Equation3308_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3308 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3308⟩ := h
  exact hh

private theorem AT13_Equation3309_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3309 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3309⟩ := h
  exact hh

private theorem AT13_Equation3315_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3315 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3315⟩ := h
  exact hh

private theorem AT13_Equation3316_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3316 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3316⟩ := h
  exact hh

private theorem AT13_Equation3319_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3319 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3319⟩ := h
  exact hh

private theorem AT13_Equation3322_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3322 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3322⟩ := h
  exact hh

private theorem AT13_Equation3323_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3323 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3323⟩ := h
  exact hh

private theorem AT13_Equation3326_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3326 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3326⟩ := h
  exact hh

private theorem AT13_Equation3331_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3331 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3331⟩ := h
  exact hh

private theorem AT13_Equation3334_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3334 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3334⟩ := h
  exact hh

private theorem AT13_Equation3342_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3342 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3342⟩ := h
  exact hh

private theorem AT13_Equation3346_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3346 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3346⟩ := h
  exact hh

private theorem AT13_Equation3350_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3350 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3350⟩ := h
  exact hh

private theorem AT13_Equation3353_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3353 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3353⟩ := h
  exact hh

private theorem AT13_Equation3388_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3388 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3388⟩ := h
  exact hh

private theorem AT13_Equation3414_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation3414 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3414⟩ := h
  exact hh

private theorem AT13_Equation4268_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4268 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4268⟩ := h
  exact hh

private theorem AT13_Equation4269_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4269 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4269⟩ := h
  exact hh

private theorem AT13_Equation4270_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4270 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4270⟩ := h
  exact hh

private theorem AT13_Equation4271_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4271 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4271⟩ := h
  exact hh

private theorem AT13_Equation4272_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4272 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4272⟩ := h
  exact hh

private theorem AT13_Equation4273_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4273 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4273⟩ := h
  exact hh

private theorem AT13_Equation4274_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4274 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4274⟩ := h
  exact hh

private theorem AT13_Equation4275_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4275 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4275⟩ := h
  exact hh

private theorem AT13_Equation4276_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4276 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4276⟩ := h
  exact hh

private theorem AT13_Equation4277_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4277 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4277⟩ := h
  exact hh

private theorem AT13_Equation4278_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4278 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4278⟩ := h
  exact hh

private theorem AT13_Equation4279_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4279 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4279⟩ := h
  exact hh

private theorem AT13_Equation4280_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4280 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4280⟩ := h
  exact hh

private theorem AT13_Equation4283_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4283 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4283⟩ := h
  exact hh

private theorem AT13_Equation4284_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4284 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4284⟩ := h
  exact hh

private theorem AT13_Equation4286_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4286 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4286⟩ := h
  exact hh

private theorem AT13_Equation4287_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4287 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4287⟩ := h
  exact hh

private theorem AT13_Equation4288_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4288 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4288⟩ := h
  exact hh

private theorem AT13_Equation4290_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4290 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4290⟩ := h
  exact hh

private theorem AT13_Equation4291_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4291 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4291⟩ := h
  exact hh

private theorem AT13_Equation4293_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4293 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4293⟩ := h
  exact hh

private theorem AT13_Equation4296_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4296 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4296⟩ := h
  exact hh

private theorem AT13_Equation4297_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4297 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4297⟩ := h
  exact hh

private theorem AT13_Equation4299_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4299 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4299⟩ := h
  exact hh

private theorem AT13_Equation4300_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4300 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4300⟩ := h
  exact hh

private theorem AT13_Equation4301_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4301 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4301⟩ := h
  exact hh

private theorem AT13_Equation4304_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4304 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4304⟩ := h
  exact hh

private theorem AT13_Equation4305_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4305 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4305⟩ := h
  exact hh

private theorem AT13_Equation4314_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4314 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4314⟩ := h
  exact hh

private theorem AT13_Equation4315_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4315 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4315⟩ := h
  exact hh

private theorem AT13_Equation4318_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4318 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4318⟩ := h
  exact hh

private theorem AT13_Equation4320_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4320 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4320⟩ := h
  exact hh

private theorem AT13_Equation4321_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4321 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4321⟩ := h
  exact hh

private theorem AT13_Equation4325_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4325 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4325⟩ := h
  exact hh

private theorem AT13_Equation4327_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4327 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4327⟩ := h
  exact hh

private theorem AT13_Equation4331_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4331 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4331⟩ := h
  exact hh

private theorem AT13_Equation4343_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4343 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4343⟩ := h
  exact hh

private theorem AT13_Equation4358_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4358 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4358⟩ := h
  exact hh

private theorem AT13_Equation4362_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4362 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4362⟩ := h
  exact hh

private theorem AT13_Equation4364_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4364 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4364⟩ := h
  exact hh

private theorem AT13_Equation4369_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4369 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4369⟩ := h
  exact hh

private theorem AT13_Equation4512_implies (G : Type*) [Magma G] (h : (AssociativeTheory13 G) ∧ (Equation4512 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4512⟩ := h
  exact hh

theorem AT13_conj_implied (G: Type*) [Magma G] (eqid : EQIndex) (h : ATearly G (conj13 eqid)) : (AssociativeTheory13 G) ∧ (EQeq G eqid) := by
have hh := (AT_equiv G (conj13 eqid)).mp h
rcases eqid
all_goals
  obtain ⟨_, _⟩ := hh
  tauto

theorem AT13_conj (G: Type*) [Magma G] (eqid : EQIndex) : (AssociativeTheory13 G) ∧ (EQeq G eqid) <-> (ATearly G (conj13 eqid)) :=
⟨match eqid with
| eq1 => AT13_Equation1_implies G
| eq2 => AT13_Equation2_implies G
| eq3 => AT13_Equation3_implies G
| eq4 => AT13_Equation4_implies G
| eq5 => AT13_Equation5_implies G
| eq8 => AT13_Equation8_implies G
| eq10 => AT13_Equation10_implies G
| eq11 => AT13_Equation11_implies G
| eq14 => AT13_Equation14_implies G
| eq16 => AT13_Equation16_implies G
| eq38 => AT13_Equation38_implies G
| eq39 => AT13_Equation39_implies G
| eq40 => AT13_Equation40_implies G
| eq41 => AT13_Equation41_implies G
| eq43 => AT13_Equation43_implies G
| eq47 => AT13_Equation47_implies G
| eq56 => AT13_Equation56_implies G
| eq66 => AT13_Equation66_implies G
| eq75 => AT13_Equation75_implies G
| eq307 => AT13_Equation307_implies G
| eq308 => AT13_Equation308_implies G
| eq309 => AT13_Equation309_implies G
| eq310 => AT13_Equation310_implies G
| eq311 => AT13_Equation311_implies G
| eq312 => AT13_Equation312_implies G
| eq313 => AT13_Equation313_implies G
| eq314 => AT13_Equation314_implies G
| eq315 => AT13_Equation315_implies G
| eq316 => AT13_Equation316_implies G
| eq318 => AT13_Equation318_implies G
| eq323 => AT13_Equation323_implies G
| eq325 => AT13_Equation325_implies G
| eq326 => AT13_Equation326_implies G
| eq327 => AT13_Equation327_implies G
| eq329 => AT13_Equation329_implies G
| eq332 => AT13_Equation332_implies G
| eq333 => AT13_Equation333_implies G
| eq343 => AT13_Equation343_implies G
| eq411 => AT13_Equation411_implies G
| eq419 => AT13_Equation419_implies G
| eq429 => AT13_Equation429_implies G
| eq440 => AT13_Equation440_implies G
| eq477 => AT13_Equation477_implies G
| eq504 => AT13_Equation504_implies G
| eq513 => AT13_Equation513_implies G
| eq3253 => AT13_Equation3253_implies G
| eq3255 => AT13_Equation3255_implies G
| eq3256 => AT13_Equation3256_implies G
| eq3258 => AT13_Equation3258_implies G
| eq3259 => AT13_Equation3259_implies G
| eq3260 => AT13_Equation3260_implies G
| eq3261 => AT13_Equation3261_implies G
| eq3264 => AT13_Equation3264_implies G
| eq3265 => AT13_Equation3265_implies G
| eq3267 => AT13_Equation3267_implies G
| eq3271 => AT13_Equation3271_implies G
| eq3273 => AT13_Equation3273_implies G
| eq3274 => AT13_Equation3274_implies G
| eq3275 => AT13_Equation3275_implies G
| eq3277 => AT13_Equation3277_implies G
| eq3278 => AT13_Equation3278_implies G
| eq3290 => AT13_Equation3290_implies G
| eq3292 => AT13_Equation3292_implies G
| eq3300 => AT13_Equation3300_implies G
| eq3306 => AT13_Equation3306_implies G
| eq3308 => AT13_Equation3308_implies G
| eq3309 => AT13_Equation3309_implies G
| eq3315 => AT13_Equation3315_implies G
| eq3316 => AT13_Equation3316_implies G
| eq3319 => AT13_Equation3319_implies G
| eq3322 => AT13_Equation3322_implies G
| eq3323 => AT13_Equation3323_implies G
| eq3326 => AT13_Equation3326_implies G
| eq3331 => AT13_Equation3331_implies G
| eq3334 => AT13_Equation3334_implies G
| eq3342 => AT13_Equation3342_implies G
| eq3346 => AT13_Equation3346_implies G
| eq3350 => AT13_Equation3350_implies G
| eq3353 => AT13_Equation3353_implies G
| eq3388 => AT13_Equation3388_implies G
| eq3414 => AT13_Equation3414_implies G
| eq4268 => AT13_Equation4268_implies G
| eq4269 => AT13_Equation4269_implies G
| eq4270 => AT13_Equation4270_implies G
| eq4271 => AT13_Equation4271_implies G
| eq4272 => AT13_Equation4272_implies G
| eq4273 => AT13_Equation4273_implies G
| eq4274 => AT13_Equation4274_implies G
| eq4275 => AT13_Equation4275_implies G
| eq4276 => AT13_Equation4276_implies G
| eq4277 => AT13_Equation4277_implies G
| eq4278 => AT13_Equation4278_implies G
| eq4279 => AT13_Equation4279_implies G
| eq4280 => AT13_Equation4280_implies G
| eq4283 => AT13_Equation4283_implies G
| eq4284 => AT13_Equation4284_implies G
| eq4286 => AT13_Equation4286_implies G
| eq4287 => AT13_Equation4287_implies G
| eq4288 => AT13_Equation4288_implies G
| eq4290 => AT13_Equation4290_implies G
| eq4291 => AT13_Equation4291_implies G
| eq4293 => AT13_Equation4293_implies G
| eq4296 => AT13_Equation4296_implies G
| eq4297 => AT13_Equation4297_implies G
| eq4299 => AT13_Equation4299_implies G
| eq4300 => AT13_Equation4300_implies G
| eq4301 => AT13_Equation4301_implies G
| eq4304 => AT13_Equation4304_implies G
| eq4305 => AT13_Equation4305_implies G
| eq4314 => AT13_Equation4314_implies G
| eq4315 => AT13_Equation4315_implies G
| eq4318 => AT13_Equation4318_implies G
| eq4320 => AT13_Equation4320_implies G
| eq4321 => AT13_Equation4321_implies G
| eq4325 => AT13_Equation4325_implies G
| eq4327 => AT13_Equation4327_implies G
| eq4331 => AT13_Equation4331_implies G
| eq4343 => AT13_Equation4343_implies G
| eq4358 => AT13_Equation4358_implies G
| eq4362 => AT13_Equation4362_implies G
| eq4364 => AT13_Equation4364_implies G
| eq4369 => AT13_Equation4369_implies G
| eq4512 => AT13_Equation4512_implies G
, AT13_conj_implied G eqid⟩

