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


def conj44 : EQIndex → ATIndex
| eq1 => at44
| eq2 => at2
| eq3 => at5
| eq4 => at2
| eq5 => at5
| eq8 => at5
| eq10 => at5
| eq11 => at2
| eq14 => at2
| eq16 => at5
| eq38 => at13
| eq39 => at12
| eq40 => at13
| eq41 => at13
| eq43 => at13
| eq47 => at5
| eq56 => at2
| eq66 => at2
| eq75 => at5
| eq307 => at44
| eq308 => at13
| eq309 => at12
| eq310 => at13
| eq311 => at13
| eq312 => at44
| eq313 => at13
| eq314 => at13
| eq315 => at12
| eq316 => at13
| eq318 => at12
| eq323 => at44
| eq325 => at13
| eq326 => at12
| eq327 => at13
| eq329 => at12
| eq332 => at13
| eq333 => at44
| eq343 => at44
| eq411 => at5
| eq419 => at5
| eq429 => at5
| eq440 => at2
| eq477 => at2
| eq504 => at2
| eq513 => at5
| eq3253 => at44
| eq3255 => at12
| eq3256 => at13
| eq3258 => at44
| eq3259 => at13
| eq3260 => at13
| eq3261 => at12
| eq3264 => at12
| eq3265 => at13
| eq3267 => at13
| eq3271 => at12
| eq3273 => at13
| eq3274 => at12
| eq3275 => at13
| eq3277 => at13
| eq3278 => at44
| eq3290 => at13
| eq3292 => at12
| eq3300 => at12
| eq3306 => at44
| eq3308 => at13
| eq3309 => at12
| eq3315 => at13
| eq3316 => at44
| eq3319 => at12
| eq3322 => at12
| eq3323 => at13
| eq3326 => at44
| eq3331 => at13
| eq3334 => at12
| eq3342 => at13
| eq3346 => at12
| eq3350 => at13
| eq3353 => at44
| eq3388 => at12
| eq3414 => at44
| eq4268 => at13
| eq4269 => at12
| eq4270 => at13
| eq4271 => at13
| eq4272 => at44
| eq4273 => at13
| eq4274 => at13
| eq4275 => at12
| eq4276 => at13
| eq4277 => at13
| eq4278 => at12
| eq4279 => at13
| eq4280 => at13
| eq4283 => at13
| eq4284 => at12
| eq4286 => at13
| eq4287 => at12
| eq4288 => at13
| eq4290 => at13
| eq4291 => at44
| eq4293 => at13
| eq4296 => at12
| eq4297 => at13
| eq4299 => at13
| eq4300 => at44
| eq4301 => at13
| eq4304 => at12
| eq4305 => at13
| eq4314 => at13
| eq4315 => at13
| eq4318 => at13
| eq4320 => at12
| eq4321 => at13
| eq4325 => at13
| eq4327 => at12
| eq4331 => at13
| eq4343 => at13
| eq4358 => at13
| eq4362 => at12
| eq4364 => at13
| eq4369 => at13
| eq4512 => at44


private theorem AT44_Equation1_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation1 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h1⟩ := h
  exact hh

private theorem AT44_Equation2_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation2 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h2⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  exact ⟨h2, h4512⟩

private theorem AT44_Equation3_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h3⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h3319 := Equation3_4512_implies_Equation3319 G h3 h4512
  have h3261 := Equation3278_3319_4512_implies_Equation3261 G h3278 h3319 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT44_Equation4_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h47 := Equation4_4512_implies_Equation47 G h4 h4512
  have h4268 := Equation4_4512_implies_Equation4268 G h4 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT44_Equation5_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation5 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h5⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  exact ⟨h5, h4512⟩

private theorem AT44_Equation8_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation8 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h8⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h411 := Equation8_4512_implies_Equation411 G h8 h4512
  have h3319 := Equation8_4512_implies_Equation3319 G h8 h4512
  have h3261 := Equation3278_3319_4512_implies_Equation3261 G h3278 h3319 h4512
  have h3 := Equation411_4291_4512_implies_Equation3 G h411 h4291 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT44_Equation10_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation10 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h10⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT44_Equation11_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation11 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h11⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  have h411 := Equation11_4512_implies_Equation411 G h11 h4512
  have h3 := Equation411_4272_4512_implies_Equation3 G h411 h4272 h4512
  have h4273 := Equation14_4512_implies_Equation4273 G h14 h4512
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT44_Equation14_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation14 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h14⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h411 := Equation14_4512_implies_Equation411 G h14 h4512
  have h4273 := Equation14_4512_implies_Equation4273 G h14 h4512
  have h3 := Equation411_4272_4512_implies_Equation3 G h411 h4272 h4512
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT44_Equation16_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation16 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h16⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h411 := Equation16_4512_implies_Equation411 G h16 h4512
  have h429 := Equation16_4512_implies_Equation429 G h16 h4512
  have h3 := Equation411_4272_4512_implies_Equation3 G h411 h4272 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT44_Equation38_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation38 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h38⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4284 := Equation38_4512_implies_Equation4284 G h38 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation39_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation39 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h39⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  exact ⟨h39, h4512⟩

private theorem AT44_Equation40_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation40 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h40⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h3350 := Equation40_3306_4512_implies_Equation3350 G h40 h3306 h4512
  have h316 := Equation40_307_4512_implies_Equation316 G h40 h307 h4512
  have h3315 := Equation3350_4512_implies_Equation3315 G h3350 h4512
  have h315 := Equation316_4512_implies_Equation315 G h316 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation41_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation41 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h41⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h38 := Equation41_4512_implies_Equation38 G h41 h4512
  have h39 := Equation41_4512_implies_Equation39 G h41 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation43_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation43 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h43⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h332 := Equation43_323_4512_implies_Equation332 G h43 h323 h4512
  have h4320 := Equation43_4512_implies_Equation4320 G h43 h4512
  have h4284 := Equation4291_4320_4512_implies_Equation4284 G h4291 h4320 h4512
  have h325 := Equation332_4512_implies_Equation325 G h332 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation47_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation47 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h47⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h3 := Equation47_4291_4512_implies_Equation3 G h47 h4291 h4512
  have h8 := Equation3_4512_implies_Equation8 G h3 h4512
  have h3319 := Equation3_4512_implies_Equation3319 G h3 h4512
  have h3261 := Equation3278_3319_4512_implies_Equation3261 G h3278 h3319 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT44_Equation56_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation56 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h56⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h47 := Equation56_4512_implies_Equation47 G h56 h4512
  have h3 := Equation47_4291_4512_implies_Equation3 G h47 h4291 h4512
  have h4 := Equation3_56_4512_implies_Equation4 G h3 h56 h4512
  have h4268 := Equation4_4512_implies_Equation4268 G h4 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT44_Equation66_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation66 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h66⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h47 := Equation66_4512_implies_Equation47 G h66 h4512
  have h4290 := Equation66_4512_implies_Equation4290 G h66 h4512
  have h4268 := Equation4272_4290_4512_implies_Equation4268 G h4272 h4290 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT44_Equation75_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation75 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h75⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h47 := Equation75_4512_implies_Equation47 G h75 h4512
  have h3 := Equation47_4291_4512_implies_Equation3 G h47 h4291 h4512
  have h5 := Equation3_75_4512_implies_Equation5 G h3 h75 h4512
  exact ⟨h5, h4512⟩

private theorem AT44_Equation307_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation307 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h307⟩ := h
  exact hh

private theorem AT44_Equation308_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation308 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h308⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h3255 := Equation308_4512_implies_Equation3255 G h308 h4512
  have h3256 := Equation308_4512_implies_Equation3256 G h308 h4512
  have h3331 := Equation3256_3306_4512_implies_Equation3331 G h3256 h3306 h4512
  have h3261 := Equation3255_3258_4512_implies_Equation3261 G h3255 h3258 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h3315 := Equation3331_4512_implies_Equation3315 G h3331 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation309_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation309 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h309⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4284 := Equation309_4512_implies_Equation4284 G h309 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation310_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation310 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h310⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h3256 := Equation310_4512_implies_Equation3256 G h310 h4512
  have h4284 := Equation310_4512_implies_Equation4284 G h310 h4512
  have h3331 := Equation3256_3306_4512_implies_Equation3331 G h3256 h3306 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h3315 := Equation3331_4512_implies_Equation3315 G h3331 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation311_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation311 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h311⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4284 := Equation311_4512_implies_Equation4284 G h311 h4512
  have h4314 := Equation311_4512_implies_Equation4314 G h311 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation312_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation312 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h312⟩ := h
  exact hh

private theorem AT44_Equation313_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation313 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h313⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h315 := Equation313_4512_implies_Equation315 G h313 h4512
  have h4314 := Equation313_4512_implies_Equation4314 G h313 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation314_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation314 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h314⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h315 := Equation314_4512_implies_Equation315 G h314 h4512
  have h4314 := Equation314_4512_implies_Equation4314 G h314 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation315_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation315 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation316_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation316 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h316⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h315 := Equation316_4512_implies_Equation315 G h316 h4512
  have h3255 := Equation316_4512_implies_Equation3255 G h316 h4512
  have h4284 := Equation316_4512_implies_Equation4284 G h316 h4512
  have h4290 := Equation316_4512_implies_Equation4290 G h316 h4512
  have h4283 := Equation307_4290_4291_4512_implies_Equation4283 G h307 h4290 h4291 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h326 := Equation3255_3316_4512_implies_Equation326 G h3255 h3316 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation318_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation318 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h318⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h315 := Equation318_4512_implies_Equation315 G h318 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation323_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation323 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h323⟩ := h
  exact hh

private theorem AT44_Equation325_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation325 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h325⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h4284 := Equation38_4512_implies_Equation4284 G h38 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation326_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation326 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h326⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h3309 := Equation323_326_4512_implies_Equation3309 G h323 h326 h4512
  have h4284 := Equation3309_4512_implies_Equation4284 G h3309 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation327_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation327 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h327⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h325 := Equation327_4512_implies_Equation325 G h327 h4512
  have h3319 := Equation327_4512_implies_Equation3319 G h327 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h3261 := Equation3278_3319_4512_implies_Equation3261 G h3278 h3319 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation329_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation329 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h329⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4284 := Equation329_4512_implies_Equation4284 G h329 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation332_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation332 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h332⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h325 := Equation332_4512_implies_Equation325 G h332 h4512
  have h4284 := Equation332_4512_implies_Equation4284 G h332 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation333_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation333 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h333⟩ := h
  exact hh

private theorem AT44_Equation343_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation343 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h343⟩ := h
  exact hh

private theorem AT44_Equation411_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation411 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h411⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h3 := Equation411_4291_4512_implies_Equation3 G h411 h4291 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h3319 := Equation3_4512_implies_Equation3319 G h3 h4512
  have h3261 := Equation3278_3319_4512_implies_Equation3261 G h3278 h3319 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT44_Equation419_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation419 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h419⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h411 := Equation419_4512_implies_Equation411 G h419 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h3 := Equation411_4291_4512_implies_Equation3 G h411 h4291 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT44_Equation429_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation429 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h429⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h411 := Equation429_4512_implies_Equation411 G h429 h4512
  have h3 := Equation411_4291_4512_implies_Equation3 G h411 h4291 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT44_Equation440_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation440 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h440⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h411 := Equation440_4512_implies_Equation411 G h440 h4512
  have h3 := Equation411_4291_4512_implies_Equation3 G h411 h4291 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h4284 := Equation3_4512_implies_Equation4284 G h3 h4512
  have h4320 := Equation4284_4291_4512_implies_Equation4320 G h4284 h4291 h4512
  have h4270 := Equation11_4512_implies_Equation4270 G h11 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT44_Equation477_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation477 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h477⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h411 := Equation477_4512_implies_Equation411 G h477 h4512
  have h4290 := Equation477_4512_implies_Equation4290 G h477 h4512
  have h3 := Equation411_4291_4512_implies_Equation3 G h411 h4291 h4512
  have h4268 := Equation4272_4290_4512_implies_Equation4268 G h4272 h4290 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT44_Equation504_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation504 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h504⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h411 := Equation504_4512_implies_Equation411 G h504 h4512
  have h4290 := Equation504_4512_implies_Equation4290 G h504 h4512
  have h3 := Equation411_4291_4512_implies_Equation3 G h411 h4291 h4512
  have h4268 := Equation4272_4290_4512_implies_Equation4268 G h4272 h4290 h4512
  have h4273 := Equation4268_4291_4512_implies_Equation4273 G h4268 h4291 h4512
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT44_Equation513_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation513 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h513⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h411 := Equation513_4512_implies_Equation411 G h513 h4512
  have h3 := Equation411_4291_4512_implies_Equation3 G h411 h4291 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h16 := Equation8_513_4512_implies_Equation16 G h8 h513 h4512
  have h429 := Equation16_4512_implies_Equation429 G h16 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT44_Equation3253_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3253 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h3253⟩ := h
  exact hh

private theorem AT44_Equation3255_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3255 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h3255⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h3261 := Equation3255_3258_4512_implies_Equation3261 G h3255 h3258 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation3256_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3256 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3256⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h40 := Equation3256_3278_4512_implies_Equation40 G h3256 h3278 h4512
  have h3331 := Equation3256_3306_4512_implies_Equation3331 G h3256 h3306 h4512
  have h316 := Equation40_307_4512_implies_Equation316 G h40 h307 h4512
  have h3315 := Equation3331_4512_implies_Equation3315 G h3331 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h315 := Equation316_4512_implies_Equation315 G h316 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation3258_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3258 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h3258⟩ := h
  exact hh

private theorem AT44_Equation3259_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3259 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3259⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h3256 := Equation3259_4512_implies_Equation3256 G h3259 h4512
  have h3261 := Equation3259_4512_implies_Equation3261 G h3259 h4512
  have h3331 := Equation3256_3306_4512_implies_Equation3331 G h3256 h3306 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h3315 := Equation3331_4512_implies_Equation3315 G h3331 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation3260_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3260 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3260⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h3256 := Equation3260_4512_implies_Equation3256 G h3260 h4512
  have h4284 := Equation3260_4512_implies_Equation4284 G h3260 h4512
  have h3331 := Equation3256_3306_4512_implies_Equation3331 G h3256 h3306 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h3315 := Equation3331_4512_implies_Equation3315 G h3331 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation3261_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3261 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h3261⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation3264_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3264 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h3264⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4284 := Equation3264_4512_implies_Equation4284 G h3264 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation3265_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3265 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3265⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h3256 := Equation3265_4512_implies_Equation3256 G h3265 h4512
  have h4284 := Equation3265_4512_implies_Equation4284 G h3265 h4512
  have h3331 := Equation3256_3306_4512_implies_Equation3331 G h3256 h3306 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h3315 := Equation3331_4512_implies_Equation3315 G h3331 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation3267_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3267 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3267⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h3256 := Equation3267_4512_implies_Equation3256 G h3267 h4512
  have h4284 := Equation3267_4512_implies_Equation4284 G h3267 h4512
  have h3331 := Equation3256_3306_4512_implies_Equation3331 G h3256 h3306 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h3315 := Equation3331_4512_implies_Equation3315 G h3331 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation3271_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3271 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h3271⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h3261 := Equation3271_4512_implies_Equation3261 G h3271 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation3273_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3273 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3273⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h315 := Equation3273_4512_implies_Equation315 G h3273 h4512
  have h3255 := Equation3273_4512_implies_Equation3255 G h3273 h4512
  have h4284 := Equation3273_4512_implies_Equation4284 G h3273 h4512
  have h4290 := Equation3273_4512_implies_Equation4290 G h3273 h4512
  have h4283 := Equation307_4290_4291_4512_implies_Equation4283 G h307 h4290 h4291 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h326 := Equation3255_3316_4512_implies_Equation326 G h3255 h3316 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation3274_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3274 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h3274⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h315 := Equation3274_4512_implies_Equation315 G h3274 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation3275_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3275 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3275⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h315 := Equation3275_4512_implies_Equation315 G h3275 h4512
  have h3255 := Equation3275_4512_implies_Equation3255 G h3275 h4512
  have h4284 := Equation3275_4512_implies_Equation4284 G h3275 h4512
  have h4290 := Equation3275_4512_implies_Equation4290 G h3275 h4512
  have h4283 := Equation307_4290_4291_4512_implies_Equation4283 G h307 h4290 h4291 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h326 := Equation3255_3316_4512_implies_Equation326 G h3255 h3316 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation3277_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3277 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3277⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h315 := Equation3277_4512_implies_Equation315 G h3277 h4512
  have h3255 := Equation3277_4512_implies_Equation3255 G h3277 h4512
  have h4284 := Equation3277_4512_implies_Equation4284 G h3277 h4512
  have h4290 := Equation3277_4512_implies_Equation4290 G h3277 h4512
  have h4283 := Equation307_4290_4291_4512_implies_Equation4283 G h307 h4290 h4291 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h326 := Equation3255_3316_4512_implies_Equation326 G h3255 h3316 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation3278_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3278 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h3278⟩ := h
  exact hh

private theorem AT44_Equation3290_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3290 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3290⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h315 := Equation3290_4512_implies_Equation315 G h3290 h4512
  have h3255 := Equation3290_4512_implies_Equation3255 G h3290 h4512
  have h4284 := Equation3290_4512_implies_Equation4284 G h3290 h4512
  have h4290 := Equation3290_4512_implies_Equation4290 G h3290 h4512
  have h4283 := Equation307_4290_4291_4512_implies_Equation4283 G h307 h4290 h4291 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h326 := Equation3255_3316_4512_implies_Equation326 G h3255 h3316 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation3292_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3292 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h3292⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h315 := Equation3292_4512_implies_Equation315 G h3292 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation3300_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3300 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h3300⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h315 := Equation3300_4512_implies_Equation315 G h3300 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation3306_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3306 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h3306⟩ := h
  exact hh

private theorem AT44_Equation3308_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3308 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3308⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h3315 := Equation3308_4512_implies_Equation3315 G h3308 h4512
  have h3319 := Equation3308_4512_implies_Equation3319 G h3308 h4512
  have h3261 := Equation3278_3319_4512_implies_Equation3261 G h3278 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation3309_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3309 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h3309⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4284 := Equation3309_4512_implies_Equation4284 G h3309 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation3315_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3315 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h3319 := Equation3315_4512_implies_Equation3319 G h3315 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h3261 := Equation3278_3319_4512_implies_Equation3261 G h3278 h3319 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation3316_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3316 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h3316⟩ := h
  exact hh

private theorem AT44_Equation3319_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3319 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h3319⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h3261 := Equation3278_3319_4512_implies_Equation3261 G h3278 h3319 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation3322_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3322 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h3322⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h3319 := Equation3322_4512_implies_Equation3319 G h3322 h4512
  have h3261 := Equation3278_3319_4512_implies_Equation3261 G h3278 h3319 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation3323_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3323 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3323⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h3315 := Equation3323_4512_implies_Equation3315 G h3323 h4512
  have h3319 := Equation3323_4512_implies_Equation3319 G h3323 h4512
  have h3261 := Equation3278_3319_4512_implies_Equation3261 G h3278 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation3326_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3326 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h3326⟩ := h
  exact hh

private theorem AT44_Equation3331_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3331 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3331⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h3261 := Equation3331_4512_implies_Equation3261 G h3331 h4512
  have h3315 := Equation3331_4512_implies_Equation3315 G h3331 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation3334_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3334 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h3334⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h3261 := Equation3334_4512_implies_Equation3261 G h3334 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation3342_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3342 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3342⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h3315 := Equation3342_4512_implies_Equation3315 G h3342 h4512
  have h4320 := Equation3342_4512_implies_Equation4320 G h3342 h4512
  have h4284 := Equation4291_4320_4512_implies_Equation4284 G h4291 h4320 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation3346_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3346 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h3346⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4320 := Equation3346_4512_implies_Equation4320 G h3346 h4512
  have h4284 := Equation4291_4320_4512_implies_Equation4284 G h4291 h4320 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation3350_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3350 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3350⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h3261 := Equation3350_4512_implies_Equation3261 G h3350 h4512
  have h3315 := Equation3350_4512_implies_Equation3315 G h3350 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation3353_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3353 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h3353⟩ := h
  exact hh

private theorem AT44_Equation3388_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3388 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h3388⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4320 := Equation3388_4512_implies_Equation4320 G h3388 h4512
  have h4284 := Equation4291_4320_4512_implies_Equation4284 G h4291 h4320 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation3414_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation3414 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h3414⟩ := h
  exact hh

private theorem AT44_Equation4268_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4268 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4268⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4299 := Equation4268_4272_4512_implies_Equation4299 G h4268 h4272 h4512
  have h308 := Equation307_4268_4512_implies_Equation308 G h307 h4268 h4512
  have h4284 := Equation4299_4512_implies_Equation4284 G h4299 h4512
  have h4290 := Equation4299_4512_implies_Equation4290 G h4299 h4512
  have h3255 := Equation308_4512_implies_Equation3255 G h308 h4512
  have h4283 := Equation307_4290_4291_4512_implies_Equation4283 G h307 h4290 h4291 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h326 := Equation3255_3316_4512_implies_Equation326 G h3255 h3316 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4269_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4269 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h4269⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4278 := Equation4269_4300_4512_implies_Equation4278 G h4269 h4300 h4512
  have h4284 := Equation4278_4512_implies_Equation4284 G h4278 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation4270_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4270 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4270⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h3259 := Equation3253_4270_4512_implies_Equation3259 G h3253 h4270 h4512
  have h3256 := Equation3259_4512_implies_Equation3256 G h3259 h4512
  have h3261 := Equation3259_4512_implies_Equation3261 G h3259 h4512
  have h3331 := Equation3256_3306_4512_implies_Equation3331 G h3256 h3306 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h3315 := Equation3331_4512_implies_Equation3315 G h3331 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4271_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4271 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4271⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4284 := Equation4271_4512_implies_Equation4284 G h4271 h4512
  have h4314 := Equation4271_4512_implies_Equation4314 G h4271 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4272_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4272 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h4272⟩ := h
  exact hh

private theorem AT44_Equation4273_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4273 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4273⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  have h3350 := Equation40_3306_4512_implies_Equation3350 G h40 h3306 h4512
  have h316 := Equation40_307_4512_implies_Equation316 G h40 h307 h4512
  have h3315 := Equation3350_4512_implies_Equation3315 G h3350 h4512
  have h315 := Equation316_4512_implies_Equation315 G h316 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4274_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4274 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4274⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4284 := Equation4274_4512_implies_Equation4284 G h4274 h4512
  have h4314 := Equation4274_4512_implies_Equation4314 G h4274 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4275_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4275 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h4275⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4304 := Equation4272_4275_4512_implies_Equation4304 G h4272 h4275 h4512
  have h4284 := Equation4304_4512_implies_Equation4284 G h4304 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation4276_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4276 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4276⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h40 := Equation3253_4276_4512_implies_Equation40 G h3253 h4276 h4512
  have h3350 := Equation40_3306_4512_implies_Equation3350 G h40 h3306 h4512
  have h316 := Equation40_307_4512_implies_Equation316 G h40 h307 h4512
  have h3315 := Equation3350_4512_implies_Equation3315 G h3350 h4512
  have h315 := Equation316_4512_implies_Equation315 G h316 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4277_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4277 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4277⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4268 := Equation4277_4512_implies_Equation4268 G h4277 h4512
  have h4293 := Equation4277_4512_implies_Equation4293 G h4277 h4512
  have h43 := Equation323_4293_4512_implies_Equation43 G h323 h4293 h4512
  have h4299 := Equation4268_4272_4512_implies_Equation4299 G h4268 h4272 h4512
  have h332 := Equation43_323_4512_implies_Equation332 G h43 h323 h4512
  have h4284 := Equation4299_4512_implies_Equation4284 G h4299 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h325 := Equation332_4512_implies_Equation325 G h332 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4278_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4278 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h4278⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4284 := Equation4278_4512_implies_Equation4284 G h4278 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation4279_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4279 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4279⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4269 := Equation4279_4512_implies_Equation4269 G h4279 h4512
  have h4321 := Equation4279_4512_implies_Equation4321 G h4279 h4512
  have h4278 := Equation4269_4300_4512_implies_Equation4278 G h4269 h4300 h4512
  have h43 := Equation3316_4321_4512_implies_Equation43 G h3316 h4321 h4512
  have h332 := Equation43_323_4512_implies_Equation332 G h43 h323 h4512
  have h4284 := Equation4278_4512_implies_Equation4284 G h4278 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h325 := Equation332_4512_implies_Equation325 G h332 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4280_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4280 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4280⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4343 := Equation4280_4512_implies_Equation4343 G h4280 h4512
  have h4283 := Equation307_4291_4343_4512_implies_Equation4283 G h307 h4291 h4343 h4512
  have h3308 := Equation3306_4283_4512_implies_Equation3308 G h3306 h4283 h4512
  have h4284 := Equation307_4283_4343_4512_implies_Equation4284 G h307 h4283 h4343 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h3315 := Equation3308_4512_implies_Equation3315 G h3308 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4283_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4283 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4283⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h40 := Equation3278_4283_4512_implies_Equation40 G h3278 h4283 h4512
  have h3308 := Equation3306_4283_4512_implies_Equation3308 G h3306 h4283 h4512
  have h4321 := Equation4283_4291_4512_implies_Equation4321 G h4283 h4291 h4512
  have h4290 := Equation40_4512_implies_Equation4290 G h40 h4512
  have h3315 := Equation3308_4512_implies_Equation3315 G h3308 h4512
  have h4284 := Equation307_4290_4321_4512_implies_Equation4284 G h307 h4290 h4321 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4284_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4284 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h4284⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation4286_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4286 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4286⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4269 := Equation4286_4512_implies_Equation4269 G h4286 h4512
  have h4283 := Equation4286_4512_implies_Equation4283 G h4286 h4512
  have h3308 := Equation3306_4283_4512_implies_Equation3308 G h3306 h4283 h4512
  have h4278 := Equation4269_4300_4512_implies_Equation4278 G h4269 h4300 h4512
  have h4284 := Equation4278_4512_implies_Equation4284 G h4278 h4512
  have h3315 := Equation3308_4512_implies_Equation3315 G h3308 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4287_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4287 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h4287⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4284 := Equation4287_4512_implies_Equation4284 G h4287 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation4288_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4288 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4288⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4268 := Equation4288_4512_implies_Equation4268 G h4288 h4512
  have h4284 := Equation4288_4512_implies_Equation4284 G h4288 h4512
  have h308 := Equation307_4268_4512_implies_Equation308 G h307 h4268 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h4320 := Equation4284_4291_4512_implies_Equation4320 G h4284 h4291 h4512
  have h3319 := Equation3353_4320_4512_implies_Equation3319 G h3353 h4320 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h3256 := Equation308_4512_implies_Equation3256 G h308 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4290_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4290 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4290⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4314 := Equation4290_4291_4512_implies_Equation4314 G h4290 h4291 h4512
  have h4283 := Equation307_4290_4291_4512_implies_Equation4283 G h307 h4290 h4291 h4512
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  have h4284 := Equation4283_4314_4512_implies_Equation4284 G h4283 h4314 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4291_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4291 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h4291⟩ := h
  exact hh

private theorem AT44_Equation4293_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4293 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4293⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h43 := Equation323_4293_4512_implies_Equation43 G h323 h4293 h4512
  have h4283 := Equation4291_4293_4512_implies_Equation4283 G h4291 h4293 h4512
  have h40 := Equation3258_4293_4512_implies_Equation40 G h3258 h4293 h4512
  have h332 := Equation43_323_4512_implies_Equation332 G h43 h323 h4512
  have h4321 := Equation4283_4291_4512_implies_Equation4321 G h4283 h4291 h4512
  have h4290 := Equation40_4512_implies_Equation4290 G h40 h4512
  have h4284 := Equation307_4290_4321_4512_implies_Equation4284 G h307 h4290 h4321 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h325 := Equation332_4512_implies_Equation325 G h332 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4296_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4296 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h4296⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4275 := Equation4296_4512_implies_Equation4275 G h4296 h4512
  have h4304 := Equation4272_4275_4512_implies_Equation4304 G h4272 h4275 h4512
  have h4284 := Equation4304_4512_implies_Equation4284 G h4304 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation4297_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4297 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4297⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4290 := Equation4297_4512_implies_Equation4290 G h4297 h4512
  have h4283 := Equation307_4290_4291_4512_implies_Equation4283 G h307 h4290 h4291 h4512
  have h4314 := Equation4290_4291_4512_implies_Equation4314 G h4290 h4291 h4512
  have h4321 := Equation4283_4291_4512_implies_Equation4321 G h4283 h4291 h4512
  have h4284 := Equation307_4290_4321_4512_implies_Equation4284 G h307 h4290 h4321 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4299_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4299 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4299⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4284 := Equation4299_4512_implies_Equation4284 G h4299 h4512
  have h4290 := Equation4299_4512_implies_Equation4290 G h4299 h4512
  have h4283 := Equation307_4290_4291_4512_implies_Equation4283 G h307 h4290 h4291 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h326 := Equation323_4284_4512_implies_Equation326 G h323 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4300_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4300 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h4300⟩ := h
  exact hh

private theorem AT44_Equation4301_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4301 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4301⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4269 := Equation4301_4512_implies_Equation4269 G h4301 h4512
  have h4283 := Equation4301_4512_implies_Equation4283 G h4301 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h3308 := Equation3306_4283_4512_implies_Equation3308 G h3306 h4283 h4512
  have h4284 := Equation309_4512_implies_Equation4284 G h309 h4512
  have h3315 := Equation3308_4512_implies_Equation3315 G h3308 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4304_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4304 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h4304⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4284 := Equation4304_4512_implies_Equation4284 G h4304 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation4305_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4305 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4305⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4275 := Equation4305_4512_implies_Equation4275 G h4305 h4512
  have h4283 := Equation4305_4512_implies_Equation4283 G h4305 h4512
  have h3308 := Equation3306_4283_4512_implies_Equation3308 G h3306 h4283 h4512
  have h4304 := Equation4272_4275_4512_implies_Equation4304 G h4272 h4275 h4512
  have h4284 := Equation4304_4512_implies_Equation4284 G h4304 h4512
  have h3315 := Equation3308_4512_implies_Equation3315 G h3308 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4314_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4314 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4314⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4290 := Equation4291_4314_4512_implies_Equation4290 G h4291 h4314 h4512
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  have h4283 := Equation307_4290_4291_4512_implies_Equation4283 G h307 h4290 h4291 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h4284 := Equation4283_4314_4512_implies_Equation4284 G h4283 h4314 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4315_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4315 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4314 := Equation4315_4512_implies_Equation4314 G h4315 h4512
  have h4290 := Equation4291_4314_4512_implies_Equation4290 G h4291 h4314 h4512
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  have h4283 := Equation307_4290_4291_4512_implies_Equation4283 G h307 h4290 h4291 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h4284 := Equation4283_4314_4512_implies_Equation4284 G h4283 h4314 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4318_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4318 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4318⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4314 := Equation4318_4512_implies_Equation4314 G h4318 h4512
  have h4290 := Equation4291_4314_4512_implies_Equation4290 G h4291 h4314 h4512
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  have h4283 := Equation307_4290_4291_4512_implies_Equation4283 G h307 h4290 h4291 h4512
  have h4284 := Equation4283_4314_4512_implies_Equation4284 G h4283 h4314 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4320_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4320 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h4320⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4284 := Equation4291_4320_4512_implies_Equation4284 G h4291 h4320 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation4321_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4321 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4321⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h43 := Equation3316_4321_4512_implies_Equation43 G h3316 h4321 h4512
  have h40 := Equation3258_4321_4512_implies_Equation40 G h3258 h4321 h4512
  have h332 := Equation43_323_4512_implies_Equation332 G h43 h323 h4512
  have h4290 := Equation40_4512_implies_Equation4290 G h40 h4512
  have h4284 := Equation307_4290_4321_4512_implies_Equation4284 G h307 h4290 h4321 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h325 := Equation332_4512_implies_Equation325 G h332 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4325_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4325 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4325⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4273 := Equation4325_4512_implies_Equation4273 G h4325 h4512
  have h4320 := Equation4325_4512_implies_Equation4320 G h4325 h4512
  have h4284 := Equation4291_4320_4512_implies_Equation4284 G h4291 h4320 h4512
  have h3319 := Equation3353_4320_4512_implies_Equation3319 G h3353 h4320 h4512
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h3256 := Equation40_4512_implies_Equation3256 G h40 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4327_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4327 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h4327⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4320 := Equation4327_4512_implies_Equation4320 G h4327 h4512
  have h4284 := Equation4291_4320_4512_implies_Equation4284 G h4291 h4320 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation4331_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4331 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4331⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4314 := Equation4331_4512_implies_Equation4314 G h4331 h4512
  have h4343 := Equation4331_4512_implies_Equation4343 G h4331 h4512
  have h4283 := Equation307_4291_4343_4512_implies_Equation4283 G h307 h4291 h4343 h4512
  have h4284 := Equation4283_4314_4512_implies_Equation4284 G h4283 h4314 h4512
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4343_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4343 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4343⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h43 := Equation3316_4343_4512_implies_Equation43 G h3316 h4343 h4512
  have h4283 := Equation307_4291_4343_4512_implies_Equation4283 G h307 h4291 h4343 h4512
  have h332 := Equation43_323_4512_implies_Equation332 G h43 h323 h4512
  have h4284 := Equation307_4283_4343_4512_implies_Equation4284 G h307 h4283 h4343 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h325 := Equation332_4512_implies_Equation325 G h332 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4358_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4358 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4358⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4283 := Equation4358_4512_implies_Equation4283 G h4358 h4512
  have h40 := Equation3278_4283_4512_implies_Equation40 G h3278 h4283 h4512
  have h3308 := Equation3306_4283_4512_implies_Equation3308 G h3306 h4283 h4512
  have h4321 := Equation4283_4291_4512_implies_Equation4321 G h4283 h4291 h4512
  have h4290 := Equation40_4512_implies_Equation4290 G h40 h4512
  have h3315 := Equation3308_4512_implies_Equation3315 G h3308 h4512
  have h4284 := Equation307_4290_4321_4512_implies_Equation4284 G h307 h4290 h4321 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4362_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4362 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h4362⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4320 := Equation4362_4512_implies_Equation4320 G h4362 h4512
  have h4284 := Equation4291_4320_4512_implies_Equation4284 G h4291 h4320 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT44_Equation4364_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4364 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4364⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4290 := Equation4364_4512_implies_Equation4290 G h4364 h4512
  have h4320 := Equation4364_4512_implies_Equation4320 G h4364 h4512
  have h4314 := Equation4290_4291_4512_implies_Equation4314 G h4290 h4291 h4512
  have h4284 := Equation4291_4320_4512_implies_Equation4284 G h4291 h4320 h4512
  have h326 := Equation3316_4320_4512_implies_Equation326 G h3316 h4320 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4369_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4369 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4369⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at44
  obtain ⟨h1, h307, h312, h323, h333, h343, h3253, h3258, h3278, h3306, h3316, h3326, h3353, h3414, h4272, h4291, h4300, h4512⟩ := g hh
  have h4290 := Equation4369_4512_implies_Equation4290 G h4369 h4512
  have h4283 := Equation307_4290_4291_4512_implies_Equation4283 G h307 h4290 h4291 h4512
  have h4314 := Equation4290_4291_4512_implies_Equation4314 G h4290 h4291 h4512
  have h4321 := Equation4283_4291_4512_implies_Equation4321 G h4283 h4291 h4512
  have h4284 := Equation307_4290_4321_4512_implies_Equation4284 G h307 h4290 h4321 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT44_Equation4512_implies (G : Type*) [Magma G] (h : (AssociativeTheory44 G) ∧ (Equation4512 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h4512⟩ := h
  exact hh

theorem AT44_conj_implied (eqid : EQIndex) (G: Type*) [Magma G] (h : ATearly G (conj44 eqid)) : (AssociativeTheory44 G) ∧ (EQeq G eqid) := by
  have h0 := (AT_equiv G (conj44 eqid)).mp h
  rcases eqid
  all_goals
    constructor
    exact AT_implies G _ h at44 True.intro
    repeat' (obtain ⟨h1, h0⟩ := h0 ; try exact h1) ; try exact h0

theorem AT44_conj (eqid : EQIndex) (G: Type*) [Magma G] : (AssociativeTheory44 G) ∧ (EQeq G eqid) <-> (ATearly G (conj44 eqid)) :=
⟨match eqid with
| eq1 => AT44_Equation1_implies G
| eq2 => AT44_Equation2_implies G
| eq3 => AT44_Equation3_implies G
| eq4 => AT44_Equation4_implies G
| eq5 => AT44_Equation5_implies G
| eq8 => AT44_Equation8_implies G
| eq10 => AT44_Equation10_implies G
| eq11 => AT44_Equation11_implies G
| eq14 => AT44_Equation14_implies G
| eq16 => AT44_Equation16_implies G
| eq38 => AT44_Equation38_implies G
| eq39 => AT44_Equation39_implies G
| eq40 => AT44_Equation40_implies G
| eq41 => AT44_Equation41_implies G
| eq43 => AT44_Equation43_implies G
| eq47 => AT44_Equation47_implies G
| eq56 => AT44_Equation56_implies G
| eq66 => AT44_Equation66_implies G
| eq75 => AT44_Equation75_implies G
| eq307 => AT44_Equation307_implies G
| eq308 => AT44_Equation308_implies G
| eq309 => AT44_Equation309_implies G
| eq310 => AT44_Equation310_implies G
| eq311 => AT44_Equation311_implies G
| eq312 => AT44_Equation312_implies G
| eq313 => AT44_Equation313_implies G
| eq314 => AT44_Equation314_implies G
| eq315 => AT44_Equation315_implies G
| eq316 => AT44_Equation316_implies G
| eq318 => AT44_Equation318_implies G
| eq323 => AT44_Equation323_implies G
| eq325 => AT44_Equation325_implies G
| eq326 => AT44_Equation326_implies G
| eq327 => AT44_Equation327_implies G
| eq329 => AT44_Equation329_implies G
| eq332 => AT44_Equation332_implies G
| eq333 => AT44_Equation333_implies G
| eq343 => AT44_Equation343_implies G
| eq411 => AT44_Equation411_implies G
| eq419 => AT44_Equation419_implies G
| eq429 => AT44_Equation429_implies G
| eq440 => AT44_Equation440_implies G
| eq477 => AT44_Equation477_implies G
| eq504 => AT44_Equation504_implies G
| eq513 => AT44_Equation513_implies G
| eq3253 => AT44_Equation3253_implies G
| eq3255 => AT44_Equation3255_implies G
| eq3256 => AT44_Equation3256_implies G
| eq3258 => AT44_Equation3258_implies G
| eq3259 => AT44_Equation3259_implies G
| eq3260 => AT44_Equation3260_implies G
| eq3261 => AT44_Equation3261_implies G
| eq3264 => AT44_Equation3264_implies G
| eq3265 => AT44_Equation3265_implies G
| eq3267 => AT44_Equation3267_implies G
| eq3271 => AT44_Equation3271_implies G
| eq3273 => AT44_Equation3273_implies G
| eq3274 => AT44_Equation3274_implies G
| eq3275 => AT44_Equation3275_implies G
| eq3277 => AT44_Equation3277_implies G
| eq3278 => AT44_Equation3278_implies G
| eq3290 => AT44_Equation3290_implies G
| eq3292 => AT44_Equation3292_implies G
| eq3300 => AT44_Equation3300_implies G
| eq3306 => AT44_Equation3306_implies G
| eq3308 => AT44_Equation3308_implies G
| eq3309 => AT44_Equation3309_implies G
| eq3315 => AT44_Equation3315_implies G
| eq3316 => AT44_Equation3316_implies G
| eq3319 => AT44_Equation3319_implies G
| eq3322 => AT44_Equation3322_implies G
| eq3323 => AT44_Equation3323_implies G
| eq3326 => AT44_Equation3326_implies G
| eq3331 => AT44_Equation3331_implies G
| eq3334 => AT44_Equation3334_implies G
| eq3342 => AT44_Equation3342_implies G
| eq3346 => AT44_Equation3346_implies G
| eq3350 => AT44_Equation3350_implies G
| eq3353 => AT44_Equation3353_implies G
| eq3388 => AT44_Equation3388_implies G
| eq3414 => AT44_Equation3414_implies G
| eq4268 => AT44_Equation4268_implies G
| eq4269 => AT44_Equation4269_implies G
| eq4270 => AT44_Equation4270_implies G
| eq4271 => AT44_Equation4271_implies G
| eq4272 => AT44_Equation4272_implies G
| eq4273 => AT44_Equation4273_implies G
| eq4274 => AT44_Equation4274_implies G
| eq4275 => AT44_Equation4275_implies G
| eq4276 => AT44_Equation4276_implies G
| eq4277 => AT44_Equation4277_implies G
| eq4278 => AT44_Equation4278_implies G
| eq4279 => AT44_Equation4279_implies G
| eq4280 => AT44_Equation4280_implies G
| eq4283 => AT44_Equation4283_implies G
| eq4284 => AT44_Equation4284_implies G
| eq4286 => AT44_Equation4286_implies G
| eq4287 => AT44_Equation4287_implies G
| eq4288 => AT44_Equation4288_implies G
| eq4290 => AT44_Equation4290_implies G
| eq4291 => AT44_Equation4291_implies G
| eq4293 => AT44_Equation4293_implies G
| eq4296 => AT44_Equation4296_implies G
| eq4297 => AT44_Equation4297_implies G
| eq4299 => AT44_Equation4299_implies G
| eq4300 => AT44_Equation4300_implies G
| eq4301 => AT44_Equation4301_implies G
| eq4304 => AT44_Equation4304_implies G
| eq4305 => AT44_Equation4305_implies G
| eq4314 => AT44_Equation4314_implies G
| eq4315 => AT44_Equation4315_implies G
| eq4318 => AT44_Equation4318_implies G
| eq4320 => AT44_Equation4320_implies G
| eq4321 => AT44_Equation4321_implies G
| eq4325 => AT44_Equation4325_implies G
| eq4327 => AT44_Equation4327_implies G
| eq4331 => AT44_Equation4331_implies G
| eq4343 => AT44_Equation4343_implies G
| eq4358 => AT44_Equation4358_implies G
| eq4362 => AT44_Equation4362_implies G
| eq4364 => AT44_Equation4364_implies G
| eq4369 => AT44_Equation4369_implies G
| eq4512 => AT44_Equation4512_implies G
, AT44_conj_implied eqid G⟩

