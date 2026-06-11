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


def conj421 : EQIndex → ATIndex
| eq1 => at421
| eq2 => at2
| eq3 => at2
| eq4 => at2
| eq5 => at2
| eq8 => at9
| eq10 => at2
| eq11 => at9
| eq14 => at9
| eq16 => at9
| eq38 => at13
| eq39 => at13
| eq40 => at421
| eq41 => at13
| eq43 => at18
| eq47 => at2
| eq56 => at2
| eq66 => at2
| eq75 => at2
| eq307 => at423
| eq308 => at423
| eq309 => at424
| eq310 => at423
| eq311 => at35
| eq312 => at423
| eq313 => at424
| eq314 => at35
| eq315 => at423
| eq316 => at423
| eq318 => at35
| eq323 => at13
| eq325 => at13
| eq326 => at13
| eq327 => at13
| eq329 => at13
| eq332 => at13
| eq333 => at13
| eq343 => at13
| eq411 => at9
| eq419 => at9
| eq429 => at9
| eq440 => at9
| eq477 => at9
| eq504 => at9
| eq513 => at9
| eq3253 => at421
| eq3255 => at423
| eq3256 => at421
| eq3258 => at423
| eq3259 => at421
| eq3260 => at423
| eq3261 => at421
| eq3264 => at423
| eq3265 => at423
| eq3267 => at426
| eq3271 => at421
| eq3273 => at423
| eq3274 => at423
| eq3275 => at423
| eq3277 => at426
| eq3278 => at421
| eq3290 => at423
| eq3292 => at423
| eq3300 => at426
| eq3306 => at105
| eq3308 => at105
| eq3309 => at13
| eq3315 => at105
| eq3316 => at13
| eq3319 => at105
| eq3322 => at13
| eq3323 => at105
| eq3326 => at13
| eq3331 => at105
| eq3334 => at105
| eq3342 => at105
| eq3346 => at105
| eq3350 => at105
| eq3353 => at105
| eq3388 => at105
| eq3414 => at105
| eq4268 => at423
| eq4269 => at424
| eq4270 => at421
| eq4271 => at35
| eq4272 => at423
| eq4273 => at433
| eq4274 => at35
| eq4275 => at421
| eq4276 => at423
| eq4277 => at423
| eq4278 => at35
| eq4279 => at424
| eq4280 => at423
| eq4283 => at433
| eq4284 => at423
| eq4286 => at424
| eq4287 => at35
| eq4288 => at423
| eq4290 => at421
| eq4291 => at424
| eq4293 => at423
| eq4296 => at424
| eq4297 => at421
| eq4299 => at423
| eq4300 => at35
| eq4301 => at424
| eq4304 => at423
| eq4305 => at433
| eq4314 => at424
| eq4315 => at35
| eq4318 => at424
| eq4320 => at433
| eq4321 => at450
| eq4325 => at433
| eq4327 => at424
| eq4331 => at424
| eq4343 => at423
| eq4358 => at397
| eq4362 => at397
| eq4364 => at397
| eq4369 => at421
| eq4512 => at421


private theorem AT421_Equation1_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation1 G)) : AssociativeTheory421 G := by
  obtain ⟨hh, h1⟩ := h
  exact hh

private theorem AT421_Equation2_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation2 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h2⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  exact ⟨h2, h4512⟩

private theorem AT421_Equation3_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h3⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h3306 := Equation3_4512_implies_Equation3306 G h3 h4512
  have h3350 := Equation40_3306_4512_implies_Equation3350 G h40 h3306 h4512
  have h4273 := Equation3350_4512_implies_Equation4273 G h3350 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT421_Equation4_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h4⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h47 := Equation4_4512_implies_Equation47 G h4 h4512
  have h4269 := Equation4_4512_implies_Equation4269 G h4 h4512
  have h4273 := Equation4269_4290_4512_implies_Equation4273 G h4269 h4290 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT421_Equation5_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation5 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h5⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h47 := Equation5_4512_implies_Equation47 G h5 h4512
  have h4320 := Equation5_4512_implies_Equation4320 G h5 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT421_Equation8_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation8 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h8⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3306 := Equation8_4512_implies_Equation3306 G h8 h4512
  have h3319 := Equation8_4512_implies_Equation3319 G h8 h4512
  have h3350 := Equation40_3306_4512_implies_Equation3350 G h40 h3306 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h11 := Equation429_3315_4512_implies_Equation11 G h429 h3315 h4512
  have h3353 := Equation3350_4512_implies_Equation3353 G h3350 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT421_Equation10_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation10 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h10⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h47 := Equation10_4512_implies_Equation47 G h10 h4512
  have h4269 := Equation10_4512_implies_Equation4269 G h10 h4512
  have h4273 := Equation4269_4290_4512_implies_Equation4273 G h4269 h4290 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT421_Equation11_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation11 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h11⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h411 := Equation11_4512_implies_Equation411 G h11 h4512
  have h3306 := Equation11_4512_implies_Equation3306 G h11 h4512
  have h4283 := Equation11_4512_implies_Equation4283 G h11 h4512
  have h43 := Equation411_4283_4290_4512_implies_Equation43 G h411 h4283 h4290 h4512
  have h3342 := Equation43_3306_4512_implies_Equation3342 G h43 h3306 h4512
  have h3353 := Equation3342_4512_implies_Equation3353 G h3342 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT421_Equation14_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation14 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h14⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  exact ⟨h14, h4512⟩

private theorem AT421_Equation16_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation16 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h16⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h8 := Equation16_4512_implies_Equation8 G h16 h4512
  have h513 := Equation16_4512_implies_Equation513 G h16 h4512
  have h3353 := Equation16_4512_implies_Equation3353 G h16 h4512
  have h440 := Equation513_4290_4512_implies_Equation440 G h513 h4290 h4512
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT421_Equation38_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation38 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h38⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation38_4512_implies_Equation307 G h38 h4512
  have h323 := Equation38_4512_implies_Equation323 G h38 h4512
  have h4284 := Equation38_4512_implies_Equation4284 G h38 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT421_Equation39_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation39 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h39⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation39_4512_implies_Equation307 G h39 h4512
  have h3258 := Equation39_4512_implies_Equation3258 G h39 h4512
  have h3319 := Equation39_4512_implies_Equation3319 G h39 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT421_Equation40_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation40 G)) : AssociativeTheory421 G := by
  obtain ⟨hh, h40⟩ := h
  exact hh

private theorem AT421_Equation41_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation41 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h41⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h38 := Equation41_4512_implies_Equation38 G h41 h4512
  have h39 := Equation41_4512_implies_Equation39 G h41 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT421_Equation43_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation43 G)) : AssociativeTheory18 G := by
  obtain ⟨hh, h43⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  exact ⟨h40, h43, h4512⟩

private theorem AT421_Equation47_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation47 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h47⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h43 := Equation47_4290_4512_implies_Equation43 G h47 h4290 h4512
  have h4320 := Equation43_4512_implies_Equation4320 G h43 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT421_Equation56_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation56 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h56⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h47 := Equation56_4512_implies_Equation47 G h56 h4512
  have h43 := Equation47_4290_4512_implies_Equation43 G h47 h4290 h4512
  have h4320 := Equation43_4512_implies_Equation4320 G h43 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT421_Equation66_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation66 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h66⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h47 := Equation66_4512_implies_Equation47 G h66 h4512
  have h4320 := Equation66_4512_implies_Equation4320 G h66 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT421_Equation75_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation75 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h75⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h47 := Equation75_4512_implies_Equation47 G h75 h4512
  have h43 := Equation47_4290_4512_implies_Equation43 G h47 h4290 h4512
  have h4320 := Equation43_4512_implies_Equation4320 G h43 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT421_Equation307_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation307 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h307⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation308_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation308 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h308⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation308_4512_implies_Equation307 G h308 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation309_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation309 G)) : AssociativeTheory424 G := by
  obtain ⟨hh, h309⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  exact ⟨h309, h4369, h4512⟩

private theorem AT421_Equation310_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation310 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h310⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation310_4512_implies_Equation307 G h310 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation311_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation311 G)) : AssociativeTheory35 G := by
  obtain ⟨hh, h311⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  exact ⟨h40, h311, h4512⟩

private theorem AT421_Equation312_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation312 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h312⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation312_4512_implies_Equation307 G h312 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation313_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation313 G)) : AssociativeTheory424 G := by
  obtain ⟨hh, h313⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h309 := Equation313_4512_implies_Equation309 G h313 h4512
  exact ⟨h309, h4369, h4512⟩

private theorem AT421_Equation314_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation314 G)) : AssociativeTheory35 G := by
  obtain ⟨hh, h314⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h311 := Equation314_4512_implies_Equation311 G h314 h4512
  exact ⟨h40, h311, h4512⟩

private theorem AT421_Equation315_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation315 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation315_4512_implies_Equation307 G h315 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation316_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation316 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h316⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation316_4512_implies_Equation307 G h316 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation318_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation318 G)) : AssociativeTheory35 G := by
  obtain ⟨hh, h318⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation318_4512_implies_Equation307 G h318 h4512
  have h309 := Equation318_4512_implies_Equation309 G h318 h4512
  have h4269 := Equation318_4512_implies_Equation4269 G h318 h4512
  have h4287 := Equation318_4512_implies_Equation4287 G h318 h4512
  have h4291 := Equation318_4512_implies_Equation4291 G h318 h4512
  have h4283 := Equation307_4290_4291_4512_implies_Equation4283 G h307 h4290 h4291 h4512
  have h4268 := Equation4269_4283_4512_implies_Equation4268 G h4269 h4283 h4512
  have h4271 := Equation4268_4287_4512_implies_Equation4271 G h4268 h4287 h4512
  have h4315 := Equation4271_4512_implies_Equation4315 G h4271 h4512
  have h311 := Equation309_4315_4512_implies_Equation311 G h309 h4315 h4512
  exact ⟨h40, h311, h4512⟩

private theorem AT421_Equation323_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation323 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h323⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation323_4512_implies_Equation307 G h323 h4512
  have h3306 := Equation323_4512_implies_Equation3306 G h323 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h3331 := Equation3256_3306_4512_implies_Equation3331 G h3256 h3306 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h3315 := Equation3331_4512_implies_Equation3315 G h3331 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT421_Equation325_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation325 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h325⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation325_4512_implies_Equation307 G h325 h4512
  have h3319 := Equation325_4512_implies_Equation3319 G h325 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h3306 := Equation3261_3319_4512_implies_Equation3306 G h3261 h3319 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT421_Equation326_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation326 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h326⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation326_4512_implies_Equation307 G h326 h4512
  have h3319 := Equation326_4512_implies_Equation3319 G h326 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h323 := Equation326_4284_4512_implies_Equation323 G h326 h4284 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT421_Equation327_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation327 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h327⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation327_4512_implies_Equation307 G h327 h4512
  have h325 := Equation327_4512_implies_Equation325 G h327 h4512
  have h3319 := Equation327_4512_implies_Equation3319 G h327 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h3306 := Equation3261_3319_4512_implies_Equation3306 G h3261 h3319 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT421_Equation329_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation329 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h329⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation329_4512_implies_Equation307 G h329 h4512
  have h323 := Equation329_4512_implies_Equation323 G h329 h4512
  have h3258 := Equation329_4512_implies_Equation3258 G h329 h4512
  have h3319 := Equation329_4512_implies_Equation3319 G h329 h4512
  have h4284 := Equation329_4512_implies_Equation4284 G h329 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT421_Equation332_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation332 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h332⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation332_4512_implies_Equation307 G h332 h4512
  have h323 := Equation332_4512_implies_Equation323 G h332 h4512
  have h325 := Equation332_4512_implies_Equation325 G h332 h4512
  have h4284 := Equation332_4512_implies_Equation4284 G h332 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT421_Equation333_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation333 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h333⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation333_4512_implies_Equation307 G h333 h4512
  have h323 := Equation333_4512_implies_Equation323 G h333 h4512
  have h3316 := Equation333_4512_implies_Equation3316 G h333 h4512
  have h4291 := Equation333_4512_implies_Equation4291 G h333 h4512
  have h4314 := Equation4290_4291_4512_implies_Equation4314 G h4290 h4291 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT421_Equation343_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation343 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h343⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation343_4512_implies_Equation307 G h343 h4512
  have h312 := Equation343_4512_implies_Equation312 G h343 h4512
  have h323 := Equation343_4512_implies_Equation323 G h343 h4512
  have h3258 := Equation343_4512_implies_Equation3258 G h343 h4512
  have h3316 := Equation343_4512_implies_Equation3316 G h343 h4512
  have h4291 := Equation343_4512_implies_Equation4291 G h343 h4512
  have h4314 := Equation4290_4291_4512_implies_Equation4314 G h4290 h4291 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT421_Equation411_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation411 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h411⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h8 := Equation411_4270_4512_implies_Equation8 G h411 h4270 h4512
  have h43 := Equation411_4369_4512_implies_Equation43 G h411 h4369 h4512
  have h419 := Equation8_3261_4512_implies_Equation419 G h8 h3261 h4512
  have h3306 := Equation8_4512_implies_Equation3306 G h8 h4512
  have h3319 := Equation8_4512_implies_Equation3319 G h8 h4512
  have h3342 := Equation43_3306_4512_implies_Equation3342 G h43 h3306 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h11 := Equation429_3315_4512_implies_Equation11 G h429 h3315 h4512
  have h3353 := Equation3342_4512_implies_Equation3353 G h3342 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT421_Equation419_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation419 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h419⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h3306 := Equation419_4512_implies_Equation3306 G h419 h4512
  have h3319 := Equation419_4512_implies_Equation3319 G h419 h4512
  have h3350 := Equation40_3306_4512_implies_Equation3350 G h40 h3306 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h11 := Equation429_3315_4512_implies_Equation11 G h429 h3315 h4512
  have h3353 := Equation3350_4512_implies_Equation3353 G h3350 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT421_Equation429_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation429 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h429⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h3306 := Equation429_4512_implies_Equation3306 G h429 h4512
  have h3319 := Equation429_4512_implies_Equation3319 G h429 h4512
  have h3350 := Equation40_3306_4512_implies_Equation3350 G h40 h3306 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h11 := Equation429_3315_4512_implies_Equation11 G h429 h3315 h4512
  have h3353 := Equation3350_4512_implies_Equation3353 G h3350 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT421_Equation440_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation440 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h440⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h504 := Equation440_4290_4512_implies_Equation504 G h440 h4290 h4512
  have h411 := Equation440_4512_implies_Equation411 G h440 h4512
  have h8 := Equation411_4270_4512_implies_Equation8 G h411 h4270 h4512
  have h513 := Equation504_4512_implies_Equation513 G h504 h4512
  have h16 := Equation8_513_4512_implies_Equation16 G h8 h513 h4512
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  have h3353 := Equation16_4512_implies_Equation3353 G h16 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT421_Equation477_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation477 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h477⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h411 := Equation477_4512_implies_Equation411 G h477 h4512
  have h440 := Equation477_4512_implies_Equation440 G h477 h4512
  have h513 := Equation477_4512_implies_Equation513 G h477 h4512
  have h8 := Equation411_4270_4512_implies_Equation8 G h411 h4270 h4512
  have h16 := Equation8_513_4512_implies_Equation16 G h8 h513 h4512
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  have h3353 := Equation16_4512_implies_Equation3353 G h16 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT421_Equation504_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation504 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h504⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h411 := Equation504_4512_implies_Equation411 G h504 h4512
  have h440 := Equation504_4512_implies_Equation440 G h504 h4512
  have h513 := Equation504_4512_implies_Equation513 G h504 h4512
  have h8 := Equation411_4270_4512_implies_Equation8 G h411 h4270 h4512
  have h16 := Equation8_513_4512_implies_Equation16 G h8 h513 h4512
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  have h3353 := Equation16_4512_implies_Equation3353 G h16 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT421_Equation513_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation513 G)) : AssociativeTheory9 G := by
  obtain ⟨hh, h513⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h440 := Equation513_4290_4512_implies_Equation440 G h513 h4290 h4512
  have h411 := Equation513_4512_implies_Equation411 G h513 h4512
  have h8 := Equation411_4270_4512_implies_Equation8 G h411 h4270 h4512
  have h16 := Equation8_513_4512_implies_Equation16 G h8 h513 h4512
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  have h3353 := Equation16_4512_implies_Equation3353 G h16 h4512
  have h14 := Equation11_3353_4512_implies_Equation14 G h11 h3353 h4512
  exact ⟨h14, h4512⟩

private theorem AT421_Equation3253_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3253 G)) : AssociativeTheory421 G := by
  obtain ⟨hh, h3253⟩ := h
  exact hh

private theorem AT421_Equation3255_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3255 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h3255⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation3255_4512_implies_Equation307 G h3255 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation3256_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3256 G)) : AssociativeTheory421 G := by
  obtain ⟨hh, h3256⟩ := h
  exact hh

private theorem AT421_Equation3258_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3258 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h3258⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation3258_4512_implies_Equation307 G h3258 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation3259_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3259 G)) : AssociativeTheory421 G := by
  obtain ⟨hh, h3259⟩ := h
  exact hh

private theorem AT421_Equation3260_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3260 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h3260⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation3260_4512_implies_Equation307 G h3260 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation3261_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3261 G)) : AssociativeTheory421 G := by
  obtain ⟨hh, h3261⟩ := h
  exact hh

private theorem AT421_Equation3264_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3264 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h3264⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation3264_4512_implies_Equation307 G h3264 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation3265_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3265 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h3265⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation3265_4512_implies_Equation307 G h3265 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation3267_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3267 G)) : AssociativeTheory426 G := by
  obtain ⟨hh, h3267⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  exact ⟨h3267, h4369, h4512⟩

private theorem AT421_Equation3271_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3271 G)) : AssociativeTheory421 G := by
  obtain ⟨hh, h3271⟩ := h
  exact hh

private theorem AT421_Equation3273_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3273 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h3273⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation3273_4512_implies_Equation307 G h3273 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation3274_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3274 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h3274⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation3274_4512_implies_Equation307 G h3274 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation3275_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3275 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h3275⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation3275_4512_implies_Equation307 G h3275 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation3277_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3277 G)) : AssociativeTheory426 G := by
  obtain ⟨hh, h3277⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h3267 := Equation3277_4512_implies_Equation3267 G h3277 h4512
  exact ⟨h3267, h4369, h4512⟩

private theorem AT421_Equation3278_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3278 G)) : AssociativeTheory421 G := by
  obtain ⟨hh, h3278⟩ := h
  exact hh

private theorem AT421_Equation3290_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3290 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h3290⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation3290_4512_implies_Equation307 G h3290 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation3292_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3292 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h3292⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation3292_4512_implies_Equation307 G h3292 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation3300_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3300 G)) : AssociativeTheory426 G := by
  obtain ⟨hh, h3300⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h3267 := Equation40_3300_4512_implies_Equation3267 G h40 h3300 h4512
  exact ⟨h3267, h4369, h4512⟩

private theorem AT421_Equation3306_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3306 G)) : AssociativeTheory105 G := by
  obtain ⟨hh, h3306⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  exact ⟨h40, h3306, h4512⟩

private theorem AT421_Equation3308_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3308 G)) : AssociativeTheory105 G := by
  obtain ⟨hh, h3308⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h3306 := Equation3308_4512_implies_Equation3306 G h3308 h4512
  exact ⟨h40, h3306, h4512⟩

private theorem AT421_Equation3309_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3309 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3309⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation3309_4512_implies_Equation307 G h3309 h4512
  have h323 := Equation3309_4512_implies_Equation323 G h3309 h4512
  have h3319 := Equation3309_4512_implies_Equation3319 G h3309 h4512
  have h4284 := Equation3309_4512_implies_Equation4284 G h3309 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT421_Equation3315_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3315 G)) : AssociativeTheory105 G := by
  obtain ⟨hh, h3315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h3319 := Equation3315_4512_implies_Equation3319 G h3315 h4512
  have h3306 := Equation3261_3319_4512_implies_Equation3306 G h3261 h3319 h4512
  exact ⟨h40, h3306, h4512⟩

private theorem AT421_Equation3316_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3316 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3316⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h43 := Equation3316_4290_4512_implies_Equation43 G h3316 h4290 h4512
  have h307 := Equation3316_4512_implies_Equation307 G h3316 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h4283 := Equation43_4512_implies_Equation4283 G h43 h4512
  have h4320 := Equation43_4512_implies_Equation4320 G h43 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h326 := Equation3316_4320_4512_implies_Equation326 G h3316 h4320 h4512
  have h323 := Equation3316_4283_4512_implies_Equation323 G h3316 h4283 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT421_Equation3319_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3319 G)) : AssociativeTheory105 G := by
  obtain ⟨hh, h3319⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h3306 := Equation3261_3319_4512_implies_Equation3306 G h3261 h3319 h4512
  exact ⟨h40, h3306, h4512⟩

private theorem AT421_Equation3322_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3322 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3322⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation3322_4512_implies_Equation307 G h3322 h4512
  have h326 := Equation3322_4512_implies_Equation326 G h3322 h4512
  have h3319 := Equation3322_4512_implies_Equation3319 G h3322 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h323 := Equation326_4284_4512_implies_Equation323 G h326 h4284 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT421_Equation3323_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3323 G)) : AssociativeTheory105 G := by
  obtain ⟨hh, h3323⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h3319 := Equation3323_4512_implies_Equation3319 G h3323 h4512
  have h3306 := Equation3261_3319_4512_implies_Equation3306 G h3261 h3319 h4512
  exact ⟨h40, h3306, h4512⟩

private theorem AT421_Equation3326_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3326 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3326⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation3326_4512_implies_Equation307 G h3326 h4512
  have h323 := Equation3326_4512_implies_Equation323 G h3326 h4512
  have h3258 := Equation3326_4512_implies_Equation3258 G h3326 h4512
  have h3306 := Equation3326_4512_implies_Equation3306 G h3326 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h3331 := Equation3256_3306_4512_implies_Equation3331 G h3256 h3306 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h3315 := Equation3331_4512_implies_Equation3315 G h3331 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT421_Equation3331_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3331 G)) : AssociativeTheory105 G := by
  obtain ⟨hh, h3331⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h3306 := Equation3331_4512_implies_Equation3306 G h3331 h4512
  exact ⟨h40, h3306, h4512⟩

private theorem AT421_Equation3334_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3334 G)) : AssociativeTheory105 G := by
  obtain ⟨hh, h3334⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h3306 := Equation3334_4512_implies_Equation3306 G h3334 h4512
  exact ⟨h40, h3306, h4512⟩

private theorem AT421_Equation3342_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3342 G)) : AssociativeTheory105 G := by
  obtain ⟨hh, h3342⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h3306 := Equation3342_4512_implies_Equation3306 G h3342 h4512
  exact ⟨h40, h3306, h4512⟩

private theorem AT421_Equation3346_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3346 G)) : AssociativeTheory105 G := by
  obtain ⟨hh, h3346⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h3306 := Equation3346_4512_implies_Equation3306 G h3346 h4512
  exact ⟨h40, h3306, h4512⟩

private theorem AT421_Equation3350_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3350 G)) : AssociativeTheory105 G := by
  obtain ⟨hh, h3350⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h3306 := Equation3350_4512_implies_Equation3306 G h3350 h4512
  exact ⟨h40, h3306, h4512⟩

private theorem AT421_Equation3353_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3353 G)) : AssociativeTheory105 G := by
  obtain ⟨hh, h3353⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h3306 := Equation3353_4512_implies_Equation3306 G h3353 h4512
  exact ⟨h40, h3306, h4512⟩

private theorem AT421_Equation3388_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3388 G)) : AssociativeTheory105 G := by
  obtain ⟨hh, h3388⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h3306 := Equation3388_4512_implies_Equation3306 G h3388 h4512
  exact ⟨h40, h3306, h4512⟩

private theorem AT421_Equation3414_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation3414 G)) : AssociativeTheory105 G := by
  obtain ⟨hh, h3414⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h3306 := Equation3414_4512_implies_Equation3306 G h3414 h4512
  exact ⟨h40, h3306, h4512⟩

private theorem AT421_Equation4268_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4268 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h4268⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation3253_4268_4512_implies_Equation307 G h3253 h4268 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation4269_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4269 G)) : AssociativeTheory424 G := by
  obtain ⟨hh, h4269⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation3253_4269_4512_implies_Equation307 G h3253 h4269 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h309, h4369, h4512⟩

private theorem AT421_Equation4270_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4270 G)) : AssociativeTheory421 G := by
  obtain ⟨hh, h4270⟩ := h
  exact hh

private theorem AT421_Equation4271_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4271 G)) : AssociativeTheory35 G := by
  obtain ⟨hh, h4271⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4269 := Equation4271_4512_implies_Equation4269 G h4271 h4512
  have h4314 := Equation4271_4512_implies_Equation4314 G h4271 h4512
  have h4315 := Equation4271_4512_implies_Equation4315 G h4271 h4512
  have h307 := Equation3253_4314_4512_implies_Equation307 G h3253 h4314 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h311 := Equation309_4315_4512_implies_Equation311 G h309 h4315 h4512
  exact ⟨h40, h311, h4512⟩

private theorem AT421_Equation4272_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4272 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h4272⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation3253_4272_4512_implies_Equation307 G h3253 h4272 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation4273_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4273 G)) : AssociativeTheory433 G := by
  obtain ⟨hh, h4273⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  exact ⟨h40, h4273, h4369, h4512⟩

private theorem AT421_Equation4274_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4274 G)) : AssociativeTheory35 G := by
  obtain ⟨hh, h4274⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4268 := Equation4274_4512_implies_Equation4268 G h4274 h4512
  have h4269 := Equation4274_4512_implies_Equation4269 G h4274 h4512
  have h4315 := Equation4274_4512_implies_Equation4315 G h4274 h4512
  have h307 := Equation3253_4268_4512_implies_Equation307 G h3253 h4268 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h311 := Equation309_4315_4512_implies_Equation311 G h309 h4315 h4512
  exact ⟨h40, h311, h4512⟩

private theorem AT421_Equation4275_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4275 G)) : AssociativeTheory421 G := by
  obtain ⟨hh, h4275⟩ := h
  exact hh

private theorem AT421_Equation4276_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4276 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h4276⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4268 := Equation4275_4276_4512_implies_Equation4268 G h4275 h4276 h4512
  have h307 := Equation3253_4268_4512_implies_Equation307 G h3253 h4268 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation4277_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4277 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h4277⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4293 := Equation4277_4512_implies_Equation4293 G h4277 h4512
  have h307 := Equation3253_4293_4512_implies_Equation307 G h3253 h4293 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation4278_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4278 G)) : AssociativeTheory35 G := by
  obtain ⟨hh, h4278⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4269 := Equation4278_4512_implies_Equation4269 G h4278 h4512
  have h4287 := Equation4278_4512_implies_Equation4287 G h4278 h4512
  have h4291 := Equation4278_4512_implies_Equation4291 G h4278 h4512
  have h4300 := Equation4278_4512_implies_Equation4300 G h4278 h4512
  have h4268 := Equation4270_4300_4512_implies_Equation4268 G h4270 h4300 h4512
  have h307 := Equation3253_4291_4512_implies_Equation307 G h3253 h4291 h4512
  have h4271 := Equation4268_4287_4512_implies_Equation4271 G h4268 h4287 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h4315 := Equation4271_4512_implies_Equation4315 G h4271 h4512
  have h311 := Equation309_4315_4512_implies_Equation311 G h309 h4315 h4512
  exact ⟨h40, h311, h4512⟩

private theorem AT421_Equation4279_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4279 G)) : AssociativeTheory424 G := by
  obtain ⟨hh, h4279⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4269 := Equation4279_4512_implies_Equation4269 G h4279 h4512
  have h4321 := Equation4279_4512_implies_Equation4321 G h4279 h4512
  have h307 := Equation3253_4321_4512_implies_Equation307 G h3253 h4321 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h309, h4369, h4512⟩

private theorem AT421_Equation4280_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4280 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h4280⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4272 := Equation4280_4512_implies_Equation4272 G h4280 h4512
  have h307 := Equation3253_4272_4512_implies_Equation307 G h3253 h4272 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation4283_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4283 G)) : AssociativeTheory433 G := by
  obtain ⟨hh, h4283⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4273 := Equation4275_4283_4512_implies_Equation4273 G h4275 h4283 h4512
  exact ⟨h40, h4273, h4369, h4512⟩

private theorem AT421_Equation4284_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4284 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h4284⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation3253_4284_4512_implies_Equation307 G h3253 h4284 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation4286_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4286 G)) : AssociativeTheory424 G := by
  obtain ⟨hh, h4286⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4268 := Equation4286_4512_implies_Equation4268 G h4286 h4512
  have h4269 := Equation4286_4512_implies_Equation4269 G h4286 h4512
  have h307 := Equation3253_4268_4512_implies_Equation307 G h3253 h4268 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h309, h4369, h4512⟩

private theorem AT421_Equation4287_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4287 G)) : AssociativeTheory35 G := by
  obtain ⟨hh, h4287⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4269 := Equation4287_4512_implies_Equation4269 G h4287 h4512
  have h4284 := Equation4287_4512_implies_Equation4284 G h4287 h4512
  have h4268 := Equation4270_4284_4512_implies_Equation4268 G h4270 h4284 h4512
  have h307 := Equation3253_4269_4512_implies_Equation307 G h3253 h4269 h4512
  have h4271 := Equation4268_4287_4512_implies_Equation4271 G h4268 h4287 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h4315 := Equation4271_4512_implies_Equation4315 G h4271 h4512
  have h311 := Equation309_4315_4512_implies_Equation311 G h309 h4315 h4512
  exact ⟨h40, h311, h4512⟩

private theorem AT421_Equation4288_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4288 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h4288⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4268 := Equation4288_4512_implies_Equation4268 G h4288 h4512
  have h307 := Equation3253_4268_4512_implies_Equation307 G h3253 h4268 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation4290_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4290 G)) : AssociativeTheory421 G := by
  obtain ⟨hh, h4290⟩ := h
  exact hh

private theorem AT421_Equation4291_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4291 G)) : AssociativeTheory424 G := by
  obtain ⟨hh, h4291⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4269 := Equation4275_4291_4512_implies_Equation4269 G h4275 h4291 h4512
  have h307 := Equation3253_4291_4512_implies_Equation307 G h3253 h4291 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h309, h4369, h4512⟩

private theorem AT421_Equation4293_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4293 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h4293⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation3253_4293_4512_implies_Equation307 G h3253 h4293 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation4296_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4296 G)) : AssociativeTheory424 G := by
  obtain ⟨hh, h4296⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4269 := Equation4296_4512_implies_Equation4269 G h4296 h4512
  have h4291 := Equation4296_4512_implies_Equation4291 G h4296 h4512
  have h307 := Equation3253_4291_4512_implies_Equation307 G h3253 h4291 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h309, h4369, h4512⟩

private theorem AT421_Equation4297_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4297 G)) : AssociativeTheory421 G := by
  obtain ⟨hh, h4297⟩ := h
  exact hh

private theorem AT421_Equation4299_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4299 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h4299⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4293 := Equation4299_4512_implies_Equation4293 G h4299 h4512
  have h307 := Equation3253_4293_4512_implies_Equation307 G h3253 h4293 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation4300_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4300 G)) : AssociativeTheory35 G := by
  obtain ⟨hh, h4300⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4268 := Equation4270_4300_4512_implies_Equation4268 G h4270 h4300 h4512
  have h4291 := Equation4300_4512_implies_Equation4291 G h4300 h4512
  have h4269 := Equation4275_4291_4512_implies_Equation4269 G h4275 h4291 h4512
  have h307 := Equation3253_4291_4512_implies_Equation307 G h3253 h4291 h4512
  have h4278 := Equation4269_4300_4512_implies_Equation4278 G h4269 h4300 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h4287 := Equation4278_4512_implies_Equation4287 G h4278 h4512
  have h4271 := Equation4268_4287_4512_implies_Equation4271 G h4268 h4287 h4512
  have h4315 := Equation4271_4512_implies_Equation4315 G h4271 h4512
  have h311 := Equation309_4315_4512_implies_Equation311 G h309 h4315 h4512
  exact ⟨h40, h311, h4512⟩

private theorem AT421_Equation4301_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4301 G)) : AssociativeTheory424 G := by
  obtain ⟨hh, h4301⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4269 := Equation4301_4512_implies_Equation4269 G h4301 h4512
  have h4291 := Equation4301_4512_implies_Equation4291 G h4301 h4512
  have h307 := Equation3253_4291_4512_implies_Equation307 G h3253 h4291 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h309, h4369, h4512⟩

private theorem AT421_Equation4304_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4304 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h4304⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4272 := Equation4304_4512_implies_Equation4272 G h4304 h4512
  have h307 := Equation3253_4272_4512_implies_Equation307 G h3253 h4272 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation4305_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4305 G)) : AssociativeTheory433 G := by
  obtain ⟨hh, h4305⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4273 := Equation4305_4512_implies_Equation4273 G h4305 h4512
  exact ⟨h40, h4273, h4369, h4512⟩

private theorem AT421_Equation4314_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4314 G)) : AssociativeTheory424 G := by
  obtain ⟨hh, h4314⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4269 := Equation4270_4314_4512_implies_Equation4269 G h4270 h4314 h4512
  have h307 := Equation3253_4314_4512_implies_Equation307 G h3253 h4314 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h309, h4369, h4512⟩

private theorem AT421_Equation4315_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4315 G)) : AssociativeTheory35 G := by
  obtain ⟨hh, h4315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4269 := Equation4275_4315_4512_implies_Equation4269 G h4275 h4315 h4512
  have h4314 := Equation4315_4512_implies_Equation4314 G h4315 h4512
  have h307 := Equation3253_4314_4512_implies_Equation307 G h3253 h4314 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h311 := Equation309_4315_4512_implies_Equation311 G h309 h4315 h4512
  exact ⟨h40, h311, h4512⟩

private theorem AT421_Equation4318_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4318 G)) : AssociativeTheory424 G := by
  obtain ⟨hh, h4318⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4269 := Equation4318_4512_implies_Equation4269 G h4318 h4512
  have h4314 := Equation4318_4512_implies_Equation4314 G h4318 h4512
  have h307 := Equation3253_4314_4512_implies_Equation307 G h3253 h4314 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h309, h4369, h4512⟩

private theorem AT421_Equation4320_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4320 G)) : AssociativeTheory433 G := by
  obtain ⟨hh, h4320⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  exact ⟨h40, h4273, h4369, h4512⟩

private theorem AT421_Equation4321_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4321 G)) : AssociativeTheory450 G := by
  obtain ⟨hh, h4321⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  exact ⟨h40, h4321, h4369, h4512⟩

private theorem AT421_Equation4325_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4325 G)) : AssociativeTheory433 G := by
  obtain ⟨hh, h4325⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4273 := Equation4325_4512_implies_Equation4273 G h4325 h4512
  exact ⟨h40, h4273, h4369, h4512⟩

private theorem AT421_Equation4327_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4327 G)) : AssociativeTheory424 G := by
  obtain ⟨hh, h4327⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4269 := Equation4327_4512_implies_Equation4269 G h4327 h4512
  have h307 := Equation3253_4269_4512_implies_Equation307 G h3253 h4269 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h309, h4369, h4512⟩

private theorem AT421_Equation4331_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4331 G)) : AssociativeTheory424 G := by
  obtain ⟨hh, h4331⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4269 := Equation4331_4512_implies_Equation4269 G h4331 h4512
  have h4314 := Equation4331_4512_implies_Equation4314 G h4331 h4512
  have h307 := Equation3253_4314_4512_implies_Equation307 G h3253 h4314 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  exact ⟨h309, h4369, h4512⟩

private theorem AT421_Equation4343_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4343 G)) : AssociativeTheory423 G := by
  obtain ⟨hh, h4343⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h307 := Equation3253_4343_4512_implies_Equation307 G h3253 h4343 h4512
  exact ⟨h40, h307, h4369, h4512⟩

private theorem AT421_Equation4358_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4358 G)) : AssociativeTheory397 G := by
  obtain ⟨hh, h4358⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4362 := Equation4358_4369_4512_implies_Equation4362 G h4358 h4369 h4512
  exact ⟨h40, h4358, h4362, h4512⟩

private theorem AT421_Equation4362_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4362 G)) : AssociativeTheory397 G := by
  obtain ⟨hh, h4362⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4358 := Equation4362_4369_4512_implies_Equation4358 G h4362 h4369 h4512
  exact ⟨h40, h4358, h4362, h4512⟩

private theorem AT421_Equation4364_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4364 G)) : AssociativeTheory397 G := by
  obtain ⟨hh, h4364⟩ := h
  obtain ⟨g, _⟩ := AT_equiv G at421
  obtain ⟨h1, h40, h3253, h3256, h3259, h3261, h3271, h3278, h4270, h4275, h4290, h4297, h4369, h4512⟩ := g hh
  have h4358 := Equation4364_4369_4512_implies_Equation4358 G h4364 h4369 h4512
  have h4362 := Equation4358_4364_4512_implies_Equation4362 G h4358 h4364 h4512
  exact ⟨h40, h4358, h4362, h4512⟩

private theorem AT421_Equation4369_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4369 G)) : AssociativeTheory421 G := by
  obtain ⟨hh, h4369⟩ := h
  exact hh

private theorem AT421_Equation4512_implies (G : Type*) [Magma G] (h : (AssociativeTheory421 G) ∧ (Equation4512 G)) : AssociativeTheory421 G := by
  obtain ⟨hh, h4512⟩ := h
  exact hh

theorem AT421_conj_implied (G: Type*) [Magma G] (eqid : EQIndex) (h : ATearly G (conj421 eqid)) : (AssociativeTheory421 G) ∧ (EQeq G eqid) := by
have hh := (AT_equiv G (conj421 eqid)).mp h
rcases eqid
all_goals
  obtain ⟨_, _⟩ := hh
  tauto

theorem AT421_conj (G: Type*) [Magma G] (eqid : EQIndex) : (AssociativeTheory421 G) ∧ (EQeq G eqid) <-> (ATearly G (conj421 eqid)) :=
⟨match eqid with
| eq1 => AT421_Equation1_implies G
| eq2 => AT421_Equation2_implies G
| eq3 => AT421_Equation3_implies G
| eq4 => AT421_Equation4_implies G
| eq5 => AT421_Equation5_implies G
| eq8 => AT421_Equation8_implies G
| eq10 => AT421_Equation10_implies G
| eq11 => AT421_Equation11_implies G
| eq14 => AT421_Equation14_implies G
| eq16 => AT421_Equation16_implies G
| eq38 => AT421_Equation38_implies G
| eq39 => AT421_Equation39_implies G
| eq40 => AT421_Equation40_implies G
| eq41 => AT421_Equation41_implies G
| eq43 => AT421_Equation43_implies G
| eq47 => AT421_Equation47_implies G
| eq56 => AT421_Equation56_implies G
| eq66 => AT421_Equation66_implies G
| eq75 => AT421_Equation75_implies G
| eq307 => AT421_Equation307_implies G
| eq308 => AT421_Equation308_implies G
| eq309 => AT421_Equation309_implies G
| eq310 => AT421_Equation310_implies G
| eq311 => AT421_Equation311_implies G
| eq312 => AT421_Equation312_implies G
| eq313 => AT421_Equation313_implies G
| eq314 => AT421_Equation314_implies G
| eq315 => AT421_Equation315_implies G
| eq316 => AT421_Equation316_implies G
| eq318 => AT421_Equation318_implies G
| eq323 => AT421_Equation323_implies G
| eq325 => AT421_Equation325_implies G
| eq326 => AT421_Equation326_implies G
| eq327 => AT421_Equation327_implies G
| eq329 => AT421_Equation329_implies G
| eq332 => AT421_Equation332_implies G
| eq333 => AT421_Equation333_implies G
| eq343 => AT421_Equation343_implies G
| eq411 => AT421_Equation411_implies G
| eq419 => AT421_Equation419_implies G
| eq429 => AT421_Equation429_implies G
| eq440 => AT421_Equation440_implies G
| eq477 => AT421_Equation477_implies G
| eq504 => AT421_Equation504_implies G
| eq513 => AT421_Equation513_implies G
| eq3253 => AT421_Equation3253_implies G
| eq3255 => AT421_Equation3255_implies G
| eq3256 => AT421_Equation3256_implies G
| eq3258 => AT421_Equation3258_implies G
| eq3259 => AT421_Equation3259_implies G
| eq3260 => AT421_Equation3260_implies G
| eq3261 => AT421_Equation3261_implies G
| eq3264 => AT421_Equation3264_implies G
| eq3265 => AT421_Equation3265_implies G
| eq3267 => AT421_Equation3267_implies G
| eq3271 => AT421_Equation3271_implies G
| eq3273 => AT421_Equation3273_implies G
| eq3274 => AT421_Equation3274_implies G
| eq3275 => AT421_Equation3275_implies G
| eq3277 => AT421_Equation3277_implies G
| eq3278 => AT421_Equation3278_implies G
| eq3290 => AT421_Equation3290_implies G
| eq3292 => AT421_Equation3292_implies G
| eq3300 => AT421_Equation3300_implies G
| eq3306 => AT421_Equation3306_implies G
| eq3308 => AT421_Equation3308_implies G
| eq3309 => AT421_Equation3309_implies G
| eq3315 => AT421_Equation3315_implies G
| eq3316 => AT421_Equation3316_implies G
| eq3319 => AT421_Equation3319_implies G
| eq3322 => AT421_Equation3322_implies G
| eq3323 => AT421_Equation3323_implies G
| eq3326 => AT421_Equation3326_implies G
| eq3331 => AT421_Equation3331_implies G
| eq3334 => AT421_Equation3334_implies G
| eq3342 => AT421_Equation3342_implies G
| eq3346 => AT421_Equation3346_implies G
| eq3350 => AT421_Equation3350_implies G
| eq3353 => AT421_Equation3353_implies G
| eq3388 => AT421_Equation3388_implies G
| eq3414 => AT421_Equation3414_implies G
| eq4268 => AT421_Equation4268_implies G
| eq4269 => AT421_Equation4269_implies G
| eq4270 => AT421_Equation4270_implies G
| eq4271 => AT421_Equation4271_implies G
| eq4272 => AT421_Equation4272_implies G
| eq4273 => AT421_Equation4273_implies G
| eq4274 => AT421_Equation4274_implies G
| eq4275 => AT421_Equation4275_implies G
| eq4276 => AT421_Equation4276_implies G
| eq4277 => AT421_Equation4277_implies G
| eq4278 => AT421_Equation4278_implies G
| eq4279 => AT421_Equation4279_implies G
| eq4280 => AT421_Equation4280_implies G
| eq4283 => AT421_Equation4283_implies G
| eq4284 => AT421_Equation4284_implies G
| eq4286 => AT421_Equation4286_implies G
| eq4287 => AT421_Equation4287_implies G
| eq4288 => AT421_Equation4288_implies G
| eq4290 => AT421_Equation4290_implies G
| eq4291 => AT421_Equation4291_implies G
| eq4293 => AT421_Equation4293_implies G
| eq4296 => AT421_Equation4296_implies G
| eq4297 => AT421_Equation4297_implies G
| eq4299 => AT421_Equation4299_implies G
| eq4300 => AT421_Equation4300_implies G
| eq4301 => AT421_Equation4301_implies G
| eq4304 => AT421_Equation4304_implies G
| eq4305 => AT421_Equation4305_implies G
| eq4314 => AT421_Equation4314_implies G
| eq4315 => AT421_Equation4315_implies G
| eq4318 => AT421_Equation4318_implies G
| eq4320 => AT421_Equation4320_implies G
| eq4321 => AT421_Equation4321_implies G
| eq4325 => AT421_Equation4325_implies G
| eq4327 => AT421_Equation4327_implies G
| eq4331 => AT421_Equation4331_implies G
| eq4343 => AT421_Equation4343_implies G
| eq4358 => AT421_Equation4358_implies G
| eq4362 => AT421_Equation4362_implies G
| eq4364 => AT421_Equation4364_implies G
| eq4369 => AT421_Equation4369_implies G
| eq4512 => AT421_Equation4512_implies G
, AT421_conj_implied G eqid⟩

