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


def conj117 : EQIndex → ATIndex
| eq1 => at117
| eq2 => at2
| eq3 => at3
| eq4 => at4
| eq5 => at5
| eq8 => at3
| eq10 => at7
| eq11 => at4
| eq14 => at2
| eq16 => at5
| eq38 => at11
| eq39 => at12
| eq40 => at13
| eq41 => at13
| eq43 => at42
| eq47 => at3
| eq56 => at4
| eq66 => at2
| eq75 => at5
| eq307 => at117
| eq308 => at47
| eq309 => at43
| eq310 => at11
| eq311 => at11
| eq312 => at44
| eq313 => at13
| eq314 => at13
| eq315 => at12
| eq316 => at13
| eq318 => at12
| eq323 => at118
| eq325 => at45
| eq326 => at119
| eq327 => at47
| eq329 => at43
| eq332 => at42
| eq333 => at51
| eq343 => at44
| eq411 => at3
| eq419 => at7
| eq429 => at7
| eq440 => at4
| eq477 => at2
| eq504 => at2
| eq513 => at5
| eq3253 => at117
| eq3255 => at66
| eq3256 => at47
| eq3258 => at69
| eq3259 => at11
| eq3260 => at11
| eq3261 => at43
| eq3264 => at43
| eq3265 => at11
| eq3267 => at11
| eq3271 => at12
| eq3273 => at13
| eq3274 => at12
| eq3275 => at13
| eq3277 => at13
| eq3278 => at44
| eq3290 => at13
| eq3292 => at12
| eq3300 => at12
| eq3306 => at118
| eq3308 => at48
| eq3309 => at50
| eq3315 => at45
| eq3316 => at117
| eq3319 => at119
| eq3322 => at66
| eq3323 => at47
| eq3326 => at69
| eq3331 => at11
| eq3334 => at43
| eq3342 => at42
| eq3346 => at53
| eq3350 => at13
| eq3353 => at51
| eq3388 => at12
| eq3414 => at44
| eq4268 => at47
| eq4269 => at43
| eq4270 => at11
| eq4271 => at11
| eq4272 => at44
| eq4273 => at13
| eq4274 => at13
| eq4275 => at12
| eq4276 => at13
| eq4277 => at13
| eq4278 => at12
| eq4279 => at13
| eq4280 => at13
| eq4283 => at48
| eq4284 => at50
| eq4286 => at11
| eq4287 => at43
| eq4288 => at11
| eq4290 => at42
| eq4291 => at51
| eq4293 => at42
| eq4296 => at12
| eq4297 => at13
| eq4299 => at13
| eq4300 => at44
| eq4301 => at13
| eq4304 => at12
| eq4305 => at13
| eq4314 => at45
| eq4315 => at47
| eq4318 => at11
| eq4320 => at53
| eq4321 => at42
| eq4325 => at13
| eq4327 => at12
| eq4331 => at13
| eq4343 => at42
| eq4358 => at314
| eq4362 => at360
| eq4364 => at42
| eq4369 => at42
| eq4512 => at117


private theorem AT117_Equation1_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation1 G)) : AssociativeTheory117 G := by
  obtain ⟨hh, h1⟩ := h
  exact hh

private theorem AT117_Equation2_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation2 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h2⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  exact ⟨h2, h4512⟩

private theorem AT117_Equation3_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3 G)) : AssociativeTheory3 G := by
  obtain ⟨hh, h3⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  exact ⟨h3, h4512⟩

private theorem AT117_Equation4_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h4⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  exact ⟨h4, h4512⟩

private theorem AT117_Equation5_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation5 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h5⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  exact ⟨h5, h4512⟩

private theorem AT117_Equation8_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation8 G)) : AssociativeTheory3 G := by
  obtain ⟨hh, h8⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h411 := Equation8_4512_implies_Equation411 G h8 h4512
  have h3306 := Equation8_4512_implies_Equation3306 G h8 h4512
  have h3319 := Equation8_4512_implies_Equation3319 G h8 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  have h326 := Equation307_3319_4512_implies_Equation326 G h307 h3319 h4512
  have h3309 := Equation323_326_4512_implies_Equation3309 G h323 h326 h4512
  have h4284 := Equation3309_4512_implies_Equation4284 G h3309 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  exact ⟨h3, h4512⟩

private theorem AT117_Equation10_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation10 G)) : AssociativeTheory7 G := by
  obtain ⟨hh, h10⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  exact ⟨h10, h4512⟩

private theorem AT117_Equation11_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation11 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h11⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h411 := Equation11_4512_implies_Equation411 G h11 h4512
  have h429 := Equation11_4512_implies_Equation429 G h11 h4512
  have h3261 := Equation11_4512_implies_Equation3261 G h11 h4512
  have h3315 := Equation11_4512_implies_Equation3315 G h11 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT117_Equation14_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation14 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h14⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h40 := Equation14_4512_implies_Equation40 G h14 h4512
  have h411 := Equation14_4512_implies_Equation411 G h14 h4512
  have h316 := Equation40_307_4512_implies_Equation316 G h40 h307 h4512
  have h4276 := Equation316_4512_implies_Equation4276 G h316 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT117_Equation16_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation16 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h16⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h411 := Equation16_4512_implies_Equation411 G h16 h4512
  have h429 := Equation16_4512_implies_Equation429 G h16 h4512
  have h3261 := Equation16_4512_implies_Equation3261 G h16 h4512
  have h3353 := Equation16_4512_implies_Equation3353 G h16 h4512
  have h333 := Equation307_3353_4512_implies_Equation333 G h307 h3353 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT117_Equation38_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation38 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h38⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  exact ⟨h38, h4512⟩

private theorem AT117_Equation39_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation39 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h39⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  exact ⟨h39, h4512⟩

private theorem AT117_Equation40_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation40 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h40⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h316 := Equation40_307_4512_implies_Equation316 G h40 h307 h4512
  have h3261 := Equation40_4512_implies_Equation3261 G h40 h4512
  have h4290 := Equation40_4512_implies_Equation4290 G h40 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h43 := Equation3316_4290_4512_implies_Equation43 G h3316 h4290 h4512
  have h315 := Equation316_4512_implies_Equation315 G h316 h4512
  have h3255 := Equation316_4512_implies_Equation3255 G h316 h4512
  have h326 := Equation3255_3316_4512_implies_Equation326 G h3255 h3316 h4512
  have h323 := Equation3258_3316_4512_implies_Equation323 G h3258 h3316 h4512
  have h4283 := Equation43_4512_implies_Equation4283 G h43 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT117_Equation41_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation41 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h41⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h38 := Equation41_4512_implies_Equation38 G h41 h4512
  have h39 := Equation41_4512_implies_Equation39 G h41 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT117_Equation43_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation43 G)) : AssociativeTheory42 G := by
  obtain ⟨hh, h43⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4283 := Equation43_4512_implies_Equation4283 G h43 h4512
  have h323 := Equation3316_4283_4512_implies_Equation323 G h3316 h4283 h4512
  exact ⟨h43, h323, h4512⟩

private theorem AT117_Equation47_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation47 G)) : AssociativeTheory3 G := by
  obtain ⟨hh, h47⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  exact ⟨h3, h4512⟩

private theorem AT117_Equation56_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation56 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h56⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h47 := Equation56_4512_implies_Equation47 G h56 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h4 := Equation3_56_4512_implies_Equation4 G h3 h56 h4512
  exact ⟨h4, h4512⟩

private theorem AT117_Equation66_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation66 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h66⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h47 := Equation66_4512_implies_Equation47 G h66 h4512
  have h4276 := Equation66_4512_implies_Equation4276 G h66 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h411 := Equation3_4512_implies_Equation411 G h3 h4512
  have h2 := Equation411_4276_4512_implies_Equation2 G h411 h4276 h4512
  exact ⟨h2, h4512⟩

private theorem AT117_Equation75_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation75 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h75⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h47 := Equation75_4512_implies_Equation47 G h75 h4512
  have h3 := Equation47_3253_4512_implies_Equation3 G h47 h3253 h4512
  have h5 := Equation3_75_4512_implies_Equation5 G h3 h75 h4512
  exact ⟨h5, h4512⟩

private theorem AT117_Equation307_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation307 G)) : AssociativeTheory117 G := by
  obtain ⟨hh, h307⟩ := h
  exact hh

private theorem AT117_Equation308_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation308 G)) : AssociativeTheory47 G := by
  obtain ⟨hh, h308⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h3255 := Equation308_4512_implies_Equation3255 G h308 h4512
  have h3256 := Equation308_4512_implies_Equation3256 G h308 h4512
  have h326 := Equation3255_3316_4512_implies_Equation326 G h3255 h3316 h4512
  have h3319 := Equation326_4512_implies_Equation3319 G h326 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  exact ⟨h308, h325, h4512⟩

private theorem AT117_Equation309_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation309 G)) : AssociativeTheory43 G := by
  obtain ⟨hh, h309⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4284 := Equation309_4512_implies_Equation4284 G h309 h4512
  have h323 := Equation3316_4284_4512_implies_Equation323 G h3316 h4284 h4512
  exact ⟨h309, h323, h4512⟩

private theorem AT117_Equation310_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation310 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h310⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h3255 := Equation310_4512_implies_Equation3255 G h310 h4512
  have h3256 := Equation310_4512_implies_Equation3256 G h310 h4512
  have h3258 := Equation310_4512_implies_Equation3258 G h310 h4512
  have h326 := Equation3255_3316_4512_implies_Equation326 G h3255 h3316 h4512
  have h3319 := Equation326_4512_implies_Equation3319 G h326 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h4512⟩

private theorem AT117_Equation311_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation311 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h311⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h3258 := Equation311_4512_implies_Equation3258 G h311 h4512
  have h4314 := Equation311_4512_implies_Equation4314 G h311 h4512
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h4512⟩

private theorem AT117_Equation312_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation312 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h312⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h3258 := Equation312_4512_implies_Equation3258 G h312 h4512
  have h323 := Equation3258_3316_4512_implies_Equation323 G h3258 h3316 h4512
  exact ⟨h312, h323, h4512⟩

private theorem AT117_Equation313_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation313 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h313⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h315 := Equation313_4512_implies_Equation315 G h313 h4512
  have h3258 := Equation313_4512_implies_Equation3258 G h313 h4512
  have h4314 := Equation313_4512_implies_Equation4314 G h313 h4512
  have h323 := Equation3258_3316_4512_implies_Equation323 G h3258 h3316 h4512
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT117_Equation314_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation314 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h314⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h315 := Equation314_4512_implies_Equation315 G h314 h4512
  have h3258 := Equation314_4512_implies_Equation3258 G h314 h4512
  have h4314 := Equation314_4512_implies_Equation4314 G h314 h4512
  have h323 := Equation3258_3316_4512_implies_Equation323 G h3258 h3316 h4512
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT117_Equation315_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation315 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4284 := Equation315_4512_implies_Equation4284 G h315 h4512
  have h323 := Equation3316_4284_4512_implies_Equation323 G h3316 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT117_Equation316_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation316 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h316⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h315 := Equation316_4512_implies_Equation315 G h316 h4512
  have h3258 := Equation316_4512_implies_Equation3258 G h316 h4512
  have h4290 := Equation316_4512_implies_Equation4290 G h316 h4512
  have h323 := Equation3258_3316_4512_implies_Equation323 G h3258 h3316 h4512
  have h43 := Equation3316_4290_4512_implies_Equation43 G h3316 h4290 h4512
  have h332 := Equation43_323_4512_implies_Equation332 G h43 h323 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h325 := Equation332_4512_implies_Equation325 G h332 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT117_Equation318_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation318 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h318⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h315 := Equation318_4512_implies_Equation315 G h318 h4512
  have h4291 := Equation318_4512_implies_Equation4291 G h318 h4512
  have h323 := Equation3316_4291_4512_implies_Equation323 G h3316 h4291 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT117_Equation323_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation323 G)) : AssociativeTheory118 G := by
  obtain ⟨hh, h323⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  exact ⟨h323, h3316, h4512⟩

private theorem AT117_Equation325_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation325 G)) : AssociativeTheory45 G := by
  obtain ⟨hh, h325⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  exact ⟨h325, h4512⟩

private theorem AT117_Equation326_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation326 G)) : AssociativeTheory119 G := by
  obtain ⟨hh, h326⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  exact ⟨h326, h3316, h4512⟩

private theorem AT117_Equation327_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation327 G)) : AssociativeTheory47 G := by
  obtain ⟨hh, h327⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h308 := Equation327_4512_implies_Equation308 G h327 h4512
  have h325 := Equation327_4512_implies_Equation325 G h327 h4512
  exact ⟨h308, h325, h4512⟩

private theorem AT117_Equation329_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation329 G)) : AssociativeTheory43 G := by
  obtain ⟨hh, h329⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h309 := Equation329_4512_implies_Equation309 G h329 h4512
  have h323 := Equation329_4512_implies_Equation323 G h329 h4512
  exact ⟨h309, h323, h4512⟩

private theorem AT117_Equation332_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation332 G)) : AssociativeTheory42 G := by
  obtain ⟨hh, h332⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h43 := Equation332_4512_implies_Equation43 G h332 h4512
  have h323 := Equation332_4512_implies_Equation323 G h332 h4512
  exact ⟨h43, h323, h4512⟩

private theorem AT117_Equation333_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation333 G)) : AssociativeTheory51 G := by
  obtain ⟨hh, h333⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  exact ⟨h333, h4512⟩

private theorem AT117_Equation343_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation343 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h343⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h312 := Equation343_4512_implies_Equation312 G h343 h4512
  have h323 := Equation343_4512_implies_Equation323 G h343 h4512
  exact ⟨h312, h323, h4512⟩

private theorem AT117_Equation411_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation411 G)) : AssociativeTheory3 G := by
  obtain ⟨hh, h411⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h3306 := Equation8_4512_implies_Equation3306 G h8 h4512
  have h3319 := Equation8_4512_implies_Equation3319 G h8 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  have h326 := Equation307_3319_4512_implies_Equation326 G h307 h3319 h4512
  have h3309 := Equation323_326_4512_implies_Equation3309 G h323 h326 h4512
  have h4284 := Equation3309_4512_implies_Equation4284 G h3309 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  exact ⟨h3, h4512⟩

private theorem AT117_Equation419_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation419 G)) : AssociativeTheory7 G := by
  obtain ⟨hh, h419⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h411 := Equation419_4512_implies_Equation411 G h419 h4512
  have h429 := Equation419_4512_implies_Equation429 G h419 h4512
  have h3261 := Equation419_4512_implies_Equation3261 G h419 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  exact ⟨h10, h4512⟩

private theorem AT117_Equation429_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation429 G)) : AssociativeTheory7 G := by
  obtain ⟨hh, h429⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h411 := Equation429_4512_implies_Equation411 G h429 h4512
  have h3306 := Equation429_4512_implies_Equation3306 G h429 h4512
  have h3319 := Equation429_4512_implies_Equation3319 G h429 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  have h326 := Equation307_3319_4512_implies_Equation326 G h307 h3319 h4512
  have h3309 := Equation323_326_4512_implies_Equation3309 G h323 h326 h4512
  have h4284 := Equation3309_4512_implies_Equation4284 G h3309 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  exact ⟨h10, h4512⟩

private theorem AT117_Equation440_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation440 G)) : AssociativeTheory4 G := by
  obtain ⟨hh, h440⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h411 := Equation440_4512_implies_Equation411 G h440 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  have h429 := Equation11_4512_implies_Equation429 G h11 h4512
  have h3261 := Equation11_4512_implies_Equation3261 G h11 h4512
  have h3315 := Equation11_4512_implies_Equation3315 G h11 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h4 := Equation10_325_4512_implies_Equation4 G h10 h325 h4512
  exact ⟨h4, h4512⟩

private theorem AT117_Equation477_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation477 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h477⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h43 := Equation477_4512_implies_Equation43 G h477 h4512
  have h411 := Equation477_4512_implies_Equation411 G h477 h4512
  have h440 := Equation477_4512_implies_Equation440 G h477 h4512
  have h4283 := Equation477_4512_implies_Equation4283 G h477 h4512
  have h4320 := Equation477_4512_implies_Equation4320 G h477 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h323 := Equation3316_4283_4512_implies_Equation323 G h3316 h4283 h4512
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  have h332 := Equation43_323_4512_implies_Equation332 G h43 h323 h4512
  have h4270 := Equation11_4512_implies_Equation4270 G h11 h4512
  have h4284 := Equation332_4512_implies_Equation4284 G h332 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT117_Equation504_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation504 G)) : AssociativeTheory2 G := by
  obtain ⟨hh, h504⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h411 := Equation504_4512_implies_Equation411 G h504 h4512
  have h440 := Equation504_4512_implies_Equation440 G h504 h4512
  have h4290 := Equation504_4512_implies_Equation4290 G h504 h4512
  have h43 := Equation3316_4290_4512_implies_Equation43 G h3316 h4290 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h11 := Equation8_440_4512_implies_Equation11 G h8 h440 h4512
  have h4320 := Equation43_4512_implies_Equation4320 G h43 h4512
  have h3261 := Equation11_4512_implies_Equation3261 G h11 h4512
  have h4270 := Equation11_4512_implies_Equation4270 G h11 h4512
  have h4273 := Equation4270_4320_4512_implies_Equation4273 G h4270 h4320 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  have h47 := Equation3_4512_implies_Equation47 G h3 h4512
  have h2 := Equation47_4273_4512_implies_Equation2 G h47 h4273 h4512
  exact ⟨h2, h4512⟩

private theorem AT117_Equation513_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation513 G)) : AssociativeTheory5 G := by
  obtain ⟨hh, h513⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h411 := Equation513_4512_implies_Equation411 G h513 h4512
  have h8 := Equation411_3253_4512_implies_Equation8 G h411 h3253 h4512
  have h16 := Equation8_513_4512_implies_Equation16 G h8 h513 h4512
  have h429 := Equation16_4512_implies_Equation429 G h16 h4512
  have h3261 := Equation16_4512_implies_Equation3261 G h16 h4512
  have h3353 := Equation16_4512_implies_Equation3353 G h16 h4512
  have h333 := Equation307_3353_4512_implies_Equation333 G h307 h3353 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h3 := Equation411_4284_4512_implies_Equation3 G h411 h4284 h4512
  have h10 := Equation3_429_4512_implies_Equation10 G h3 h429 h4512
  have h5 := Equation10_333_4512_implies_Equation5 G h10 h333 h4512
  exact ⟨h5, h4512⟩

private theorem AT117_Equation3253_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3253 G)) : AssociativeTheory117 G := by
  obtain ⟨hh, h3253⟩ := h
  exact hh

private theorem AT117_Equation3255_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3255 G)) : AssociativeTheory66 G := by
  obtain ⟨hh, h3255⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h326 := Equation3255_3316_4512_implies_Equation326 G h3255 h3316 h4512
  exact ⟨h326, h3255, h4512⟩

private theorem AT117_Equation3256_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3256 G)) : AssociativeTheory47 G := by
  obtain ⟨hh, h3256⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h308 := Equation307_3256_4512_implies_Equation308 G h307 h3256 h4512
  have h3255 := Equation308_4512_implies_Equation3255 G h308 h4512
  have h326 := Equation3255_3316_4512_implies_Equation326 G h3255 h3316 h4512
  have h3319 := Equation326_4512_implies_Equation3319 G h326 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  exact ⟨h308, h325, h4512⟩

private theorem AT117_Equation3258_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3258 G)) : AssociativeTheory69 G := by
  obtain ⟨hh, h3258⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h323 := Equation3258_3316_4512_implies_Equation323 G h3258 h3316 h4512
  exact ⟨h323, h3258, h4512⟩

private theorem AT117_Equation3259_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3259 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h3259⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h3256 := Equation3259_4512_implies_Equation3256 G h3259 h4512
  have h3261 := Equation3259_4512_implies_Equation3261 G h3259 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h323 := Equation3316_4284_4512_implies_Equation323 G h3316 h4284 h4512
  have h326 := Equation323_4284_4512_implies_Equation326 G h323 h4284 h4512
  have h3319 := Equation326_4512_implies_Equation3319 G h326 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h4512⟩

private theorem AT117_Equation3260_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3260 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h3260⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h3255 := Equation3260_4512_implies_Equation3255 G h3260 h4512
  have h3256 := Equation3260_4512_implies_Equation3256 G h3260 h4512
  have h3258 := Equation3260_4512_implies_Equation3258 G h3260 h4512
  have h326 := Equation3255_3316_4512_implies_Equation326 G h3255 h3316 h4512
  have h3319 := Equation326_4512_implies_Equation3319 G h326 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h4512⟩

private theorem AT117_Equation3261_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3261 G)) : AssociativeTheory43 G := by
  obtain ⟨hh, h3261⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h323 := Equation3316_4284_4512_implies_Equation323 G h3316 h4284 h4512
  have h3255 := Equation3258_4284_4512_implies_Equation3255 G h3258 h4284 h4512
  have h309 := Equation323_3255_4512_implies_Equation309 G h323 h3255 h4512
  exact ⟨h309, h323, h4512⟩

private theorem AT117_Equation3264_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3264 G)) : AssociativeTheory43 G := by
  obtain ⟨hh, h3264⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h3255 := Equation3264_4512_implies_Equation3255 G h3264 h4512
  have h4284 := Equation3264_4512_implies_Equation4284 G h3264 h4512
  have h323 := Equation3316_4284_4512_implies_Equation323 G h3316 h4284 h4512
  have h309 := Equation323_3255_4512_implies_Equation309 G h323 h3255 h4512
  exact ⟨h309, h323, h4512⟩

private theorem AT117_Equation3265_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3265 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h3265⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h3255 := Equation3265_4512_implies_Equation3255 G h3265 h4512
  have h3256 := Equation3265_4512_implies_Equation3256 G h3265 h4512
  have h3258 := Equation3265_4512_implies_Equation3258 G h3265 h4512
  have h326 := Equation3255_3316_4512_implies_Equation326 G h3255 h3316 h4512
  have h3319 := Equation326_4512_implies_Equation3319 G h326 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h4512⟩

private theorem AT117_Equation3267_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3267 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h3267⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h3255 := Equation3267_4512_implies_Equation3255 G h3267 h4512
  have h3256 := Equation3267_4512_implies_Equation3256 G h3267 h4512
  have h3258 := Equation3267_4512_implies_Equation3258 G h3267 h4512
  have h326 := Equation3255_3316_4512_implies_Equation326 G h3255 h3316 h4512
  have h3319 := Equation326_4512_implies_Equation3319 G h326 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h4512⟩

private theorem AT117_Equation3271_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3271 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h3271⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h3261 := Equation3271_4512_implies_Equation3261 G h3271 h4512
  have h3278 := Equation3271_4512_implies_Equation3278 G h3271 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h323 := Equation3316_4284_4512_implies_Equation323 G h3316 h4284 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT117_Equation3273_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3273 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3273⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h315 := Equation3273_4512_implies_Equation315 G h3273 h4512
  have h3258 := Equation3273_4512_implies_Equation3258 G h3273 h4512
  have h4290 := Equation3273_4512_implies_Equation4290 G h3273 h4512
  have h323 := Equation3258_3316_4512_implies_Equation323 G h3258 h3316 h4512
  have h43 := Equation3316_4290_4512_implies_Equation43 G h3316 h4290 h4512
  have h332 := Equation43_323_4512_implies_Equation332 G h43 h323 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h325 := Equation332_4512_implies_Equation325 G h332 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT117_Equation3274_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3274 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h3274⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h315 := Equation3274_4512_implies_Equation315 G h3274 h4512
  have h4284 := Equation3274_4512_implies_Equation4284 G h3274 h4512
  have h323 := Equation3316_4284_4512_implies_Equation323 G h3316 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT117_Equation3275_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3275 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3275⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h315 := Equation3275_4512_implies_Equation315 G h3275 h4512
  have h3258 := Equation3275_4512_implies_Equation3258 G h3275 h4512
  have h4290 := Equation3275_4512_implies_Equation4290 G h3275 h4512
  have h323 := Equation3258_3316_4512_implies_Equation323 G h3258 h3316 h4512
  have h43 := Equation3316_4290_4512_implies_Equation43 G h3316 h4290 h4512
  have h332 := Equation43_323_4512_implies_Equation332 G h43 h323 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h325 := Equation332_4512_implies_Equation325 G h332 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT117_Equation3277_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3277 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3277⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h315 := Equation3277_4512_implies_Equation315 G h3277 h4512
  have h3258 := Equation3277_4512_implies_Equation3258 G h3277 h4512
  have h4290 := Equation3277_4512_implies_Equation4290 G h3277 h4512
  have h323 := Equation3258_3316_4512_implies_Equation323 G h3258 h3316 h4512
  have h43 := Equation3316_4290_4512_implies_Equation43 G h3316 h4290 h4512
  have h332 := Equation43_323_4512_implies_Equation332 G h43 h323 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h325 := Equation332_4512_implies_Equation325 G h332 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT117_Equation3278_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3278 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h3278⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h3258 := Equation312_4512_implies_Equation3258 G h312 h4512
  have h323 := Equation3258_3316_4512_implies_Equation323 G h3258 h3316 h4512
  exact ⟨h312, h323, h4512⟩

private theorem AT117_Equation3290_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3290 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3290⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h315 := Equation3290_4512_implies_Equation315 G h3290 h4512
  have h3258 := Equation3290_4512_implies_Equation3258 G h3290 h4512
  have h4290 := Equation3290_4512_implies_Equation4290 G h3290 h4512
  have h323 := Equation3258_3316_4512_implies_Equation323 G h3258 h3316 h4512
  have h43 := Equation3316_4290_4512_implies_Equation43 G h3316 h4290 h4512
  have h332 := Equation43_323_4512_implies_Equation332 G h43 h323 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h325 := Equation332_4512_implies_Equation325 G h332 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT117_Equation3292_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3292 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h3292⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h315 := Equation3292_4512_implies_Equation315 G h3292 h4512
  have h4284 := Equation3292_4512_implies_Equation4284 G h3292 h4512
  have h323 := Equation3316_4284_4512_implies_Equation323 G h3316 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT117_Equation3300_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3300 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h3300⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h315 := Equation3300_4512_implies_Equation315 G h3300 h4512
  have h4284 := Equation3300_4512_implies_Equation4284 G h3300 h4512
  have h323 := Equation3316_4284_4512_implies_Equation323 G h3316 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT117_Equation3306_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3306 G)) : AssociativeTheory118 G := by
  obtain ⟨hh, h3306⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  exact ⟨h323, h3316, h4512⟩

private theorem AT117_Equation3308_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3308 G)) : AssociativeTheory48 G := by
  obtain ⟨hh, h3308⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h3306 := Equation3308_4512_implies_Equation3306 G h3308 h4512
  have h3315 := Equation3308_4512_implies_Equation3315 G h3308 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  exact ⟨h323, h325, h4512⟩

private theorem AT117_Equation3309_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3309 G)) : AssociativeTheory50 G := by
  obtain ⟨hh, h3309⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h323 := Equation3309_4512_implies_Equation323 G h3309 h4512
  have h326 := Equation3309_4512_implies_Equation326 G h3309 h4512
  exact ⟨h323, h326, h4512⟩

private theorem AT117_Equation3315_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3315 G)) : AssociativeTheory45 G := by
  obtain ⟨hh, h3315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  exact ⟨h325, h4512⟩

private theorem AT117_Equation3316_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3316 G)) : AssociativeTheory117 G := by
  obtain ⟨hh, h3316⟩ := h
  exact hh

private theorem AT117_Equation3319_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3319 G)) : AssociativeTheory119 G := by
  obtain ⟨hh, h3319⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h326 := Equation307_3319_4512_implies_Equation326 G h307 h3319 h4512
  exact ⟨h326, h3316, h4512⟩

private theorem AT117_Equation3322_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3322 G)) : AssociativeTheory66 G := by
  obtain ⟨hh, h3322⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h326 := Equation3322_4512_implies_Equation326 G h3322 h4512
  have h3255 := Equation3322_4512_implies_Equation3255 G h3322 h4512
  exact ⟨h326, h3255, h4512⟩

private theorem AT117_Equation3323_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3323 G)) : AssociativeTheory47 G := by
  obtain ⟨hh, h3323⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h3256 := Equation3323_4512_implies_Equation3256 G h3323 h4512
  have h3315 := Equation3323_4512_implies_Equation3315 G h3323 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h308 := Equation307_3256_4512_implies_Equation308 G h307 h3256 h4512
  exact ⟨h308, h325, h4512⟩

private theorem AT117_Equation3326_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3326 G)) : AssociativeTheory69 G := by
  obtain ⟨hh, h3326⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h323 := Equation3326_4512_implies_Equation323 G h3326 h4512
  have h3258 := Equation3326_4512_implies_Equation3258 G h3326 h4512
  exact ⟨h323, h3258, h4512⟩

private theorem AT117_Equation3331_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3331 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h3331⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h3261 := Equation3331_4512_implies_Equation3261 G h3331 h4512
  have h3315 := Equation3331_4512_implies_Equation3315 G h3331 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h4512⟩

private theorem AT117_Equation3334_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3334 G)) : AssociativeTheory43 G := by
  obtain ⟨hh, h3334⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h3261 := Equation3334_4512_implies_Equation3261 G h3334 h4512
  have h3306 := Equation3334_4512_implies_Equation3306 G h3334 h4512
  have h3319 := Equation3334_4512_implies_Equation3319 G h3334 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  have h326 := Equation307_3319_4512_implies_Equation326 G h307 h3319 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h309 := Equation326_3258_4512_implies_Equation309 G h326 h3258 h4512
  exact ⟨h309, h323, h4512⟩

private theorem AT117_Equation3342_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3342 G)) : AssociativeTheory42 G := by
  obtain ⟨hh, h3342⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h43 := Equation3342_4512_implies_Equation43 G h3342 h4512
  have h3306 := Equation3342_4512_implies_Equation3306 G h3342 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  exact ⟨h43, h323, h4512⟩

private theorem AT117_Equation3346_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3346 G)) : AssociativeTheory53 G := by
  obtain ⟨hh, h3346⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h3319 := Equation3346_4512_implies_Equation3319 G h3346 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h326 := Equation307_3319_4512_implies_Equation326 G h307 h3319 h4512
  have h333 := Equation307_3353_4512_implies_Equation333 G h307 h3353 h4512
  exact ⟨h326, h333, h4512⟩

private theorem AT117_Equation3350_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3350 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h3350⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h3261 := Equation3350_4512_implies_Equation3261 G h3350 h4512
  have h3278 := Equation3350_4512_implies_Equation3278 G h3350 h4512
  have h3306 := Equation3350_4512_implies_Equation3306 G h3350 h4512
  have h3315 := Equation3350_4512_implies_Equation3315 G h3350 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT117_Equation3353_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3353 G)) : AssociativeTheory51 G := by
  obtain ⟨hh, h3353⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h333 := Equation307_3353_4512_implies_Equation333 G h307 h3353 h4512
  exact ⟨h333, h4512⟩

private theorem AT117_Equation3388_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3388 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h3388⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h3261 := Equation3388_4512_implies_Equation3261 G h3388 h4512
  have h3278 := Equation3388_4512_implies_Equation3278 G h3388 h4512
  have h3306 := Equation3388_4512_implies_Equation3306 G h3388 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT117_Equation3414_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation3414 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h3414⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h3278 := Equation3414_4512_implies_Equation3278 G h3414 h4512
  have h3306 := Equation3414_4512_implies_Equation3306 G h3414 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  exact ⟨h312, h323, h4512⟩

private theorem AT117_Equation4268_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4268 G)) : AssociativeTheory47 G := by
  obtain ⟨hh, h4268⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h308 := Equation307_4268_4512_implies_Equation308 G h307 h4268 h4512
  have h3255 := Equation308_4512_implies_Equation3255 G h308 h4512
  have h3256 := Equation308_4512_implies_Equation3256 G h308 h4512
  have h326 := Equation3255_3316_4512_implies_Equation326 G h3255 h3316 h4512
  have h3319 := Equation326_4512_implies_Equation3319 G h326 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  exact ⟨h308, h325, h4512⟩

private theorem AT117_Equation4269_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4269 G)) : AssociativeTheory43 G := by
  obtain ⟨hh, h4269⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h4284 := Equation309_4512_implies_Equation4284 G h309 h4512
  have h323 := Equation3316_4284_4512_implies_Equation323 G h3316 h4284 h4512
  exact ⟨h309, h323, h4512⟩

private theorem AT117_Equation4270_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4270 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h4270⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h3259 := Equation3253_4270_4512_implies_Equation3259 G h3253 h4270 h4512
  have h3256 := Equation3259_4512_implies_Equation3256 G h3259 h4512
  have h3261 := Equation3259_4512_implies_Equation3261 G h3259 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h323 := Equation3316_4284_4512_implies_Equation323 G h3316 h4284 h4512
  have h326 := Equation323_4284_4512_implies_Equation326 G h323 h4284 h4512
  have h3319 := Equation326_4512_implies_Equation3319 G h326 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h4512⟩

private theorem AT117_Equation4271_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4271 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h4271⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4269 := Equation4271_4512_implies_Equation4269 G h4271 h4512
  have h4314 := Equation4271_4512_implies_Equation4314 G h4271 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  have h3258 := Equation309_4512_implies_Equation3258 G h309 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h4512⟩

private theorem AT117_Equation4272_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4272 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h4272⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h312 := Equation307_4272_4512_implies_Equation312 G h307 h4272 h4512
  have h3258 := Equation312_4512_implies_Equation3258 G h312 h4512
  have h323 := Equation3258_3316_4512_implies_Equation323 G h3258 h3316 h4512
  exact ⟨h312, h323, h4512⟩

private theorem AT117_Equation4273_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4273 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4273⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  have h316 := Equation40_307_4512_implies_Equation316 G h40 h307 h4512
  have h3261 := Equation40_4512_implies_Equation3261 G h40 h4512
  have h4290 := Equation40_4512_implies_Equation4290 G h40 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h43 := Equation3316_4290_4512_implies_Equation43 G h3316 h4290 h4512
  have h315 := Equation316_4512_implies_Equation315 G h316 h4512
  have h3255 := Equation316_4512_implies_Equation3255 G h316 h4512
  have h326 := Equation3255_3316_4512_implies_Equation326 G h3255 h3316 h4512
  have h323 := Equation3258_3316_4512_implies_Equation323 G h3258 h3316 h4512
  have h4283 := Equation43_4512_implies_Equation4283 G h43 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT117_Equation4274_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4274 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4274⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4269 := Equation4274_4512_implies_Equation4269 G h4274 h4512
  have h4272 := Equation4274_4512_implies_Equation4272 G h4274 h4512
  have h4283 := Equation4274_4512_implies_Equation4283 G h4274 h4512
  have h4284 := Equation4274_4512_implies_Equation4284 G h4274 h4512
  have h4314 := Equation4274_4512_implies_Equation4314 G h4274 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h312 := Equation307_4272_4512_implies_Equation312 G h307 h4272 h4512
  have h323 := Equation3316_4283_4512_implies_Equation323 G h3316 h4283 h4512
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h3258 := Equation309_4512_implies_Equation3258 G h309 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT117_Equation4275_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4275 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h4275⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h3271 := Equation3253_4275_4512_implies_Equation3271 G h3253 h4275 h4512
  have h3261 := Equation3271_4512_implies_Equation3261 G h3271 h4512
  have h3278 := Equation3271_4512_implies_Equation3278 G h3271 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h323 := Equation3316_4284_4512_implies_Equation323 G h3316 h4284 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT117_Equation4276_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4276 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4276⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h40 := Equation3253_4276_4512_implies_Equation40 G h3253 h4276 h4512
  have h316 := Equation40_307_4512_implies_Equation316 G h40 h307 h4512
  have h3261 := Equation40_4512_implies_Equation3261 G h40 h4512
  have h4290 := Equation40_4512_implies_Equation4290 G h40 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h43 := Equation3316_4290_4512_implies_Equation43 G h3316 h4290 h4512
  have h315 := Equation316_4512_implies_Equation315 G h316 h4512
  have h3255 := Equation316_4512_implies_Equation3255 G h316 h4512
  have h326 := Equation3255_3316_4512_implies_Equation326 G h3255 h3316 h4512
  have h323 := Equation3258_3316_4512_implies_Equation323 G h3258 h3316 h4512
  have h4283 := Equation43_4512_implies_Equation4283 G h43 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT117_Equation4277_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4277 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4277⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4268 := Equation4277_4512_implies_Equation4268 G h4277 h4512
  have h4275 := Equation4277_4512_implies_Equation4275 G h4277 h4512
  have h4276 := Equation4277_4512_implies_Equation4276 G h4277 h4512
  have h4293 := Equation4277_4512_implies_Equation4293 G h4277 h4512
  have h308 := Equation307_4268_4512_implies_Equation308 G h307 h4268 h4512
  have h43 := Equation3316_4293_4512_implies_Equation43 G h3316 h4293 h4512
  have h3271 := Equation3253_4275_4512_implies_Equation3271 G h3253 h4275 h4512
  have h40 := Equation3253_4276_4512_implies_Equation40 G h3253 h4276 h4512
  have h316 := Equation40_307_4512_implies_Equation316 G h40 h307 h4512
  have h3261 := Equation3271_4512_implies_Equation3261 G h3271 h4512
  have h4290 := Equation40_4512_implies_Equation4290 G h40 h4512
  have h4283 := Equation43_4512_implies_Equation4283 G h43 h4512
  have h3255 := Equation308_4512_implies_Equation3255 G h308 h4512
  have h4284 := Equation4290_4293_4512_implies_Equation4284 G h4290 h4293 h4512
  have h326 := Equation3255_3316_4512_implies_Equation326 G h3255 h3316 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h323 := Equation3316_4283_4512_implies_Equation323 G h3316 h4283 h4512
  have h315 := Equation316_4512_implies_Equation315 G h316 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT117_Equation4278_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4278 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h4278⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4272 := Equation4278_4512_implies_Equation4272 G h4278 h4512
  have h4284 := Equation4278_4512_implies_Equation4284 G h4278 h4512
  have h4291 := Equation4278_4512_implies_Equation4291 G h4278 h4512
  have h312 := Equation307_4272_4512_implies_Equation312 G h307 h4272 h4512
  have h323 := Equation3316_4291_4512_implies_Equation323 G h3316 h4291 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT117_Equation4279_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4279 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4279⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4269 := Equation4279_4512_implies_Equation4269 G h4279 h4512
  have h4273 := Equation4279_4512_implies_Equation4273 G h4279 h4512
  have h4321 := Equation4279_4512_implies_Equation4321 G h4279 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h43 := Equation3316_4321_4512_implies_Equation43 G h3316 h4321 h4512
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  have h313 := Equation40_309_4512_implies_Equation313 G h40 h309 h4512
  have h4283 := Equation43_4512_implies_Equation4283 G h43 h4512
  have h3255 := Equation309_4512_implies_Equation3255 G h309 h4512
  have h3258 := Equation309_4512_implies_Equation3258 G h309 h4512
  have h4284 := Equation309_4512_implies_Equation4284 G h309 h4512
  have h326 := Equation3255_3316_4512_implies_Equation326 G h3255 h3316 h4512
  have h323 := Equation3258_3316_4512_implies_Equation323 G h3258 h3316 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h315 := Equation313_4512_implies_Equation315 G h313 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT117_Equation4280_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4280 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4280⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4272 := Equation4280_4512_implies_Equation4272 G h4280 h4512
  have h4343 := Equation4280_4512_implies_Equation4343 G h4280 h4512
  have h312 := Equation307_4272_4512_implies_Equation312 G h307 h4272 h4512
  have h43 := Equation3316_4343_4512_implies_Equation43 G h3316 h4343 h4512
  have h4283 := Equation43_4512_implies_Equation4283 G h43 h4512
  have h4320 := Equation43_4512_implies_Equation4320 G h43 h4512
  have h3258 := Equation312_4512_implies_Equation3258 G h312 h4512
  have h4284 := Equation307_4283_4343_4512_implies_Equation4284 G h307 h4283 h4343 h4512
  have h4314 := Equation4320_4343_4512_implies_Equation4314 G h4320 h4343 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h326 := Equation3316_4320_4512_implies_Equation326 G h3316 h4320 h4512
  have h323 := Equation3316_4283_4512_implies_Equation323 G h3316 h4283 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT117_Equation4283_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4283 G)) : AssociativeTheory48 G := by
  obtain ⟨hh, h4283⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h323 := Equation3316_4283_4512_implies_Equation323 G h3316 h4283 h4512
  have h3306 := Equation323_4512_implies_Equation3306 G h323 h4512
  have h3308 := Equation3306_4283_4512_implies_Equation3308 G h3306 h4283 h4512
  have h3315 := Equation3308_4512_implies_Equation3315 G h3308 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  exact ⟨h323, h325, h4512⟩

private theorem AT117_Equation4284_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4284 G)) : AssociativeTheory50 G := by
  obtain ⟨hh, h4284⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h323 := Equation3316_4284_4512_implies_Equation323 G h3316 h4284 h4512
  have h326 := Equation323_4284_4512_implies_Equation326 G h323 h4284 h4512
  exact ⟨h323, h326, h4512⟩

private theorem AT117_Equation4286_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4286 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h4286⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4269 := Equation4286_4512_implies_Equation4269 G h4286 h4512
  have h4283 := Equation4286_4512_implies_Equation4283 G h4286 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h323 := Equation3316_4283_4512_implies_Equation323 G h3316 h4283 h4512
  have h3258 := Equation309_4512_implies_Equation3258 G h309 h4512
  have h4284 := Equation309_4512_implies_Equation4284 G h309 h4512
  have h326 := Equation323_4284_4512_implies_Equation326 G h323 h4284 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h4512⟩

private theorem AT117_Equation4287_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4287 G)) : AssociativeTheory43 G := by
  obtain ⟨hh, h4287⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4269 := Equation4287_4512_implies_Equation4269 G h4287 h4512
  have h4284 := Equation4287_4512_implies_Equation4284 G h4287 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h323 := Equation3316_4284_4512_implies_Equation323 G h3316 h4284 h4512
  exact ⟨h309, h323, h4512⟩

private theorem AT117_Equation4288_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4288 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h4288⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4268 := Equation4288_4512_implies_Equation4268 G h4288 h4512
  have h4270 := Equation4288_4512_implies_Equation4270 G h4288 h4512
  have h4284 := Equation4288_4512_implies_Equation4284 G h4288 h4512
  have h308 := Equation307_4268_4512_implies_Equation308 G h307 h4268 h4512
  have h323 := Equation3316_4284_4512_implies_Equation323 G h3316 h4284 h4512
  have h3259 := Equation3253_4270_4512_implies_Equation3259 G h3253 h4270 h4512
  have h326 := Equation323_4284_4512_implies_Equation326 G h323 h4284 h4512
  have h3256 := Equation308_4512_implies_Equation3256 G h308 h4512
  have h3261 := Equation3259_4512_implies_Equation3261 G h3259 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h3319 := Equation326_4512_implies_Equation3319 G h326 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h4512⟩

private theorem AT117_Equation4290_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4290 G)) : AssociativeTheory42 G := by
  obtain ⟨hh, h4290⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h43 := Equation3316_4290_4512_implies_Equation43 G h3316 h4290 h4512
  have h4283 := Equation43_4512_implies_Equation4283 G h43 h4512
  have h323 := Equation3316_4283_4512_implies_Equation323 G h3316 h4283 h4512
  exact ⟨h43, h323, h4512⟩

private theorem AT117_Equation4291_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4291 G)) : AssociativeTheory51 G := by
  obtain ⟨hh, h4291⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h323 := Equation3316_4291_4512_implies_Equation323 G h3316 h4291 h4512
  have h333 := Equation323_4291_4512_implies_Equation333 G h323 h4291 h4512
  exact ⟨h333, h4512⟩

private theorem AT117_Equation4293_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4293 G)) : AssociativeTheory42 G := by
  obtain ⟨hh, h4293⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h43 := Equation3316_4293_4512_implies_Equation43 G h3316 h4293 h4512
  have h4283 := Equation43_4512_implies_Equation4283 G h43 h4512
  have h323 := Equation3316_4283_4512_implies_Equation323 G h3316 h4283 h4512
  exact ⟨h43, h323, h4512⟩

private theorem AT117_Equation4296_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4296 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h4296⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4269 := Equation4296_4512_implies_Equation4269 G h4296 h4512
  have h4275 := Equation4296_4512_implies_Equation4275 G h4296 h4512
  have h4291 := Equation4296_4512_implies_Equation4291 G h4296 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h323 := Equation3316_4291_4512_implies_Equation323 G h3316 h4291 h4512
  have h3271 := Equation3253_4275_4512_implies_Equation3271 G h3253 h4275 h4512
  have h3278 := Equation3271_4512_implies_Equation3278 G h3271 h4512
  have h4284 := Equation309_4512_implies_Equation4284 G h309 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT117_Equation4297_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4297 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4297⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4275 := Equation4297_4512_implies_Equation4275 G h4297 h4512
  have h4290 := Equation4297_4512_implies_Equation4290 G h4297 h4512
  have h43 := Equation3316_4290_4512_implies_Equation43 G h3316 h4290 h4512
  have h3271 := Equation3253_4275_4512_implies_Equation3271 G h3253 h4275 h4512
  have h3261 := Equation3271_4512_implies_Equation3261 G h3271 h4512
  have h3278 := Equation3271_4512_implies_Equation3278 G h3271 h4512
  have h4283 := Equation43_4512_implies_Equation4283 G h43 h4512
  have h4320 := Equation43_4512_implies_Equation4320 G h43 h4512
  have h312 := Equation307_3278_4512_implies_Equation312 G h307 h3278 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h4284 := Equation307_3261_4512_implies_Equation4284 G h307 h3261 h4512
  have h326 := Equation3316_4320_4512_implies_Equation326 G h3316 h4320 h4512
  have h323 := Equation3316_4283_4512_implies_Equation323 G h3316 h4283 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h4314 := Equation4283_4284_4512_implies_Equation4314 G h4283 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h325 := Equation326_4314_4512_implies_Equation325 G h326 h4314 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT117_Equation4299_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4299 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4299⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4272 := Equation4299_4512_implies_Equation4272 G h4299 h4512
  have h4284 := Equation4299_4512_implies_Equation4284 G h4299 h4512
  have h4290 := Equation4299_4512_implies_Equation4290 G h4299 h4512
  have h312 := Equation307_4272_4512_implies_Equation312 G h307 h4272 h4512
  have h43 := Equation3316_4290_4512_implies_Equation43 G h3316 h4290 h4512
  have h323 := Equation3316_4284_4512_implies_Equation323 G h3316 h4284 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h332 := Equation43_323_4512_implies_Equation332 G h43 h323 h4512
  have h3258 := Equation312_4512_implies_Equation3258 G h312 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h325 := Equation332_4512_implies_Equation325 G h332 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT117_Equation4300_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4300 G)) : AssociativeTheory44 G := by
  obtain ⟨hh, h4300⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4272 := Equation4300_4512_implies_Equation4272 G h4300 h4512
  have h4291 := Equation4300_4512_implies_Equation4291 G h4300 h4512
  have h312 := Equation307_4272_4512_implies_Equation312 G h307 h4272 h4512
  have h323 := Equation3316_4291_4512_implies_Equation323 G h3316 h4291 h4512
  exact ⟨h312, h323, h4512⟩

private theorem AT117_Equation4301_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4301 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4301⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4269 := Equation4301_4512_implies_Equation4269 G h4301 h4512
  have h4273 := Equation4301_4512_implies_Equation4273 G h4301 h4512
  have h4291 := Equation4301_4512_implies_Equation4291 G h4301 h4512
  have h4293 := Equation4301_4512_implies_Equation4293 G h4301 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h323 := Equation3316_4291_4512_implies_Equation323 G h3316 h4291 h4512
  have h43 := Equation3316_4293_4512_implies_Equation43 G h3316 h4293 h4512
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  have h313 := Equation40_309_4512_implies_Equation313 G h40 h309 h4512
  have h332 := Equation43_323_4512_implies_Equation332 G h43 h323 h4512
  have h3258 := Equation309_4512_implies_Equation3258 G h309 h4512
  have h315 := Equation313_4512_implies_Equation315 G h313 h4512
  have h325 := Equation332_4512_implies_Equation325 G h332 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT117_Equation4304_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4304 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h4304⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4272 := Equation4304_4512_implies_Equation4272 G h4304 h4512
  have h4284 := Equation4304_4512_implies_Equation4284 G h4304 h4512
  have h312 := Equation307_4272_4512_implies_Equation312 G h307 h4272 h4512
  have h323 := Equation3316_4284_4512_implies_Equation323 G h3316 h4284 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT117_Equation4305_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4305 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4305⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4273 := Equation4305_4512_implies_Equation4273 G h4305 h4512
  have h4275 := Equation4305_4512_implies_Equation4275 G h4305 h4512
  have h4283 := Equation4305_4512_implies_Equation4283 G h4305 h4512
  have h323 := Equation3316_4283_4512_implies_Equation323 G h3316 h4283 h4512
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  have h3271 := Equation3253_4275_4512_implies_Equation3271 G h3253 h4275 h4512
  have h316 := Equation40_307_4512_implies_Equation316 G h40 h307 h4512
  have h3306 := Equation323_4512_implies_Equation3306 G h323 h4512
  have h3261 := Equation3271_4512_implies_Equation3261 G h3271 h4512
  have h3256 := Equation40_4512_implies_Equation3256 G h40 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h3331 := Equation3256_3306_4512_implies_Equation3331 G h3256 h3306 h4512
  have h315 := Equation316_4512_implies_Equation315 G h316 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h3315 := Equation3331_4512_implies_Equation3315 G h3331 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT117_Equation4314_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4314 G)) : AssociativeTheory45 G := by
  obtain ⟨hh, h4314⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  exact ⟨h325, h4512⟩

private theorem AT117_Equation4315_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4315 G)) : AssociativeTheory47 G := by
  obtain ⟨hh, h4315⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4268 := Equation4315_4512_implies_Equation4268 G h4315 h4512
  have h4314 := Equation4315_4512_implies_Equation4314 G h4315 h4512
  have h308 := Equation307_4268_4512_implies_Equation308 G h307 h4268 h4512
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  exact ⟨h308, h325, h4512⟩

private theorem AT117_Equation4318_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4318 G)) : AssociativeTheory11 G := by
  obtain ⟨hh, h4318⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4269 := Equation4318_4512_implies_Equation4269 G h4318 h4512
  have h4314 := Equation4318_4512_implies_Equation4314 G h4318 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  have h3258 := Equation309_4512_implies_Equation3258 G h309 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h4512⟩

private theorem AT117_Equation4320_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4320 G)) : AssociativeTheory53 G := by
  obtain ⟨hh, h4320⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h326 := Equation3316_4320_4512_implies_Equation326 G h3316 h4320 h4512
  have h3319 := Equation326_4512_implies_Equation3319 G h326 h4512
  have h3346 := Equation3319_4320_4512_implies_Equation3346 G h3319 h4320 h4512
  have h3353 := Equation3346_4512_implies_Equation3353 G h3346 h4512
  have h333 := Equation307_3353_4512_implies_Equation333 G h307 h3353 h4512
  exact ⟨h326, h333, h4512⟩

private theorem AT117_Equation4321_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4321 G)) : AssociativeTheory42 G := by
  obtain ⟨hh, h4321⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h43 := Equation3316_4321_4512_implies_Equation43 G h3316 h4321 h4512
  have h4283 := Equation43_4512_implies_Equation4283 G h43 h4512
  have h323 := Equation3316_4283_4512_implies_Equation323 G h3316 h4283 h4512
  exact ⟨h43, h323, h4512⟩

private theorem AT117_Equation4325_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4325 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4325⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4273 := Equation4325_4512_implies_Equation4273 G h4325 h4512
  have h4320 := Equation4325_4512_implies_Equation4320 G h4325 h4512
  have h326 := Equation3316_4320_4512_implies_Equation326 G h3316 h4320 h4512
  have h40 := Equation3253_4273_4512_implies_Equation40 G h3253 h4273 h4512
  have h316 := Equation40_307_4512_implies_Equation316 G h40 h307 h4512
  have h3319 := Equation326_4512_implies_Equation3319 G h326 h4512
  have h3256 := Equation40_4512_implies_Equation3256 G h40 h4512
  have h3261 := Equation40_4512_implies_Equation3261 G h40 h4512
  have h3258 := Equation307_3261_4512_implies_Equation3258 G h307 h3261 h4512
  have h3315 := Equation3256_3319_4512_implies_Equation3315 G h3256 h3319 h4512
  have h3306 := Equation3261_3319_4512_implies_Equation3306 G h3261 h3319 h4512
  have h315 := Equation316_4512_implies_Equation315 G h316 h4512
  have h323 := Equation307_3306_4512_implies_Equation323 G h307 h3306 h4512
  have h325 := Equation307_3315_4512_implies_Equation325 G h307 h3315 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT117_Equation4327_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4327 G)) : AssociativeTheory12 G := by
  obtain ⟨hh, h4327⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4269 := Equation4327_4512_implies_Equation4269 G h4327 h4512
  have h4272 := Equation4327_4512_implies_Equation4272 G h4327 h4512
  have h4320 := Equation4327_4512_implies_Equation4320 G h4327 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h312 := Equation307_4272_4512_implies_Equation312 G h307 h4272 h4512
  have h326 := Equation3316_4320_4512_implies_Equation326 G h3316 h4320 h4512
  have h4284 := Equation309_4512_implies_Equation4284 G h309 h4512
  have h323 := Equation326_4284_4512_implies_Equation323 G h326 h4284 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h39, h4512⟩

private theorem AT117_Equation4331_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4331 G)) : AssociativeTheory13 G := by
  obtain ⟨hh, h4331⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4269 := Equation4331_4512_implies_Equation4269 G h4331 h4512
  have h4272 := Equation4331_4512_implies_Equation4272 G h4331 h4512
  have h4314 := Equation4331_4512_implies_Equation4314 G h4331 h4512
  have h309 := Equation307_4269_4512_implies_Equation309 G h307 h4269 h4512
  have h312 := Equation307_4272_4512_implies_Equation312 G h307 h4272 h4512
  have h325 := Equation3316_4314_4512_implies_Equation325 G h3316 h4314 h4512
  have h3258 := Equation312_4512_implies_Equation3258 G h312 h4512
  have h4284 := Equation309_4512_implies_Equation4284 G h309 h4512
  have h315 := Equation312_4284_4512_implies_Equation315 G h312 h4284 h4512
  have h323 := Equation3258_3316_4512_implies_Equation323 G h3258 h3316 h4512
  have h38 := Equation325_3258_4512_implies_Equation38 G h325 h3258 h4512
  have h39 := Equation315_323_4512_implies_Equation39 G h315 h323 h4512
  exact ⟨h38, h39, h4512⟩

private theorem AT117_Equation4343_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4343 G)) : AssociativeTheory42 G := by
  obtain ⟨hh, h4343⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h43 := Equation3316_4343_4512_implies_Equation43 G h3316 h4343 h4512
  have h4283 := Equation43_4512_implies_Equation4283 G h43 h4512
  have h323 := Equation3316_4283_4512_implies_Equation323 G h3316 h4283 h4512
  exact ⟨h43, h323, h4512⟩

private theorem AT117_Equation4358_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4358 G)) : AssociativeTheory314 G := by
  obtain ⟨hh, h4358⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4283 := Equation4358_4512_implies_Equation4283 G h4358 h4512
  have h323 := Equation3316_4283_4512_implies_Equation323 G h3316 h4283 h4512
  exact ⟨h323, h4358, h4512⟩

private theorem AT117_Equation4362_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4362 G)) : AssociativeTheory360 G := by
  obtain ⟨hh, h4362⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4320 := Equation4362_4512_implies_Equation4320 G h4362 h4512
  have h326 := Equation3316_4320_4512_implies_Equation326 G h3316 h4320 h4512
  exact ⟨h326, h4362, h4512⟩

private theorem AT117_Equation4364_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4364 G)) : AssociativeTheory42 G := by
  obtain ⟨hh, h4364⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4283 := Equation4364_4512_implies_Equation4283 G h4364 h4512
  have h4290 := Equation4364_4512_implies_Equation4290 G h4364 h4512
  have h43 := Equation3316_4290_4512_implies_Equation43 G h3316 h4290 h4512
  have h323 := Equation3316_4283_4512_implies_Equation323 G h3316 h4283 h4512
  exact ⟨h43, h323, h4512⟩

private theorem AT117_Equation4369_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4369 G)) : AssociativeTheory42 G := by
  obtain ⟨hh, h4369⟩ := h
  obtain ⟨g, _⟩ := AT_equiv at117 G
  obtain ⟨h1, h307, h3253, h3316, h4512⟩ := g hh
  have h4290 := Equation4369_4512_implies_Equation4290 G h4369 h4512
  have h43 := Equation3316_4290_4512_implies_Equation43 G h3316 h4290 h4512
  have h4283 := Equation43_4512_implies_Equation4283 G h43 h4512
  have h323 := Equation3316_4283_4512_implies_Equation323 G h3316 h4283 h4512
  exact ⟨h43, h323, h4512⟩

private theorem AT117_Equation4512_implies (G : Type*) [Magma G] (h : (AssociativeTheory117 G) ∧ (Equation4512 G)) : AssociativeTheory117 G := by
  obtain ⟨hh, h4512⟩ := h
  exact hh

theorem AT117_conj_implied (eqid : EQIndex) (G: Type*) [Magma G] (h : ATearly (conj117 eqid) G) : (AssociativeTheory117 G) ∧ (EQeq eqid G) := by
  have h0 := (AT_equiv (conj117 eqid) G).mp h
  rcases eqid
  all_goals
    constructor
    exact AT_implies' _ G h at117 True.intro
    repeat' (obtain ⟨h1, h0⟩ := h0 ; try exact h1) ; try exact h0

theorem AT117_conj (eqid : EQIndex) (G: Type*) [Magma G] : (AssociativeTheory117 G) ∧ (EQeq eqid G) <-> (ATearly (conj117 eqid) G) :=
⟨match eqid with
| eq1 => AT117_Equation1_implies G
| eq2 => AT117_Equation2_implies G
| eq3 => AT117_Equation3_implies G
| eq4 => AT117_Equation4_implies G
| eq5 => AT117_Equation5_implies G
| eq8 => AT117_Equation8_implies G
| eq10 => AT117_Equation10_implies G
| eq11 => AT117_Equation11_implies G
| eq14 => AT117_Equation14_implies G
| eq16 => AT117_Equation16_implies G
| eq38 => AT117_Equation38_implies G
| eq39 => AT117_Equation39_implies G
| eq40 => AT117_Equation40_implies G
| eq41 => AT117_Equation41_implies G
| eq43 => AT117_Equation43_implies G
| eq47 => AT117_Equation47_implies G
| eq56 => AT117_Equation56_implies G
| eq66 => AT117_Equation66_implies G
| eq75 => AT117_Equation75_implies G
| eq307 => AT117_Equation307_implies G
| eq308 => AT117_Equation308_implies G
| eq309 => AT117_Equation309_implies G
| eq310 => AT117_Equation310_implies G
| eq311 => AT117_Equation311_implies G
| eq312 => AT117_Equation312_implies G
| eq313 => AT117_Equation313_implies G
| eq314 => AT117_Equation314_implies G
| eq315 => AT117_Equation315_implies G
| eq316 => AT117_Equation316_implies G
| eq318 => AT117_Equation318_implies G
| eq323 => AT117_Equation323_implies G
| eq325 => AT117_Equation325_implies G
| eq326 => AT117_Equation326_implies G
| eq327 => AT117_Equation327_implies G
| eq329 => AT117_Equation329_implies G
| eq332 => AT117_Equation332_implies G
| eq333 => AT117_Equation333_implies G
| eq343 => AT117_Equation343_implies G
| eq411 => AT117_Equation411_implies G
| eq419 => AT117_Equation419_implies G
| eq429 => AT117_Equation429_implies G
| eq440 => AT117_Equation440_implies G
| eq477 => AT117_Equation477_implies G
| eq504 => AT117_Equation504_implies G
| eq513 => AT117_Equation513_implies G
| eq3253 => AT117_Equation3253_implies G
| eq3255 => AT117_Equation3255_implies G
| eq3256 => AT117_Equation3256_implies G
| eq3258 => AT117_Equation3258_implies G
| eq3259 => AT117_Equation3259_implies G
| eq3260 => AT117_Equation3260_implies G
| eq3261 => AT117_Equation3261_implies G
| eq3264 => AT117_Equation3264_implies G
| eq3265 => AT117_Equation3265_implies G
| eq3267 => AT117_Equation3267_implies G
| eq3271 => AT117_Equation3271_implies G
| eq3273 => AT117_Equation3273_implies G
| eq3274 => AT117_Equation3274_implies G
| eq3275 => AT117_Equation3275_implies G
| eq3277 => AT117_Equation3277_implies G
| eq3278 => AT117_Equation3278_implies G
| eq3290 => AT117_Equation3290_implies G
| eq3292 => AT117_Equation3292_implies G
| eq3300 => AT117_Equation3300_implies G
| eq3306 => AT117_Equation3306_implies G
| eq3308 => AT117_Equation3308_implies G
| eq3309 => AT117_Equation3309_implies G
| eq3315 => AT117_Equation3315_implies G
| eq3316 => AT117_Equation3316_implies G
| eq3319 => AT117_Equation3319_implies G
| eq3322 => AT117_Equation3322_implies G
| eq3323 => AT117_Equation3323_implies G
| eq3326 => AT117_Equation3326_implies G
| eq3331 => AT117_Equation3331_implies G
| eq3334 => AT117_Equation3334_implies G
| eq3342 => AT117_Equation3342_implies G
| eq3346 => AT117_Equation3346_implies G
| eq3350 => AT117_Equation3350_implies G
| eq3353 => AT117_Equation3353_implies G
| eq3388 => AT117_Equation3388_implies G
| eq3414 => AT117_Equation3414_implies G
| eq4268 => AT117_Equation4268_implies G
| eq4269 => AT117_Equation4269_implies G
| eq4270 => AT117_Equation4270_implies G
| eq4271 => AT117_Equation4271_implies G
| eq4272 => AT117_Equation4272_implies G
| eq4273 => AT117_Equation4273_implies G
| eq4274 => AT117_Equation4274_implies G
| eq4275 => AT117_Equation4275_implies G
| eq4276 => AT117_Equation4276_implies G
| eq4277 => AT117_Equation4277_implies G
| eq4278 => AT117_Equation4278_implies G
| eq4279 => AT117_Equation4279_implies G
| eq4280 => AT117_Equation4280_implies G
| eq4283 => AT117_Equation4283_implies G
| eq4284 => AT117_Equation4284_implies G
| eq4286 => AT117_Equation4286_implies G
| eq4287 => AT117_Equation4287_implies G
| eq4288 => AT117_Equation4288_implies G
| eq4290 => AT117_Equation4290_implies G
| eq4291 => AT117_Equation4291_implies G
| eq4293 => AT117_Equation4293_implies G
| eq4296 => AT117_Equation4296_implies G
| eq4297 => AT117_Equation4297_implies G
| eq4299 => AT117_Equation4299_implies G
| eq4300 => AT117_Equation4300_implies G
| eq4301 => AT117_Equation4301_implies G
| eq4304 => AT117_Equation4304_implies G
| eq4305 => AT117_Equation4305_implies G
| eq4314 => AT117_Equation4314_implies G
| eq4315 => AT117_Equation4315_implies G
| eq4318 => AT117_Equation4318_implies G
| eq4320 => AT117_Equation4320_implies G
| eq4321 => AT117_Equation4321_implies G
| eq4325 => AT117_Equation4325_implies G
| eq4327 => AT117_Equation4327_implies G
| eq4331 => AT117_Equation4331_implies G
| eq4343 => AT117_Equation4343_implies G
| eq4358 => AT117_Equation4358_implies G
| eq4362 => AT117_Equation4362_implies G
| eq4364 => AT117_Equation4364_implies G
| eq4369 => AT117_Equation4369_implies G
| eq4512 => AT117_Equation4512_implies G
, AT117_conj_implied eqid G⟩

